#include "kernel/log.h"
#include "kernel/utils.h"
#include "kernel/binding.h"
#include "libs/sha1/sha1.h"
#include "ast.h"
#include "ast_binding.h"
#include "kernel/bitpattern.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/consteval.h"
#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include <stdlib.h>
#include <stdio.h>
#include <sstream>
#include <stdarg.h>
#include <algorithm>
#include <string>
#include <iostream>
#include <fstream>


//std::vector <int> line_number;

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
std::map <std::string, std::string> string_assign_le; //used for storing the string values
std::map <std::string, std::string> string_assign_eq; //used for storing the string values
std::multimap <std::string, std::string> comb_latch_ff_details; // used to store latch, comb and ff, true for latch, NULL for ff, false for Combination
std::vector <std::string> string_details; //To check guideline number 6 
std::multimap <std::string, int> string_values; //Trying dictionary
std::multimap <std::string, std::string> string_values_update; //Trying dictionary

struct proc_dlatch_db_t
{
	Module *module;
	SigMap sigmap;
	FfInitVals initvals;

	pool<Cell*> generated_dlatches;
	dict<Cell*, vector<SigBit>> mux_srcbits;
	dict<SigBit, pair<Cell*, int>> mux_drivers;
	dict<SigBit, int> sigusers;

	proc_dlatch_db_t(Module *module) : module(module), sigmap(module)
	{
		initvals.set(&sigmap, module);
        //printf("Yes we are inside proc \n");
		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($mux), ID($pmux)))
			{
				auto sig_y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(sig_y); i++)
					mux_drivers[sig_y[i]] = pair<Cell*, int>(cell, i);

				pool<SigBit> mux_srcbits_pool;
				for (auto bit : sigmap(cell->getPort(ID::A)))
					mux_srcbits_pool.insert(bit);
				for (auto bit : sigmap(cell->getPort(ID::B)))
					mux_srcbits_pool.insert(bit);

				vector<SigBit> mux_srcbits_vec;
				for (auto bit : mux_srcbits_pool)
					if (bit.wire != nullptr)
						mux_srcbits_vec.push_back(bit);

				mux_srcbits[cell].swap(mux_srcbits_vec);
			}

			for (auto &conn : cell->connections())
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigusers[bit]++;
		}

		for (auto wire : module->wires())
		{
			if (wire->port_input)
				for (auto bit : sigmap(wire))
					sigusers[bit]++;
		}
	}


	bool quickcheck(const SigSpec &haystack, const SigSpec &needle)
	{
		pool<SigBit> haystack_bits = sigmap(haystack).to_sigbit_pool();
		pool<SigBit> needle_bits = sigmap(needle).to_sigbit_pool();

		pool<Cell*> cells_queue, cells_visited;
		pool<SigBit> bits_queue, bits_visited;

		bits_queue = haystack_bits;
		while (!bits_queue.empty())
		{
			for (auto &bit : bits_queue) {
				auto it = mux_drivers.find(bit);
				if (it != mux_drivers.end())
					if (!cells_visited.count(it->second.first))
						cells_queue.insert(it->second.first);
				bits_visited.insert(bit);
			}

			bits_queue.clear();

			for (auto c : cells_queue) {
				for (auto bit : mux_srcbits[c]) {
					if (needle_bits.count(bit))
						return true;
					if (!bits_visited.count(bit))
						bits_queue.insert(bit);
				}
			}

			cells_queue.clear();
		}

		return false;
	}

	struct rule_node_t
	{
		// a node is true if "signal" equals "match" and [any
		// of the child nodes is true or "children" is empty]
		SigBit signal, match;
		vector<int> children;

		bool operator==(const rule_node_t &other) const {
			return signal == other.signal && match == other.match && children == other.children;
		}

		unsigned int hash() const {
			unsigned int h = mkhash_init;
			mkhash(h, signal.hash());
			mkhash(h, match.hash());
			for (auto i : children) mkhash(h, i);
			return h;
		}
	};

	enum tf_node_types_t : int {
		true_node = 1,
		false_node = 2
	};

	idict<rule_node_t, 3> rules_db;
	dict<int, SigBit> rules_sig;

	int make_leaf(SigBit signal, SigBit match)
	{
		rule_node_t node;
		node.signal = signal;
		node.match = match;
		return rules_db(node);
	}

	int make_inner(SigBit signal, SigBit match, int child)
	{
		rule_node_t node;
		node.signal = signal;
		node.match = match;
		node.children.push_back(child);
		return rules_db(node);
	}

	int make_inner(const pool<int> &children)
	{
		rule_node_t node;
		node.signal = State::S0;
		node.match = State::S0;
		node.children = vector<int>(children.begin(), children.end());
		std::sort(node.children.begin(), node.children.end());
		return rules_db(node);
	}

	int find_mux_feedback(SigBit haystack, SigBit needle, bool set_undef)
	{
		if (sigusers[haystack] > 1)
			set_undef = false;

		if (haystack == needle)
			return true_node;

		auto it = mux_drivers.find(haystack);
		if (it == mux_drivers.end())
			return false_node;

		Cell *cell = it->second.first;
		int index = it->second.second;

		SigSpec sig_a = sigmap(cell->getPort(ID::A));
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		SigSpec sig_s = sigmap(cell->getPort(ID::S));
		int width = GetSize(sig_a);

		pool<int> children;

		int n = find_mux_feedback(sig_a[index], needle, set_undef);
		if (n != false_node) {
			if (set_undef && sig_a[index] == needle) {
				SigSpec sig = cell->getPort(ID::A);
				sig[index] = State::Sx;
				cell->setPort(ID::A, sig);
			}
			for (int i = 0; i < GetSize(sig_s); i++)
				n = make_inner(sig_s[i], State::S0, n);
			children.insert(n);
		}

		for (int i = 0; i < GetSize(sig_s); i++) {
			n = find_mux_feedback(sig_b[i*width + index], needle, set_undef);
			if (n != false_node) {
				if (set_undef && sig_b[i*width + index] == needle) {
					SigSpec sig = cell->getPort(ID::B);
					sig[i*width + index] = State::Sx;
					cell->setPort(ID::B, sig);
				}
				children.insert(make_inner(sig_s[i], State::S1, n));
			}
		}

		if (children.empty())
			return false_node;

		return make_inner(children);
	}

	SigBit make_hold(int n, string &src)
	{
		if (n == true_node)
			return State::S1;

		if (n == false_node)
			return State::S0;

		if (rules_sig.count(n))
			return rules_sig.at(n);

		const rule_node_t &rule = rules_db[n];
		SigSpec and_bits;

		if (rule.signal != rule.match) {
			if (rule.match == State::S1)
				and_bits.append(rule.signal);
			else if (rule.match == State::S0)
				and_bits.append(module->Not(NEW_ID, rule.signal, false, src));
			else
				and_bits.append(module->Eq(NEW_ID, rule.signal, rule.match, false, src));
		}

		if (!rule.children.empty()) {
			SigSpec or_bits;
			for (int k : rule.children)
				or_bits.append(make_hold(k, src));
			and_bits.append(module->ReduceOr(NEW_ID, or_bits, false, src));
		}

		if (GetSize(and_bits) == 2)
			and_bits = module->And(NEW_ID, and_bits[0], and_bits[1], false, src);
		log_assert(GetSize(and_bits) == 1);

		rules_sig[n] = and_bits[0];
		return and_bits[0];
	}

	void fixup_mux(Cell *cell)
	{
		SigSpec sig_a = cell->getPort(ID::A);
		SigSpec sig_b = cell->getPort(ID::B);
		SigSpec sig_s = cell->getPort(ID::S);
		SigSpec sig_any_valid_b;

		SigSpec sig_new_b, sig_new_s;
		for (int i = 0; i < GetSize(sig_s); i++) {
			SigSpec b = sig_b.extract(i*GetSize(sig_a), GetSize(sig_a));
			if (!b.is_fully_undef()) {
				sig_any_valid_b = b;
				sig_new_b.append(b);
				sig_new_s.append(sig_s[i]);
			}
		}

		if (sig_new_s.empty()) {
			sig_new_b = sig_a;
			sig_new_s = State::S0;
		}

		if (sig_a.is_fully_undef() && !sig_any_valid_b.empty())
			cell->setPort(ID::A, sig_any_valid_b);

		if (GetSize(sig_new_s) == 1) {
			cell->type = ID($mux);
			cell->unsetParam(ID::S_WIDTH);
		} else {
			cell->type = ID($pmux);
			cell->setParam(ID::S_WIDTH, GetSize(sig_new_s));
		}

		cell->setPort(ID::B, sig_new_b);
		cell->setPort(ID::S, sig_new_s);
	}

	void fixup_muxes()
	{
		pool<Cell*> visited, queue;
		dict<Cell*, pool<SigBit>> upstream_cell2net;
		dict<SigBit, pool<Cell*>> upstream_net2cell;

		CellTypes ct;
		ct.setup_internals();

		for (auto cell : module->cells())
		for (auto conn : cell->connections()) {
			if (cell->input(conn.first))
				for (auto bit : sigmap(conn.second))
					upstream_cell2net[cell].insert(bit);
			if (cell->output(conn.first))
				for (auto bit : sigmap(conn.second))
					upstream_net2cell[bit].insert(cell);
		}

		queue = generated_dlatches;
		while (!queue.empty())
		{
			pool<Cell*> next_queue;

			for (auto cell : queue) {
				if (cell->type.in(ID($mux), ID($pmux)))
					fixup_mux(cell);
				for (auto bit : upstream_cell2net[cell])
					for (auto cell : upstream_net2cell[bit])
						next_queue.insert(cell);
				visited.insert(cell);
			}

			queue.clear();
			for (auto cell : next_queue) {
				if (!visited.count(cell) && ct.cell_known(cell->type))
					queue.insert(cell);
			}
		}
	}
};

void proc_dlatch(proc_dlatch_db_t &db, RTLIL::Process *proc)
{
	RTLIL::SigSig latches_bits, nolatches_bits;
	dict<SigBit, SigBit> latches_out_in;
	dict<SigBit, int> latches_hold;
	std::string src = proc->get_src_attribute();

	for (auto sr : proc->syncs)
	{
		if (sr->type != RTLIL::SyncType::STa) {
			continue;
		}

		if (proc->get_bool_attribute(ID::always_ff))
			log_error("Found non edge/level sensitive event in always_ff process `%s.%s'.\n",
					db.module->name.c_str(), proc->name.c_str());

		for (auto ss : sr->actions)
		{
			db.sigmap.apply(ss.first);
			db.sigmap.apply(ss.second);

			if (!db.quickcheck(ss.second, ss.first)) {
				nolatches_bits.first.append(ss.first);
				nolatches_bits.second.append(ss.second);
				continue;
			}

			for (int i = 0; i < GetSize(ss.first); i++)
				latches_out_in[ss.first[i]] = ss.second[i];
		}
		sr->actions.clear();
	}

	latches_out_in.sort();
	for (auto &it : latches_out_in) {
		int n = db.find_mux_feedback(it.second, it.first, true);
		if (n == db.false_node) {
			nolatches_bits.first.append(it.first);
			nolatches_bits.second.append(it.second);
		} else {
			latches_bits.first.append(it.first);
			latches_bits.second.append(it.second);
			latches_hold[it.first] = n;
		}
	}

	int offset = 0;
	for (auto chunk : nolatches_bits.first.chunks()) {
		SigSpec lhs = chunk, rhs = nolatches_bits.second.extract(offset, chunk.width);
		if (proc->get_bool_attribute(ID::always_latch))
			log_error("No latch inferred for signal `%s.%s' from always_latch process `%s.%s'.\n",
					db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str());
		else{
			// log("No latch inferred for signal `%s.%s' from process `%s.%s'.\n",
			// 		db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str());
			comb_latch_ff_details.emplace(log_signal(lhs),"Comb");
		}
		for (auto &bit : lhs) {
			State val = db.initvals(bit);
			if (db.initvals(bit) != State::Sx) {
				log("Removing init bit %s for non-memory siginal `%s.%s` in process `%s.%s`.\n", log_signal(val), db.module->name.c_str(), log_signal(bit), db.module->name.c_str(), proc->name.c_str());
			}
			db.initvals.remove_init(bit);
		}
		db.module->connect(lhs, rhs);
		offset += chunk.width;
	}

	offset = 0;
	while (offset < GetSize(latches_bits.first))
	{
		int width = 1;
		int n = latches_hold[latches_bits.first[offset]];
		Wire *w = latches_bits.first[offset].wire;

		if (w != nullptr)
		{
			while (offset+width < GetSize(latches_bits.first) &&
					n == latches_hold[latches_bits.first[offset+width]] &&
					w == latches_bits.first[offset+width].wire)
				width++;

			SigSpec lhs = latches_bits.first.extract(offset, width);
			SigSpec rhs = latches_bits.second.extract(offset, width);

			Cell *cell = db.module->addDlatch(NEW_ID, db.module->Not(NEW_ID, db.make_hold(n, src)), rhs, lhs);
			cell->set_src_attribute(src);
			db.generated_dlatches.insert(cell);

			if (proc->get_bool_attribute(ID::always_comb))
				log_error("Latch inferred for signal `%s.%s' from always_comb process `%s.%s'.\n",
						db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str());
			else{
				// log("Latch inferred for signal `%s.%s' from process `%s.%s': %s\n",
				// 		db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str(), log_id(cell));
				comb_latch_ff_details.emplace(log_signal(lhs),"Latch");
			}
		}

		offset += width;
	}
}

//proc_mux
struct SigSnippets
{
	idict<SigSpec> sigidx;
	dict<SigBit, int> bit2snippet;
	pool<int> snippets;

	void insert(SigSpec sig)
	{
		if (sig.empty())
			return;

		int key = sigidx(sig);
		if (snippets.count(key))
			return;

		SigSpec new_sig;

		for (int i = 0; i < GetSize(sig); i++)
		{
			int other_key = bit2snippet.at(sig[i], -1);

			if (other_key < 0) {
				new_sig.append(sig[i]);
				continue;
			}

			if (!new_sig.empty()) {
				int new_key = sigidx(new_sig);
				snippets.insert(new_key);
				for (auto bit : new_sig)
					bit2snippet[bit] = new_key;
				new_sig = SigSpec();
			}

			SigSpec other_sig = sigidx[other_key];
			int k = 0, n = 1;

			while (other_sig[k] != sig[i]) {
				k++;
				log_assert(k < GetSize(other_sig));
			}

			while (i+n < GetSize(sig) && k+n < GetSize(other_sig) && sig[i+n] == other_sig[k+n])
				n++;

			SigSpec sig1 = other_sig.extract(0, k);
			SigSpec sig2 = other_sig.extract(k, n);
			SigSpec sig3 = other_sig.extract(k+n, GetSize(other_sig)-k-n);

			for (auto bit : other_sig)
				bit2snippet.erase(bit);
			snippets.erase(other_key);

			insert(sig1);
			insert(sig2);
			insert(sig3);

			i += n-1;
		}

		if (!new_sig.empty()) {
			int new_key = sigidx(new_sig);
			snippets.insert(new_key);
			for (auto bit : new_sig)
				bit2snippet[bit] = new_key;
		}
	}

	void insert(const RTLIL::CaseRule *cs)
	{
		for (auto &action : cs->actions)
			insert(action.first);

		for (auto sw : cs->switches)
		for (auto cs2 : sw->cases)
			insert(cs2);
	}
};

struct SnippetSwCache
{
	dict<RTLIL::SwitchRule*, pool<RTLIL::SigBit>, hash_ptr_ops> full_case_bits_cache;
	dict<RTLIL::SwitchRule*, pool<int>, hash_ptr_ops> cache;
	const SigSnippets *snippets;
	int current_snippet;

	bool check(RTLIL::SwitchRule *sw)
	{
		return cache[sw].count(current_snippet) != 0;
	}

	void insert(const RTLIL::CaseRule *cs, vector<RTLIL::SwitchRule*> &sw_stack)
	{
		for (auto &action : cs->actions)
		for (auto bit : action.first) {
			int sn = snippets->bit2snippet.at(bit, -1);
			if (sn < 0)
				continue;
			for (auto sw : sw_stack)
				cache[sw].insert(sn);
		}

		for (auto sw : cs->switches) {
			sw_stack.push_back(sw);
			for (auto cs2 : sw->cases)
				insert(cs2, sw_stack);
			sw_stack.pop_back();
		}
	}

	void insert(const RTLIL::CaseRule *cs)
	{
		vector<RTLIL::SwitchRule*> sw_stack;
		insert(cs, sw_stack);
	}
};

void apply_attrs(RTLIL::Cell *cell, const RTLIL::SwitchRule *sw, const RTLIL::CaseRule *cs)
{
	cell->attributes = sw->attributes;
	cell->add_strpool_attribute(ID::src, cs->get_strpool_attribute(ID::src));
}

RTLIL::SigSpec gen_cmp(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	std::stringstream sstr;
	sstr << "$procmux$" << (autoidx++);

	RTLIL::Wire *cmp_wire = mod->addWire(sstr.str() + "_CMP", 0);

	for (auto comp : compare)
	{
		RTLIL::SigSpec sig = signal;

		// get rid of don't-care bits
		log_assert(sig.size() == comp.size());
		for (int i = 0; i < comp.size(); i++)
			if (comp[i] == RTLIL::State::Sa) {
				sig.remove(i);
				comp.remove(i--);
			}
		if (comp.size() == 0)
			return RTLIL::SigSpec();

		if (sig.size() == 1 && comp == RTLIL::SigSpec(1,1) && !ifxmode)
		{
			mod->connect(RTLIL::SigSig(RTLIL::SigSpec(cmp_wire, cmp_wire->width++), sig));
		}
		else
		{
			// create compare cell
			RTLIL::Cell *eq_cell = mod->addCell(stringf("%s_CMP%d", sstr.str().c_str(), cmp_wire->width), ifxmode ? ID($eqx) : ID($eq));
			apply_attrs(eq_cell, sw, cs);

			eq_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
			eq_cell->parameters[ID::B_SIGNED] = RTLIL::Const(0);

			eq_cell->parameters[ID::A_WIDTH] = RTLIL::Const(sig.size());
			eq_cell->parameters[ID::B_WIDTH] = RTLIL::Const(comp.size());
			eq_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);

			eq_cell->setPort(ID::A, sig);
			eq_cell->setPort(ID::B, comp);
			eq_cell->setPort(ID::Y, RTLIL::SigSpec(cmp_wire, cmp_wire->width++));
		}
	}

	RTLIL::Wire *ctrl_wire;
	if (cmp_wire->width == 1)
	{
		ctrl_wire = cmp_wire;
	}
	else
	{
		ctrl_wire = mod->addWire(sstr.str() + "_CTRL");

		// reduce cmp vector to one logic signal
		RTLIL::Cell *any_cell = mod->addCell(sstr.str() + "_ANY", ID($reduce_or));
		apply_attrs(any_cell, sw, cs);

		any_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
		any_cell->parameters[ID::A_WIDTH] = RTLIL::Const(cmp_wire->width);
		any_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);

		any_cell->setPort(ID::A, cmp_wire);
		any_cell->setPort(ID::Y, RTLIL::SigSpec(ctrl_wire));
	}

	return RTLIL::SigSpec(ctrl_wire);
}

RTLIL::SigSpec gen_mux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::SigSpec else_signal, RTLIL::Cell *&last_mux_cell, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	log_assert(when_signal.size() == else_signal.size());

	std::stringstream sstr;
	sstr << "$procmux$" << (autoidx++);

	// the trivial cases
	if (compare.size() == 0 || when_signal == else_signal)
		return when_signal;

	// compare results
	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw, cs, ifxmode);
	if (ctrl_sig.size() == 0)
		return when_signal;
	log_assert(ctrl_sig.size() == 1);

	// prepare multiplexer output signal
	RTLIL::Wire *result_wire = mod->addWire(sstr.str() + "_Y", when_signal.size());

	// create the multiplexer itself
	RTLIL::Cell *mux_cell = mod->addCell(sstr.str(), ID($mux));
	apply_attrs(mux_cell, sw, cs);

	mux_cell->parameters[ID::WIDTH] = RTLIL::Const(when_signal.size());
	mux_cell->setPort(ID::A, else_signal);
	mux_cell->setPort(ID::B, when_signal);
	mux_cell->setPort(ID::S, ctrl_sig);
	mux_cell->setPort(ID::Y, RTLIL::SigSpec(result_wire));

	last_mux_cell = mux_cell;
	return RTLIL::SigSpec(result_wire);
}

void append_pmux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::Cell *last_mux_cell, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	log_assert(last_mux_cell != NULL);
	log_assert(when_signal.size() == last_mux_cell->getPort(ID::A).size());

	if (when_signal == last_mux_cell->getPort(ID::A))
		return;

	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw, cs, ifxmode);
	log_assert(ctrl_sig.size() == 1);
	last_mux_cell->type = ID($pmux);

	RTLIL::SigSpec new_s = last_mux_cell->getPort(ID::S);
	new_s.append(ctrl_sig);
	last_mux_cell->setPort(ID::S, new_s);

	RTLIL::SigSpec new_b = last_mux_cell->getPort(ID::B);
	new_b.append(when_signal);
	last_mux_cell->setPort(ID::B, new_b);

	last_mux_cell->parameters[ID::S_WIDTH] = last_mux_cell->getPort(ID::S).size();
}

const pool<SigBit> &get_full_case_bits(SnippetSwCache &swcache, RTLIL::SwitchRule *sw)
{
	if (!swcache.full_case_bits_cache.count(sw))
	{
		pool<SigBit> bits;

		if (sw->get_bool_attribute(ID::full_case))
		{
			bool first_case = true;

			for (auto cs : sw->cases)
			{
				pool<SigBit> case_bits;

				for (auto it : cs->actions) {
					for (auto bit : it.first)
						case_bits.insert(bit);
				}

				for (auto it : cs->switches) {
					for (auto bit : get_full_case_bits(swcache, it))
						case_bits.insert(bit);
				}

				if (first_case) {
					first_case = false;
					bits = case_bits;
				} else {
					pool<SigBit> new_bits;
					for (auto bit : bits)
						if (case_bits.count(bit))
							new_bits.insert(bit);
					bits.swap(new_bits);
				}
			}
		}

		bits.swap(swcache.full_case_bits_cache[sw]);
	}

	return swcache.full_case_bits_cache.at(sw);
}

RTLIL::SigSpec signal_to_mux_tree(RTLIL::Module *mod, SnippetSwCache &swcache, dict<RTLIL::SwitchRule*, bool, hash_ptr_ops> &swpara,
		RTLIL::CaseRule *cs, const RTLIL::SigSpec &sig, const RTLIL::SigSpec &defval, bool ifxmode)
{
	RTLIL::SigSpec result = defval;

	for (auto &action : cs->actions) {
		sig.replace(action.first, action.second, &result);
		action.first.remove2(sig, &action.second);
	}

	for (auto sw : cs->switches)
	{
		if (!swcache.check(sw))
			continue;

		// detect groups of parallel cases
		std::vector<int> pgroups(sw->cases.size());
		bool is_simple_parallel_case = true;

		if (!sw->get_bool_attribute(ID::parallel_case)) {
			if (!swpara.count(sw)) {
				pool<Const> case_values;
				for (size_t i = 0; i < sw->cases.size(); i++) {
					RTLIL::CaseRule *cs2 = sw->cases[i];
					for (auto pat : cs2->compare) {
						if (!pat.is_fully_def())
							goto not_simple_parallel_case;
						Const cpat = pat.as_const();
						if (case_values.count(cpat))
							goto not_simple_parallel_case;
						case_values.insert(cpat);
					}
				}
				if (0)
			not_simple_parallel_case:
					is_simple_parallel_case = false;
				swpara[sw] = is_simple_parallel_case;
			} else {
				is_simple_parallel_case = swpara.at(sw);
			}
		}

		if (!is_simple_parallel_case) {
			BitPatternPool pool(sw->signal.size());
			bool extra_group_for_next_case = false;
			for (size_t i = 0; i < sw->cases.size(); i++) {
				RTLIL::CaseRule *cs2 = sw->cases[i];
				if (i != 0) {
					pgroups[i] = pgroups[i-1];
					if (extra_group_for_next_case) {
						pgroups[i] = pgroups[i-1]+1;
						extra_group_for_next_case = false;
					}
					for (auto pat : cs2->compare)
						if (!pat.is_fully_const() || !pool.has_all(pat))
							pgroups[i] = pgroups[i-1]+1;
					if (cs2->compare.empty())
						pgroups[i] = pgroups[i-1]+1;
					if (pgroups[i] != pgroups[i-1])
						pool = BitPatternPool(sw->signal.size());
				}
				for (auto pat : cs2->compare)
					if (!pat.is_fully_const())
						extra_group_for_next_case = true;
					else if (!ifxmode)
						pool.take(pat);
			}
		}

		// mask default bits that are irrelevant because the output is driven by a full case
		const pool<SigBit> &full_case_bits = get_full_case_bits(swcache, sw);
		for (int i = 0; i < GetSize(sig); i++)
			if (full_case_bits.count(sig[i]))
				result[i] = State::Sx;

		// evaluate in reverse order to give the first entry the top priority
		RTLIL::SigSpec initial_val = result;
		RTLIL::Cell *last_mux_cell = NULL;
		for (size_t i = 0; i < sw->cases.size(); i++) {
			int case_idx = sw->cases.size() - i - 1;
			RTLIL::CaseRule *cs2 = sw->cases[case_idx];
			RTLIL::SigSpec value = signal_to_mux_tree(mod, swcache, swpara, cs2, sig, initial_val, ifxmode);
			if (last_mux_cell && pgroups[case_idx] == pgroups[case_idx+1])
				append_pmux(mod, sw->signal, cs2->compare, value, last_mux_cell, sw, cs2, ifxmode);
			else
				result = gen_mux(mod, sw->signal, cs2->compare, value, result, last_mux_cell, sw, cs2, ifxmode);
		}
	}

	return result;
}

void proc_mux(RTLIL::Module *mod, RTLIL::Process *proc, bool ifxmode)
{
	//log("Creating decoders for process `%s.%s'.\n", mod->name.c_str(), proc->name.c_str());

	SigSnippets sigsnip;
	sigsnip.insert(&proc->root_case);

	SnippetSwCache swcache;
	swcache.snippets = &sigsnip;
	swcache.insert(&proc->root_case);

	dict<RTLIL::SwitchRule*, bool, hash_ptr_ops> swpara;

	//int cnt = 0;
	for (int idx : sigsnip.snippets)
	{
		swcache.current_snippet = idx;
		RTLIL::SigSpec sig = sigsnip.sigidx[idx];

		//log("%6d/%d: %s\n", ++cnt, GetSize(sigsnip.snippets), log_signal(sig));

		RTLIL::SigSpec value = signal_to_mux_tree(mod, swcache, swpara, &proc->root_case, sig, RTLIL::SigSpec(RTLIL::State::Sx, sig.size()), ifxmode);
		mod->connect(RTLIL::SigSig(sig, value));
	}
}

//proc_dff
RTLIL::SigSpec find_any_lvalue(const RTLIL::Process *proc)
{
	RTLIL::SigSpec lvalue;

	for (auto sync : proc->syncs)
	for (auto &action : sync->actions)
		if (action.first.size() > 0) {
			lvalue = action.first;
			lvalue.sort_and_unify();
			break;
		}

	for (auto sync : proc->syncs) {
		RTLIL::SigSpec this_lvalue;
		for (auto &action : sync->actions)
			this_lvalue.append(action.first);
		this_lvalue.sort_and_unify();
		RTLIL::SigSpec common_sig = this_lvalue.extract(lvalue);
		if (common_sig.size() > 0)
			lvalue = common_sig;
	}

	return lvalue;
}

void gen_dffsr_complex(RTLIL::Module *mod, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, RTLIL::SigSpec clk, bool clk_polarity,
		std::map<RTLIL::SigSpec, std::set<RTLIL::SyncRule*>> &async_rules, RTLIL::Process *proc)
{
	RTLIL::SigSpec sig_sr_set = RTLIL::SigSpec(0, sig_d.size());
	RTLIL::SigSpec sig_sr_clr = RTLIL::SigSpec(0, sig_d.size());

	for (auto &it : async_rules)
	{
		RTLIL::SigSpec sync_value = it.first;
		RTLIL::SigSpec sync_value_inv;
		RTLIL::SigSpec sync_high_signals;
		RTLIL::SigSpec sync_low_signals;

		for (auto &it2 : it.second)
			if (it2->type == RTLIL::SyncType::ST0)
				sync_low_signals.append(it2->signal);
			else if (it2->type == RTLIL::SyncType::ST1)
				sync_high_signals.append(it2->signal);
			else
				log_abort();

		if (sync_low_signals.size() > 1) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, ID($reduce_or));
			cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
			cell->parameters[ID::A_WIDTH] = RTLIL::Const(sync_low_signals.size());
			cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
			cell->setPort(ID::A, sync_low_signals);
			cell->setPort(ID::Y, sync_low_signals = mod->addWire(NEW_ID));
		}

		if (sync_low_signals.size() > 0) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, ID($not));
			cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
			cell->parameters[ID::A_WIDTH] = RTLIL::Const(sync_low_signals.size());
			cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
			cell->setPort(ID::A, sync_low_signals);
			cell->setPort(ID::Y, mod->addWire(NEW_ID));
			sync_high_signals.append(cell->getPort(ID::Y));
		}

		if (sync_high_signals.size() > 1) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, ID($reduce_or));
			cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
			cell->parameters[ID::A_WIDTH] = RTLIL::Const(sync_high_signals.size());
			cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
			cell->setPort(ID::A, sync_high_signals);
			cell->setPort(ID::Y, sync_high_signals = mod->addWire(NEW_ID));
		}

		RTLIL::Cell *inv_cell = mod->addCell(NEW_ID, ID($not));
		inv_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
		inv_cell->parameters[ID::A_WIDTH] = RTLIL::Const(sig_d.size());
		inv_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(sig_d.size());
		inv_cell->setPort(ID::A, sync_value);
		inv_cell->setPort(ID::Y, sync_value_inv = mod->addWire(NEW_ID, sig_d.size()));

		RTLIL::Cell *mux_set_cell = mod->addCell(NEW_ID, ID($mux));
		mux_set_cell->parameters[ID::WIDTH] = RTLIL::Const(sig_d.size());
		mux_set_cell->setPort(ID::A, sig_sr_set);
		mux_set_cell->setPort(ID::B, sync_value);
		mux_set_cell->setPort(ID::S, sync_high_signals);
		mux_set_cell->setPort(ID::Y, sig_sr_set = mod->addWire(NEW_ID, sig_d.size()));

		RTLIL::Cell *mux_clr_cell = mod->addCell(NEW_ID, ID($mux));
		mux_clr_cell->parameters[ID::WIDTH] = RTLIL::Const(sig_d.size());
		mux_clr_cell->setPort(ID::A, sig_sr_clr);
		mux_clr_cell->setPort(ID::B, sync_value_inv);
		mux_clr_cell->setPort(ID::S, sync_high_signals);
		mux_clr_cell->setPort(ID::Y, sig_sr_clr = mod->addWire(NEW_ID, sig_d.size()));
	}

	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), ID($dffsr));
	cell->attributes = proc->attributes;
	cell->parameters[ID::WIDTH] = RTLIL::Const(sig_d.size());
	cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity, 1);
	cell->parameters[ID::SET_POLARITY] = RTLIL::Const(true, 1);
	cell->parameters[ID::CLR_POLARITY] = RTLIL::Const(true, 1);
	cell->setPort(ID::D, sig_d);
	cell->setPort(ID::Q, sig_q);
	cell->setPort(ID::CLK, clk);
	cell->setPort(ID::SET, sig_sr_set);
	cell->setPort(ID::CLR, sig_sr_clr);

	// log("  created %s cell `%s' with %s edge clock and multiple level-sensitive resets.\n",
	// 		cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
}

void gen_aldff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool set_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec set, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), ID($aldff));
	cell->attributes = proc->attributes;

	cell->parameters[ID::WIDTH] = RTLIL::Const(sig_in.size());
	cell->parameters[ID::ALOAD_POLARITY] = RTLIL::Const(set_polarity, 1);
	cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity, 1);
	cell->setPort(ID::D, sig_in);
	cell->setPort(ID::Q, sig_out);
	cell->setPort(ID::AD, sig_set);
	cell->setPort(ID::CLK, clk);
	cell->setPort(ID::ALOAD, set);

	// log("  created %s cell `%s' with %s edge clock and %s level non-const reset.\n", cell->type.c_str(), cell->name.c_str(),
	// 		clk_polarity ? "positive" : "negative", set_polarity ? "positive" : "negative");
}

void gen_dff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::Const val_rst, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool arst_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec *arst, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), clk.empty() ? ID($ff) : arst ? ID($adff) : ID($dff));
	cell->attributes = proc->attributes;

	cell->parameters[ID::WIDTH] = RTLIL::Const(sig_in.size());
	if (arst) {
		cell->parameters[ID::ARST_POLARITY] = RTLIL::Const(arst_polarity, 1);
		cell->parameters[ID::ARST_VALUE] = val_rst;
	}
	if (!clk.empty()) {
		cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity, 1);
	}

	cell->setPort(ID::D, sig_in);
	//std::cout << "sig_in" << sig_in << std::endl;
	cell->setPort(ID::Q, sig_out);
	//std::cout << "sig_out" << sig_out << std::endl;
	if (arst)
		cell->setPort(ID::ARST, *arst);
	if (!clk.empty())
		cell->setPort(ID::CLK, clk);

	// if (!clk.empty())
	// 	log("  created %s cell `%s' with %s edge clock", cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
	// else
	// 	log("  created %s cell `%s' with global clock", cell->type.c_str(), cell->name.c_str());
	// if (arst)
	// 	log(" and %s level reset", arst_polarity ? "positive" : "negative");
	// log(".\n");
}

void proc_dff(RTLIL::Module *mod, RTLIL::Process *proc, ConstEval &ce)
{
	//bool did_something = true;
	while (1)
	{
		//did_something = false;
		RTLIL::SigSpec sig = find_any_lvalue(proc);
		bool free_sync_level = false;

		if (sig.size() == 0)
		 	break;

		// log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
		// 		mod->name.c_str(), log_signal(sig), mod->name.c_str(), proc->name.c_str());
		comb_latch_ff_details.emplace(log_signal(sig),"Flip_Flop");

		RTLIL::SigSpec insig = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
		RTLIL::SigSpec rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
		RTLIL::SyncRule *sync_level = NULL;
		RTLIL::SyncRule *sync_edge = NULL;
		RTLIL::SyncRule *sync_always = NULL;
		bool global_clock = false;

		std::map<RTLIL::SigSpec, std::set<RTLIL::SyncRule*>> many_async_rules;

		for (auto sync : proc->syncs)
		for (auto &action : sync->actions)
		{
			if (action.first.extract(sig).size() == 0)
				continue;

			if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
				if (sync_level != NULL && sync_level != sync) {
					// log_error("Multiple level sensitive events found for this signal!\n");
					many_async_rules[rstval].insert(sync_level);
					rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				}
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				sig.replace(action.first, action.second, &rstval);
				sync_level = sync;
			}
			else if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
				if (sync_edge != NULL && sync_edge != sync)
					//log_error("Multiple edge sensitive events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_edge = sync;
			}
			else if (sync->type == RTLIL::SyncType::STa) {
				if (sync_always != NULL && sync_always != sync)
					log_error("Multiple always events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_always = sync;
			}
			else if (sync->type == RTLIL::SyncType::STg) {
				sig.replace(action.first, action.second, &insig);
				global_clock = true;
			}
			else {
				log_error("Event with any-edge sensitivity found for this signal!\n");
			}

			action.first.remove2(sig, &action.second);
		}

		if (many_async_rules.size() > 0)
		{
			many_async_rules[rstval].insert(sync_level);
			if (many_async_rules.size() == 1)
			{
				sync_level = new RTLIL::SyncRule;
				sync_level->type = RTLIL::SyncType::ST1;
				sync_level->signal = mod->addWire(NEW_ID);
				sync_level->actions.push_back(RTLIL::SigSig(sig, rstval));
				free_sync_level = true;

				RTLIL::SigSpec inputs, compare;
				for (auto &it : many_async_rules[rstval]) {
					inputs.append(it->signal);
					compare.append(it->type == RTLIL::SyncType::ST0 ? RTLIL::State::S1 : RTLIL::State::S0);
				}
				log_assert(inputs.size() == compare.size());

				RTLIL::Cell *cell = mod->addCell(NEW_ID, ID($ne));
				cell->parameters[ID::A_SIGNED] = RTLIL::Const(false, 1);
				cell->parameters[ID::B_SIGNED] = RTLIL::Const(false, 1);
				cell->parameters[ID::A_WIDTH] = RTLIL::Const(inputs.size());
				cell->parameters[ID::B_WIDTH] = RTLIL::Const(inputs.size());
				cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
				cell->setPort(ID::A, inputs);
				cell->setPort(ID::B, compare);
				cell->setPort(ID::Y, sync_level->signal);

				many_async_rules.clear();
			}
			else
			{
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				sync_level = NULL;
			}
		}

		SigSpec sig_q = sig;

		ce.assign_map.apply(insig);
		ce.assign_map.apply(rstval);
		ce.assign_map.apply(sig);

		if (rstval == sig) {
			if (sync_level->type == RTLIL::SyncType::ST1)
				insig = mod->Mux(NEW_ID, insig, sig, sync_level->signal);
			else
				insig = mod->Mux(NEW_ID, sig, insig, sync_level->signal);
			rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
			sync_level = NULL;
		}

		if (sync_always) {
			if (sync_edge || sync_level || many_async_rules.size() > 0)
				log_error("Mixed always event with edge and/or level sensitive events!\n");
			//log("  created direct connection (no actual register cell created).\n");
			mod->connect(RTLIL::SigSig(sig, insig));
			//continue;
		}

		if (!sync_edge && !global_clock)
			log_error("Missing edge-sensitive event for this signal!\n");

		if (many_async_rules.size() > 0)
		{
			log_warning("Complex async reset for dff `%s'.\n", log_signal(sig));
			gen_dffsr_complex(mod, insig, sig, sync_edge->signal, sync_edge->type == RTLIL::SyncType::STp, many_async_rules, proc);
		}
		else if (!rstval.is_fully_const() && !ce.eval(rstval))
		{
			log_warning("Async reset value `%s' is not constant!\n", log_signal(rstval));
			gen_aldff(mod, insig, rstval, sig_q,
					sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge->signal, sync_level->signal, proc);
		}
		else{
				gen_dff(mod, insig, rstval.as_const(), sig_q,
					sync_edge && sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge ? sync_edge->signal : SigSpec(),
					sync_level ? &sync_level->signal : NULL, proc);
		}
		if (free_sync_level)
			delete sync_level;
	}
}

PRIVATE_NAMESPACE_END

//***********************************************************************************************************
//Different namespace as through this namespace we want to access ASTNODE or AST
YOSYS_NAMESPACE_BEGIN
using namespace AST;
using namespace AST_INTERNAL;
//***********************************************************************************************************

//program to differentiate between latch ,combinational circuits and flip_flops
//proc_mux and proc_dlatch logic
void identifying_difference(RTLIL::Design *design)
{
	//proc_mux
	bool ifxmode = false;
	for (auto mod : design->modules()){
			if (design->selected(mod)){
				//RTLIL::Module try_mod = *mod;
				for (auto &proc_it : mod->processes)
					if (design->selected(mod, proc_it.second))
						proc_mux(mod, proc_it.second, ifxmode);
			}
	}
	//proc_dlatch 
	for (auto module : design->selected_modules()) {
		//RTLIL::Module try_mod = *module;
		proc_dlatch_db_t db(module);
		ConstEval ce(module);
		for (auto &proc_it : module->processes)
				if (design->selected(module, proc_it.second)){
					proc_dlatch(db, proc_it.second);
					proc_dff(module, proc_it.second, ce);
				}
			db.fixup_muxes();
    }
}
//***********************************************************************************************************


//***********************************************************************************************************
//This function is similar to Backend::extra_args but used to
//print the checked guidelines or warning if any to a file 
//provided by users
void extra_args_rules(std::ofstream *&f, std::string &filename)
{
	bool bin_output = false;
	rewrite_filename(filename);
	std::ofstream *ff = new std::ofstream;
	ff->open(filename.c_str(), bin_output ? (std::ofstream::trunc | std::ofstream::binary) : std::ofstream::trunc);
	yosys_output_files.insert(filename);
	if (ff->fail()) {
		delete ff;
		log_cmd_error("Can't open output file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
	}
	f = ff;
}
//*************************************************************************************************************

//*************************************************************************************************************
//This function is actually where we are operating on always block
//To check guidelines
void processing_always_guidelines(std::vector <std::string> &processing_always , int index, std::ofstream &f){
	bool flag_posedge = false;
	bool flag_negedge = false;
	bool flag_edge = false;
	bool flag_nonblocking = false;
	bool flag_blocking = false;
	
	int posedge_index;
	int nonblocking_index;
	int blocking_index;

	for(long unsigned int i=0; i<processing_always.size(); i++){
		if (processing_always[i] == "AST_POSEDGE"){ //identifying posedge int the AST
			flag_posedge = true;
			posedge_index = i;
		}
		if (processing_always[i] == "AST_NEGEDGE"){ //identifying posedge int the AST
			flag_negedge = true;
		}
		if (processing_always[i] == "AST_EDGE"){ //identifying normal combinational block in the AST
			flag_edge = true;
		}
		if (processing_always[i] == "AST_ASSIGN_LE"){
			flag_nonblocking = true;
			nonblocking_index = i;
			if (processing_always[i+3]== "AST_IDENTIFIER"){
				string_assign_le.emplace(processing_always[i+4],processing_always[i+5]);
				string_values.emplace(processing_always[i+4], index);
				string_values_update.emplace(processing_always[i+4], processing_always[i+5]);
			}
		}

		if (processing_always[i] == "AST_ASSIGN_EQ"){
			flag_blocking = true;	
			blocking_index = i;
			if (processing_always[i+3]== "AST_IDENTIFIER"){
				string_assign_eq.emplace(processing_always[i+4],processing_always[i+5]);
				string_values.emplace(processing_always[i+4], index);
				string_values_update.emplace(processing_always[i+4], processing_always[i+5]);
			}
		}
	}
	//std::string messages;
	if (((flag_posedge == true)||(flag_negedge == true)) && (flag_blocking == true)){
		f << stringf("Warning:");
		f << stringf("%s:",processing_always[(blocking_index)+2].c_str());
		f << stringf("NB_SEQ \n");
	}

	if((flag_posedge == true) && (flag_negedge == true)){
		f << stringf("Warning:");
		f << stringf("%s:",processing_always[(posedge_index)+2].c_str());
		f << stringf("NO_POS_NEG_EDGE \n");
	}
	
	if((flag_blocking == true) && (flag_nonblocking == true)){
		f << stringf("Warning:");
		f << stringf("%s:",processing_always[(blocking_index)+2].c_str());
		f << stringf("NO_B_NB \n");
	}
}
// //*************************************************************************************************************

//*************************************************************************************************************
//Printing all the vectors to make ensure to verify the operations
void implementing_guidelines(std::vector <std::string> &type_info, std::vector <std::string> &string_info, 
							std::vector <std::string> &line_info, std::string &filename_rules, std::ofstream *&file_rules,
							std::map <std::string , std::vector <std::string>> range_info)
{
	long unsigned int i;
	std::vector <std::string> combine;
	//combining both type_name and string values
	for (i = 0; i < type_info.size(); i++) {
		combine.push_back(type_info[i]);
		combine.push_back(string_info[i]);
		combine.push_back(line_info[i]);
    }

	// std::vector <std::string> temp_check;
	// for (auto itr=range_info.begin(); itr!=range_info.end(); ++itr){
	// 	temp_check = itr->second;
	// 	std::cout << itr->first << "  " ;
	// 	for(long unsigned int i = 0; i<temp_check.size(); i++)
	// 		std::cout << temp_check[i];
	// 	printf("\n");
	// }

	// for (long unsigned int i=0; i<combine.size(); i++)
	// 	std::cout << "combine " << combine[i] << std::endl;
	extra_args_rules(file_rules, filename_rules);

	int asdf = 0;
	long unsigned int index =0;
	//long unsigned int start_off =0;
	for (long unsigned int j=0; j<combine.size(); j++){
		if (combine[j] == "AST_ALWAYS"){
			std::vector <std::string> intermediate;
			index = j;
			asdf = asdf +1;
			for (i=index; i<combine.size() ; i++){
				if ((i!=index) && (combine[i] == "AST_ALWAYS")){
					break;
				}		
				intermediate.push_back(combine[i]);
			}
			processing_always_guidelines(intermediate, asdf, *file_rules);
		}
	}

	//We are modifying our code just below.. checking the base work
	// for (auto itr=string_assign_eq.begin(); itr!=string_assign_eq.end(); ++itr){
	// 	std::cout << " string_assign_eq ";
	// 	std::cout << itr->first << "  " << itr->second << std::endl;
	// }
	
	// for (auto itr=string_values.begin(); itr!=string_values.end(); ++itr){
	// 	std::cout << " string_values ";
	// 	std::cout << itr->first << "  " << itr->second << std::endl;
	// }

	// for (auto itr=string_values_update.begin(); itr!=string_values_update.end(); ++itr){
	// 	std::cout << " string_values_update ";
	// 	std::cout << itr->first << "  " << itr->second << std::endl;
	// }


	//Below logic is used to implement guideline 6
	//No variable should be assign in different always block
	for (auto itr=string_values.begin(); itr!=string_values.end(); ++itr){
		auto itr1 = string_values.begin();
		auto itr2 = string_values.end();
		while(itr1!=itr2)
		{
			if(itr->first == itr1->first){
				if(itr->second != itr1->second){
					string_details.push_back(itr->first);
				}
			}
			itr1++;
		}
	}

	sort(string_details.begin(), string_details.end());
	std::vector<std::string>::iterator ip;
	ip = std::unique(string_details.begin(), string_details.end());
	string_details.resize(std::distance(string_details.begin(), ip));

	if(string_details.size() > 0){
		*file_rules << stringf("Warning:");
		for (long unsigned int j=0; j<string_details.size(); j++){
			// *file_rules << stringf ("%s \n", string_details[j].c_str());
			for (auto itr=string_values_update.begin(); itr!=string_values_update.end(); ++itr){
				if(string_details[j] == itr->first){
					*file_rules << stringf ("%s:", itr->second.c_str());
					*file_rules << stringf ("NO_SAME_VAR \n ");
					break;
				}
			}
		}
		*file_rules << stringf("Following variable has been assigned multiple times included one shown above \n");
	}

	for (long unsigned int j=0; j<string_details.size(); j++){
		*file_rules << stringf ("%s \n", string_details[j].c_str());
		for (auto itr=string_values_update.begin(); itr!=string_values_update.end(); ++itr){
			if(string_details[j] == itr->first){
				*file_rules << stringf ("match found at : %s \n", itr->second.c_str());
			}
		}
	}
		for (auto itr = comb_latch_ff_details.begin(); itr != comb_latch_ff_details.end(); ++itr) {
			for (auto itr1 = string_assign_le.begin(); itr1 != string_assign_le.end(); ++itr1){
				if(!strcmp(itr1->first.c_str(),itr->first.c_str())){
					if(!strcmp(itr->second.c_str(),"Comb")){
						*file_rules << stringf("Warning:");
						*file_rules << stringf("%s:",itr1->second.c_str());
						*file_rules << stringf("B_COMB \n");
					}
				}
			}

			for (auto itr1 = string_assign_eq.begin(); itr1 != string_assign_eq.end(); ++itr1){
				if(!strcmp(itr1->first.c_str(),itr->first.c_str())){
					if(!strcmp(itr->second.c_str(),"Latch")){
						*file_rules << stringf("Warning:");
						*file_rules << stringf("%s:",itr1->second.c_str());
						*file_rules << stringf("NB_LATCH \n");
					}
				}
			}
			
		}
	string_assign_le.clear();
	string_assign_eq.clear();
	if (file_rules != &std::cout)
		delete file_rules;

	//clearing all the vectors and map
	// dupl_elements.clear();
	// string_values.clear();
	// string_values_update.clear();
	// string_ast_values.clear(); 
	// total_args.clear();
	// comb_latch_ff_details.clear();

}
//***********************************************************************************************************


// //***********************************************************************************************************
// //Defining different rules under capstone project
// void checkingforedges()
// {
// // bool flag_posedge = false;
// // bool flag_negedge = false;
// // bool flag_edge = false;

// if(flag_rules){
	
// 	AstNode *node_module;
// 	AstNode *node_always;
// 	AstNode *ast = current_ast;
// 	//Checking for ast module
// 	for (auto &child : ast->children) {
// 		if (child->type == AST_MODULE){
// 		node_module = child;
// 		}
// 	}

// 	//checking for ast always
// 	int c=0;
// 	for (auto child : node_module->children){
// 		if (child->type == AST_ALWAYS){
// 			node_always = child;
// 			bool flag_posedge = false;
// 			bool flag_negedge = false;
// 			//bool flag_edge = false;
// 			for (auto child : node_always->children){
// 			//if (child->type == AST_ALWAYS){
// 			//node_always = child;
// 			//printf("Yes we reached in a always block \n");
// 				switch(child->type){

// 					case AST_POSEDGE:
// 					//printf("In the posedge \n");
// 						flag_posedge = true;
// 						break;
			
// 					case AST_NEGEDGE:
// 					//printf("In the negedge \n");
// 						flag_negedge = true;
// 						break;
			
// 					default:
// 						break;
// 				}
// 			}
// 			c = c+1;
// 			//printf("Yes we reached in a %d always block \n",c);
// 			if((flag_negedge == true) && (flag_posedge == true)){
// 			printf("Both edges are defined in the rtl code, may cause some problem during flow.\n" );
// 			}
// 		}
// 	}
// }

// }

// //For race conditions
// void checkingforraceguidelines()
// {
// AstNode *node_race_module;
// AstNode *node_race_always;
// AstNode *node_race_block; //defined new block
// //AstNode *node_race_block2;
// AstNode *node_race_cond; //defined for cond
// AstNode *node_race_case; //defined for case
// AstNode *race_ast = current_ast;
// AstNode *node_race_conBlock;
// AstNode *node_assign_le;
// AstNode *node_assign_eq;

// std::string identifier_name;
// std::string identifier_name_eq;

// if(flag_rules){
// 	//Checking for ast module
// 	for (auto &child : race_ast->children) {
// 		if (child->type == AST_MODULE){
// 		node_race_module = child;
// 		}
// 	}

// 	//checking for ast always
// 	int c=0;
// 	for (auto child : node_race_module->children){
// 		if (child->type == AST_ALWAYS){
// 			node_race_always = child;
// 			bool flag_blocking = false;
// 			bool flag_nonblocking = false;
// 			bool flag_posedge = false;
// 			bool flag_negedge = false;
// 			bool flag_edge = false;
// 			for (auto child : node_race_always->children){
// 				switch(child->type){
// 					case AST_EDGE:
// 					//printf("In the level edge \n");
// 						flag_edge = true;
// 						break;

// 					case AST_POSEDGE:
// 					//printf("In the level edge \n");
// 						flag_posedge = true;
// 						break;

// 					case AST_NEGEDGE:
// 					//printf("In the level edge \n");
// 						flag_negedge = true;
// 						break;
					
// 					case AST_BLOCK:
// 						node_race_block=child;
// 						for (auto child:node_race_block->children){
// 							switch(child->type){
// 								case AST_CASE:
// 									//printf("We are here in case block \n");
// 									node_race_case = child;
// 									for (auto child:node_race_case->children){
// 										if(child->type == AST_COND){
// 											node_race_cond = child;
// 											//printf("We are here in cond \n");
// 											for (auto child:node_race_cond->children){
// 												if (child->type == AST_BLOCK){
// 													node_race_conBlock = child;
// 													for(auto child: node_race_conBlock->children){
// 														switch(child->type){
// 															case AST_ASSIGN_LE:
// 																//printf("we are in non-blocking assighnment \n");
// 																flag_nonblocking=true;
// 																node_assign_le = child;
// 																for (auto child: node_assign_le->children){
// 																	if (child->type == AST_IDENTIFIER){
// 																		identifier_name = child->str;
// 																	}
// 																}
// 																printf("%s", identifier_name.c_str());
// 																break;
															
// 															case AST_ASSIGN_EQ:
// 																printf("We are in blocking assignment \n");
// 																flag_blocking=true;
// 																node_assign_eq = child;
// 																for (auto child: node_assign_eq->children){
// 																	if (child->type == AST_IDENTIFIER){
// 																		identifier_name_eq = child->str;
// 																	}
// 																}
// 																printf("%s", identifier_name_eq.c_str());
// 																break;

// 															default:
// 																continue;
// 														}
// 													}


// 												}
// 											}

// 										}
// 									}
								
// 								default:
// 									continue;
// 							}					
// 						}
// 					default:
// 						break;
// 				}
// 			}
// 			c = c+1;
// 			printf("Yes we reached in a race check %d always block \n",c);
// 			if((flag_nonblocking == true) && (flag_blocking == true)){
// 				printf("This is bad coding practice of using both blocking and non blocking assignments in same always block\n" );
// 			}

// 			if(((flag_posedge == true) || (flag_negedge == true)) && (flag_blocking == true)){
// 				printf("This is bad coding practice of using blocking assignment in sequential block\n" );
// 			}

// 			if((flag_edge == true) && (flag_nonblocking == true)){
// 				printf("This is bad coding practice of using non-blocking assignment in combinational block\n" );
// 			}
// 		}
// 	}
// }
// }

//function to check whether the posedge and negedge arriving together
void rules()
{
	//printf("We are checking for edges here \n");
	//printf("*********************************************** \n");
	//checkingforedges();
    //design_check(design);
	//printf("*********************************************** \n");
	//printf("We are checking for race guidelines here \n");
	//printf("*********************************************** \n");
	//checkingforraceguidelines();
	//printf("*********************************************** \n");
	//current_ast->checking_rules_try(NULL, "    ");
	//print_vectors();

	for (auto itr = comb_latch_ff_details.begin(); itr != comb_latch_ff_details.end(); ++itr) {
        std::cout << itr->first
             << '\t' << itr->second << '\n';
    }
}

YOSYS_NAMESPACE_END
//Ending rules program 
//*************************************************************************************************************
