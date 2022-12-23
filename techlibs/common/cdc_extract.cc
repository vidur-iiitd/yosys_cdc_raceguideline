#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/mem.h"
#include <string>
#include <sstream>
#include <set>
#include <map>
#include <list>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

int auto_name_counter, auto_name_offset, auto_name_digits;
std::map<RTLIL::IdString, int> auto_name_map;
std::set<RTLIL::IdString> reg_wires;
std::string auto_prefix, extmem_prefix;

RTLIL::Module *active_module;
dict<RTLIL::SigBit, RTLIL::State> active_initdata;
SigMap active_sigmap;
IdString initial_id;

// definitions of vectors required for cdc checking
// std::vector <std::string> input_wires, output_wires, int_wires;
// std::list <std::multimap <std::string, std::string>> gates_list;
std::map <unsigned int, std::vector <unsigned int>> fan_out_details; // key is wire and value is cells connected to it
std::vector <unsigned int> visited_wires; //To store the visited wires
bool visited_tag = false; // For high complex thinking - checking whether a wire already visited or not
bool cdc_design = false; // To check whether the design contains any cdc or not.
std::vector <std::string> user_def_async_clk; // To store asynchronoous clk user defined in command line
bool ext_async_clk; // This boolean function is to denote whether the user defined external asynchronous clock sources
bool async1, async2; // This boolean variables are to check and determine about logic implementation
std::string gate_pins;
std::string gate_conn;
unsigned int id_conn;

void dump_const(const RTLIL::Const &data, int width = -1, int offset = 0, bool no_decimal = false, bool escape_comment = false)
{
	bool set_signed = (data.flags & RTLIL::CONST_FLAG_SIGNED) != 0;
	if (width < 0)
		width = data.bits.size() - offset;
	if (width == 0) {
		// See IEEE 1364-2005 Clause 5.1.14.
		//f << "{0{1'b0}}";
		return;
	}
	// if (nostr)
	// 	goto dump_hex;
	if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.bits.size()) {
		if (width == 32 ) {
			int32_t val = 0;
			for (int i = offset+width-1; i >= offset; i--) {
				log_assert(i < (int)data.bits.size());
				if (data.bits[i] != State::S0 && data.bits[i] != State::S1)
					goto dump_hex;
				if (data.bits[i] == State::S1)
					val |= 1 << (i - offset);
			}
			if (no_decimal)
				printf("%d", val);
			else if (set_signed && val < 0)
				printf("-32'sd%u", -val);
			else
				printf("32'%sd%u", set_signed ? "s" : "", val);
		} else {
	dump_hex:
			// if (nohex)
			// 	goto dump_bin;
			vector<char> bin_digits, hex_digits;
			for (int i = offset; i < offset+width; i++) {
				log_assert(i < (int)data.bits.size());
				switch (data.bits[i]) {
				case State::S0: bin_digits.push_back('0'); break;
				case State::S1: bin_digits.push_back('1'); break;
				case RTLIL::Sx: bin_digits.push_back('x'); break;
				case RTLIL::Sz: bin_digits.push_back('z'); break;
				case RTLIL::Sa: bin_digits.push_back('?'); break;
				case RTLIL::Sm: log_error("Found marker state in final netlist.");
				}
			}
			if (GetSize(bin_digits) == 0)
				goto dump_bin;
			while (GetSize(bin_digits) % 4 != 0)
				if (bin_digits.back() == '1')
					bin_digits.push_back('0');
				else
					bin_digits.push_back(bin_digits.back());
			for (int i = 0; i < GetSize(bin_digits); i += 4)
			{
				char bit_3 = bin_digits[i+3];
				char bit_2 = bin_digits[i+2];
				char bit_1 = bin_digits[i+1];
				char bit_0 = bin_digits[i+0];
				if (bit_3 == 'x' || bit_2 == 'x' || bit_1 == 'x' || bit_0 == 'x') {
					if (bit_3 != 'x' || bit_2 != 'x' || bit_1 != 'x' || bit_0 != 'x')
						goto dump_bin;
					hex_digits.push_back('x');
					continue;
				}
				if (bit_3 == 'z' || bit_2 == 'z' || bit_1 == 'z' || bit_0 == 'z') {
					if (bit_3 != 'z' || bit_2 != 'z' || bit_1 != 'z' || bit_0 != 'z')
						goto dump_bin;
					hex_digits.push_back('z');
					continue;
				}
				if (bit_3 == '?' || bit_2 == '?' || bit_1 == '?' || bit_0 == '?') {
					if (bit_3 != '?' || bit_2 != '?' || bit_1 != '?' || bit_0 != '?')
						goto dump_bin;
					hex_digits.push_back('?');
					continue;
				}
				int val = 8*(bit_3 - '0') + 4*(bit_2 - '0') + 2*(bit_1 - '0') + (bit_0 - '0');
				hex_digits.push_back(val < 10 ? '0' + val : 'a' + val - 10);
			}
			printf("%d'%sh", width, set_signed ? "s" : "");
			// for (int i = GetSize(hex_digits)-1; i >= 0; i--)
			// 	f << hex_digits[i];
		}
		if (0) {
	dump_bin:
			printf("%d'%sb", width, set_signed ? "s" : "");
			if (width == 0)
				printf("0");
			for (int i = offset+width-1; i >= offset; i--) {
				log_assert(i < (int)data.bits.size());
				switch (data.bits[i]) {
				case State::S0: printf("0"); break;
				case State::S1: printf("1"); break;
				case RTLIL::Sx: printf("x"); break;
				case RTLIL::Sz: printf("z"); break;
				case RTLIL::Sa: printf("?"); break;
				case RTLIL::Sm: log_error("Found marker state in final netlist.");
				}
			}
		}
	} else {
		if ((data.flags & RTLIL::CONST_FLAG_REAL) == 0)
			printf("\"");
		std::string str = data.decode_string();
		for (size_t i = 0; i < str.size(); i++) {
			if (str[i] == '\n')
				printf("\\n");
			else if (str[i] == '\t')
				printf("\\t");
			else if (str[i] < 32)
				printf("\\%03o", str[i]);
			else if (str[i] == '"')
				printf("\\\"");
			else if (str[i] == '\\')
				printf("\\\\");
			else if (str[i] == '/' && escape_comment && i > 0 && str[i-1] == '*')
				printf("\\/");
			// else
			// 	f << str[i];
		}
		if ((data.flags & RTLIL::CONST_FLAG_REAL) == 0)
			printf("\"");
	}
}

void reset_auto_counter_id(RTLIL::IdString id, bool may_rename)
{
	const char *str = id.c_str();

	bool norename = false;

	if (*str == '$' && may_rename && !norename)
		auto_name_map[id] = auto_name_counter++;

	if (str[0] != '\\' || str[1] != '_' || str[2] == 0)
		return;

	for (int i = 2; str[i] != 0; i++) {
		if (str[i] == '_' && str[i+1] == 0)
			continue;
		if (str[i] < '0' || str[i] > '9')
			return;
	}

	int num = atoi(str+2);
	if (num >= auto_name_offset)
		auto_name_offset = num + 1;
}

void reset_auto_counter(RTLIL::Module *module)
{
	auto_name_map.clear();
	auto_name_counter = 0;
	auto_name_offset = 0;

	bool verbose = false;
	 
	reset_auto_counter_id(module->name, false);

	for (auto w : module->wires())
		reset_auto_counter_id(w->name, true);

	for (auto cell : module->cells()) {
		reset_auto_counter_id(cell->name, true);
		reset_auto_counter_id(cell->type, false);
	}

	for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
		reset_auto_counter_id(it->second->name, false);

	auto_name_digits = 1;
	for (size_t i = 10; i < auto_name_offset + auto_name_map.size(); i = i*10)
		auto_name_digits++;

	if (verbose)
		for (auto it = auto_name_map.begin(); it != auto_name_map.end(); ++it)
			log("  renaming `%s' to `%s_%0*d_'.\n", it->first.c_str(), auto_prefix.c_str(), auto_name_digits, auto_name_offset + it->second);
}

// std::string next_auto_id()
// {
// 	return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_counter++);
// }

std::string id(RTLIL::IdString internal_id, bool may_rename = true)
{
	const char *str = internal_id.c_str();
	bool do_escape = false;

	if (may_rename && auto_name_map.count(internal_id) != 0)
		return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_map[internal_id]);

	if (*str == '\\')
		str++;

	if ('0' <= *str && *str <= '9')
		do_escape = true;

	for (int i = 0; str[i]; i++)
	{
		if ('0' <= str[i] && str[i] <= '9')
			continue;
		if ('a' <= str[i] && str[i] <= 'z')
			continue;
		if ('A' <= str[i] && str[i] <= 'Z')
			continue;
		if (str[i] == '_')
			continue;
		do_escape = true;
		break;
	}

	const pool<string> keywords = {
		// IEEE 1800-2017 Annex B
		"accept_on", "alias", "always", "always_comb", "always_ff", "always_latch", "and", "assert", "assign", "assume", "automatic", "before",
		"begin", "bind", "bins", "binsof", "bit", "break", "buf", "bufif0", "bufif1", "byte", "case", "casex", "casez", "cell", "chandle",
		"checker", "class", "clocking", "cmos", "config", "const", "constraint", "context", "continue", "cover", "covergroup", "coverpoint",
		"cross", "deassign", "default", "defparam", "design", "disable", "dist", "do", "edge", "else", "end", "endcase", "endchecker",
		"endclass", "endclocking", "endconfig", "endfunction", "endgenerate", "endgroup", "endinterface", "endmodule", "endpackage",
		"endprimitive", "endprogram", "endproperty", "endsequence", "endspecify", "endtable", "endtask", "enum", "event", "eventually",
		"expect", "export", "extends", "extern", "final", "first_match", "for", "force", "foreach", "forever", "fork", "forkjoin", "function",
		"generate", "genvar", "global", "highz0", "highz1", "if", "iff", "ifnone", "ignore_bins", "illegal_bins", "implements", "implies",
		"import", "incdir", "include", "initial", "inout", "input", "inside", "instance", "int", "integer", "interconnect", "interface",
		"intersect", "join", "join_any", "join_none", "large", "let", "liblist", "library", "local", "localparam", "logic", "longint",
		"macromodule", "matches", "medium", "modport", "module", "nand", "negedge", "nettype", "new", "nexttime", "nmos", "nor",
		"noshowcancelled", "not", "notif0", "notif1", "null", "or", "output", "package", "packed", "parameter", "pmos", "posedge", "primitive",
		"priority", "program", "property", "protected", "pull0", "pull1", "pulldown", "pullup", "pulsestyle_ondetect", "pulsestyle_onevent",
		"pure", "rand", "randc", "randcase", "randsequence", "rcmos", "real", "realtime", "ref", "reg", "reject_on", "release", "repeat",
		"restrict", "return", "rnmos", "rpmos", "rtran", "rtranif0", "rtranif1", "s_always", "s_eventually", "s_nexttime", "s_until",
		"s_until_with", "scalared", "sequence", "shortint", "shortreal", "showcancelled", "signed", "small", "soft", "solve", "specify",
		"specparam", "static", "string", "strong", "strong0", "strong1", "struct", "super", "supply0", "supply1", "sync_accept_on",
		"sync_reject_on", "table", "tagged", "task", "this", "throughout", "time", "timeprecision", "timeunit", "tran", "tranif0", "tranif1",
		"tri", "tri0", "tri1", "triand", "trior", "trireg", "type", "typedef", "union", "unique", "unique0", "unsigned", "until", "until_with",
		"untyped", "use", "uwire", "var", "vectored", "virtual", "void", "wait", "wait_order", "wand", "weak", "weak0", "weak1", "while",
		"wildcard", "wire", "with", "within", "wor", "xnor", "xor",
	};
	if (keywords.count(str))
		do_escape = true;

	if (do_escape)
		return "\\" + std::string(str) + " ";
	return std::string(str);
}

std::string cellname(RTLIL::Cell *cell)
{
	if (cell->name[0] == '$' && RTLIL::builtin_ff_cell_types().count(cell->type) && cell->hasPort(ID::Q) && !cell->type.in(ID($ff), ID($_FF_)))
	{
		RTLIL::SigSpec sig = cell->getPort(ID::Q);
		if (GetSize(sig) != 1 || sig.is_fully_const())
			goto no_special_reg_name;

		RTLIL::Wire *wire = sig[0].wire;

		if (wire->name[0] != '\\')
			goto no_special_reg_name;

		std::string cell_name = wire->name.str();

		size_t pos = cell_name.find('[');
		if (pos != std::string::npos)
			cell_name = cell_name.substr(0, pos) + "_reg" + cell_name.substr(pos);
		else
			cell_name = cell_name + "_reg";

		if (wire->width != 1)
			cell_name += stringf("[%d]", wire->start_offset + sig[0].offset);

		if (active_module && active_module->count_id(cell_name) > 0)
				goto no_special_reg_name;

		return id(cell_name);
	}
	else
	{
no_special_reg_name:
		return id(cell->name).c_str();
	}
}

void dump_sigchunk(const RTLIL::SigChunk &chunk)
{
	if (chunk.wire == NULL) {
		dump_const(chunk.data, chunk.width, chunk.offset);
        printf(" ");
	} else {
		if (chunk.width == chunk.wire->width && chunk.offset == 0) {
			gate_conn = id(chunk.wire->name).c_str();
			id_conn = chunk.wire->hashidx_;
		} else if (chunk.width == 1) {
			if (chunk.wire->upto){
				gate_conn = id(chunk.wire->name).c_str();
				id_conn = chunk.wire->hashidx_;

			}
			else{
				gate_conn= id(chunk.wire->name).c_str();
				id_conn = chunk.wire->hashidx_;
			}
		} else {
			if (chunk.wire->upto){
				gate_conn = id(chunk.wire->name).c_str();
				id_conn = chunk.wire->hashidx_;
			}
			else {
				gate_conn = id(chunk.wire->name).c_str();
				id_conn = chunk.wire->hashidx_;
			}
		}
	}
}

void dump_sigspec(const RTLIL::SigSpec &sig)
{
	// if (GetSize(sig) == 0) {
	// 	// See IEEE 1364-2005 Clause 5.1.14.
	// 	f << "{0{1'b0}}";
	// 	return;
	// }
	if (sig.is_chunk()) {
		dump_sigchunk(sig.as_chunk());
	} else {
		//printf("{ ");
		for (auto it = sig.chunks().rbegin(); it != sig.chunks().rend(); ++it) {
			if (it != sig.chunks().rbegin())
				printf(", ");
			dump_sigchunk(*it);
		}
		//printf(" }");
	}
}

// void dump_wire(RTLIL::Wire *wire)
// {
// 	//dump_attributes(wire->attributes, '\n', /*regattr=*/reg_wires.count(wire->name));
// 	// do not use Verilog-2k "output reg" syntax in Verilog export
// 	std::string range = "";
// 	if (wire->width != 1) {
// 		if (wire->upto)
// 			range = stringf(" [%d:%d]", wire->start_offset, wire->width - 1 + wire->start_offset);
// 		else
// 			range = stringf(" [%d:%d]", wire->width - 1 + wire->start_offset, wire->start_offset);
// 	}
// 	if (wire->port_input && !wire->port_output)
// 		input_wires.push_back(id(wire->name).c_str());
// 	if (!wire->port_input && wire->port_output)
// 		output_wires.push_back(id(wire->name).c_str());
// 	if (wire->port_input && wire->port_output)
// 		printf("inout%s %s;\n",  range.c_str(), id(wire->name).c_str());
// 	if (reg_wires.count(wire->name)) {
// 		printf("reg%s %s",  range.c_str(), id(wire->name).c_str());
// 		if (wire->attributes.count(ID::init)) {
// 			printf(" = ");
// 			dump_const(wire->attributes.at(ID::init));
// 		}
// 		printf(";\n");
// 	} else if (!wire->port_input && !wire->port_output)
// 		int_wires.push_back(id(wire->name).c_str());

// }
// bool synchronizers_cdc(RTLIL::Module *module, std::string cell_name_comp, std::string q_sync, std::string clk_comp){
// 	std::string clk_found;
// 	// This following loop will iterate among the cells to give whether the cdc affected reg is connected to 
// 	// different register to form a two level synchronizers
// 	for(auto cell: module->cells()){
// 		std::string cell_name_found = cellname(cell);
// 		if(strcmp(cell_name_found.c_str(), cell_name_comp.c_str()) && cell_name_found != id(cell->name)){
// 			for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
// 				if (it->second.size() > 0)
// 					dump_sigspec(it->second); // this function giving the details of pin connections

// 				if(!strcmp("C",id(it->first).c_str()))
// 					clk_found = gate_conn;

// 				if(!strcmp("D",id(it->first).c_str()))
// 					if(!strcmp(q_sync.c_str(), gate_conn.c_str()) && (!strcmp(clk_found.c_str(),clk_comp.c_str())))
// 						return true;
// 			}
// 		}
// 	}
// 	return false;
// }

//The following function is forward traversal of cddc check
// int cdc_check_fwd(RTLIL::Module *module, std::string cell_name_comp,std::string gate_conn_comp, std::string clk_comp){
// 	bool comb_connection_found = false; // boolean function to be set for combinational gate
// 	bool synchronizer_present = false; // boolean function to be set if two-level synchronizers is present 
// 	bool cdc_found =  false; // boolean for cdc found
// 	std::string clk_found;

// 	for(auto cell: module->cells()){
// 		std::string cell_name_found = cellname(cell);
// 		if(strcmp(cell_name_found.c_str(), cell_name_comp.c_str())){
// 			for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
// 				if (it->second.size() > 0)
// 					dump_sigspec(it->second); // this function giving the details of pin connections

// 				if (cell_name_found != id(cell->name)){
// 					// Clock of gate from which we are comparing the passed gate in instance where signal matches
// 					if(!strcmp("C",id(it->first).c_str())){
// 						clk_found = gate_conn;
// 					}
// 					//comparision with flip flop
// 					if(!strcmp(gate_conn.c_str(), gate_conn_comp.c_str()) && strcmp(clk_found.c_str(),clk_comp.c_str()))
// 						cdc_found = true;

// 					// This extra condition is is incorporated beacuse of the sorting nature of storing of dictionary
// 					// Q pin will be stored after the D pin connection
// 					if(cdc_found && !strcmp("Q", id(it->first).c_str())){
// 						cdc_found = false;
// 						synchronizer_present = synchronizers_cdc (module, cell_name_found, gate_conn, clk_found);
// 						if(!synchronizer_present){
// 							printf("cdc found between %s & %s \n",cell_name_comp.c_str(), cell_name_found.c_str());
// 							printf("%s <- %s \n",clk_comp.c_str(), clk_found.c_str());
// 							return 0;
// 						}
// 					}
// 				}
// 				else{
// 					if (it->second.size() > 0)
// 						dump_sigspec(it->second); // this function giving the details of pin connections
					
// 					// The following iteration is when a connection is found in combinational gate 
// 					if(comb_connection_found && !strcmp("Y",id(it->first).c_str())){
// 						comb_connection_found = false;
// 						cdc_check_fwd(module, cell_name_comp, gate_conn , clk_comp);	
// 					}

// 					if(!strcmp(gate_conn.c_str(), gate_conn_comp.c_str()))
// 						comb_connection_found  = true;
// 				}
// 			}
// 		}
// 	}
// 	return 0;
// }

// int cdc_check(RTLIL::Module *module, std::string cell_name_comp,std::string gate_conn_comp, std::string clk_comp){
// 	long unsigned int i = 0 ;
// 	for(i=0; i<input_wires.size(); i++){
// 		if(!strcmp(gate_conn_comp.c_str(),input_wires[i].c_str())){
// 			return 0;
// 		}
// 	}
// 	std::string clk_found;
// 	std::map <std::string, std::string> comb_gate_conn;
// 	for(auto cell: module->cells()){
// 		std::string cell_name_found = cellname(cell);
// 		if(strcmp(cell_name_found.c_str(), cell_name_comp.c_str())){
// 			for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
// 				if (it->second.size() > 0)
// 					dump_sigspec(it->second); // this function giving the details of pin connections
// 				if (cell_name_found != id(cell->name)){
// 					// Clock of gate from which we are comparing the passed gate in instance where signal matches
// 					if(!strcmp("C",id(it->first).c_str())){
// 						clk_found = gate_conn;
// 					}
// 					//comparision with flip flop
// 					if(!strcmp(gate_conn.c_str(), gate_conn_comp.c_str()) && strcmp(clk_found.c_str(),clk_comp.c_str())){
// 							printf("cdc found between %s & %s \n",cell_name_found.c_str(), cell_name_comp.c_str());
// 							printf("%s <- %s \n",clk_found.c_str(),clk_comp.c_str());
// 							return 0;
// 					}
// 				}
// 				else{
// 					if (it->second.size() > 0)
// 						dump_sigspec(it->second); // this function giving the details of pin connections				
// 					if(!strcmp("Y",id(it->first).c_str())){
// 						if(!strcmp(gate_conn.c_str(), gate_conn_comp.c_str())){
// 							for(auto check = comb_gate_conn.begin(); check != comb_gate_conn.end(); ++check)
// 								cdc_check(module, cell_name_comp, check->second.c_str() , clk_comp);
// 						}
// 					}
// 					else{
// 						comb_gate_conn.emplace(id(it->first).c_str(), gate_conn);
// 					}
// 				}
// 			}
// 		}
// 		// printf("%s \n",cell_comp.c_str());
// 	}
// 	//printf("%s \n", gate_conn.c_str());
// 	comb_gate_conn.clear();
// 	return 0;
// }
void checking_id(RTLIL::Module *module){

	std::multimap <unsigned int, unsigned int> cell_hash; // key is wire hash_id and value is cell_hashid
	// Following loop is creating map with corresponding wire connected to cell pins and cell hash id
	for (auto cell : module ->cells()){
		for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
			if (it->second.size() > 0)
				dump_sigspec(it->second); // this function giving the details of pin connecti
			cell_hash.emplace(id_conn, cell->hashidx_);
		}			
	}

	std::vector<unsigned int> temp_vector;
	// Following loop will create the required map which can store wires as the key and corresponding cell
	for(auto w: module->wires()){
		for(auto itr=cell_hash.begin(); itr!=cell_hash.end(); ++itr) {
			if(itr->first == w->hashidx_){
				temp_vector.push_back(itr->second);
			}
		}
		if(temp_vector.size() > 1)
			fan_out_details.emplace(w->hashidx_,temp_vector);
		temp_vector.clear();
	}
	cell_hash.clear();
}

//For two level synchronizers 
bool synchronizers(RTLIL::Module *module, const RTLIL::SigSpec &sig, RTLIL::Cell *cell_comp, unsigned int cell_hash_id){
	std::string clk_comp; //storing clock of cell which has to be compared
	std::string clk_found_sync; //storing clock of found cell
	unsigned int wire_to_be_search;
	dump_sigspec(sig);
	wire_to_be_search = id_conn;
	//std::cout << "hello" << id_conn << std::endl;
	std::vector <unsigned int> temp_vector; // vector for storing the corresponding cell details of a wire
	for(auto it=fan_out_details.begin(); it!=fan_out_details.end(); ++it){
		//std::cout << it->first << std::endl;
		if(it->first == id_conn){
			temp_vector = it ->second;
			// std::cout << "checking return criterion : " << wire_to_be_search << std::endl;
			break;
		}
		// else //The function is returned from here mostly because the wire passed in the functionn have atmost one connection
		// 	return 0;
	}
	if(temp_vector.size() == 0)
		return 0;

	std::string cell_name_comp = cellname(cell_comp);
	for(auto it = cell_comp->connections().begin(); it != cell_comp->connections().end(); ++it) {
		if(!strcmp("C",id(it->first).c_str()))
			if(it->second.size()>0){
				dump_sigspec(it->second);
				clk_comp = gate_conn;
				break;
			}		
	}
	for (long unsigned int i=0; i<temp_vector.size(); i++){
		for(auto cell: module->cells()){
			if(temp_vector[i] == cell->hashidx_ && temp_vector[i] != cell_hash_id) {
				std::string cell_name_found = cellname(cell);
				// std::cout << "cell_is passed to function : " << cell_comp->hashidx_ << std::endl;
				// std::cout << "wire connected to : " << cell_name << std::endl;
				for(auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
					if (cell_name_found != id(cell->name)){
						if(!strcmp("C",id(it->first).c_str()))
							if(it->second.size() > 0)
								dump_sigspec(it->second);
						clk_found_sync = gate_conn;

						if(!strcmp("D",id(it->first).c_str()))
							if(it->second.size() > 0)
								dump_sigspec(it->second);

						if(id_conn == wire_to_be_search && !strcmp(clk_found_sync.c_str(),clk_comp.c_str()))
							return true;
					}
				}
			}
		}
	}
	return false;
}

//Trying new function for cdc_check incorporating the fan_out_details
int cdc_check_fanout(RTLIL::Module *module, const RTLIL::SigSpec &sig, RTLIL::Cell *cell_comp, unsigned int cell_hash_id){
	std::string clk_comp; //storing clock of cell which has to be compared
	std::string clk_found; //storing clock of found cell
	bool cdc_found = false;
	unsigned int wire_to_be_search;
	dump_sigspec(sig);
	wire_to_be_search = id_conn; //This id_conn will be corresponding to wire id which needs to be searched
	std::vector <unsigned int> temp_vector; // vector for storing the corresponding cell details of a wire
	for(auto it=fan_out_details.begin(); it!=fan_out_details.end(); ++it){
		if(it->first == id_conn){
			visited_wires.push_back(it->first); //This visited wire will store all the wires visited so that infinite loop can be avoided
			temp_vector = it ->second;
			break;
		}
	}
	if(temp_vector.size() == 0)
		return false;

	// The following block will extract the clk_name of the cell we are parsing
	std::string cell_name_comp = cellname(cell_comp);
	for(auto it = cell_comp->connections().begin(); it != cell_comp->connections().end(); ++it) {
		if(!strcmp("C",id(it->first).c_str()))
			if(it->second.size()>0){
				dump_sigspec(it->second);
				clk_comp = gate_conn;
				break;
			}		
	}

	// The following is loop on temp_vector i.e, only those cells will be evaluated connected to the wire under consideration
	for (long unsigned int i=0; i<temp_vector.size(); i++){
		for(auto cell: module->cells()){
			if(temp_vector[i] == cell->hashidx_ && temp_vector[i] != cell_hash_id) {
				std::string cell_name_found = cellname(cell);
				for(auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
					if (cell_name_found != id(cell->name)){ // for flip flops
						//For reading the clock of the cell found
						if(!strcmp("C",id(it->first).c_str()))
							if(it->second.size() > 0){
								dump_sigspec(it->second);
								clk_found = gate_conn;
							}

						// For reading the input of the flip flop
						if(!strcmp("D",id(it->first).c_str()))
							if(it->second.size() > 0)
								dump_sigspec(it->second);

						// Checking for the connections and cell_name to comment on cdc
						if(id_conn == wire_to_be_search && strcmp(clk_found.c_str(),clk_comp.c_str()))
							cdc_found = true;
						
						// This checks for synchronizers
						if(!strcmp("Q",id(it->first).c_str()) && cdc_found){
							if(it->second.size() > 0)
								if(!synchronizers(module,it->second,cell,cell->hashidx_)){
									cdc_found = false;
									cdc_design = true;
									std::cout << "cdc found between " << cell_name_found << " & " << cell_name_comp << std::endl; 
									std::cout << clk_found << "<-" << clk_comp << std::endl;
									return 0;
								}
						}
					}
					// This else block will be used in case of combinational block between flip flops.
					else{
						if(!strcmp("Y",id(it->first).c_str()))
							if(it->second.size() > 0){
								dump_sigspec(it->second);
								for(long unsigned int i=0; i<visited_wires.size(); i++)
									if(id_conn == visited_wires[i])
										visited_tag = true;
								
								if(!visited_tag)
									cdc_check_fanout(module, it->second, cell_comp, cell->hashidx_);
								visited_tag = false;
							}					
					}
				}
			}
		}
	}
	return 0;
}

//Trying new function for cdc_check incorporating the fan_out_details and external assync clock sources
int cdc_check_fanout_ext(RTLIL::Module *module, const RTLIL::SigSpec &sig, RTLIL::Cell *cell_comp, unsigned int cell_hash_id,
						bool async1)
{
	bool cdc_found = false;
	unsigned int wire_to_be_search;
	dump_sigspec(sig);
	wire_to_be_search = id_conn; //This id_conn will be corresponding to wire id which needs to be searched
	std::vector <unsigned int> temp_vector; // vector for storing the corresponding cell details of a wire
	for(auto it=fan_out_details.begin(); it!=fan_out_details.end(); ++it){
		if(it->first == id_conn){
			visited_wires.push_back(it->first); //This visited wire will store all the wires visited so that infinite loop can be avoided
			temp_vector = it ->second;
			break;
		}
	}
	if(temp_vector.size() == 0)
		return false;

	// The following block will extract the clk_name of the cell we are parsing
	std::string cell_name_comp = cellname(cell_comp);

	// The following is loop on temp_vector i.e, only those cells will be evaluated connected to the wire under consideration
	for (long unsigned int i=0; i<temp_vector.size(); i++){
		for(auto cell: module->cells()){
			if(temp_vector[i] == cell->hashidx_ && temp_vector[i] != cell_hash_id) {
				std::string cell_name_found = cellname(cell);
				for(long unsigned int i=0; i<user_def_async_clk.size(); i++){
					if(!strcmp(user_def_async_clk[i].c_str(), cell_name_found.c_str())){
						async2 = true;
						break;
					}
					else
						async2= false;
				}
				// std::cout << cell_name_comp << ":" << cell_name_found << std::endl;
				for(auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
					if (cell_name_found != id(cell->name)){ // for flip flops
						// For reading the input of the flip flop
						if(!strcmp("D",id(it->first).c_str()))
							if(it->second.size() > 0)
								dump_sigspec(it->second);

						// Checking for the connections and cell_name to comment on cdc
						if(id_conn == wire_to_be_search && async1==async2)
							cdc_found = true;
						
						// This checks for synchronizers
						if(!strcmp("Q",id(it->first).c_str()) && cdc_found){
							if(it->second.size() > 0){
								if(!synchronizers(module,it->second,cell,cell->hashidx_)){
									cdc_found = false;
									cdc_design = true;
									std::cout << "cdc found between " << cell_name_found << " & " << cell_name_comp << std::endl; 
									// std::cout << clk_found << "<-" << clk_comp << std::endl;
									return 0;
								}
								else
									std::cout << "synchronizer found" <<std::endl;
							}
						}
					}
					// This else block will be used in case of combinational block between flip flops.
					else{
						if(!strcmp("Y",id(it->first).c_str()))
							if(it->second.size() > 0){
								dump_sigspec(it->second);
								for(long unsigned int i=0; i<visited_wires.size(); i++)
									if(id_conn == visited_wires[i])
										visited_tag = true;
								
								if(!visited_tag)
									cdc_check_fanout_ext(module, it->second, cell_comp, cell->hashidx_, async1);
								visited_tag = false;
							}					
					}
				}
			}
		}
	}
	return 0;
}

//This function is used to read the connections of the cell 
void dump_cell(RTLIL::Cell *cell, RTLIL::Module *module){
    std::string cell_name = cellname(cell);
	
	if (cell_name != id(cell->name)){ //This if condition is for flip flops!!
		//Following for loop will traverse to every pins and its connection of the corresponding cell
    	for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
			// Following snippet of code will invoke forward traversing for cdc_check
			if(!strcmp("Q",id(it->first).c_str())){
				if(it->second.size()>0){
					if(!ext_async_clk) // Condition to check on the basis of different clock names
						cdc_check_fanout(module, it->second, cell, cell->hashidx_);	
					else{ // Condition to check on the basis of user input asynchronous clock
						for(long unsigned int i=0; i<user_def_async_clk.size(); i++){
							if(!strcmp(user_def_async_clk[i].c_str(), cell_name.c_str())){
								async1 = true;
								break;
							}
							else{
								async1= false;
							}
						}
						visited_wires.clear(); // Technical clearance of visited_wires based on ddd 
						cdc_check_fanout_ext(module, it->second, cell, cell->hashidx_,async1); 

					}
				}	
			}
    	}
	}  
}

void dump_module(RTLIL::Module *module){
    reg_wires.clear();
	reset_auto_counter(module);
	active_module = module;
	active_sigmap.set(module);
	active_initdata.clear();
	checking_id(module); //function calling for fan_out details - forms wire-cell mapping
	bool keep_running = true;
	// Following loop will assign different port ids to wires based on their definition in module
	for (int port_id = 1; keep_running; port_id++) {
		keep_running = false;
		for (auto wire : module->wires()) {
			if (wire->port_id == port_id) {
				keep_running = true;
				continue;
			}
		}
	}

	// for (auto cell : module->cells()){
	// 	std::string cell_name = cellname(cell);
	// 	std::cout << "cell used  ::" << cell_name << std::endl;
	// }

    for (auto cell : module->cells())
        dump_cell(cell,module);
	
}

void cdc_extract(RTLIL::Design *design, std::vector <std::string> &args)
{
    auto_name_map.clear();
	reg_wires.clear();
	fan_out_details.clear();
	visited_wires.clear();
	user_def_async_clk.clear();
	ext_async_clk = false;
	async1 = false;
	async2 = false;

	for(long unsigned int i=0; i<args.size(); i++){
		// std::cout << "Checking " << args[i] << std::endl;
		if(!strcmp(args[i].c_str(), "-input")){
			ext_async_clk = true;
			i++;
			while(strcmp(args[i].c_str(), "-endlist")){
				//std::cout << "Checking " << args[i] << std::endl;
				user_def_async_clk.push_back(args[i]);
				i++;
			}
		}
	}

	// for (long unsigned int j=0; j<user_def_async_clk.size(); j++)
	// 	std::cout << "baby " << user_def_async_clk[j] << std::endl;
	

	Pass::call(design, "clean_zerowidth");

	std::cout << "**************************************************************************************" << std::endl;
	std::cout << "The cdc report for the design starts here" << std::endl;

	design->sort();
    for (auto module : design->modules()) {
        dump_module(module);
    }
	// If design doesn't have cdc
	if(!cdc_design)
		std::cout << "The design under consideration is free from cdc" << std::endl;

	std::cout << "The cdc report for the design stop here" << std::endl;
	std::cout << "**************************************************************************************" << std::endl;
	
	
	visited_tag = false;
	visited_wires.clear();
	auto_name_map.clear();
	reg_wires.clear();
	fan_out_details.clear();
	user_def_async_clk.clear();

}
PRIVATE_NAMESPACE_END