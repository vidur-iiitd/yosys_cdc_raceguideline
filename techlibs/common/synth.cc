/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
//#include "techmap_extract.cc"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthPass : public ScriptPass
{
	SynthPass() : ScriptPass("synth", "generic synthesis script") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth [options]\n");
		log("\n");
		log("This command runs the default synthesis script. This command does not operate\n");
		log("on partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy\n");
		log("\n");
		log("    -flatten\n");
		log("        flatten the design before synthesis. this will pass '-auto-top' to\n");
		log("        'hierarchy' if no top module is specified.\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        passed to 'fsm_recode' via 'fsm'\n");
		log("\n");
		log("    -lut <k>\n");
		log("        perform synthesis for a k-LUT architecture.\n");
		log("\n");
		log("    -nofsm\n");
		log("        do not run FSM optimization\n");
		log("\n");
		log("    -noabc\n");
		log("        do not run abc (as if yosys was compiled without ABC support)\n");
		log("\n");
		log("    -noalumacc\n");
		log("        do not run 'alumacc' pass. i.e. keep arithmetic operators in\n");
		log("        their direct form ($add, $sub, etc.).\n");
		log("\n");
		log("    -nordff\n");
		log("        passed to 'memory'. prohibits merging of FFs into memory read ports\n");
		log("\n");
		log("    -noshare\n");
		log("        do not run SAT-based resource sharing\n");
		log("\n");
		log("    -run <from_label>[:<to_label>]\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("    -flowmap\n");
		log("        use FlowMap LUT techmapping instead of ABC\n");
		log("\n");
		log("\n");
		log("    -input\n");
		log("        use to define user defined asynchronous clocks for cdc check\n");
		log("        this attribute must be followed by endlist to mark end of list\n");
		log("\n");
		log("    -endlist\n");
		log("        use to mark end of cdc asynnchronous clock list\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, fsm_opts, memory_opts, abc;
	bool autotop, flatten, noalumacc, nofsm, noabc, noshare, flowmap;
	int lut;

	void clear_flags() override
	{
		top_module.clear();
		fsm_opts.clear();
		memory_opts.clear();

		autotop = false;
		flatten = false;
		lut = 0;
		noalumacc = false;
		nofsm = false;
		noabc = false;
		noshare = false;
		flowmap = false;
		abc = "abc";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();
		

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-encfile" && argidx+1 < args.size()) {
				fsm_opts = " -encfile " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			if (args[argidx] == "-auto-top") {
				autotop = true;
				continue;
			}
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			if (args[argidx] == "-lut") {
				lut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nofsm") {
				nofsm = true;
				continue;
			}
			if (args[argidx] == "-noabc") {
				noabc = true;
				continue;
			}
			if (args[argidx] == "-noalumacc") {
				noalumacc = true;
				continue;
			}
			if (args[argidx] == "-nordff") {
				memory_opts += " -nordff";
				continue;
			}
			if (args[argidx] == "-noshare") {
				noshare = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc = "abc9";
				continue;
			}
			if (args[argidx] == "-flowmap") {
				flowmap = true;
				continue;
			}
			if (args[argidx] == "-input") {
				argidx++;
				while(strcmp(args[argidx].c_str(), "-endlist")){
					argidx++;
				}
				// flowmap = true;
				continue;
			}
			if (args[argidx] == "-endlist") {
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc == "abc9" && !lut)
			log_cmd_error("ABC9 flow only supported for FPGA synthesis (using '-lut' option)\n");
		if (flowmap && !lut)
			log_cmd_error("FlowMap is only supported for FPGA synthesis (using '-lut' option)\n");

		log_header(design, "Executing SYNTH pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}
	
	void script() override
	{
		if (check_label("begin"))
		{
			if (help_mode) {
				run("hierarchy -check [-top <top> | -auto-top]");
			} else {
				if (top_module.empty()) {
					if (flatten || autotop){
						run("hierarchy -check -auto-top");
					}
					else{
						run("hierarchy -check");
					}
				} else{
					run(stringf("hierarchy -check -top %s", top_module.c_str()));
				}
			}
		}

		if (check_label("coarse"))
		{
			run("proc");
			if (help_mode || flatten)
				run("flatten", "  (if -flatten)");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			if (!nofsm)
				run("fsm" + fsm_opts, "      (unless -nofsm)");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			if (help_mode)
				run("techmap -map +/cmp2lut.v -map +/cmp2lcu.v", " (if -lut)");
			else if (lut)
				run(stringf("techmap -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=%d", lut));
			if (!noalumacc)
				run("alumacc", "  (unless -noalumacc)");
			if (!noshare)
				run("share", "    (unless -noshare)");
			run("opt");
			run("memory -nomap" + memory_opts);
			run("opt_clean");
		}

		if (check_label("fine"))
		{
			run("opt -fast -full");
			run("memory_map");
			run("opt -full");
			run("techmap");
			if (help_mode)
			{
				run("techmap -map +/gate2lut.v", "(if -noabc and -lut)");
				run("clean; opt_lut", "           (if -noabc and -lut)");
				run("flowmap -maxlut K", "        (if -flowmap and -lut)");
			}
			else if (noabc && lut)
			{
				run(stringf("techmap -map +/gate2lut.v -D LUT_WIDTH=%d", lut));
				run("clean; opt_lut");
			}
			else if (flowmap)
			{
				run(stringf("flowmap -maxlut %d", lut));
			}
			run("opt -fast");

			if (!noabc && !flowmap) {
		#ifdef YOSYS_ENABLE_ABC
				if (help_mode)
				{
					run(abc + " -fast", "       (unless -noabc, unless -lut)");
					run(abc + " -fast -lut k", "(unless -noabc, if -lut)");
				}
				else
				{
					if (lut)
						run(stringf("%s -fast -lut %d", abc.c_str(), lut));
					else
						run(abc + " -fast");
				}
				run("opt -fast", "       (unless -noabc)");
		#endif
			}
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check");
		}
	}
	
} SynthPass;

PRIVATE_NAMESPACE_END
