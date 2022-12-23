#include "kernel/yosys.h"
#include "libs/sha1/sha1.h"
#include <stdarg.h>
//#include "frontends/verilog/verilog_frontend.h"

YOSYS_NAMESPACE_BEGIN
//using namespace VERILOG_FRONTEND;

void help_section(){
    log("\n");
    log("NB_SEQ \n");
    log("   Guideline #1: When modeling sequential logic, use nonblocking assignments \n");
    //log("Possible error \n");
    log("       Consider following example in which shift register is designed using blocking statement. \n");
    log("           always @(posedge clk) begin \n" );
    log("               q1 = d; \n");    
    log("               q2 = q1; \n");        
    log("               q3 = q2; \n");        
    log("           end \n");
    log("       The resultant synthesized model consist of only one flip flop due to the stratified event queue concept. \n");
    log("       Thus it is advisable and also safest to use non blocking assignments in such sequential blocks. \n");

    log("\n");
    log("NB_LATCH \n");
    log("   Guideline #2:  When modeling latches, use nonblocking assignments \n");
    log("       A similar analysis as of guideline 1 would show that it is also safest to use nonblocking assignments to model latches \n");

    log("\n");
    log("B_COMB \n");
    log("   Guideline #3: When modeling combinational logic with an always block, use blocking assignments. \n");
    log("       Consider following example in which shift register is designed using blocking statement. \n");
    log("           always @(a or b or c or d) begin \n");
    log("               tmp1 <= a & b; \n");    
    log("               tmp2 <= c & d; \n");        
    log("               y <= tmp1 | tmp2; \n");        
    log("           end \n");
    log("       The resultant program will not work because of the functioning of non-blocking assignments. To generate proper output \n");
    log("       we need to add tmp1 and tmp2 to sensitivity list which can have different complexity \n");
    log("       Thus it is advisable and also safest to use blocking assignments in such combinational blocks. \n");

    log("\n");
    log("NB_SEQ_COMB \n");
    log("   Guideline #4: When modeling both sequential and combinational logic within the same always block, use nonblocking assignments.\n");
    log("       This guideline is very useful when designing fsm. There are some forms of fsm in which designer needs to \n");
    log("       use both combinational as well as sequential block in single always block. \n");
    log("       Thus it is advisable and also safest to use non blocking assignments in such blocks. \n");
    log("       Designer can always use two different always block for the same. \n");

    log("\n");
    log("NO_B_NB \n");
    log("   Guideline #5: Do not mix blocking and nonblocking assignments in the same always block. \n");
    log("       This guideline generally do not cause any errors or discperancy in pre and post synthesis results provided \n");
    log("       both assignments are done to different variables. Synopsys tool will report error for the same. \n");
    log("       Thus it is advisable and also safest to use not use non blocking & blocking assignments in such blocks. \n");

    log("\n");
    log("NO_SAME_VAR \n");
    log("   Guideline #6: Do not make assignments to the same variable from more than one always block. \n");
    log("       The synopsys tool will give following warning for this practice: ");
    log("           Warning: there is 1 multiple-driver net with unknown wired-logic type \n");
    log("       Thus advisable to not assign values to same variable in different always block \n");

    log("\n");
    log("NO_POS_NEG_EDGE \n");
    log("   Guideline #7: Do not provide posedge and negedge together in the sensitivity list of a single always block. \n");
    log("       The reason behind this is, in every library FF's and Latches with such sensitivity list is not always available. \n");
    log("       Thus advisable to use only one edge in the sensitivity list of an always block. \n");

    YOSYS_NAMESPACE_END

}