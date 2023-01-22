// This code is corrected version of violation of race_guideline 7
// Don't provide posedge and negedge together in the sensitivity list of a single always block.


module case7_neg (q, d1, clk, rst_n);
 output q;
 input d1, clk, rst_n;
 reg q;

 always @(posedge clk)
 if (!rst_n) q <= 1'b0;
 else q <= d1;
 
endmodule