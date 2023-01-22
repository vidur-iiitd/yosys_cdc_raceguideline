// This code generates race_guideline 7 violation
// Don't provide posedge and negedge together in the sensitivity list of a single always block

module case7_pos (q, d1, clk, rst_n);
 output q;
 input d1, clk, rst_n;
 reg q;

 always @(posedge clk or negedge rst_n)
 if (!rst_n) q <= 1'b0;
 else q <= d1;
 
endmodule