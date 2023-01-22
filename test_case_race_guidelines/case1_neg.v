// This code is corrected version of violation of race_guideline 1
// Use of non-blocking assignment in sequential block.

module case1_neg(D, clk, rst, q1);

input D, clk, rst;
output q1;
reg q1;

always @(posedge clk)
begin
	q1 <= D;
end

endmodule