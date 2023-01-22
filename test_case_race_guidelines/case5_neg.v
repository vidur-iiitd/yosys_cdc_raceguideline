// This code is corrected version of violation of race_guideline 5
// Don't use non-blocking & blocking assignment in single always block.

module case5_neg(a,b,D, clk, rst, q1);

input D,clk, rst,a,b;
output q1;
reg q1;

always @(posedge clk)
begin
	D <= a&b;
	q1 <= D;
end

endmodule
