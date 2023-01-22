// This code generates race_guideline 5 violation
// Don't use non-blocking & blocking assignment in single always block.

// This code by default also violates race guideline 1 - non-bloocking
// assignment in sequential block.

module case5_pos(a,b,D, clk, rst, q1);

input D,clk, rst,a,b;
output q1;
reg q1;

always @(posedge clk)
begin
	D = a&b;
	q1 <= D;
end

endmodule