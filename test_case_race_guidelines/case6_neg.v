// This code is corrected version of violation of race_guideline 6
// Don't assign to same variable in different always block.

module case6_neg(a,b,D, clk, rst, q1);

input D,clk, rst,a,b;
output q1;
reg q1;

always @(posedge clk)
begin
	D <= a&b;
end

always @(posedge clk)
begin
	q1 <= a^b;
end

endmodule