// This code generates race_guideline 6 violation
// Don't assign to same variable in different always block.

module case6_pos(a,b,D, clk, rst, q1);

input D,clk, rst,a,b;
output q1;
reg q1;

always @(posedge clk)
begin
	D <= a&b;
end

always @(posedge clk)
begin
	D <= a^b;
end

endmodule