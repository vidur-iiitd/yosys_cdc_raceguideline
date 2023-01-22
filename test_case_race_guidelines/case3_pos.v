// This code generates race_guideline 3 violation.
// Use of blocking assignment in combinational block.

module case3_pos (a,b,y);

input a,b;
output y;
reg y;

always @(a,b)
begin
	y <= a&b;
end

endmodule