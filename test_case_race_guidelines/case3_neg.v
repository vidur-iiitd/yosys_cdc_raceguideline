// This code is corrected version of violation of race_guideline 3
// Use of blocking assignment in combinational block.

module case3_neg (a,b,y);

input a,b;
output y;
reg y;

always @(a,b)
begin
	y = a&b;
end

endmodule