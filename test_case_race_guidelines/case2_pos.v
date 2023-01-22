// This code generates race_guideline 2 violation.
// Use of non-blocking assignment in sequential block - latch.

module case2_pos (  input d,           
                  input en,            
                  input rstn,        
                  output reg q);      
  
   always @ (en or d)  
         if (en)  
            q = d;  
endmodule