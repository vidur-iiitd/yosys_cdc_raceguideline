// This code is corrected version of violation of race_guideline 2
// Use of non-blocking assignment in sequential block - latch case.

module case2_neg (  input d,           
                  input en,            
                  input rstn,        
                  output reg q);      
  
   always @ (en or d)  
         if (en)  
            q <= d;  
endmodule