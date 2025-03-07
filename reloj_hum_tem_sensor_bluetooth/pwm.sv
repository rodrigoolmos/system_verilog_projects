module pwm_gen(
    input  logic clk,
    input  logic arstn,
    output logic pwm_sig
    );
    
    logic[13:0] cnt_pwm;
    logic[30:0] cnt_s;
    logic[15:0] end_cnt = 10000; // Tamaño del ciclo PWM
    const logic[30:0] end_cnt_s = 100000000; // Tamaño del ciclo PWM

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            cnt_pwm <= 0;
            pwm_sig <= 0;
        end else begin
            if (cnt_pwm == end_cnt - 1) begin
                cnt_pwm <= 0;            // Resetear el contador
                pwm_sig <= ~pwm_sig; // Invertir la señal PWM
            end else begin
                cnt_pwm <= cnt_pwm + 1;      // Incrementar el contador
            end        
        end        
    end
    
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            cnt_s <= 0;
            end_cnt <= 5000;
        end else begin
            if (cnt_s == end_cnt_s - 1) begin
                cnt_s <= 0;            
                if (end_cnt > 10000) begin
                    end_cnt <= 2500; 
                end else begin
                    end_cnt <= end_cnt + 2000;      
                end 
            end else begin
                cnt_s <= cnt_s + 1;
            end        
        end        
    end
    
endmodule
