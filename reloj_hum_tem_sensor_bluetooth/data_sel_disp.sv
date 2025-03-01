module data_sel_disp(
    input logic clk,
    input logic arstn,
    input logic[7:0][3:0] time_Hh_Mm_Ss,
    input logic[7:0][3:0] humidity,
    input logic[7:0][3:0] temperature,
    output logic disp_time,
    output logic[3:0] dig0,  // data display 0 
    output logic[3:0] dig1,  // data display 1 
    output logic[3:0] dig2,  // data display 2 
    output logic[3:0] dig3,  // data display 3 
    output logic[3:0] dig4,  // data display 4 
    output logic[3:0] dig5,  // data display 5
    output logic[3:0] dig6,  // data display 6
    output logic[3:0] dig7   // data display 7 
);

    logic [28:0] clk_div;
    logic [1:0] data_sel;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            clk_div <= 0;
        else
            if(clk_div == 100000000) // 5s
                clk_div <= 0;
            else
                clk_div <= clk_div + 1;
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            data_sel <= 0;
        else
            if(clk_div == 100000000) // 5s
                if(data_sel == 2)
                    data_sel <= 0;
                else
                    data_sel <= data_sel + 1; 
    end
    

    always_comb begin
        case(data_sel)
            0: begin
                disp_time = 1;
                dig0 = time_Hh_Mm_Ss[0];
                dig1 = time_Hh_Mm_Ss[1];
                dig2 = time_Hh_Mm_Ss[2];
                dig3 = time_Hh_Mm_Ss[3];
                dig4 = time_Hh_Mm_Ss[4];
                dig5 = time_Hh_Mm_Ss[5];
                dig6 = time_Hh_Mm_Ss[6];
                dig7 = time_Hh_Mm_Ss[7];
            end
            1: begin
                disp_time = 0;
                dig0 = humidity[0];
                dig1 = humidity[1];
                dig2 = humidity[2];
                dig3 = humidity[3];
                dig4 = humidity[4];
                dig5 = humidity[5];
                dig6 = humidity[6];
                dig7 = humidity[7];
            end
            2: begin
                disp_time = 0;
                dig0 = temperature[0];
                dig1 = temperature[1];
                dig2 = temperature[2];
                dig3 = temperature[3];
                dig4 = temperature[4];
                dig5 = temperature[5];
                dig6 = temperature[6];
                dig7 = temperature[7];
            end
            default: begin
                disp_time = 0;
                dig0 = 4'b1111;
                dig1 = 4'b1111;
                dig2 = 4'b1111;
                dig3 = 4'b1111;
                dig4 = 4'b1111;
                dig5 = 4'b1111;
                dig6 = 4'b1111;
                dig7 = 4'b1111;
            end
        endcase
    end

endmodule