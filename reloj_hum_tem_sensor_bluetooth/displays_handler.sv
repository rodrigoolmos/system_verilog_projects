module display_handler(
    input logic clk,
    input logic arstn,
    input logic[3:0] dig0,  // data display 0 
    input logic[3:0] dig1,  // data display 1 
    input logic[3:0] dig2,  // data display 2 
    input logic[3:0] dig3,  // data display 3 
    input logic[3:0] dig4,  // data display 4 
    input logic[3:0] dig5,  // data display 5
    input logic[3:0] dig6,  // data display 6
    input logic[3:0] dig7,  // data display 7 
    input logic[5:0] position,
    output logic DP,
    output logic[7:0] display_mux,
    output logic[7:0] display_data
);


    logic[15:0] clk_div;
    logic[3:0] coded_dis;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            clk_div <= 0;
        else
            clk_div <= clk_div + 1;
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            display_mux <= 8'b11111110;
        else if (clk_div == 19'b1)
            display_mux <= {display_mux[6:0], display_mux[7]};
    end
    
    // display decoders
    always_comb begin
        unique case (coded_dis)
                                //gfedcba
            0: display_data <= 7'b1000000;
            1: display_data <= 7'b1111001;
            2: display_data <= 7'b0100100;
            3: display_data <= 7'b0110000;
            4: display_data <= 7'b0011001;
            5: display_data <= 7'b0010010;
            6: display_data <= 7'b0000010;
            7: display_data <= 7'b1111000;
            8: display_data <= 7'b0000000;
            9: display_data <= 7'b0010000;
            10: display_data <= 7'b0001001; // H
            11: display_data <= 7'b0000011;
            12: display_data <= 7'b1000110;
            13: display_data <= 7'b0100001;
            14: display_data <= 7'b1111111; // off
            15: display_data <= 7'b0111111; // -
            default: display_data <= 7'b1111111;
        endcase
    end

    always_comb begin
        unique case (display_mux)
            8'b11111110: coded_dis <= dig0;
            8'b11111101: coded_dis <= dig1;
            8'b11111011: coded_dis <= dig2;
            8'b11110111: coded_dis <= dig3;
            8'b11101111: coded_dis <= dig4;
            8'b11011111: coded_dis <= dig5;
            8'b10111111: coded_dis <= dig6;
            8'b01111111: coded_dis <= dig7;
            default: coded_dis <= 1'bXXXX;
        endcase
    end

    always_comb DP <= (~display_mux[5:0] & position) ? 0 : 1;

endmodule