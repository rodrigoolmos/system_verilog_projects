module counter_h_m_s(
    input  logic clk,
    input  logic arstn,
    input  logic clock_ena,
    input  logic[5:0] position,
    input  logic incre,
    input  logic decre,
    input  logic load,
    input  logic[5:0][7:0] time_h_m_s,
    output logic[1:0] d_hours,
    output logic[3:0] u_hours,
    output logic[3:0] d_min,
    output logic[3:0] u_min,
    output logic[3:0] d_seg,
    output logic[3:0] u_seg

);
    
    logic end_d_hours;
    logic end_u_hours;
    logic end_d_min;
    logic end_u_min;
    logic end_d_seg;
    logic end_u_seg;
    logic[26:0] cnt_scaler;
    logic end_cnt_scaler;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            cnt_scaler <= 0;
        else if(clock_ena)
            if(end_cnt_scaler)
                cnt_scaler <= 0;
            else
                cnt_scaler <= cnt_scaler + 1;
    end
    always_comb end_cnt_scaler <= cnt_scaler == 99999999 ? 1'b1 : 1'b0;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            u_seg <= 0;
        else if (load) begin
            if(time_h_m_s[0][3:0] <= 9)
                u_seg <= time_h_m_s[0][3:0];
        end else if(end_cnt_scaler && clock_ena)
            if(end_u_seg)
                u_seg <= 0;
            else
                u_seg <= u_seg + 1;
        else if(position[0] == 1)
            if (u_seg < 9 && incre)
                u_seg <= u_seg + 1;
            else if (u_seg > 0 && decre)
                u_seg <= u_seg - 1;
    end
    always_comb end_u_seg <= u_seg == 9 && end_cnt_scaler ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            d_seg <= 0;
        else if (load) begin
            if(time_h_m_s[1][3:0] <= 5)
                d_seg <= time_h_m_s[1][3:0];
        end else if(end_u_seg && clock_ena)
            if(end_d_seg)
                d_seg <= 0;
            else
                d_seg <= d_seg + 1;
        else if(position[1] == 1)
            if (d_seg < 5 && incre)
                d_seg <= d_seg + 1;
            else if(d_seg > 0 && decre)
                d_seg <= d_seg - 1;
    end
    always_comb end_d_seg <= d_seg == 5 && end_u_seg ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            u_min <= 0;
        else if (load) begin
            if(time_h_m_s[2][3:0] <= 9)
                u_min <= time_h_m_s[2][3:0];
        end else if(end_d_seg && clock_ena)
            if(end_u_min)
                u_min <= 0;
            else
                u_min <= u_min + 1;
        else if(position[2] == 1)
            if(u_min < 9 && incre)
                u_min <= u_min + 1;
            else if(u_min > 0 && decre)
                u_min <= u_min - 1;
    end
    always_comb end_u_min <= u_min == 9 && end_d_seg ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            d_min <= 0;
        else if (load) begin
            if(time_h_m_s[3][3:0] <= 5)
                d_min <= time_h_m_s[3][3:0];
        end else if(end_u_min && clock_ena)
            if(end_d_min)
                d_min <= 0;
            else
                d_min <= d_min + 1;
        else if(position[3] == 1)
            if(d_min < 5 && incre)
                d_min <= d_min + 1;
            else if(d_min > 0 && decre)
                d_min <= d_min - 1;
    end
    always_comb end_d_min <= d_min == 5 && end_u_min ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            u_hours <= 0;
        else if (load) begin
            if(time_h_m_s[4][3:0] <= 9 && time_h_m_s[5][3:0] < 2 || time_h_m_s[4][3:0] <= 3 && time_h_m_s[5][3:0] == 2)
                u_hours <= time_h_m_s[4][3:0];
        end else if(end_d_min && clock_ena)
            if(end_u_hours)
                u_hours <= 0;
            else
                u_hours <= u_hours + 1;
        else if(position[4] == 1)
            if(((u_hours < 9 && d_hours < 2) || (u_hours < 3)) && incre)
                u_hours <= u_hours + 1;
            else if(u_hours > 0 && decre)
                u_hours <= u_hours - 1;
    end
    always_comb end_u_hours <= (u_hours == 9 || end_d_hours) && end_d_min ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            d_hours <= 0;
        else if (load) begin
            if(time_h_m_s[5][3:0] < 2 || time_h_m_s[4][3:0] <= 3 && time_h_m_s[5][3:0] == 2)
                d_hours <= time_h_m_s[5][1:0];
        end else if(end_u_hours && clock_ena)
            if(end_d_hours)
                d_hours <= 0;
            else
                d_hours <= d_hours + 1;
        else if(position[5] == 1)
            if(((u_hours > 3 && d_hours < 1) || (u_hours <= 3 && d_hours < 2)) && incre)
                d_hours <= d_hours + 1;
            else if(d_hours > 0 && decre)
                d_hours <= d_hours - 1;
    end
    always_comb end_d_hours <= d_hours == 2 && u_hours == 3 && end_d_min ? 1 : 0;

endmodule