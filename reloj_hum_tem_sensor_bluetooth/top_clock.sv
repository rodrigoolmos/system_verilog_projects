module top_clock(
    input  logic clk,
    input  logic arstn,
    input  logic key_up,
    input  logic key_down,
    input  logic key_mid,
    input  logic key_left,
    input  logic key_right,
    input  logic rx,
    inout  logic dht22_in_out,
    output logic tx,
    output logic[6:0] SEG, 
    output logic DP,
    output logic pwm_sig,
    output logic[7:0] AN
);
    logic[1:0] d_hours;
    logic[3:0] u_hours;
    logic[3:0] d_min;
    logic[3:0] u_min;
    logic[3:0] d_seg;
    logic[3:0] u_seg;
    logic[3:0] dig0;
    logic[3:0] dig1;
    logic[3:0] dig2;
    logic[3:0] dig3;
    logic[3:0] dig4;
    logic[3:0] dig5;
    logic[3:0] dig6;
    logic[3:0] dig7;
    logic clock_ena;
    logic tic_key_up;
    logic tic_key_down;
    logic[5:0] position;
    logic load;
    logic disp_time;
    logic[5:0][7:0] time_h_m_s;
    logic trigger_medida;
    logic[1:0] trigger_medida_ff;
    logic[2:0][3:0] humidity_bcd;
    logic[2:0][3:0] temperature_bcd;
    logic negativo_temp;
    logic[2:0][3:0] humidity_bcd_ff;
    logic[2:0][3:0] temperature_bcd_ff;
    logic negativo_temp_ff;
    logic[3:0] negativo_simb;

    top_dht22 #(.CLK_FREQ(100000000))
                    top_dht22_inst (
                                    .start_read(trigger_medida),
                                    .data_ready(data_ready),
                                    .sys_idle(),
                                    .*);

    // generar triggers para inicializar medidas de temperatura y humedad 
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            trigger_medida_ff <= 0;
        end else begin
            trigger_medida_ff <= {trigger_medida_ff[0], disp_time};
        end
    end
    // generar triggers para inicializar medidas de temperatura y humedad 
    always_comb trigger_medida <= trigger_medida_ff[0] & ~trigger_medida_ff[1];
    
    // si la medida es correcta guardar el resultadi 
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            humidity_bcd_ff <= 0;
            temperature_bcd_ff <= 0;
            negativo_temp_ff <= 0;
        end else begin
            humidity_bcd_ff <= humidity_bcd;
            temperature_bcd_ff <= temperature_bcd;
            negativo_temp_ff <= negativo_temp;
        end
    end

    // codificar simbolo "-" o " " 
    always_comb negativo_simb <= negativo_temp_ff ? 4'hF : 4'hE;

    data_sel_disp data_sel_disp_ins(
        .clk(clk),
        .arstn(arstn),
        .disp_time(disp_time),
        .time_Hh_Mm_Ss({4'd0, 4'd0, d_hours, u_hours, d_min, u_min, d_seg, u_seg}),
        .humidity({4'hE, 4'hE, 4'hE, 4'hE, humidity_bcd_ff[2], humidity_bcd_ff[1], humidity_bcd_ff[0], 4'hA}),
        .temperature({4'hE, 4'hE, 4'hE, negativo_simb, temperature_bcd_ff[2], temperature_bcd_ff[1], temperature_bcd_ff[0], 4'hC}),
        .dig0(dig0),
        .dig1(dig1),
        .dig2(dig2),
        .dig3(dig3),
        .dig4(dig4),
        .dig5(dig5),
        .dig6(dig6),
        .dig7(dig7)
    );

    counter_h_m_s counter_h_m_s_ins(
        .incre(tic_key_up),
        .decre(tic_key_down),
        .*);
        
    display_handler display_handler_ins(
        .display_mux(AN),
        .display_data(SEG),
        .*);


    uart_cntr #(
        .baudrate(9600),
        .clk_frec(100000000)
    )uart_cntr_ins(
//         .clk(clk), 
//         .arstn(arstn), 
//         .rx(rx), 
//         .time_reg(time_h_m_s), 
//         .new_time(load)
         .clk(clk), 
         .arstn(arstn), 
         .rx(rx),
         .humidity({{4'b0, humidity_bcd_ff[2]}, {4'b0, humidity_bcd_ff[1]}, {4'b0, humidity_bcd_ff[0]}}), //
         .temperature({{4'b0, temperature_bcd_ff[2]}, {4'b0, temperature_bcd_ff[1]}, {4'b0, temperature_bcd_ff[0]}}), //
         .time_reg(time_h_m_s), 
         .new_time(load),
         .send_h_t(trigger_medida), // pulso de un CLK
         .tx(tx)
    );

    control_keys clock_controll(.*);

    pwm_gen(
    .clk(clk),
    .arstn(arstn),
    .pwm_sig(pwm_sig)
    );

endmodule