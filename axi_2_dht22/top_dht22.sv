module top_dht22 #(
        parameter CLK_FREQ = 100000000
    )(
    input  logic clk,
    input  logic arstn,
    input  logic start_read,
    inout logic dht22_in_out,
    output logic data_ready,
    output logic sys_idle,
    output logic[2:0][3:0] humidity_bcd,
    output logic negativo_temp,
    output logic [7:0] parity,
    output logic[2:0][3:0] temperature_bcd
);

    logic dht22_out;
    logic dht22_dir;
    logic correct_data;
    logic [15:0] humidity;
    logic [15:0] temperature;
    logic data_ready_ff;

    dht22_driver #(.CLK_FREQ(CLK_FREQ))
                    dht22_driver_inst (
                        .clk(clk),
                        .arstn(arstn),
                        .start_read(start_read),
                        .dht22_in(dht22_in_out),
                        .dht22_out(dht22_out),
                        .dht22_dir(dht22_dir),
                        .sys_idle(sys_idle),
                        .humidity(humidity),
                        .temperature(temperature),
                        .parity(parity)
                    );

    dht22_CRC dht22_CRC_inst (
        .correct_data(correct_data),
        .humidity(humidity),
        .temperature(temperature),
        .parity(parity)
    );

    convert2BCD convert2BCD_h_inst (
        .numero(humidity),
        .negativo(), // humidity is always positive
        .decenas(humidity_bcd[2]),
        .unidades(humidity_bcd[1]),
        .decimal(humidity_bcd[0])
    );

    convert2BCD convert2BCD_t_inst (
        .numero(temperature),
        .negativo(negativo_temp),
        .decenas(temperature_bcd[2]),
        .unidades(temperature_bcd[1]),
        .decimal(temperature_bcd[0])
    );

    always_comb data_ready <= (correct_data & sys_idle) & ~data_ready_ff;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            data_ready_ff <= 0;
        end else begin
            data_ready_ff <= correct_data & sys_idle;
        end
        
    end

    // tristate buffer
    assign dht22_in_out = dht22_dir == 0 ? dht22_out : 1'bZ;

endmodule