`include "agent_dht22.sv"

module tb_top_dht22;

    const integer t_clk = 10;
    integer max_test = 5;


    bit clk;
    bit arstn;
    bit start_read;
    logic data_ready;
    logic sys_idle;
    logic[2:0][3:0] humidity_bcd;
    logic negativo_temp;
    logic[2:0][3:0] temperature_bcd;

    logic[15:0] data_humidity;
    logic[15:0] data_temperature;
    logic[7:0] data_parity;

    int unsigned seed = 32'hDEADBEEF;
    integer sim_num = 0;
    logic first_data_sended;
    logic error_transmission = 0;

    agent_dht22 agent_dht22_h;
    dht22_if    dht22_vif();

    checker_dht22 checker_dht22_ins(dht22_vif, error_transmission);

    // Pull-up virtual sobre la señal SDA
    pullup(dht22_vif.dht22_in_out);

    function integer correct_data_read();
        int unsigned humidity_decimal;
        int unsigned humidity_unidades;
        int unsigned humidity_decenas;
        int unsigned temperature_decimal;
        int unsigned temperature_unidades;
        int unsigned temperature_decenas;
        logic signo_temp;

        humidity_decimal = data_humidity % 10;
        humidity_unidades = (data_humidity / 10) % 10;
        humidity_decenas = (data_humidity / 100) % 10;

        signo_temp = data_temperature[15];
        temperature_decimal = data_temperature[14:0] % 10;
        temperature_unidades = (data_temperature[14:0] / 10) % 10;
        temperature_decenas = (data_temperature[14:0] / 100) % 10;

        if (humidity_decimal == humidity_bcd[0] &&
            humidity_unidades == humidity_bcd[1] &&
            humidity_decenas == humidity_bcd[2] &&
            temperature_decimal == temperature_bcd[0] &&
            temperature_unidades == temperature_bcd[1] &&
            temperature_decenas == temperature_bcd[2] &&
            negativo_temp == signo_temp) begin

                $display("Test passed number %0d", sim_num);
                sim_num++;
            end else begin
                $display("Test failed"); 
                $display("SENDED -> data_humidity: %0d %0d %0d data_temperature: %0d %0d %0d", 
                                    humidity_decimal, humidity_unidades, humidity_decenas,
                                    temperature_decimal, temperature_unidades, temperature_decenas);
                $display("RECIVED -> data_humidity: %0d %0d %0d data_temperature: %0d %0d %0d",
                        humidity_bcd[0], humidity_bcd[1], humidity_bcd[2],
                        temperature_bcd[0], temperature_bcd[1], temperature_bcd[2]);
                $display("SENDED -> negativo_temp: %0d", signo_temp);
                $display("RECIVED -> negativo_temp: %0d", negativo_temp);
            $stop;
        end
        return 0;
    endfunction

    initial
    forever
        #(t_clk/2) clk = ~clk;

    top_dht22 #(
        .CLK_FREQ(100000000)
    )top_dht22_inst (
        .*,
        .dht22_in_out(dht22_vif.dht22_in_out));


    initial
    begin
        fork
            begin // interface of control
                agent_dht22_h = new(dht22_vif);
                first_data_sended = 0;
                start_read = 0;
                arstn = 0;
                #52us;
                arstn = 1;
                #52us;

                for (int i=0; i<max_test; ++i) begin
                    start_read = 1;
                    @(posedge clk)
                    start_read = 0;
                    @(posedge sys_idle);
                    first_data_sended = 1;
                    #2ms @(posedge clk);
                end

                // simulate error transmission
                error_transmission = 1;
                start_read = 1;
                @(posedge clk)
                start_read = 0;
                #10ms @(posedge clk);
                error_transmission = 0;

                // simulate recovery
                for (int i=0; i<max_test; ++i) begin
                    start_read = 1;
                    @(posedge clk)
                    start_read = 0;
                    @(posedge sys_idle);
                    #2ms @(posedge clk);
                end

            end

            begin // dth22 emulation
                for (int i=0; i<max_test; ++i) begin
                    seed = $urandom(seed);
                    data_humidity = $dist_uniform(seed, 0, 999); // 0-99.9%
                    seed = $urandom(seed);
                    data_temperature[14:0] = $dist_uniform(seed, 0, 900); // -90.0-90.0°C
                    seed = $urandom(seed);
                    data_temperature[15] = $dist_uniform(seed, 0, 1); // sign
                    data_parity = data_humidity[15:8] + data_humidity[7:0] + 
                                data_temperature[15:8] + data_temperature[7:0];
                    agent_dht22_h.generate_dht22_data(data_humidity, data_temperature, data_parity);
                end

                seed = $urandom(seed);
                data_humidity = $dist_uniform(seed, 0, 999); // 0-99.9%
                seed = $urandom(seed);
                data_temperature[14:0] = $dist_uniform(seed, 0, 900); // -90.0-90.0°C
                seed = $urandom(seed);
                data_temperature[15] = $dist_uniform(seed, 0, 1); // sign
                data_parity = data_humidity[15:8] + data_humidity[7:0] + 
                                data_temperature[15:8] + data_temperature[7:0];
                agent_dht22_h.generate_dht22_error(data_humidity, data_temperature, data_parity);

                for (int i=0; i<max_test; ++i) begin
                    seed = $urandom(seed);
                    data_humidity = $dist_uniform(seed, 0, 999); // 0-99.9%
                    seed = $urandom(seed);
                    data_temperature[14:0] = $dist_uniform(seed, 0, 900); // -90.0-90.0°C
                    seed = $urandom(seed);
                    data_temperature[15] = $dist_uniform(seed, 0, 1); // sign
                    data_parity = data_humidity[15:8] + data_humidity[7:0] + 
                            data_temperature[15:8] + data_temperature[7:0];
                    agent_dht22_h.generate_dht22_data(data_humidity, data_temperature, data_parity);
                end

            end

            // score board
            begin
                $display("Score board listening");
                forever
                begin
                    @(posedge data_ready);
                    if (error_transmission == 0 && first_data_sended == 1) begin
                        $display("New data received performing test");
                        correct_data_read();
                    end
                end
            end

        join_any

        $display("end of simulation");
        #1000us;
        $stop;
    end

endmodule