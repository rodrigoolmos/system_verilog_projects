module tb_dht22_cntr;

    timeunit 1ns;
    timeprecision 1ps;

    const integer t_clk = 10;

    bit clk;
    bit arstn;
    bit start_read;
    logic sys_idle;
    logic dht22_in;
    logic dht22_out;
    logic dht22_dir;
    logic[15:0] humidity;
    logic[15:0] temperature;
    logic[7:0] parity;

    logic[15:0] data_humidity;
    logic[15:0] data_temperature;
    logic[7:0] data_parity;

    task automatic generate_dht22_data(ref logic dht22_in, 
                                    const ref logic dht22_out,
                                    const ref logic[15:0] data_humidity,
                                    const ref logic[15:0] data_temperature,
                                    const ref logic[7:0] data_parity);
        
        @(negedge dht22_out); 
        // host pull low
        @(posedge dht22_out);
        #36us; // host pull UP

        dht22_in = 0;
        #80us;
        dht22_in = 1;
        #80us;

        // 16 bits RH data
        for (int i=15; i>=0; i = i - 1) begin
            if (data_humidity[i] == 0) begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #25us;
            end else begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #70us;
            end
        end

        // 16 bits T data
        for (int i=15; i>=0; i = i - 1) begin
            if (data_temperature[i] == 0) begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #25us;
            end else begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #70us;
            end
        end

        // 8 bits check sum
        for (int i=7; i>=0; i = i - 1) begin
            if (data_parity[i] == 0) begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #25us;
            end else begin
                dht22_in = 0;
                #50us;
                dht22_in = 1;
                #70us;
            end
            $display("data_parity[%d] = %d", i, data_parity[i]);
        end

        dht22_in = 0;
        #50us;
        dht22_in = 1;

    endtask

    initial
    forever 
        #(t_clk/2) clk = ~clk;

    dht22_cntr #(.CLK_FREQ(100000000))
                    dht22_cntr_inst (.*);


    initial
    begin
        fork
            begin // interface of control
            start_read <= 0;
            arstn <= 0;
            #52us;
            arstn <= 1;
            #52us;

            start_read <= 1;
            @(posedge clk)
            start_read <= 0;
            @(posedge sys_idle);
            #1ms @(posedge clk);

            start_read <= 1;
            @(posedge clk)
            start_read <= 0;
            @(posedge sys_idle);
            #1ms @(posedge clk);
            end

            begin // dth22 emulation
                dht22_in = 1;
                data_humidity = 16'd625;
                data_temperature = 16'd351;
                data_parity = 8'b1110_1110;

                generate_dht22_data(dht22_in, dht22_out, data_humidity,
                                         data_temperature, data_parity);


                dht22_in = 1;
                data_humidity = 16'd413;
                data_temperature = 16'd236;
                data_parity = 8'b1010_1101;

                generate_dht22_data(dht22_in, dht22_out, data_humidity,
                                         data_temperature, data_parity);
            end

        join
        #1000us;
        $stop;
    end

endmodule