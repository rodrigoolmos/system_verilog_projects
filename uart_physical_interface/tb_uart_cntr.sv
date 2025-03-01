module tb_uart_cntr;

    timeunit 1ns;
    timeprecision 1ps;

    bit             clk;
    bit             arstn;
    bit             rx;         
    bit             send_h_t;
    bit[2:0][7:0]   humidity;
    bit[2:0][7:0]   temperature;
    bit[7:0]        tb_byte_tx;
    bit             end_sim_tx = 0;

    logic[5:0][7:0] time_reg;
    logic           new_time;

    logic           tx;
    const integer t_clk = 10;

    initial
        forever 
            #(t_clk/2) clk = ~clk;

    uart_cntr #(
        .baudrate(9600),
        .clk_frec(100000000)
    )dut(.clk(clk), 
         .arstn(arstn), 
         .rx(rx), 
         .humidity(humidity),
         .temperature(temperature),
         .time_reg(time_reg), 
         .new_time(new_time),
         .send_h_t(send_h_t),
         .tx(tx)
    );

    // model rx <- tb tx 
    initial begin

        arstn = 0;
        rx = 1;
        #100us;
        arstn = 1;
        #200us;

        tb_byte_tx = 8'h72; // r
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;

        for (int j=0; j<6; ++j) begin
            tb_byte_tx = 30 + j; // 30, 31, 32, 33, 34, 35
            //start
            rx = 0;
            #104us;
            // transmiting
            for (int i=0; i<8; ++i) begin
                rx = tb_byte_tx[i];
                #104us;
            end
            //stop
            rx = 1;
            #104us;
        end

        tb_byte_tx = 8'h74; // t
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;


        #1040us; // new trama


        tb_byte_tx = 8'h72; // r
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;

        for (int j=0; j<6; ++j) begin
            tb_byte_tx = 33 + j; // 33, 34, 35, 36, 37, 38
            //start
            rx = 0;
            #104us;
            // transmiting
            for (int i=0; i<8; ++i) begin
                rx = tb_byte_tx[i];
                #104us;
            end
            //stop
            rx = 1;
            #104us;
        end

        tb_byte_tx = 8'h74; // t
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;




        #1040us; // new trama


        tb_byte_tx = 8'h72; // r
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;

        for (int j=0; j<6; ++j) begin
            tb_byte_tx = 30 + j; // 30, 31, 32, 33, 34, 35
            //start
            rx = 0;
            #104us;
            // transmiting
            for (int i=0; i<8; ++i) begin
                rx = tb_byte_tx[i];
                #104us;
            end
            //stop
            rx = 1;
            #104us;
        end

        tb_byte_tx = 8'h74; // t
        //start
        rx = 0;
        #104us;
        // transmiting
        for (int i=0; i<8; ++i) begin
            rx = tb_byte_tx[i];
            #104us;
        end
        //stop
        rx = 1;
        #104us;

        #1040us;
        end_sim_tx = 1;
    end

    // end sim
    initial begin

        @(posedge arstn);
        @(posedge clk);

        send_h_t = 0;
        humidity[2]    = 8'd01;
        humidity[1]    = 8'd02;
        humidity[0]    = 8'd03;
        temperature[2] = 8'd11;
        temperature[1] = 8'd12;
        temperature[0] = 8'd13;
        @(posedge clk);
        send_h_t = 1;
        @(posedge clk);
        send_h_t = 0;
        #20000us @(posedge clk);

        send_h_t = 0;
        humidity[2]    = 8'd21;
        humidity[1]    = 8'd22;
        humidity[0]    = 8'd23;
        temperature[2] = 8'd31;
        temperature[1] = 8'd32;
        temperature[0] = 8'd33;
        @(posedge clk);
        send_h_t = 1;
        @(posedge clk);
        send_h_t = 0;
        #15000us @(posedge clk);

        $display("Start simulation");
        @(posedge end_sim_tx);
        $display("End simulation");
        $stop;
    end

endmodule