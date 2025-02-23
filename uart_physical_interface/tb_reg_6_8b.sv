module tb_reg_6_8b;

    timeunit 1ns;
    timeprecision 1ps;

    bit           clk;
    bit           arstn;
    bit           rx;         
    logic[5:0][7:0] time_reg;
    logic           new_time;

    const integer t_clk = 10;
    bit[7:0]    tb_byte_tx;
    bit         end_sim_tx = 0;

    initial
        forever 
            #(t_clk/2) clk = ~clk;

    reg_6_8b #(
        .baudrate(9600),
        .clk_frec(100000000)
    )dut(.clk(clk), 
         .arstn(arstn), 
         .rx(rx), 
         .time_reg(time_reg), 
         .new_time(new_time)
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
        $display("Start simulation");
        @(posedge end_sim_tx);
        $display("End simulation");
        $stop;
    end

endmodule