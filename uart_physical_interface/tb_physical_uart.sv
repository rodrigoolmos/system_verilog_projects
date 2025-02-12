module tb_physical_uart;

    timeunit 1ns;
    timeprecision 1ps;

    bit         clk;
    bit         arstn;
    bit         rx;
    bit[7:0]    byte_tx;
    bit         start_tx;
    logic       done_tx;
    logic[7:0]  byte_rx;
    logic       tx;
    logic       new_byte_rx;

    const integer t_clk = 10;
    bit[7:0]    tb_byte_tx;
    bit[7:0]    tb_byte_rx;
    bit         end_sim_tx = 0;
    bit         end_sim_rx = 0;



    initial
        forever 
            #(t_clk/2) clk = ~clk;

    physical_uart #(
        .baudrate(9600),
        .clk_frec(100000000)
    )dut(.*);

    // reset
    initial begin
        arstn = 0;
        rx = 1;
        #100us;
        arstn = 1;
        #200us;
    end

    // model rx <- tb tx 
    initial begin

        @(posedge arstn);

        for (int j=0; j<256; ++j) begin
            tb_byte_tx = j;
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

            Correct_rx: assert (byte_rx == tb_byte_tx)
                else $error("Assertion Correct_rx failed! sended %d recived %d", tb_byte_tx, byte_rx);
        end

        for (int j=0; j<256; ++j) begin
            tb_byte_tx = j;
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

            Correct_rx: assert (byte_rx == tb_byte_tx)
                else $error("Assertion Correct_rx failed! sended %d recived %d", tb_byte_tx, byte_rx);

            #400us;
        end

        #1040us;
        end_sim_tx = 1;
    end

    // control model tx model
    initial begin
        byte_tx = 0;
        start_tx = 0;

        @(posedge arstn);
        @(posedge clk);
        // continuous tx
        for (int i=0; i<255; ++i) begin
            byte_tx = i;
            start_tx = 1;
            @(posedge clk);
            start_tx = 0;
            @(posedge done_tx);
        end
        #50000 @(posedge clk);
        // steping tx
        for (int i=0; i<255; ++i) begin
            byte_tx = i;
            start_tx = 1;
            @(posedge clk);
            start_tx = 0;
            @(posedge done_tx);
            #500 @(posedge clk);
        end
        end_sim_rx = 1;

    end

    // model tx -> tb rx 
    initial begin

        // continuous tx
        for (int i=0; i<255; ++i) begin
            @(negedge tx);
            #156us; // start and half of bit 1
            for (int index=0; index<8; ++index) begin
                tb_byte_rx[index] = tx;
                #104us;
            end
            #25us; // quarter of stop
            Generation_stop: assert (tx == 1)
                    else $error("El bit de stop no se genera correctamente");

            Check_byte_tx: assert (tb_byte_rx == i)
                    else $error("El byte transmitido es incorrecto %d != %d", tb_byte_rx, i);
        end

        // steping tx
        for (int i=0; i<255; ++i) begin
            @(negedge tx);
            #156us; // start and half of bit 1
            for (int index=0; index<8; ++index) begin
                tb_byte_rx[index] = tx;
                #104us;
            end
            #25us; // quarter of stop
            Generation_stop: assert (tx == 1)
                    else $error("El bit de stop no se genera correctamente");

            Check_byte_tx: assert (tb_byte_rx == i)
                    else $error("El byte transmitido es incorrecto %d != %d", tb_byte_rx, i);
        end

    end

    // end sim
    initial begin
        $display("Start simulation");
        @(posedge end_sim_rx);
        @(posedge end_sim_tx);
        $display("End simulation");
        $stop;
    end

endmodule