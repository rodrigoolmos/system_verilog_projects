module i2c #(
    parameter CLK_FREQ  = 100_000_000,  // 100 MHz
    parameter BITS_WAIT = 2,            // 100 MHz
    parameter I2C_FREQ  = 100_000       // 100 KHz
) (
    input  logic        clk,
    input  logic        arstn,

    // control signals
    input  logic[7:0]   byte_2_send,        // byte to send laches the byte when end_trans is 1
    output logic[7:0]   byte_received,      // byte received ready when end_trans is 1
    input  logic        ena_i2c,            // enable i2c interface trsnasaction when this signal is 1 
    // end of transaction lower ena_i2c when end_trans 1 if you dont want to send more bytes
    // when this signal is 1 the byte_received is ready to be read or the byte_2_send is ready to be written
    output logic        end_trans,          
    input  logic        msb_lsb,            // msb = 1 or lsb = 0
    input  logic[7:0]   adrr_r_w,           // slave addres + (r/w) bit


    // i2c signals
    inout  logic        sda,
    output logic        scl);

    generate if (CLK_FREQ / I2C_FREQ < 10) begin : err_gen
        initial
          $fatal("ERROR: CLK_FREQ / I2C_FREQ < 10");
        end
    endgenerate

    logic[$clog2(CLK_FREQ/I2C_FREQ)-1:0] clk_div;
    logic reset_clk_div;
    logic send_receive;             // 0 = send 1 = receive
    logic[2:0] bit_cnt;

    localparam MAX_CNT = (CLK_FREQ/I2C_FREQ) - 1;
    localparam HALF_CNT = MAX_CNT/2;
    localparam QUAR_CNT = MAX_CNT/4;

    logic        sda_o;     // output
    logic        sda_i;     // input
    logic        sda_s;     // select 1 = sda_o 0 = sda_i

    typedef enum logic[2:0] {idle, start, addr, r_w, ack, send_receive_data, wait_time, stop} state_i2c_t;
    state_i2c_t state_i2c;

    // clk divider
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            clk_div <= 0;
        end else begin
            if (clk_div == (CLK_FREQ/I2C_FREQ) - 1 || reset_clk_div) begin
                clk_div <= 0;
            end else begin
                clk_div <= clk_div + 1;
            end
        end
    end

    // state machine
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            state_i2c <= idle;
            bit_cnt <= 7;
            send_receive <= 0;
            reset_clk_div <= 1;
        end else begin
            case (state_i2c)
                idle: begin
                reset_clk_div <= 1;
                    if (ena_i2c) begin
                        if (clk_div == 1) begin
                            state_i2c <= start;
                        end
                        reset_clk_div <= 0;
                    end
                end
                start: begin
                    if (clk_div == 0) begin
                        state_i2c <= addr;
                    end
                end
                addr: begin
                    if (clk_div == HALF_CNT) begin
                        bit_cnt <= bit_cnt - 1;
                    end else if (bit_cnt == 1 && clk_div == 0) begin
                            bit_cnt <= 0;
                            state_i2c <= r_w;
                    end
                end
                r_w: begin
                    send_receive <= adrr_r_w[0];
                    if (clk_div == HALF_CNT) begin
                        state_i2c <= ack;
                    end
                end
                ack: begin
                    if (clk_div == HALF_CNT) begin
                        if (sda == 0) begin
                            if (ena_i2c) begin
                                bit_cnt <= BITS_WAIT - 1;
                                state_i2c <= wait_time;
                            end else begin
                                state_i2c <= stop;
                            end
                        end else begin
                            state_i2c <= idle;
                        end
                    end
                end
                wait_time: begin
                    if (clk_div == 0) begin
                        bit_cnt <= bit_cnt - 1;
                        if (bit_cnt == 0) begin
                            bit_cnt <= 7;
                            state_i2c <= send_receive_data;
                        end
                    end
                end
                send_receive_data: begin
                    if (clk_div == HALF_CNT) begin
                        bit_cnt <= bit_cnt - 1;
                    end else if (bit_cnt == 7 && clk_div == 0) begin
                            bit_cnt <= 7;
                            state_i2c <= ack;
                    end
                end
                stop: begin
                    if (clk_div == HALF_CNT) begin
                        state_i2c <= idle;
                    end
                end
                default: begin
                    state_i2c <= idle;
                end
            endcase
        end
    end

    // i2c signals
    always_comb begin
        if (state_i2c == idle) begin
            scl = 1;
            sda_o = 1;
        // START CONDITION
        end else if (state_i2c == start) begin
            sda_o = (clk_div < QUAR_CNT);
            scl = (clk_div < HALF_CNT);
        // ADDRES TRANSMISION
        end else if (state_i2c == addr) begin
            sda_o = adrr_r_w[bit_cnt];
            scl = (clk_div < HALF_CNT);
        // R/W TRANSMISION
        end else if (state_i2c == r_w) begin
            sda_o = adrr_r_w[0];
            scl = (clk_div < HALF_CNT);
        // ACK
        end else if (state_i2c == ack) begin
            sda_o = 1;
            scl = (clk_div < HALF_CNT);
        // WAIT TIME
        end else if (state_i2c == wait_time) begin
            sda_o = 1;
            scl = (clk_div < HALF_CNT);
        // SEND DATA
        end else if (state_i2c == send_receive_data) begin
            sda_o = byte_2_send[bit_cnt];
            scl = (clk_div < HALF_CNT);
        // STOP CONDITION
        end else if (state_i2c == stop) begin
            sda_o = (clk_div > QUAR_CNT);
            scl = 1;
        end else begin
            scl = 1;
            sda_o = 1;
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            byte_received <= 0;
        end else begin
            if (clk_div == 0) begin
                if (state_i2c == send_receive_data && send_receive == 0) begin
                    if (msb_lsb) begin
                        byte_received <= {byte_received[6:0], sda_i};
                    end else begin
                        byte_received <= {sda_i, byte_received[7:1]};
                    end
                end
            end
        end
    end

    always_comb begin
        if (state_i2c == ack)
            sda_s = 1;
        else if (state_i2c == send_receive_data)
            sda_s = send_receive;
        else
            sda_s = 0;
    end
    

    assign sda = sda_s ? sda_o : 1'bz;
    always_comb sda_i = sda;


    always_comb end_trans = (state_i2c == ack);

endmodule