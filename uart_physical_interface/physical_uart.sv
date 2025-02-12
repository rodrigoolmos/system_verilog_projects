module physical_uart#(
    parameter int baudrate = 9600,
    parameter int clk_frec = 50000000
)
(
    input logic         clk,
    input logic         arstn,
    input logic         rx,         // reception signal
    input logic[7:0]    byte_tx,    // byte to transmit
    input logic         start_tx,   // start transmission asseerted with 1 tic to start transmision of byte_tx
    output logic        done_tx,    // transmission done 1 if byte_tx was transmitted else 0
    output logic[7:0]   byte_rx,    // received byte
    output logic        tx,         // transmision signal
    output logic        new_byte_rx // new byte received asseerted with 1 tic when a new byte is received
    );

    localparam needed_bits = $clog2(clk_frec/baudrate);
    localparam time_bit = clk_frec/baudrate;
    localparam time_start = clk_frec/(2*baudrate);
    localparam time_stop = clk_frec/(4*baudrate);

    logic[needed_bits-1:0] bit_cnt_rx;
    logic[3:0] bit_num_rx;
    logic[1:0] ff_rx;
    logic new_bit;

    logic[needed_bits-1:0] bit_cnt_tx;
    logic[3:0] bit_num_tx;

    typedef enum logic[1:0] {RX_IDLE, RX_START, RX_DATA, RX_STOP} t_state_rx;
    t_state_rx state_rx;
    typedef enum logic[1:0] {TX_IDLE, TX_START, TX_DATA, TX_STOP} t_state_tx;
    t_state_tx state_tx;

    //ff reg metastabilidad
    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            ff_rx <= 2'b11;
        end else begin
            ff_rx <= {ff_rx[0], rx};
        end
    end

    //rx
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            state_rx <= RX_IDLE;
            new_byte_rx <= 0;
            byte_rx <= 8'b0;
            bit_cnt_rx <= 0;
            new_bit <= 0;
            bit_num_rx <= 0;
        end else begin
            unique case(state_rx)
                RX_IDLE: begin
                    new_byte_rx <= 0;
                    if(ff_rx[1] == 0)
                        state_rx <= RX_START;
                end
                RX_START: begin
                    if(bit_cnt_rx < time_start) begin
                        bit_cnt_rx <= bit_cnt_rx + 1;
                    end else begin
                        bit_cnt_rx <= 0;
                        state_rx <= RX_DATA;
                    end
                end
                RX_DATA: begin
                    if(bit_cnt_rx < time_bit) begin
                        bit_cnt_rx <= bit_cnt_rx + 1;
                        new_bit <= 0;
                    end else begin
                        bit_cnt_rx <= 0;
                        if (bit_num_rx == 8) begin
                            bit_num_rx <= 0;
                            bit_cnt_rx <= 0;
                            state_rx <= RX_STOP;
                        end else begin
                            new_bit <= 1;
                            byte_rx <= {ff_rx[1], byte_rx[7:1]};
                            bit_num_rx <= bit_num_rx + 1;
                        end
                    end
                end
                RX_STOP: begin
                    if(bit_cnt_rx < time_stop) begin
                        bit_cnt_rx <= bit_cnt_rx + 1;
                    end else begin
                        state_rx <= RX_IDLE;
                        new_byte_rx <= 1;
                        bit_cnt_rx <= 0;
                    end
                end
                default:
                    state_rx <= RX_IDLE;
            endcase
        end
    end


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            bit_cnt_tx <= 0;
            bit_num_tx <= 0;
            state_tx <= TX_IDLE;
            tx <= 1;
        end else begin
            unique case (state_tx)
                TX_IDLE: begin
                    done_tx <= 1;
                    tx <= 1;
                    if(start_tx) 
                        state_tx <= TX_START;
                end
                TX_START: begin
                    done_tx <= 0;
                    tx <= 0;
                    if (bit_cnt_tx < time_bit) begin
                        bit_cnt_tx <= bit_cnt_tx + 1;
                    end else begin
                        bit_cnt_tx <= 0;
                        state_tx <= TX_DATA;
                    end
                end
                TX_DATA: begin
                    tx <= byte_tx[bit_num_tx];
                    if (bit_cnt_tx < time_bit) begin
                        bit_cnt_tx <= bit_cnt_tx + 1;
                    end else begin
                        if (bit_num_tx < 7) begin
                            bit_num_tx <= bit_num_tx + 1;
                        end else begin
                            bit_num_tx <= 0;
                            state_tx <= TX_STOP;
                        end
                        bit_cnt_tx <= 0;
                    end
                end
                TX_STOP: begin
                    tx <= 1;
                    if (bit_cnt_tx < time_bit) begin
                        bit_cnt_tx <= bit_cnt_tx + 1;
                    end else begin
                        bit_cnt_tx <= 0;
                        state_tx <= TX_IDLE;
                    end                    
                end
                default:
                    state_tx <= TX_IDLE;
            endcase
        end
        
    end

endmodule