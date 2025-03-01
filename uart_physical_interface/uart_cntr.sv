module uart_cntr#(
    parameter int baudrate = 9600,
    parameter int clk_frec = 50000000
)
(
    input  logic            clk,
    input  logic            arstn,
    input  logic            rx,
    input  logic            send_h_t,
    input  logic[2:0][7:0]  humidity,
    input  logic[2:0][7:0]  temperature,
    output logic            tx,
    output logic[5:0][7:0]  time_reg,
    output logic            new_time);

    logic[7:0]  byte_tx;
    logic       start_tx;
    logic       done_tx;
    logic[7:0]  byte_rx;
    logic       new_byte_rx;
    logic       end_trama;
    logic       end_trama_t1;

    logic[2:0]  cnt_rx_bytes;
    logic[3:0]  cnt_tx_bytes;

    logic[11:0][7:0]  byte_tx_reg;

    typedef enum logic[1:0] { idle, transmiting } state_tx_byte_t;
    state_tx_byte_t state_tx_byte;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            state_tx_byte <= idle;
            byte_tx <= 0;
            cnt_tx_bytes <= 0;
                        
            byte_tx_reg <=//ASCI  *      8      6      2      T      *
                   {/*tempera*/ 8'd42, 8'd56, 8'd54, 8'd50, 8'd84, 8'd42,
                          //ASCI  *      1      6      8      H      *
                    /*humedad*/ 8'd42, 8'd49, 8'd54, 8'd56, 8'd72, 8'd42};
        end else begin
            case (state_tx_byte)
                idle: begin
                    cnt_tx_bytes <= 0;
                    byte_tx_reg[2]  <= humidity[2] + 48;
                    byte_tx_reg[3]  <= humidity[1] + 48;
                    byte_tx_reg[4]  <= humidity[0] + 48;
                    
                    byte_tx_reg[8]  <= temperature[2] + 48;
                    byte_tx_reg[9]  <= temperature[1] + 48;
                    byte_tx_reg[10] <= temperature[0] + 48;

                    byte_tx <= byte_tx_reg[0];
                    if (send_h_t) begin
                        state_tx_byte <= transmiting;
                    end
                end
                transmiting: begin
                    if (done_tx) begin
                        if (cnt_tx_bytes == 11) begin
                            state_tx_byte <= idle;
                            byte_tx <= byte_tx_reg[cnt_tx_bytes];
                        end else begin
                            cnt_tx_bytes <= cnt_tx_bytes + 1;
                            byte_tx <= byte_tx_reg[cnt_tx_bytes];
                        end
                    end
                end
            endcase
        end
    end

    always_comb start_tx <= state_tx_byte == transmiting ? done_tx : 0;

    physical_uart #(
        .baudrate(baudrate),
        .clk_frec(clk_frec)
    )dut(.clk(clk), 
         .arstn(arstn), 
         .rx(rx), 
         .byte_tx(byte_tx), 
         .start_tx(start_tx), 
         .done_tx(done_tx), 
         .byte_rx(byte_rx), 
         .tx(tx), 
         .new_byte_rx(new_byte_rx)
    );

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            cnt_rx_bytes <= 5;
            end_trama  <= 0;
            time_reg   <= 0;
        end else if (new_byte_rx) begin
            if (byte_rx == 114) begin       // 'r' inicio de trama
                time_reg   <= 0;
                end_trama  <= 0;
                cnt_rx_bytes <= 5;
            end else if (byte_rx == 116) begin // 't' fin de trama
                end_trama <= 1;
            end else begin                    // datos
                if (cnt_rx_bytes >= 0) begin
                    time_reg[cnt_rx_bytes] <= byte_rx - 48;
                    cnt_rx_bytes <= cnt_rx_bytes - 1;
                end
            end
        end
    end


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            end_trama_t1 <= 0;
        end else begin
            end_trama_t1 <= end_trama;
        end
    end

    always_comb new_time <= end_trama & ~end_trama_t1;

endmodule