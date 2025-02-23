module reg_6_8b#(
    parameter int baudrate = 9600,
    parameter int clk_frec = 50000000
)
(
    input  logic         clk,
    input  logic         arstn,
    input  logic         rx,
    output logic[5:0][7:0]  time_reg,
    output logic    new_time
    );


    logic[7:0]  byte_tx;
    logic       start_tx;
    logic       done_tx;
    logic[7:0]  byte_rx;
    logic       tx;
    logic       new_byte_rx;
    logic       end_trama;
    logic       end_trama_t1;



    logic[2:0]  cnt_rx_bytes;

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