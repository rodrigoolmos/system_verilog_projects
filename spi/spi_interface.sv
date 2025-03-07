module spi_interface #(
    parameter CLK_FREC = 100000000,
    parameter SCL_FREC = 1000000

) (
    input  logic        clk,
    input  logic        arstn,

    // control signals
    input  logic[7:0]   byte_send,
    output logic[7:0]   byte_receive,
    input  logic        send_byte,
    input  logic        receive_byte,
    output logic        system_idle,

    // spi signals
    input  logic        miso,
    output logic        mosi,
    output logic        scl,
    output logic        cs);

    const int MAX_CNT = CLK_FREC/SCL_FREC;
    const int HALF_CNT = MAX_CNT/2;

    logic[$clog2(CLK_FREC/SCL_FREC)-1:0] clk_div;
    logic[3:0] bits_cnt;
    logic set_data_mosi;
    logic sample_data_miso;
    logic[7:0] byte_send_reg;

    logic        system_idle_ff;


    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            clk_div <= 0;
        else
            if (send_byte || receive_byte)
                clk_div <= 0;
            else
                if (clk_div == MAX_CNT - 1 || bits_cnt == 9)
                    clk_div <= 0;
                else
                    clk_div <= clk_div + 1;
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            bits_cnt <= 9;
        end else begin
            if (send_byte || receive_byte) begin
                bits_cnt <= 0;
            end else if (clk_div == MAX_CNT - 1) begin
                if (bits_cnt != 9) begin
                    bits_cnt <= bits_cnt + 1;
                end
            end
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            byte_receive <= 0;
        else
            if (sample_data_miso)
                byte_receive <= {miso, byte_receive[7:1]};
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            mosi <= 0;
        else
            if (send_byte)
                byte_send_reg <= byte_send;
            else if (set_data_mosi) begin
                byte_send_reg <= {1'b0, byte_send_reg[7:1]};
                mosi <= byte_send_reg[0];
            end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            cs <= 1;
            system_idle_ff <= 1;
        end else begin
            system_idle_ff <= system_idle;
            cs <= (bits_cnt < 9) ? 0 : system_idle_ff;
        end
    end

    always_comb begin
        scl <= (clk_div < HALF_CNT) || (bits_cnt >= 8) ? 1 : 0;
        sample_data_miso <= (clk_div == (MAX_CNT - 1)) && (bits_cnt < 8) ? 1 : 0;
        system_idle <= (bits_cnt < 9) ? 0 : 1;
        set_data_mosi <= (clk_div == HALF_CNT) && (bits_cnt < 8) ? 1 : 0;            
    end
    
endmodule