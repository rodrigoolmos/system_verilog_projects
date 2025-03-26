// CPHA = 1
// CPOL = 1
module spi_interface #(
    parameter CLK_FREC = 100000000,
    parameter SCL_FREC = 1000000

) (
    input  logic        clk,
    input  logic        arstn,

    // control signals
    input  logic[7:0]   byte_2_send,        // byte to send laches the byte when end_trans is 1
    output logic[7:0]   byte_received,      // byte received ready when end_trans is 1
    input  logic        ena_spi,            // enable spi interface trsnasaction when this signal is 1 
    // end of transaction lower ena_spi when end_trans 1 if you dont want to send more bytes
    // when this signal is 1 the byte_received is ready to be read or the byte_2_send is ready to be written
    output logic        end_trans,          
    input  logic        msb_lsb,            // msb = 1 or lsb = 0

    // spi signals
    input  logic        miso,
    output logic        mosi,
    output logic        scl,
    output logic        cs);

    generate if (SCL_FREC *10 > CLK_FREC) begin : err_gen
          initial
            $fatal("ERROR: SCL_FREC * 10 > CLK_FREC");
        end
    endgenerate

    localparam MAX_CNT = (CLK_FREC/SCL_FREC) - 1;
    localparam HALF_CNT = MAX_CNT/2;

    logic[$clog2(CLK_FREC/SCL_FREC)-1:0] clk_div;

    logic posedge_scl;
    logic negedge_scl;
    logic ena_clk_div;

    logic[3:0] cnt_mosi;
    logic[3:0] cnt_miso;

    logic[7:0] byte_2_send_reg;
    logic[7:0] byte_received_reg;

    typedef enum logic[2:0] {
        IDLE,
        LOAD_BYTE,
        WAIT_BEFORE,
        SEND_RECEIVE,
        WAIT_AFTER
    } state_t; state_t state_spi;


    // CLK_DIV GENERATION
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn)
            clk_div <= 0;
        else if(ena_clk_div)
            if (clk_div == MAX_CNT || state_spi == LOAD_BYTE)
                clk_div <= 0;
            else
                clk_div <= clk_div + 1;
    end

    always_comb ena_clk_div = (state_spi != IDLE);

    // FSM
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            state_spi <= IDLE;
            byte_2_send_reg <= 0;
            byte_received <= 0;
        end else if(!ena_spi) begin
            state_spi <= IDLE;
            byte_2_send_reg <= 0;
            byte_received <= 0;
        end else begin
            case(state_spi)
                IDLE: begin
                    if(ena_spi)
                        state_spi <= WAIT_BEFORE;
                end
                WAIT_BEFORE: begin
                    if(clk_div == MAX_CNT)
                        state_spi <= LOAD_BYTE;
                end
                LOAD_BYTE: begin
                    byte_2_send_reg <= byte_2_send;
                    state_spi <= SEND_RECEIVE;
                end
                SEND_RECEIVE: begin
                    if(cnt_miso == 8 && clk_div == MAX_CNT) begin
                        byte_received <= byte_received_reg;
                        state_spi <= WAIT_AFTER;
                    end
                end
                WAIT_AFTER: begin
                    if(clk_div == MAX_CNT) begin
                        if(ena_spi) begin
                            state_spi <= LOAD_BYTE;
                        end else
                            state_spi <= IDLE;
                    end
                end
                default: state_spi <= IDLE;
            endcase
        end
    end

    always_comb end_trans = (state_spi == WAIT_AFTER) && clk_div == 0;

    // MISO
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            cnt_miso <= 0;
            byte_received_reg <= 0;
        end else if(state_spi == SEND_RECEIVE) begin
            if(posedge_scl) begin
                cnt_miso <= cnt_miso + 1;
                if (cnt_miso < 8) begin
                    if (msb_lsb)
                        byte_received_reg[7 - cnt_miso] <= miso;
                    else
                        byte_received_reg[cnt_miso] <= miso;
                end
            end
        end else begin
            cnt_miso <= 0;
        end 
    end
    
    // MOSI
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            cnt_mosi <= 0;
            mosi <= 0;
        end else if(state_spi == SEND_RECEIVE) begin
            if(negedge_scl) begin
                cnt_mosi <= cnt_mosi + 1;
                if (cnt_mosi < 8) begin
                    if (msb_lsb)
                        mosi <= byte_2_send_reg[7 - cnt_mosi];
                    else
                        mosi <= byte_2_send_reg[cnt_mosi];
                end
            end
        end else begin
            mosi <= 0;
            cnt_mosi <= 0;
        end 
    end

    // SCL
    always_comb scl = (state_spi == SEND_RECEIVE) && ena_spi ? (clk_div >= HALF_CNT) : 1;
    always_comb posedge_scl = (state_spi == SEND_RECEIVE) ? (clk_div == HALF_CNT) : 0;
    always_comb negedge_scl = (state_spi == SEND_RECEIVE) ? (clk_div == 0) : 0;

    // CS
    assign cs = (state_spi != IDLE) ? 0 : 1;

endmodule