// CPHA = 1
// CPOL = 1
module spi_interface #(
    parameter CLK_FREC = 100000000,
    parameter SCL_FREC = 1000000

) (
    input  logic        clk,
    input  logic        arstn,

    // control signals
    input  logic[7:0]   byte_2_send,        // byte to send
    output logic[7:0]   byte_received,      // byte received
    output logic        new_byte,           // new byte received or ready sent
    input  logic        ena_spi,            // enable spi

    // spi signals
    input  logic        miso,
    output logic        mosi,
    output logic        scl,
    output logic        cs);

    const int MAX_CNT = CLK_FREC/SCL_FREC;
    const int HALF_CNT = MAX_CNT/2;

    logic[$clog2(CLK_FREC/SCL_FREC)-1:0] clk_div;

    logic posedge_scl;
    logic negedge_scl;
    logic ena_clk_div;

    logic[3:0] cnt_mosi;
    logic[3:0] cnt_miso;


    typedef enum logic[1:0] {
        IDLE,
        SEND_RECEIVE,
        WAIT_SCL
    } state_t; state_t state_spi;


    // CLK_DIV GENERATION
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn)
            clk_div <= 0;
        else if(ena_clk_div)
            if (clk_div == MAX_CNT)
                clk_div <= 0;
            else
                clk_div <= clk_div + 1;
    end

    always_comb ena_clk_div = state_spi == !IDLE;

    // FSM
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            state_spi <= IDLE;
        end else begin
            case(state_spi)
                IDLE: begin
                    new_byte <= 0;
                    if(ena_spi)
                        state_spi <= SEND_RECEIVE;
                end
                SEND_RECEIVE: begin
                    new_byte <= 0;
                    if(cnt_miso == 8 && clk_div == MAX_CNT)
                        state_spi <= WAIT_SCL;
                end
                WAIT_SCL: begin
                    if(clk_div == MAX_CNT) begin
                        if(ena_spi)
                            state_spi <= SEND_RECEIVE;
                        else
                            state_spi <= IDLE;
                        new_byte <= 1;                        
                    end

                end
                default: state_spi <= IDLE;
            endcase
        end
    end

    // MOSI
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            cnt_mosi <= 0;
        end else if(state_spi == SEND_RECEIVE) begin
            if(negedge_scl)
                cnt_mosi <= cnt_mosi + 1;
        end
    end
    always_comb mosi <= byte_2_send[cnt_mosi];

    // MISO
    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn) begin
            cnt_miso <= 0;
            byte_received <= 0;
        end else if(state_spi == SEND_RECEIVE) begin
            if(posedge_scl)
                cnt_miso <= cnt_miso + 1;
            byte_received[cnt_miso] <= miso;
        end
    end


    always_comb posedge_scl = (clk_div == HALF_CNT);
    always_comb negedge_scl = (clk_div == 0);


endmodule