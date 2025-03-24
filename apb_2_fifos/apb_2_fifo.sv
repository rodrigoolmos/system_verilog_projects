module apb_2_fifo #(
    parameter BASE_ADDR = 8,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 16    // power of 2
) (
    input  logic                      pclk,
    input  logic                      presetn,

    // apb
    input  logic [31:0]               paddr,
    input  logic [2:0]                pprot,
    input  logic                      psel,
    input  logic                      penable,
    input  logic                      pwrite,
    input  logic [DATA_WIDTH-1:0]     pwdata,
    input  logic [(DATA_WIDTH/8)-1:0] pstrb,
    output logic                      pready,
    output logic [DATA_WIDTH-1:0]     prdata,
    output logic                      pslverr,

    // fifo out tx
    input  logic                      read_fifo_tx,
    output logic                      empty_tx,
    output logic                      almost_empty_tx,
    output logic [DATA_WIDTH-1:0]     fifo_r_data_tx,

    // fifo in rx
    input  logic                      write_fifo_rx,
    output logic                      full_rx,
    output logic                      almost_full_rx,
    input  logic [DATA_WIDTH-1:0]     fifo_w_data_rx
);

    localparam ADDR_READ_TX_STATUS  = 2'b00;
    localparam ADDR_WRITE_TX        = 2'b00;
    localparam ADDR_READ_RX_STATUS  = 2'b01;
    localparam ADDR_READ_RX_DATA    = 2'b10;

    localparam N_REGS_ADDR          = 3;



    logic[DATA_WIDTH-1:0]       regs_tx[DEPTH-1:0];
    logic[$clog2(DEPTH)-1:0]    index_write_tx;
    logic[$clog2(DEPTH)-1:0]    index_read_tx;
    logic[$clog2(DEPTH):0]      size_fifo_tx;
    logic                       almost_full_tx;
    logic                       full_tx;
    logic                       write_fifo_tx;


    logic[DATA_WIDTH-1:0]       regs_rx[DEPTH-1:0];
    logic[$clog2(DEPTH)-1:0]    index_write_rx;
    logic[$clog2(DEPTH)-1:0]    index_read_rx;
    logic[$clog2(DEPTH):0]      size_fifo_rx;
    logic                       almost_empty_rx;
    logic                       empty_rx;
    logic                       read_fifo_rx;

    logic [3:0] reg_addr;

    /*******************      RX      *********************/
    // Logica escritura fifo rx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            index_write_rx <= 0;
            for (int i=0; i<DEPTH; ++i)
                regs_rx[i] <= 0;
        end else begin
            if (write_fifo_rx & ~full_rx) begin
                index_write_rx <= index_write_rx + 1;
                regs_rx[index_write_rx] <= fifo_w_data_rx;
            end
        end
    end

    // upodate index read fifo rx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            index_read_rx <= 0;
        end else begin
            if (read_fifo_rx & ~empty_rx) begin
                index_read_rx <= index_read_rx + 1;
            end
        end
    end

    // update size fifo rx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            size_fifo_rx <= DEPTH;
        end else begin
            case ({write_fifo_rx & ~full_rx, read_fifo_rx & ~empty_rx})
                2'b10: size_fifo_rx <= size_fifo_rx - 1;
                2'b01: size_fifo_rx <= size_fifo_rx + 1;
                default: size_fifo_rx <= size_fifo_rx;
            endcase        
        end
    end

    // calculate fifo size rx
    always_comb begin
        full_rx = size_fifo_rx == 0;
        almost_full_rx = size_fifo_rx == 1;
        empty_rx = size_fifo_rx == DEPTH;
        almost_empty_rx = size_fifo_rx == DEPTH - 1;
    end
    
    // enable read fifo rx
    always_comb read_fifo_rx = psel & ~pwrite & penable & ~pslverr & (reg_addr[3:2] == ADDR_READ_RX_DATA);

    /*******************      TX      *********************/
    // Logica escritura APB a fifo tx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            index_write_tx <= 0;  
            for (int i=0; i<DEPTH; ++i)
                regs_tx[i] <= 0;
        end else if (write_fifo_tx & ~full_tx) begin
            index_write_tx <= index_write_tx + 1;
            regs_tx[index_write_tx] <= pwdata;
        end
    end

    // Logica lectura fifo tx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            index_read_tx <= 0;
        end else if (read_fifo_tx & ~empty_tx) begin
            index_read_tx <= index_read_tx + 1;
        end
    end

    // update size fifo tx
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            size_fifo_tx <= DEPTH;
        end else begin
            case ({write_fifo_tx & ~full_tx, read_fifo_tx & ~empty_tx})
                2'b10: size_fifo_tx <= size_fifo_tx - 1;
                2'b01: size_fifo_tx <= size_fifo_tx + 1;
                default: size_fifo_tx <= size_fifo_tx;
            endcase        
        end
    end

    // calculate fifo size tx
    always_comb begin
        full_tx = size_fifo_tx == 0;
        almost_full_tx = size_fifo_tx == 1;
        empty_tx = size_fifo_tx == DEPTH;
        almost_empty_tx = size_fifo_tx == DEPTH - 1;
    end

    // read data from fifo tx
    always_comb fifo_r_data_tx = regs_tx[index_read_tx];

    // enable write to fifo tx
    always_comb write_fifo_tx = psel & pwrite & penable & ~pslverr & (reg_addr[3:2] == ADDR_WRITE_TX);



    /****************** APB *****************/
    // Señal de transferencia realizada
    always_comb pready = penable & psel;
    // Error si la dirección está fuera de rango
    always_comb pslverr = (paddr < BASE_ADDR || paddr > BASE_ADDR + 4*(N_REGS_ADDR-1)) & penable;
    // calculate reg @drres base on paddr
    always_comb reg_addr = paddr - BASE_ADDR;

    // lectura apb
    always_comb begin
        if (penable && !pslverr && psel && !pwrite) begin
            case (reg_addr[3:2])
                ADDR_READ_TX_STATUS: prdata = {{28{1'b0}}, full_tx, almost_full_tx, empty_tx, almost_empty_tx};
                ADDR_READ_RX_STATUS: prdata = {{28{1'b0}}, full_rx, almost_full_rx, empty_rx, almost_empty_rx};
                ADDR_READ_RX_DATA:   prdata = regs_rx[index_read_rx];
                default: prdata = 0;
            endcase
        end else begin
            prdata = 0;
        end
    end

endmodule
