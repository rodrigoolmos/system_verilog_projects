module fifo #(
    parameter WIDTH = 32,
    parameter DEPTH = 16    // power of 2
) (
    input  logic clk,
    input  logic arstn,
    input  logic[WIDTH-1:0] data_in,
    output logic[WIDTH-1:0] data_out,
    input  logic read,
    input  logic write,
    output logic empty,
    output logic almost_empty,
    output logic full,
    output logic almost_full
);
    
    logic[WIDTH-1:0] regs[DEPTH-1:0];
    logic[$clog2(DEPTH)-1:0] index_write;
    logic[$clog2(DEPTH)-1:0] index_read;
    logic[$clog2(DEPTH):0]   size_fifo;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            index_read <= 0;
            index_write <= 0;            
            for (int i=0; i<DEPTH; ++i)
                regs[i] <= 0;
        end else begin
            if (write & ~full) begin
                index_write <= index_write + 1;
                regs[index_write] <= data_in;
            end
            if (read & ~empty) begin
                index_read <= index_read + 1;
            end
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            size_fifo <= DEPTH;
        end else begin
            case ({write & ~full, read & ~empty})
                2'b10: size_fifo <= size_fifo - 1;
                2'b01: size_fifo <= size_fifo + 1;
                default: size_fifo <= size_fifo;
            endcase        
        end
    end

    always_comb begin
        full <= size_fifo == 0;
        almost_full <= size_fifo == 1;        
        empty <= size_fifo == DEPTH;
        almost_empty <= size_fifo == DEPTH - 1;        
    end

    always_comb data_out <= regs[index_read];

endmodule