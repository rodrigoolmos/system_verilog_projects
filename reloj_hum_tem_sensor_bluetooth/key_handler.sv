module key_handler(
    input logic clk,
    input logic arstn,
    input logic key,
    output logic tic
);

    logic[19:0] cnt;
    logic debounced_t0;
    logic debounced_t1;
    logic[1:0] key_ff;

    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn)
            key_ff <= 0;    
        else
            key_ff <= {key_ff[0], key};
    end

    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn)
            cnt <= 1000000;    
        else
            if(cnt < 1000000)
                cnt <= cnt + 1;
            else if (key_ff[1])
                cnt <= 0;
    end

    always_comb debounced_t0 <= (cnt < 1000000 || key_ff[1] == 1) ? 1 : 0;


    always_ff @(posedge clk or negedge arstn) begin
        if(!arstn)
            debounced_t1 <= 0;    
        else
            debounced_t1 <= debounced_t0;
    end

    always_comb tic <= (debounced_t0 && ~debounced_t1) ? 1 : 0;

endmodule