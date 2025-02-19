module dht22_cntr #(
        parameter CLK_FREQ = 100000000
    )(
    input  logic clk,
    input  logic arstn,
    input  logic dht22_in,
    input  logic start_read,
    output logic dht22_out,
    output logic dht22_dir, // 1 in 0 out
    output logic sys_idle,
    output logic [15:0] humidity,
    output logic [15:0] temperature,
    output logic [7:0] parity
);
    
    typedef enum logic[2:0] {idle, trigger_start, release_host,
                            start_dev_low, start_dev_hight, reciving} state_t_dht22;

    state_t_dht22 state_dht22;

    localparam clk_40_us = CLK_FREQ/25000;
    localparam clk_2_ms = CLK_FREQ/500;
    logic [($clog2(CLK_FREQ/500)):0] cnt; // cnt up to 4ms

    logic rest_cnt;
    logic[3:0] meta_dht22;
    logic negedge_dht22;
    logic[5:0] n_bits;
    logic[39:0] data_dht22;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            meta_dht22 <= 4'b1111;
        end else begin
            meta_dht22 <= {meta_dht22[2:0], dht22_in};
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            cnt <= 0;
        end else begin
            if (rest_cnt) begin
                cnt <= 0;
            end else begin
                cnt <= cnt + 1;
            end
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            state_dht22 <= idle;
        end else begin
            case (state_dht22)
                idle: begin
                    if (start_read) begin
                        state_dht22 <= trigger_start;
                        rest_cnt <= 1;
                    end
                end
                trigger_start: begin
                    rest_cnt <= 0;
                    if (cnt == clk_2_ms) begin
                        rest_cnt <= 1;
                        state_dht22 <= release_host;
                    end
                end
                release_host: begin
                    if (meta_dht22[3] == 0) begin
                        state_dht22 <= start_dev_low;
                    end
                end
                start_dev_low: begin
                    if (meta_dht22[3] == 1) begin
                        state_dht22 <= start_dev_hight;
                    end
                end
                start_dev_hight: begin
                    if (meta_dht22[3] == 0) begin
                        state_dht22 <= reciving;
                    end
                end
                reciving: begin
                    if (meta_dht22[3]) begin
                        rest_cnt <= 0;
                    end else begin
                        rest_cnt <= 1;
                    end
                    if (n_bits == 40) begin
                        state_dht22 <= idle;
                    end
                end
                default: begin
                    state_dht22 <= idle;
                end
            endcase
        end
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            n_bits <= 0;
            data_dht22 <= 0;
        end else begin
            if (state_dht22 == reciving) begin
                if (negedge_dht22) begin
                    if (n_bits < 40) begin
                        n_bits <= n_bits + 1;
                        if (cnt < clk_40_us) begin
                            data_dht22 <= {data_dht22[38:0], 1'b0};
                        end else begin
                            data_dht22 <= {data_dht22[38:0], 1'b1}; 
                        end
                    end
                end 
            end else begin
                n_bits <= 0;
            end
        end
    end

    always_comb negedge_dht22 <= meta_dht22[3] & !meta_dht22[2];

    always_comb begin
        humidity <= data_dht22[39:24];
        temperature <= data_dht22[23:8];
        parity <= data_dht22[7:0];
    end
    
    always_comb sys_idle <= (state_dht22 == idle) ? 1 : 0;

    always_comb dht22_out <= (state_dht22 == trigger_start) ? 0 : 1;

    always_comb dht22_dir <= dht22_out;


endmodule