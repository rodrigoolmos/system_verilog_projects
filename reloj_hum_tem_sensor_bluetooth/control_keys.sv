module control_keys(
    input logic clk,
    input logic arstn,
    input logic key_up,
    input logic key_down,
    input logic key_mid,
    input logic key_left,
    input logic key_right,

    output logic clock_ena,
    output logic tic_key_up,
    output logic tic_key_down,
    output logic[5:0] position
);
    
    logic tic_key_mid;
    logic tic_key_left;
    logic tic_key_right;

    key_handler debouncing_up(
        .key(key_up),
        .tic(tic_key_up),
        .*);

    key_handler debouncing_down(
        .key(key_down),
        .tic(tic_key_down),
        .*);

    key_handler debouncing_left(
        .key(key_left),
        .tic(tic_key_left),
        .*);

    key_handler debouncing_right(
        .key(key_right),
        .tic(tic_key_right),
        .*);

    key_handler debouncing_mid(
        .key(key_mid),
        .tic(tic_key_mid),
        .*);

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            clock_ena <= 0;
        else if(tic_key_mid)
            clock_ena <= ~clock_ena;
    end

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn)
            position <= 1;
        else if(tic_key_left)
            position <= {position[4:0], position[5]};
        else if(tic_key_right)
            position <= {position[0], position[5:1]};
    end

endmodule










