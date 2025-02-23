module dht22_CRC (
    output logic correct_data,
    input logic [15:0] humidity,
    input logic [15:0] temperature,
    input logic [7:0] parity
);


    always_comb begin
        correct_data <= (humidity[15:8] + humidity[7:0] + temperature[15:8] + temperature[7:0] == parity) ? 1 : 0; 
    end

endmodule