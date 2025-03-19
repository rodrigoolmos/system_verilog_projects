`timescale 1us/1ns

// Definición del interface SPI
interface spi_if;
    logic miso;
    logic mosi;
    logic scl;
    logic cs;
endinterface

class agent_spi #(parameter int N_RECEPTIONS = 256);
    // Declaramos un virtual interface del tipo spi_if
    virtual spi_if spi_vif;

    // Arreglo para almacenar bytes leídos
    logic [7:0] bytes_readed[N_RECEPTIONS-1:0];
    int n_bytes_readed = 0;

    // Constructor que recibe el virtual interface y el baudrate
    function new(virtual spi_if spi_vif);
        this.spi_vif = spi_vif;
        spi_vif.miso = 0;
    endfunction

    task recive_data();
        var logic [7:0] received_byte;
        wait(spi_vif.cs == 0);
        for (int i=0; i<8; ++i) begin
            @(posedge spi_vif.scl);
            received_byte[i] = spi_vif.miso;
        end

        bytes_readed[n_bytes_readed] = received_byte;
        n_bytes_readed++;
    endtask

    task send_data(logic [7:0] byte_to_send);
        wait(spi_vif.cs == 0);
        for (int i=0; i<8; ++i) begin
            spi_vif.mosi = byte_to_send[i];
            @(negedge spi_vif.scl);
        end
    endtask


    // Tarea para validar los bytes recibidos
    task validate_received_bytes(logic [7:0] bytes_expected[N_RECEPTIONS-1:0]);
        for (int n_bytes = 0; n_bytes < n_bytes_readed; ++n_bytes) begin
            assert (bytes_expected[n_bytes] == bytes_readed[n_bytes])
                else begin
                    $error("Error los datos enviados y leidos no cuadran %d, %d", 
                        bytes_expected[n_bytes], bytes_readed[n_bytes]);
                    $stop;
                end
        end
    endtask

endclass