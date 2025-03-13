`timescale 1us/1ns

// Definición del interface UART
interface uart_if;
    logic rx;
    logic tx;
endinterface

// Clase que utiliza el virtual interface
class agent_uart #(parameter int N_RECEPTIONS = 256);
    // Declaramos un virtual interface del tipo uart_if
    virtual uart_if uart_vif;

    // Arreglo para almacenar bytes leídos y otras variables
    logic [7:0] bytes_readed[N_RECEPTIONS];
    int n_bytes_readed = 0;
    integer us_bit;

    // Constructor que recibe el virtual interface y el baudrate
    function new(virtual uart_if uart_vif, int baudrate);
        this.uart_vif = uart_vif;
        this.us_bit = 1000000 / baudrate;
        // Aseguramos que la línea de transmisión esté en estado inactivo (alta)
        this.uart_vif.tx = 1;
    endfunction

    // Tarea para recibir datos a través de la línea rx
    task recive_data();
        var logic [7:0] rx_byte;
        rx_byte = 0;
        // Espera el flanco descendente de rx para detectar el inicio del bit de start
        @(negedge uart_vif.rx);
        #(3 * us_bit / 2);
        // Lectura de los 8 bits de datos
        for (int n_bit = 0; n_bit < 8; n_bit++) begin
            rx_byte[n_bit] = uart_vif.rx;
            #us_bit;
        end
        #(us_bit / 2);
        bytes_readed[n_bytes_readed] = rx_byte;
        n_bytes_readed++;
    endtask

    // Tarea para enviar datos a través de la línea tx
    task send_data(logic [7:0] byte_2_send);
        uart_vif.tx = 0; // Bit de start
        #us_bit;
        // Transmisión de los 8 bits de datos
        for (int n_bit = 0; n_bit < 8; n_bit++) begin
            uart_vif.tx = byte_2_send[n_bit];
            #us_bit;
        end
        uart_vif.tx = 1; // Bit de stop (idle)
        #us_bit;
    endtask

    // Tarea para validar los bytes recibidos (por implementar)
    task validate_rx_bytes(logic [7:0] bytes_expected[N_RECEPTIONS]);
        for (int n_bytes = 0; n_bytes < n_bytes_readed; ++n_bytes) begin
            assert (bytes_expected[n_bytes] == bytes_readed[n_bytes])
                else begin
                    $error("Assertion  failed!");
                    $stop;
                end
        end
    endtask
endclass
