`include "agent_uart.sv"
`timescale 1us/1ns

// Instancia del interface UART. Este interface declara internamente las señales rx y tx.

module tb_uart;

    int baudrate = 9600;
    int us_bit = 1000000 / baudrate;

    // Declaramos el agente que utilizará el virtual interface
    agent_uart agent_uart_h;
    uart_if uart_inst();
    uart_if uart_tb();
    assign uart_tb.rx = uart_inst.tx;
    assign uart_tb.tx = uart_inst.rx;


    // Tarea para enviar datos directamente desde el testbench a través del interface
    task send_data(logic [7:0] byte_2_send);
        // Utilizamos directamente las señales del interface
        uart_inst.tx = 0;
        #us_bit;
        for (int n_bit = 0; n_bit < 8; n_bit++) begin
            uart_inst.tx = byte_2_send[n_bit];
            #us_bit;
        end
        uart_inst.tx = 1;
        #us_bit;
    endtask

    initial begin
        // Inicializamos la línea tx en idle (alta) a través del interface
        uart_inst.tx = 1;

        // Se crea el agente pasando el virtual interface (uart_inst) y el baudrate
        agent_uart_h = new(uart_tb, baudrate);

        fork
            // Proceso para recibir datos: el agente utiliza el interface para leer rx
            begin
                forever begin
                    agent_uart_h.recive_data();
                end
            end

            // Proceso para enviar datos, combinando envío directo desde el testbench y desde el agente
            begin
                send_data(8'h23);
                #10ns;
                agent_uart_h.send_data(8'h51);
                #10ns;
            end
        join
    end

endmodule
