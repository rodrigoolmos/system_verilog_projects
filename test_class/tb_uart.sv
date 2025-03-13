`include "agent_uart.sv"

module tb_uart;
    // Instanciamos dos interfaces, uno para el agente y otro para el testbench.
    uart_if agent_if();
    uart_if tb_if();

    // Conexión cruzada de señales:
    // La transmisión del agente se conecta a la recepción del TB y viceversa.
    assign agent_if.rx = tb_if.tx;
    assign tb_if.rx = agent_if.tx;
    
    int baudrate = 9600;
    int us_bit = 1000000 / baudrate;

    agent_uart agent_uart_h;

    // Tarea para enviar datos desde el testbench usando su interfaz (tb_if)
    task send_data_via_tb(logic [7:0] byte_2_send);
        tb_if.tx = 0; // bit de start
        #us_bit;
        for (int n_bit = 0; n_bit < 8; n_bit++) begin
            tb_if.tx = byte_2_send[n_bit];
            #us_bit;
        end
        tb_if.tx = 1; // bit de stop (idle)
        #us_bit;
        $display("TB envió: %h a tiempo %0t", byte_2_send, $time);
    endtask

    initial begin
        // Inicializamos las señales en estado inactivo
        agent_if.tx = 1;
        tb_if.tx = 1;

        // Se instancia el agente, pasándole su interface (agent_if) y el baudrate.
        agent_uart_h = new(agent_if, baudrate);

        fork
            // Proceso del agente: se queda recibiendo datos indefinidamente.
            begin
                forever begin
                    agent_uart_h.recive_data();
                end
            end

            // Proceso del testbench: envía datos por su extremo.
            begin
                send_data_via_tb(8'h23);  // Envío desde el TB
                #10ns;
                agent_uart_h.send_data(8'h51); // Envío desde el agente
                #10ns;
            end
        join
    end
endmodule
