module rmii #(

) (
    // RMII Interface (MAC ↔ PHY)
    input  logic        RMII_REF_CLK,   // 50 MHz reference clock (REF_CLK_IN)
    input  logic        RMII_TX_EN,     // Indica que TXD[1:0] es válido
    input  logic [1:0]  RMII_TXD,       // Datos de TX (paralelo 2 bits)
    output logic        RMII_CRS_DV,    // Carrier Sense + Data Valid
    output logic [1:0]  RMII_RXD,       // Datos de RX (paralelo 2 bits)

    // MDIO/MDC Management Interface
    inout  logic        MDIO,           // Canal de datos bidireccional
    input  logic        MDC             // Reloj de gestión (≤ 2.5 MHz)
);
    


endmodule