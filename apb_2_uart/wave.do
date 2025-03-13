onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/arstn
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/BASE_ADDR
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/baudrate
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/byte_2_send
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/byte_recived
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/clk
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/clk_frec
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/done_tx
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/empty_tx
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/FIFO_DEPTH
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/new_byte_rx
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/paddr
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/penable
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pprot
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/prdata
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pready
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/psel
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pslverr
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pstrb
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pwdata
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/pwrite
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/rx
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/send_byte
add wave -noupdate -group top /tb_apb_2_uart/apb_2_uart_inst/tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/arstn
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/baudrate
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/bit_cnt_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/bit_cnt_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/bit_num_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/bit_num_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/byte_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/byte_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/byte_tx_reg
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/clk
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/clk_frec
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/done_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/ff_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/needed_bits
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/new_bit
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/new_byte_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/start_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/state_rx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/state_tx
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/time_bit
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/time_start
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/time_stop
add wave -noupdate -group uart /tb_apb_2_uart/apb_2_uart_inst/physical_uart_inst/tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/ADDR_READ_RX_DATA
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/ADDR_READ_RX_STATUS
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/ADDR_READ_TX_STATUS
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/ADDR_WRITE_TX
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/almost_empty_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/almost_empty_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/almost_full_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/almost_full_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/BASE_ADDR
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/DATA_WIDTH
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/DEPTH
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/empty_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/empty_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/fifo_r_data_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/fifo_w_data_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/full_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/full_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/index_read_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/index_read_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/index_write_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/index_write_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/N_REGS_ADDR
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/paddr
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pclk
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/penable
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pprot
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/prdata
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pready
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/presetn
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/psel
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pslverr
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pstrb
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pwdata
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/pwrite
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/read_fifo_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/read_fifo_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/reg_addr
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/regs_rx
add wave -noupdate -group fifos -expand /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/regs_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/size_fifo_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/size_fifo_tx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/write_fifo_rx
add wave -noupdate -group fifos /tb_apb_2_uart/apb_2_uart_inst/apb_2_fifo_inst/write_fifo_tx
add wave -noupdate /tb_apb_2_uart/agent_uart_h
add wave -noupdate /tb_apb_2_uart/agent_APB_m_h
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {694975430 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {30115601981 ps}
