onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color White /top_tb/clk
add wave -noupdate -color White /top_tb/c0_ck_pad
add wave -noupdate -color White /top_tb/c0_ckbar_pad
add wave -noupdate -color {Pale Green} /top_tb/c0_a_pad
add wave -noupdate -color {Pale Green} /top_tb/c0_ba_pad
add wave -noupdate -color {Pale Green} /top_tb/c0_cke_pad
add wave -noupdate -color Aquamarine /top_tb/c0_dq_pad
add wave -noupdate -color Aquamarine -subitemconfig {{/top_tb/c0_dqs_pad[1]} {-color Aquamarine} {/top_tb/c0_dqs_pad[0]} {-color Aquamarine}} /top_tb/c0_dqs_pad
add wave -noupdate -color Magenta -radix binary /top_tb/c0_dm_pad
add wave -noupdate -color Magenta /top_tb/c0_odt_pad
add wave -noupdate -color {Indian Red} /top_tb/i_ddr2_dram/addr_reg
add wave -noupdate -expand -group CMD -color Gold /top_tb/c0_csbar_pad
add wave -noupdate -expand -group CMD -color Gold /top_tb/c0_rasbar_pad
add wave -noupdate -expand -group CMD -color Gold /top_tb/c0_casbar_pad
add wave -noupdate -expand -group CMD -color Gold /top_tb/c0_webar_pad
add wave -noupdate -color {Cornflower Blue} /top_tb/i_ddr2_dram/en_dq
add wave -noupdate -color {Cornflower Blue} /top_tb/i_ddr2_dram/en_dqs
add wave -noupdate -color {Cornflower Blue} /top_tb/i_ddr2_dram/en_dqs_n
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {202988969 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 188
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {202476232 ps} {202695279 ps}
