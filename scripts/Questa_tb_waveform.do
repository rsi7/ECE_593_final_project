onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color White /tb/clk
add wave -noupdate -color White /tb/c0_ck_pad
add wave -noupdate -color White /tb/c0_ckbar_pad
add wave -noupdate -color {Pale Green} /tb/c0_a_pad
add wave -noupdate -color {Pale Green} /tb/c0_ba_pad
add wave -noupdate -color {Pale Green} /tb/c0_cke_pad
add wave -noupdate -color Aquamarine /tb/c0_dq_pad
add wave -noupdate -color Aquamarine -subitemconfig {{/tb/c0_dqs_pad[1]} {-color Aquamarine} {/tb/c0_dqs_pad[0]} {-color Aquamarine}} /tb/c0_dqs_pad
add wave -noupdate -color Magenta -radix binary /tb/c0_dm_pad
add wave -noupdate -color Magenta /tb/c0_odt_pad
add wave -noupdate -color {Indian Red} /tb/i_ddr2_dram/addr_reg
add wave -noupdate -expand -group CMD -color Gold /tb/c0_csbar_pad
add wave -noupdate -expand -group CMD -color Gold /tb/c0_rasbar_pad
add wave -noupdate -expand -group CMD -color Gold /tb/c0_casbar_pad
add wave -noupdate -expand -group CMD -color Gold /tb/c0_webar_pad
add wave -noupdate -color {Cornflower Blue} /tb/i_ddr2_dram/en_dq
add wave -noupdate -color {Cornflower Blue} /tb/i_ddr2_dram/en_dqs
add wave -noupdate -color {Cornflower Blue} /tb/i_ddr2_dram/en_dqs_n
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