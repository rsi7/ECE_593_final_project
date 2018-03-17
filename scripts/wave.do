onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color White /tb/clk
add wave -noupdate -color White /tb/c0_ck_pad
add wave -noupdate -color Cyan /tb/reset
add wave -noupdate -color Cyan /tb/r
add wave -noupdate -color Cyan /tb/c
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/WaitCycles
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/Cmd
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/cmd
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/Sz
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/sz
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/Op
add wave -noupdate -color Yellow -radix unsigned -radixshowbase 0 /tb/op
add wave -noupdate -color Red /tb/Addr
add wave -noupdate -color Red /tb/addr
add wave -noupdate -color Red /tb/c0_a_pad
add wave -noupdate -color Red /tb/raddr
add wave -noupdate -color {Spring Green} /tb/Data
add wave -noupdate -color {Spring Green} /tb/c0_dq_pad
add wave -noupdate -color {Spring Green} /tb/dout
add wave -noupdate -color {Spring Green} /tb/din
add wave -noupdate -color Orange /tb/fillcount
add wave -noupdate -color Orange /tb/notfull
add wave -noupdate -color Orange /tb/ready
add wave -noupdate -color Orange /tb/validout
add wave -noupdate -color Orange /tb/fetching
add wave -noupdate -color Orange /tb/initddr
add wave -noupdate -color Orange /tb/DataFifoHasSpace
add wave -noupdate -color Orange /tb/CmdFifoHasSpace
add wave -noupdate -color Orange /tb/test_pattern_injection_done
add wave -noupdate -color Orange /tb/cycle_counter
add wave -noupdate -color Orange /tb/start_count
add wave -noupdate -color Orange /tb/end_count
add wave -noupdate -color Orange /tb/Fetching
add wave -noupdate -color Orange /tb/waiting
add wave -noupdate -color Orange /tb/BlkWriteInProgress
add wave -noupdate -color Orange /tb/fetchNextTestPattern
add wave -noupdate -color Orange /tb/ApplyTestPattern
add wave -noupdate -color Orange /tb/waitCount
add wave -noupdate -color Orange /tb/blkWriteCount
add wave -noupdate -color Orange /tb/non_read_cmd_consumed
add wave -noupdate -color Orange /tb/read_cmd_consumed
add wave -noupdate -color Orange /tb/nop_consumed
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {203015337 ps} 0}
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
WaveRestoreZoom {202979199 ps} {203001101 ps}
