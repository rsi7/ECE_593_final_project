// Module: RingBuffer_monitor.sv
// Author: Chris Loop
// Date: March 15th, 2018
// Organization: Portland State University
//
// Description:
// 	ring buffer monitor module, this can be enabled via
//	conditional instantiation in top level
//
module RingBuffer_monitor (dout,listen,strobe,readPtr,din,reset,clk);
	input listen;
	input strobe;
	input reset;
	input [15:0]	din;
	input [2:0] 	readPtr;
	input [15:0]	dout;
	input clk;

	int count = 0;
	logic [7:0][15:0] r;	// reg values

always @(reset) if (reset) $display("%m time %0t: RESET asserted", $time);

always @(listen) if (listen && !reset) $display("%m time %0t: LISTEN asserted", $time);

always @(strobe) begin
	if (!reset && (strobe == 1'b1)) begin
		//$display("%m time %0t: STROBE detected, data=%04h, byte R%0d", $time, din, count);
		$display("%m time %0t: STROBE detected", $time);

		r[0] = din;
		for (int i=1; i<8; i++) begin
			@(strobe);	// latch data
			r[i] = din;
		end // for
		$display("%m time %0t: BUFFER FULL, data=%x", $time, r);

	end // if
end // always strobe

always @(readPtr) begin	// any change in readPtr
	if (!reset) begin
		@(posedge clk); // wait for dout output
		$display("%m time %0t: ReadPtr=%03b , data=%04h", $time, readPtr, dout);
	end // if
end // always

endmodule
