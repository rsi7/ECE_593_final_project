// Module: RingBuffer_monitor.sv
// Author: Chris Loop
// Date: March 15th, 2018
// Organization: Portland State University
//
// Monitor for ring buffer module located inside DDR controller.
// This can be enabled via conditional instantiation in the top-level
// testbench to prevent overwhelming number of messages.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module RingBuffer_monitor (dout, listen, strobe, readPtr, din, reset, clk);

	input ulogic1	listen;
	input ulogic1	strobe;
	input ulogic1	reset;
	input ulogic16	din;
	input ulogic3	readPtr;
	input ulogic16	dout;
	input ulogic1	clk;

	int count = 0;
	logic [7:0][15:0] r;
	
	// Monitor when 'reset' is applied to ring buffer
	always @(reset) begin
		if (reset) $display("Ring Buffer Monitor: 'reset' asserted at %t", $time);
	end

	// Monitor when 'listen' is applied to ring buffer
	always @(listen) begin
		if (listen && !reset) $display("Ring Buffer Monitor: 'listen' asserted at %t", $time);
	end

	// Monitor for strobe activity in ring buffer and capture data once it's full
	always @(strobe) begin

		if (!reset && (strobe == 1'b1)) begin
			$display("Ring Buffer Monitor: 'strobe' detected at %t", $time);

			r[0] = din;

			for (int i = 1; i < 8; i++) begin
				@(strobe);
				r[i] = din;
			end

			$display("Ring Buffer Monitor: Data '%x' available in full buffer at %t", r, $time);
		end // if

	end // always @(strobe)

	// Monitor any read data from DRAM leaving the ring buffer...
	always @(readPtr) begin	// any change in readPtr

		if (!reset) begin
			// Wait for output 'dout'
			@(posedge clk); // wait for dout output
			$display("Ring Buffer Monitor: READ transaction of data '%x' from pointer address %1d at %t", dout, readPtr, $time);
		end // if

	end // always @(readPtr)

endmodule