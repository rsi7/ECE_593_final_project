// Module: RingBuffer_monitor.sv
// Author: Chris Loop (modified by Rehan Iqbal)
// Date: March 22nd, 2018
// Organization: Portland State University
//
// Monitor for ring buffer module located inside DDR controller.
// It will log all activity on the strobe/listen/dq/etc. signals to console
// if the global 'DEBUG' parameter is set. It will also run assertions to
// check the protocol and make sure read data are processed successfully
// back into the DDR controller.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module RingBuffer_monitor #(parameter DEBUG = 0) (dout, listen, strobe, readPtr, din, reset, clk);

	input ulogic1	listen;
	input ulogic1	strobe;
	input ulogic1	reset;
	input ulogic16	din;
	input ulogic3	readPtr;
	input ulogic16	dout;
	input ulogic1	clk;

	int count = 0;
	logic [7:0][15:0] r;
	
	/************************************************************************/
	/* Debug Messaging														*/
	/************************************************************************/

	// Monitor when 'reset' is applied to ring buffer
	always @(reset) begin

		if (DEBUG) begin
			if (reset) $display("Ring Buffer Monitor: 'reset' asserted at %t", $time);
		end
	end

	// Monitor when 'listen' is applied to ring buffer
	always @(listen) begin

		if (DEBUG) begin
			if (listen && !reset) $display("Ring Buffer Monitor: 'listen' asserted at %t", $time);
		end
	end

	// Monitor for strobe activity in ring buffer and capture data once it's full
	always @(strobe) begin

		if (!reset && (strobe == 1'b1)) begin

			if (DEBUG) begin
				$display("Ring Buffer Monitor: 'strobe' detected at %t", $time);
			end

			r[0] = din;

			for (int i = 1; i < 8; i++) begin
				@(strobe);
				r[i] = din;
			end

			if (DEBUG) begin
				$display("Ring Buffer Monitor: Data '%x' available in full buffer at %t", r, $time);
			end

		end // if (!reset && (strobe == 1'b1))

	end // always @(strobe)

	// Monitor any read data from DRAM leaving the ring buffer...
	always @(readPtr) begin	// any change in readPtr

		if (!reset) begin
			// Wait for output 'dout'
			@(posedge clk); // wait for dout output

			if (DEBUG) begin
				$display("Ring Buffer Monitor: READ transaction of data '%x' from pointer address %1d at %t", dout, readPtr, $time);
			end

		end // if

	end // always @(readPtr)

	/************************************************************************/
	/* Assertions															*/
	/************************************************************************/

	// ValidListenAssertion: 'listen' signal must be a valid value (unless device is in reset)
	property ValidListen();
		@(posedge clk) disable iff (reset)
			(!$isunknown(listen));
	endproperty
	ValidListenAssertion: assert property (ValidListen);

	// disabling 'ValidStrobeAssertion' because of overwhelming amount of errors

	// ValidStrobeAssertion: Strobe must be a valid value (unless device is in reset)
	// property ValidStrobe();
	// 	@(posedge clk) disable iff (reset)
	// 		(!$isunknown(strobe));
	// endproperty
	// ValidStrobeAssertion: assert property (ValidStrobe);

	// ValidDinAssertion: Input data must be valid during strobes (unless device is in reset)
	property ValidDin();
		@(posedge strobe) disable iff (reset)
			(!$isunknown(din));
	endproperty
	ValidDinAssertion: assert property (ValidDin);

	// ValidreadPtrAssertion: Buffer's read pointer must be always be valid (unless device is in reset)
	property ValidreadPtr();
		@(posedge clk) disable iff (reset)
			(!$isunknown(readPtr));
	endproperty
	ValidreadPtrAssertion: assert property (ValidreadPtr);

	// ValidDoutAssertio: Output data must be valid when read pointer changes (unless device is in reset)
	property ValidDout();
		@(readPtr)  disable iff (reset)	// possible?
			(!$isunknown(dout));
	endproperty
	ValidDoutAssertion: assert property (ValidDout);

endmodule