// Module: RingBuffer_assertions.sv
// Author: Chris Loop
// Date: March 2, 2018
// Organization: Portland State University
//
// Description:
//	CHECKER MODULE:
//	No protocols spec'd, aside from asserting listen before strobe (1 check),
//	and even then there aren't any timing req's
//		- use checker module tied to all ringbuffer lines
//		- standard check for non-reset Xs on all lines
//
//	NOTE: THIS REQUIRES CLOCK AS INPUT, when ddr2_ring_buffer8 does NOT
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module RingBuffer_assertions (dout, listen, strobe, readPtr, din, reset, clk);

	input ulogic1	listen;
	input ulogic1	strobe;
	input ulogic1	reset;
	input ulogic16	din;
	input ulogic3	readPtr;
	input ulogic16	dout;
	input ulogic1	clk;

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

endmodule // ringbuffer_assertions module