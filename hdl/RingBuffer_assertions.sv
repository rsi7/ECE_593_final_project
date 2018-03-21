//
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
module RingBuffer_assertions (dout,listen,strobe,readPtr,din,reset, clk);
	input listen;
	input strobe;
	input reset;
	input [15:0]	din;
	input [2:0] 	readPtr;
	input [15:0]	dout;
	input clk;

//listen must be valid unless reset
property ValidListen();
	@(posedge clk) disable iff (reset)
		(!$isunknown(listen));
endproperty
ValidListenAssertion: assert property (ValidListen);


//strobe must be valid unless reset
property ValidStrobe();
	@(posedge clk) disable iff (reset)
		(!$isunknown(strobe));
endproperty
ValidStrobeAssertion: assert property (ValidStrobe);


//din must be valid during strobes, unless reset
property ValidDin();
	@(posedge strobe) disable iff (reset)
		(!$isunknown(din));
endproperty
ValidDinAssertion: assert property (ValidDin);


//readPtr must be valid always, unless reset
property ValidReadPtr();
	@(posedge clk) disable iff (reset)
		(!$isunknown(ReadPtr));
endproperty
ValidReadPtrAssertion: assert property (ValidReadPtr);


//dout must be valid during readPtr change, unless reset
property ValidDout();
	@(ReadPtr)  disable iff (reset)	// possible?
		(!$isunknown(dout));
endproperty
ValidDoutAssertion: assert property (ValidDout);

endmodule // ringbuffer_assertions module
