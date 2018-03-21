// unit_tb_ringbuffer.sv - testbench for ring ddr2_ring_buffer8
//
// Chris Loop
// 3-2-2018
//
//
//	TESTING NOTES:
//		test1: send in r0-7 data, then read it all back via ptr
//		test2: send in half data, read back full r0-7, send in other half, read back full r0-7
//		test3: set ptr to r0, read init val, send in r0, verify new val read back
//		test4: set r0, RESET, verify r0 val on dout during RESET
//		test5: set strobes WITHOUT setting listen first, verify data DIDN'T changed
//
//	use task function(s) in tb to drive stimulus/response:
//		- task for driving listen, strobe, din
//		- task for driving readPtr, latching/checking dout
//
//	CHECKER MODULE:
//	No protocols spec'd, aside from asserting listen before strobe (1 check),
//	and even then there aren't any timing req's
//		- use checker module tied to all ringbuffer lines
//		- standard check for non-reset Xs on all lines
//

`timescale 1ns/10ps

module RingBufferULTB;

// define global params
//
parameter TRUE			= 1'b1;
parameter FALSE		= 1'b0;
parameter CLOCK_WIDTH	= 10;



// define some vars for the testbench
//
logic		reset, listen, strobe, clk;
logic 		[15:0] din;
logic 		[2:0] readPtr;     // inputs to ddr2_ring_buffer8
wire    		[15:0] dout;		// output

int 	num_errors = 0;	// number of errors detected
int datavals[0:7] = '{16'h0, 16'h1111, 16'h2222, 16'h3333, 16'h4444, 16'h5555, 16'h6666, 16'h7777};


// gen the clock
//
initial begin
    clk = FALSE;
    forever #CLOCK_WIDTH clk = ~clk;
end



// instantiate ring buffer
//
ddr2_ring_buffer8 ddr2_ring_buffer8_0 (
	.listen(listen),
	.strobe(strobe),
	.din(din),
	.readPtr(readPtr),
     .dout(dout),
	.reset(reset)
);


// instantiate ringbuffer_monitor
//
ringbuffer_monitor ringbuffer_monitor_0 (
	.listen(listen),
	.strobe(strobe),
	.din(din),
	.readPtr(readPtr),
     .dout(dout),
	.reset(reset),
	.clk(clk)
);

// bind the ring buffer assertion module
//
bind ddr2_ring_buffer8 ringbuffer_assertions AssertCheckRB (
	.listen(listen),
	.strobe(strobe),
	.din(din),
	.readPtr(readPtr),
     .dout(dout),
	.reset(reset),
	.clk(clk)
);

// task to set the ringbuffer (STIMULUS), inputs are:
//	enable listen
//	# times to strobe (2/4/6/8, corresponds to #bytes to read in)
//	din value (16bits)
//
task automatic setRingBuf(int set_listen, int strobes, const ref int din_val[8]);

	strobe = 0;
	if (set_listen) begin
		listen = TRUE;
		@(posedge clk);
	end // if

	listen = FALSE;

	din = din_val[0];
	@(posedge clk);	// timing between listen and strobes isn't spec'd, choosing a clk delay
	strobe = 1;
	@(negedge clk);

	for (int i=1; i<strobes; i++) begin
		din = din_val[i];
		@(posedge clk);
		strobe = ~strobe;
		@(negedge clk);
	end // for

	din = 0;

endtask


// task to read the ringbuffer(STIMULUS), inputs are:
//		readPtr value, expected data_out
//
task automatic readRingBuf(int readPtr_val, int dout_val);

	readPtr = readPtr_val;
	@(posedge clk);

	if (dout !== dout_val) begin	// data didnt match!
		$display("ERROR, expected data: %04x, rec'vd data: %04x!", dout_val, dout);
		num_errors++;
	end // if


endtask


//////////////////////////////////
//  BEGIN STIMULUS
//////////////////////////////////


always begin

// let the system settle for a small time...
//
reset = TRUE;
strobe = 0;
listen = 0;
readPtr = 3'b000;
din = '0;

repeat (5) @(posedge clk);
reset = FALSE;



$display("Testing ringbuffer logic ...\n");

repeat(10) @(posedge clk);

// test 1: send in r0-7 data, then read it all back via ptr
//
setRingBuf(1, 8, datavals);

for (int j=0; j<8; j++) begin
//	readRingBuf(j, (16'h1111 * j) );
	readRingBuf(j, (16'h1111 * j) );
end // for

repeat(10) @(posedge clk);

// test 2: send in half data, read back full r0-7,
//		send in other half, read back full r0-7
//
	datavals[0] = 16'hAAAA; // now datavals[] = xAAAA..xFFFF
	datavals[1] = 16'hBBBB;
	datavals[2] = 16'hCCCC;
	datavals[3] = 16'hDDDD;
	datavals[4] = 16'hAAAA;
	datavals[5] = 16'hBBBB;
	datavals[6] = 16'hCCCC;
	datavals[7] = 16'hDDDD;


setRingBuf(1, 4, datavals);	// 2 strobes, R0-R3 are xAAAA..xDDDD
	readRingBuf(0, 16'hAAAA );
	readRingBuf(1, 16'hBBBB );
	readRingBuf(2, 16'hCCCC );
	readRingBuf(3, 16'hDDDD );
	readRingBuf(4, 16'h4444 );	// back half are still old values
	readRingBuf(5, 16'h5555 );
	readRingBuf(6, 16'h6666 );
	readRingBuf(7, 16'h7777 );

setRingBuf(1, 4, datavals);	// the buffer is still listening: 2 strobes, R4-R7 are xAAAA..xDDDD
	readRingBuf(0, 16'hAAAA );
	readRingBuf(1, 16'hBBBB );
	readRingBuf(2, 16'hCCCC );
	readRingBuf(3, 16'hDDDD );
	readRingBuf(4, 16'hAAAA );	// back half are now new vals
	readRingBuf(5, 16'hBBBB );
	readRingBuf(6, 16'hCCCC );
	readRingBuf(7, 16'hDDDD );

reset = 1;
repeat(10) @(posedge clk);
reset = 0;
repeat(10) @(posedge clk);

// test 3: set ptr to r0, read init val,
//		send in r0, verify new val read back

setRingBuf(1, 8, datavals);	// datavals are xAAAA..xDDDD sequence still

for (int j=0; j<8; j++) begin
	datavals[j] = j * 16'h1111; // now datavals[] = x0000 - x7777 again
end // for

readRingBuf(0, 16'hAAAA );	// read in last value (xAAAA)
setRingBuf(1, 8, datavals);	// send in new datavals
if (dout != 16'h0000) begin	// test directly for new data, though readPtr hasn't changed
	$display("TEST3 ERROR, expected data: 0000, rec'vd data: %04x!\n", dout);
	num_errors++;
end // if


// test 4: set r0, RESET, verify r0 val on dout during RESET
//
reset = TRUE;
repeat (5) @(posedge clk);
if (dout != 16'h00) begin	// test directly for data, readPtr hasn't changed/set
	$display("TEST4 ERROR, expected data: 0000, rec'vd data: %04x!\n", dout);
	num_errors++;
end // if
reset = FALSE;
repeat (5) @(posedge clk);

// test 5: set strobes WITHOUT setting listen first, verify data DIDN'T changed
//

// init the buffer to x00-x77
setRingBuf(1, 8, datavals);

// now datavals[] = xAAAA..xDDDD
datavals[0] = 16'hAAAA;
datavals[1] = 16'hBBBB;
datavals[2] = 16'hCCCC;
datavals[3] = 16'hDDDD;
datavals[4] = 16'hAAAA;
datavals[5] = 16'hBBBB;
datavals[6] = 16'hCCCC;
datavals[7] = 16'hDDDD;


setRingBuf(0, 8, datavals);	// try to send in new data, strobes but NO LISTEN

// read back original values
for (int j=0; j<8; j++) begin
	readRingBuf(j, (16'h1111 * j) );
end // for


repeat (50) @(posedge clk);



// end of testing, check for errors and report
//
if (num_errors > 0) $display ("Done, ERRORS detected!");
else $display("Done.  No Errors found.");
$stop;

end // always

endmodule // unit level ringbuffer tb


// checker module, built in concurrent assertions
//	NOTE: THIS REQUIRES CLOCK AS INPUT, when ddr2_ring_buffer8 does NOT
//
module ringbuffer_assertions (dout,listen,strobe,readPtr,din,reset, clk);
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
		(!$isunknown(readPtr));
endproperty
ValidReadPtrAssertion: assert property (ValidReadPtr);


//dout must be valid during readPtr change, unless reset
property ValidDout();
	@(readPtr)  disable iff (reset)	// possible?
		(!$isunknown(dout));
endproperty
ValidDoutAssertion: assert property (ValidDout);

endmodule // ringbuffer_assertions module


// monitor module, this will be enabled via conditional instantiation in top level
//
module ringbuffer_monitor (dout,listen,strobe,readPtr,din,reset,clk);
	input listen;
	input strobe;
	input reset;
	input [15:0]	din;
	input [2:0] 	readPtr;
	input [15:0]	dout;
	input clk;

	int count = 0;

always @(reset) if (reset) $display("%m time %0t: RESET asserted", $time);

always @(listen) if (listen && !reset) $display("%m time %0t: LISTEN asserted", $time);

always @(strobe) begin
	if (!reset) begin
		$display("%m time %0t: STROBE detected, data=%04h, byte R%0d", $time, din, count);
		if (count == 7) count = 0;
		else count++;
	end // if
end // always strobe

always @(readPtr) begin	// any change in readPtr
	if (!reset) begin
		@(posedge clk); // wait for dout output
		$display("%m time %0t: ReadPtr=%03b , data=%04h", $time, readPtr, dout);
	end // if
end // always

endmodule
