// Module: tb.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// The testbench provides a 500MHz clock (250MHz DDR clock) and active-low reset... 
// after reset a one-cycle long 'initddr' signal is issued. 
// Testbench then waits for the 'ready' signal to come out of DDR2 controller,
// which handles this through the 'init_enginer' module.
//
// After 'ready' goes high, the testbench initiates the first 'FetchNextTestPattern'
// task in the driver module. Then it waits - Once all patterns have been read,
// 'test_pattern_injection_done' flag set in the driver module will let the 
// testbench know to end simulation.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"
`timescale  1ns / 10ps

module tb();

	`define INPUT_FILE_NAME "C:/Users/riqbal/Dropbox/ECE 593/Final Project/hdl/ddr2_test_pattern.txt"

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	/////////////
	// Globals //
	/////////////

	ulogic1		clk = 0;
	ulogic1		reset = 1;

	////////////////////////////////////
	// Testbench <--> DDR2 controller //
	////////////////////////////////////

	// Testbench --> DDR2 controller
	ulogic1		initddr = 0;

	// DDR2 controller --> Testbench
	ulogic1		ready;
	ulogic16	dout;
	ulogic25	raddr;
	ulogic1		validout;

	////////////////////////////////////////////
	// Controller driver <--> DDR2 controller //
	////////////////////////////////////////////

	// Driver --> DDR2 controller
	ulogic3 	cmd;
	ulogic2 	sz;
	ulogic3 	op;
	ulogic1		fetching;
	ulogic16	din;
	ulogic25 	addr;

	// DDR2 controller --> driver
	ulogic7		fillcount;
	ulogic1		notfull;

	/////////////////////////////
	// DDR2 controller --> RAM //
	/////////////////////////////
	
	ulogic1		c0_ck_pad;
	ulogic1		c0_ckbar_pad;
	ulogic1		c0_cke_pad;

	ulogic2 	c0_ba_pad;
	ulogic13	c0_a_pad;

	ulogic1		c0_csbar_pad;
	ulogic1		c0_casbar_pad;
	ulogic1		c0_rasbar_pad;
	ulogic1		c0_webar_pad;

	// Bidirectional data signals
	wire	[15:0]	c0_dq_pad;
	wire 	[1:0]	c0_dqs_pad;
	wire 	[1:0]	c0_dqsbar_pad;

	ulogic2 	c0_dm_pad;
	ulogic1		c0_odt_pad;

	/************************************************************************/
	/* System clock generation												*/
	/************************************************************************/

	// Run system-clock at 500MHz
	always #1 clk = ~clk;

	/************************************************************************/
	/* Main simulation block												*/
	/************************************************************************/

	initial begin

		$timeformat(-9, 0, "ns", 8);

		// clear the 'reset' to DDR2 controller...
		// then kick-off its initialization sequence
		repeat (5) @(negedge clk);
		reset = 0;
		@(negedge clk);
		initddr  = 1;
		@(negedge clk);
		initddr  = 0;

		// Check 'ready' flag to determine when controller has been initialized
		$display("Testbench: Waiting for DDR2 controller to become ready...");
		wait (ready);
		$display("Testbench: DDR2 controller is ready... now reading input test pattern file");

		// Open test pattern input file... return error if file not found
		InputFileCheck : assert ((i_controller_driver.fhandle_in = $fopen(`INPUT_FILE_NAME, "r")) != 0) begin
			$display("Testbench: Opened input file '%s' successfully!", `INPUT_FILE_NAME);
		end

		else begin
			$error("Testbench: Cannot open file '%s'!", `INPUT_FILE_NAME);
			$stop;
		end

		// Start reading the input file's test patterns
		@(posedge clk);
		-> i_controller_driver.fetchNextTestPattern;

		// All patterns from input file have been read... time to wrap up simulation
		@(posedge i_controller_driver.test_pattern_injection_done);
		$display("Testbench: All test patterns are successfully applied!");
		$display("Testbench: Now waiting to let the DDR2 controller drain out...");
		
		repeat (1500) @(negedge clk);
		$display("Testbench: End of simulation at %t", $time);
		$stop;

	end // initial begin

	/************************************************************************/
	/* Instance: Controller Driver											*/
	/************************************************************************/

	controller_driver i_controller_driver (

		// Globals
		.clk			(clk), 
		.reset			(reset),

		// DDR2 controller --> driver
		.fillcount		(fillcount),
		.notfull		(notfull),

		// Driver --> DDR2 controller
		.cmd			(cmd),
		.sz				(sz),
		.op				(op),
		.fetching		(fetching),
		.din			(din),
		.addr			(addr)
	
	);

	/************************************************************************/
	/* Instance: DDR2 Controller											*/
	/************************************************************************/

	ddr2_controller i_ddr2_controller (

		// Globals
		.CLK					(clk),
		.RESET					(reset),

		// Testbench --> DDR2 controller
		.INITDDR				(initddr),

		// DDR2 controller --> testbench
		.DOUT					(dout[15:0]),
		.RADDR					(raddr[24:0]),
		.VALIDOUT				(validout),
		.READY					(ready),

		// Driver --> DDR2 controller
		.CMD					(cmd[2:0]),
		.SZ						(sz[1:0]),
		.OP						(op[2:0]),
		.DIN					(din[15:0]),
		.ADDR					(addr[24:0]),
		.FETCHING				(fetching),

		// DDR2 controller --> driver
		.FILLCOUNT				(fillcount[6:0]),
		.NOTFULL			    (notfull),

		// DDR2 controller --> RAM
		.C0_CK_PAD				(c0_ck_pad),
		.C0_CKBAR_PAD			(c0_ckbar_pad),
		.C0_CKE_PAD				(c0_cke_pad),
		.C0_CSBAR_PAD			(c0_csbar_pad),
		.C0_RASBAR_PAD			(c0_rasbar_pad),
		.C0_CASBAR_PAD			(c0_casbar_pad),
		.C0_WEBAR_PAD			(c0_webar_pad),
		.C0_BA_PAD				(c0_ba_pad[1:0]),
		.C0_A_PAD				(c0_a_pad[12:0]),
		.C0_DM_PAD				(c0_dm_pad[1:0]),
		.C0_ODT_PAD				(c0_odt_pad),

		// DDR2 controller <--> RAM
		.C0_DQ_PAD				(c0_dq_pad[15:0]),
		.C0_DQS_PAD				(c0_dqs_pad[1:0]),
		.C0_DQSBAR_PAD			(c0_dqsbar_pad[1:0])

	);

	/************************************************************************/
	/* Instance: DDR2 DRAM													*/
	/************************************************************************/

	ddr2_dram i_ddr2_dram (

		.ck			(c0_ck_pad),			// I [0:0]  Diffpair clock for data (posedge samples)
		.ck_n		(c0_ckbar_pad),			// I [0:0]  Diffpair clock for data (negedge samples)
		.cke		(c0_cke_pad),			// I [0:0]  Active-high: enables clocking circuitry

		.ba			(c0_ba_pad),			// I [1:0]  Bank address (which bank to ACTIVATE, READ, WRITE, or PRECHARGE) 
		.addr		(c0_a_pad),				// I [12:0] Row address for ACTIVATE & column address for READ/WRITE... A[10] is precharge

		.cs_n		(c0_csbar_pad),			// I [0:0]  Active-low: enables command decoder
		.ras_n		(c0_rasbar_pad),		// I [0:0]  Active-low row address strobe
		.cas_n		(c0_casbar_pad),		// I [0:0]  Active-low column address strobe
		.we_n		(c0_webar_pad),			// I [0:0]  Active low write-enable

		.dq			(c0_dq_pad),			// IO [15:0] Bidirectional data bus for 32 Meg x 16
		.dqs		(c0_dqs_pad),			// IO [1:0]  Diffpair strobe (output & edge-aligned for READ, input & center-aligned for WRITE)
		.dqs_n		(c0_dqsbar_pad),		// IO [1:0]  Diffpair strobe (output & edge-aligned for READ, input & center-aligned for WRITE)

		.dm_rdqs	(c0_dm_pad),			// I [1:0]  Active-high data mask (masks input data WRITE bytes)
		.odt		(c0_odt_pad)			// I [0:0]  Active high on-die termination (internal resistors for DQ/DQS/DM signals)

	);

	/************************************************************************/
	/* Instance: DDR Monitor												*/
	/************************************************************************/

	ddr2ifc_monitor ddr2ifc_monitor0 (

		.ck			(c0_ck_pad),
		.cke		(c0_cke_pad),
		.reset		(reset),

		.addr		(c0_a_pad),
		.ba			(c0_ba_pad),
		.dq			(c0_dq_pad),
		.dqs		(c0_dqs_pad),

		.cs_n		(c0_csbar_pad),			// I [0:0]  Active-low: enables command decoder
		.ras_n		(c0_rasbar_pad),		// I [0:0]  Active-low row address strobe
		.cas_n		(c0_casbar_pad),		// I [0:0]  Active-low column address strobe
		.we_n		(c0_webar_pad)

	);

	/************************************************************************/
	/* Instance: Ring Buffer Monitor										*/
	/************************************************************************/

	// instantiate ringbuffer_monitor

	RingBuffer_monitor ringbuffer_monitor_0 (
		.listen		(i_ddr2_controller.ring.listen),
		.strobe		(i_ddr2_controller.ring.strobe),
		.din		(i_ddr2_controller.ring.din),
		.readPtr	(i_ddr2_controller.ring.readPtr),
		.dout		(i_ddr2_controller.ring.dout),
		.reset		(i_ddr2_controller.ring.reset),
		.clk		(i_ddr2_controller.CLK)
	);
	
	/************************************************************************/
	/* Bind: Ring Buffer Assertions											*/
	/************************************************************************/

	bind ddr2_ring_buffer8 RingBuffer_assertions AssertCheckRB (

		.listen		(i_ddr2_controller.ring.listen),
		.strobe		(i_ddr2_controller.ring.strobe),
		.din		(i_ddr2_controller.ring.din),
		.readPtr	(i_ddr2_controller.ring.readPtr),
	    .dout		(i_ddr2_controller.ring.dout),
		.reset		(i_ddr2_controller.ring.reset),
		.clk		(i_ddr2_controller.CLK)
	);
	

endmodule // tb