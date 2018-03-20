// Module: tb.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// The testbench provides a 500MHz clock and active-low reset... after reset
// a one-cycle long 'initddr' signal is issued. Testbench then waits for the
// 'ready' signal to come out.
//
// After 'read' goes high, the testbench fetches a line from the test pattern
// input file every cycle, waits for the amount specified (first column in file),
// and then applies 'Cmd', 'Addr', 'Data' and others onto the ports of the
// DDR2 controller. If 'WaitCycles' is zero, these signals are applied same-cycle.
//
// Once all patterns have been read, it sets the 'test_pattern_injection_done'
// which will wrap up simulation.
//
////////////////////////////////////////////////////////////////////////////////

`timescale  1ns / 10ps

module tb();

	`define INPUT_FILE_NAME "C:/Users/riqbal/Dropbox/ECE 593/Final Project/hdl/ddr2_test_pattern.txt"

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	///////////////////////////////////////////
	// Signals between DDR2 controller & RAM //
	///////////////////////////////////////////

	wire [12:0] 		c0_a_pad;
	wire [1:0] 			c0_ba_pad;
	wire				c0_casbar_pad;
	wire				c0_ckbar_pad;
	wire				c0_cke_pad;
	wire				c0_ck_pad;
	wire				c0_csbar_pad;
	wire [1:0] 			c0_dm_pad;
	wire [1:0] 			c0_dqsbar_pad;
	wire [1:0] 			c0_dqs_pad;
	wire [15:0] 		c0_dq_pad;
	wire				c0_odt_pad;
	wire				c0_rasbar_pad;
	wire				c0_webar_pad;

	//////////////////////////////////////////////////////
	// Output signals from DDR2 controller to testbench //
	//////////////////////////////////////////////////////

	wire [15:0]			dout;
	wire [24:0] 		raddr;
	wire				ready;
	wire				validout;

	//////////////////////////////////////////////////////////
	// Testbench command signals going into DDR2 controller //
	//////////////////////////////////////////////////////////

	reg [1:0] 			sz = 0;
	reg [2:0] 			op = 0;
	reg [24:0] 			addr = 0;
	reg					clk = 0;
	reg [2:0] 			cmd = 0;
	reg [15:0] 			din = 0;
	reg 				fetching = 0;
	reg					initddr = 0;
	reg					reset = 1;

	//////////////////////////////////////////
	// Command signals read from input file //
	//////////////////////////////////////////

	integer 			WaitCycles = 0;
	reg [2:0] 			Cmd = 0;
	reg [1:0] 			Sz = 0;
	reg [2:0] 			Op = 0;
	reg [24:0] 			Addr = 0;
	reg [15:0] 			Data = 0;
	reg 				Fetching = 0;

	////////////////////
	// Task variables //
	////////////////////

	event 			fetchNextTestPattern, ApplyTestPattern;

	reg 			test_pattern_injection_done = 1;
	reg				waiting = 0;
	reg				BlkWriteInProgress = 0;

	integer 		waitCount = 0;
	integer			blkWriteCount = 0;
	integer 		line, fhandle_in;

	/////////////////////////
	// FIFO status signals //
	/////////////////////////

	wire 			DataFifoHasSpace;
	wire			CmdFifoHasSpace;
	wire [6:0] 		fillcount;
	wire			notfull;

	/************************************************************************/
	/* Continuous Assignments												*/
	/************************************************************************/

	assign			DataFifoHasSpace = (fillcount <= 63) ? 1 : 0;
	assign			CmdFifoHasSpace  = notfull;

	assign			#0.1 non_read_cmd_consumed = ((DataFifoHasSpace == 1) && (CmdFifoHasSpace == 1) && (Cmd != 1) && (Cmd !=3) && (Cmd != 0) && (Cmd != 7));
	assign			#0.1 read_cmd_consumed = ((CmdFifoHasSpace == 1) && ((Cmd == 1) || (Cmd ==3)));
	assign			#0.1 nop_consumed = ((Cmd == 0) || (Cmd == 7));

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
		$display("MSG: Waiting for DDR2 controller to become ready...");
		wait (ready);
		$display("MSG: DDR2 controller is ready... now reading input test pattern file");

		// Open test pattern input file... return error if file not found
		InputFileCheck : assert ((fhandle_in = $fopen(`INPUT_FILE_NAME, "r")) != 0) begin
			$display("MSG: %m was able to open input file %s successfully!", `INPUT_FILE_NAME);
		end

		else begin
			$error("ERROR: %m can't open file %s!", `INPUT_FILE_NAME);
			$stop;
		end

		// Start reading the input file's test patterns
		@(posedge clk);
		-> fetchNextTestPattern;

		// All patterns from input file have been read... time to wrap up simulation
		@(posedge test_pattern_injection_done);
		$display("MSG: All test patterns are successfully applied!");
		$display("MSG: Now waiting to let the DDR2 controller drain out...");
		
		repeat (1500) @(negedge clk);
		$display("MSG: End of simulation at %t", $time);
		$stop;

	end // initial begin

	/************************************************************************/
	/* Block: send commands to ddr2_controller								*/
	/************************************************************************/

	// This block only tests if the applied current test pattern is consumed or not
	// Then triggers next fetch and apply

	always @ (posedge clk) begin

		// Check if all test patterns have been read from input file...
		if (!test_pattern_injection_done) begin

			// Make sure no 'waiting' flag set by WaitCycles in input file...
			if (!waiting) begin

				// Check if a Block write (BLW) is currently happening...
				if ((BlkWriteInProgress  == 1) && (DataFifoHasSpace == 1)) begin

					blkWriteCount <= #0.1 blkWriteCount - 1;

					if (blkWriteCount  == 1)
						BlkWriteInProgress = 0;
					-> fetchNextTestPattern;
				end

				// No Block write in progress... see if previous command was consumed or not before
				// grabbing the next test pattern from input file
				else if ((BlkWriteInProgress  == 0) && ((non_read_cmd_consumed) || (read_cmd_consumed) || (nop_consumed))) begin

					// If a Block write was specified, need to set the flag and count...
					if (Cmd == 4) begin
						BlkWriteInProgress = 1;
						blkWriteCount <= #0.1 blkWriteCount - 1;
					end

					-> fetchNextTestPattern;
				end
			end // if (waiting != 0)

			// Otherwise, 'waiting' flag was set by WaitCycles field in input file... 
			// Need to decrement waiting counter and eventually call 'ApplyTestPattern' task
			else begin

				waitCount <= #0.1 waitCount -1;
				if (waitCount == 1) begin
					waiting <=  #0.1 0;
					-> ApplyTestPattern;
				end
			end // else: !if(waiting != 0)
		
		end // if(!test_pattern_injection_done)

	end // always@(posedge clk)

	/************************************************************************/
	/* Task: fetchNextTestPattern											*/
	/************************************************************************/

	// This task reads the input file to fetch the next test pattern to apply
	// This is only triggered if last applied command is consumed
	// If there are no more test patterns, it sets the 'test_pattern_injection_done' flag

	always@(fetchNextTestPattern) begin
		
		// Check for end-of-file on input file
		if (!($feof(fhandle_in))) begin

			test_pattern_injection_done = 0;
			
			// Example1: Scalar write (SCW) of data 'FACE' to column 0x7A in bank 0, row 0x8F
			// Example2: Scalar read (SCR) of data from column 0xB9 in bank 3, row 0x2E

			// WaitCycle	Cmd		Size	Op		Row(Addr[25:12])	Bank(Addr[4:3])		Column({Addr[11:5],Addr[2:0]})	Data	Fetching
			// ==============================================================================================================================
			// 0			2		0		0		008F				0					07A								FACE	0
			// 0			1		0		0		002E				3					0B9								0000	0

			line = $fscanf(fhandle_in,"%d\t%d\t%d\t%d\t%x\t%d\t%x\t%x\t%d\n", 
									WaitCycles, 
									Cmd, 
									Sz, 
									Op, 
									Addr[24:12], 
									Addr[4:3], 
									{Addr[11:5],Addr[2:0]}, 
									Data, 
									Fetching);
			
			// Immediately apply test pattern if no wait is specified...
			if (WaitCycles == 0) begin
				waitCount	<= #0.1 0;
				waiting		<= #0.1 0;
				-> ApplyTestPattern;
			end
			
			// Otherwise, set the 'waiting' flag and wait the appropriate amount of time... then apply
			else begin
				waitCount	<= #0.1 WaitCycles;
				waiting		<= #0.1 1;
				cmd			<= #0.1 3'b0;
				din			<= #0.1 16'bx;
				addr		<= #0.1 25'bx;
				sz			<= #0.1 2'bx;
				op			<= #0.1 3'bx;
			end

		end // if !$feof(fhandle_in)
		
		// Input file has been read, and there are no more test patterns... 
		// Set 'test_pattern_injection_done' flag which will trigger end of simulation

		else begin

			test_pattern_injection_done <= #0.1 1;

			Cmd			= 3'b0;
			Data		= 16'bx;
			Addr		= 25'bx;
			Sz			= 2'bx;
			Op			= 3'bx;
			Fetching	= 3'b1;

			-> ApplyTestPattern;

		end // else: $feof(fhandle_in)

	end // always@(fetchNextTestPattern)

	/************************************************************************/
	/* Task: ApplyTestPattern												*/
	/************************************************************************/

	// This task actually applies the commands read in 'fetchNextTestPattern' task to the controller

	// Commands
	// ---------
	// 000: No Operation (NOP)
	// 001: Scalar Read  (SCR)
	// 010: Scalar Write  (SCW)
	// 011: Block Read (BLR)
	// 100: Block Write ((BLW)
	// 101: Atomic Read (ATR)
	// 110: Atomic Write (ATW)
	// 111: No Operation (NOP)

	always@(ApplyTestPattern) begin

		if (BlkWriteInProgress) begin
			cmd			<= #0.1 3'bx;
			din			<= #0.1 Data;
			addr		<= #0.1 25'bx;
			sz			<= #0.1 2'bx;
			op			<= #0.1 3'bx; 
			fetching	<= #0.1 Fetching;
		end

		// 111 or 000: No Operation (NOP)
		else if ((Cmd == 0) || (Cmd == 7)) begin
			cmd			<= #0.1 Cmd;
			din			<= #0.1 16'bx;
			addr		<= #0.1 25'bx;
			sz			<= #0.1 2'bx;
			op			<= #0.1 3'bx; 
			fetching	<= #0.1 Fetching;
		end

		// 001: Scalar Read (SCR)
		else if (Cmd == 1) begin
			cmd			<= #0.1 Cmd;
			din			<= #0.1 16'bx;
			addr		<= #0.1 Addr;
			sz			<= #0.1 2'bx;
			op			<= #0.1 3'bx; 
			fetching	<= #0.1 Fetching;
		end

		// 010: Scalar Write  (SCW)
		else if (Cmd == 2) begin
			cmd			<= #0.1 Cmd; 
			din			<= #0.1 Data;
			addr		<= #0.1 Addr;
			sz			<= #0.1 2'bx;
			op			<= #0.1 3'bx;
			fetching	<= #0.1 Fetching;
		end

		// 011: Block Read (BLR)
		else if (Cmd == 3) begin
			cmd			<= #0.1 Cmd;
			din			<= #0.1 16'bx;
			addr		<= #0.1 Addr;
			sz			<= #0.1 Sz;
			op			<= #0.1 3'bx; 
			fetching	<= #0.1 Fetching;
		end

		// 100: Block Write ((BLW)
		else if (Cmd == 4) begin
			cmd				<= #0.1 Cmd; 
			din				<= #0.1 Data;
			addr			<= #0.1 Addr;
			sz				<= #0.1 Sz;
			op				<= #0.1 3'bx;
			fetching		<= #0.1 Fetching;
			blkWriteCount	<= #0.1 (8 * (Sz + 1));
		end

		// 101: Atomic Read (ATR) or 110: Atomic Write (ATW)
		else if ((Cmd == 5) || (Cmd == 6)) begin
			cmd			<= #0.1 Cmd; 
			din			<= #0.1 Data;
			addr		<= #0.1 Addr;
			sz			<= #0.1 Sz;
			op			<= #0.1 Op;
			fetching	<= #0.1 Fetching;
		end

	end // always@(ApplyTestPattern)

	/************************************************************************/
	/* Instance: DDR2 Controller											*/
	/************************************************************************/

	ddr2_controller i_ddr2_controller (

		// Inputs from testbench
		.CLK					(clk),
		.RESET					(reset),
		.CMD					(cmd[2:0]),
		.SZ						(sz[1:0]),
		.OP						(op[2:0]),
		.DIN					(din[15:0]),
		.ADDR					(addr[24:0]),
		.FETCHING				(fetching),
		.INITDDR				(initddr),

		// Bidirectional data signals going between controller <--> RAM
		.C0_DQ_PAD				(c0_dq_pad[15:0]),
		.C0_DQS_PAD				(c0_dqs_pad[1:0]),
		.C0_DQSBAR_PAD			(c0_dqsbar_pad[1:0]),

		// Control & address outputs to RAM
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

		// Status signal outputs to testbench
		.DOUT					(dout[15:0]),
		.RADDR					(raddr[24:0]),
		.FILLCOUNT				(fillcount[6:0]),
		.VALIDOUT				(validout),
		.NOTFULL			    (notfull),
		.READY					(ready)

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

endmodule // tb