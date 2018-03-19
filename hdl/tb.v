// Module: tb.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// User defined Test Pattern is fetched from INPUT_FILE_NAME
// The file should have data in five columns
// WaitForCycles[decimal]  Cmd[decimal]  Address[hex] Data[hex]   Read[decimal]
// 
// Sample Test Pattern File
// 0   1     1BABAFE  CAFE   0
// 0   1     1BABAFE  D0C0   0 
// 0   2     1BABAFE  CAFE   0
// 0   3     1BABAFE  CAFE   0
// 10  0           0     0   1
// 0   6     1BABAFE  BABA   1
// 0   0     1BABAFE  CAFE   1
//
// The testbench provides 500MHz clock
// The testbench provides an active low reset
// After reset a one cycle long initddr signal is issued
// Testbench then waits for the ready signal to come out
// After ready becomes high the testbench fetches a line from the Test Pattern File every cycles,
// waits for "WaitForCycles" (given in the first column of the fetched line) and then put the 
// Cmd , Addr, Data and Read to the ports of the DDR2 controller
// If the WaitForCycles = 0 then the values are applied in the same cycles
//
// Notes:
// (1) Test Pattern file should not have text header of any kind
// (2) Test Pattern file should not have any blank lines
//
////////////////////////////////////////////////////////////////////////////////

`timescale  1ns / 10ps

module tb();

	`define INPUT_FILE_NAME "C:/Users/riqbal/Dropbox/ECE 593/Final Project/hdl/ddr2_test_pattern.txt"
	`define NULL 0  

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	//////////////////////////////////////////////
	// Signals between DDR2 controller and DRAM //
	//////////////////////////////////////////////

	wire [15:0]			dout;
	wire [24:0] 		raddr;
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
	wire [6:0] 			fillcount;				
	wire				notfull;				
	wire				ready;					
	wire				validout;

	////////////////////////////////////////////////
	// Command signals going into DDR2 controller //
	////////////////////////////////////////////////

	reg [1:0] 			sz;
	reg [2:0] 			op;
	reg [24:0] 			addr;
	reg					clk;
	reg [2:0] 			cmd;
	reg [15:0] 			din;
	reg 				fetching;
	reg					initddr;
	reg					reset;

	//////////////////////////////////////////
	// Command signals read from input file //
	//////////////////////////////////////////

	integer 			WaitCycles;
	reg [2:0] 			Cmd;
	reg [1:0] 			Sz;
	reg [2:0] 			Op;
	reg [24:0] 			Addr;
	reg [15:0] 			Data;
	reg 				Fetching;

	///////////////////////
	// Control variables //
	///////////////////////

	reg 			test_pattern_injection_done, waiting, BlkWriteInProgress;
	event 			fetchNextTestPattern;
	event 			ApplyTestPattern;
	integer 		waitCount, blkWriteCount;
	wire 			DataFifoHasSpace, CmdFifoHasSpace;
	integer 		c, r, fhandle_in;

	assign			DataFifoHasSpace = (fillcount <= 63) ? 1 : 0;
	assign			CmdFifoHasSpace  = notfull;

	assign			#0.1 non_read_cmd_consumed =((DataFifoHasSpace == 1) && (CmdFifoHasSpace == 1) && (Cmd != 1) && (Cmd !=3) && (Cmd != 0) && (Cmd != 7));
	assign			#0.1 read_cmd_consumed = ((CmdFifoHasSpace == 1) && ((Cmd == 1) || (Cmd ==3)));
	assign			#0.1 nop_consumed = ((Cmd == 0) || (Cmd == 7));

	/************************************************************************/
	/* System clock generation												*/
	/************************************************************************/

	initial begin 
		clk = 0;
	end

	// Run at 500MHz
	always #1 clk = ~clk;

	/************************************************************************/
	/* Reset & initialization												*/
	/************************************************************************/

	initial begin

		$timeformat(-9, 0, "ns", 8);

		test_pattern_injection_done = 1; // keep the testpattern activity suppressed
		reset = 1;
		clk = 0;
		initddr = 0;
		addr <= 0;
		cmd <= 0;
		sz <=0;
		op <=0;
		din <= 0;

		// Initialize control variables
		waiting = 0;
		BlkWriteInProgress = 0;
		waitCount = 0;
		blkWriteCount = 0;
		repeat (5) @(negedge clk);
		reset = 0;
		@(negedge clk);
		initddr  = 1;
		@(negedge clk);
		initddr  = 0;

		// Now wait for DDR to be ready
		$display("MSG: Waiting for DDR2 to become ready");
		wait (ready);

		// Open Test Pattern File
		fhandle_in = $fopen(`INPUT_FILE_NAME,"r");

		if (fhandle_in == `NULL) begin
			$display("*** ERROR *** Could not open the file %s\n", `INPUT_FILE_NAME);
			$finish;
		end

		// Start the test pattern
		@(posedge clk);
		-> fetchNextTestPattern;

		// All patterns from input file have been read... time to wrap up simulation
		@(posedge test_pattern_injection_done);
		$display("MSG: All test patterns are successfully applied");
		$display("MSG: Now waiting to let the DDR2 controller drain out");
		repeat (1500) @(negedge clk);
		$display("MSG: End Simulation!!!");
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
			
			// Push the character back to the file then read the next time
			r = $ungetc(c, fhandle_in);
			
			// Example1: Scalar write (SCW) of data 'FACE' to column 0x7A in bank 0, row 0x8F
			// Example2: Scalar read (SCR) of data from column 0xB9 in bank 3, row 0x2E

			// WaitCycle	Cmd		Size	Op		Row(Addr[25:12])	Bank(Addr[4:3])		Column({Addr[11:5],Addr[2:0]})	Data	Fetching
			// ==============================================================================================================================
			// 0			2		0		0		008F				0					07A								FACE	0
			// 0			1		0		0		002E				3					0B9								0000	0

			r = $fscanf(fhandle_in,"%d\t%d\t%d\t%d\t%x\t%d\t%x\t%x\t%d\n", 
									WaitCycles, 
									Cmd, 
									Sz, 
									Op, 
									Addr[24:12], 
									Addr[4:3], 
									{Addr[11:5],Addr[2:0]}, 
									Data, 
									Fetching);

			c = $fgetc(fhandle_in);
			
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

	ddr2_controller XCON (

		// Inputs from Stimulator
		.CLK					(clk),
		.RESET					(reset),
		.CMD					(cmd[2:0]),
		.SZ						(sz[1:0]),
		.OP						(op[2:0]),
		.DIN					(din[15:0]),
		.ADDR					(addr[24:0]),
		.FETCHING				(fetching),
		.INITDDR				(initddr),

		// Inouts between DRAM
		.C0_DQ_PAD				(c0_dq_pad[15:0]),
		.C0_DQS_PAD				(c0_dqs_pad[1:0]),
		.C0_DQSBAR_PAD			(c0_dqsbar_pad[1:0]),

		// Outputs to DRAM
		.DOUT					(dout[15:0]),
		.RADDR					(raddr[24:0]),
		.FILLCOUNT				(fillcount[6:0]),
		.VALIDOUT				(validout),
		.NOTFULL			    (notfull),
		.READY					(ready),
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
		.C0_ODT_PAD				(c0_odt_pad)

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