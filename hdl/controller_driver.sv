// Module: controller_driver.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// This module reads an input file with memory test cases, parses
// the input, and sends the resulting commands to the DDR2 controller.
// It uses a task (FetchNextTestPattern) to read a line from the input file,
// another task (ApplyNextTestPattern) to generate the output command signals,
// and an 'always' block to mediate between fetching lines & applying commands.
//
// It also takes in input signals about the status of the CMD & DATA FIFOs when
// determining whether to fetch/apply next commands.
//
// Once all patterns have been read, it sets the 'test_pattern_injection_done'
// which will wrap up simulation in the parent-level testbench.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"
`timescale  1ns / 10ps

module controller_driver (

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/

	// Globals
	input ulogic1		clk,
	input ulogic1		reset,

	// DDR2 controller --> driver
	input ulogic7		fillcount,
	input ulogic1		notfull,

	// Driver --> DDR2 controller
	output ulogic3		cmd = 0,
	output ulogic2		sz = 0,
	output ulogic3		op = 0,
	output ulogic1		fetching = 0,
	output ulogic16		din = 0,
	output ulogic25		addr = 0

);

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	//////////////////////////////////////////
	// Command signals read from input file //
	//////////////////////////////////////////

	integer 		WaitCycles = 0;
	ulogic3			Cmd = 0;
	ulogic2			Sz = 0;
	ulogic3			Op = 0;
	ulogic25		Addr = 0;
	ulogic16		Data = 0;
	ulogic1			Fetching = 0;

	////////////////////
	// Task variables //
	////////////////////

	event 			fetchNextTestPattern, ApplyTestPattern;

	ulogic1			waiting = 0;
	ulogic1			BlkWriteInProgress = 0;

	integer 		waitCount = 0;
	integer			blkWriteCount = 0;
	integer 		line, fhandle_in;
	ulogic1			test_pattern_injection_done = 1;

	/////////////////////////
	// FIFO status signals //
	/////////////////////////

	ulogic1			DataFifoHasSpace;
	ulogic1			CmdFifoHasSpace;

	/************************************************************************/
	/* Continuous Assignments												*/
	/************************************************************************/

	assign	DataFifoHasSpace = (fillcount <= 63) ? 1 : 0;
	assign	CmdFifoHasSpace  = notfull;

	assign	#0.1 non_read_cmd_consumed = ((DataFifoHasSpace == 1) && (CmdFifoHasSpace == 1) && (Cmd != 1) && (Cmd !=3) && (Cmd != 0) && (Cmd != 7));
	assign	#0.1 read_cmd_consumed = ((CmdFifoHasSpace == 1) && ((Cmd == 1) || (Cmd ==3)));
	assign	#0.1 nop_consumed = ((Cmd == 0) || (Cmd == 7));

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

endmodule // controller_driver