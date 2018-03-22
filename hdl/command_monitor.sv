// Module: command_monitor.sv
// Author: Rehan Iqbal
// Date: March 15th, 2018
// Organization: Portland State University
//
// Monitor for command bus going between controller driver and DDR2
// controller. Contains assertions to ensure that no illegal commands,
// data, or addresses are submitted to the DDR2 controller.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module command_monitor (

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/

	// Driver --> DDR2 controller

	input ulogic3	cmd,
	input ulogic2	sz,
	input ulogic1	fetching,
	input ulogic16	din,
	input ulogic25	addr

	);

	/************************************************************************/
	/* Assertions															*/
	/************************************************************************/

	// Valid_Command: ensures that command falls between 0 - 7
	// unless 'BlkWriteInProgress', in which case it is 'x
	property Valid_Command();
		@(cmd) disable iff(reset)
			((cmd >= 0) && (cmd <= 7)) || $isunknown(cmd);
	endproperty
	Valid_Command_Assertion: assert property(Valid_Command);

	// Valid_Sz: ensures that size is between 0 - 64 bytes
	// for Block Read, Block Write, Atomic Read, Atomic Write
	property Valid_Sz();
		@(sz) disable iff(reset)
			((cmd >= 3) && (cmd <= 6)) |-> (sz >= 0) && (sz <= 64);
	endproperty
	Valid_Sz_Assertion: assert property(Valid_Sz);

	// Valid_Fetching_Assertion: ensures that fetching is 1 or 0
	property Valid_Fetching();
		@(fetching) disable iff(reset)
			(fetching == 1'b0) || (fetching == 1'b1);
	endproperty
	Valid_Fetching_Assertion: assert property(Valid_Fetching);	

	// Valid_Din: ensures that data input is in range (16'h0000 to 16'hFFFF)
	// for Scalar Write, Block Write, Atomic Read, Atomic Write
	property Valid_Din();
		@(din) disable iff(reset)
			(cmd == 2) || (cmd >= 4 && cmd <= 6) |-> (din >= 16'h0000) && (din <= 16'hFFFF);
	endproperty
	Valid_Din_Assertion: assert property(Valid_Din);

	// Valid_Addr_Bank: ensures that bank address input is in range (0 to 3)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Bank();
		@(addr) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[4:3] >= 2'd0) && (addr[4:3] <= 2'd3);
	endproperty
	Valid_Addr_Bank_Assertion: assert property(Valid_Addr_Bank);

	// Valid_Addr_Row: ensures that row address input is in range (0 to 8191)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Row();
		@(addr) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[24:12] >= 13'd0) && (addr[4:3] <= 13'd8191);
	endproperty
	Valid_Addr_Row_Assertion: assert property(Valid_Addr_Row);

	// Valid_Addr_Col: ensures that column address input is in range (0 to 1023)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Col();
		@(addr) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[9:0] >= 10'd0) && (addr[9:0] <= 10'd1023);
	endproperty
	Valid_Addr_Col_Assertion: assert property(Valid_Addr_Col);

endmodule // command_monitor