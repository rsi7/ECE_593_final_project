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

module command_monitor #(parameter DEBUG = 0) (

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/

	// Globals

	input ulogic1	clk,
	input ulogic1	reset,

	// Driver --> DDR2 controller

	input ulogic3	cmd,
	input ulogic2	sz,
	input ulogic3	op,
	input ulogic1	fetching,
	input ulogic16	din,
	input ulogic25	addr

	);

	/************************************************************************/
	/* Debug Messaging														*/
	/************************************************************************/

	// Monitor reset applied to the controller
	always@(reset) begin

		if (DEBUG) begin
			$display("Command Monitor: Reset applied to controller at %t", $time);
		end
	end

	// Monitor commands, addr, data being applied to the controller
	always@(cmd, addr, din) begin

		if (DEBUG) begin

			string str;

			case (cmd)

			(3'd0) : str = "NOP";
			(3'd1) : str = "Scalar read";
			(3'd2) : str = "Scalar write";
			(3'd4) : str = "Block write";
			(3'd5) : str = "Atomic read";
			(3'd6) : str = "Atomic write";
			(3'd7) : str = "NOP";

		endcase // cmd

			$display("Command Monitor: %s applied with data '%4x' to controller at bank %d, row 0x%x, column 0x%x at %t", str, din, addr[4:3], addr[24:12], {addr[11:5],addr[2:0]}, $time);
		end
	end

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

	// Valid_Sz: ensures that size is between 1 - 4 bytes
	// for Block Read, Block Write, Atomic Read, Atomic Write
	property Valid_Sz();
		@(sz, cmd) disable iff(reset)
			((cmd >= 3) && (cmd <= 6)) |-> (sz >= 0) && (sz <= 3);
	endproperty
	Valid_Sz_Assertion: assert property(Valid_Sz);

	// Valid_Op: ensures that op is between 1 - 8
	// only for Atomic Read, Atomic Write
	property Valid_Op();
		@(op, cmd) disable iff(reset)
			((cmd == 5) || (cmd == 6)) |-> (op >= 0) && (sz <= 7);
	endproperty
	Valid_Op_Assertion: assert property(Valid_Op);

	// Valid_Fetching_Assertion: ensures that fetching is 1 or 0
	property Valid_Fetching();
		@(fetching) disable iff(reset)
			(fetching == 1'b0) || (fetching == 1'b1);
	endproperty
	Valid_Fetching_Assertion: assert property(Valid_Fetching);	

	// Valid_Din: ensures that data input is in range (16'h0000 to 16'hFFFF)
	// for Scalar Write, Block Write, Atomic Read, Atomic Write
	property Valid_Din();
		@(din, cmd) disable iff(reset)
			(cmd == 2) || (cmd >= 4 && cmd <= 6) |-> (din >= 16'h0000) && (din <= 16'hFFFF);
	endproperty
	Valid_Din_Assertion: assert property(Valid_Din);

	// Valid_Addr_Bank: ensures that bank address input is in range (0 to 3)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Bank();
		@(addr, cmd) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[4:3] >= 2'd0) && (addr[4:3] <= 2'd3);
	endproperty
	Valid_Addr_Bank_Assertion: assert property(Valid_Addr_Bank);

	// Valid_Addr_Row: ensures that row address input is in range (0 to 8191)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Row();
		@(addr, cmd) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[24:12] >= 13'd0) && (addr[4:3] <= 13'd8191);
	endproperty
	Valid_Addr_Row_Assertion: assert property(Valid_Addr_Row);

	// Valid_Addr_Col: ensures that column address input is in range (0 to 1023)
	// when command is legitimate read/write (i.e. not a NOP)
	property Valid_Addr_Col();
		@(addr, cmd) disable iff(reset)
			((cmd != 0) && (cmd != 7)) |-> (addr[9:0] >= 10'd0) && (addr[9:0] <= 10'd1023);
	endproperty
	Valid_Addr_Col_Assertion: assert property(Valid_Addr_Col);

endmodule // command_monitor