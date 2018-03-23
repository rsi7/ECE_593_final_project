// Module: ddr2ifc_monitor.sv
// Author: Chris Loop (modified by Rehan Iqbal)
// Date: March 22nd, 2018
// Organization: Portland State University
//
// Monitor for the interface between DDR2 controller and DRAM. The monitor
// will log all transactions based on the address signals (addr/ba) and commands
// (cs_n, ras_n, cas_n, we_n) if the global 'DEBUG' parameter is set. It will also
// run assertions to check the protocol. Lastly, it creates a packet of the
// memory transaction (read/write) and passes it to the checker module so it
// can check against the command packet.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module ddr2ifc_monitor #(parameter DEBUG = 0) (

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/
	
	// Globals
	input ulogic1	ck,		// I [0:0]  Diffpair clock for data (posedge samples)
	input ulogic1	cke,	// I [0:0]  Active-high: enables clocking circuitry
	input ulogic1	reset,	// I [0:0]  Active-high reset

	// Address signals
	input ulogic13	addr,	// I [12:0] Row address for ACTIVATE & column address for READ/WRITE... A[10] is precharge
	input ulogic2	ba,		// I [1:0]  Bank address (which bank to ACTIVATE, READ, WRITE, or PRECHARGE) 

	// Data signals
	input ulogic16	dq,		// IO [15:0] Bidirectional data bus for 32 Meg x 16
	input ulogic2 	dqs,	// IO [1:0]  Diffpair strobe (output & edge-aligned for READ, input & center-aligned for WRITE)

	// Command signals
	input ulogic1	cs_n,	// I [0:0]  Active-low: enables command decoder
	input ulogic1	ras_n,	// I [0:0]  Active-low row address strobe
	input ulogic1	cas_n,	// I [0:0]  Active-low column address strobe
	input ulogic1	we_n,	// I [0:0]  Active low write-enable

	// Output packet --> checker
	output packet	pkt
);

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	localparam	CMD_READ		= 4'b0101;
	localparam	CMD_WRITE		= 4'b0100;
	localparam	CMD_ACTIVATE	= 4'b0011;
	localparam	CMD_PRECHRG		= 4'b0010;
	localparam	CMD_NOP			= 4'b0111;

	ulogic1		cke_prev = 0;

	ulogic2		bank_reg;
	ulogic13	row_reg;
	ulogic10	col_reg;
	
	logic [7:0][15:0]	data;	// create packed array, for easy printout later

	int count_reg = 0;

	/************************************************************************/
	/* always block : case statement										*/
	/************************************************************************/

	always @(posedge ck) begin

		// Set cke_prev register
		cke_prev <= cke;

		if (!reset && cke && cke_prev) begin

			case ({cs_n, ras_n, cas_n, we_n})

				CMD_ACTIVATE: begin
							row_reg = addr;
							bank_reg = ba;

							if (DEBUG) begin
								$display("DDR2 Monitor: ACTIVATE to bank %d, row 0x%x at time %t", bank_reg, row_reg, $time);
							end
						
						end
				
				CMD_PRECHRG: begin

						if (DEBUG) begin
							$display("DDR2 Monitor: PRECHARGE detected at time %t", $time);
						end
					end
				
				CMD_READ: begin

							col_reg = addr[9:0];
							bank_reg = ba;

							// Latch data on first DQS strobe rising edge
							@(posedge dqs[0]);
							data[0] = dq;

							for (int i = 1; i < 8; i++) begin
								@(dqs[0]);
								data[i] = dq;
							end // for

							if(DEBUG) begin
								$display("DDR2 Monitor: READ transaction of data '%4x' from bank %d, row 0x%x, column 0x%x at %t", data, bank_reg, row_reg, col_reg, $time);
							end
							sendToChecker({cs_n, ras_n, cas_n, we_n}, bank_reg, row_reg, col_reg, data, pkt);
						end

				CMD_WRITE: begin

							col_reg = addr[9:0];
							bank_reg = ba;

							// Latch data on first DQS strobe rising edge
							@(posedge dqs[0]);
							data[0] = dq;
							
							for (int i = 1; i < 8; i++) begin
								@(dqs[0]);
								data[i] = dq;
							end
							
							if (DEBUG) begin
								$display("DDR2 Monitor: WRITE transaction of data '%4x' to bank %d, row 0x%x, column 0x%x at %t", data, bank_reg, row_reg, col_reg, $time);
							end
							sendToChecker({cs_n, ras_n, cas_n, we_n}, bank_reg, row_reg, col_reg, data, pkt);
						end
			endcase

		end // if (!reset && cke && cke_prev) 

	end // always

	/************************************************************************/
	/* Task: sendToChecker													*/
	/************************************************************************/

	task sendToChecker (

		// Commmand signals
		input ulogic4	cmd,

		// Address signals
		input ulogic2	bank,
		input ulogic13	row,
		input ulogic10	col,

		// Data signals
		input ulogic16	data,

		// Output packet to checker
		output packet	pkt

	);

		packet new_packet;

		new_packet.timestamp = $time();
		new_packet.id = count_reg;


		new_packet.command = (cmd == CMD_WRITE) ? 3'd2 : 3'd1;
		new_packet.address.bank = bank;
		new_packet.address.row = row;
		new_packet.address.column = col;

		new_packet.data = data;

		pkt = new_packet;
		count_reg += 1'b1;

	endtask

endmodule