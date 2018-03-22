// Module: ddr2ifc_monitor.sv
// Author: Chris Loop (modified by Rehan Iqbal)
// Date: March 20th, 2018
// Organization: Portland State University
//
// Monitor for the interface between DDR2 controller and DRAM. The monitor
// will log all transactions based on the address signals (addr/ba) and commands
// (cs_n, ras_n, cas_n, we_n).
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module ddr2ifc_monitor #(parameter DEBUG = 0) (

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
	input ulogic1	we_n	// I [0:0]  Active low write-enable

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
								$display("DDR2 Monitor: READ transaction of data '%x' from bank %d, row 0x%x, column 0x%x at %t", data, bank_reg, row_reg, col_reg, $time);
							end

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
								$display("DDR2 Monitor: WRITE transaction of data '%x' to bank %d, row 0x%x, column 0x%x at %t", data, bank_reg, row_reg, col_reg, $time);
							end

						end
			endcase

		end // if (!reset && cke && cke_prev) 

	end // always

endmodule