// Module: ddr2_dram.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// Description:
//
// This module implements a simple RAM model for use in the DDR2
// verification final project (ECE 593). It monitors the CS#, RAS#, CAS#, and
// WE# pins to determine when there is a valid read or write. This assumes
// that the previous cycle & current cycle that CE is high.
//
//  It stores the data in a simple 2-dimensional array (no timing checks or 
// further protocol checking here).
//
// Commands (CS#/RAS#/CAS#/WE#):
//
// Precharge	- 4'b0010
// Activate 	- 4'b0011 
// Read  		- 4'b0101
// Write 		- 4'b0100
// NOP			- 4'b0111
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/

	module ddr2_dram #(

		parameter 	ADDR_WIDTH		= 13,
		parameter 	MEM_DEPTH 		= 2**ADDR_WIDTH,
		parameter 	MEM_WIDTH 		= 16) 

		(

		input	ulogic1		ck,			// I [0:0]  Diffpair clock for data (posedge samples)
		input	ulogic1		ck_n,		// I [0:0]  Diffpair clock for data (negedge samples)
		input	ulogic1		cke,		// I [0:0]  Active-high: enables clocking circuitry
		
		input	ulogic2		ba,			// I [1:0]  Bank address (which bank to ACTIVATE, READ, WRITE, or PRECHARGE) 
		input	ulogic13	addr,		// I [12:0] Row address for ACTIVATE & column address for READ/WRITE... A[10] is precharge

		input	ulogic1		cs_n,		// I [0:0]  Active-low: enables command decoder
		input	ulogic1		ras_n,		// I [0:0]  Active-low row address strobe
		input	ulogic1		cas_n,		// I [0:0]  Active-low column address strobe
		input	ulogic1		we_n,		// I [0:0]  Active low write-enable
		
		inout	ulogic16	dq,			// IO [15:0] Bidirectional data bus for 32 Meg x 16
		inout	ulogic2		dqs,		// IO [1:0]  Diffpair strobe (output & edge-aligned for READ, input & center-aligned for WRITE)
		inout	ulogic2		dqs_n,		// IO [1:0]  Diffpair strobe (output & edge-aligned for READ, input & center-aligned for WRITE)

		input	ulogic2		dm_rdqs,	// I [1:0]  Active-high data mask (masks input data WRITE bytes)
		input	ulogic1		odt			// I [0:0]  Active high on-die termination (internal resistors for DQ/DQS/DM signals)

	);

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	// Create RAM as an associative array (non-synthesizable)
	// This makes it so that only populated entries take up space

	// Useful as memory will likely be sparesly populated... 
	// don't need allocate memory for each row until it gets used

	// 4-banks of arrays, each w/ 8192 entries of 16-bit values (default)

	logic unsigned [MEM_WIDTH-1:0]	RAM[*][ulogic13];

	localparam		CMD_READ 		= 4'b0101;
	localparam		CMD_WRITE 		= 4'b0100;
	localparam		CMD_ACTIVATE	= 4'b0011;
	localparam		CMD_PRECHRG		= 4'b0010;
	localparam		CMD_NOP			= 4'b0111;

	ulogic1		cke_prev;
	ulogic1		en_dq, en_dqs, en_dqs_n;
	ulogic2		dqs_reg, dqs_n_reg;

	ulogic13	addr_reg;
	ulogic2		bank_reg;

	/************************************************************************/
	/* always block : read/write memory										*/
	/************************************************************************/

	always@(posedge ck) begin

		case ({cs_n, ras_n, cas_n, we_n})

			CMD_READ : begin
				if ((RAM.exists(ba)&&RAM[ba].exists(addr)) && (cke_prev && cke)) begin

					addr_reg = addr;
					bank_reg = ba;

					// CAS Latency
					repeat(7) @(posedge ck);

					dqs_reg = 2'b00;
					dqs_n_reg = 2'b11;
					en_dqs = 1'b1;
					en_dqs_n = 1'b1;

					// First cycle
					@(posedge ck);
					dqs_reg = 2'b11;
					dqs_n_reg = 2'b00;
					en_dq = 1'b1;
					$display("MSG: READ transaction of data '%x' from bank %d, address 0x%x at %t", bank_reg, RAM[bank_reg][addr_reg], addr_reg, $time);

					// Second cycle
					@(negedge ck);
					dqs_reg = 2'b00;
					dqs_n_reg = 2'b11;
					addr_reg += 1'b1;

					// Third cycle
					@(posedge ck);
					dqs_reg = 2'b11;
					dqs_n_reg = 2'b00;
					addr_reg += 1'b1;

					// Fourth cycle
					@(negedge ck);
					dqs_reg = 2'b00;
					dqs_n_reg = 2'b11;
					addr_reg += 1'b1;

					// Fifth cycle
					@(posedge ck);
					dqs_reg = 2'b11;
					dqs_n_reg = 2'b00;
					addr_reg += 1'b1;

					// Sixth cycle
					@(negedge ck);
					dqs_reg = 2'b00;
					dqs_n_reg = 2'b11;
					addr_reg += 1'b1;

					// Seventh cycle
					@(posedge ck);
					dqs_reg = 2'b11;
					dqs_n_reg = 2'b00;
					addr_reg += 1'b1;

					// Eigth cycle
					@(negedge ck);
					dqs_reg = 2'b00;
					dqs_n_reg = 2'b11;
					addr_reg += 1'b1;

					// End transaction
					@(posedge ck);
					en_dqs = 1'b0;
					en_dqs_n = 1'b0;
					en_dq = 1'b0;

				end
			end

			CMD_WRITE : begin
				if (cke_prev && cke) begin

					RAM[ba].delete(addr);
					addr_reg = addr;
					bank_reg = ba;
					wait(dqs == 2'b00);
					@(posedge dqs[0]);
					$display("MSG: WRITE transaction of data '%x' to bank %d, address 0x%x at %t", dq, bank_reg, addr_reg, $time);
					RAM[bank_reg][addr_reg] = dq;
				end
			end

			default : begin
				en_dq = 1'b0;
				en_dqs = 1'b0;
				en_dqs_n = 1'b0;
			end

		endcase

		// Store previous value of cke
		// Need cke_prev && cke to read/write according to datasheet
		cke_prev <= cke;

	end

	/************************************************************************/
	/* Continuous assignments												*/
	/************************************************************************/

	// Have to use wire assignments and extra registers because dq/dqs/dqs_n
	// are tri-state (can only use continous wire assignments)

	assign dq = en_dq ? ((RAM.exists(bank_reg)&&RAM[bank_reg].exists(addr_reg)) ? RAM[bank_reg][addr_reg] : 16'b0) : 'z;
	assign dqs = en_dqs ? dqs_reg : 'z;
	assign dqs_n = en_dqs_n ? dqs_n_reg : 'z;

endmodule // ddr2_dram