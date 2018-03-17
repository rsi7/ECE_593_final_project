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

	unsigned logic	[ADDR_WIDTH-1:0]	RAM[MEM_WIDTH];

	ulogic1		cke_prev;

	/************************************************************************/
	/* always block : read/write memory										*/
	/************************************************************************/

	always@(posedge ck) begin

		case ({cs_n, ras_n, cas_n, we_n})

			4'b0101 : begin		// READ
				if ((RAM.exists(addr)) && (cke_prev && cke)) begin
					repeat (4) @ (posedge ck);
					dq <= RAM[addr];
				end
			end

			4'b0100 : begin		// WRITE
				if (cke_prev && cke) begin
					repeat (4) @ (posedge ck);
					RAM.delete(addr);
					RAM[addr] <= dq;
				end
			end

			else : begin
				dq		<= 'z;
				dqs		<= 'z;
				dqs_n	<= 'z;
			end

		endcase

		// Store previous value of cke
		cke_prev <= cke;

	end

endmodule // ddr2_dram