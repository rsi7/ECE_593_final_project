// Module: definitions.pkg
// Author: Rehan Iqbal
// Date: January 15th, 2018
// Organization: Portland State University
//
// Description:
// ------------
// Package definitions file for the ECE 593 Lab #1 module & testbench. 
// Contains type definitions for unsigned vars & parameters for FSM states.
//
// Include in target modules through syntax: `include "definitions.pkg"
// Make sure library paths include this file!
// 
//////////////////////////////////////////////////////////////////////////////
	
// check if file has been imported already
`ifndef IMPORT_DEFS

	// make sure other modules dont' re-import
	`define IMPORT_DEFS

	package definitions;

		// type definitions for unsigned 4-state variables
		typedef	logic		unsigned			ulogic1;
		typedef	logic		unsigned	[1:0]	ulogic2;
		typedef logic		unsigned	[2:0]	ulogic3;
		typedef	logic		unsigned	[3:0]	ulogic4;
		typedef logic		unsigned	[4:0]	ulogic5;
		typedef logic		unsigned	[5:0]	ulogic6;
		typedef logic		unsigned	[6:0]	ulogic7;
		typedef	logic		unsigned	[7:0]	ulogic8;

		typedef logic		unsigned	[8:0]	ulogic9;
		typedef logic		unsigned	[9:0]	ulogic10;
		typedef logic		unsigned	[10:0]	ulogic11;
		typedef logic		unsigned	[11:0]	ulogic12;
		typedef logic		unsigned	[12:0]	ulogic13;
		typedef logic		unsigned	[13:0]	ulogic14;
		typedef logic		unsigned	[14:0]	ulogic15;
		typedef	logic		unsigned	[15:0]	ulogic16;

		typedef logic		unsigned	[24:0]	ulogic25;
		typedef	logic		unsigned	[31:0]	ulogic32;
		typedef	logic		unsigned	[63:0]	ulogic64;

		// type definitions for unsigned 2-state variables
		typedef bit			unsigned			uint1;
		typedef	bit			unsigned	[1:0]	uint2;
		typedef	bit			unsigned	[3:0]	uint4;
		typedef	byte		unsigned			uint8;
		typedef	shortint	unsigned			uint16;
		typedef	int			unsigned			uint32;
		typedef	longint		unsigned			uint64;

		// Enum for input file commands
		typedef enum logic unsigned [2:0] {	

			NOP1		= 3'b000,
			SCR			= 3'b001,
			SCW			= 3'b010,
			BLR			= 3'b011,
			BLW			= 3'b100,
			ATR			= 3'b101,
			ATW			= 3'b110,
			NOP2		= 3'b111
			
		} FILE_CMD;

		// Enum for DDR commands
		// { CS# / RAS# / CAS# / WE# }
		typedef enum logic unsigned [3:0] {	

			READ		= 4'b0101,
			WRITE		= 4'b0100,
			ACTIVATE	= 4'b0011,
			PRECHRG		= 4'b0010,
			NOP_DDR		= 4'b0111
			
		} DDR_CMD;

		// Address structure used in packet structure below
		typedef struct {

		ulogic2		bank;
		ulogic13	row;
		ulogic10	column;

		} packet_address;

		// Packet structure for monitor modules
		typedef struct {

			int				timestamp;
			int				id;
			ulogic3			command;
			packet_address	address;
			ulogic16		data;

		} packet;

	endpackage

	// include the above definitions in the modules
	import definitions::*;

`endif