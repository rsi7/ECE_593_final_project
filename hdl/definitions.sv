// Module: definitions.pkg
// Author: Rehan Iqbal
// Date: March 22nd, 2018
// Organization: Portland State University
//
// Description:
// ------------
// Package definitions file for the ECE 593 final project testbench. 
// Contains type definitions for unsigned vars & structs for packets.
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