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
		typedef	logic		unsigned	[3:0]	ulogic4;
		typedef	logic		unsigned	[7:0]	ulogic8;
		typedef logic		unsigned	[11:0]	ulogic12;
		typedef	logic		unsigned	[15:0]	ulogic16;
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

		// typedef for state
		typedef enum logic unsigned [3:0] {	

			RESET 		= 4'd0, 
			IDLE 		= 4'd1, 
			LOAD_FIB 	= 4'd2, 
			LOAD_TRI 	= 4'd3, 
			ERROR 		= 4'd4,
			FIB_ADD 	= 4'd5,
			TRI_ADD 	= 4'd6,
			OVRFLOW 	= 4'd7,
			DONE 		= 4'd8
			
			} state_t;

	endpackage

	// include the above definitions in the modules
	import definitions::*;

`endif