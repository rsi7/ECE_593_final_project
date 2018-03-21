// Module: ddr2ifc_monitor.sv
// Author: Chris Loop
// Date: March 20th, 2018
// Organization: Portland State University
//
// Description:
// 	ddr2 interface monitor module
//
module ddr2ifc_monitor (

	// Inputs
	// Generic inputs

	input		ck,
	input		cke,
	input		reset,

// data signals
	input logic [12:0]	addr,
	input logic [1:0]	ba,
	input logic [15:0]	dq,
	input logic 		dqs,


// command signals
	input		cs_n,
	input		ras_n,
	input		cas_n,
	input		we_n

);

// local vars

	localparam	CMD_READ = 4'b0101;
	localparam	CMD_WRITE = 4'b0100;
	localparam	CMD_ACTIVATE = 4'b0011;
	localparam	CMD_PRECHRG = 4'b0010;
	localparam	CMD_NOP = 4'b0111;

	logic				cke_prev = 0;
	logic [12:0]		row;
	logic [1:0]			bank;
	logic [9:0]			col;
	logic [7:0][15:0]	data;	// create packed array, for easy printout later


	always @(posedge ck) begin
		// set cke_prev
		cke_prev <= cke;

		if (!reset && cke && cke_prev) begin
			case ({cs_n, ras_n, cas_n, we_n})
				CMD_ACTIVATE:	begin
							row = addr;
							bank = ba;
							$display("%m: ACT to bank %x row %x, at time %t", bank, row, $time);
						end
				CMD_PRECHRG:	$display("%m: PRECHARGE detected at time %t", $time);
				CMD_READ:	begin
							col = addr[9:0];

							@(posedge dqs);	// latch first data, ensure dqs on posedge first
							data[0] = dq;
							for (int i=1; i<8; i++) begin
								@(dqs);	// latch data
								data[i] = dq;
							end // for

							$display("%m: READ to column %x: data %x at time %t", col, data, $time);

						end
				CMD_WRITE: begin
							col = addr[9:0];

							@(posedge dqs);	// latch first data, ensure dqs on posedge first
							data[0] = dq;
							for (int i=1; i<8; i++) begin
								@(dqs);	// latch data
								data[i] = dq;
							end // for
							$display("%m: WRITE to column %x: data %x at time %t", col, data, $time);

						end
			endcase

		end // if


	end // always

endmodule