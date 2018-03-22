// Module: top_checker_scoreboard.sv
// Author: Rehan Iqbal
// Date: March 17th, 2018
// Organziation: Portland State University
//
// This checker/scoreboard takes in an input packet (cmd_pkt from the command_monitor)
// and an output packet (ddr_pkt from the ddr_monitor) and stores them all
// in arrays. At the end of simulation (signalled with 'start_check') it will
// make sure all output packets have a corresponding input packet and vice-versa.
//
////////////////////////////////////////////////////////////////////////////////

`include "definitions.sv"

module top_checker_scoreboard (

	/************************************************************************/
	/* Top-level port declarations											*/
	/************************************************************************/

	input	packet		ddr_pkt,
	input	packet		cmd_pkt
	
);

	/************************************************************************/
	/* Local parameters and variables										*/
	/************************************************************************/

	// Declare two associative arrays for storing each type of packet...
	// will iterate through this to compare them
	packet	ddr_pkt_array[int];
	packet	cmd_pkt_array[int];

	ulogic1	done_check = 0;

	/************************************************************************/
	/* always block : store ddr_pkt											*/
	/************************************************************************/

	always@(ddr_pkt.id) begin
		ddr_pkt_array[ddr_pkt.id] = ddr_pkt;
	end

	/************************************************************************/
	/* always block : store cmd_pkt											*/
	/************************************************************************/
	
	always@(cmd_pkt.id) begin
		cmd_pkt_array[cmd_pkt.id] = cmd_pkt;
	end

	/************************************************************************/
	/* task block : checking												*/
	/************************************************************************/

	task start_check ();

		foreach(ddr_pkt_array[i]) begin

			// Check the address on both packets raise an error if difference
			// between DDR & commands is found on either bank or row or column
			// Using an else statement since we don't need to raise 3 messages if all 3 are wrong...
			if ((ddr_pkt_array[i].address.bank != cmd_pkt_array[i+1].address.bank)) begin
				$display("Checker: Error found located on DDR packet '%8x' bank address! DDR was '%d' while command was '%d'", i, ddr_pkt_array[i].address.bank, cmd_pkt_array[i+1].address.bank);
			end

			else if ((ddr_pkt_array[i].address.row != cmd_pkt_array[i+1].address.row)) begin
				$display("Checker: Disparity located on DDR packet '%8x' row address! DDR was '0x%x' while command was '0x%x'", i, ddr_pkt_array[i].address.row, cmd_pkt_array[i+1].address.row);
			end 

			else if ((ddr_pkt_array[i].address.column != cmd_pkt_array[i+1].address.column)) begin
				$display("Checker: Disparity located on DDR packet '%8x' column address! DDR was '0x%x' while command was '0x%x'", i, ddr_pkt_array[i].address.column, cmd_pkt_array[i+1].address.column);
			end

			// Check the data on both packets and raise an error if difference
			// between DDR & commands is found
			if ((ddr_pkt_array[i].data != cmd_pkt_array[i+1].data)) begin
				$display("Checker: Disparity located on DDR packet '%8x' data! DDR was '%4x' while command was '%4x'", i, ddr_pkt_array[i].data, cmd_pkt_array[i+1].data);
			end

		end

		done_check = 1'b1;

	endtask

endmodule // top_checker_scoreboard