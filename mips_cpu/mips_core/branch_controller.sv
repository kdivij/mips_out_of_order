/*
 * branch_controller.sv
 * Author: Zinsser Zhang
 * Last Revision: 04/08/2018
 *
 * branch_controller is a bridge between branch predictor to hazard controller.
 * Two simple predictors are also provided as examples.
 *
 * See wiki page "Branch and Jump" for details.
 */
`include "mips_core.svh"

module branch_controller (
        input clk,    // Clock
        input rst_n,  // Synchronous reset active low

        // Request
        pc_ifc.in dec_pc,
        branch_decoded_ifc.hazard dec_branch_decoded,

        // Feedback
        pc_ifc.in ex_pc,
        branch_result_ifc.in ex_branch_result
);
        logic request_prediction;

        // Change the following line to switch predictor
        // branch_predictor_always_not_taken PREDICTOR (
        // branch_predictor_2bit PREDICTOR (
        branch_predictor_global PREDICTOR (
                .clk, .rst_n,

                .i_req_valid     (request_prediction),
                .i_req_pc        (dec_pc.pc),
                .i_req_target    (dec_branch_decoded.target),
                .o_req_prediction(dec_branch_decoded.prediction),

                .i_fb_valid      (ex_branch_result.valid),
                .i_fb_pc         (ex_pc.pc),
                .i_fb_prediction (ex_branch_result.prediction),
                .i_fb_outcome    (ex_branch_result.outcome)
        );

        always_comb
        begin
                request_prediction = dec_branch_decoded.valid & ~dec_branch_decoded.is_jump;
                dec_branch_decoded.recovery_target =
                        (dec_branch_decoded.prediction == TAKEN)
                        ? dec_pc.pc + `ADDR_WIDTH'd8
                        : dec_branch_decoded.target;
        end

        wire outcome;
        assign outcome = (ex_branch_result.outcome === NOT_TAKEN) ? 0 : ( (ex_branch_result.outcome === TAKEN) ? 1 : 0);
        reg prev_prediction;
        always_ff @(posedge clk) begin
                if(~rst_n)              		prev_prediction <= 'd0;
                else if(ex_branch_result.valid)     	prev_prediction <= (dec_branch_decoded.prediction === NOT_TAKEN) ? 0 : ( (dec_branch_decoded.prediction === TAKEN) ? 1 : 0);
        end

        reg [31:0] branch_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		branch_count <= 'd0;
                else if(ex_branch_result.valid)     	branch_count <= branch_count + 1'd1;
        end

        reg [31:0] correct_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		correct_count <= 'd0;
                else if(ex_branch_result.valid)     	correct_count <= correct_count + (prev_prediction == outcome);
        end

        reg [31:0] incorrect_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		incorrect_count <= 'd0;
                else if(ex_branch_result.valid)     	incorrect_count <= incorrect_count + (prev_prediction != outcome);
        end

        always_ff @(posedge clk) begin
                if(ex_branch_result.valid && (branch_count%100000 == 0) )  begin
			$display("Total=%d Correct=%d Incorrect=%d Branch Accuracy=%f",branch_count,correct_count,incorrect_count,((correct_count/(branch_count*1.0))*100)  );
			if(branch_count == 1000000)
				$stop;
		end
        end


endmodule

module branch_predictor_always_not_taken (
        input clk,    // Clock
        input rst_n,  // Synchronous reset active low

        // Request
        input logic i_req_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_pc,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_target,
        output mips_core_pkg::BranchOutcome o_req_prediction,

        // Feedback
        input logic i_fb_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_fb_pc,
        input mips_core_pkg::BranchOutcome i_fb_prediction,
        input mips_core_pkg::BranchOutcome i_fb_outcome
);

        always_comb
        begin
                o_req_prediction = NOT_TAKEN;
        end

endmodule

module branch_predictor_2bit (
        input clk,    // Clock
        input rst_n,  // Synchronous reset active low

        // Request
        input logic i_req_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_pc,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_target,
        output mips_core_pkg::BranchOutcome o_req_prediction,

        // Feedback
        input logic i_fb_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_fb_pc,
        input mips_core_pkg::BranchOutcome i_fb_prediction,
        input mips_core_pkg::BranchOutcome i_fb_outcome
);

        localparam N = 2;

        logic [N-1:0] counter;

        task incr;
                begin
                        if (counter != {N{1'b1}})
                                counter <= counter + 'd01;
                end
        endtask

        task decr;
                begin
                        if (counter != {N{1'b0}})
                                counter <= counter - 'd01;
                end
        endtask

        always_ff @(posedge clk)
        begin
                if(~rst_n)
                begin
                        counter <= 'd1; // Weakly not taken
                end
                else
                begin
                        if (i_fb_valid)
                        begin
                                case (i_fb_outcome)
                                        NOT_TAKEN: decr();
                                        TAKEN:     incr();
                                endcase
                        end
                end
        end

        always_comb
        begin
                o_req_prediction = counter[N-1] ? TAKEN : NOT_TAKEN;
        end

endmodule

module SAT_CNT_2bit (
        input clk,    // Clock
        input rst_n,  // Synchronous reset active low

        // Request
        input logic i_req_valid,
        output  o_req_prediction,

        // Feedback
        input logic i_fb_valid,
        input mips_core_pkg::BranchOutcome i_fb_outcome
);

        wire outcome;
        assign outcome = (i_fb_outcome === NOT_TAKEN) ? 0 : ( (i_fb_outcome === TAKEN) ? 1 : 0);


        localparam N = 2;

        logic [N-1:0] counter;

        task incr;
                begin
                        if (counter != {N{1'b1}})
                                counter <= counter + 'd01;
                end
        endtask

        task decr;
                begin
                        if (counter != {N{1'b0}})
                                counter <= counter - 'd01;
                end
        endtask

        always_ff @(posedge clk)
        begin
                if(~rst_n)
                begin
                        counter <= 'd1; // Weakly not taken
                end
                else
                begin
                        if (i_fb_valid)
                        begin
                                case (i_fb_outcome)
                                        NOT_TAKEN: decr();
                                        TAKEN:     incr();
                                endcase
                        end
                end
        end

        always_comb
        begin
                assign o_req_prediction = counter[N-1];
        end

endmodule

module branch_predictor_global (
        input clk,    // Clock
        input rst_n,  // Synchronous reset active low

        // Request
        input logic i_req_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_pc,
        input logic [`ADDR_WIDTH - 1 : 0] i_req_target,
        output mips_core_pkg::BranchOutcome o_req_prediction,

        // Feedback
        input logic i_fb_valid,
        input logic [`ADDR_WIDTH - 1 : 0] i_fb_pc,
        input mips_core_pkg::BranchOutcome i_fb_prediction,
        input mips_core_pkg::BranchOutcome i_fb_outcome
);

        wire outcome;
        assign outcome = (i_fb_outcome === NOT_TAKEN) ? 0 : ( (i_fb_outcome === TAKEN) ? 1 : 0);

        localparam N = 2;
        localparam M = 6; // History bits

        reg [M-1:0] GHR ;  // Global History Register
        wire [2**M-1:0] PRED ;


        always_ff @(posedge clk) begin
                if(~rst_n)              GHR <= 'd0;
                else if(i_fb_valid)     GHR <= {GHR[M-2:0],outcome};
        end

        genvar i;
        generate
                for(i=0; i<2**M; i=i+1) begin : SATCNT_2BIT
                        SAT_CNT_2bit SAT_CNT_2BIT (
                                .clk, .rst_n,
                                .o_req_prediction(PRED[i]),
                                .i_fb_valid      (i_fb_valid & (i == (GHR /*^ i_req_pc[M+1  -: M]*/) )),
                                .i_fb_outcome    (i_fb_outcome)
                        );
                end
        endgenerate



        always_comb
        begin
                // o_req_prediction = counter[N-1] ? TAKEN : NOT_TAKEN;
                o_req_prediction = PRED[GHR /*^ i_req_pc[M+1  -: M]*/] ? TAKEN : NOT_TAKEN;
                // o_req_prediction = PRED[GHR] ? TAKEN : NOT_TAKEN;
                // o_req_prediction = PRED[0] ? TAKEN : NOT_TAKEN;
                // o_req_prediction = TAKEN;
        end

endmodule

