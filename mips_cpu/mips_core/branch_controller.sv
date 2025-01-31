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
        // branch_predictor_always_taken PREDICTOR (
        // branch_predictor_2bit PREDICTOR (
        // branch_predictor_global PREDICTOR (
	// branch_predictor_2level_local PREDICTOR (
	branch_predictor_tournament PREDICTOR (
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


	//----------------------------------- Branch Mispredict Counter -------------------------------------------------

        // wire i_fb_outcome, i_fb_valid;
	// assign i_fb_valid   = ex_branch_result.valid;
        // assign i_fb_outcome = (ex_branch_result.outcome === NOT_TAKEN) ? 0 : ( (ex_branch_result.outcome === TAKEN) ? 1 : 0);
        // 
	// wire [`ADDR_WIDTH - 1 : 0] i_fb_pc;
	// assign i_fb_pc = ex_pc.pc;

        // wire [`ADDR_WIDTH - 1 : 0] i_req_pc;
	// wire i_req_valid;
	// wire i_req_pred;
	// assign i_req_pc = dec_pc.pc;

	// wire curr_prediction;
	// assign curr_prediction = (dec_branch_decoded.prediction === NOT_TAKEN) ? 0 : ( (dec_branch_decoded.prediction === TAKEN) ? 1 : 0);
        // reg prev_prediction;
        // always_ff @(posedge clk) begin
        //         if(~rst_n)              	prev_prediction <= 'd0;
        //         else if(i_fb_valid)     	prev_prediction <= curr_prediction;
        // end

        // reg [31:0] branch_count;
        // always_ff @(posedge clk) begin
        //         if(~rst_n)              	branch_count <= 'd0;
        //         else if(i_fb_valid)     	branch_count <= branch_count + 1'd1;
        // end

        // reg [31:0] correct_count;
        // always_ff @(posedge clk) begin
        //         if(~rst_n)              	correct_count <= 'd0;
        //         else if(i_fb_valid)     	correct_count <= correct_count + (curr_prediction == i_fb_outcome);
        // end

        // reg [31:0] incorrect_count;
        // always_ff @(posedge clk) begin
        //         if(~rst_n)              	incorrect_count <= 'd0;
        //         else if(i_fb_valid)     	incorrect_count <= incorrect_count + (curr_prediction != i_fb_outcome);
        // end

	wire ex_overload;
	assign ex_overload = ex_branch_result.valid & (ex_branch_result.prediction != ex_branch_result.outcome);

        reg [31:0] branch_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		branch_count <= 'd0;
                else if(ex_branch_result.valid)     	branch_count <= branch_count + 1'd1;
        end

        reg [31:0] correct_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		correct_count <= 'd0;
                else if(ex_branch_result.valid)     	correct_count <= correct_count + (ex_overload ? 0 : 1);
        end

        reg [31:0] incorrect_count;
        always_ff @(posedge clk) begin
                if(~rst_n)              		incorrect_count <= 'd0;
                else if(ex_branch_result.valid)     	incorrect_count <= incorrect_count + (ex_overload ? 1 : 0);
        end



        always_ff @(posedge clk) begin
                if(ex_branch_result.valid && (branch_count%100000 == 0) )  begin
			$display("Total=%d Correct=%d Incorrect=%d Branch Accuracy=%f",branch_count,correct_count,incorrect_count,((correct_count/(branch_count*1.0))*100)  );
			if(branch_count == 1000000)
				$stop;
		end
        end
	//---------------------------------------------------------------------------------------------------------------


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

module branch_predictor_always_taken (
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
                o_req_prediction = TAKEN;
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

        parameter N = 2;
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
        localparam M = 9; // History bits
	localparam PC_OFFSET = 2;

        reg [M-1:0] GHR ;  // Global History Register
        reg [M-1:0] GHR_PREV ;  // Global History Register
        wire [2**M-1:0] PRED ;

        wire [M-1:0] PHT_INDEX_PREDICT, PHT_INDEX_UPDATE;
	assign PHT_INDEX_UPDATE  = GHR ^  i_fb_pc[M+PC_OFFSET-1  -: M] ;
	assign PHT_INDEX_PREDICT = GHR ^ i_req_pc[M+PC_OFFSET-1  -: M] ;

        always_ff @(posedge clk) begin
                if(~rst_n)              GHR <= 'd0;
                else if(i_fb_valid)     GHR <= {GHR[M-2:0],outcome};
        end

        always_ff @(posedge clk) begin
                if(~rst_n)              GHR_PREV <= 'd0;
                else if(i_fb_valid)     GHR_PREV <= GHR;
        end

        genvar i;
        generate
                for(i=0; i<2**M; i=i+1) begin : SATCNT_2BIT
                        SAT_CNT_2bit #(.N(N)) SAT_CNT_2BIT (
                                .clk, .rst_n,
                                .o_req_prediction(PRED[i]),
                                .i_fb_valid      (i_fb_valid & (i ==  PHT_INDEX_UPDATE)),
                                .i_fb_outcome    (i_fb_outcome)
                        );
                end
        endgenerate



        always_comb
        begin
                // o_req_prediction = counter[N-1] ? TAKEN : NOT_TAKEN;
                o_req_prediction = PRED[PHT_INDEX_PREDICT] ? TAKEN : NOT_TAKEN;
        end

endmodule

module branch_predictor_2level_local (
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

        localparam PHT_N = 2;
	localparam PHT_ENTRIES = 10;
        localparam M = 5;
	localparam K = 6;
	localparam N = PHT_ENTRIES - M; 
	localparam PC_OFFSET = 2;

        reg [M-1:0] BHT [0:2**K-1] ;  // Global History Register
        wire [2**PHT_ENTRIES-1:0] PRED ;

        wire [N+M-1:0] 	PHT_INDEX_UPDATE;
	wire [K-1:0]	BHT_INDEX_UPDATE;
	assign BHT_INDEX_UPDATE  = i_fb_pc[K+PC_OFFSET-1  -: K] ;
	assign PHT_INDEX_UPDATE  = {i_fb_pc[N+PC_OFFSET-1  -: N],BHT[BHT_INDEX_UPDATE]} ;

        wire [N+M-1:0] 	PHT_INDEX_PREDICT;
	wire [K-1:0]	BHT_INDEX_PREDICT;
	wire [M-1:0]	BHT_ENTRY;
	assign BHT_ENTRY	  = BHT[BHT_INDEX_PREDICT];
	assign BHT_INDEX_PREDICT  = i_req_pc[K+PC_OFFSET-1  -: K] ;
	assign PHT_INDEX_PREDICT  = {i_req_pc[N+PC_OFFSET-1  -: N],BHT_ENTRY} ;

        genvar i;
	generate
		for(i=0; i<2**K; i=i+1) begin
        		always_ff @(posedge clk) begin
        		        if(~rst_n)              			BHT[i] <= 'd0;
        		        else if(i_fb_valid & (i == BHT_INDEX_UPDATE))   BHT[i] <= {BHT[i][M-2:0],outcome};
        		end
		end
	endgenerate

        generate
                for(i=0; i<2**PHT_ENTRIES; i=i+1) begin : SATCNT_2BIT
                        SAT_CNT_2bit #(.N(PHT_N)) SAT_CNT_2BIT (
                                .clk, .rst_n,
                                .o_req_prediction(PRED[i]),
                                .i_fb_valid      (i_fb_valid & (i ==  PHT_INDEX_UPDATE)),
                                .i_fb_outcome    (i_fb_outcome)
                        );
                end
        endgenerate



        always_comb
        begin
                // o_req_prediction = counter[N-1] ? TAKEN : NOT_TAKEN;
                o_req_prediction = PRED[PHT_INDEX_PREDICT] ? TAKEN : NOT_TAKEN;
        end

endmodule

module branch_predictor_tournament (
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
	localparam M = 10;
	localparam PC_OFFSET = 2;

        wire mips_core_pkg::BranchOutcome 	o_req_pred_local_t;
        wire mips_core_pkg::BranchOutcome 	o_req_pred_gshare_t;
        wire  					o_req_pred_local;
        wire  					o_req_pred_gshare;

        assign o_req_pred_local = (o_req_pred_local_t === NOT_TAKEN) ? 0 : ( (o_req_pred_local_t === TAKEN) ? 1 : 0);
        assign o_req_pred_gshare = (o_req_pred_gshare_t === NOT_TAKEN) ? 0 : ( (o_req_pred_gshare_t === TAKEN) ? 1 : 0);

	// Predictor 0
	branch_predictor_2level_local bp_local (
                .clk, .rst_n,

                .i_req_valid     (i_req_valid),
                .i_req_pc        (i_req_pc),
                .i_req_target    (i_req_target),
                .o_req_prediction(o_req_pred_local_t),

                .i_fb_valid      (i_fb_valid),
                .i_fb_pc         (i_fb_pc),
                .i_fb_prediction (i_fb_prediction),
                .i_fb_outcome    (i_fb_outcome)
        );

	// Predictor 1
	branch_predictor_global bp_gshare (
                .clk, .rst_n,

                .i_req_valid     (i_req_valid),
                .i_req_pc        (i_req_pc),
                .i_req_target    (i_req_target),
                .o_req_prediction(o_req_pred_gshare_t),

                .i_fb_valid      (i_fb_valid),
                .i_fb_pc         (i_fb_pc),
                .i_fb_prediction (i_fb_prediction),
                .i_fb_outcome    (i_fb_outcome)
        );

	// Meta Predictor
        wire [2**M-1:0] PRED ;
	wire [M-1:0] 	META_INDEX_UPDATE;
	assign 		META_INDEX_UPDATE  =  i_fb_pc[M+PC_OFFSET-1  -: M] ;

	wire [M-1:0] 	META_INDEX_PREDICT;
	assign 		META_INDEX_PREDICT = i_req_pc[M+PC_OFFSET-1  -: M] ;

	reg w_fb_pred_local;
	always_ff  @(posedge clk) begin
		if(~rst_n)			w_fb_pred_local <= 1'b0;
		else if(i_req_valid)		w_fb_pred_local <= o_req_pred_local;
	end

	reg w_fb_pred_gshare;
	always_ff  @(posedge clk) begin
		if(~rst_n)			w_fb_pred_gshare <= 1'b0;
		else if(i_req_valid)		w_fb_pred_gshare <= o_req_pred_gshare;
	end



	// Training the Meta Predictor
	wire choice_predictor;
	assign choice_predictor = i_fb_outcome == w_fb_pred_local ? 0 : 1; 

        genvar i;
        generate
                for(i=0; i<2**M; i=i+1) begin : SATCNT_2BIT
                        SAT_CNT_2bit #(.N(N)) SAT_CNT_2BIT (
                                .clk, .rst_n,
                                .o_req_prediction(PRED[i]),
                                .i_fb_valid      (i_fb_valid & (i ==  META_INDEX_UPDATE) & (w_fb_pred_local ^ w_fb_pred_gshare)), 
                                .i_fb_outcome    (choice_predictor) 	// Predictor 0 (local) or predictor 1 (gshare)
                        );
                end
        endgenerate


	// Predicter Selection Mux
	assign o_req_prediction = PRED[META_INDEX_PREDICT] == 0 ? o_req_pred_local_t : o_req_pred_gshare_t ;


endmodule
