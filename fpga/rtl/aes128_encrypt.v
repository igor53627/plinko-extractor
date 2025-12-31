// AES-128 Encryption Core (Pipelined)
// 10 rounds, 12 pipeline stages total
// Throughput: 1 block per cycle after pipeline fills
`timescale 1ns/1ps

module aes128_encrypt (
    input          clk,
    input          rst_n,
    input          valid_in,
    input  [127:0] plaintext,
    input  [127:0] key,
    output         valid_out,
    output [127:0] ciphertext
);
    // Round constants for key expansion
    wire [7:0] rcon [0:9];
    assign rcon[0] = 8'h01; assign rcon[1] = 8'h02; assign rcon[2] = 8'h04;
    assign rcon[3] = 8'h08; assign rcon[4] = 8'h10; assign rcon[5] = 8'h20;
    assign rcon[6] = 8'h40; assign rcon[7] = 8'h80; assign rcon[8] = 8'h1b;
    assign rcon[9] = 8'h36;
    
    // Key expansion (combinational)
    wire [127:0] round_keys [0:10];
    assign round_keys[0] = key;
    
    genvar rnd;
    generate
        for (rnd = 0; rnd < 10; rnd = rnd + 1) begin : keygen
            wire [31:0] w0 = round_keys[rnd][127:96];
            wire [31:0] w1 = round_keys[rnd][95:64];
            wire [31:0] w2 = round_keys[rnd][63:32];
            wire [31:0] w3 = round_keys[rnd][31:0];
            
            // RotWord + SubWord on w3
            wire [7:0] sb0, sb1, sb2, sb3;
            aes_sbox sb_inst0 (.in(w3[23:16]), .out(sb0));
            aes_sbox sb_inst1 (.in(w3[15:8]),  .out(sb1));
            aes_sbox sb_inst2 (.in(w3[7:0]),   .out(sb2));
            aes_sbox sb_inst3 (.in(w3[31:24]), .out(sb3));
            
            wire [31:0] temp = {sb0 ^ rcon[rnd], sb1, sb2, sb3};
            
            wire [31:0] nw0 = w0 ^ temp;
            wire [31:0] nw1 = w1 ^ nw0;
            wire [31:0] nw2 = w2 ^ nw1;
            wire [31:0] nw3 = w3 ^ nw2;
            
            assign round_keys[rnd+1] = {nw0, nw1, nw2, nw3};
        end
    endgenerate
    
    // Pipeline: stage 0 = input, stages 1-10 = rounds, stage 11 = output
    reg [127:0] state_reg [0:11];
    reg [11:0]  valid_reg;
    
    // Initial AddRoundKey (combinational)
    wire [127:0] state_after_init = plaintext ^ round_keys[0];
    
    // Round function outputs (combinational)
    wire [127:0] state_after_round [1:10];
    
    generate
        for (rnd = 1; rnd <= 10; rnd = rnd + 1) begin : rounds
            aes_round round_inst (
                .state_in(state_reg[rnd]),
                .round_key(round_keys[rnd]),
                .is_last_round(rnd == 10),
                .state_out(state_after_round[rnd])
            );
        end
    endgenerate
    
    // Pipeline registers
    integer i;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_reg <= 12'b0;
            for (i = 0; i <= 11; i = i + 1) begin
                state_reg[i] <= 128'b0;
            end
        end else begin
            // Stage 0: capture input with initial AddRoundKey
            state_reg[0] <= state_after_init;
            valid_reg[0] <= valid_in;
            
            // Stages 1-10: round functions
            // Each stage reads from previous stage's register
            state_reg[1]  <= state_reg[0];           // Pass to round 1
            state_reg[2]  <= state_after_round[1];   // Round 1 result
            state_reg[3]  <= state_after_round[2];   // Round 2 result
            state_reg[4]  <= state_after_round[3];
            state_reg[5]  <= state_after_round[4];
            state_reg[6]  <= state_after_round[5];
            state_reg[7]  <= state_after_round[6];
            state_reg[8]  <= state_after_round[7];
            state_reg[9]  <= state_after_round[8];
            state_reg[10] <= state_after_round[9];
            state_reg[11] <= state_after_round[10];  // Final result
            
            // Shift valid through pipeline
            valid_reg[11:1] <= valid_reg[10:0];
        end
    end
    
    assign ciphertext = state_reg[11];
    assign valid_out = valid_reg[11];
endmodule
