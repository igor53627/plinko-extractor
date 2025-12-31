// Single Swap-or-Not Round (Constant-Time)
// Implements one round of Morris-Rogaway Swap-or-Not PRP
//
// Per round:
//   1. Compute partner = K_i - x mod N
//   2. Compute canonical = max(x, partner)
//   3. PRF bit from AES(round | 0x80000000, canonical)
//   4. If PRF bit = 1, swap to partner; else keep x
//
// This module assumes K_i and PRF bit are pre-computed externally
module swap_or_not_round #(
    parameter WIDTH = 64
)(
    input                  clk,
    input                  rst_n,
    input                  valid_in,
    input  [WIDTH-1:0]     x_in,
    input  [WIDTH-1:0]     k_i,        // Round key (derived from AES)
    input  [WIDTH-1:0]     domain,     // N
    input                  prf_bit,    // Pre-computed PRF decision bit
    output reg             valid_out,
    output reg [WIDTH-1:0] x_out
);
    // Combinational logic
    wire [WIDTH-1:0] partner;
    wire [WIDTH-1:0] canonical;
    wire [WIDTH-1:0] result;
    
    // partner = (k_i + domain - x) mod domain
    // Using wide arithmetic to avoid overflow
    wire [WIDTH:0] sum = k_i + domain - x_in;
    wire [WIDTH-1:0] partner_raw = sum[WIDTH-1:0];
    
    // Modular reduction (constant-time)
    wire partner_ge_domain = (partner_raw >= domain);
    assign partner = partner_ge_domain ? (partner_raw - domain) : partner_raw;
    
    // canonical = max(x, partner) - constant-time select
    wire x_ge_partner = (x_in >= partner);
    assign canonical = x_ge_partner ? x_in : partner;
    
    // Result selection based on PRF bit (constant-time)
    assign result = prf_bit ? partner : x_in;
    
    // Pipeline register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
            x_out <= {WIDTH{1'b0}};
        end else begin
            valid_out <= valid_in;
            x_out <= result;
        end
    end
endmodule

// Swap-or-Not PRP with N rounds (iterative)
// Processes one value through all rounds sequentially
module swap_or_not_prp #(
    parameter WIDTH = 64,
    parameter MAX_ROUNDS = 128  // Support up to 128 rounds
)(
    input                  clk,
    input                  rst_n,
    input                  start,
    input  [WIDTH-1:0]     x_in,
    input  [WIDTH-1:0]     domain,
    input  [127:0]         key,
    input  [7:0]           num_rounds, // Actual rounds to use
    input                  direction,  // 0=forward, 1=inverse
    output reg             done,
    output reg [WIDTH-1:0] x_out,
    output reg             busy
);
    // State machine
    localparam IDLE = 2'd0, COMPUTING = 2'd1, DONE = 2'd2;
    reg [1:0] state;
    
    // Round counter
    reg [7:0] round_cnt;
    reg [7:0] current_round;
    
    // Current value being permuted
    reg [WIDTH-1:0] x_current;
    
    // AES interface for PRF (simplified - assumes external AES)
    reg [127:0] aes_input;
    wire [127:0] aes_output;
    reg aes_valid_in;
    wire aes_valid_out;
    
    // Instantiate AES for PRF
    aes128_encrypt aes_inst (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(aes_valid_in),
        .plaintext(aes_input),
        .key(key),
        .valid_out(aes_valid_out),
        .ciphertext(aes_output)
    );
    
    // Derive K_i from AES output
    wire [WIDTH-1:0] k_i = aes_output[127:64] % domain;
    wire prf_bit = aes_output[0];
    
    // Compute partner and result
    wire [WIDTH:0] sum = k_i + domain - x_current;
    wire [WIDTH-1:0] partner_raw = sum[WIDTH-1:0];
    wire partner_ge_domain = (partner_raw >= domain);
    wire [WIDTH-1:0] partner = partner_ge_domain ? (partner_raw - domain) : partner_raw;
    wire [WIDTH-1:0] next_x = prf_bit ? partner : x_current;
    
    // State machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 1'b0;
            busy <= 1'b0;
            round_cnt <= 8'd0;
            x_current <= {WIDTH{1'b0}};
            x_out <= {WIDTH{1'b0}};
            aes_valid_in <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 1'b0;
                    if (start) begin
                        state <= COMPUTING;
                        busy <= 1'b1;
                        x_current <= x_in;
                        round_cnt <= 8'd0;
                        // Start first AES computation
                        current_round <= direction ? (num_rounds - 1) : 8'd0;
                        aes_input <= {current_round, 56'd0, domain};
                        aes_valid_in <= 1'b1;
                    end
                end
                
                COMPUTING: begin
                    aes_valid_in <= 1'b0;
                    
                    if (aes_valid_out) begin
                        // Apply round function
                        x_current <= next_x;
                        round_cnt <= round_cnt + 1;
                        
                        if (round_cnt + 1 >= num_rounds) begin
                            // All rounds complete
                            state <= DONE;
                            x_out <= next_x;
                            done <= 1'b1;
                            busy <= 1'b0;
                        end else begin
                            // Start next round's AES
                            if (direction) begin
                                current_round <= current_round - 1;
                            end else begin
                                current_round <= current_round + 1;
                            end
                            aes_input <= {current_round, 56'd0, domain};
                            aes_valid_in <= 1'b1;
                        end
                    end
                end
                
                DONE: begin
                    done <= 1'b0;
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule
