// Systolic Array for Parallel PRP Inverse
// Processes NUM_LANES candidates simultaneously through shared round logic
//
// Architecture:
//   - All lanes share the same AES key schedule (derived once per batch)
//   - Each lane has its own value register
//   - Round keys broadcast to all lanes
//   - Throughput: NUM_LANES results per (num_rounds * AES_LATENCY) cycles
//
// For Plinko iPRF inverse: NUM_LANES = 512 (MAX_PREIMAGES)
module prp_systolic_array #(
    parameter WIDTH = 64,
    parameter NUM_LANES = 512,
    parameter MAX_ROUNDS = 128,
    parameter AES_LATENCY = 11  // Pipelined AES latency
)(
    input                          clk,
    input                          rst_n,
    input                          start,
    input  [WIDTH*NUM_LANES-1:0]   x_in,        // All candidates packed
    input  [WIDTH-1:0]             domain,
    input  [127:0]                 key,
    input  [7:0]                   num_rounds,
    input                          direction,   // 0=forward, 1=inverse
    output reg                     done,
    output [WIDTH*NUM_LANES-1:0]   x_out,
    output reg                     busy
);
    // State machine
    localparam IDLE = 2'd0, WAIT_AES = 2'd1, APPLY_ROUND = 2'd2, DONE_ST = 2'd3;
    reg [1:0] state;
    
    // Round tracking
    reg [7:0] round_cnt;
    reg [7:0] current_round;
    
    // Lane value registers
    reg [WIDTH-1:0] lane_vals [0:NUM_LANES-1];
    
    // AES for PRF computation (shared across all lanes per round)
    reg [127:0] aes_input;
    wire [127:0] aes_output;
    reg aes_valid_in;
    wire aes_valid_out;
    
    aes128_encrypt aes_inst (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(aes_valid_in),
        .plaintext(aes_input),
        .key(key),
        .valid_out(aes_valid_out),
        .ciphertext(aes_output)
    );
    
    // Round key derived from AES (same for all lanes in this round)
    wire [WIDTH-1:0] k_i = aes_output[127:64] % domain;
    wire prf_base_bit = aes_output[0];
    
    // Generate parallel lane logic
    genvar lane;
    generate
        for (lane = 0; lane < NUM_LANES; lane = lane + 1) begin : lane_logic
            // Compute partner for this lane
            wire [WIDTH:0] sum = k_i + domain - lane_vals[lane];
            wire [WIDTH-1:0] partner_raw = sum[WIDTH-1:0];
            wire partner_ge_domain = (partner_raw >= domain);
            wire [WIDTH-1:0] partner = partner_ge_domain ? (partner_raw - domain) : partner_raw;
            
            // Canonical representative for PRF bit derivation
            wire [WIDTH-1:0] canonical = (lane_vals[lane] >= partner) ? lane_vals[lane] : partner;
            
            // Each lane needs its own PRF bit based on canonical value
            // Simplified: use hash of (prf_base_bit, canonical, lane) 
            // In real impl, would need per-lane AES or different derivation
            wire prf_bit = prf_base_bit ^ canonical[0] ^ lane_vals[lane][1];
            
            // Next value (constant-time select)
            wire [WIDTH-1:0] next_val = prf_bit ? partner : lane_vals[lane];
            
            // Output assignment
            assign x_out[lane*WIDTH +: WIDTH] = lane_vals[lane];
        end
    endgenerate
    
    // State machine
    integer i;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 1'b0;
            busy <= 1'b0;
            round_cnt <= 8'd0;
            aes_valid_in <= 1'b0;
            for (i = 0; i < NUM_LANES; i = i + 1) begin
                lane_vals[i] <= {WIDTH{1'b0}};
            end
        end else begin
            case (state)
                IDLE: begin
                    done <= 1'b0;
                    if (start) begin
                        state <= WAIT_AES;
                        busy <= 1'b1;
                        round_cnt <= 8'd0;
                        current_round <= direction ? (num_rounds - 1) : 8'd0;
                        
                        // Load all lanes
                        for (i = 0; i < NUM_LANES; i = i + 1) begin
                            lane_vals[i] <= x_in[i*WIDTH +: WIDTH];
                        end
                        
                        // Start AES for first round key
                        aes_input <= {current_round, 56'd0, domain};
                        aes_valid_in <= 1'b1;
                    end
                end
                
                WAIT_AES: begin
                    aes_valid_in <= 1'b0;
                    if (aes_valid_out) begin
                        state <= APPLY_ROUND;
                    end
                end
                
                APPLY_ROUND: begin
                    // Apply round function to all lanes simultaneously
                    for (i = 0; i < NUM_LANES; i = i + 1) begin
                        // Recalculate (same as generate block but for assignment)
                        lane_vals[i] <= lane_logic[i].next_val;
                    end
                    
                    round_cnt <= round_cnt + 1;
                    
                    if (round_cnt + 1 >= num_rounds) begin
                        state <= DONE_ST;
                        done <= 1'b1;
                        busy <= 1'b0;
                    end else begin
                        // Next round
                        if (direction) begin
                            current_round <= current_round - 1;
                        end else begin
                            current_round <= current_round + 1;
                        end
                        aes_input <= {current_round, 56'd0, domain};
                        aes_valid_in <= 1'b1;
                        state <= WAIT_AES;
                    end
                end
                
                DONE_ST: begin
                    done <= 1'b0;
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule

// Top-level Plinko iPRF Inverse Accelerator
module iprf_inverse_accel #(
    parameter WIDTH = 64,
    parameter NUM_CANDIDATES = 512
)(
    input                              clk,
    input                              rst_n,
    // Control interface
    input                              start,
    input  [WIDTH-1:0]                 y,           // Output value to invert
    input  [WIDTH-1:0]                 domain,      // iPRF domain (n)
    input  [WIDTH-1:0]                 range,       // iPRF range (m)
    input  [127:0]                     key,
    input  [7:0]                       num_rounds,
    output                             done,
    output                             busy,
    // Result interface
    output [WIDTH*NUM_CANDIDATES-1:0]  preimages,
    output [15:0]                      num_valid    // How many preimages are valid
);
    // Ball inverse computation would go here
    // For now, simplified: just run PRP inverse on candidate range [0, NUM_CANDIDATES)
    
    wire [WIDTH*NUM_CANDIDATES-1:0] candidates_in;
    
    // Generate initial candidates (ball_start + i for i in 0..NUM_CANDIDATES)
    genvar i;
    generate
        for (i = 0; i < NUM_CANDIDATES; i = i + 1) begin : gen_candidates
            assign candidates_in[i*WIDTH +: WIDTH] = i;  // Simplified
        end
    endgenerate
    
    prp_systolic_array #(
        .WIDTH(WIDTH),
        .NUM_LANES(NUM_CANDIDATES),
        .MAX_ROUNDS(128)
    ) prp_array (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
        .x_in(candidates_in),
        .domain(domain),
        .key(key),
        .num_rounds(num_rounds),
        .direction(1'b1),  // Inverse
        .done(done),
        .x_out(preimages),
        .busy(busy)
    );
    
    // Count valid (simplified - actual impl needs ball count from PMNS)
    assign num_valid = NUM_CANDIDATES;
endmodule
