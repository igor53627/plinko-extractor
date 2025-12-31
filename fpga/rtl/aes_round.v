// AES-128 Single Round (combinational)
// Implements SubBytes, ShiftRows, MixColumns, AddRoundKey
module aes_round (
    input  [127:0] state_in,
    input  [127:0] round_key,
    input          is_last_round,
    output [127:0] state_out
);
    wire [127:0] after_subbytes;
    wire [127:0] after_shiftrows;
    wire [127:0] after_mixcolumns;
    
    // SubBytes - 16 parallel S-Box lookups
    genvar i;
    generate
        for (i = 0; i < 16; i = i + 1) begin : sbox_gen
            aes_sbox sbox_inst (
                .in(state_in[i*8 +: 8]),
                .out(after_subbytes[i*8 +: 8])
            );
        end
    endgenerate
    
    // ShiftRows
    // Row 0: no shift
    // Row 1: shift left by 1
    // Row 2: shift left by 2
    // Row 3: shift left by 3
    // State layout: [s0,s4,s8,s12; s1,s5,s9,s13; s2,s6,s10,s14; s3,s7,s11,s15]
    assign after_shiftrows[0*8 +: 8]  = after_subbytes[0*8 +: 8];   // s0
    assign after_shiftrows[4*8 +: 8]  = after_subbytes[4*8 +: 8];   // s4
    assign after_shiftrows[8*8 +: 8]  = after_subbytes[8*8 +: 8];   // s8
    assign after_shiftrows[12*8 +: 8] = after_subbytes[12*8 +: 8];  // s12
    
    assign after_shiftrows[1*8 +: 8]  = after_subbytes[5*8 +: 8];   // s5 -> pos 1
    assign after_shiftrows[5*8 +: 8]  = after_subbytes[9*8 +: 8];   // s9 -> pos 5
    assign after_shiftrows[9*8 +: 8]  = after_subbytes[13*8 +: 8];  // s13 -> pos 9
    assign after_shiftrows[13*8 +: 8] = after_subbytes[1*8 +: 8];   // s1 -> pos 13
    
    assign after_shiftrows[2*8 +: 8]  = after_subbytes[10*8 +: 8];  // s10 -> pos 2
    assign after_shiftrows[6*8 +: 8]  = after_subbytes[14*8 +: 8];  // s14 -> pos 6
    assign after_shiftrows[10*8 +: 8] = after_subbytes[2*8 +: 8];   // s2 -> pos 10
    assign after_shiftrows[14*8 +: 8] = after_subbytes[6*8 +: 8];   // s6 -> pos 14
    
    assign after_shiftrows[3*8 +: 8]  = after_subbytes[15*8 +: 8];  // s15 -> pos 3
    assign after_shiftrows[7*8 +: 8]  = after_subbytes[3*8 +: 8];   // s3 -> pos 7
    assign after_shiftrows[11*8 +: 8] = after_subbytes[7*8 +: 8];   // s7 -> pos 11
    assign after_shiftrows[15*8 +: 8] = after_subbytes[11*8 +: 8];  // s11 -> pos 15
    
    // MixColumns (skip on last round)
    genvar col;
    generate
        for (col = 0; col < 4; col = col + 1) begin : mixcol_gen
            wire [7:0] s0 = after_shiftrows[(col*4+0)*8 +: 8];
            wire [7:0] s1 = after_shiftrows[(col*4+1)*8 +: 8];
            wire [7:0] s2 = after_shiftrows[(col*4+2)*8 +: 8];
            wire [7:0] s3 = after_shiftrows[(col*4+3)*8 +: 8];
            
            // xtime(x) = (x << 1) ^ (0x1b if x[7] else 0)
            wire [7:0] s0x2 = {s0[6:0], 1'b0} ^ (s0[7] ? 8'h1b : 8'h00);
            wire [7:0] s1x2 = {s1[6:0], 1'b0} ^ (s1[7] ? 8'h1b : 8'h00);
            wire [7:0] s2x2 = {s2[6:0], 1'b0} ^ (s2[7] ? 8'h1b : 8'h00);
            wire [7:0] s3x2 = {s3[6:0], 1'b0} ^ (s3[7] ? 8'h1b : 8'h00);
            
            // MixColumns matrix multiplication
            wire [7:0] r0 = s0x2 ^ s1x2 ^ s1 ^ s2 ^ s3;
            wire [7:0] r1 = s0 ^ s1x2 ^ s2x2 ^ s2 ^ s3;
            wire [7:0] r2 = s0 ^ s1 ^ s2x2 ^ s3x2 ^ s3;
            wire [7:0] r3 = s0x2 ^ s0 ^ s1 ^ s2 ^ s3x2;
            
            assign after_mixcolumns[(col*4+0)*8 +: 8] = r0;
            assign after_mixcolumns[(col*4+1)*8 +: 8] = r1;
            assign after_mixcolumns[(col*4+2)*8 +: 8] = r2;
            assign after_mixcolumns[(col*4+3)*8 +: 8] = r3;
        end
    endgenerate
    
    // Select MixColumns or skip (last round)
    wire [127:0] before_addroundkey = is_last_round ? after_shiftrows : after_mixcolumns;
    
    // AddRoundKey
    assign state_out = before_addroundkey ^ round_key;
endmodule
