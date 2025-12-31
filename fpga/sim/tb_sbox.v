// S-Box verification
`timescale 1ns/1ps

module tb_sbox;
    reg [7:0] in;
    wire [7:0] out;
    
    aes_sbox dut (.in(in), .out(out));
    
    initial begin
        // Test known values from FIPS 197
        in = 8'h00; #1;
        if (out != 8'h63) $display("[FAIL] S[00] = %h, expected 63", out);
        else $display("[PASS] S[00] = 63");
        
        in = 8'h53; #1;
        if (out != 8'hed) $display("[FAIL] S[53] = %h, expected ed", out);
        else $display("[PASS] S[53] = ed");
        
        in = 8'hff; #1;
        if (out != 8'h16) $display("[FAIL] S[ff] = %h, expected 16", out);
        else $display("[PASS] S[ff] = 16");
        
        // From FIPS test: first byte of plaintext XOR first byte of key
        // 32 XOR 2b = 19
        in = 8'h19; #1;
        if (out != 8'hd4) $display("[FAIL] S[19] = %h, expected d4", out);
        else $display("[PASS] S[19] = d4");
        
        $finish;
    end
endmodule
