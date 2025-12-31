// AES-128 Debug Testbench - check pipeline and key expansion
`timescale 1ns/1ps

module tb_aes128_debug;
    reg clk;
    reg rst_n;
    reg valid_in;
    reg [127:0] plaintext;
    reg [127:0] key;
    wire valid_out;
    wire [127:0] ciphertext;
    
    aes128_encrypt dut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .plaintext(plaintext),
        .key(key),
        .valid_out(valid_out),
        .ciphertext(ciphertext)
    );
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    integer cycle_count;
    
    initial begin
        $dumpfile("aes_debug.vcd");
        $dumpvars(0, tb_aes128_debug);
        
        rst_n = 0;
        valid_in = 0;
        plaintext = 128'h0;
        key = 128'h0;
        cycle_count = 0;
        
        #20;
        rst_n = 1;
        #10;
        
        // FIPS 197 test vector
        $display("Input plaintext: 3243f6a8885a308d313198a2e0370734");
        $display("Input key:       2b7e151628aed2a6abf7158809cf4f3c");
        plaintext = 128'h3243f6a8885a308d313198a2e0370734;
        key = 128'h2b7e151628aed2a6abf7158809cf4f3c;
        
        // Set valid_in before clock edge
        @(negedge clk);
        valid_in = 1;
        @(posedge clk);  // This edge captures valid_in=1
        cycle_count = 0;
        @(negedge clk);
        valid_in = 0;
        
        // Monitor output for 20 cycles
        repeat(20) begin
            @(posedge clk);
            cycle_count = cycle_count + 1;
            $display("Cycle %2d: valid_out=%b, ciphertext=%h", 
                     cycle_count, valid_out, ciphertext);
            if (valid_out) begin
                $display("  -> Valid output detected at cycle %d", cycle_count);
            end
        end
        
        $display("\n--- Check pipeline state ---");
        $display("valid_reg = %b", dut.valid_reg);
        
        $finish;
    end
endmodule
