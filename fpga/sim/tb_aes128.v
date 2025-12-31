// AES-128 Testbench
// Verifies against FIPS 197 test vector
`timescale 1ns/1ps

module tb_aes128;
    reg clk;
    reg rst_n;
    reg valid_in;
    reg [127:0] plaintext;
    reg [127:0] key;
    wire valid_out;
    wire [127:0] ciphertext;
    
    // Instantiate DUT
    aes128_encrypt dut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .plaintext(plaintext),
        .key(key),
        .valid_out(valid_out),
        .ciphertext(ciphertext)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz
    end
    
    // Test sequence
    initial begin
        $dumpfile("aes128.vcd");
        $dumpvars(0, tb_aes128);
        
        rst_n = 0;
        valid_in = 0;
        plaintext = 128'h0;
        key = 128'h0;
        
        #20;
        rst_n = 1;
        #10;
        
        // FIPS 197 Appendix B test vector
        plaintext = 128'h3243f6a8885a308d313198a2e0370734;
        key = 128'h2b7e151628aed2a6abf7158809cf4f3c;
        valid_in = 1;
        #10;
        valid_in = 0;
        
        // Wait for pipeline (11 stages + margin)
        @(posedge clk);  // Input registered
        repeat(12) @(posedge clk);  // Pipeline depth
        
        // Wait for valid_out
        while (!valid_out) @(posedge clk);
        
        begin
            // Expected: 3925841d02dc09fbdc118597196a0b32
            if (ciphertext == 128'h3925841d02dc09fbdc118597196a0b32) begin
                $display("[PASS] AES-128 FIPS test vector matches");
                $display("  Ciphertext: %h", ciphertext);
            end else begin
                $display("[FAIL] AES-128 mismatch");
                $display("  Expected: 3925841d02dc09fbdc118597196a0b32");
                $display("  Got:      %h", ciphertext);
            end
        end
        
        // Additional test: all zeros
        #10;
        plaintext = 128'h00000000000000000000000000000000;
        key = 128'h00000000000000000000000000000000;
        valid_in = 1;
        #10;
        valid_in = 0;
        
        // Wait for valid output
        while (!valid_out) @(posedge clk);
        
        begin
            // Expected: 66e94bd4ef8a2c3b884cfa59ca342b2e
            if (ciphertext == 128'h66e94bd4ef8a2c3b884cfa59ca342b2e) begin
                $display("[PASS] AES-128 all-zeros test vector matches");
            end else begin
                $display("[FAIL] AES-128 all-zeros mismatch");
                $display("  Expected: 66e94bd4ef8a2c3b884cfa59ca342b2e");
                $display("  Got:      %h", ciphertext);
            end
        end
        
        // Throughput test: stream 100 blocks
        $display("\n--- Throughput Test ---");
        repeat(5) @(posedge clk);
        
        fork
            // Producer: inject 100 blocks
            begin : producer
                integer i;
                for (i = 0; i < 100; i = i + 1) begin
                    plaintext = i;
                    valid_in = 1;
                    @(posedge clk);
                end
                valid_in = 0;
            end
            
            // Consumer: count valid outputs
            begin : consumer
                integer count;
                count = 0;
                repeat(120) begin
                    @(posedge clk);
                    if (valid_out) count = count + 1;
                end
                $display("  Received %0d valid outputs (expected ~100)", count);
            end
        join
        
        $display("\n--- Simulation Complete ---");
        #100;
        $finish;
    end
endmodule
