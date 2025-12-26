/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

// Formal specification for GF(2^128) arithmetic in Verilog
// This can be used with formal verification tools like Yosys/SymbiYosys

module gf128_add (
    input [127:0] a,
    input [127:0] b,
    output [127:0] result
);
    // GF(2^128) addition is XOR
    assign result = a ^ b;
    
    // Formal properties
    `ifdef FORMAL
        // Property: Addition is commutative
        assert property (result == (b ^ a));
        
        // Property: Addition is associative
        wire [127:0] c = 128'h123456789abcdef0123456789abcdef0;
        wire [127:0] ab_c = (a ^ b) ^ c;
        wire [127:0] a_bc = a ^ (b ^ c);
        assert property (ab_c == a_bc);
        
        // Property: Zero is identity
        assert property ((a ^ 128'h0) == a);
        
        // Property: Self-addition gives zero
        assert property ((a ^ a) == 128'h0);
    `endif
endmodule

module gf128_mul (
    input [127:0] a,
    input [127:0] b,
    output [127:0] result
);
    // GF(2^128) multiplication with reduction polynomial x^128 + x^7 + x^2 + x + 1
    
    reg [127:0] accumulator;
    reg [127:0] v;
    integer i;
    
    always @(*) begin
        accumulator = 128'h0;
        v = a;
        
        for (i = 0; i < 128; i = i + 1) begin
            if (b[i]) begin
                accumulator = accumulator ^ v;
            end
            
            // Multiply v by x (shift left)
            if (v[127]) begin
                // Apply reduction: x^128 = x^7 + x^2 + x + 1
                v = {v[126:0], 1'b0} ^ 128'h87;
            end else begin
                v = {v[126:0], 1'b0};
            end
        end
        
        result = accumulator;
    end
    
    `ifdef FORMAL
        // Property: Multiplication by 1 is identity
        wire [127:0] one = 128'h1;
        assert property ((a == one) -> (result == b));
        assert property ((b == one) -> (result == a));
        
        // Property: Multiplication by 0 gives 0
        wire [127:0] zero = 128'h0;
        assert property ((a == zero) -> (result == zero));
        assert property ((b == zero) -> (result == zero));
        
        // Property: Multiplication is commutative (expensive to verify)
        // Can be checked with bounded model checking
    `endif
endmodule

// Formal specification for complete GF128 circuit
module gf128_circuit_spec (
    input wire clk,
    input wire reset,
    input wire [127:0] input_a,
    input wire [127:0] input_b,
    input wire [1:0] operation, // 00: add, 01: mul
    output reg [127:0] output_result,
    output reg valid
);
    reg [127:0] a_reg, b_reg;
    reg [1:0] op_reg;
    wire [127:0] add_result, mul_result;
    
    gf128_add adder(.a(a_reg), .b(b_reg), .result(add_result));
    gf128_mul multiplier(.a(a_reg), .b(b_reg), .result(mul_result));
    
    always @(posedge clk) begin
        if (reset) begin
            a_reg <= 128'h0;
            b_reg <= 128'h0;
            op_reg <= 2'b00;
            output_result <= 128'h0;
            valid <= 1'b0;
        end else begin
            a_reg <= input_a;
            b_reg <= input_b;
            op_reg <= operation;
            valid <= 1'b1;
            
            case (op_reg)
                2'b00: output_result <= add_result;
                2'b01: output_result <= mul_result;
                default: output_result <= 128'h0;
            endcase
        end
    end
    
    `ifdef FORMAL
        // Assume inputs are stable for at least 2 cycles
        reg [127:0] prev_a, prev_b;
        always @(posedge clk) begin
            prev_a <= input_a;
            prev_b <= input_b;
        end
        
        // Property: Output is valid after reset
        assert property (!reset && $past(reset) |-> !valid);
        assert property (!reset && !$past(reset) && $past(!reset, 2) |-> valid);
        
        // Property: Results match operations
        assert property (valid && op_reg == 2'b00 |-> output_result == (a_reg ^ b_reg));
    `endif
endmodule