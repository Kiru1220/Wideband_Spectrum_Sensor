// windowing.sv
// Applies a window function (Hann/Hamming/Blackman) to input samples.
`timescale 1ns/1ps
module windowing #(
  parameter int N = 1024,
  parameter int DATA_W = 16,
  parameter int COEF_W = 16
) (
  input  logic                 clk,
  input  logic                 rst_n,
  // stream in
  input  logic                 s_valid,
  output logic                 s_ready,
  input  logic                 s_last,
  input  logic signed [DATA_W-1:0] s_data,
  // stream out
  output logic                 m_valid,
  input  logic                 m_ready,
  output logic                 m_last,
  output logic signed [DATA_W+COEF_W-1:0] m_data
);

  // Coefficient ROM (behavioral) - Hann as default: w[n]=0.5-0.5cos(2pi n/(N-1)) scaled to Q1.(COEF_W-1)
  logic [COEF_W-1:0] coef_rom [0:N-1];
  initial begin
    int i;
    for (i=0; i<N; i++) begin
      real w = 0.5 - 0.5*$cos(2.0*3.1415926535*i/(N-1));
      int v = integer'(w * (2**(COEF_W-1)-1));
      coef_rom[i] = v[COEF_W-1:0];
    end
  end

  // index and pipeline
  logic [$clog2(N)-1:0] idx;
  logic signed [DATA_W-1:0] s_q;
  logic [COEF_W-1:0]        c_q;
  logic                      v_q, last_q;

  assign s_ready = m_ready; // 1-stage backpressure

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      idx    <= '0;
      s_q    <= '0;
      c_q    <= '0;
      v_q    <= 1'b0;
      last_q <= 1'b0;
    end else if (s_ready) begin
      v_q    <= s_valid;
      s_q    <= s_data;
      c_q    <= coef_rom[idx];
      last_q <= s_last;
      if (s_valid) begin
        if (s_last) idx <= '0; else idx <= idx + 1'b1;
      end
    end
  end

  // Multiply
  logic signed [DATA_W+COEF_W-1:0] prod;
  assign prod = s_q * $signed({1'b0,c_q});

  assign m_valid = v_q;
  assign m_last  = last_q;
  assign m_data  = prod;

  // Assertions
  property p_valid_hold_in; @(posedge clk) disable iff(!rst_n) s_valid & ~s_ready |-> s_valid until_with s_ready; endproperty
  a_valid_hold_in: assert property(p_valid_hold_in);

  property p_valid_hold_out; @(posedge clk) disable iff(!rst_n) m_valid & ~m_ready |-> m_valid until_with m_ready; endproperty
  a_valid_hold_out: assert property(p_valid_hold_out);

  property p_last_only_with_valid; @(posedge clk) disable iff(!rst_n) s_last |-> s_valid; endproperty
  a_last_only_with_valid: assert property(p_last_only_with_valid);

endmodule
