module detector #(
  parameter DATA_W = 32
) (
  input  logic              clk,
  input  logic              rst_n,
  // AXI-Stream in (magnitude or power)
  input  logic              s_tvalid,
  output logic              s_tready,
  input  logic [DATA_W-1:0] s_tdata,
  input  logic              s_tlast,
  // AXI-Stream out (flags)
  output logic              m_tvalid,
  input  logic              m_tready,
  output logic [7:0]        m_tdata, // bit0: threshold exceed, others reserved
  output logic              m_tlast,
  // control
  input  logic [15:0]       thresh
);
  // simple pass-through with compare
  assign s_tready = m_tready; // combinational backpressure

  logic exceed;
  assign exceed = (s_tdata[15:0] > thresh);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      m_tvalid <= 1'b0;
      m_tdata  <= '0;
      m_tlast  <= 1'b0;
    end else begin
      m_tvalid <= s_tvalid && s_tready;
      m_tdata  <= {7'b0, exceed};
      m_tlast  <= s_tlast && s_tvalid && s_tready;
    end
  end

  // Assertions
  // No data should be lost: when s_tvalid && s_tready, m_tvalid must be 1 next cycle or same
  property p_handshake_transfer;
    @(posedge clk) disable iff(!rst_n)
      (s_tvalid && s_tready) |-> (m_tvalid);
  endproperty
  assert property(p_handshake_transfer);

endmodule
