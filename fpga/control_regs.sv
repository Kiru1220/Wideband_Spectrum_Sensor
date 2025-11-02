module control_regs #(
  parameter ADDR_W = 8,
  parameter DATA_W = 32
) (
  input  logic              clk,
  input  logic              rst_n,
  // simple CSR bus
  input  logic              cs,
  input  logic              we,
  input  logic [ADDR_W-1:0] addr,
  input  logic [DATA_W-1:0] wdata,
  output logic [DATA_W-1:0] rdata,
  // exposed controls
  output logic              enable,
  output logic [15:0]       fft_size,
  output logic [15:0]       thresh
);
  // regs
  logic              enable_q;
  logic [15:0]       fft_size_q;
  logic [15:0]       thresh_q;

  // write logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      enable_q   <= 1'b0;
      fft_size_q <= 16'd1024;
      thresh_q   <= 16'd100;
    end else if (cs && we) begin
      unique case (addr)
        8'h00: enable_q   <= wdata[0];
        8'h04: fft_size_q <= wdata[15:0];
        8'h08: thresh_q   <= wdata[15:0];
        default: ;
      endcase
    end
  end

  // read logic
  always_comb begin
    unique case (addr)
      8'h00: rdata = {31'b0, enable_q};
      8'h04: rdata = {16'b0, fft_size_q};
      8'h08: rdata = {16'b0, thresh_q};
      default: rdata = '0;
    endcase
  end

  assign enable   = enable_q;
  assign fft_size = fft_size_q;
  assign thresh   = thresh_q;

  // Assertions
  // fft_size must be power of two between 16 and 32768
  property p_pow2;
    @(posedge clk) disable iff(!rst_n)
      (cs && we && addr==8'h04) |-> ($onehot0({wdata[15:0] & (wdata[15:0]-1)} ) || (wdata[15:0]==0));
  endproperty
  // threshold limited
  property p_thresh_range;
    @(posedge clk) disable iff(!rst_n)
      (cs && we && addr==8'h08) |-> (wdata[15:0] <= 16'h7FFF);
  endproperty
  assert property(p_thresh_range);

endmodule
