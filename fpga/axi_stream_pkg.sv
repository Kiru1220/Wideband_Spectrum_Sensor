package axi_stream_pkg;
  // Simple AXI-Stream like interface typedefs and helpers
  typedef struct packed {
    logic        tvalid;
    logic        tready;
    logic [31:0] tdata;
    logic [3:0]  tkeep;
    logic        tlast;
  } axis32_t;

  // Inline assertions for handshake correctness
  `define AXIS_ASSERT_HANDSHAKE(clk, rst_n, tv, tr) \
    assert property (@(posedge clk) disable iff (!rst_n) !(tv && !tr) throughout ##1 (tv && tr))

  // Helper function: byte enable width from data width
  function automatic int keep_width(input int data_width);
    keep_width = (data_width+7)/8;
  endfunction
endpackage: axi_stream_pkg
