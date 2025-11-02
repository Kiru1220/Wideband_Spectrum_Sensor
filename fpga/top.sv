// top.sv - Top-level module connecting adc_interface, windowing, fft_engine, detector
// Provides AXI-like streaming valid/ready/last between stages.
// Includes SVAs for handshake and frame integrity.

`timescale 1ns/1ps

`include "axi_stream_pkg.sv"

module top #(
  parameter int DATA_W = 16,
  parameter int FFT_MAX_LOG2 = 12
)(
  input  logic                clk,
  input  logic                rst_n,
  // ADC pins
  input  logic [DATA_W-1:0]   adc_data,
  input  logic                adc_valid,
  // Control register interface (simple)
  input  logic [FFT_MAX_LOG2-1:0] cfg_fft_log2,
  input  logic                cfg_win_en,
  input  logic [31:0]         cfg_threshold,
  // Output stream
  output logic                det_valid,
  input  logic                det_ready,
  output logic                det_last,
  output logic [31:0]         det_data
);
  import axi_stream_pkg::*;

  // Stage channels
  axi_stream_ch #(.W(DATA_W))          ch_adc();
  axi_stream_ch #(.W(DATA_W))          ch_win();
  axi_stream_ch #(.W(2*DATA_W))        ch_fft();
  axi_stream_ch #(.W(32))              ch_det();

  // adc_interface converts discrete adc_valid/data to stream with frames of 2**cfg_fft_log2
  adc_interface #(
    .DATA_W(DATA_W)
  ) u_adc_if (
    .clk        (clk),
    .rst_n      (rst_n),
    .cfg_nfft_lg2(cfg_fft_log2),
    .adc_data   (adc_data),
    .adc_valid  (adc_valid),
    // stream out
    .m_valid    (ch_adc.valid),
    .m_ready    (ch_adc.ready),
    .m_last     (ch_adc.last),
    .m_data     (ch_adc.data)
  );

  // Windowing
  windowing #(
    .DATA_W(DATA_W)
  ) u_window (
    .clk        (clk),
    .rst_n      (rst_n),
    .cfg_enable (cfg_win_en),
    .s_valid    (ch_adc.valid),
    .s_ready    (ch_adc.ready),
    .s_last     (ch_adc.last),
    .s_data     (ch_adc.data),
    .m_valid    (ch_win.valid),
    .m_ready    (ch_win.ready),
    .m_last     (ch_win.last),
    .m_data     (ch_win.data)
  );

  // FFT engine
  fft_engine #(
    .DATA_W(DATA_W),
    .FFT_MAX_LOG2(FFT_MAX_LOG2)
  ) u_fft (
    .clk        (clk),
    .rst_n      (rst_n),
    .cfg_fft_log2(cfg_fft_log2),
    .s_valid    (ch_win.valid),
    .s_ready    (ch_win.ready),
    .s_last     (ch_win.last),
    .s_data     (ch_win.data),
    .m_valid    (ch_fft.valid),
    .m_ready    (ch_fft.ready),
    .m_last     (ch_fft.last),
    .m_data     (ch_fft.data)
  );

  // Detector (magnitude and threshold)
  detector u_det (
    .clk        (clk),
    .rst_n      (rst_n),
    .cfg_threshold(cfg_threshold),
    .s_valid    (ch_fft.valid),
    .s_ready    (ch_fft.ready),
    .s_last     (ch_fft.last),
    .s_data     (ch_fft.data),
    .m_valid    (ch_det.valid),
    .m_ready    (ch_det.ready),
    .m_last     (ch_det.last),
    .m_data     (ch_det.data)
  );

  // Output
  assign det_valid = ch_det.valid;
  assign ch_det.ready = det_ready;
  assign det_last  = ch_det.last;
  assign det_data  = ch_det.data;

  // Simple system-level SVAs
`ifdef ASSERT_ON
  // Valid must remain asserted until accepted
  a_hold_valid_adc:    assert property (@(posedge clk) disable iff (!rst_n) ch_adc.valid && !ch_adc.ready |-> ch_adc.valid);
  a_hold_valid_win:    assert property (@(posedge clk) disable iff (!rst_n) ch_win.valid && !ch_win.ready |-> ch_win.valid);
  a_hold_valid_fft:    assert property (@(posedge clk) disable iff (!rst_n) ch_fft.valid && !ch_fft.ready |-> ch_fft.valid);
  a_hold_valid_det:    assert property (@(posedge clk) disable iff (!rst_n) ch_det.valid && !ch_det.ready |-> ch_det.valid);

  // last must only assert on final beat of a frame, propagate from adc to output
  logic [FFT_MAX_LOG2:0] beat_cnt;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) beat_cnt <= '0; else if (ch_adc.valid && ch_adc.ready) begin
      beat_cnt <= ch_adc.last ? '0 : beat_cnt + 1'b1;
    end
  end
  a_last_when_end: assert property (@(posedge clk) disable iff(!rst_n)
      ch_adc.valid && ch_adc.ready && ch_adc.last |-> beat_cnt==0);
`endif

endmodule
