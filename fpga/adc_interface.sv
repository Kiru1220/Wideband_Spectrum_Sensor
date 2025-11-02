// Wideband Spectrum Sensor - ADC Interface Module
// 12-bit ADC sampling at 100 MS/s
// Data acquisition and buffering for FFT processing

module adc_interface #(
    parameter ADC_WIDTH = 12,
    parameter FIFO_DEPTH = 1024,
    parameter CLK_FREQ_MHZ = 100
)(
    input  logic                      clk_adc,      // ADC clock (100 MHz)
    input  logic                      clk_sys,      // System clock (50 MHz)
    input  logic                      rst_n,
    input  logic [ADC_WIDTH-1:0]      adc_data,     // 12-bit ADC output
    input  logic                      adc_valid,    // Data valid strobe
    output logic [ADC_WIDTH-1:0]      sample_out,   // Sample output to FFT
    output logic                      sample_valid, // Sample valid flag
    output logic                      fifo_full,    // FIFO full indicator
    output logic                      fifo_empty,   // FIFO empty indicator
    input  logic                      read_enable   // Read request from FFT engine
);

    // Asynchronous FIFO for clock domain crossing
    logic [ADC_WIDTH-1:0] fifo_mem [0:FIFO_DEPTH-1];
    logic [$clog2(FIFO_DEPTH):0] write_ptr_gray, read_ptr_gray;
    logic [$clog2(FIFO_DEPTH):0] write_ptr_gray_sync, read_ptr_gray_sync;
    logic [$clog2(FIFO_DEPTH):0] write_ptr, read_ptr;
    
    logic write_ptr_gray_sync1, write_ptr_gray_sync2;
    logic read_ptr_gray_sync1, read_ptr_gray_sync2;

    // Gray code converters
    function logic [$clog2(FIFO_DEPTH):0] bin_to_gray(logic [$clog2(FIFO_DEPTH):0] bin);
        return bin ^ (bin >> 1);
    endfunction

    function logic [$clog2(FIFO_DEPTH):0] gray_to_bin(logic [$clog2(FIFO_DEPTH):0] gray);
        logic [$clog2(FIFO_DEPTH):0] bin;
        for (int i = 0; i < $clog2(FIFO_DEPTH)+1; i++) begin
            bin[i] = |(gray >> i);
        end
        return bin;
    endfunction

    // Write domain (ADC clock)
    always_ff @(posedge clk_adc or negedge rst_n) begin
        if (!rst_n) begin
            write_ptr <= '0;
            write_ptr_gray <= '0;
        end else if (adc_valid && !fifo_full) begin
            fifo_mem[write_ptr[$clog2(FIFO_DEPTH)-1:0]] <= adc_data;
            write_ptr <= write_ptr + 1'b1;
            write_ptr_gray <= bin_to_gray(write_ptr + 1'b1);
        end
    end

    // Clock domain crossing - synchronize read pointer to write domain
    always_ff @(posedge clk_adc or negedge rst_n) begin
        if (!rst_n) begin
            read_ptr_gray_sync1 <= '0;
            read_ptr_gray_sync2 <= '0;
        end else begin
            read_ptr_gray_sync1 <= read_ptr_gray;
            read_ptr_gray_sync2 <= read_ptr_gray_sync1;
        end
    end

    // FIFO full detection (write domain)
    logic [$clog2(FIFO_DEPTH):0] write_ptr_next;
    assign write_ptr_next = write_ptr + 1'b1;
    assign fifo_full = (bin_to_gray(write_ptr_next) == read_ptr_gray_sync2);

    // Read domain (System clock)
    always_ff @(posedge clk_sys or negedge rst_n) begin
        if (!rst_n) begin
            read_ptr <= '0;
            read_ptr_gray <= '0;
        end else if (read_enable && !fifo_empty) begin
            read_ptr <= read_ptr + 1'b1;
            read_ptr_gray <= bin_to_gray(read_ptr + 1'b1);
        end
    end

    // Clock domain crossing - synchronize write pointer to read domain
    always_ff @(posedge clk_sys or negedge rst_n) begin
        if (!rst_n) begin
            write_ptr_gray_sync1 <= '0;
            write_ptr_gray_sync2 <= '0;
        end else begin
            write_ptr_gray_sync1 <= write_ptr_gray;
            write_ptr_gray_sync2 <= write_ptr_gray_sync1;
        end
    end

    // FIFO empty detection (read domain)
    assign fifo_empty = (read_ptr_gray == write_ptr_gray_sync2);

    // Sample output multiplexer
    assign sample_out = fifo_mem[read_ptr[$clog2(FIFO_DEPTH)-1:0]];
    assign sample_valid = !fifo_empty && read_enable;

    // Debug and Status Signals
    logic [$clog2(FIFO_DEPTH):0] fifo_occupancy;
    assign fifo_occupancy = write_ptr - read_ptr;

    // Assertions for debugging
    // assert property (@(posedge clk_adc) disable iff (!rst_n) 
    //    !(adc_valid && fifo_full)) else $error("Writing to full FIFO!");

endmodule
