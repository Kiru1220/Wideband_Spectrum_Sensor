# Wideband Spectrum Sensor for Cognitive Radio Networks

Parameterized RTL modules in SystemVerilog for real-time wideband spectrum sensing, developed as a PG Diploma project (IIIT Bangalore / FutureWiz Academy).

## Overview

This project implements a wideband spectrum sensing pipeline for cognitive radio applications, built around multicoset (sub-Nyquist) sampling and the MUSIC algorithm for spectral peak identification. The goal was to detect signals across a wide frequency range while sampling well below the Nyquist rate, reducing hardware resource requirements compared to a conventional Nyquist-rate approach.

## Key Features

- **Multicoset sampling**: Sub-Nyquist compressive sampling front-end to reduce ADC/resource requirements
- **MUSIC algorithm**: Eigen-decomposition-based spectral peak identification for wideband signal detection
- **FFT-based processing**: Used alongside compressive sampling for spectral analysis
- **Target bandwidth**: 2 GHz wideband coverage

## Results

| Metric | Result |
|---|---|
| Bandwidth covered | 2 GHz |
| Resource reduction vs. Nyquist sampling | 40% |
| Detection accuracy | >90% |
| Processing throughput | 200 MSPS |

These figures come from simulation and synthesis reports generated for this project, validating the area-power-performance tradeoffs of the multicoset/MUSIC approach against a conventional Nyquist-rate baseline.

## Repository Structure

```
.
├── fpga/            # SystemVerilog RTL: compressive sampling, FFT processing,
│                    # eigen decomposition, spectral peak detection modules
└── README.md
```

## Design Approach

1. **Compressive (multicoset) sampling** — reduces the number of physical sampling channels needed to reconstruct a wideband signal, versus sampling at the full Nyquist rate for the entire 2 GHz span.
2. **FFT-based processing** — used for initial spectral analysis of the sub-sampled data.
3. **Eigen decomposition + MUSIC** — applied to the covariance structure of the sampled data to identify spectral peaks with high resolution, even under compressive sampling.

## Verification

Functionality was verified through simulation against known test signals, with synthesis reports generated to validate area, power, and performance tradeoffs of the compressive-sampling approach relative to full Nyquist-rate sampling.

## Tools Used

- SystemVerilog (RTL)
- ModelSim / QuestaSim (simulation)
- EDA Playground

## Status

Academic project (PG Diploma, 2025). RTL modules for compressive sampling, FFT processing, eigen decomposition, and peak detection are included; simulation/synthesis reports referenced above were generated during the project and are available on request.

## Author

Usha Kiran H N — ushakiru20@gmail.com

## License

MIT
