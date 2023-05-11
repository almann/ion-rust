# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`               | `Ion v1.1`                       |
|:--------|:-------------------------|:-------------------------------- |
| **`1`** | `47.28 us` (✅ **1.00x**) | `12.95 us` (🚀 **3.65x faster**)  |
| **`2`** | `48.37 us` (✅ **1.00x**) | `42.65 us` (✅ **1.13x faster**)  |
| **`3`** | `53.42 us` (✅ **1.00x**) | `50.65 us` (✅ **1.05x faster**)  |
| **`4`** | `55.95 us` (✅ **1.00x**) | `50.11 us` (✅ **1.12x faster**)  |
| **`5`** | `60.75 us` (✅ **1.00x**) | `51.60 us` (✅ **1.18x faster**)  |
| **`6`** | `66.08 us` (✅ **1.00x**) | `54.14 us` (✅ **1.22x faster**)  |
| **`7`** | `44.80 us` (✅ **1.00x**) | `30.50 us` (✅ **1.47x faster**)  |
| **`8`** | `74.83 us` (✅ **1.00x**) | `38.04 us` (🚀 **1.97x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `36.65 us` (✅ **1.00x**)  | `29.85 us` (✅ **1.23x faster**)  |
| **`2`** | `38.91 us` (✅ **1.00x**)  | `30.00 us` (✅ **1.30x faster**)  |
| **`3`** | `43.82 us` (✅ **1.00x**)  | `29.95 us` (✅ **1.46x faster**)  |
| **`4`** | `46.87 us` (✅ **1.00x**)  | `29.94 us` (✅ **1.57x faster**)  |
| **`5`** | `52.70 us` (✅ **1.00x**)  | `30.39 us` (✅ **1.73x faster**)  |
| **`6`** | `58.95 us` (✅ **1.00x**)  | `30.70 us` (🚀 **1.92x faster**)  |
| **`7`** | `66.12 us` (✅ **1.00x**)  | `30.61 us` (🚀 **2.16x faster**)  |
| **`8`** | `109.07 us` (✅ **1.00x**) | `34.71 us` (🚀 **3.14x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

