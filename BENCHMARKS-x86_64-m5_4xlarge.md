# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `99.20 us` (✅ **1.00x**)  | `37.79 us` (🚀 **2.63x faster**)  |
| **`2`** | `89.39 us` (✅ **1.00x**)  | `62.60 us` (✅ **1.43x faster**)  |
| **`3`** | `76.96 us` (✅ **1.00x**)  | `59.30 us` (✅ **1.30x faster**)  |
| **`4`** | `75.76 us` (✅ **1.00x**)  | `42.57 us` (✅ **1.78x faster**)  |
| **`5`** | `85.85 us` (✅ **1.00x**)  | `42.45 us` (🚀 **2.02x faster**)  |
| **`6`** | `88.83 us` (✅ **1.00x**)  | `42.38 us` (🚀 **2.10x faster**)  |
| **`7`** | `93.32 us` (✅ **1.00x**)  | `37.40 us` (🚀 **2.50x faster**)  |
| **`8`** | `126.92 us` (✅ **1.00x**) | `76.71 us` (✅ **1.65x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `87.22 us` (✅ **1.00x**)  | `46.03 us` (🚀 **1.90x faster**)  |
| **`2`** | `89.47 us` (✅ **1.00x**)  | `45.85 us` (🚀 **1.95x faster**)  |
| **`3`** | `95.29 us` (✅ **1.00x**)  | `45.84 us` (🚀 **2.08x faster**)  |
| **`4`** | `105.02 us` (✅ **1.00x**) | `45.87 us` (🚀 **2.29x faster**)  |
| **`5`** | `117.51 us` (✅ **1.00x**) | `45.87 us` (🚀 **2.56x faster**)  |
| **`6`** | `130.70 us` (✅ **1.00x**) | `45.91 us` (🚀 **2.85x faster**)  |
| **`7`** | `146.24 us` (✅ **1.00x**) | `45.88 us` (🚀 **3.19x faster**)  |
| **`8`** | `212.42 us` (✅ **1.00x**) | `70.51 us` (🚀 **3.01x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

