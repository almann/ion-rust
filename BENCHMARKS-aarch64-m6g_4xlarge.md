# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `104.85 us` (✅ **1.00x**) | `37.84 us` (🚀 **2.77x faster**)  |
| **`2`** | `87.05 us` (✅ **1.00x**)  | `79.86 us` (✅ **1.09x faster**)  |
| **`3`** | `84.71 us` (✅ **1.00x**)  | `81.84 us` (✅ **1.04x faster**)  |
| **`4`** | `87.42 us` (✅ **1.00x**)  | `68.21 us` (✅ **1.28x faster**)  |
| **`5`** | `86.39 us` (✅ **1.00x**)  | `68.17 us` (✅ **1.27x faster**)  |
| **`6`** | `89.21 us` (✅ **1.00x**)  | `68.16 us` (✅ **1.31x faster**)  |
| **`7`** | `92.73 us` (✅ **1.00x**)  | `65.22 us` (✅ **1.42x faster**)  |
| **`8`** | `129.22 us` (✅ **1.00x**) | `65.77 us` (🚀 **1.96x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `82.49 us` (✅ **1.00x**)  | `46.79 us` (✅ **1.76x faster**)  |
| **`2`** | `88.13 us` (✅ **1.00x**)  | `46.85 us` (🚀 **1.88x faster**)  |
| **`3`** | `99.07 us` (✅ **1.00x**)  | `46.68 us` (🚀 **2.12x faster**)  |
| **`4`** | `112.56 us` (✅ **1.00x**) | `46.73 us` (🚀 **2.41x faster**)  |
| **`5`** | `127.28 us` (✅ **1.00x**) | `46.81 us` (🚀 **2.72x faster**)  |
| **`6`** | `142.77 us` (✅ **1.00x**) | `46.93 us` (🚀 **3.04x faster**)  |
| **`7`** | `158.11 us` (✅ **1.00x**) | `46.78 us` (🚀 **3.38x faster**)  |
| **`8`** | `215.31 us` (✅ **1.00x**) | `70.19 us` (🚀 **3.07x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

