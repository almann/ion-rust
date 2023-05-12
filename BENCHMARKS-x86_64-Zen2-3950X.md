# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`               | `Ion v1.1`                       |
|:--------|:-------------------------|:-------------------------------- |
| **`1`** | `59.46 us` (✅ **1.00x**) | `17.80 us` (🚀 **3.34x faster**)  |
| **`2`** | `63.91 us` (✅ **1.00x**) | `43.98 us` (✅ **1.45x faster**)  |
| **`3`** | `62.79 us` (✅ **1.00x**) | `46.95 us` (✅ **1.34x faster**)  |
| **`4`** | `64.62 us` (✅ **1.00x**) | `36.37 us` (✅ **1.78x faster**)  |
| **`5`** | `66.51 us` (✅ **1.00x**) | `37.47 us` (✅ **1.77x faster**)  |
| **`6`** | `66.05 us` (✅ **1.00x**) | `37.05 us` (✅ **1.78x faster**)  |
| **`7`** | `79.93 us` (✅ **1.00x**) | `36.47 us` (🚀 **2.19x faster**)  |
| **`8`** | `84.09 us` (✅ **1.00x**) | `44.94 us` (🚀 **1.87x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `46.61 us` (✅ **1.00x**)  | `32.79 us` (✅ **1.42x faster**)  |
| **`2`** | `53.59 us` (✅ **1.00x**)  | `32.56 us` (✅ **1.65x faster**)  |
| **`3`** | `61.32 us` (✅ **1.00x**)  | `33.47 us` (🚀 **1.83x faster**)  |
| **`4`** | `64.99 us` (✅ **1.00x**)  | `33.23 us` (🚀 **1.96x faster**)  |
| **`5`** | `75.23 us` (✅ **1.00x**)  | `33.62 us` (🚀 **2.24x faster**)  |
| **`6`** | `85.66 us` (✅ **1.00x**)  | `33.53 us` (🚀 **2.55x faster**)  |
| **`7`** | `95.64 us` (✅ **1.00x**)  | `32.75 us` (🚀 **2.92x faster**)  |
| **`8`** | `139.38 us` (✅ **1.00x**) | `42.77 us` (🚀 **3.26x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

