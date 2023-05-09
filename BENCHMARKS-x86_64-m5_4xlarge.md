# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `99.20 us` (✅ **1.00x**)  | `38.59 us` (🚀 **2.57x faster**)  |
| **`2`** | `89.22 us` (✅ **1.00x**)  | `70.74 us` (✅ **1.26x faster**)  |
| **`3`** | `77.14 us` (✅ **1.00x**)  | `81.99 us` (✅ **1.06x slower**)  |
| **`4`** | `75.63 us` (✅ **1.00x**)  | `69.73 us` (✅ **1.08x faster**)  |
| **`5`** | `85.85 us` (✅ **1.00x**)  | `69.59 us` (✅ **1.23x faster**)  |
| **`6`** | `88.83 us` (✅ **1.00x**)  | `69.51 us` (✅ **1.28x faster**)  |
| **`7`** | `93.31 us` (✅ **1.00x**)  | `71.38 us` (✅ **1.31x faster**)  |
| **`8`** | `126.40 us` (✅ **1.00x**) | `67.85 us` (🚀 **1.86x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `88.09 us` (✅ **1.00x**)  | `49.00 us` (✅ **1.80x faster**)  |
| **`2`** | `92.01 us` (✅ **1.00x**)  | `49.14 us` (🚀 **1.87x faster**)  |
| **`3`** | `97.72 us` (✅ **1.00x**)  | `49.01 us` (🚀 **1.99x faster**)  |
| **`4`** | `105.01 us` (✅ **1.00x**) | `49.02 us` (🚀 **2.14x faster**)  |
| **`5`** | `117.58 us` (✅ **1.00x**) | `49.00 us` (🚀 **2.40x faster**)  |
| **`6`** | `131.88 us` (✅ **1.00x**) | `49.00 us` (🚀 **2.69x faster**)  |
| **`7`** | `146.19 us` (✅ **1.00x**) | `48.97 us` (🚀 **2.99x faster**)  |
| **`8`** | `213.57 us` (✅ **1.00x**) | `73.83 us` (🚀 **2.89x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

