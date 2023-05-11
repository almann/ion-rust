# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `94.36 us` (✅ **1.00x**)  | `40.47 us` (🚀 **2.33x faster**)  |
| **`2`** | `85.14 us` (✅ **1.00x**)  | `73.24 us` (✅ **1.16x faster**)  |
| **`3`** | `82.37 us` (✅ **1.00x**)  | `71.49 us` (✅ **1.15x faster**)  |
| **`4`** | `84.15 us` (✅ **1.00x**)  | `60.26 us` (✅ **1.40x faster**)  |
| **`5`** | `90.31 us` (✅ **1.00x**)  | `60.52 us` (✅ **1.49x faster**)  |
| **`6`** | `93.23 us` (✅ **1.00x**)  | `60.72 us` (✅ **1.54x faster**)  |
| **`7`** | `88.79 us` (✅ **1.00x**)  | `56.77 us` (✅ **1.56x faster**)  |
| **`8`** | `125.43 us` (✅ **1.00x**) | `72.94 us` (✅ **1.72x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `79.30 us` (✅ **1.00x**)  | `40.40 us` (🚀 **1.96x faster**)  |
| **`2`** | `85.33 us` (✅ **1.00x**)  | `40.58 us` (🚀 **2.10x faster**)  |
| **`3`** | `96.55 us` (✅ **1.00x**)  | `40.30 us` (🚀 **2.40x faster**)  |
| **`4`** | `109.66 us` (✅ **1.00x**) | `40.37 us` (🚀 **2.72x faster**)  |
| **`5`** | `125.00 us` (✅ **1.00x**) | `40.44 us` (🚀 **3.09x faster**)  |
| **`6`** | `140.05 us` (✅ **1.00x**) | `40.58 us` (🚀 **3.45x faster**)  |
| **`7`** | `155.57 us` (✅ **1.00x**) | `40.60 us` (🚀 **3.83x faster**)  |
| **`8`** | `213.10 us` (✅ **1.00x**) | `69.74 us` (🚀 **3.06x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

