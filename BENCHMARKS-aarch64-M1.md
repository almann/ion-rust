# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`               | `Ion v1.1`                       |
|:--------|:-------------------------|:-------------------------------- |
| **`1`** | `47.08 us` (✅ **1.00x**) | `9.22 us` (🚀 **5.11x faster**)   |
| **`2`** | `48.31 us` (✅ **1.00x**) | `42.89 us` (✅ **1.13x faster**)  |
| **`3`** | `53.66 us` (✅ **1.00x**) | `54.35 us` (✅ **1.01x slower**)  |
| **`4`** | `55.86 us` (✅ **1.00x**) | `51.10 us` (✅ **1.09x faster**)  |
| **`5`** | `60.82 us` (✅ **1.00x**) | `52.33 us` (✅ **1.16x faster**)  |
| **`6`** | `66.08 us` (✅ **1.00x**) | `54.11 us` (✅ **1.22x faster**)  |
| **`7`** | `44.26 us` (✅ **1.00x**) | `28.96 us` (✅ **1.53x faster**)  |
| **`8`** | `74.35 us` (✅ **1.00x**) | `41.69 us` (✅ **1.78x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                       |
|:--------|:--------------------------|:-------------------------------- |
| **`1`** | `39.78 us` (✅ **1.00x**)  | `32.80 us` (✅ **1.21x faster**)  |
| **`2`** | `37.76 us` (✅ **1.00x**)  | `32.83 us` (✅ **1.15x faster**)  |
| **`3`** | `42.20 us` (✅ **1.00x**)  | `33.06 us` (✅ **1.28x faster**)  |
| **`4`** | `46.16 us` (✅ **1.00x**)  | `32.96 us` (✅ **1.40x faster**)  |
| **`5`** | `52.61 us` (✅ **1.00x**)  | `33.28 us` (✅ **1.58x faster**)  |
| **`6`** | `59.08 us` (✅ **1.00x**)  | `33.63 us` (✅ **1.76x faster**)  |
| **`7`** | `66.11 us` (✅ **1.00x**)  | `33.44 us` (🚀 **1.98x faster**)  |
| **`8`** | `106.99 us` (✅ **1.00x**) | `38.42 us` (🚀 **2.78x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

