# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [VarUInt Encoding](#varuint-encoding)
    - [VarUInt Decoding](#varuint-decoding)

## Benchmark Results

### VarUInt Encoding

|         | `Ion v1.0`               | `Ion v1.1`                      | `Ion v1.1 Alt`                   |
|:--------|:-------------------------|:--------------------------------|:-------------------------------- |
| **`1`** | `48.11 us` (✅ **1.00x**) | `11.91 us` (🚀 **4.04x faster**) | `17.94 us` (🚀 **2.68x faster**)  |
| **`2`** | `48.40 us` (✅ **1.00x**) | `43.46 us` (✅ **1.11x faster**) | `46.45 us` (✅ **1.04x faster**)  |
| **`3`** | `53.12 us` (✅ **1.00x**) | `52.75 us` (✅ **1.01x faster**) | `53.53 us` (✅ **1.01x slower**)  |
| **`4`** | `55.94 us` (✅ **1.00x**) | `50.88 us` (✅ **1.10x faster**) | `52.52 us` (✅ **1.06x faster**)  |
| **`5`** | `60.86 us` (✅ **1.00x**) | `52.33 us` (✅ **1.16x faster**) | `54.78 us` (✅ **1.11x faster**)  |
| **`6`** | `66.50 us` (✅ **1.00x**) | `54.35 us` (✅ **1.22x faster**) | `56.78 us` (✅ **1.17x faster**)  |
| **`7`** | `44.44 us` (✅ **1.00x**) | `28.96 us` (✅ **1.53x faster**) | `32.03 us` (✅ **1.39x faster**)  |
| **`8`** | `74.45 us` (✅ **1.00x**) | `33.59 us` (🚀 **2.22x faster**) | `41.87 us` (✅ **1.78x faster**)  |

### VarUInt Decoding

|         | `Ion v1.0`                | `Ion v1.1`                      | `Ion v1.1 Alt`                   |
|:--------|:--------------------------|:--------------------------------|:-------------------------------- |
| **`1`** | `40.38 us` (✅ **1.00x**)  | `32.92 us` (✅ **1.23x faster**) | `30.00 us` (✅ **1.35x faster**)  |
| **`2`** | `38.26 us` (✅ **1.00x**)  | `32.87 us` (✅ **1.16x faster**) | `29.79 us` (✅ **1.28x faster**)  |
| **`3`** | `42.22 us` (✅ **1.00x**)  | `33.27 us` (✅ **1.27x faster**) | `31.13 us` (✅ **1.36x faster**)  |
| **`4`** | `46.02 us` (✅ **1.00x**)  | `33.07 us` (✅ **1.39x faster**) | `30.09 us` (✅ **1.53x faster**)  |
| **`5`** | `52.83 us` (✅ **1.00x**)  | `33.26 us` (✅ **1.59x faster**) | `30.35 us` (✅ **1.74x faster**)  |
| **`6`** | `59.02 us` (✅ **1.00x**)  | `33.52 us` (✅ **1.76x faster**) | `30.67 us` (🚀 **1.92x faster**)  |
| **`7`** | `66.10 us` (✅ **1.00x**)  | `33.43 us` (🚀 **1.98x faster**) | `30.62 us` (🚀 **2.16x faster**)  |
| **`8`** | `106.53 us` (✅ **1.00x**) | `39.40 us` (🚀 **2.70x faster**) | `36.10 us` (🚀 **2.95x faster**)  |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

