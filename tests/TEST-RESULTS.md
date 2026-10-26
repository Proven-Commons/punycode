# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of RFC 3492, `model_encode` and `model_decode` in `tests/run_tests.py`, and the four implementations below
- RFC 3492: the sample implementation of appendix C, compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- Python: the `punycode` codec of Python 3.13.17
- Node: v22.22.0, punycode.js 2.1.0
- libidn2: 2.3.7
- Seed: 20261026
- Inputs: 25751
- By kind: edge decode 35, edge encode 11, grid decode 19608, long decode 20, long encode 20, mutated decode 2000, random decode 2000, random encode 2000, sample decode 38, sample encode 19
- Answers that differ from the model: 0
- Strings decoded: 23701, of which 5984 are Punycode strings and 17717 are not
- Texts encoded: 2050
- Inputs whose processing needs a number past 2**31 - 1: 26
- Agreement with each oracle over all inputs: RFC 3492 25520 of 25751, Python 25364 of 25751, Node 25671 of 25751, libidn2 22516 of 25751
- Malformed requests answered `error`: 12 of 12
- Requests ending in CR LF: every seventh, 3678
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms.

### RFC 3492

- the oracle returns a value that is not a scalar value, decoding: 223
- the oracle's integers overflow at 4,294,967,296, encoding: 4
- the oracle's integers overflow at 4,294,967,296, decoding: 4

### Python

- Python reads a delimiter with nothing before it, decoding: 331
- the oracle returns a value that is not a scalar value, decoding: 56

### Node

- the oracle returns a value that is not a scalar value, decoding: 56
- the oracle's integers overflow at 2,147,483,648, encoding: 12
- the oracle's integers overflow at 2,147,483,648, decoding: 12

### libidn2

- libidn2 refuses a string with no deltas, decoding: 1908
- libidn2 refuses basic code points other than letters, digits, - and _, decoding: 1311
- the oracle returns a value that is not a scalar value, decoding: 8
- the oracle's integers overflow at 4,294,967,296, encoding: 4
- the oracle's integers overflow at 4,294,967,296, decoding: 4
