# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of RFC 3492, `model_encode` and `model_decode` in `tests/run_tests.py`, and the four implementations below
- RFC 3492: the sample implementation of appendix C, compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- Python: the `punycode` codec of Python 3.13.17
- Node: v22.22.0, punycode.js 2.1.0
- libidn2: 2.3.7
- Seed: 20261026
- Inputs: 319757
- By kind: edge decode 41, edge encode 11, grid decode 19608, long decode 20, long encode 20, mutated decode 100000, random decode 100000, random encode 100000, sample decode 38, sample encode 19
- Answers that differ from the model: 0
- Strings decoded: 219707, of which 161072 are Punycode strings and 58635 are not
- Texts encoded: 100050
- Inputs whose processing needs a number past 2**31 - 1: 107
- Agreement with each oracle over all inputs: RFC 3492 310259 of 319757, Python 308157 of 319757, Node 316950 of 319757, libidn2 244820 of 319757
- Malformed requests answered `error`: 12 of 12
- The tool's encodings decoded back by the tool: 100050 of 100050
- Command-line modes other than `serve` answered right: 8 of 8
- Requests ending in CR LF: every seventh, 45679
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms.

### RFC 3492

- the oracle returns a value that is not a scalar value, decoding: 9490
- the oracle's integers overflow at 4,294,967,296, encoding: 4
- the oracle's integers overflow at 4,294,967,296, decoding: 4

### Python

- Python reads a delimiter with nothing before it, decoding: 8813
- the oracle returns a value that is not a scalar value, decoding: 2787

### Node

- the oracle returns a value that is not a scalar value, decoding: 2776
- the oracle's integers overflow at 2,147,483,648, encoding: 12
- the oracle's integers overflow at 2,147,483,648, decoding: 12
- Node returns surrogates, which pair up in its UTF-16 string, decoding: 7

### libidn2

- libidn2 refuses basic code points other than letters, digits, - and _, decoding: 56667
- libidn2 refuses a string with no deltas, decoding: 17831
- the oracle returns a value that is not a scalar value, decoding: 409
- libidn2 reads _ in the deltas as the digit a, decoding: 22
- the oracle's integers overflow at 4,294,967,296, encoding: 4
- the oracle's integers overflow at 4,294,967,296, decoding: 4
