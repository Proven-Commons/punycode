# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Punycode/Basic.lean`, tested with `tests/run_tests.py --count 2000`. Every bug must give failures, and the unchanged code none.

| Planted bug | Failures |
|---|---|
| none | 0 |
| tmin is 2, not 1 | 24274 |
| bias adaptation ignores the first delta | 16400 |
| the digits 0 to 9 are worth one less | 18236 |
| a delimiter with nothing before it is read as one | 1291 |
| surrogates are decoded | 246 |
| code points past U+10FFFF are let through the limit | 79 |
| code points outside ASCII are let into the literal portion | 5960 |
| equal code points are inserted from the first occurrence | 1610 |
| a delta counts one state change too few | 9201 |
| the encoder adapts the bias with one code point too few | 4905 |

Bugs caught: 10 of 10
