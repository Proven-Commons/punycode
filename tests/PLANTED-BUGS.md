# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Punycode/Basic.lean`, tested with `tests/run_tests.py --count 2000`. Every bug must give failures, and the unchanged code none. A run that gives up, because the code did not build or an oracle could not be run, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| tmin is 2, not 1 | 24287 |
| bias adaptation ignores the first delta | 16400 |
| the digits 0 to 9 are worth one less | 20030 |
| a delimiter with nothing before it is read as one | 1292 |
| surrogates are decoded | 254 |
| code points past U+10FFFF are let through the limit | 79 |
| code points outside ASCII are let into the literal portion | 5960 |
| equal code points are inserted from the first occurrence | 1932 |
| a delta counts one state change too few | 11046 |
| the encoder adapts the bias with one code point too few | 5886 |

Bugs caught: 10 of 10
