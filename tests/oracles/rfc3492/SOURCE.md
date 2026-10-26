# Where `punycode.c` comes from

`punycode.c` is the library part of the sample implementation in
appendix C of RFC 3492 (https://www.rfc-editor.org/rfc/rfc3492.txt). It
runs from the opening comment `punycode.c from RFC 3492` to the line
before `Wrapper for testing`, with the RFC's page headers and footers
taken out and nothing else changed.

The RFC text it was taken from has SHA-256
`d1848b1b4f01e20708a64f42394e5f4b840141935bed7f09ad7baeb6693b8772`.

Appendix B of RFC 3492 grants permission to use, modify and distribute
the C code. `wrapper.c` is new: it drives the library through standard
input and output for `tests/run_tests.py`, in place of the RFC's own
test wrapper.
