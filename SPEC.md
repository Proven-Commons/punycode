# Specification: punycode

Punycode (RFC 3492, https://www.rfc-editor.org/rfc/rfc3492) writes a string of Unicode code points as a string of ASCII letters, digits and hyphens, and reads it back. IDNA uses it to put names such as `bücher` into the DNS as `xn--bcher-kva`. This library encodes and decodes one string. It does not add or remove the `xn--` prefix. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

## The format

Section 3 of RFC 3492 describes the format, with the parameters of section 5.

- **Basic code points** are U+0000 to U+007F. A string's basic code points come first, in their order, followed by a hyphen-minus (the delimiter) if and only if there is at least one (section 3.1).
- **The other code points** are written as deltas (section 3.2). The decoder starts from the basic code points and keeps a state `⟨n, i⟩`, which starts at `⟨128, 0⟩`. For each delta it:
  1. makes that many state changes, where a state change moves `⟨n, i⟩` to `⟨n, i + 1⟩`, or to `⟨n + 1, 0⟩` when `i` is the length of the string so far;
  2. inserts code point `n` at position `i`;
  3. makes one more state change.
- **Each delta** is a generalized variable-length integer (section 3.3): base 36 digits, least significant first. `A` to `Z` and `a` to `z` are 0 to 25, and `0` to `9` are 26 to 35. Digit `j` has threshold `t(j)` and weight `w(j)`, and the first digit below its threshold is the last.
- **After each delta**, the bias that sets the thresholds adapts (section 3.4).

`Spec.decode` in `Spec/Defs.lean` sets these rules out as written, one state change at a time. The code follows the pseudocode of section 6 instead, and the proofs show the two agree.

## Decoding

`decode s` gives the code points `s` stands for, or nothing when `s` stands for none. That covers:

- a code point that is not a digit after the delimiter, or one outside ASCII before it;
- digits that end inside an integer;
- a value that is not a Unicode scalar value: a surrogate (U+D800 to U+DFFF), or anything past U+10FFFF.

**A delimiter with nothing before it** is not a delimiter, because a delimiter follows the basic code points only when there are some. So `-tda` fails, where `tda` gives `ü`. Python's `punycode` codec reads `-tda` as `ü`. The RFC's own decoder in section 6.2, its sample code in appendix C, Node's punycode.js and libidn2 all reject it.

**Overflow.** Section 6.4 has an implementation fail when a number outgrows its integer type, so where it fails depends on the type. This library computes with unbounded naturals, so it has no such limit. Instead it fails as soon as the code point being built would pass U+10FFFF. A decoded value can then never be out of range, and every number stays below 0x110000 times the length of the input, so no input can make the arithmetic run long.

Digits may be upper case or lower case, as section 5 requires of a decoder. Letters before the delimiter are code points of the string and keep their case. Mixed-case annotation (appendix A) is not read.

## Encoding

`encode cs` writes the basic code points of `cs`, then the delimiter if there are any, then the deltas, with digits in lower case. Section 5 says an encoder should write one case. Every list of code points has an encoding: `encode` cannot fail.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| `decode` reads a string as section 3 describes, as `Spec.decode` states it. | `Spec.decode_eq` |
| A decoded string is never longer than the string it came from. | `Spec.decode_length` |
| Decoding an encoding gives the code points back. | `Spec.decode_encode` |
| `decode s` gives `cs` exactly when `encode cs` is `s` with its digits in lower case. | `Spec.decode_iff` |
| An encoding starts with the basic code points, in order, then a delimiter if there are any. The rest are lower case letters and digits. | `Spec.encode_form` |
| The 19 samples of section 7.1, decoded and encoded. | `Spec.rfc3492_decode`, `Spec.rfc3492_encode` |
| Strings that stand for nothing, and strings at the edges that do. | `Spec.reject_vectors`, `Spec.accept_vectors` |

Together, these fix every output.

- `decode` is fixed for every string by `Spec.decode_eq`.
- `Spec.decode_iff` then says `encode cs` is the one string with lower case digits that decodes to `cs`.
- `Spec.decode_encode` says there is such a string for every `cs`.

So two strings decode to the same code points only when they differ in the case of their digits. Section 6.2 of the RFC states this uniqueness in prose. `Spec.decode_iff` proves it.

## The command-line tool

The command-line tool in `Main.lean` has these modes:

- `punycode encode TEXT` prints the encoding of TEXT.
- `punycode decode PUNYCODE` prints the text, or exits with 1 when the string stands for none.
- `punycode serve` answers requests from the differential tests, one per line. Each string is sent as the hex digits of its UTF-8 bytes. The header comment of `Main.lean` gives the protocol.

Every answer comes from `encode` and `decode`.

## Oracles

The differential tests compare the tool with Python transcriptions of the pseudocode of sections 6.2 and 6.3, with unbounded integers. They also compare it with four implementations:

- the RFC's sample code in appendix C;
- Python's `punycode` codec;
- Node's punycode.js;
- libidn2.

The tool must agree with the transcriptions on every input. With each implementation, a difference is allowed only for a known reason, confirmed by the transcription:

- a value that is not a scalar value;
- an integer overflow in the implementation;
- Python's reading of a leading delimiter;
- libidn2's IDNA-specific refusals.
