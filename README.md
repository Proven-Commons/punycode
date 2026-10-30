# punycode: Punycode (RFC 3492), proved

Punycode writes Unicode text as ASCII letters, digits and hyphens, so that names such as `bücher` can live in the DNS as `xn--bcher-kva`. This library encodes and decodes it in Lean. Machine-checked proofs show four things:

- The decoder reads a string exactly as section 3 of RFC 3492 describes, except that it fails where a decoded value would not be a Unicode scalar value, which RFC 3492 itself allows.
- Decoding an encoding gives the text back, for every text.
- Every text has one encoding, up to the case of its digits. The decoder accepts no other string, so two strings that differ in more than case never decode to the same text.
- Where a decoded value would be a surrogate or pass U+10FFFF, the decoder fails rather than returning something else.

So `-tda` is rejected, while Python's codec reads it as `ü`. `ib9b` and `en32g`, which stand for U+D800 and for a value past U+10FFFF, are rejected too.

It is tested against a model of RFC 3492, the RFC's own sample code, Python, Node's punycode.js and libidn2. `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Punycode.encode : List Char → String`
- `Punycode.decode : String → Option (List Char)`

Neither adds or removes the `xn--` prefix of IDNA. `SPEC.md` says what each one does.

## What is proved

The statements are in `Punycode/Spec.lean`, the definitions they use in `Punycode/Spec/Defs.lean`, and the proofs in `Punycode/Proofs/`.

| Claim | Theorem |
|-------|---------|
| `decode` gives what section 3 of RFC 3492 describes: the basic code points, then one insertion per delta, with the state machine of section 3.2, the variable-length integers of section 3.3 and the bias adaptation of section 3.4. It fails when a value is not a Unicode scalar value. `Punycode.Spec.decode` sets the rules out one state change at a time, apart from the code. | `Punycode.Spec.decode_eq` |
| A decoded text is never longer than the string it came from. | `Punycode.Spec.decode_length` |
| Decoding an encoding gives the text back. | `Punycode.Spec.decode_encode` |
| `decode s` gives `cs` exactly when `encode cs` is `s` with its digits in lower case. So the encoding is unique up to case, and `decode` accepts nothing else. | `Punycode.Spec.decode_iff` |
| An encoding is the basic code points, in order, then a delimiter if there are any, then lower case letters and digits. | `Punycode.Spec.encode_form` |
| The 19 samples of section 7.1, both ways. Strings that stand for nothing, and strings at the edges that do. | `Punycode.Spec.rfc3492_decode`, `Punycode.Spec.rfc3492_encode`, `Punycode.Spec.reject_vectors`, `Punycode.Spec.accept_vectors` |

The command-line tool in `Main.lean` answers requests with these functions directly.

## What is not proved

- **IDNA.** This library does not check that a decoded label is a valid IDNA U-label, map case or normalize (UTS 46, IDNA2008), or handle the `xn--` prefix. IDNA's checks belong to the caller, or to a later slice.
- **Mixed-case annotation** (appendix A). The case of digits is ignored when decoding, and digits are written in lower case.
- **Reading requests and printing answers in `Main.lean`.** The differential tests cover them, with malformed requests and CR LF line endings.
- **The bound on the decoder's numbers.** The code stops reading an integer as soon as the code point it builds would pass U+10FFFF, so its numbers stay below 1,226 times 0x110000 times the length of the input. The factor is not 1: the code adds a digit times its weight before it compares, and that product can reach 1,225 times the limit, so for `aaa-bb0009` it computes 46,410,386 where 0x110000 times the length is 11,141,120. No theorem states any bound.
- **Speed.** The code works on lists of characters. Encoding takes time that grows with the square of the text's length. Decoding takes time proportional to its length times the number of code points inserted. Both are quick for DNS labels, which hold at most 63 characters.

## Where other implementations differ

The tests count every disagreement with the four implementations, with its reason, confirmed against the model.

- **Integer width.** RFC 3492, section 6.4, has an implementation fail when its integers overflow. The RFC's sample code and libidn2 overflow past 2^32 - 1, and Node's punycode.js past 2^31 - 1. This library uses unbounded integers, so it encodes and decodes long texts that they refuse.
- **Values that are not scalar values.** RFC 3492, section 5, allows any nonnegative integer as a code point. This library accepts only Unicode scalar values, since Lean's characters and UTF-8 hold no others. The RFC's sample code returns surrogates and values past U+10FFFF. Python and Node return surrogates. libidn2 2.3.7 rejects values past U+10FFFF and high surrogates, but returns low surrogates (U+DC00 to U+DFFF). This library fails on all of them.
- **Node's surrogates pair up.** Node returns surrogates as part of a UTF-16 string, so a high surrogate followed by a low one reads back as a single code point. `8c9bk9h` stands for U+D83D U+DE00, which Node returns as U+1F600.
- **Python's `punycode` codec** reads a delimiter with nothing before it, so it decodes `-tda` as `ü`.
- **libidn2** refuses two kinds of string RFC 3492 allows. It refuses a string with no deltas, such as `abc-` or the empty string. It also refuses a basic code point before the delimiter that is not a letter, digit, `-` or `_`. These are IDNA rules, not Punycode ones.
- **libidn2 reads `_` as a digit.** In the deltas, libidn2 2.3.7 reads `_` as `a`, the digit 0, so `td_` decodes to `ü` as `tda` does, and `_` alone to U+0080. `_` is not a Punycode digit, so this library rejects both.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number arithmetic and the conversion between strings and lists.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and the four implementations. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), Python 3, a C compiler, Node and libidn2.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Punycode/Proofs/` proves exactly the statement in `Punycode/Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script builds the tool and the RFC's sample code, and runs these inputs:

- the samples of section 7.1;
- strings at the edges;
- every string of up to five characters over `a`, `Z`, `0`, `9`, `-`, `.` and `ü`;
- random texts, their encodings and mutations of them, from a recorded seed;
- long texts.

It then rewrites `tests/TEST-RESULTS.md`. `tests/plant_bugs.py` plants ten bugs in a copy of the code, one at a time, and records in `tests/PLANTED-BUGS.md` how many failures the tests report for each. Every bug must be caught, and each of them also breaks a proof.

## Layout

- `Punycode/Basic.lean`: the code under proof.
- `Punycode/Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Punycode/Spec/Defs.lean`: the definitions the statements use, written from section 3 of RFC 3492.
- `Punycode/Proofs.lean` and `Punycode/Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/oracles/rfc3492/`: the RFC's sample code, unchanged, with a wrapper and a note on where it comes from.
- `tests/oracles/node/oracle.js`: the Node oracle.
- `tests/plant_bugs.py` and `tests/PLANTED-BUGS.md`: the planted bugs, and the record that the tests catch each one.
