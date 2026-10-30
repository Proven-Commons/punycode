/-
  The definitions the statements in `Punycode/Spec.lean` use, written from
  RFC 3492, separately from the code in `Punycode/`.

  `Punycode.Spec.decode` follows the description of Bootstring in section 3,
  with the parameters of section 5, rather than the pseudocode of
  section 6 that the code follows:

  - 3.1: the basic code points come first, then a delimiter if and
    only if there are any. The delimiter never appears after it.
  - 3.2: the decoder starts with the literal portion and inserts one
    code point per delta. It makes `delta` state changes, inserts `n`
    at `i`, then makes one more state change. A state change takes
    `⟨n, i⟩` to `⟨n, i + 1⟩`, or to `⟨n + 1, 0⟩` when `i` is the length
    of the string. Here it is made one step at a time, not by division.
  - 3.3: each delta is a generalized variable-length integer, least
    significant digit first. Digit `j` has threshold `t(j)`, which is
    `base * (j + 1) - bias` clamped to `tmin` to `tmax`, and weight
    `w(j)`. The first digit below its threshold is the last.
  - 3.4: after each delta, the bias adapts.

  Every inserted code point must be a Unicode scalar value: at most
  U+10FFFF, and not a surrogate. This is a departure from RFC 3492,
  whose section 5 allows any nonnegative integer: Lean's `Char`, like
  UTF-8, holds only scalar values. Section 6.4 lets an implementation
  fail when its integers overflow; this specification has no integer
  bound, so it fails only on values that are not scalar values.
-/

namespace Punycode.Spec

/-! ## Parameters (section 5) -/

def base : Nat := 36
def tmin : Nat := 1
def tmax : Nat := 26
def skew : Nat := 38
def damp : Nat := 700
def initialBias : Nat := 72
def initialN : Nat := 128

/-- A basic code point: U+0000 to U+007F. -/
def Basic (c : Char) : Prop := c.toNat < 128

instance (c : Char) : Decidable (Basic c) := inferInstanceAs (Decidable (c.toNat < 128))

/-- The digit value of a code point (section 5): U+0041 to U+005A and
    U+0061 to U+007A are 0 to 25, and U+0030 to U+0039 are 26 to 35. -/
def digitValue (c : Char) : Option Nat :=
  if 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A then some (c.toNat - 0x41)
  else if 0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A then some (c.toNat - 0x61)
  else if 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 then some (c.toNat - 0x30 + 26)
  else none

/-- A Unicode scalar value: at most U+10FFFF, and not a surrogate. -/
def Scalar (n : Nat) : Prop := n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)

instance (n : Nat) : Decidable (Scalar n) := inferInstanceAs (Decidable (_ ∨ _))

/-! ## Variable-length integers (section 3.3) -/

/-- `t(j)`: `base * (j + 1) - bias`, clamped to `tmin` to `tmax`. -/
def t (bias j : Nat) : Nat := min tmax (max tmin (base * (j + 1) - bias))

/-- `w(0) = 1`, and `w(j) = w(j - 1) * (base - t(j - 1))`. -/
def w (bias : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => w bias j * (base - t bias j)

/-- Read one integer from digit values, starting at digit `j`: digits
    up to and including the first below its threshold. Gives the sum
    of each digit times its weight, and the digits after it. -/
def readInt (bias : Nat) : Nat → List Nat → Option (Nat × List Nat)
  | _, [] => none
  | j, d :: ds =>
    if d < t bias j then some (d * w bias j, ds)
    else (readInt bias (j + 1) ds).map fun r => (d * w bias j + r.1, r.2)

theorem readInt_length {bias : Nat} : ∀ {j : Nat} {ds : List Nat} {v : Nat} {rest : List Nat},
    readInt bias j ds = some (v, rest) → rest.length < ds.length
  | _, [], _, _, h => by simp [readInt] at h
  | j, d :: ds, v, rest, h => by
    unfold readInt at h
    split at h
    · cases h; simp
    · cases h' : readInt bias (j + 1) ds with
      | none => rw [h'] at h; cases h
      | some r =>
        rw [h'] at h
        cases h
        have := readInt_length h'
        simp only [List.length_cons]; omega

/-! ## Bias adaptation (section 3.4) -/

/-- Step 3 of section 3.4: divide by `base - tmin` while above
    `((base - tmin) * tmax) / 2`. Gives the number of divisions and
    what is left. -/
def divisions (delta : Nat) : Nat × Nat :=
  if ((base - tmin) * tmax) / 2 < delta then
    let r := divisions (delta / (base - tmin))
    (r.1 + 1, r.2)
  else (0, delta)
termination_by delta
decreasing_by simp only [base, tmin, tmax] at *; omega

/-- Section 3.4: the bias for the next delta. -/
def adapt (delta numpoints : Nat) (first : Bool) : Nat :=
  let scaled := delta / (if first then damp else 2)
  let grown := scaled + scaled / numpoints
  base * (divisions grown).1 + ((base - tmin + 1) * (divisions grown).2) /
    ((divisions grown).2 + skew)

/-- Read every delta, adapting the bias after each. `count` is the
    number of code points the string will hold before the next
    insertion. -/
def readDeltas (bias : Nat) (first : Bool) (count : Nat) (ds : List Nat) :
    Option (List Nat) :=
  match ds with
  | [] => some []
  | d :: ds' =>
    match h : readInt bias 0 (d :: ds') with
    | none => none
    | some (v, rest) =>
      (readDeltas (adapt v (count + 1) first) false (count + 1) rest).map (v :: ·)
termination_by ds.length
decreasing_by exact readInt_length h

/-! ## The state machine (section 3.2) -/

/-- One state change, on a string of length `L`. -/
def next (L : Nat) (s : Nat × Nat) : Nat × Nat :=
  if s.2 < L then (s.1, s.2 + 1) else (s.1 + 1, 0)

/-- `k` state changes, on a string of length `L`. -/
def advance (L : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | k + 1, s => advance L k (next L s)

/-- Insert one code point per delta, starting from state `s`: `delta`
    state changes, the insertion of `n` at `i`, then one more state
    change. Fail when a value inserted is not a scalar value. -/
def insertAll : List Char → Nat × Nat → List Nat → Option (List Char)
  | out, _, [] => some out
  | out, s, d :: ds =>
    if Scalar (advance out.length d s).1 then
      insertAll (out.insertIdx (advance out.length d s).2 (Char.ofNat (advance out.length d s).1))
        (next (out.length + 1) (advance out.length d s)) ds
    else none

/-! ## Decoding (section 3) -/

/-- The literal portion and the rest (section 3.1). With a delimiter,
    the literal portion is everything before the last one, and must
    not be empty, since a delimiter follows the basic code points only
    when there are some. With no delimiter, it is empty. -/
def split (s : List Char) : Option (List Char × List Char) :=
  if '-' ∈ s then
    let p := s.length - 1 - (s.reverse.idxOf '-')
    if p = 0 then none else some (s.take p, s.drop (p + 1))
  else some ([], s)

/-- The code points a Punycode string stands for (section 3), or none
    when it does not stand for any. -/
def decode (s : List Char) : Option (List Char) :=
  match split s with
  | none => none
  | some (lit, rest) =>
    if ∀ c ∈ lit, Basic c then
      match rest.mapM digitValue with
      | none => none
      | some digits =>
        match readDeltas initialBias true lit.length digits with
        | none => none
        | some deltas => insertAll lit (initialN, 0) deltas
    else none

/-! ## Case -/

/-- ASCII lower case of one code point. -/
def lower (c : Char) : Char := if 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A then Char.ofNat (c.toNat + 32) else c

/-- A string with its digits in lower case: the part after the literal
    portion, or the whole string when it has no literal portion.
    Section 5 has a decoder read digits in either case, and an encoder
    write one case; letters in the literal portion are code points of
    the string and keep their case. -/
def lowerDigits (s : List Char) : List Char :=
  match split s with
  | some (c :: lit, rest) => (c :: lit) ++ '-' :: rest.map lower
  | _ => s.map lower

end Punycode.Spec
