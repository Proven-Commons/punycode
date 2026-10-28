/-
  Punycode, RFC 3492: the code under proof.

  `encode` turns a list of Unicode code points into its Punycode
  string, and `decode` turns a Punycode string back into the code
  points, or fails. The `xn--` prefix of IDNA is not part of either.

  The decoder follows the procedure of section 6.2. Where section 6.4
  has an implementation fail when a number outgrows its integer type,
  this one computes with unbounded naturals and fails as soon as the
  code point being built would pass U+10FFFF, which keeps every
  number below 1,226 times 0x110000 times the length of the input. It also fails on a surrogate, which is not a
  Unicode scalar value.

  The encoder finds the insertions the decoder will make, then writes
  the deltas between them as section 3 describes, with the integer
  encoding and bias adaptation of section 6.

  `Spec.lean` states what the two compute.
-/

namespace Punycode

/-! ## Parameters (section 5) -/

def base : Nat := 36
def tmin : Nat := 1
def tmax : Nat := 26
def skew : Nat := 38
def damp : Nat := 700
def initialBias : Nat := 72
def initialN : Nat := 0x80

/-- A basic code point: one of ASCII. -/
def isBasic (c : Char) : Bool := c.toNat < 0x80

/-- The threshold of the digit at `k = base * (j + 1)`, for the current
    bias (section 6.2). -/
def threshold (k bias : Nat) : Nat :=
  if k ≤ bias then tmin else if bias + tmax ≤ k then tmax else k - bias

theorem threshold_pos (k bias : Nat) : 1 ≤ threshold k bias := by
  unfold threshold tmin tmax; split <;> (try split) <;> omega

theorem threshold_le (k bias : Nat) : threshold k bias ≤ 26 := by
  unfold threshold tmin tmax; split <;> (try split) <;> omega

/-- Bias adaptation (section 6.1). -/
def adapt (delta numpoints : Nat) (firsttime : Bool) : Nat :=
  let delta := if firsttime then delta / damp else delta / 2
  go (delta + delta / numpoints) 0
where
  go (delta k : Nat) : Nat :=
    if ((base - tmin) * tmax) / 2 < delta then go (delta / (base - tmin)) (k + base)
    else k + ((base - tmin + 1) * delta) / (delta + skew)
  termination_by delta
  decreasing_by simp only [base, tmin, tmax] at *; omega

/-! ## Digits -/

/-- The digit value of a code point (section 5): `A` to `Z` and `a` to
    `z` are 0 to 25, and `0` to `9` are 26 to 35. -/
def digitValue (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 26)
  else none

/-- The code point the encoder writes for a digit value: lower case
    letters, then digits. -/
def digitChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat ('a'.toNat + d) else Char.ofNat ('0'.toNat + (d - 26))

/-! ## Variable-length integers (sections 3.3 and 6) -/

/-- The digits of `q` as a generalized variable-length integer, least
    significant first, with the first threshold at `k` (section 6.3). -/
def encodeInt (bias q k : Nat) : List Nat :=
  if q < threshold k bias then [q]
  else (threshold k bias + (q - threshold k bias) % (base - threshold k bias)) ::
    encodeInt bias ((q - threshold k bias) / (base - threshold k bias)) (k + base)
termination_by q
decreasing_by
  have h1 := threshold_pos k bias
  have h2 := threshold_le k bias
  simp only [base]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- Read one variable-length integer from the input and add it to `i`
    (the inner loop of section 6.2). Fail on a code point that is not a
    digit, at the end of the input, or once `i` passes `limit`. -/
def decodeInt (bias limit : Nat) : List Char → Nat → Nat → Nat → Option (Nat × List Char)
  | [], _, _, _ => none
  | c :: rest, i, w, k =>
    match digitValue c with
    | none => none
    | some d =>
      if limit < i + d * w then none
      else if d < threshold k bias then some (i + d * w, rest)
      else decodeInt bias limit rest (i + d * w) (w * (base - threshold k bias)) (k + base)

theorem decodeInt_length {bias limit : Nat} :
    ∀ {cs : List Char} {i w k v : Nat} {rest : List Char},
      decodeInt bias limit cs i w k = some (v, rest) → rest.length < cs.length
  | [], _, _, _, _, _, h => by simp [decodeInt] at h
  | c :: cs, i, w, k, v, rest, h => by
    unfold decodeInt at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; simp
        · have := decodeInt_length h
          simp only [List.length_cons]; omega

/-! ## Decoding (section 6.2) -/

/-- The input split at its last delimiter, when code points come
    before it: the literal portion, then the rest. Otherwise nothing,
    and the whole input (section 6.2). -/
def splitLast : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    match splitLast cs with
    | some (before, after) => some (c :: before, after)
    | none => if c = '-' then some ([], cs) else none

def splitLiteral (s : List Char) : List Char × List Char :=
  match splitLast s with
  | some (c :: before, after) => (c :: before, after)
  | _ => ([], s)

/-- The main loop of section 6.2: read each delta, move the state
    `⟨n, i⟩` on, and insert `n` at `i`. Fail when the code point would
    pass U+10FFFF or be a surrogate. -/
def decodeLoop (bias : Nat) (first : Bool) (n i : Nat) (out input : List Char) :
    Option (List Char) :=
  match input with
  | [] => some out
  | c :: cs =>
    match h : decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1 base with
    | none => none
    | some (i', rest) =>
      if 0xD800 ≤ n + i' / (out.length + 1) ∧ n + i' / (out.length + 1) ≤ 0xDFFF then none
      else
        decodeLoop (adapt (i' - i) (out.length + 1) first) false (n + i' / (out.length + 1))
          (i' % (out.length + 1) + 1)
          (out.insertIdx (i' % (out.length + 1)) (Char.ofNat (n + i' / (out.length + 1)))) rest
termination_by input.length
decreasing_by exact decodeInt_length h

/-- Decode a Punycode string into code points (section 6.2), or fail. -/
def decode (s : String) : Option (List Char) :=
  if (splitLiteral s.toList).1.all isBasic then
    decodeLoop initialBias true initialN 0 (splitLiteral s.toList).1 (splitLiteral s.toList).2
  else none

/-! ## Encoding -/

/-- The value and position of the last occurrence of the greatest code
    point, starting from `acc` at position `j`. -/
def maxPos : List Char → Nat → Nat × Nat → Nat × Nat
  | [], _, acc => acc
  | c :: cs, j, (v, p) => if v ≤ c.toNat then maxPos cs (j + 1) (c.toNat, j) else maxPos cs (j + 1) (v, p)

theorem maxPos_lt : ∀ {cs : List Char} {j v p : Nat},
    (maxPos cs j (v, p)).2 < j + cs.length ∨ maxPos cs j (v, p) = (v, p)
  | [], j, v, p => by simp [maxPos]
  | c :: cs, j, v, p => by
    unfold maxPos
    split
    · rcases maxPos_lt (cs := cs) (j := j + 1) (v := c.toNat) (p := j) with h | h
      · left; simp only [List.length_cons]; omega
      · left; rw [h]; simp only [List.length_cons]; omega
    · rcases maxPos_lt (cs := cs) (j := j + 1) (v := v) (p := p) with h | h
      · left; simp only [List.length_cons]; omega
      · right; exact h

theorem maxPos_fst_le : ∀ {cs : List Char} {j v p : Nat}, v ≤ (maxPos cs j (v, p)).1
  | [], _, _, _ => by simp [maxPos]
  | c :: cs, j, v, p => by
    unfold maxPos
    split
    · exact Nat.le_trans (by omega) maxPos_fst_le
    · exact maxPos_fst_le

/-- The insertions that build `cs` from its basic code points, in the
    order the decoder makes them: each code point that is not basic,
    with the index it is inserted at. The last one is the greatest code
    point, at its last occurrence; it goes in at its own index. -/
def insertions (cs : List Char) : List (Nat × Nat) :=
  if _h : (maxPos cs 0 (0, 0)).1 < 0x80 then []
  else insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2) ++ [maxPos cs 0 (0, 0)]
termination_by cs.length
decreasing_by
  rcases maxPos_lt (cs := cs) (j := 0) (v := 0) (p := 0) with h' | h'
  · rw [List.length_eraseIdx_of_lt (by omega)]
    have : cs.length ≠ 0 := by omega
    omega
  · rw [h'] at _h; simp at _h

/-- The deltas between consecutive insertions (section 3.2): the number
    of state changes from the state after one insertion to the state of
    the next. With `L` code points in the string, state `⟨n, i⟩` is
    number `n * (L + 1) + i`. -/
def deltas (b : Nat) : Nat → Nat → Nat → List (Nat × Nat) → List Nat
  | _, _, _, [] => []
  | pn, pi, j, (n, i) :: rest =>
    (n * (b + j + 1) + i - (pn * (b + j + 1) + pi)) :: deltas b n (i + 1) (j + 1) rest

/-- The digits for each delta, adapting the bias after each
    (section 6.3). -/
def encodeDeltas (b bias : Nat) (first : Bool) (j : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => encodeInt bias d base ++ encodeDeltas b (adapt d (b + j + 1) first) false (j + 1) ds

/-- Encode code points as a Punycode string: the basic code points in
    order, a delimiter if there were any, then the deltas. -/
def encode (cs : List Char) : String :=
  String.ofList (cs.filter isBasic ++ (if (cs.filter isBasic).isEmpty then [] else ['-']) ++
    (encodeDeltas (cs.filter isBasic).length initialBias true 0
      (deltas (cs.filter isBasic).length initialN 0 0 (insertions cs))).map digitChar)

end Punycode
