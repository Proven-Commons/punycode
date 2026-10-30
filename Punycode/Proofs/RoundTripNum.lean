/-
  Digits and variable-length integers, for the round trip of the
  encoder and the decoder.
-/

import Punycode
import Punycode.Spec.Defs

namespace Punycode.Proofs.Enc

open Punycode

/-! ## Code points -/

theorem toNat_ofNat_of_valid {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  simp only [h, dite_true]
  rfl

theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]
  rfl

theorem char_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) :=
  c.valid

theorem char_lt (c : Char) : c.toNat < 0x110000 := by
  have := char_valid c
  omega

theorem char_not_surrogate (c : Char) : ¬ (0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF) := by
  have := char_valid c
  omega

/-- The value of `Char.ofNat n` when `n` is below the limit and not a surrogate. -/
theorem toNat_ofNat_of_lt {n : Nat} (h1 : n < 0x110000) (h2 : ¬ (0xD800 ≤ n ∧ n ≤ 0xDFFF)) :
    (Char.ofNat n).toNat = n := by
  apply toNat_ofNat_of_valid
  show n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)
  omega

/-! ## Digits -/

theorem digitValue_eq (c : Char) : digitValue c =
    if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then some (c.toNat - 65)
    else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 97)
    else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48 + 26)
    else none := by
  simp only [digitValue, char_le_iff]
  rfl

theorem toNat_digitChar_all : ∀ d, d < 36 → (digitChar d).toNat = if d < 26 then 97 + d else 22 + d := by
  decide

theorem toNat_digitChar {d : Nat} (h : d < 36) :
    (digitChar d).toNat = if d < 26 then 97 + d else 22 + d :=
  toNat_digitChar_all d h

theorem digitValue_digitChar_all : ∀ d, d < 36 → digitValue (digitChar d) = some d := by
  decide

theorem digitValue_digitChar {d : Nat} (h : d < 36) : digitValue (digitChar d) = some d :=
  digitValue_digitChar_all d h

theorem lower_digitChar_all : ∀ d, d < 36 → Punycode.Spec.lower (digitChar d) = digitChar d := by
  decide

theorem lower_digitChar {d : Nat} (h : d < 36) : Punycode.Spec.lower (digitChar d) = digitChar d :=
  lower_digitChar_all d h

theorem digitChar_ne_dash_all : ∀ d, d < 36 → digitChar d ≠ '-' := by
  decide

theorem digitChar_ne_dash {d : Nat} (h : d < 36) : digitChar d ≠ '-' :=
  digitChar_ne_dash_all d h

theorem digitChar_form_all : ∀ d, d < 36 →
    ('a' ≤ digitChar d ∧ digitChar d ≤ 'z') ∨ ('0' ≤ digitChar d ∧ digitChar d ≤ '9') := by
  decide

theorem digitChar_form {d : Nat} (h : d < 36) :
    ('a' ≤ digitChar d ∧ digitChar d ≤ 'z') ∨ ('0' ≤ digitChar d ∧ digitChar d ≤ '9') :=
  digitChar_form_all d h

theorem toNat_lower (c : Char) :
    (Punycode.Spec.lower c).toNat = if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat + 32 else c.toNat := by
  unfold Punycode.Spec.lower
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have h' : 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A := h
    rw [ite_eq_left h', ite_eq_left h]
    exact toNat_ofNat_of_lt (by omega) (by omega)
  · have h' : ¬ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) := h
    rw [ite_eq_right h', ite_eq_right h]

theorem digitValue_lower (c : Char) : digitValue (Punycode.Spec.lower c) = digitValue c := by
  rw [digitValue_eq, digitValue_eq, toNat_lower]
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have e : c.toNat + 32 - 97 = c.toNat - 65 := by omega
    rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h, e]
  · rw [ite_eq_right h]

theorem lower_of_digitValue {c : Char} {d : Nat} (h : digitValue c = some d) :
    Punycode.Spec.lower c = digitChar d ∧ d < 36 := by
  rw [digitValue_eq] at h
  have hd : d < 36 := by
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h
  refine ⟨?_, hd⟩
  apply Char.toNat_inj.mp
  rw [toNat_lower, toNat_digitChar hd]
  split at h
  · cases h
    rw [ite_eq_left (by assumption), ite_eq_left (by omega)]
    omega
  · split at h
    · cases h
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
    · split at h
      · cases h
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega
      · cases h

theorem lower_dash : Punycode.Spec.lower '-' = '-' := by decide

theorem lower_eq_dash_iff (c : Char) : Punycode.Spec.lower c = '-' ↔ c = '-' := by
  constructor
  · intro h
    have h1 := congrArg Char.toNat h
    rw [toNat_lower] at h1
    have h2 : ('-' : Char).toNat = 45 := rfl
    apply Char.toNat_inj.mp
    rw [h2]
    rw [h2] at h1
    split at h1 <;> omega
  · intro h
    rw [h]
    exact lower_dash

/-! ## Variable-length integers -/

theorem encodeInt_ne_nil (bias q k : Nat) : encodeInt bias q k ≠ [] := by
  rw [encodeInt]
  split <;> simp

theorem encodeInt_lt (bias : Nat) : ∀ q k, ∀ d ∈ encodeInt bias q k, d < 36 := by
  intro q k
  induction q, k using encodeInt.induct bias with
  | case1 q k h =>
    intro d hd
    rw [encodeInt, ite_eq_left h] at hd
    have := threshold_le k bias
    simp only [List.mem_singleton] at hd
    omega
  | case2 q k h ih =>
    intro d hd
    rw [encodeInt, ite_eq_right h] at hd
    simp only [List.mem_cons] at hd
    rcases hd with hd | hd
    · have h1 := threshold_le k bias
      have h2 := threshold_pos k bias
      have hbase : base = 36 := rfl
      have h3 : (q - threshold k bias) % (base - threshold k bias) < base - threshold k bias :=
        Nat.mod_lt _ (by omega)
      omega
    · exact ih d hd

/-- Writing `q` and reading it back: the digits `encodeInt` writes, read
    by `decodeInt` with weight `w`, add `q * w` to `i`. -/
theorem decodeInt_encodeInt (bias limit : Nat) (rest : List Char) :
    ∀ q k i w, 1 ≤ w → i + q * w ≤ limit →
      decodeInt bias limit ((encodeInt bias q k).map digitChar ++ rest) i w k =
        some (i + q * w, rest) := by
  intro q k
  induction q, k using encodeInt.induct bias with
  | case1 q k h =>
    intro i w _ hlim
    have h1 := threshold_le k bias
    rw [encodeInt, ite_eq_left h]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [decodeInt, digitValue_digitChar (by omega)]
    simp only
    rw [ite_eq_right (by omega), ite_eq_left h]
  | case2 q k h ih =>
    intro i w hw hlim
    have h1 := threshold_le k bias
    have h2 := threshold_pos k bias
    rw [encodeInt, ite_eq_right h]
    simp only [List.map_cons, List.cons_append]
    rw [decodeInt]
    have hbase : base = 36 := rfl
    generalize threshold k bias = t at *
    generalize hm : base - t = m at *
    have hm0 : 0 < m := by omega
    have hmod := Nat.mod_add_div (q - t) m
    have hlt := Nat.mod_lt (q - t) hm0
    generalize (q - t) % m = r at *
    generalize (q - t) / m = q' at *
    have hd36 : t + r < 36 := by omega
    rw [digitValue_digitChar hd36]
    simp only
    -- `q = d + q' * m`, so the partial sum stays below the whole one
    have hq : q = (t + r) + q' * m := by rw [Nat.mul_comm]; omega
    have hsum : i + (t + r) * w + q' * (w * m) = i + q * w := by
      rw [hq, Nat.add_mul (t + r), Nat.mul_assoc, Nat.mul_comm m w, Nat.add_assoc]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [ih _ _ (Nat.mul_pos hw hm0) (by omega), hsum]

/-- What `decodeInt` reads is, up to the case of its digits, what
    `encodeInt` writes. -/
theorem decodeInt_inv (bias limit : Nat) :
    ∀ (cs : List Char) (i w k i' : Nat) (rest : List Char), 1 ≤ w →
      decodeInt bias limit cs i w k = some (i', rest) →
      ∃ pre q, cs = pre ++ rest ∧ i' = i + q * w ∧
        pre.map Punycode.Spec.lower = (encodeInt bias q k).map digitChar ∧ i' ≤ limit := by
  intro cs
  induction cs with
  | nil =>
    intro i w k i' rest _ h
    simp [decodeInt] at h
  | cons c cs ih =>
    intro i w k i' rest hw h
    rw [decodeInt] at h
    split at h
    · cases h
    · rename_i d hd
      have ⟨hlow, hd36⟩ := lower_of_digitValue hd
      split at h
      · cases h
      · rename_i hlim
        split at h
        · rename_i ht
          cases h
          refine ⟨[c], d, rfl, rfl, ?_, by omega⟩
          rw [encodeInt, ite_eq_left ht]
          simp [hlow]
        · rename_i ht
          have h1 := threshold_le k bias
          have h2 := threshold_pos k bias
          have hb : base - threshold k bias > 0 := by simp only [base]; omega
          obtain ⟨pre, q, hcs, hi', hpre, hle⟩ := ih _ _ _ _ _ (Nat.mul_pos hw hb) h
          refine ⟨c :: pre, d + q * (base - threshold k bias), ?_, ?_, ?_, hle⟩
          · rw [hcs]; rfl
          · rw [hi', Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (base - threshold k bias) w,
              Nat.add_assoc]
          · have hdt : d - threshold k bias < base - threshold k bias := by
              simp only [base]; omega
            have hge : ¬ d + q * (base - threshold k bias) < threshold k bias := by omega
            have hsub : d + q * (base - threshold k bias) - threshold k bias =
                (d - threshold k bias) + q * (base - threshold k bias) := by omega
            have hmod : (d + q * (base - threshold k bias) - threshold k bias) %
                (base - threshold k bias) = d - threshold k bias := by
              rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdt]
            have hdiv : (d + q * (base - threshold k bias) - threshold k bias) /
                (base - threshold k bias) = q := by
              rw [hsub, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hdt, Nat.zero_add]
            rw [encodeInt, ite_eq_right hge, hmod, hdiv]
            simp only [List.map_cons, hlow, hpre]
            congr 2
            omega

/-- `decodeInt` reads digits in either case. -/
theorem decodeInt_map_lower (bias limit : Nat) :
    ∀ (cs : List Char) (i w k : Nat),
      decodeInt bias limit (cs.map Punycode.Spec.lower) i w k =
        (decodeInt bias limit cs i w k).map (fun r => (r.1, r.2.map Punycode.Spec.lower)) := by
  intro cs
  induction cs with
  | nil => intro i w k; simp [decodeInt]
  | cons c cs ih =>
    intro i w k
    simp only [List.map_cons]
    rw [decodeInt, decodeInt, digitValue_lower]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact ih _ _ _

end Punycode.Proofs.Enc
