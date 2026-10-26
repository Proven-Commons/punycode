import Punycode
import Spec.Defs

/-!
  Building blocks for `Proofs/Decode.lean`: the code's digits,
  thresholds, bias adaptation and variable-length integers agree with
  those of `Spec/Defs.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Punycode.Proofs

/-! ## Characters -/

theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem digitValue_eq (c : Char) : Punycode.digitValue c = Spec.digitValue c := by
  unfold Punycode.digitValue Spec.digitValue
  have hA : 'A'.toNat = 0x41 := rfl
  have hZ : 'Z'.toNat = 0x5A := rfl
  have ha : 'a'.toNat = 0x61 := rfl
  have hz : 'z'.toNat = 0x7A := rfl
  have h0 : '0'.toNat = 0x30 := rfl
  have h9 : '9'.toNat = 0x39 := rfl
  simp only [char_le_iff, hA, hZ, ha, hz, h0, h9]

theorem isBasic_iff (c : Char) : Punycode.isBasic c = true ↔ Spec.Basic c := by
  unfold Punycode.isBasic Spec.Basic
  simp

theorem all_isBasic_iff (l : List Char) : l.all Punycode.isBasic = true ↔ ∀ c ∈ l, Spec.Basic c := by
  rw [List.all_eq_true]
  simp only [isBasic_iff]

/-! ## Constants -/

theorem base_eq : Punycode.base = Spec.base := rfl
theorem initialBias_eq : Punycode.initialBias = Spec.initialBias := rfl
theorem initialN_eq : Punycode.initialN = Spec.initialN := rfl

/-! ## Thresholds -/

theorem threshold_eq (bias j : Nat) :
    Punycode.threshold (Punycode.base * (j + 1)) bias = Spec.t bias j := by
  unfold Punycode.threshold Spec.t
  split
  · simp only [Punycode.base, Punycode.tmin, Punycode.tmax, Spec.base, Spec.tmin, Spec.tmax] at *
    omega
  · split <;>
    · simp only [Punycode.base, Punycode.tmin, Punycode.tmax, Spec.base, Spec.tmin, Spec.tmax] at *
      omega

/-! ## Bias adaptation -/

theorem go_eq : ∀ (delta k : Nat), Punycode.adapt.go delta k =
    k + Spec.base * (Spec.divisions delta).1 +
      ((Spec.base - Spec.tmin + 1) * (Spec.divisions delta).2) /
        ((Spec.divisions delta).2 + Spec.skew)
  | delta, k => by
    rw [Punycode.adapt.go.eq_def, Spec.divisions.eq_def]
    have hb : (Punycode.base - Punycode.tmin) * Punycode.tmax / 2 =
        (Spec.base - Spec.tmin) * Spec.tmax / 2 := rfl
    rw [hb]
    split
    · have ih := go_eq (delta / (Spec.base - Spec.tmin)) (k + Punycode.base)
      have h35 : Punycode.base - Punycode.tmin = Spec.base - Spec.tmin := rfl
      rw [h35, ih]
      simp only [Punycode.base, Spec.base, Spec.tmin, Spec.skew]
      omega
    · simp only [Punycode.base, Punycode.tmin, Punycode.skew, Spec.base, Spec.tmin, Spec.skew]
      omega
termination_by delta => delta
decreasing_by simp only [Spec.base, Spec.tmin, Spec.tmax] at *; omega

theorem adapt_eq (delta numpoints : Nat) (first : Bool) :
    Punycode.adapt delta numpoints first = Spec.adapt delta numpoints first := by
  unfold Punycode.adapt Spec.adapt
  rw [go_eq]
  cases first <;> simp only [Punycode.damp, Spec.damp] <;> simp

end Punycode.Proofs
