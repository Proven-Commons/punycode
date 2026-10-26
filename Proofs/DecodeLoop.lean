import Proofs.DecodeInt

/-!
  The main loop: the code's `decodeLoop`, which reads one delta and
  inserts one code point per step, computes what the specification
  computes by reading every delta with `readDeltas`, then inserting
  with `insertAll`.
-/

set_option linter.unusedSimpArgs false

namespace Punycode.Proofs

/-! ## The state machine -/

theorem next_lt {L n i : Nat} (h : i < L) : Spec.next L (n, i) = (n, i + 1) := by
  unfold Spec.next
  rw [ite_eq_left h]

theorem next_self {L n : Nat} : Spec.next L (n, L) = (n + 1, 0) := by
  unfold Spec.next
  rw [ite_eq_right (Nat.lt_irrefl L)]

/-- `d` state changes from `⟨n, i⟩`, on a string of length `L`, by
    division. -/
theorem advance_eq (L : Nat) : ∀ (d n i : Nat), i ≤ L →
    Spec.advance L d (n, i) = (n + (i + d) / (L + 1), (i + d) % (L + 1))
  | 0, n, i, h => by
    rw [Spec.advance, Nat.add_zero, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.add_zero]
  | d + 1, n, i, h => by
    rw [Spec.advance]
    by_cases hi : i < L
    · rw [next_lt hi, advance_eq L d n (i + 1) (by omega), show i + 1 + d = i + (d + 1) by omega]
    · have hL : i = L := by omega
      subst hL
      rw [next_self, advance_eq i d (n + 1) 0 (Nat.zero_le _),
        show i + (d + 1) = d + (i + 1) by omega, Nat.add_div_right _ (Nat.succ_pos i),
        Nat.add_mod_right, Nat.zero_add]
      refine Prod.ext ?_ rfl
      show n + 1 + d / (i + 1) = n + (d / (i + 1) + 1)
      omega

/-- One insertion of the specification, from a state `⟨n, i⟩` with `i`
    at most the length of the string. -/
theorem insertAll_step (out : List Char) (n i v : Nat) (deltas : List Nat)
    (hi : i ≤ out.length) :
    Spec.insertAll out (n, i) (v :: deltas) =
      if Spec.Scalar (n + (i + v) / (out.length + 1)) then
        Spec.insertAll
          (out.insertIdx ((i + v) % (out.length + 1)) (Char.ofNat (n + (i + v) / (out.length + 1))))
          (n + (i + v) / (out.length + 1), (i + v) % (out.length + 1) + 1) deltas
      else none := by
  rw [Spec.insertAll, advance_eq _ v n i hi]
  simp only []
  rw [next_lt (Nat.mod_lt _ (Nat.succ_pos _))]

/-! ## The limit -/

theorem limit_lt_iff (n L x : Nat) (hn : n ≤ 0x10FFFF) :
    (0x110000 - n) * (L + 1) - 1 < x ↔ 0x110000 ≤ n + x / (L + 1) := by
  have hpos : 0 < (0x110000 - n) * (L + 1) := Nat.mul_pos (by omega) (by omega)
  have h1 : (0x110000 - n) * (L + 1) - 1 < x ↔ (0x110000 - n) * (L + 1) ≤ x := by omega
  rw [h1, ← Nat.le_div_iff_mul_le (by omega : 0 < L + 1)]
  omega

/-! ## Reading deltas -/

theorem readDeltas_of_none {bias count d : Nat} {first : Bool} {ds : List Nat}
    (h : Spec.readInt bias 0 (d :: ds) = none) :
    Spec.readDeltas bias first count (d :: ds) = none := by
  rw [Spec.readDeltas.eq_def]
  simp only []
  split
  · rfl
  · rename_i heq
    rw [h] at heq
    cases heq

theorem readDeltas_of_some {bias count d v : Nat} {first : Bool} {ds rds : List Nat}
    (h : Spec.readInt bias 0 (d :: ds) = some (v, rds)) :
    Spec.readDeltas bias first count (d :: ds) =
      (Spec.readDeltas (Spec.adapt v (count + 1) first) false (count + 1) rds).map (v :: ·) := by
  rw [Spec.readDeltas.eq_def]
  simp only []
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
    rfl

/-! ## One step of the code -/

theorem decodeLoop_cons_none {bias n i : Nat} {first : Bool} {out cs : List Char} {c : Char}
    (h : Punycode.decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1
      Punycode.base = none) :
    Punycode.decodeLoop bias first n i out (c :: cs) = none := by
  rw [Punycode.decodeLoop.eq_def]
  simp only []
  split
  · rfl
  · rename_i heq
    rw [h] at heq
    cases heq

theorem decodeLoop_cons_some {bias n i i' : Nat} {first : Bool} {out cs rest : List Char}
    {c : Char}
    (h : Punycode.decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1
      Punycode.base = some (i', rest)) :
    Punycode.decodeLoop bias first n i out (c :: cs) =
      if 0xD800 ≤ n + i' / (out.length + 1) ∧ n + i' / (out.length + 1) ≤ 0xDFFF then none
      else
        Punycode.decodeLoop (Punycode.adapt (i' - i) (out.length + 1) first) false
          (n + i' / (out.length + 1)) (i' % (out.length + 1) + 1)
          (out.insertIdx (i' % (out.length + 1)) (Char.ofNat (n + i' / (out.length + 1)))) rest := by
  rw [Punycode.decodeLoop.eq_def]
  simp only []
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
    rfl

/-! ## Code points that are not digits -/

/-- The code fails when a code point after the literal portion is not a
    digit: it reads them all, or fails before. -/
theorem decodeLoop_of_mapM_none : ∀ (len bias : Nat) (first : Bool) (n i : Nat)
    (out input : List Char), input.length ≤ len → input.mapM Spec.digitValue = none →
    Punycode.decodeLoop bias first n i out input = none
  | _, _, _, _, _, _, [], _, hm => by cases hm
  | 0, _, _, _, _, _, _ :: _, hl, _ => by simp at hl
  | len + 1, bias, first, n, i, out, c :: cs, hl, hm => by
    cases hd : Punycode.decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1
        Punycode.base with
    | none => exact decodeLoop_cons_none hd
    | some r =>
      obtain ⟨i', rest⟩ := r
      rw [decodeLoop_cons_some hd]
      split
      · rfl
      · have hlen := Punycode.decodeInt_length hd
        exact decodeLoop_of_mapM_none len _ _ _ _ _ rest
          (by simp only [List.length_cons] at hlen hl; omega)
          (decodeInt_mapM_none bias _ (c :: cs) i 1 Punycode.base i' rest hd hm)

/-! ## The loop -/

/-- The main loop agrees with the specification, from a state `⟨n, i⟩`
    with `i` at most the length of the string and `n` a code point. -/
theorem decodeLoop_eq : ∀ (len bias : Nat) (first : Bool) (n i : Nat) (out input : List Char),
    input.length ≤ len → i ≤ out.length → n ≤ 0x10FFFF →
    Punycode.decodeLoop bias first n i out input =
      (input.mapM Spec.digitValue).bind fun ds =>
        (Spec.readDeltas bias first out.length ds).bind (Spec.insertAll out (n, i))
  | _, _, _, _, _, out, [], _, _, _ => by
    rw [Punycode.decodeLoop.eq_1, List.mapM_nil]
    show some out = (Spec.readDeltas _ _ out.length []).bind (Spec.insertAll out _)
    rw [Spec.readDeltas.eq_1]
    rfl
  | 0, _, _, _, _, _, _ :: _, hl, _, _ => by simp at hl
  | len + 1, bias, first, n, i, out, c :: cs, hl, hi, hn => by
    cases hm : (c :: cs).mapM Spec.digitValue with
    | none => exact decodeLoop_of_mapM_none (len + 1) bias first n i out (c :: cs) hl hm
    | some ds =>
      obtain ⟨d0, ds', hd0, hm', rfl⟩ := mapM_cons_some hm
      simp only [Option.bind]
      cases hr : Spec.readInt bias 0 (d0 :: ds') with
      | none =>
        rw [readDeltas_of_none hr]
        exact decodeLoop_cons_none
          (decodeInt_of_readInt_none bias _ (c :: cs) (d0 :: ds') i 0 hm hr)
      | some p =>
        obtain ⟨v, rds⟩ := p
        rw [readDeltas_of_some hr]
        by_cases hlim : (0x110000 - n) * (out.length + 1) - 1 < i + v
        · rw [decodeLoop_cons_none (decodeInt_of_gt bias _ (c :: cs) (d0 :: ds') i 0 v rds hm hr hlim)]
          have hbig := (limit_lt_iff n out.length (i + v) hn).mp hlim
          cases Spec.readDeltas (Spec.adapt v (out.length + 1) first) false (out.length + 1) rds with
          | none => rfl
          | some deltas =>
            simp only [Option.map, Option.bind]
            rw [insertAll_step out n i v deltas hi, ite_eq_right]
            unfold Spec.Scalar
            omega
        · obtain ⟨rest, hdi, hrm⟩ :=
            decodeInt_of_le bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) (d0 :: ds') i 0
              v rds hm hr (by omega)
          have hsmall : n + (i + v) / (out.length + 1) < 0x110000 := by
            have h1 := limit_lt_iff n out.length (i + v) hn
            have h2 : ¬ (0x110000 ≤ n + (i + v) / (out.length + 1)) := fun h => hlim (h1.mpr h)
            omega
          rw [decodeLoop_cons_some hdi]
          split
          · rename_i hsur
            cases Spec.readDeltas (Spec.adapt v (out.length + 1) first) false (out.length + 1) rds with
            | none => rfl
            | some deltas =>
              simp only [Option.map, Option.bind]
              rw [insertAll_step out n i v deltas hi, ite_eq_right]
              unfold Spec.Scalar
              omega
          · rename_i hsur
            have hp : (i + v) % (out.length + 1) ≤ out.length :=
              Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
            have hlen := Punycode.decodeInt_length hdi
            rw [decodeLoop_eq len _ _ _ _ _ rest
              (by simp only [List.length_cons] at hlen hl; omega)
              (by rw [List.length_insertIdx_of_le_length hp]; omega)
              (by omega)]
            rw [hrm, Nat.add_sub_cancel_left, adapt_eq, List.length_insertIdx_of_le_length hp]
            simp only [Option.bind]
            cases Spec.readDeltas (Spec.adapt v (out.length + 1) first) false (out.length + 1) rds with
            | none => rfl
            | some deltas =>
              simp only [Option.map, Option.bind]
              rw [insertAll_step out n i v deltas hi, ite_eq_left]
              unfold Spec.Scalar
              omega

/-! ## Lengths -/

/-- Each step of the loop reads at least one code point and inserts
    one. -/
theorem decodeLoop_length : ∀ (len bias : Nat) (first : Bool) (n i : Nat)
    (out input r : List Char), input.length ≤ len →
    Punycode.decodeLoop bias first n i out input = some r → r.length ≤ out.length + input.length
  | _, _, _, _, _, out, [], r, _, h => by
    rw [Punycode.decodeLoop.eq_1] at h
    cases h
    omega
  | 0, _, _, _, _, _, _ :: _, _, hl, _ => by simp at hl
  | len + 1, bias, first, n, i, out, c :: cs, r, hl, h => by
    cases hd : Punycode.decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1
        Punycode.base with
    | none => rw [decodeLoop_cons_none hd] at h; cases h
    | some p =>
      obtain ⟨i', rest⟩ := p
      rw [decodeLoop_cons_some hd] at h
      split at h
      · cases h
      · have hlen := Punycode.decodeInt_length hd
        have hp : i' % (out.length + 1) ≤ out.length :=
          Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
        have ih := decodeLoop_length len _ _ _ _ _ rest r
          (by simp only [List.length_cons] at hlen hl; omega) h
        rw [List.length_insertIdx_of_le_length hp] at ih
        simp only [List.length_cons] at hlen ⊢
        omega

end Punycode.Proofs
