/-
  The decoder's main loop, run on deltas instead of digits.
-/

import Punycode.Proofs.RoundTripNum

namespace Punycode.Proofs.Enc

open Punycode

/-! ## The loop on deltas -/

/-- The state of the decoder's main loop. -/
structure St where
  bias : Nat
  first : Bool
  n : Nat
  i : Nat
  out : List Char

/-- One delta, applied as `decodeLoop` applies it. -/
def step (s : St) (d : Nat) : Option St :=
  if (0x110000 - s.n) * (s.out.length + 1) - 1 < s.i + d then none
  else if 0xD800 ≤ s.n + (s.i + d) / (s.out.length + 1) ∧
      s.n + (s.i + d) / (s.out.length + 1) ≤ 0xDFFF then none
  else some ⟨adapt d (s.out.length + 1) s.first, false, s.n + (s.i + d) / (s.out.length + 1),
    (s.i + d) % (s.out.length + 1) + 1,
    s.out.insertIdx ((s.i + d) % (s.out.length + 1))
      (Char.ofNat (s.n + (s.i + d) / (s.out.length + 1)))⟩

/-- The deltas, applied in turn. -/
def run : St → List Nat → Option St
  | s, [] => some s
  | s, d :: ds => (step s d).bind (fun s' => run s' ds)

theorem run_nil (s : St) : run s [] = some s := rfl

theorem run_cons (s : St) (d : Nat) (ds : List Nat) :
    run s (d :: ds) = (step s d).bind (fun s' => run s' ds) := rfl

theorem run_append (s : St) (xs ys : List Nat) :
    run s (xs ++ ys) = (run s xs).bind (fun s' => run s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons d xs ih =>
    rw [List.cons_append, run_cons, run_cons, Option.bind_assoc]
    congr 1
    funext s'
    exact ih s'

theorem run_single (s : St) (d : Nat) : run s [d] = step s d := by
  rw [run_cons]
  cases step s d <;> rfl

theorem step_eq_some {s s' : St} {d : Nat} (h : step s d = some s') :
    s.i + d ≤ (0x110000 - s.n) * (s.out.length + 1) - 1 ∧
    ¬ (0xD800 ≤ s.n + (s.i + d) / (s.out.length + 1) ∧
      s.n + (s.i + d) / (s.out.length + 1) ≤ 0xDFFF) ∧
    s' = ⟨adapt d (s.out.length + 1) s.first, false, s.n + (s.i + d) / (s.out.length + 1),
      (s.i + d) % (s.out.length + 1) + 1,
      s.out.insertIdx ((s.i + d) % (s.out.length + 1))
        (Char.ofNat (s.n + (s.i + d) / (s.out.length + 1)))⟩ := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      refine ⟨by omega, by assumption, rfl⟩

theorem step_of {s : St} {d : Nat}
    (h1 : s.i + d ≤ (0x110000 - s.n) * (s.out.length + 1) - 1)
    (h2 : ¬ (0xD800 ≤ s.n + (s.i + d) / (s.out.length + 1) ∧
      s.n + (s.i + d) / (s.out.length + 1) ≤ 0xDFFF)) :
    step s d = some ⟨adapt d (s.out.length + 1) s.first, false,
      s.n + (s.i + d) / (s.out.length + 1), (s.i + d) % (s.out.length + 1) + 1,
      s.out.insertIdx ((s.i + d) % (s.out.length + 1))
        (Char.ofNat (s.n + (s.i + d) / (s.out.length + 1)))⟩ := by
  unfold step
  rw [ite_eq_right (by omega), ite_eq_right h2]

/-! ## Unfolding `decodeLoop` -/

theorem decodeLoop_nil (bias : Nat) (first : Bool) (n i : Nat) (out : List Char) :
    decodeLoop bias first n i out [] = some out := by
  rw [decodeLoop]

theorem decodeLoop_of_some {bias : Nat} {first : Bool} {n i : Nat} {out input : List Char}
    {i' : Nat} {rest : List Char} (hne : input ≠ [])
    (h : decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) input i 1 base = some (i', rest)) :
    decodeLoop bias first n i out input =
      if 0xD800 ≤ n + i' / (out.length + 1) ∧ n + i' / (out.length + 1) ≤ 0xDFFF then none
      else decodeLoop (adapt (i' - i) (out.length + 1) first) false (n + i' / (out.length + 1))
          (i' % (out.length + 1) + 1)
          (out.insertIdx (i' % (out.length + 1)) (Char.ofNat (n + i' / (out.length + 1)))) rest := by
  cases input with
  | nil => exact absurd rfl hne
  | cons c cs =>
    rw [decodeLoop]
    split
    · rename_i heq
      rw [h] at heq
      cases heq
    · rename_i i'' rest'' heq
      rw [h] at heq
      cases heq
      rfl

theorem decodeLoop_of_none {bias : Nat} {first : Bool} {n i : Nat} {out input : List Char}
    (hne : input ≠ [])
    (h : decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) input i 1 base = none) :
    decodeLoop bias first n i out input = none := by
  cases input with
  | nil => exact absurd rfl hne
  | cons c cs =>
    rw [decodeLoop]
    split
    · rfl
    · rename_i i'' rest'' heq
      rw [h] at heq
      cases heq

/-! ## Digits in either case -/

theorem decodeLoop_map_lower :
    ∀ (bias : Nat) (first : Bool) (n i : Nat) (out input : List Char),
      decodeLoop bias first n i out (input.map Punycode.Spec.lower) = decodeLoop bias first n i out input := by
  intro bias first n i out input
  induction bias, first, n, i, out, input using decodeLoop.induct with
  | case1 bias first n i out => rfl
  | case2 bias first n i out c cs h =>
    rw [decodeLoop_of_none (by simp) h, decodeLoop_of_none (by simp)]
    rw [decodeInt_map_lower, h]
    rfl
  | case3 bias first n i out c cs i' rest h hs =>
    rw [decodeLoop_of_some (by simp) h, ite_eq_left hs]
    rw [decodeLoop_of_some (by simp) (by rw [decodeInt_map_lower, h]; rfl), ite_eq_left hs]
  | case4 bias first n i out c cs i' rest h hs ih =>
    rw [decodeLoop_of_some (by simp) h, ite_eq_right hs]
    rw [decodeLoop_of_some (by simp) (by rw [decodeInt_map_lower, h]; rfl), ite_eq_right hs]
    exact ih

/-! ## From deltas to digits and back -/

theorem encodeDeltas_cons (b bias : Nat) (first : Bool) (j d : Nat) (ds : List Nat) :
    encodeDeltas b bias first j (d :: ds) =
      encodeInt bias d base ++ encodeDeltas b (adapt d (b + j + 1) first) false (j + 1) ds := rfl

/-- The decoder, on the digits of some deltas, does what `run` does with
    the deltas. -/
theorem decodeLoop_encodeDeltas (b : Nat) :
    ∀ (ds : List Nat) (s s' : St) (j : Nat), s.out.length = b + j → run s ds = some s' →
      decodeLoop s.bias s.first s.n s.i s.out ((encodeDeltas b s.bias s.first j ds).map digitChar) =
        some s'.out := by
  intro ds
  induction ds with
  | nil =>
    intro s s' j _ h
    rw [run_nil] at h
    cases h
    exact decodeLoop_nil _ _ _ _ _
  | cons d ds ih =>
    intro s s' j hlen h
    rw [run_cons] at h
    cases hstep : step s d with
    | none => rw [hstep] at h; cases h
    | some s1 =>
      rw [hstep] at h
      have h' : run s1 ds = some s' := h
      obtain ⟨hlim, hsur, hs1⟩ := step_eq_some hstep
      rw [encodeDeltas_cons, List.map_append]
      have hdec := decodeInt_encodeInt s.bias ((0x110000 - s.n) * (s.out.length + 1) - 1)
        ((encodeDeltas b (adapt d (b + j + 1) s.first) false (j + 1) ds).map digitChar)
        d base s.i 1 (Nat.le_refl 1) (by rw [Nat.mul_one]; exact hlim)
      rw [Nat.mul_one] at hdec
      have hne : (encodeInt s.bias d base).map digitChar ++
          (encodeDeltas b (adapt d (b + j + 1) s.first) false (j + 1) ds).map digitChar ≠ [] := by
        intro he
        have := List.append_eq_nil_iff.mp he
        exact encodeInt_ne_nil s.bias d base (List.map_eq_nil_iff.mp this.1)
      rw [decodeLoop_of_some hne hdec, ite_eq_right hsur, Nat.add_sub_cancel_left]
      have hlen1 : s1.out.length = b + (j + 1) := by
        rw [hs1]
        simp only
        rw [List.length_insertIdx_of_le_length (Nat.le_of_lt_succ (Nat.mod_lt _ (by omega)))]
        omega
      have := ih s1 s' (j + 1) hlen1 h'
      rw [hs1] at this
      simp only at this
      rw [← hlen]
      exact this

/-- What the decoder reads is, up to the case of its digits, the digits
    of some deltas, and it does with them what `run` does. -/
theorem decodeLoop_inv (b : Nat) :
    ∀ (bias : Nat) (first : Bool) (n i : Nat) (out input : List Char) (j : Nat) (cs : List Char),
      out.length = b + j → decodeLoop bias first n i out input = some cs →
      ∃ ds s', input.map Punycode.Spec.lower = (encodeDeltas b bias first j ds).map digitChar ∧
        run ⟨bias, first, n, i, out⟩ ds = some s' ∧ s'.out = cs := by
  intro bias first n i out input
  induction bias, first, n, i, out, input using decodeLoop.induct with
  | case1 bias first n i out =>
    intro j cs _ h
    rw [decodeLoop_nil] at h
    cases h
    exact ⟨[], ⟨bias, first, n, i, out⟩, rfl, rfl, rfl⟩
  | case2 bias first n i out c cs h =>
    intro j cs' _ h'
    rw [decodeLoop_of_none (by simp) h] at h'
    cases h'
  | case3 bias first n i out c cs i' rest h hs =>
    intro j cs' _ h'
    rw [decodeLoop_of_some (by simp) h, ite_eq_left hs] at h'
    cases h'
  | case4 bias first n i out c cs i' rest h hs ih =>
    intro j cs' hlen h'
    rw [decodeLoop_of_some (by simp) h, ite_eq_right hs] at h'
    obtain ⟨pre, q, hcs, hi', hpre, hle⟩ := decodeInt_inv _ _ _ _ _ _ _ _ (Nat.le_refl 1) h
    rw [Nat.mul_one] at hi'
    subst hi'
    have hlen1 : (out.insertIdx ((i + q) % (out.length + 1))
        (Char.ofNat (n + (i + q) / (out.length + 1)))).length = b + (j + 1) := by
      rw [List.length_insertIdx_of_le_length (Nat.le_of_lt_succ (Nat.mod_lt _ (by omega)))]
      omega
    obtain ⟨ds, s', hds, hrun, hout⟩ := ih (j + 1) cs' hlen1 h'
    refine ⟨q :: ds, s', ?_, ?_, hout⟩
    · rw [hcs, List.map_append, hpre, hds, encodeDeltas_cons, List.map_append, Nat.add_sub_cancel_left,
        hlen]
    · rw [run_cons, step_of hle hs]
      rw [Nat.add_sub_cancel_left] at hrun
      exact hrun

end Punycode.Proofs.Enc
