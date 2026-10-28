/-
  The round trip of `encode` and `decode`: decoding an encoding gives the
  code points back, a string decodes to some code points exactly when it
  is their encoding up to the case of its digits, and an encoding is the
  basic code points, a delimiter if there are any, then digits.
-/

import Proofs.RoundTripIns

namespace Punycode.Proofs.Enc

open Punycode

/-! ## The delimiter -/

theorem splitLast_none {l : List Char} (h : splitLast l = none) : '-' ∉ l := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    cases hcs : splitLast cs with
    | some r =>
      obtain ⟨bf, af⟩ := r
      rw [splitLast, hcs] at h
      cases h
    | none =>
      rw [splitLast, hcs] at h
      simp only at h
      split at h
      · cases h
      · rename_i hc
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc e.symm, ih hcs⟩

theorem splitLast_some {l a b : List Char} (h : splitLast l = some (a, b)) :
    l = a ++ '-' :: b ∧ '-' ∉ b := by
  induction l generalizing a b with
  | nil => simp [splitLast] at h
  | cons c cs ih =>
    cases hcs : splitLast cs with
    | some r =>
      obtain ⟨bf, af⟩ := r
      rw [splitLast, hcs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := ih hcs
      exact ⟨by rw [h1]; rfl, h2⟩
    | none =>
      rw [splitLast, hcs] at h
      simp only at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by rw [hc]; rfl, splitLast_none hcs⟩
      · cases h

theorem splitLast_of_not_mem {l : List Char} (h : '-' ∉ l) : splitLast l = none := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    rw [splitLast, ih h.2]
    simp only
    rw [ite_eq_right (fun e => h.1 e.symm)]

theorem splitLast_append {a b : List Char} (hb : '-' ∉ b) :
    splitLast (a ++ '-' :: b) = some (a, b) := by
  induction a with
  | nil =>
    rw [List.nil_append, splitLast, splitLast_of_not_mem hb]
    simp
  | cons c a ih =>
    rw [List.cons_append, splitLast, ih]

theorem dash_not_mem_map_lower {l : List Char} (h : '-' ∉ l) : '-' ∉ l.map Spec.lower := by
  intro hm
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
  rw [(lower_eq_dash_iff x).mp hxe] at hx
  exact h hx

theorem split_of_not_mem {l : List Char} (h : '-' ∉ l) : Spec.split l = some ([], l) := by
  unfold Spec.split
  rw [ite_eq_right h]

theorem split_append {a b : List Char} (hb : '-' ∉ b) :
    Spec.split (a ++ '-' :: b) = if a = [] then none else some (a, b) := by
  unfold Spec.split
  have hmem : '-' ∈ a ++ '-' :: b := by simp
  rw [ite_eq_left hmem]
  have hidx : (a ++ '-' :: b).reverse.idxOf '-' = b.length := by
    rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.idxOf_append, ite_eq_right (by simpa using hb), List.idxOf_cons_self, List.length_reverse,
      Nat.zero_add]
  have hp : (a ++ '-' :: b).length - 1 - b.length = a.length := by
    simp only [List.length_append, List.length_cons]
    omega
  simp only
  rw [hidx, hp]
  by_cases ha : a = []
  · subst ha
    rfl
  · have hlen : a.length ≠ 0 := fun h => ha (List.length_eq_zero_iff.mp h)
    rw [ite_eq_right hlen, ite_eq_right ha, List.take_left' rfl]
    rw [show a ++ '-' :: b = (a ++ ['-']) ++ b by simp, List.drop_left' (by simp)]

/-- `lowerDigits` in terms of `splitLiteral`, and `splitLiteral` of it. -/
theorem lowerDigits_split (l : List Char) :
    Spec.lowerDigits l = (splitLiteral l).1 ++ (if (splitLiteral l).1 = [] then [] else ['-']) ++
        (splitLiteral l).2.map Spec.lower ∧
      splitLiteral (Spec.lowerDigits l) = ((splitLiteral l).1, (splitLiteral l).2.map Spec.lower) := by
  cases hs : splitLast l with
  | none =>
    have hl := splitLast_none hs
    have hsl : splitLiteral l = ([], l) := by unfold splitLiteral; rw [hs]
    have hld : Spec.lowerDigits l = l.map Spec.lower := by
      unfold Spec.lowerDigits; rw [split_of_not_mem hl]
    rw [hsl, hld]
    refine ⟨rfl, ?_⟩
    unfold splitLiteral
    rw [splitLast_of_not_mem (dash_not_mem_map_lower hl)]
  | some r =>
    obtain ⟨a, b⟩ := r
    obtain ⟨hl, hb⟩ := splitLast_some hs
    cases a with
    | nil =>
      have hsl : splitLiteral l = ([], l) := by unfold splitLiteral; rw [hs]
      have hld : Spec.lowerDigits l = l.map Spec.lower := by
        unfold Spec.lowerDigits
        rw [hl, split_append hb, ite_eq_left rfl]
      rw [hsl, hld]
      refine ⟨rfl, ?_⟩
      unfold splitLiteral
      rw [hl, List.nil_append, List.map_cons, lower_dash,
        show '-' :: b.map Spec.lower = [] ++ '-' :: b.map Spec.lower from rfl,
        splitLast_append (dash_not_mem_map_lower hb)]
    | cons c a =>
      have hsl : splitLiteral l = (c :: a, b) := by unfold splitLiteral; rw [hs]
      have hld : Spec.lowerDigits l = (c :: a) ++ '-' :: b.map Spec.lower := by
        unfold Spec.lowerDigits
        rw [hl, split_append hb, ite_eq_right (List.cons_ne_nil c a)]
      rw [hsl, hld]
      refine ⟨by simp, ?_⟩
      unfold splitLiteral
      rw [splitLast_append (dash_not_mem_map_lower hb)]

/-! ## The encoding -/

theorem encodeDeltas_lt (b : Nat) : ∀ (ds : List Nat) (bias : Nat) (first : Bool) (j : Nat),
    ∀ d ∈ encodeDeltas b bias first j ds, d < 36 := by
  intro ds
  induction ds with
  | nil => intro bias first j d hd; simp [encodeDeltas] at hd
  | cons x ds ih =>
    intro bias first j d hd
    rw [encodeDeltas_cons, List.mem_append] at hd
    rcases hd with hd | hd
    · exact encodeInt_lt bias x base d hd
    · exact ih _ _ _ d hd

theorem dash_not_mem_digits (b bias : Nat) (first : Bool) (j : Nat) (ds : List Nat) :
    '-' ∉ (encodeDeltas b bias first j ds).map digitChar := by
  intro hm
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  exact digitChar_ne_dash (encodeDeltas_lt b ds bias first j d hd) he

theorem encode_toList (cs : List Char) : (encode cs).toList =
    cs.filter isBasic ++ (if cs.filter isBasic = [] then [] else ['-']) ++
      (encodeDeltas (cs.filter isBasic).length 72 true 0
        (deltas (cs.filter isBasic).length 128 0 0 (insertions cs))).map digitChar := by
  unfold encode
  rw [String.toList_ofList]
  congr 2
  cases cs.filter isBasic <;> rfl

theorem splitLiteral_form {lit R : List Char} (hR : '-' ∉ R) :
    splitLiteral (lit ++ (if lit = [] then [] else ['-']) ++ R) = (lit, R) := by
  cases lit with
  | nil =>
    rw [ite_eq_left rfl, List.nil_append, List.nil_append]
    unfold splitLiteral
    rw [splitLast_of_not_mem hR]
  | cons c lit =>
    rw [ite_eq_right (List.cons_ne_nil c lit), List.append_assoc, List.singleton_append]
    unfold splitLiteral
    rw [splitLast_append hR]

theorem decode_eq (s : String) : decode s =
    if (splitLiteral s.toList).1.all isBasic then
      decodeLoop 72 true 128 0 (splitLiteral s.toList).1 (splitLiteral s.toList).2
    else none := rfl

/-- Lower-casing the digits of a string does not change what it decodes to. -/
theorem decode_lowerDigits (s : String) :
    decode (String.ofList (Spec.lowerDigits s.toList)) = decode s := by
  rw [decode_eq, decode_eq, String.toList_ofList, (lowerDigits_split s.toList).2]
  by_cases hc : (splitLiteral s.toList).1.all isBasic = true
  · rw [ite_eq_left hc, ite_eq_left hc, decodeLoop_map_lower]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem filter_eq_nil_iff_any (cs : List Char) : cs.filter isBasic = [] ↔ cs.any isBasic = false := by
  rw [List.filter_eq_nil_iff, List.any_eq_false]

end Punycode.Proofs.Enc

namespace Punycode.Proofs

open Punycode Punycode.Proofs.Enc

theorem decode_encode' (cs : List Char) : Punycode.decode (Punycode.encode cs) = some cs := by
  rw [decode_eq, encode_toList, splitLiteral_form (dash_not_mem_digits _ _ _ _ _)]
  have hall : (cs.filter isBasic).all isBasic = true := by
    rw [List.all_eq_true]
    intro x hx
    exact (List.mem_filter.mp hx).2
  rw [ite_eq_left hall]
  obtain ⟨s', hrun, hout, _⟩ := run_insertions 72 true cs
  have := decodeLoop_encodeDeltas (cs.filter isBasic).length _ ⟨72, true, 128, 0, cs.filter isBasic⟩
    s' 0 (by simp) hrun
  rw [hout] at this
  exact this

theorem decode_iff' (s : String) (cs : List Char) :
    Punycode.decode s = some cs ↔ (Punycode.encode cs).toList = Spec.lowerDigits s.toList := by
  constructor
  · intro h
    rw [decode_eq] at h
    by_cases hc : (splitLiteral s.toList).1.all isBasic = true
    · rw [ite_eq_left hc] at h
      obtain ⟨ds, s', hds, hrun, hout⟩ :=
        decodeLoop_inv (splitLiteral s.toList).1.length 72 true 128 0 _ _ 0 cs (by simp) h
      have hlit : ∀ c ∈ (splitLiteral s.toList).1, c.toNat < 128 := by
        intro c hc'
        exact (isBasic_iff c).mp (List.all_eq_true.mp hc c hc')
      have hI := run_unique hlit 72 true ds s' hrun
      have hf := hI.filt
      have hd := hI.dts
      rw [hout] at hf hd
      rw [encode_toList, hf, hd, (lowerDigits_split s.toList).1, ← hds]
    · rw [ite_eq_right hc] at h
      cases h
  · intro h
    rw [← decode_lowerDigits s, ← h, String.ofList_toList]
    exact decode_encode' cs

theorem encode_form' (cs : List Char) :
    ∃ digits, (Punycode.encode cs).toList = cs.filter (fun c => decide (Spec.Basic c)) ++
        (if cs.any (fun c => decide (Spec.Basic c)) then ['-'] else []) ++ digits ∧
      ∀ c ∈ digits, ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') := by
  refine ⟨(encodeDeltas (cs.filter isBasic).length 72 true 0
    (deltas (cs.filter isBasic).length 128 0 0 (insertions cs))).map digitChar, ?_, ?_⟩
  · have hb : (fun c => decide (Spec.Basic c)) = isBasic := rfl
    rw [encode_toList, hb]
    congr 2
    by_cases hany : cs.any isBasic = true
    · have hne : cs.filter isBasic ≠ [] := by
        intro he
        rw [(filter_eq_nil_iff_any cs).mp he] at hany
        cases hany
      rw [ite_eq_right hne, ite_eq_left hany]
    · have he : cs.filter isBasic = [] := (filter_eq_nil_iff_any cs).mpr (by simpa using hany)
      rw [ite_eq_left he, ite_eq_right hany]
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact digitChar_form (encodeDeltas_lt _ _ _ _ _ d hd)

end Punycode.Proofs
