import Proofs.DecodeLoop

/-!
  The decoder: `Punycode.decode` computes `Spec.decode`, and never gives
  more code points than its input has.

  - `Proofs/DecodeBasic.lean`: digits, thresholds and bias adaptation.
  - `Proofs/DecodeInt.lean`: variable-length integers.
  - `Proofs/DecodeLoop.lean`: the main loop against `readDeltas` and
    `insertAll`.
  - This file: the split at the last delimiter, and the two theorems.
-/

set_option linter.unusedSimpArgs false

namespace Punycode.Proofs

/-! ## The last delimiter -/

theorem idxOf_decomp (x : Char) : ∀ (l : List Char), x ∈ l →
    ∃ pre post, l = pre ++ x :: post ∧ x ∉ pre ∧ l.idxOf x = pre.length
  | [], h => by cases h
  | c :: l, h => by
    rw [List.idxOf_cons]
    by_cases hc : c = x
    · subst hc
      refine ⟨[], l, rfl, List.not_mem_nil, ?_⟩
      rw [ite_eq_left (beq_self_eq_true c)]
      rfl
    · have hx : x ∈ l := by
        cases h with
        | head => exact absurd rfl hc
        | tail _ h => exact h
      obtain ⟨pre, post, h1, h2, h3⟩ := idxOf_decomp x l hx
      refine ⟨c :: pre, post, by rw [h1]; rfl, ?_, ?_⟩
      · intro hm
        cases hm with
        | head => exact hc rfl
        | tail _ hm => exact h2 hm
      · rw [ite_eq_right (fun hb => hc (beq_iff_eq.mp hb)), h3]
        rfl

theorem splitLast_of_not_mem : ∀ (l : List Char), '-' ∉ l → Punycode.splitLast l = none
  | [], _ => rfl
  | c :: l, h => by
    rw [Punycode.splitLast, splitLast_of_not_mem l (fun hm => h (List.mem_cons_of_mem c hm))]
    simp only []
    refine ite_eq_right fun hc => h ?_
    subst hc
    exact List.mem_cons_self

theorem splitLast_append (a : List Char) (ha : '-' ∉ a) :
    ∀ (b : List Char), Punycode.splitLast (b ++ '-' :: a) = some (b, a)
  | [] => by
    rw [List.nil_append, Punycode.splitLast, splitLast_of_not_mem a ha]
    rfl
  | c :: b => by
    rw [List.cons_append, Punycode.splitLast, splitLast_append a ha b]

theorem splitLast_some : ∀ (l b a : List Char), Punycode.splitLast l = some (b, a) →
    l = b ++ '-' :: a
  | [], _, _, h => by cases h
  | c :: l, b, a, h => by
    rw [Punycode.splitLast] at h
    cases h' : Punycode.splitLast l with
    | some r =>
      obtain ⟨b', a'⟩ := r
      rw [h'] at h
      cases h
      rw [splitLast_some l b' a h']
      rfl
    | none =>
      rw [h'] at h
      simp only [] at h
      split at h
      · rename_i hc
        cases h
        rw [hc]
        rfl
      · cases h

/-- The last delimiter, as `Spec.split` finds it. -/
theorem last_decomp (l : List Char) (h : '-' ∈ l) :
    ∃ b a, l = b ++ '-' :: a ∧ '-' ∉ a ∧ l.length - 1 - l.reverse.idxOf '-' = b.length := by
  obtain ⟨pre, post, h1, h2, h3⟩ := idxOf_decomp '-' l.reverse (List.mem_reverse.mpr h)
  have hl : l = post.reverse ++ '-' :: pre.reverse := by
    rw [← List.reverse_reverse l, h1, List.reverse_append, List.reverse_cons, List.append_assoc]
    rfl
  refine ⟨post.reverse, pre.reverse, hl, fun hm => h2 (List.mem_reverse.mp hm), ?_⟩
  rw [h3, hl]
  simp only [List.length_append, List.length_reverse, List.length_cons]
  omega

/-- The code's split agrees with the specification's, except when the
    last delimiter comes first: then the specification fails, and the
    code reads the delimiter as a digit. -/
theorem split_cases (l : List Char) :
    (∃ lit rest, Punycode.splitLiteral l = (lit, rest) ∧ Spec.split l = some (lit, rest)) ∨
    (∃ a, l = '-' :: a ∧ Punycode.splitLiteral l = ([], l) ∧ Spec.split l = none) := by
  by_cases h : '-' ∈ l
  · obtain ⟨b, a, hl, ha, hp⟩ := last_decomp l h
    have hs : Punycode.splitLast l = some (b, a) := by rw [hl]; exact splitLast_append a ha b
    unfold Punycode.splitLiteral Spec.split
    rw [hs, ite_eq_left h]
    dsimp only
    rw [hp]
    cases b with
    | nil =>
      right
      exact ⟨a, hl, rfl, rfl⟩
    | cons c b =>
      left
      refine ⟨c :: b, a, rfl, ?_⟩
      rw [ite_eq_right (by simp), hl, List.take_left' rfl]
      rw [show (c :: b).length + 1 = (c :: b ++ ['-']).length by simp,
        show c :: b ++ '-' :: a = (c :: b ++ ['-']) ++ a by simp, List.drop_left' rfl]
  · left
    refine ⟨[], l, ?_, ?_⟩
    · unfold Punycode.splitLiteral
      rw [splitLast_of_not_mem l h]
    · unfold Spec.split
      rw [ite_eq_right h]

theorem splitLiteral_length (l : List Char) :
    (Punycode.splitLiteral l).1.length + (Punycode.splitLiteral l).2.length ≤ l.length := by
  unfold Punycode.splitLiteral
  split
  · rename_i c before after heq
    rw [splitLast_some l _ _ heq]
    simp only [List.length_append, List.length_cons]
    omega
  · simp

/-! ## The theorems -/

theorem decode_eq' (s : String) : Punycode.decode s = Spec.decode s.toList := by
  unfold Punycode.decode Spec.decode
  rcases split_cases s.toList with ⟨lit, rest, h1, h2⟩ | ⟨a, ha, h1, h2⟩
  · rw [h1, h2]
    dsimp only
    by_cases hb : ∀ c ∈ lit, Spec.Basic c
    · rw [ite_eq_left ((all_isBasic_iff lit).mpr hb), ite_eq_left hb,
        decodeLoop_eq rest.length _ _ _ _ _ _ (Nat.le_refl _) (Nat.zero_le _) (by decide),
        initialBias_eq, initialN_eq]
      cases rest.mapM Spec.digitValue with
      | none => rfl
      | some ds =>
        simp only [Option.bind]
        cases Spec.readDeltas Spec.initialBias true lit.length ds <;> rfl
    · rw [ite_eq_right (fun h => hb ((all_isBasic_iff lit).mp h)), ite_eq_right hb]
  · rw [h1, h2]
    dsimp only
    rw [ite_eq_left (by rfl : ([] : List Char).all Punycode.isBasic = true), ha]
    exact decodeLoop_of_mapM_none _ _ _ _ _ _ _ (Nat.le_refl _)
      (mapM_eq_none_of_none a (by rfl))

theorem decode_length' (s : String) (cs : List Char) (h : Punycode.decode s = some cs) :
    cs.length ≤ s.length := by
  unfold Punycode.decode at h
  split at h
  · have h1 := decodeLoop_length _ _ _ _ _ _ _ cs (Nat.le_refl _) h
    have h2 := splitLiteral_length s.toList
    rw [← String.length_toList]
    omega
  · cases h

end Punycode.Proofs
