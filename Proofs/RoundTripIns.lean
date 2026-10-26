/-
  The insertions the encoder finds, and the deltas between them: the
  decoder makes exactly those insertions, and no other deltas build the
  same code points.
-/

import Proofs.RoundTripLoop

namespace Punycode.Proofs.Enc

open Punycode

/-! ## `maxPos` -/

/-- `maxPos` gives the greatest value, at its last occurrence, unless
    the accumulator is greater than every value. -/
theorem maxPos_spec : ∀ (cs : List Char) (j v0 p0 : Nat),
    v0 ≤ (maxPos cs j (v0, p0)).1 ∧
    (∀ x ∈ cs, x.toNat ≤ (maxPos cs j (v0, p0)).1) ∧
    ((maxPos cs j (v0, p0) = (v0, p0) ∧ ∀ x ∈ cs, x.toNat < v0) ∨
      ∃ q, ∃ h : q < cs.length, (maxPos cs j (v0, p0)).2 = j + q ∧
        cs[q].toNat = (maxPos cs j (v0, p0)).1 ∧
        ∀ q' (h' : q' < cs.length), cs[q'].toNat = (maxPos cs j (v0, p0)).1 → q' ≤ q) := by
  intro cs
  induction cs with
  | nil =>
    intro j v0 p0
    refine ⟨Nat.le_refl _, by simp, Or.inl ⟨rfl, by simp⟩⟩
  | cons c cs ih =>
    intro j v0 p0
    rw [maxPos]
    split
    · rename_i hle
      obtain ⟨ha, hb, hc⟩ := ih (j + 1) c.toNat j
      refine ⟨Nat.le_trans hle ha, ?_, Or.inr ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact ha
        · exact hb x hx
      · rcases hc with ⟨hr, hlt⟩ | ⟨q, hq, h2, h3, h4⟩
        · refine ⟨0, by simp, by rw [hr, Nat.add_zero], by rw [hr]; rfl, ?_⟩
          intro q' hq' heq
          cases q' with
          | zero => exact Nat.le_refl 0
          | succ k =>
            simp only [List.getElem_cons_succ] at heq
            rw [hr] at heq
            have := hlt _ (List.getElem_mem (by simp at hq'; omega))
            simp only at heq
            omega
        · refine ⟨q + 1, by simp; omega, by rw [h2]; omega, by simpa using h3, ?_⟩
          intro q' hq' heq
          cases q' with
          | zero => omega
          | succ k =>
            simp only [List.getElem_cons_succ] at heq
            have := h4 k (by simp at hq'; omega) heq
            omega
    · rename_i hle
      obtain ⟨ha, hb, hc⟩ := ih (j + 1) v0 p0
      refine ⟨ha, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; omega
        · exact hb x hx
      · rcases hc with ⟨hr, hlt⟩ | ⟨q, hq, h2, h3, h4⟩
        · refine Or.inl ⟨hr, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]; omega
          · exact hlt x hx
        · refine Or.inr ⟨q + 1, by simp; omega, by rw [h2]; omega, by simpa using h3, ?_⟩
          intro q' hq' heq
          cases q' with
          | zero =>
            simp only [List.getElem_cons_zero] at heq
            omega
          | succ k =>
            simp only [List.getElem_cons_succ] at heq
            have := h4 k (by simp at hq'; omega) heq
            omega

theorem maxPos_le (cs : List Char) : ∀ x ∈ cs, x.toNat ≤ (maxPos cs 0 (0, 0)).1 :=
  (maxPos_spec cs 0 0 0).2.1

theorem maxPos_pos {cs : List Char} (h : 0 < (maxPos cs 0 (0, 0)).1) :
    ∃ hp : (maxPos cs 0 (0, 0)).2 < cs.length,
      cs[(maxPos cs 0 (0, 0)).2].toNat = (maxPos cs 0 (0, 0)).1 ∧
      ∀ q (hq : q < cs.length), cs[q].toNat = (maxPos cs 0 (0, 0)).1 → q ≤ (maxPos cs 0 (0, 0)).2 := by
  obtain ⟨_, _, hc⟩ := maxPos_spec cs 0 0 0
  rcases hc with ⟨hr, _⟩ | ⟨q, hq, h2, h3, h4⟩
  · rw [hr] at h; simp at h
  · rw [Nat.zero_add] at h2
    have hq' : (maxPos cs 0 (0, 0)).2 < cs.length := by rw [h2]; exact hq
    refine ⟨hq', ?_, ?_⟩
    · simp only [h2]; exact h3
    · intro q' hq'' heq
      rw [h2]; exact h4 q' hq'' heq

/-- The greatest value at its last occurrence is what `maxPos` finds. -/
theorem maxPos_eq_of {cs : List Char} {v p : Nat} (hp : p < cs.length) (hv : cs[p].toNat = v)
    (hpos : 0 < v) (hall : ∀ x ∈ cs, x.toNat ≤ v)
    (hlast : ∀ q (hq : q < cs.length), cs[q].toNat = v → q ≤ p) :
    maxPos cs 0 (0, 0) = (v, p) := by
  have h1 : v ≤ (maxPos cs 0 (0, 0)).1 := by
    rw [← hv]; exact maxPos_le cs _ (List.getElem_mem hp)
  obtain ⟨hp', h2, h3⟩ := maxPos_pos (Nat.lt_of_lt_of_le hpos h1)
  have h4 : (maxPos cs 0 (0, 0)).1 ≤ v := by
    rw [← h2]; exact hall _ (List.getElem_mem hp')
  have h5 : (maxPos cs 0 (0, 0)).1 = v := Nat.le_antisymm h4 h1
  have h6 := hlast _ hp' (by rw [h2, h5])
  have h7 := h3 p hp (by rw [hv, h5])
  apply Prod.ext
  · exact h5
  · exact Nat.le_antisymm h6 h7

/-! ## `insertions` -/

theorem insertions_of_lt {cs : List Char} (h : (maxPos cs 0 (0, 0)).1 < 128) : insertions cs = [] := by
  rw [insertions, dite_eq_left h]

theorem insertions_of_ge {cs : List Char} (h : ¬ (maxPos cs 0 (0, 0)).1 < 128) :
    insertions cs = insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2) ++ [maxPos cs 0 (0, 0)] := by
  rw [insertions, dite_eq_right h]

theorem isBasic_iff (c : Char) : isBasic c = true ↔ c.toNat < 128 := by
  unfold isBasic
  simp

theorem filter_eraseIdx_of_not_basic {cs : List Char} {p : Nat} (hp : p < cs.length)
    (h : ¬ cs[p].toNat < 128) : (cs.eraseIdx p).filter isBasic = cs.filter isBasic := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => rhs; rw [← List.take_append_drop p cs, List.drop_eq_getElem_cons hp]
  rw [List.filter_append, List.filter_append, List.filter_cons_of_neg (by rw [isBasic_iff]; exact h)]

theorem filter_insertIdx_of_not_basic {c : Char} (h : ¬ c.toNat < 128) :
    ∀ (l : List Char) (p : Nat), (l.insertIdx p c).filter isBasic = l.filter isBasic := by
  intro l
  induction l with
  | nil =>
    intro p
    cases p with
    | zero => rw [List.insertIdx_zero, List.filter_cons_of_neg (by rw [isBasic_iff]; exact h)]
    | succ k => rfl
  | cons a l ih =>
    intro p
    cases p with
    | zero => rw [List.insertIdx_zero, List.filter_cons_of_neg (by rw [isBasic_iff]; exact h)]
    | succ k =>
      rw [List.insertIdx_succ_cons, List.filter_cons, List.filter_cons, ih k]

theorem insertIdx_eraseIdx_getElem {α : Type} : ∀ (l : List α) (p : Nat) (hp : p < l.length),
    (l.eraseIdx p).insertIdx p l[p] = l := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons a l ih =>
    intro p hp
    cases p with
    | zero => rfl
    | succ k =>
      rw [List.eraseIdx_cons_succ, List.insertIdx_succ_cons, List.getElem_cons_succ,
        ih k (by simp at hp; omega)]

theorem filter_of_lt {cs : List Char} (h : (maxPos cs 0 (0, 0)).1 < 128) : cs.filter isBasic = cs := by
  apply List.filter_eq_self.mpr
  intro a ha
  rw [isBasic_iff]
  exact Nat.lt_of_le_of_lt (maxPos_le cs a ha) h

/-- One insertion per code point that is not basic. -/
theorem length_insertions (cs : List Char) :
    (cs.filter isBasic).length + (insertions cs).length = cs.length := by
  induction cs using insertions.induct with
  | case1 cs h =>
    rw [insertions_of_lt h, filter_of_lt h]
    rfl
  | case2 cs h ih =>
    obtain ⟨hp, hv, _⟩ := maxPos_pos (cs := cs) (by omega)
    rw [insertions_of_ge h, List.length_append, List.length_singleton]
    rw [filter_eraseIdx_of_not_basic hp (by rw [hv]; exact h), List.length_eraseIdx_of_lt hp] at ih
    have : cs.length ≠ 0 := by omega
    omega

/-! ## Deltas -/

/-- The state after a list of insertions, from state `s`. -/
def lastSt : Nat × Nat → List (Nat × Nat) → Nat × Nat
  | s, [] => s
  | _, x :: rest => lastSt (x.1, x.2 + 1) rest

theorem lastSt_append_single (s : Nat × Nat) (xs : List (Nat × Nat)) (x : Nat × Nat) :
    lastSt s (xs ++ [x]) = (x.1, x.2 + 1) := by
  induction xs generalizing s with
  | nil => rfl
  | cons y xs ih => exact ih _

theorem deltas_append (b : Nat) : ∀ (xs ys : List (Nat × Nat)) (pn pi j : Nat),
    deltas b pn pi j (xs ++ ys) =
      deltas b pn pi j xs ++
        deltas b (lastSt (pn, pi) xs).1 (lastSt (pn, pi) xs).2 (j + xs.length) ys := by
  intro xs ys
  induction xs with
  | nil => intro pn pi j; rfl
  | cons x xs ih =>
    intro pn pi j
    obtain ⟨n, i⟩ := x
    show _ :: deltas b n (i + 1) (j + 1) (xs ++ ys) = _ :: _
    rw [ih]
    congr 3
    simp only [List.length_cons]
    omega

theorem deltas_single (b pn pi j : Nat) (x : Nat × Nat) :
    deltas b pn pi j [x] = [x.1 * (b + j + 1) + x.2 - (pn * (b + j + 1) + pi)] := by
  obtain ⟨n, i⟩ := x
  rfl

theorem length_deltas (b : Nat) : ∀ (xs : List (Nat × Nat)) (pn pi j : Nat),
    (deltas b pn pi j xs).length = xs.length := by
  intro xs
  induction xs with
  | nil => intro pn pi j; rfl
  | cons x xs ih =>
    intro pn pi j
    obtain ⟨n, i⟩ := x
    show (deltas b n (i + 1) (j + 1) xs).length + 1 = xs.length + 1
    rw [ih]

/-! ## One insertion -/

/-- The delta from state `⟨s.n, s.i⟩` to `⟨v, p⟩` takes the decoder there. -/
theorem step_insert {s : St} {v p : Nat} (hp : p ≤ s.out.length) (hi : s.i ≤ s.out.length)
    (hnv : s.n ≤ v) (heq : s.n = v → s.i ≤ p) (hv : v < 0x110000)
    (hs : ¬ (0xD800 ≤ v ∧ v ≤ 0xDFFF)) :
    ∃ s', step s (v * (s.out.length + 1) + p - (s.n * (s.out.length + 1) + s.i)) = some s' ∧
      s'.n = v ∧ s'.i = p + 1 ∧ s'.out = s.out.insertIdx p (Char.ofNat v) := by
  have hst := step_of (s := s) (d := v * (s.out.length + 1) + p - (s.n * (s.out.length + 1) + s.i))
  generalize s.out.length = L at *
  have hL : 0 < L + 1 := by omega
  -- `v = s.n + e`
  obtain ⟨e, rfl⟩ : ∃ e, v = s.n + e := ⟨v - s.n, by omega⟩
  have hmul : (s.n + e) * (L + 1) = s.n * (L + 1) + e * (L + 1) := Nat.add_mul _ _ _
  have hge : s.i ≤ e * (L + 1) + p := by
    cases e with
    | zero => have := heq (by omega); omega
    | succ e =>
      have : L + 1 ≤ (e + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have hsum : s.i + ((s.n + e) * (L + 1) + p - (s.n * (L + 1) + s.i)) = p + e * (L + 1) := by
    omega
  have hdiv : (p + e * (L + 1)) / (L + 1) = e := by
    rw [Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmod : (p + e * (L + 1)) % (L + 1) = p := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hlim : p + e * (L + 1) ≤ (0x110000 - s.n) * (L + 1) - 1 := by
    have : (e + 1) * (L + 1) ≤ (0x110000 - s.n) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  rw [hsum, hdiv, hmod] at hst
  exact ⟨_, hst hlim hs, rfl, rfl, rfl⟩

/-- Against the last insertion of `cs`, the state after the insertions
    before it: not past it in the order of states. -/
theorem prev_facts {cs : List Char} (h : ¬ (maxPos cs 0 (0, 0)).1 < 128) :
    (lastSt (128, 0) (insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2))).1 ≤ (maxPos cs 0 (0, 0)).1 ∧
    (lastSt (128, 0) (insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2))).2 ≤
      (cs.eraseIdx (maxPos cs 0 (0, 0)).2).length ∧
    ((lastSt (128, 0) (insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2))).1 = (maxPos cs 0 (0, 0)).1 →
      (lastSt (128, 0) (insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2))).2 ≤ (maxPos cs 0 (0, 0)).2) := by
  obtain ⟨hp, hv, hlast⟩ := maxPos_pos (cs := cs) (by omega)
  have hall := maxPos_le cs
  generalize maxPos cs 0 (0, 0) = m at *
  by_cases h' : (maxPos (cs.eraseIdx m.2) 0 (0, 0)).1 < 128
  · rw [insertions_of_lt h']
    refine ⟨by simp only [lastSt]; omega, by simp only [lastSt]; omega, fun _ => by simp only [lastSt]; omega⟩
  · rw [insertions_of_ge h', lastSt_append_single]
    obtain ⟨hp', hv', _⟩ := maxPos_pos (cs := cs.eraseIdx m.2) (by omega)
    generalize maxPos (cs.eraseIdx m.2) 0 (0, 0) = m' at *
    have hlen := List.length_eraseIdx_of_lt hp
    rw [List.getElem_eraseIdx] at hv'
    split at hv'
    · refine ⟨by rw [← hv']; exact hall _ (List.getElem_mem _), by omega, fun _ => by omega⟩
    · refine ⟨by rw [← hv']; exact hall _ (List.getElem_mem _), by omega, fun heq => ?_⟩
      have := hlast (m'.2 + 1) (by omega) (by rw [hv', heq])
      omega

/-! ## The round trip -/

/-- From the basic code points, the deltas of `insertions cs` build `cs`. -/
theorem run_insertions (bias : Nat) (first : Bool) (cs : List Char) :
    ∃ s', run ⟨bias, first, 128, 0, cs.filter isBasic⟩
        (deltas (cs.filter isBasic).length 128 0 0 (insertions cs)) = some s' ∧
      s'.out = cs ∧ (s'.n, s'.i) = lastSt (128, 0) (insertions cs) := by
  induction cs using insertions.induct with
  | case1 cs h =>
    rw [insertions_of_lt h]
    exact ⟨_, rfl, filter_of_lt h, rfl⟩
  | case2 cs h ih =>
    obtain ⟨hp, hv, hlast⟩ := maxPos_pos (cs := cs) (by omega)
    have hfilter := filter_eraseIdx_of_not_basic hp (by rw [hv]; exact h)
    have hlen := length_insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2)
    have hprev := prev_facts h
    have hlen' := List.length_eraseIdx_of_lt hp
    rw [hfilter] at ih hlen
    obtain ⟨s0, hrun, hout, hst⟩ := ih
    rw [insertions_of_ge h, deltas_append, run_append, hrun, Option.bind_some, deltas_single,
      run_single, lastSt_append_single]
    rw [← hst] at hprev ⊢
    rw [← hout] at hprev hlen'
    simp only at hprev ⊢
    have hL : (cs.filter isBasic).length + (0 + (insertions (cs.eraseIdx (maxPos cs 0 (0, 0)).2)).length) =
        s0.out.length := by rw [hout]; omega
    rw [hL]
    obtain ⟨s', hstep, hn, hi, hout'⟩ := step_insert (s := s0) (v := (maxPos cs 0 (0, 0)).1)
      (p := (maxPos cs 0 (0, 0)).2) (by omega) hprev.2.1 hprev.1 hprev.2.2
      (by rw [← hv]; exact char_lt _) (by rw [← hv]; exact char_not_surrogate _)
    refine ⟨s', hstep, ?_, ?_⟩
    · rw [hout', hout]
      conv => lhs; rw [← hv, Char.ofNat_toNat]
      exact insertIdx_eraseIdx_getElem cs _ hp
    · rw [hn, hi]

/-! ## Uniqueness -/

/-- What holds of the decoder's state after the deltas `ds`, from the
    literal portion `lit`. -/
structure Inv (lit : List Char) (ds : List Nat) (s : St) : Prop where
  len : s.out.length = lit.length + ds.length
  filt : s.out.filter isBasic = lit
  dts : deltas lit.length 128 0 0 (insertions s.out) = ds
  last : lastSt (128, 0) (insertions s.out) = (s.n, s.i)
  nlo : 128 ≤ s.n
  nhi : s.n < 0x110000
  le : ∀ x ∈ s.out, x.toNat ≤ s.n
  lt : ∀ q (hq : q < s.out.length), s.out[q].toNat = s.n → q < s.i
  ile : s.i ≤ s.out.length

theorem inv_init {lit : List Char} (hlit : ∀ c ∈ lit, c.toNat < 128) (bias : Nat) (first : Bool) :
    Inv lit [] ⟨bias, first, 128, 0, lit⟩ := by
  have hmax : (maxPos lit 0 (0, 0)).1 < 128 := by
    obtain ⟨_, _, hc⟩ := maxPos_spec lit 0 0 0
    rcases hc with ⟨hr, _⟩ | ⟨q, hq, _, h3, _⟩
    · rw [hr]; decide
    · rw [← h3]; exact hlit _ (List.getElem_mem hq)
  refine ⟨rfl, ?_, ?_, ?_, Nat.le_refl _, by show 128 < 0x110000; omega, ?_, ?_, Nat.zero_le _⟩
  · exact filter_of_lt hmax
  · simp only; rw [insertions_of_lt hmax]; rfl
  · simp only; rw [insertions_of_lt hmax]; rfl
  · intro x hx; exact Nat.le_of_lt (hlit x hx)
  · intro q hq heq
    simp only at hq heq ⊢
    have := hlit _ (List.getElem_mem hq)
    omega

theorem inv_step {lit : List Char} {ds : List Nat} {s s' : St} {d : Nat} (hI : Inv lit ds s)
    (h : step s d = some s') : Inv lit (ds ++ [d]) s' := by
  obtain ⟨hlim, hsur, rfl⟩ := step_eq_some h
  have hL0 : 0 < s.out.length + 1 := by omega
  have hpL : (s.i + d) % (s.out.length + 1) < s.out.length + 1 := Nat.mod_lt _ hL0
  have hnhi := hI.nhi
  have hpos : 0 < (0x110000 - s.n) * (s.out.length + 1) := Nat.mul_pos (by omega) hL0
  have hq : (s.i + d) / (s.out.length + 1) < 0x110000 - s.n :=
    (Nat.div_lt_iff_lt_mul hL0).mpr (by omega)
  have hdm := Nat.div_add_mod (s.i + d) (s.out.length + 1)
  generalize (s.i + d) / (s.out.length + 1) = e at *
  generalize (s.i + d) % (s.out.length + 1) = p at *
  have hv : s.n + e < 0x110000 := by omega
  have hc : (Char.ofNat (s.n + e)).toNat = s.n + e := toNat_ofNat_of_lt hv hsur
  have hlen : (s.out.insertIdx p (Char.ofNat (s.n + e))).length = s.out.length + 1 :=
    List.length_insertIdx_of_le_length (by omega) _
  -- the inserted code point is the greatest, at its last occurrence
  have hall : ∀ x ∈ s.out.insertIdx p (Char.ofNat (s.n + e)), x.toNat ≤ s.n + e := by
    intro x hx
    rcases (List.mem_insertIdx (by omega)).mp hx with hx | hx
    · rw [hx, hc]; exact Nat.le_refl _
    · have := hI.le x hx; omega
  have hlast : ∀ q (hq : q < (s.out.insertIdx p (Char.ofNat (s.n + e))).length),
      (s.out.insertIdx p (Char.ofNat (s.n + e)))[q].toNat = s.n + e → q ≤ p := by
    intro q hq heq
    rcases Nat.lt_or_ge p q with hgt | hle
    · rw [List.getElem_insertIdx_of_gt hgt] at heq
      have h1 := hI.le _ (List.getElem_mem (by omega : q - 1 < s.out.length))
      have he : e = 0 := by omega
      subst he
      rw [Nat.mul_zero, Nat.zero_add] at hdm
      have h2 := hI.lt (q - 1) (by omega) (by omega)
      omega
    · exact hle
  have hmax : maxPos (s.out.insertIdx p (Char.ofNat (s.n + e))) 0 (0, 0) = (s.n + e, p) :=
    maxPos_eq_of (by omega) (by rw [List.getElem_insertIdx_self, hc]) (by have := hI.nlo; omega)
      hall hlast
  have hins : insertions (s.out.insertIdx p (Char.ofNat (s.n + e))) =
      insertions s.out ++ [(s.n + e, p)] := by
    rw [insertions_of_ge (by rw [hmax]; have := hI.nlo; omega), hmax, List.eraseIdx_insertIdx_self]
  have hlenins : (insertions s.out).length = ds.length := by
    rw [← length_deltas lit.length (insertions s.out) 128 0 0, hI.dts]
  refine ⟨?_, ?_, ?_, ?_, ?_, hv, hall, ?_, ?_⟩
  · simp only
    rw [hlen, hI.len, List.length_append, List.length_singleton, Nat.add_assoc]
  · simp only
    rw [filter_insertIdx_of_not_basic (by rw [hc]; have := hI.nlo; omega), hI.filt]
  · simp only
    rw [hins, deltas_append, hI.dts, hI.last, deltas_single]
    simp only
    have hL : lit.length + (0 + (insertions s.out).length) = s.out.length := by
      rw [hlenins, hI.len]; omega
    rw [hL, Nat.add_mul, Nat.mul_comm e]
    congr 2
    omega
  · simp only
    rw [hins, lastSt_append_single]
  · simp only
    have := hI.nlo
    omega
  · intro q hq heq
    have := hlast q hq heq
    simp only
    omega
  · simp only
    rw [hlen]
    omega

theorem rev_induction {α : Type} {P : List α → Prop} (h0 : P []) (h1 : ∀ l a, P l → P (l ++ [a])) :
    ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons a l ih =>
    rw [List.reverse_cons]
    exact h1 _ _ ih

/-- The deltas that build some code points from their literal portion
    are the deltas of the encoder. -/
theorem run_unique {lit : List Char} (hlit : ∀ c ∈ lit, c.toNat < 128) (bias : Nat) (first : Bool) :
    ∀ ds s', run ⟨bias, first, 128, 0, lit⟩ ds = some s' → Inv lit ds s' := by
  refine rev_induction (P := fun ds => ∀ s', run ⟨bias, first, 128, 0, lit⟩ ds = some s' → Inv lit ds s')
    ?_ ?_
  · intro s' h
    rw [run_nil] at h
    cases h
    exact inv_init hlit bias first
  · intro ds d ih s' h
    rw [run_append] at h
    cases hr : run ⟨bias, first, 128, 0, lit⟩ ds with
    | none => rw [hr] at h; cases h
    | some s =>
      rw [hr, Option.bind_some, run_single] at h
      exact inv_step (ih s hr) h

end Punycode.Proofs.Enc
