import Punycode.Proofs.DecodeBasic

/-!
  The code's `decodeInt` reads the same variable-length integers as the
  specification's `readInt`, and fails exactly when the sum passes the
  limit, the digits run out, or a code point that is not a digit comes
  before the integer ends.
-/

set_option linter.unusedSimpArgs false

namespace Punycode.Proofs

/-! ## `mapM` in `Option` -/

theorem mapM_cons_opt {α β : Type} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).mapM f = (f a).bind (fun b => (l.mapM f).map (b :: ·)) := by
  rw [List.mapM_cons]
  cases f a <;> cases l.mapM f <;> rfl

theorem mapM_cons_of_some {α β : Type} {f : α → Option β} {a : α} {b : β} (l : List α)
    (h : f a = some b) : (a :: l).mapM f = (l.mapM f).map (b :: ·) := by
  rw [mapM_cons_opt, h]
  rfl

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {r : List β}
    (h : (a :: l).mapM f = some r) :
    ∃ b bs, f a = some b ∧ l.mapM f = some bs ∧ r = b :: bs := by
  rw [mapM_cons_opt] at h
  cases hb : f a with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hbs : l.mapM f with
    | none => rw [hbs] at h; cases h
    | some bs =>
      rw [hbs] at h
      cases h
      exact ⟨b, bs, rfl, rfl, rfl⟩

theorem mapM_cons_none {α β : Type} {f : α → Option β} {a : α} {l : List α} {b : β}
    (h : (a :: l).mapM f = none) (hb : f a = some b) : l.mapM f = none := by
  rw [mapM_cons_of_some l hb] at h
  cases hbs : l.mapM f with
  | none => rfl
  | some bs => rw [hbs] at h; cases h

theorem mapM_eq_none_of_none {α β : Type} {f : α → Option β} {a : α} (l : List α)
    (h : f a = none) : (a :: l).mapM f = none := by
  rw [mapM_cons_opt, h]
  rfl

/-! ## One digit -/

theorem w_succ (bias j : Nat) :
    Punycode.Spec.w bias j * (Punycode.base - Punycode.Spec.t bias j) = Punycode.Spec.w bias (j + 1) := rfl

theorem k_succ (j : Nat) :
    Punycode.base * (j + 1) + Punycode.base = Punycode.base * (j + 1 + 1) := by
  simp only [Punycode.base]; omega

/-- One step of `decodeInt`, at digit `j`, written with the
    specification's thresholds and weights. -/
theorem decodeInt_cons_digit (bias limit : Nat) {c : Char} {d : Nat} (cs : List Char)
    (i j : Nat) (h : Punycode.Spec.digitValue c = some d) :
    Punycode.decodeInt bias limit (c :: cs) i (Punycode.Spec.w bias j) (Punycode.base * (j + 1)) =
      if limit < i + d * Punycode.Spec.w bias j then none
      else if d < Punycode.Spec.t bias j then some (i + d * Punycode.Spec.w bias j, cs)
      else Punycode.decodeInt bias limit cs (i + d * Punycode.Spec.w bias j) (Punycode.Spec.w bias (j + 1))
        (Punycode.base * (j + 1 + 1)) := by
  rw [Punycode.decodeInt, digitValue_eq, h]
  simp only []
  rw [threshold_eq, w_succ, k_succ]

theorem readInt_cons (bias j d : Nat) (ds : List Nat) :
    Punycode.Spec.readInt bias j (d :: ds) =
      if d < Punycode.Spec.t bias j then some (d * Punycode.Spec.w bias j, ds)
      else (Punycode.Spec.readInt bias (j + 1) ds).map fun r => (d * Punycode.Spec.w bias j + r.1, r.2) := by
  rw [Punycode.Spec.readInt]

/-! ## The three outcomes -/

/-- When the digits end before the integer does, so does `decodeInt`. -/
theorem decodeInt_of_readInt_none (bias limit : Nat) :
    ∀ (cs : List Char) (ds : List Nat) (i j : Nat),
      cs.mapM Punycode.Spec.digitValue = some ds → Punycode.Spec.readInt bias j ds = none →
      Punycode.decodeInt bias limit cs i (Punycode.Spec.w bias j) (Punycode.base * (j + 1)) = none
  | [], _, _, _, _, _ => rfl
  | c :: cs, ds, i, j, hm, hr => by
    obtain ⟨d, ds', hd, hm', rfl⟩ := mapM_cons_some hm
    rw [decodeInt_cons_digit bias limit cs i j hd]
    rw [readInt_cons] at hr
    split
    · rfl
    · split at hr
      · cases hr
      · rw [ite_eq_right ‹¬d < Punycode.Spec.t bias j›]
        have hr' : Punycode.Spec.readInt bias (j + 1) ds' = none := by
          cases h : Punycode.Spec.readInt bias (j + 1) ds' with
          | none => rfl
          | some r => rw [h] at hr; cases hr
        exact decodeInt_of_readInt_none bias limit cs ds' _ (j + 1) hm' hr'

/-- When the sum passes the limit, `decodeInt` fails. -/
theorem decodeInt_of_gt (bias limit : Nat) :
    ∀ (cs : List Char) (ds : List Nat) (i j v : Nat) (rds : List Nat),
      cs.mapM Punycode.Spec.digitValue = some ds → Punycode.Spec.readInt bias j ds = some (v, rds) →
      limit < i + v →
      Punycode.decodeInt bias limit cs i (Punycode.Spec.w bias j) (Punycode.base * (j + 1)) = none
  | [], _, _, _, _, _, hm, hr, _ => by
    cases hm; simp [Punycode.Spec.readInt] at hr
  | c :: cs, ds, i, j, v, rds, hm, hr, hl => by
    obtain ⟨d, ds', hd, hm', rfl⟩ := mapM_cons_some hm
    rw [decodeInt_cons_digit bias limit cs i j hd]
    rw [readInt_cons] at hr
    split
    · rfl
    · split at hr
      · cases hr
        omega
      · rw [ite_eq_right ‹¬d < Punycode.Spec.t bias j›]
        cases h : Punycode.Spec.readInt bias (j + 1) ds' with
        | none => rw [h] at hr; cases hr
        | some r =>
          rw [h] at hr
          cases hr
          exact decodeInt_of_gt bias limit cs ds' _ (j + 1) r.1 r.2 hm' h (by omega)

/-- When the sum stays within the limit, `decodeInt` reads the integer
    and leaves the code points of the digits after it. -/
theorem decodeInt_of_le (bias limit : Nat) :
    ∀ (cs : List Char) (ds : List Nat) (i j v : Nat) (rds : List Nat),
      cs.mapM Punycode.Spec.digitValue = some ds → Punycode.Spec.readInt bias j ds = some (v, rds) →
      i + v ≤ limit →
      ∃ rest, Punycode.decodeInt bias limit cs i (Punycode.Spec.w bias j) (Punycode.base * (j + 1)) =
        some (i + v, rest) ∧ rest.mapM Punycode.Spec.digitValue = some rds
  | [], _, _, _, _, _, hm, hr, _ => by
    cases hm; simp [Punycode.Spec.readInt] at hr
  | c :: cs, ds, i, j, v, rds, hm, hr, hl => by
    obtain ⟨d, ds', hd, hm', rfl⟩ := mapM_cons_some hm
    rw [decodeInt_cons_digit bias limit cs i j hd]
    rw [readInt_cons] at hr
    split at hr
    · cases hr
      rw [ite_eq_right (by omega), ite_eq_left ‹d < Punycode.Spec.t bias j›]
      exact ⟨cs, rfl, hm'⟩
    · cases h : Punycode.Spec.readInt bias (j + 1) ds' with
      | none => rw [h] at hr; cases hr
      | some r =>
        rw [h] at hr
        cases hr
        rw [ite_eq_right (by omega), ite_eq_right ‹¬d < Punycode.Spec.t bias j›]
        obtain ⟨rest, h1, h2⟩ :=
          decodeInt_of_le bias limit cs ds' (i + d * Punycode.Spec.w bias j) (j + 1) r.1 r.2 hm' h (by omega)
        refine ⟨rest, ?_, h2⟩
        rw [h1, Nat.add_assoc]

/-- `decodeInt` reads its digits one by one: what it leaves still holds
    every code point that is not a digit. -/
theorem decodeInt_mapM_none (bias limit : Nat) :
    ∀ (cs : List Char) (i w k v : Nat) (rest : List Char),
      Punycode.decodeInt bias limit cs i w k = some (v, rest) →
      cs.mapM Punycode.Spec.digitValue = none → rest.mapM Punycode.Spec.digitValue = none
  | [], _, _, _, _, _, h, _ => by simp [Punycode.decodeInt] at h
  | c :: cs, i, w, k, v, rest, h, hm => by
    rw [Punycode.decodeInt, digitValue_eq] at h
    cases hd : Punycode.Spec.digitValue c with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      simp only [] at h
      have hm' := mapM_cons_none hm hd
      split at h
      · cases h
      · split at h
        · cases h; exact hm'
        · exact decodeInt_mapM_none bias limit cs _ _ _ v rest h hm'

end Punycode.Proofs
