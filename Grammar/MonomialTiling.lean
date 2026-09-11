/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StripNormalisation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Exact-monomial rectangular extraction (Astra #68 unit 4a)

On a box `[-r, r]^m` with the **exact monomial phase** `∏_j u_j^{2k_j}` the region near the divisor
tiles, up to a positive phase gap, into finitely many **monomial cores**: sets on which one
coordinate `i` of a stratum `S` is rescaled by the tangential monomial
`q_S(u)^{1/k_i}`, `q_S(u) = ∏_{j ∉ S} |u_j|^{k_j}` (`coreMap`), so that

* the phase is exactly `∏_{j ∈ S} w_j^{2k_j}` in the rescaled coordinates `w = coreMap u`
  (`normalPhase_eq_prod_coreMap`), and
* the core is a product `B ∩ {|w_j| ≤ b (j ≠ i), |w_i| ≤ b q_min^{1/k_i}}` of a tangential base
  `B` (measurable, `S`-cylindrical, on which `q_S ≥ q_min > 0`) with a normal box.

The engine is a single induction on the number of remaining normal coordinates with the
**weighted-product invariant** `q_S ≥ q_min` on the base (`exists_absorption`): extracting the
core of the stratum `S` at its coordinate `i` leaves the region
`q_S^{1/k_i}|u_i| > b q_min^{1/k_i}`,
on which `q_{S∖i} = q_S |u_i|^{k_i} > b^{k_i} q_min` — the invariant for the child state `S ∖ {i}`
with `u_i` now tangential. At `S = ∅` the invariant is the phase gap. The box theorem
(`exists_monomialTiling`) first splits `[-r,r]^m` by the set `T` of coordinates with `|u_j| > b`
(the initial strata, invariant `q_{Tᶜ} ≥ b^{∑_T k}`), then runs the extraction on each stratum.

This replaces the paper's adapted partition of unity inside an exact-monomial box by an exact
measurable tiling with no smooth cutoff. Non-claims: no measure transport, no amplitude; the cores
are sets, not yet `CorePresentation`s (unit 4b); nothing about several charts.
-/

open Set Filter Topology MeasureTheory

namespace Grammar

variable {m : ℕ}

/-! ### The tangential monomial and the normal phase -/

/-- The tangential monomial `∏_{j ∉ S} |u_j|^{k_j}`. -/
def tanMonomial (k : Fin m → ℕ) (S : Finset (Fin m)) (u : Fin m → ℝ) : ℝ :=
  ∏ j ∈ Sᶜ, |u j| ^ k j

theorem tanMonomial_nonneg (k : Fin m → ℕ) (S : Finset (Fin m)) (u : Fin m → ℝ) :
    0 ≤ tanMonomial k S u :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _

theorem tanMonomial_congr (k : Fin m → ℕ) (S : Finset (Fin m)) {u v : Fin m → ℝ}
    (h : ∀ j ∉ S, u j = v j) : tanMonomial k S u = tanMonomial k S v :=
  Finset.prod_congr rfl fun j hj => by rw [h j (Finset.mem_compl.1 hj)]

theorem continuous_tanMonomial (k : Fin m → ℕ) (S : Finset (Fin m)) :
    Continuous (tanMonomial k S) :=
  continuous_finsetProd _ fun j _ => (continuous_abs.comp (continuous_apply j)).pow _

theorem tanMonomial_erase (k : Fin m → ℕ) {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S)
    (u : Fin m → ℝ) : tanMonomial k (S.erase i) u = tanMonomial k S u * |u i| ^ k i := by
  classical
  unfold tanMonomial
  have h : (S.erase i)ᶜ = insert i Sᶜ := by
    ext j
    simp [Finset.mem_compl, or_iff_not_imp_right]
  rw [h, Finset.prod_insert (by simpa using hi), mul_comm]

/-- The normal phase `∏_j u_j^{2k_j}`. -/
def normalPhase (k : Fin m → ℕ) (u : Fin m → ℝ) : ℝ := ∏ j, u j ^ (2 * k j)

theorem normalPhase_eq (k : Fin m → ℕ) (S : Finset (Fin m)) (u : Fin m → ℝ) :
    normalPhase k u = tanMonomial k S u ^ 2 * ∏ j ∈ S, u j ^ (2 * k j) := by
  unfold normalPhase tanMonomial
  rw [← Finset.prod_compl_mul_prod S, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm (k j) 2, Even.pow_abs ⟨k j, two_mul _⟩]

/-! ### The core map -/

/-- The rescaling factor `q_S(u)^{1/k_i}`. -/
noncomputable def coreScale (k : Fin m → ℕ) (S : Finset (Fin m)) (i : Fin m) (u : Fin m → ℝ) :
    ℝ :=
  tanMonomial k S u ^ (1 / (k i : ℝ))

/-- The core map: coordinate `i` rescaled by the tangential factor. -/
noncomputable def coreMap (k : Fin m → ℕ) (S : Finset (Fin m)) (i : Fin m) :
    (Fin m → ℝ) → (Fin m → ℝ) :=
  rescale i (coreScale k S i)

theorem coreScale_nonneg (k : Fin m → ℕ) (S : Finset (Fin m)) (i : Fin m) (u : Fin m → ℝ) :
    0 ≤ coreScale k S i u :=
  Real.rpow_nonneg (tanMonomial_nonneg k S u) _

theorem coreScale_pow (k : Fin m → ℕ) (S : Finset (Fin m)) {i : Fin m} (hk : 0 < k i)
    (u : Fin m → ℝ) : coreScale k S i u ^ k i = tanMonomial k S u := by
  unfold coreScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (tanMonomial_nonneg k S u), one_div,
    inv_mul_cancel₀ (by exact_mod_cast hk.ne'), Real.rpow_one]

theorem coreScale_congr (k : Fin m → ℕ) (S : Finset (Fin m)) (i : Fin m) {u v : Fin m → ℝ}
    (h : ∀ j ∉ S, u j = v j) : coreScale k S i u = coreScale k S i v := by
  unfold coreScale
  rw [tanMonomial_congr k S h]

theorem coreMap_apply_self (k : Fin m → ℕ) (S : Finset (Fin m)) (i : Fin m) (u : Fin m → ℝ) :
    coreMap k S i u i = u i * coreScale k S i u :=
  rescale_apply_self _ _ _

theorem coreMap_apply_of_ne (k : Fin m → ℕ) (S : Finset (Fin m)) {i j : Fin m} (h : j ≠ i)
    (u : Fin m → ℝ) : coreMap k S i u j = u j :=
  rescale_apply_of_ne h _ _

theorem abs_coreMap_self_pow (k : Fin m → ℕ) (S : Finset (Fin m)) {i : Fin m} (hk : 0 < k i)
    (u : Fin m → ℝ) : |coreMap k S i u i| ^ k i = |u i| ^ k i * tanMonomial k S u := by
  rw [coreMap_apply_self, abs_mul, mul_pow, abs_of_nonneg (coreScale_nonneg k S i u),
    coreScale_pow k S hk]

theorem coreMap_pow_self (k : Fin m → ℕ) (S : Finset (Fin m)) {i : Fin m} (hk : 0 < k i)
    (u : Fin m → ℝ) :
    coreMap k S i u i ^ (2 * k i) = u i ^ (2 * k i) * tanMonomial k S u ^ 2 := by
  rw [coreMap_apply_self, mul_pow]
  congr 1
  rw [mul_comm, pow_mul, coreScale_pow k S hk]

/-- **The phase in core coordinates**: `∏_j u_j^{2k_j} = ∏_{j ∈ S} (coreMap u)_j^{2k_j}`. -/
theorem normalPhase_eq_prod_coreMap (k : Fin m → ℕ) {S : Finset (Fin m)} {i : Fin m}
    (hk : 0 < k i) (hi : i ∈ S) (u : Fin m → ℝ) :
    normalPhase k u = ∏ j ∈ S, coreMap k S i u j ^ (2 * k j) := by
  have hprod : ∏ j ∈ S.erase i, coreMap k S i u j ^ (2 * k j) =
      ∏ j ∈ S.erase i, u j ^ (2 * k j) :=
    Finset.prod_congr rfl fun j hj => by rw [coreMap_apply_of_ne k S (Finset.ne_of_mem_erase hj)]
  rw [normalPhase_eq k S u, ← Finset.mul_prod_erase S (fun j => u j ^ (2 * k j)) hi,
    ← Finset.mul_prod_erase S (fun j => coreMap k S i u j ^ (2 * k j)) hi, coreMap_pow_self k S hk,
    hprod]
  ring

/-- The inverse of a rescaling by an `i`-independent nonvanishing factor. -/
theorem rescale_inv_rescale {d : ℕ} {i : Fin d} {f : (Fin d → ℝ) → ℝ}
    (hf : ∀ u s, f (Function.update u i s) = f u) {u : Fin d → ℝ} (hf0 : f u ≠ 0) :
    rescale i (fun v => (f v)⁻¹) (rescale i f u) = u := by
  unfold rescale
  rw [Function.update_idem, Function.update_self]
  beta_reduce
  rw [hf, mul_inv_cancel_right₀ hf0, Function.update_eq_self]

theorem coreScale_update (k : Fin m → ℕ) {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S)
    (u : Fin m → ℝ) (s : ℝ) : coreScale k S i (Function.update u i s) = coreScale k S i u :=
  coreScale_congr k S i fun j hj => Function.update_of_ne (fun h => hj (by rw [h]; exact hi)) _ _

/-! ### Monomial cores -/

/-- Membership in `B` depends only on the coordinates outside `S`. -/
def IsCylindrical (S : Finset (Fin m)) (B : Set (Fin m → ℝ)) : Prop :=
  ∀ u v : Fin m → ℝ, (∀ j ∉ S, u j = v j) → (u ∈ B ↔ v ∈ B)

/-- **A monomial core**: the stratum `S` (normal coordinates), the rescaled coordinate `i ∈ S`,
the tangential base `B` and the lower bound `qmin` of the tangential monomial on the base. -/
structure MonomialCore (m : ℕ) where
  /-- the normal coordinates -/
  S : Finset (Fin m)
  /-- the rescaled coordinate -/
  i : Fin m
  i_mem : i ∈ S
  /-- the tangential base -/
  B : Set (Fin m → ℝ)
  /-- the lower bound of the tangential monomial on the base -/
  qmin : ℝ

namespace MonomialCore

variable (k : Fin m → ℕ) (b : ℝ) (C : MonomialCore m)

/-- The side of the rescaled normal coordinate, `b · qmin^{1/k_i}`. -/
noncomputable def side : ℝ := b * C.qmin ^ (1 / (k C.i : ℝ))

/-- The core set: base, the unrescaled normal box of side `b`, and the rescaled coordinate
bounded by `side`. -/
def set : Set (Fin m → ℝ) :=
  {u | u ∈ C.B ∧ (∀ j ∈ C.S, j ≠ C.i → |u j| ≤ b) ∧ |coreMap k C.S C.i u C.i| ≤ C.side k b}

/-- The goodness certificate of a core. -/
structure IsGood : Prop where
  cyl : IsCylindrical C.S C.B
  meas : MeasurableSet C.B
  qmin_pos : 0 < C.qmin
  qmin_le : ∀ u ∈ C.B, C.qmin ≤ tanMonomial k C.S u

theorem side_pos {k : Fin m → ℕ} {b : ℝ} (hb : 0 < b) {C : MonomialCore m} (h : C.IsGood k) :
    0 < C.side k b :=
  mul_pos hb (Real.rpow_pos_of_pos h.qmin_pos _)

/-- On the core, the rescaled coordinate has modulus at most `b` in the original coordinate. -/
theorem abs_apply_self_le {k : Fin m → ℕ} {b : ℝ} (hb : 0 < b) {C : MonomialCore m}
    (h : C.IsGood k) {u : Fin m → ℝ} (hu : u ∈ C.set k b) : |u C.i| ≤ b := by
  obtain ⟨huB, -, hui⟩ := hu
  have hq : C.qmin ≤ tanMonomial k C.S u := h.qmin_le u huB
  have hs : 0 < coreScale k C.S C.i u :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le h.qmin_pos hq) _
  have hle : C.qmin ^ (1 / (k C.i : ℝ)) ≤ coreScale k C.S C.i u :=
    Real.rpow_le_rpow h.qmin_pos.le hq (by positivity)
  rw [coreMap_apply_self, abs_mul, abs_of_pos hs] at hui
  unfold side at hui
  by_contra hcon
  push Not at hcon
  have : b * coreScale k C.S C.i u < |u C.i| * coreScale k C.S C.i u :=
    mul_lt_mul_of_pos_right hcon hs
  have : b * C.qmin ^ (1 / (k C.i : ℝ)) ≤ b * coreScale k C.S C.i u :=
    mul_le_mul_of_nonneg_left hle hb.le
  linarith

end MonomialCore

/-- The region of a state: the base intersected with the normal box of side `b` on `S`. -/
def stateRegion (S : Finset (Fin m)) (B : Set (Fin m → ℝ)) (b : ℝ) : Set (Fin m → ℝ) :=
  {u | u ∈ B ∧ ∀ j ∈ S, |u j| ≤ b}

/-! ### The absorption theorem -/

/-- **Exact-monomial rectangular extraction.** For a state `(S, B)` with the weighted-product
invariant `q_S ≥ qmin > 0` on the `S`-cylindrical measurable base `B`, the region
`B ∩ {|u_j| ≤ b, j ∈ S}` is the disjoint union of finitely many good monomial cores and a set on
which the phase has a positive lower bound. -/
theorem exists_absorption (k : Fin m → ℕ) (hk : ∀ j, 0 < k j) {b : ℝ} (hb : 0 < b) :
    ∀ (n : ℕ) (S : Finset (Fin m)), S.card = n →
    ∀ (B : Set (Fin m → ℝ)), IsCylindrical S B → MeasurableSet B →
    ∀ qmin : ℝ, 0 < qmin → (∀ u ∈ B, qmin ≤ tanMonomial k S u) →
    ∃ (N : ℕ) (C : Fin N → MonomialCore m),
      (∀ α, (C α).IsGood k) ∧
      (∀ α, (C α).set k b ⊆ stateRegion S B b) ∧
      (∀ α β, α ≠ β → Disjoint ((C α).set k b) ((C β).set k b)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ stateRegion S B b, u ∉ ⋃ α, (C α).set k b → δ ≤ normalPhase k u := by
  intro n
  induction n with
  | zero =>
    intro S hS B hcyl hmeas qmin hq hqB
    rw [Finset.card_eq_zero] at hS
    subst hS
    refine ⟨0, Fin.elim0, fun α => α.elim0, fun α => α.elim0, fun α => α.elim0, qmin ^ 2,
      by positivity, fun u hu _ => ?_⟩
    rw [normalPhase_eq k ∅ u, Finset.prod_empty, mul_one]
    exact pow_le_pow_left₀ hq.le (hqB u hu.1) 2
  | succ n ih =>
    intro S hS B hcyl hmeas qmin hq hqB
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨i, hi⟩ := hSne
    set c : ℝ := b * qmin ^ (1 / (k i : ℝ)) with hc
    have hcpos : 0 < c := mul_pos hb (Real.rpow_pos_of_pos hq _)
    -- the first core and the leftover base
    set C₀ : MonomialCore m := ⟨S, i, hi, B, qmin⟩ with hC₀
    set B' : Set (Fin m → ℝ) := {u | u ∈ B ∧ |u i| ≤ b ∧ c < |coreMap k S i u i|} with hB'
    have hB'cyl : IsCylindrical (S.erase i) B' := by
      intro u v huv
      have hi' : u i = v i := huv i (by simp)
      have hSc : ∀ j ∉ S, u j = v j := fun j hj => huv j (fun h => hj (Finset.mem_of_mem_erase h))
      have hscale : coreScale k S i u = coreScale k S i v := coreScale_congr k S i hSc
      simp only [hB', Set.mem_ofPred_eq, coreMap_apply_self, hi', hscale, hcyl u v hSc]
    have hB'meas : MeasurableSet B' := by
      have h1 : Measurable fun u : Fin m → ℝ => |u i| :=
        (continuous_abs.comp (continuous_apply i)).measurable
      have h2 : Measurable fun u : Fin m → ℝ => |coreMap k S i u i| := by
        simp only [coreMap_apply_self]
        exact (continuous_abs.comp ((continuous_apply i).mul
          ((continuous_tanMonomial k S).rpow_const fun _ => Or.inr (by positivity)))
          ).measurable
      exact hmeas.inter ((measurableSet_le h1 measurable_const).inter
        (measurableSet_lt measurable_const h2))
    have hB'sub : B' ⊆ B := fun u hu => hu.1
    set qmin' : ℝ := b ^ k i * qmin with hqmin'
    have hq' : 0 < qmin' := by positivity
    have hqB' : ∀ u ∈ B', qmin' ≤ tanMonomial k (S.erase i) u := by
      intro u hu
      rw [tanMonomial_erase k hi, mul_comm, ← abs_coreMap_self_pow k S (hk i)]
      have h1 : c ^ k i ≤ |coreMap k S i u i| ^ k i :=
        pow_le_pow_left₀ hcpos.le hu.2.2.le _
      have h2 : c ^ k i = qmin' := by
        rw [hc, hqmin', mul_pow, ← Real.rpow_natCast (qmin ^ _), ← Real.rpow_mul hq.le, one_div,
          inv_mul_cancel₀ (by exact_mod_cast (hk i).ne'), Real.rpow_one]
      rw [← h2]
      exact h1
    have hcard : (S.erase i).card = n := by
      rw [Finset.card_erase_of_mem hi, hS]
      rfl
    obtain ⟨N', C', hgood', hsub', hdisj', δ', hδ', htail'⟩ :=
      ih (S.erase i) hcard B' hB'cyl hB'meas qmin' hq' hqB'
    have hC₀good : C₀.IsGood k := ⟨hcyl, hmeas, hq, hqB⟩
    -- the core of the child state lies in the leftover region
    have hsub'' : ∀ β, (C' β).set k b ⊆ stateRegion S B b := by
      intro β u hu
      have hu' := hsub' β hu
      refine ⟨hu'.1.1, fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji; exact hu'.1.2.1
      · exact hu'.2 j (Finset.mem_erase.2 ⟨hji, hj⟩)
    refine ⟨N' + 1, Fin.cons C₀ C', ?_, ?_, ?_, δ', hδ', ?_⟩
    · intro α
      induction α using Fin.cases with
      | zero => simpa using hC₀good
      | succ β => simpa using hgood' β
    · intro α
      induction α using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        intro u hu
        refine ⟨hu.1, fun j hj => ?_⟩
        by_cases hji : j = i
        · subst hji; exact MonomialCore.abs_apply_self_le hb hC₀good hu
        · exact hu.2.1 j hj hji
      | succ β => simpa using hsub'' β
    · intro α β hne
      induction α using Fin.cases with
      | zero =>
        induction β using Fin.cases with
        | zero => exact absurd rfl hne
        | succ β' =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [Set.disjoint_left]
          intro u hu hu'
          have := (hsub' β' hu').1.2.2
          exact absurd hu.2.2 (not_le.2 this)
      | succ α' =>
        induction β using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [Set.disjoint_left]
          intro u hu hu'
          have := (hsub' α' hu).1.2.2
          exact absurd hu'.2.2 (not_le.2 this)
        | succ β' =>
          simp only [Fin.cons_succ]
          exact hdisj' α' β' fun h => hne (congrArg Fin.succ h)
    · intro u hu hnot
      have hnot0 : u ∉ C₀.set k b := fun h => hnot (Set.mem_iUnion.2 ⟨0, by simpa using h⟩)
      have hnot' : u ∉ ⋃ β, (C' β).set k b := fun h => by
        obtain ⟨β, hβ⟩ := Set.mem_iUnion.1 h
        exact hnot (Set.mem_iUnion.2 ⟨β.succ, by simpa using hβ⟩)
      have hui : |u i| ≤ b := hu.2 i hi
      have hgt : c < |coreMap k S i u i| := by
        by_contra hle
        push Not at hle
        exact hnot0 ⟨hu.1, fun j hj _ => hu.2 j hj, hle⟩
      have huR' : u ∈ stateRegion (S.erase i) B' b :=
        ⟨⟨hu.1, hui, hgt⟩, fun j hj => hu.2 j (Finset.mem_of_mem_erase hj)⟩
      exact htail' u huR' hnot'

/-! ### The box theorem -/

/-- The normal box `[-r, r]^m`. -/
def normalBox (r : ℝ) : Set (Fin m → ℝ) := {u | ∀ j, |u j| ≤ r}

/-- The base of the initial stratum `T`: the coordinates in `T` are large, `b < |u_j| ≤ r`. -/
def stratumBase (b r : ℝ) (T : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {u | ∀ j ∈ T, b < |u j| ∧ |u j| ≤ r}

theorem isCylindrical_stratumBase (b r : ℝ) (T : Finset (Fin m)) :
    IsCylindrical Tᶜ (stratumBase b r T) := by
  intro u v huv
  have h : ∀ j ∈ T, u j = v j := fun j hj => huv j (by simpa using hj)
  simp only [stratumBase, Set.mem_ofPred_eq]
  exact forall₂_congr fun j hj => by rw [h j hj]

theorem measurableSet_stratumBase (b r : ℝ) (T : Finset (Fin m)) :
    MeasurableSet (stratumBase b r T) := by
  have h : stratumBase b r T =
      ⋂ j ∈ (T : Set (Fin m)), ({u : Fin m → ℝ | b < |u j|} ∩ {u | |u j| ≤ r}) := by
    ext u
    simp [stratumBase]
  rw [h]
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_
  have hmj : Measurable fun u : Fin m → ℝ => |u j| :=
    (continuous_abs.comp (continuous_apply j)).measurable
  exact (measurableSet_lt measurable_const hmj).inter (measurableSet_le hmj measurable_const)

theorem tanMonomial_compl_ge (k : Fin m → ℕ) {b r : ℝ} (hb : 0 < b) (T : Finset (Fin m))
    {u : Fin m → ℝ} (hu : u ∈ stratumBase b r T) :
    b ^ (∑ j ∈ T, k j) ≤ tanMonomial k Tᶜ u := by
  unfold tanMonomial
  rw [compl_compl, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun j _ => by positivity)
    fun j hj => pow_le_pow_left₀ hb.le (hu j hj).1.le _

/-- **The exact-monomial tiling of the box.** For positive exponents `k` and `0 < b ≤ r`, the box
`[-r, r]^m` is, up to a set on which the phase `∏ u_j^{2k_j}` has a positive lower bound, the
disjoint union of finitely many good monomial cores. -/
theorem exists_monomialTiling (k : Fin m → ℕ) (hk : ∀ j, 0 < k j) {b r : ℝ} (hb : 0 < b)
    (hbr : b ≤ r) :
    ∃ (ι : Type) (_ : Fintype ι) (C : ι → MonomialCore m),
      (∀ α, (C α).IsGood k) ∧
      (∀ α, (C α).set k b ⊆ normalBox r) ∧
      (∀ α β, α ≠ β → Disjoint ((C α).set k b) ((C β).set k b)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ normalBox r, u ∉ ⋃ α, (C α).set k b → δ ≤ normalPhase k u := by
  classical
  have key : ∀ T : Finset (Fin m), ∃ (N : ℕ) (C : Fin N → MonomialCore m),
      (∀ α, (C α).IsGood k) ∧
      (∀ α, (C α).set k b ⊆ stateRegion Tᶜ (stratumBase b r T) b) ∧
      (∀ α β, α ≠ β → Disjoint ((C α).set k b) ((C β).set k b)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ stateRegion Tᶜ (stratumBase b r T) b,
        u ∉ ⋃ α, (C α).set k b → δ ≤ normalPhase k u := fun T =>
    exists_absorption k hk hb _ Tᶜ rfl (stratumBase b r T) (isCylindrical_stratumBase b r T)
      (measurableSet_stratumBase b r T) (b ^ (∑ j ∈ T, k j)) (by positivity)
      fun u hu => tanMonomial_compl_ge k hb T hu
  choose N C hgood hsub hdisj δ hδpos htail using key
  -- the region of a stratum lies in the box, and distinct strata have disjoint regions
  have hregion : ∀ T : Finset (Fin m), stateRegion Tᶜ (stratumBase b r T) b ⊆ normalBox r := by
    intro T u hu j
    by_cases hj : j ∈ T
    · exact (hu.1 j hj).2
    · exact (hu.2 j (Finset.mem_compl.2 hj)).trans hbr
  have hregdisj : ∀ T T' : Finset (Fin m), T ≠ T' →
      Disjoint (stateRegion Tᶜ (stratumBase b r T) b) (stateRegion T'ᶜ (stratumBase b r T') b) := by
    intro T T' hTT'
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ T ↔ j ∈ T') := by
      by_contra h
      push Not at h
      exact hTT' (Finset.ext h)
    by_cases h1 : j ∈ T
    · have h2 : j ∉ T' := fun h2 => hj ⟨fun _ => h2, fun _ => h1⟩
      have := (hu.1 j h1).1
      have := hu'.2 j (Finset.mem_compl.2 h2)
      linarith
    · have h2 : j ∈ T' := by
        by_contra h2
        exact hj ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      have := (hu'.1 j h2).1
      have := hu.2 j (Finset.mem_compl.2 h1)
      linarith
  obtain ⟨T₀, -, hT₀⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
  refine ⟨Σ T : Finset (Fin m), Fin (N T), inferInstance, fun p => C p.1 p.2,
    fun p => hgood p.1 p.2,
    fun p => (hsub p.1 p.2).trans (hregion p.1), ?_, δ T₀, hδpos T₀, ?_⟩
  · rintro ⟨T, α⟩ ⟨T', α'⟩ hne
    by_cases hTT' : T = T'
    · subst hTT'
      have hαα' : α ≠ α' := fun h => hne (by rw [h])
      exact hdisj T α α' hαα'
    · exact ((hregdisj T T' hTT').mono (hsub T α) (hsub T' α'))
  · intro u hu hnot
    set T : Finset (Fin m) := Finset.univ.filter fun j => b < |u j| with hT
    have huR : u ∈ stateRegion Tᶜ (stratumBase b r T) b := by
      refine ⟨fun j hj => ⟨(Finset.mem_filter.1 hj).2, hu j⟩, fun j hj => ?_⟩
      have : ¬ b < |u j| := fun h =>
        (Finset.mem_compl.1 hj) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact not_lt.1 this
    have hnotT : u ∉ ⋃ α, (C T α).set k b := fun h => by
      obtain ⟨α, hα⟩ := Set.mem_iUnion.1 h
      exact hnot (Set.mem_iUnion.2 ⟨⟨T, α⟩, hα⟩)
    exact (hT₀ T (Finset.mem_univ _)).trans (htail T u huR hnotT)

end Grammar
