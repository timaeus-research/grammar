/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ConstantUnitKernel

/-!
# Finite constant-unit atlases and the conditional global leading coefficient

Modules 4–6 of the adapted-density programme (`tide-log/gpt6_bigpicture_v75.md`), with the cells
of CCXXIX. A **constant-unit cell** (`ConstantUnitCell`) is a compact tangential base with an
integrable base weight, a prescribed normal cube, integer normal exponents, the constant phase
unit `β` and a jointly continuous amplitude; its integral `∫_base β_w(z) L_N(z) dz` has the
leading-term certificate of CCXXIX at the cell's pair `(λ_cell, m_cell − 1)` with the integrated
face coefficient (`ConstantUnitCell.hasLeadingTerm`). A **finite constant-unit atlas** of a function
of the inverse temperature (`FiniteConstantUnitAtlas`) is a finite family of cells whose integrals
sum EXACTLY to that function for every `N ≥ 0` — the a.e. weighted identity of module 4, transported
to normal coordinates. Then:

* the function has the leading term of the atlas at any pair dominating every cell pair, with
  coefficient the sum over the tied cells (`FiniteConstantUnitAtlas.hasLeadingTerm_of_extremal`),
  and at the atlas's own extremal pair (`FiniteConstantUnitAtlas.hasLeadingTerm`);
* **the conditional global theorem** (`hasLeadingTerm_boltzmannIntegral_of_atlases`): for a
  resolution cover of hironaka monomial charts, if every nonempty chart–stratum piece integral
  admits a finite constant-unit atlas, the resolved Boltzmann integral has the leading term at a
  pair dominating every cell of every atlas, with coefficient the sum of the tied cell
  coefficients over all chart–stratum pairs — the divisor-free pieces being negligible (CCXXVI).

Non-claims: the atlas is a HYPOTHESIS — its existence for a given chart–stratum piece is the
adapted geometry (fibre-constant allocation, strip normalisation of the phase unit on the whole
piece, orthant assembly) that neither hironaka's `PartialResolution` nor CCXXIII–CCXXIX construct
(and which is false for arbitrary compact domains and normalised indicator cover weights); the
coefficient is signed, and no positivity is inferred.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### Constant-unit cells -/

/-- **A constant-unit cell** over the tangential space `ℝ^t`: a compact base with an integrable
weight, a prescribed normal cube `(0,b]^{n+1}`, integer exponents, the constant phase unit `β` and
a jointly continuous amplitude. -/
structure ConstantUnitCell (t : ℕ) where
  /-- The normal dimension is `n + 1`. -/
  n : ℕ
  /-- The density exponents. -/
  h : Fin (n + 1) → ℕ
  /-- The half phase exponents. -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- The constant phase unit. -/
  β : ℝ
  β_pos : 0 < β
  /-- The box side. -/
  b : ℝ
  b_pos : 0 < b
  /-- The amplitude. -/
  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  A_cont : Continuous (Function.uncurry A)
  /-- The tangential base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The tangential weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_int : IntegrableOn βw base

namespace ConstantUnitCell

variable {t : ℕ} (c : ConstantUnitCell t)

/-- The cell's exponent `λ = min_j (h_j+1)/(2k_j)`. -/
noncomputable def lam : ℝ := minRatio c.h c.k

/-- The cell's multiplicity `m = #minimisers`. -/
noncomputable def mult : ℕ := multCount (ratioExp c.h c.k) c.lam

theorem lam_pos : 0 < c.lam := minRatio_pos c.h c.k c.k_pos

theorem lam_le (i : Fin (c.n + 1)) : c.lam ≤ ratioExp c.h c.k i := minRatio_le c.h c.k i

theorem exists_ratioExp_eq_lam : ∃ i, ratioExp c.h c.k i = c.lam :=
  exists_ratioExp_eq_minRatio c.h c.k

/-- The cell integral `∫_base β_w(z) L_N(z) dz`. -/
noncomputable def integral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * boxKernel c.n c.h c.k c.β c.b c.A z N

/-- The cell coefficient `∫_base β_w(z) faceCoeff(z) dz`. -/
noncomputable def coeff : ℝ :=
  ∫ z in c.base, c.βw z * boxFaceCoeff c.n c.h c.k c.β c.b c.A c.lam z

/-- **The cell certificate** (CCXXIX). -/
theorem hasLeadingTerm : HasLeadingTerm c.integral c.coeff c.lam (c.mult - 1) :=
  hasLeadingTerm_integral_boxKernel c.k_pos c.β_pos c.b_pos c.lam_pos c.lam_le
    c.exists_ratioExp_eq_lam c.A_cont c.base_compact c.βw_int

end ConstantUnitCell

/-! ### Finite atlases -/

/-- **A finite constant-unit atlas** of `Z`: finitely many cells whose integrals sum exactly to
`Z N` for every `N ≥ 0`. -/
structure FiniteConstantUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where
  /-- The cell index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The cells. -/
  cell : ι → ConstantUnitCell t
  /-- The exact decomposition. -/
  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N

namespace FiniteConstantUnitAtlas

variable {t : ℕ} {Z : ℝ → ℝ} (At : FiniteConstantUnitAtlas t Z)

attribute [instance] FiniteConstantUnitAtlas.fintype

/-- The tied cells at a nominated pair. -/
noncomputable def tied (lam₀ : ℝ) (k₀ : ℕ) : Finset At.ι :=
  Finset.univ.filter fun i => (At.cell i).lam = lam₀ ∧ (At.cell i).mult - 1 = k₀

/-- **The leading term of an atlas at a pair dominating every cell**: coefficient the sum of the
tied cell coefficients (possibly zero). -/
theorem hasLeadingTerm_of_extremal (lam₀ : ℝ) (k₀ : ℕ) (hlam : ∀ i, lam₀ ≤ (At.cell i).lam)
    (hk : ∀ i, (At.cell i).lam = lam₀ → (At.cell i).mult - 1 ≤ k₀) :
    HasLeadingTerm Z (∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff) lam₀ k₀ := by
  have h := hasLeadingTerm_sum_of_extremal Finset.univ (fun i N => (At.cell i).integral N)
    (fun i => (At.cell i).coeff) (fun i => (At.cell i).lam) (fun i => (At.cell i).mult - 1) lam₀ k₀
    (fun i _ => (At.cell i).hasLeadingTerm) (fun i _ => hlam i) (fun i _ => hk i)
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN => (At.eq N hN).symm)

/-- The atlas's extremal exponent (the cell index type is nonempty). -/
noncomputable def extremalLam [Nonempty At.ι] : ℝ :=
  extremalExponent Finset.univ (fun i => (At.cell i).lam) Finset.univ_nonempty

/-- The atlas's extremal log degree. -/
noncomputable def extremalDeg [Nonempty At.ι] : ℕ :=
  extremalDegree Finset.univ (fun i => (At.cell i).lam) (fun i => (At.cell i).mult - 1)
    Finset.univ_nonempty

/-- **The leading term of an atlas at its own extremal pair.** -/
theorem hasLeadingTerm [Nonempty At.ι] :
    HasLeadingTerm Z (∑ i ∈ At.tied At.extremalLam At.extremalDeg, (At.cell i).coeff)
      At.extremalLam At.extremalDeg :=
  At.hasLeadingTerm_of_extremal _ _
    (fun i => extremalExponent_le Finset.univ (fun i => (At.cell i).lam) Finset.univ_nonempty
      (Finset.mem_univ i))
    fun i hi => le_extremalDegree Finset.univ (fun i => (At.cell i).lam)
      (fun i => (At.cell i).mult - 1) Finset.univ_nonempty (Finset.mem_univ i) hi

end FiniteConstantUnitAtlas

/-! ### The conditional global theorem -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The coefficient contributed by the chart–stratum pair `(i, I)`: the sum of the tied cell
coefficients of its atlas (zero for pairs without an atlas). -/
noncomputable def atlasPieceCoeff {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteConstantUnitAtlas d (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ (e i).support ∧ I.Nonempty then
    ∑ j ∈ (At i I hI.1 hI.2).tied lam₀ k₀, ((At i I hI.1 hI.2).cell j).coeff
  else 0

/-- **The conditional global leading coefficient**: for a resolution cover of monomial charts whose
nonempty chart–stratum piece integrals all admit finite constant-unit atlases, the resolved
Boltzmann integral has the leading term at any pair dominating every cell of every atlas, with
coefficient the sum of the tied cell coefficients over all chart–stratum pairs. -/
theorem hasLeadingTerm_boltzmannIntegral_of_atlases (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteConstantUnitAtlas d (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι),
      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        atlasPieceCoeff At lam₀ k₀ i I) lam₀ k₀ := by
  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
    (atlasPieceCoeff At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
    (fun i I hI => by
      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
      unfold atlasPieceCoeff
      rw [dif_pos ⟨hsub, hne⟩]
      exact (At i I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam i I hsub hne)
        (hk i I hsub hne))
    (fun _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
  have hcoef : ∀ i : ι, (∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
      (fun _ => lam₀ = lam₀ ∧ k₀ = k₀), atlasPieceCoeff At lam₀ k₀ i I) =
      ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty), atlasPieceCoeff At lam₀ k₀ i I :=
    fun i => by rw [Finset.filter_true_of_mem fun _ _ => ⟨rfl, rfl⟩]
  beta_reduce at hmain
  rw [Finset.sum_congr rfl fun i _ => hcoef i] at hmain
  exact hmain

end ResolutionCover

end Grammar
