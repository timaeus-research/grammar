/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetProducer
import Grammar.SheetCubeRegression

/-!
# Regression: the cube blow-up with a radial SMOOTH prior (consult #117 §8)

The cube blow-up atlas of `hironaka` with every orthant selected (`cubeDomainAtlas`, unit
weights via `DomainSectorAtlas.toWeighted`) satisfies the SMOOTH sheet inputs
(`smoothCubeInputs`) for the phase `K(x) = |x|²` on `[−1,1]^d`, a RADIAL prior `ψ(|x|²)` with
`ψ : ℝ → ℝ` smooth and nonnegative, and an arbitrary smooth observable `Q`. The chart data are
polynomial (`φ_β`), the weights and Jacobian units are `1`, and the phase unit
`1 + Σ_{γ≠β} y_γ²` is tangential. The smooth producer yields the coordinate-free expansion of
`∫_{[−1,1]^d} ψ(|x|²) Q(x) e^{−N|x|²} dx` (★★ `smoothCube_hasSmoothCoordFreeExpansion`), with
log degree `0` (`smoothCubeInputs_commonD`) and lattice denominator `2^{d·2^d}`
(`smoothCubeInputs_commonQ`); the coefficients are independent of the choice of `ψ` representing
the same prior (`coeff_eq_of_inputs`). The instance `bumpPrior x = σ(1 − |x|²)`, `σ` Mathlib's
`Real.smoothTransition`, is a smooth radial prior vanishing identically on `|x| ≥ 1` — hence not
analytic on the cube (not formalised here); the analytic cube regression
(`SheetAssembly.cubeInputs`) cannot accept it. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

open BlowUpCube SheetAssembly

variable {d : ℕ}

/-! ### Radial smooth priors -/

/-- The radial prior `ψ(|x|²) = ψ(K x)`. -/
noncomputable def radialPrior (ψ : ℝ → ℝ) (x : Fin d → ℝ) : ℝ := ψ (K x)

theorem contDiff_K : ContDiff ℝ ∞ (K (d := d)) :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

theorem contDiff_radialPrior {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (radialPrior (d := d) ψ) :=
  hψ.comp contDiff_K

theorem radialPrior_nonneg {ψ : ℝ → ℝ} (hψ0 : ∀ t, 0 ≤ ψ t) (x : Fin d → ℝ) :
    0 ≤ radialPrior ψ x :=
  hψ0 _

/-- The smooth bump profile `t ↦ σ(1 − t)`: `1` for `t ≤ 0`, `0` for `t ≥ 1`. -/
noncomputable def bumpProfile (t : ℝ) : ℝ := Real.smoothTransition (1 - t)

theorem contDiff_bumpProfile : ContDiff ℝ ∞ bumpProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem bumpProfile_nonneg (t : ℝ) : 0 ≤ bumpProfile t := Real.smoothTransition.nonneg _

theorem bumpProfile_of_one_le {t : ℝ} (ht : 1 ≤ t) : bumpProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem bumpProfile_of_nonpos {t : ℝ} (ht : t ≤ 0) : bumpProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The radial bump prior `σ(1 − |x|²)`: smooth, nonnegative, `1` at the origin and identically
`0` on `|x| ≥ 1`. -/
noncomputable def bumpPrior (x : Fin d → ℝ) : ℝ := radialPrior bumpProfile x

theorem bumpPrior_zero : bumpPrior (0 : Fin d → ℝ) = 1 := by
  unfold bumpPrior radialPrior K
  simp [bumpProfile_of_nonpos]

theorem bumpPrior_eq_zero {x : Fin d → ℝ} (hx : 1 ≤ K x) : bumpPrior x = 0 :=
  bumpProfile_of_one_le hx

/-! ### The smooth sheet inputs of the cube -/

section Inputs

theorem isCompact_centeredBox_one : IsCompact (centeredBox d 1) := by
  rw [centeredBox_one_eq_cube]
  exact isCompact_cube

variable [NeZero d] {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ∀ t, 0 ≤ ψ t)
  {Q : (Fin d → ℝ) → ℝ} (hQ : ContDiff ℝ ∞ Q)

/-- ★★ **The cube blow-up atlas with a radial smooth prior satisfies the smooth sheet inputs**:
unit weights, unit Jacobians, polynomial charts and the tangential unit `1 + Σ_{γ≠β} y_γ²`. -/
noncomputable def smoothCubeInputs : SmoothSheetInputs d where
  K := K
  K_m := continuous_K.measurable
  Ω := centeredBox d 1
  A := cubeDomainAtlas.toWeighted
  a := 1
  ha := one_pos
  lo_eq := fun (β : Fin d) (j : Fin d) => by
    change -(if j = β then (1 : ℝ) else 1) = -1
    simp
  hi_eq := fun (β : Fin d) (j : Fin d) => by
    change (if j = β then (1 : ℝ) else 1) = 1
    simp
  K_nonneg w _ := K_nonneg w
  prior := radialPrior ψ
  obs := Q
  prior_nonneg := radialPrior_nonneg hψ0
  prior_smooth := contDiff_radialPrior hψ
  obs_smooth := hQ
  obs_int := integrable_of_continuous_of_subset_compact (contDiff_radialPrior hψ).continuous
    hQ.continuous isCompact_centeredBox_one subset_rfl
    (cubeDomainAtlas (d := d)).measurableSet_W
  φ_smooth := fun (β : Fin d) => contDiff_blowUpChart (B d) β (n := ⊤)
  ω_smooth := fun _ => contDiff_const
  jacAbs_smooth := fun _ => by
    change ContDiff ℝ ∞ fun _ : Fin d → ℝ => |(1 : ℝ)|
    exact contDiff_const
  hu_tan := fun (β : Fin d) w w' h => unit_tan β w w' fun j hj => h j (by
    change ¬ 0 < (if j = β then 1 else 0)
    simp [hj])

theorem smoothCubeInputs_K : (smoothCubeInputs hψ hψ0 hQ).K = K := rfl

theorem smoothCubeInputs_W : (smoothCubeInputs hψ hψ0 hQ).A.W = centeredBox d 1 := rfl

theorem smoothCubeInputs_prior : (smoothCubeInputs hψ hψ0 hQ).prior = radialPrior ψ := rfl

theorem smoothCubeInputs_ω (β : Fin d) (y : Fin d → ℝ) :
    (smoothCubeInputs hψ hψ0 hQ).A.ω β y = 1 := rfl

theorem smoothCubeInputs_jacUnit (β : Fin d) (y : Fin d → ℝ) :
    (smoothCubeInputs hψ hψ0 hQ).A.jacUnit β y = 1 := rfl

theorem smoothCubeInputs_phaseUnit (β : Fin d) (y : Fin d → ℝ) :
    (smoothCubeInputs hψ hψ0 hQ).A.phaseUnit β y = unit β y := rfl

/-- ★★ **Smooth cube regression**: the coordinate-free expansion of
`∫_{[−1,1]^d} ψ(|x|²) Q(x) e^{−N|x|²} dx` through the cube blow-up atlas, for a radial SMOOTH
prior. -/
theorem smoothCube_hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion
      (globalLaplace (centeredBox d 1) K fun w => radialPrior ψ w * Q w)
      (smoothCubeInputs hψ hψ0 hQ).decomp.coeff
      (smoothCubeInputs hψ hψ0 hQ).decomp.commonQ
      (smoothCubeInputs hψ hψ0 hQ).decomp.commonD :=
  (smoothCubeInputs hψ hψ0 hQ).hasSmoothCoordFreeExpansion

/-- Membership in the active set of a cube chart: the pivot only. -/
theorem smoothCubeInputs_mem_act (i j : Fin d) :
    j ∈ (smoothCubeInputs hψ hψ0 hQ).act i ↔ j = i := by
  unfold SmoothSheetInputs.act
  rw [Finset.mem_filter]
  change (j ∈ Finset.univ ∧ 0 < (if j = i then 1 else 0)) ↔ j = i
  constructor
  · rintro ⟨-, h⟩
    by_contra hne
    rw [if_neg hne] at h
    exact lt_irrefl _ h
  · rintro rfl
    exact ⟨Finset.mem_univ _, by rw [if_pos rfl]; exact one_pos⟩

/-- The active set of a cube chart is the pivot. -/
theorem smoothCubeInputs_act (β : Fin d) : (smoothCubeInputs hψ hψ0 hQ).act β = {β} :=
  Finset.ext fun j => (smoothCubeInputs_mem_act hψ hψ0 hQ β j).trans Finset.mem_singleton.symm

/-- Every piece has exactly one active coordinate. -/
theorem smoothCubeInputs_da (p : (smoothCubeInputs hψ hψ0 hQ).PIdx) :
    (smoothCubeInputs hψ hψ0 hQ).da p = 1 := by
  unfold SmoothSheetInputs.da
  rw [Fintype.card_of_subtype (p := inJ ((smoothCubeInputs hψ hψ0 hQ).act p.1))
    ((smoothCubeInputs hψ hψ0 hQ).act p.1) fun _ => Iff.rfl]
  exact Finset.card_eq_one.2 ⟨p.1, smoothCubeInputs_act hψ hψ0 hQ p.1⟩

/-- ★ **No logarithms for the smooth cube**: the produced log degree is `0`. -/
theorem smoothCubeInputs_commonD : (smoothCubeInputs hψ hψ0 hQ).decomp.commonD = 0 :=
  le_antisymm (Finset.sup_le fun I _ => by
    change (smoothCubeInputs hψ hψ0 hQ).da _ - 1 ≤ 0
    rw [smoothCubeInputs_da]) (Nat.zero_le _)

/-- The active phase exponent of every piece is `1`. -/
theorem smoothCubeInputs_kA (p : (smoothCubeInputs hψ hψ0 hQ).PIdx)
    (j : Fin ((smoothCubeInputs hψ hψ0 hQ).da p)) : (smoothCubeInputs hψ hψ0 hQ).kA p j = 1 := by
  have hmem : (((smoothCubeInputs hψ hψ0 hQ).eqv p j).1 : Fin d) = p.1 :=
    (smoothCubeInputs_mem_act hψ hψ0 hQ p.1 _).1 ((smoothCubeInputs hψ hψ0 hQ).eqv p j).2
  exact if_pos hmem

/-- The lattice denominator of every piece is `2`. -/
theorem smoothCubeInputs_Qamb (I : Fin (Fintype.card (smoothCubeInputs hψ hψ0 hQ).PIdx)) :
    Qamb ((smoothCubeInputs hψ hψ0 hQ).decomp.chart I).k = 2 := by
  change 2 * ∏ j, (smoothCubeInputs hψ hψ0 hQ).kA _ j = 2
  rw [Finset.prod_eq_one fun j _ => smoothCubeInputs_kA hψ hψ0 hQ _ j, mul_one]

/-- The number of pieces: `d` charts times `2^d` orthants. -/
theorem smoothCubeInputs_card_PIdx :
    Fintype.card (smoothCubeInputs hψ hψ0 hQ).PIdx = d * 2 ^ d := by
  rw [Fintype.card_sigma]
  change ∑ _ : Fin d, Fintype.card (↥(Finset.univ : Finset (WaterFilling.CoordSign d))) = _
  simp [WaterFilling.CoordSign]

/-- ★ The common lattice denominator of the smooth cube: every piece has denominator `2`, so the
product over the `d·2^d` pieces is `2^{d·2^d}`. -/
theorem smoothCubeInputs_commonQ :
    (smoothCubeInputs hψ hψ0 hQ).decomp.commonQ = 2 ^ (d * 2 ^ d) := by
  unfold SmoothCoreDecomposition.commonQ
  rw [Finset.prod_congr rfl fun I _ => smoothCubeInputs_Qamb hψ hψ0 hQ I, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smoothCubeInputs_card_PIdx]

/-- ★ **Profile independence**: two smooth profiles representing the same radial prior give the
same coefficients (presentation independence). -/
theorem coeff_eq_of_profile {ψ' : ℝ → ℝ} (hψ' : ContDiff ℝ ∞ ψ') (hψ0' : ∀ t, 0 ≤ ψ' t)
    (hψψ' : radialPrior (d := d) ψ = radialPrior ψ') :
    (smoothCubeInputs hψ hψ0 hQ).decomp.coeff = (smoothCubeInputs hψ' hψ0' hQ).decomp.coeff :=
  funext fun μ => funext fun q =>
    (smoothCubeInputs hψ hψ0 hQ).coeff_eq_of_inputs (Y := smoothCubeInputs hψ' hψ0' hQ) rfl rfl
      hψψ' rfl μ q

end Inputs

/-! ### The bump instance -/

section Bump

variable [NeZero d] {Q : (Fin d → ℝ) → ℝ} (hQ : ContDiff ℝ ∞ Q)

/-- The smooth sheet inputs of the cube with the radial bump prior `σ(1 − |x|²)`. -/
noncomputable def bumpCubeInputs : SmoothSheetInputs d :=
  smoothCubeInputs contDiff_bumpProfile bumpProfile_nonneg hQ

theorem bumpCubeInputs_prior : (bumpCubeInputs hQ).prior = bumpPrior := rfl

/-- ★★ **The bump regression**: the coordinate-free expansion of
`∫_{[−1,1]^d} σ(1 − |x|²) Q(x) e^{−N|x|²} dx` with the non-analytic radial bump prior, log degree
`0`. -/
theorem bumpCube_hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion
      (globalLaplace (centeredBox d 1) K fun w => bumpPrior w * Q w)
      (bumpCubeInputs hQ).decomp.coeff (bumpCubeInputs hQ).decomp.commonQ 0 := by
  have h := smoothCube_hasSmoothCoordFreeExpansion contDiff_bumpProfile bumpProfile_nonneg hQ
  rwa [smoothCubeInputs_commonD] at h

end Bump

end SmoothEngine

end Grammar
