/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Grammar.MonomialCoefficients
import Grammar.ResolvedCoordFreeExpansion

/-!
# The Taylor family of an analytic observable is its monomial coefficient family (CCCIX)

Plan unit 8d / consult #93 B, in every dimension. For `F` with a power series `p` at `0`
(`HasFPowerSeriesOnBall F p 0 R`), Mathlib's `iteratedFDeriv_eq_sum_of_completeSpace` writes the
iterated derivative as the sum over permutations `D^rF(0)(v) = ∑_σ p_r(v∘σ)`. Summing over the
words of weight `b` (a set stable under permutations, `sum_weightFibre_comp_perm`) gives
`∑_{w : weight b} D^rF(0)(e_w) = r! · ∑_{w : weight b} p_r(e_w) = r! · monoCoeff p r b`, hence

* `weightComponent_normalJet_eq`: `∂^b F(0) = (b!/r!) · r! · monoCoeff p r b` (the weight
  component of the jet, `SymmetricWeights`, in terms of the monomial coefficient of the series,
  `MonomialCoefficients`);
* ★ `jetFamily_eq_monoFamily`: `jetFamily F = monoFamily p` — **the observable's Taylor family
  (`∂^bF(0)/b!`, CCCII) is the monomial coefficient family of any power series representing it**;
* `absSummableAt_jetFamily`: the Taylor family is `b`-weighted ℓ¹ as soon as `(n+1)·b < ρ < R`
  (the dimension-loss margin of `MonomialCoefficients`; this is stronger than the
  `NormalMomentPresentation` radius `b < R` and is therefore an explicit hypothesis);
* `CoefficientCertificate.ofSeries`: a coefficient certificate from a density family and the
  factorisation of the amplitude datum through the series' monomial family — no jet computation
  is needed to certify an analytic observable.

Non-claims: the density family is still a factorisation hypothesis; the margin `(n+1)·b < R` is
sufficient, not sharp.
-/

open Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {d : ℕ}

theorem wordMult_eq_weightOf {r : ℕ} (w : Fin r → Fin d) : wordMult w = weightOf w := rfl

/-- The weight fibre is stable under precomposition with a permutation. -/
theorem sum_weightFibre_comp_perm {r : ℕ} (bb : Fin d → ℕ) (g : (Fin r → Fin d) → ℝ)
    (σ : Equiv.Perm (Fin r)) :
    ∑ w ∈ weightFibre bb, g (w ∘ σ) = ∑ w ∈ weightFibre bb, g w := by
  refine Finset.sum_nbij' (fun w => w ∘ σ) (fun w => w ∘ σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_weightFibre] at hw ⊢
    rw [weightOf_comp_perm, hw]
  · intro w hw
    rw [mem_weightFibre] at hw ⊢
    rw [weightOf_comp_perm, hw]
  · intro w _
    funext i
    simp
  · intro w _
    funext i
    simp
  · intro w _
    rfl

/-- **The weight component of the analytic jet** in terms of the monomial coefficient of the
series: `∂^bF(0) = (r!/#fibre(b)) · monoCoeff p r b`. -/
theorem weightComponent_normalJet_eq {F : (Fin d → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F p 0 R)
    {r : ℕ} (bb : Fin d → ℕ) (hb : ∑ i, bb i = r) :
    weightComponent (normalJet F r) bb =
      (Nat.multinomial Finset.univ bb : ℝ)⁻¹ * ((r.factorial : ℝ) * monoCoeff p r bb) := by
  rw [weightComponent_def, card_weightFibre bb hb]
  congr 1
  have h1 : ∀ w ∈ weightFibre bb, jetComponent (normalJet F r) w =
      ∑ σ : Equiv.Perm (Fin r), p r fun i => Pi.single (w (σ i)) 1 := fun w _ => by
    unfold jetComponent normalJet
    exact hF.iteratedFDeriv_eq_sum_of_completeSpace _
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ σ : Equiv.Perm (Fin r),
      ∑ w ∈ weightFibre bb, p r (fun i => Pi.single (w (σ i)) 1) =
        ∑ w ∈ weightFibre bb, p r (fun i => Pi.single (w i) 1) := fun σ =>
    sum_weightFibre_comp_perm bb (fun w => p r fun i => Pi.single (w i) 1) σ
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rfl

/-- ★ **The Taylor family of an analytic observable is the monomial coefficient family of its
series.** -/
theorem jetFamily_eq_monoFamily {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hF : HasFPowerSeriesOnBall F p 0 R) : jetFamily n F = monoFamily p := by
  funext bb
  rw [jetFamily_eq n F rfl, weightComponent_normalJet_eq hF bb rfl]
  unfold monoFamily
  have hm := multinomial_div_factorial bb rfl
  rw [← hm]
  have hM : (Nat.multinomial Finset.univ bb : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hr : ((∑ i, bb i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The Taylor family is `b`-weighted ℓ¹** under the dimension-loss margin `(n+1)·b < ρ < R`. -/
theorem absSummableAt_jetFamily {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hF : HasFPowerSeriesOnBall F p 0 R) {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) {b : ℝ} (hb : 0 ≤ b)
    (hbρ : ((n + 1 : ℕ) : ℝ) * b < ρ) : AbsSummableAt (jetFamily n F) b := by
  rw [jetFamily_eq_monoFamily hF]
  exact absSummableAt_monoFamily p (hρ.trans_le hF.r_le) hb hbρ

/-! ### Coefficient certificates from series data -/

variable {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}
  (C : ResolvedCertificate R D W K ϕ φ)

omit [T2Space U] [BorelSpace U] in
/-- **A coefficient certificate from series data**: a density factorisation family and the
identification of the amplitude datum with its Cauchy product with the monomial family of the
presentation's power series, under the dimension-loss radius margin. -/
noncomputable def ResolvedCertificate.CoefficientCertificate.ofSeries
    (cc : ∀ J, ↥(C.base J) → CoeffFamily (C.n J + 1))
    (cc_abs : ∀ J s, AbsSummableAt (cc J s) (C.cores.b J))
    (ρ : ∀ J, ↥(C.base J) → ℝ≥0) (hρ : ∀ J s, ((ρ J s : ℝ≥0) : ℝ≥0∞) < (C.T J).R s)
    (hbρ : ∀ J s, ((C.n J + 1 : ℕ) : ℝ) * C.cores.b J < ρ J s)
    (datum_eq : ∀ J s, toEta (C.cores.b J) ((C.cores.chart J).x s) =
      CoeffFamily.conv (cc J s) (monoFamily ((C.T J).p s))) :
    C.CoefficientCertificate where
  cc := cc
  cc_abs := cc_abs
  jet_abs := fun J s =>
    absSummableAt_jetFamily ((C.T J).analytic s) (hρ J s) (C.cores.b_pos J).le (hbρ J s)
  datum_eq := fun J s => by
    rw [datum_eq J s, jetFamily_eq_monoFamily ((C.T J).analytic s)]

end Grammar
