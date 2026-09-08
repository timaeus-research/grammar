# Fidelity review v32 — units 290–292 (grammar §3 rewrite, Programme P per Astra #37)

You are reviewing three small Lean 4 / Mathlib units in `timaeus-research/grammar` (branch `tide/population-normal-form`, base `99fbdd8`, 283 modules, no `sorry`, no added `axiom`; everything compiles). They open the §3 programme designed in Astra consult #37 (your own design, reproduced below in relevant part): rewrite the grammar paper's population theorem `thm:expectation_expansion` around the §4 Taylor-tree machinery at zero empirical process (`ξ = 0`), with 20-unit cap and reviews after units 3, 5, 9, 12, 16, 20. This is the unit-3 review. Astra #37's acceptance criteria for these units:

* u290: "the theorem exposes the original population integral, not only the family integral. Preserve the complete existing remainder conclusion." Proof by instantiating `thm_TaylorTree_taylor` with the constant-zero holomorphic function; companion `taylorFamily (n+1) (fun _ => 0) = 0`.
* u291: `familyCoeffSeries n h k β 0 cη μ j = familyCoeffTerm … 0`, helper `p ≠ 0 → familyCoeffTerm … 0 cη μ j p = 0` via the zero fluctuation family and positive convolution powers of zero; "expand the surviving term in documentation against the existing K_k Σ_γ cη_γ S_0 kernel. This outer-series collapse does not by itself establish absolute convergence of the inner amplitude series for arbitrary cη; invoke the existing admissibility hypotheses for that assertion."
* u292: `fluctMoment β 0 0 μ 0 = Γ(μ) β^{-μ}`, explicit `μ > 0, β > 0`, "no derivative-under-asymptotics argument".
* Unit-3 review: "check that the zero-noise specialisation really uses the population integrand and that neither amplitude factorials nor box scaling have been duplicated."

Frozen background (reviewed v1–v31): `thm_TaylorTree_taylor` (Headline XXXIII), `TaylorTreeConclusion`, `familyCoeffSeries/familyCoeffTerm/kernelFunctional/kernelS`, `fluctMoment`, `phaseKernel`, `integral_rpow_mul_exp_neg_mul`, `CoeffFamily.conv/convPow/fluctFamily`, `familySpectralCoeff_eq_series`. Relevant definitions:
```lean
abbrev CoeffFamily (d : ℕ) := (Fin d → ℕ) → ℝ
def AbsSummable (c : CoeffFamily d) : Prop := Summable fun γ => |c γ|
noncomputable def scale (c : CoeffFamily d) (b : ℝ) : CoeffFamily d := fun γ => c γ * b ^ (∑ i, γ i)
noncomputable def CoeffFamily.conv (c e : CoeffFamily d) : CoeffFamily d := fun γ => ∑ α ∈ Finset.Iic γ, c α * e (γ - α)
noncomputable def CoeffFamily.convPow (c : CoeffFamily d) : ℕ → CoeffFamily d
  | 0 => fun γ => if γ = 0 then 1 else 0
  | p + 1 => conv c (convPow c p)
noncomputable def CoeffFamily.fluctFamily (c : CoeffFamily d) : CoeffFamily d := fun γ => if γ = 0 then 0 else c γ
noncomputable def kernelS (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ) (γ : Fin (n + 1) → ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico j (n + 1), PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) * fluctMoment β a p μ (q - j)
noncomputable def kernelFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ) (f : CoeffFamily (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑' γ, f γ * kernelS n h k β a p μ j γ
noncomputable def familyCoeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j p : ℕ) : ℝ :=
  β ^ p / (p.factorial : ℝ) * kernelFunctional n h k β (cξ 0) p μ j (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p))
noncomputable def familyCoeffSeries … (cξ cη) (μ : ℝ) (j : ℕ) : ℝ := ∑' p : ℕ, familyCoeffTerm n h k β cξ cη μ j p
theorem familySpectralCoeff_eq_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = familyCoeffSeries n h k β cξ cη μ j
noncomputable def phaseKernel (β a : ℝ) (p : ℕ) (t : ℝ) : ℝ := Real.sqrt t ^ p * Real.exp (-(β * t) + β * Real.sqrt t * a)
noncomputable def fluctMoment (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t
theorem integral_rpow_mul_exp_neg_mul (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) : ∫ t in Ioi (0 : ℝ), t ^ (l - 1) * Real.exp (-(β * t)) = Real.Gamma l * β ^ (-l)
noncomputable def coordDeriv : (d : ℕ) → ((Fin d → ℂ) → ℂ) → (Fin d → ℕ) → ℂ
  | 0, F, _ => F Fin.elim0
  | d + 1, F, γ => iteratedDeriv (γ 0) (fun x => coordDeriv d (fun w' => F (Fin.cons x w')) (Fin.tail γ)) 0
noncomputable def multiFactorial {d : ℕ} (γ : Fin d → ℕ) : ℂ := ∏ i, ((γ i).factorial : ℂ)
noncomputable def taylorFamily (d : ℕ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d := fun γ => (coordDeriv d F γ / multiFactorial γ).re
-- origPhaseIntegral n h k β N b ξ η = ∫_{(0,b]^{n+1}} η u · u^h · exp(-βN u^{2k} + β√N u^k ξ u) du  (Bochner set integral over piBox (Ioc 0 b))
-- familyPhaseIntegralBox n h k β N b cξ cη = the same integral with ξ, η replaced by the evaluated families (equal to the original by thm_TaylorTree_taylor's second clause)
```
`thm_TaylorTree_taylor` and `TaylorTreeConclusion` were quoted to you verbatim in consult #37 (structure fields `coeff_eq`, `vanish`, `summable`, `series`, `remainder`, `isBigO`, `dictionary`).

## The three units (complete files)

### Grammar/PopulationTaylorTree.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TaylorTreeDerivatives

/-!
# The population Taylor tree (grammar §3 rewrite, Astra #37 P1, unit 290)

The population partition function of §3 is, chart by chart, the standard integral of §4 at zero
empirical process (`rem:pop_vs_emp`: "the population version is the specialisation `ξ = 0`").
This file records that specialisation of Headline XXXIII on the **original** integral: for an
amplitude `η` on `(0,b]^{n+1}` with a holomorphic extension `Fη` to the polydisc of radius
`R > b`, the population integral
```
𝒵(N) = ∫_{(0,b]^{n+1}} η(u) u^h e^{-βN u^{2k}} du = origPhaseIntegral n h k β N b 0 η
```
satisfies the full Taylor-tree conclusion (`TaylorTreeConclusion`: cutoff-independent canonical
coefficients equal to the explicit series, support on `Λ(h,k)`, quantitative remainder for every
cutoff, `IsBigO` in the sample size, derivative dictionary) with the zero phase family and the
Taylor-derivative amplitude family `Re(∂^γ Fη(0)/γ!)`. The phase family of the constant zero
function is the zero family (`taylorFamily_const_zero`), so the conclusion is also stated with
`0 : CoeffFamily` in the phase slot (`population_TaylorTree_taylor'`).

Scope (Astra #37): this is the analytic normal-form population theorem for supplied one-sided
box data. It does not construct a resolution, a tubular neighbourhood or an adapted partition of
unity, and it does not show that a geometrically localised amplitude has a holomorphic normal
extension. Lean `N` is the paper's sample size `n`; the log degree `j` is the paper's `m − 1`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Grammar

/-- Every fixed-order coordinate derivative of the constant zero function vanishes. -/
theorem coordDeriv_const_zero : ∀ (d : ℕ) (γ : Fin d → ℕ),
    coordDeriv d (fun _ : Fin d → ℂ => (0 : ℂ)) γ = 0
  | 0, _ => by simp [coordDeriv]
  | d + 1, γ => by
    have ih : (fun x : ℂ => coordDeriv d
        (fun w' : Fin d → ℂ => (fun _ : Fin (d + 1) → ℂ => (0 : ℂ)) (Fin.cons x w'))
        (Fin.tail γ)) = fun _ => (0 : ℂ) := by
      funext x
      exact coordDeriv_const_zero d _
    change iteratedDeriv (γ 0) (fun x : ℂ => coordDeriv d
        (fun w' : Fin d → ℂ => (fun _ : Fin (d + 1) → ℂ => (0 : ℂ)) (Fin.cons x w'))
        (Fin.tail γ)) 0 = 0
    rw [ih, iteratedDeriv_const]
    simp

/-- The Taylor-derivative family of the constant zero function is the zero family. -/
theorem taylorFamily_const_zero (d : ℕ) :
    taylorFamily d (fun _ : Fin d → ℂ => (0 : ℂ)) = 0 := by
  funext γ
  simp [taylorFamily, coordDeriv_const_zero]

/-- **The population Taylor tree on the original integral** (`thm:TaylorTree` at `ξ = 0`, the
§3 population instance of Headline XXXIII): for `η` on `(0,b]^{n+1}` with a holomorphic extension
`Fη` to the polydisc of radius `R > b`, the population integral `∫ η u^h e^{-βN u^{2k}}` has the
full Taylor-tree conclusion for the zero phase family and the amplitude family `Re(∂^γ Fη(0)/γ!)`,
and the family integral is the original population integral. -/
theorem population_TaylorTree_taylor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (taylorFamily (n + 1) (fun _ : Fin (n + 1) → ℂ => (0 : ℂ)))
        (taylorFamily (n + 1) Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b
          (taylorFamily (n + 1) (fun _ : Fin (n + 1) → ℂ => (0 : ℂ))) (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N b (fun _ => 0) η := by
  have h0 : DifferentiableOn ℂ (fun _ : Fin (n + 1) → ℂ => (0 : ℂ)) (openPolydisc (n + 1) R) :=
    differentiableOn_const 0
  have hξ0 : ∀ u ∈ piBox (n + 1) (Ioc 0 b),
      ((fun _ : Fin (n + 1) → ℂ => (0 : ℂ)) fun i => (u i : ℂ)).re =
        (fun _ : Fin (n + 1) → ℝ => (0 : ℝ)) u := by
    intro u _
    simp
  exact thm_TaylorTree_taylor n h k hk β hβ hb hbR h0 hFη hξ0 hη

/-- The population Taylor tree with the zero coefficient family in the phase slot. -/
theorem population_TaylorTree_taylor' (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b 0 (taylorFamily (n + 1) Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N b (fun _ => 0) η := by
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor n h k hk β hβ hb hbR hFη hη
  rw [taylorFamily_const_zero] at hC hI
  exact ⟨C, hC, hI⟩

end Grammar
```

### Grammar/PopulationCoefficient.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FamilyCoeffSeries

/-!
# Collapse of the population coefficient series (grammar §3 rewrite, Astra #37 P1, unit 291)

At zero phase the Taylor-tree coefficient series `A_{μ,j}(cξ,cη) = ∑_p β^p/p! T_p(cη * J^{*p})`
(Headline XXIX) collapses to its `p = 0` term: the constant-free part `J` of the zero family is
zero, its positive convolution powers vanish, and the `p = 0` convolution power is the delta at
`γ = 0`, so `cη * J^{*0} = cη`. Hence
```
familyCoeffSeries n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη
                                   = K_k ∑_γ cη_γ S_0(μ,j;γ),
```
the paper's dressed-moment expansion `∑_γ (η_γ/γ!)·[coefficient of N^{-μ}(log N)^j in M_{h+γ}]`
(`eq:tubular_expansion`) with `S_0(μ,j;γ) = ∑_{q≥j} coeffAt(ρ_{h+γ},μ,q) C(q,j)
fluctMoment β 0 0 μ (q−j)` (`kernelS`). Under absolute summability of `cη` and `μ > 0` this is the
canonical (limit-defined) family coefficient (`familySpectralCoeff_population`).

These are algebraic identities; they do not by themselves assert convergence of the inner
amplitude series (`kernelFunctional` is a `tsum`), which is supplied by the admissibility
hypotheses of the Taylor tree. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- The constant-free part of the zero family is zero. -/
theorem CoeffFamily.fluctFamily_zero : fluctFamily (0 : CoeffFamily d) = 0 := by
  funext γ
  unfold fluctFamily
  split_ifs <;> rfl

/-- Convolution with the zero family on the left. -/
theorem CoeffFamily.conv_zero_left (e : CoeffFamily d) : conv (0 : CoeffFamily d) e = 0 := by
  funext γ
  simp [conv]

/-- Convolution with the zero family on the right. -/
theorem CoeffFamily.conv_zero_right (c : CoeffFamily d) : conv c (0 : CoeffFamily d) = 0 := by
  funext γ
  simp [conv]

/-- Positive convolution powers of the zero family vanish. -/
theorem CoeffFamily.convPow_zero_family {p : ℕ} (hp : p ≠ 0) :
    convPow (0 : CoeffFamily d) p = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  simp [convPow, conv_zero_left]

/-- Convolution with the zeroth convolution power (the delta family at `γ = 0`) is the
identity. -/
theorem CoeffFamily.conv_convPow_zero (c e : CoeffFamily d) : conv c (convPow e 0) = c := by
  funext γ
  simp only [convPow, conv]
  rw [Finset.sum_eq_single γ]
  · simp
  · intro α hα hne
    have hle : α ≤ γ := Finset.mem_Iic.1 hα
    have hsub : γ - α ≠ 0 := by
      intro h0
      apply hne
      refine le_antisymm hle fun i => ?_
      have hi := congrFun h0 i
      simp only [Pi.sub_apply, Pi.zero_apply] at hi
      exact Nat.sub_eq_zero_iff_le.1 hi
    simp [hsub]
  · intro hγ
    exact absurd (Finset.mem_Iic.2 le_rfl) hγ

/-- The kernel functional of the zero family vanishes. -/
theorem kernelFunctional_zero_family (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ)
    (j : ℕ) : kernelFunctional n h k β a p μ j (0 : CoeffFamily (n + 1)) = 0 := by
  simp [kernelFunctional]

/-- At zero phase every coefficient term of positive fluctuation order vanishes. -/
theorem familyCoeffTerm_population_ne (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) {p : ℕ} (hp : p ≠ 0) :
    familyCoeffTerm n h k β 0 cη μ j p = 0 := by
  unfold familyCoeffTerm
  rw [fluctFamily_zero, convPow_zero_family hp, conv_zero_right, kernelFunctional_zero_family,
    mul_zero]

/-- At zero phase the `p = 0` coefficient term is the kernel functional of the amplitude family
with zero constant phase: `K_k ∑_γ cη_γ S_0(μ,j;γ)`. -/
theorem familyCoeffTerm_population_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffTerm n h k β 0 cη μ j 0 = kernelFunctional n h k β 0 0 μ j cη := by
  unfold familyCoeffTerm
  rw [fluctFamily_zero, conv_convPow_zero]
  simp

/-- **Collapse of the population coefficient series**: at zero phase the Taylor-tree coefficient
series is its `p = 0` term. -/
theorem familyCoeffSeries_population_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffSeries n h k β 0 cη μ j = familyCoeffTerm n h k β 0 cη μ j 0 := by
  unfold familyCoeffSeries
  exact tsum_eq_single 0 fun p hp => familyCoeffTerm_population_ne n h k β cη μ j hp

/-- The population coefficient series is the dressed-moment kernel functional
`K_k ∑_γ cη_γ S_0(μ,j;γ)` of the amplitude family. -/
theorem familyCoeffSeries_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) :
    familyCoeffSeries n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη := by
  rw [familyCoeffSeries_population_term, familyCoeffTerm_population_zero]

/-- The canonical population coefficient (the limit-defined family spectral coefficient at zero
phase) is the dressed-moment kernel functional, for absolutely summable amplitude data and
`μ > 0`. -/
theorem familySpectralCoeff_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β 0 cη μ j = kernelFunctional n h k β 0 0 μ j cη := by
  have h0 : AbsSummable (0 : CoeffFamily (n + 1)) := by
    simp [AbsSummable]
  rw [familySpectralCoeff_eq_series n h k hk β hβ h0 hη hμ j, familyCoeffSeries_population]

end Grammar
```

### Grammar/PopulationGammaMoment.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialPhaseTail
import Grammar.GammaLogAsymptotic

/-!
# The zero-phase, zero-log fluctuation moment is the Gamma integral (Astra #37 P1, unit 292)

The kernel moments of the Taylor tree are `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1} (−log t)^i (√t)^p
e^{−βt + β√t a} dt`. At zero phase (`a = 0`) and zero fluctuation order (`p = 0`) they are the
Mellin moments `∫₀^∞ t^{μ-1} (−log t)^i e^{−βt} dt` of the pure exponential; for `i = 0` this is
the Gamma integral `Γ(μ) β^{−μ}` (`μ > 0`, `β > 0`). This is the analytic constant of the paper's
bare normal moments (`eq:a_minus_m_explicit` with the Tauberian factor `Γ(λ)`), now identified
inside the Taylor-tree coefficient kernel `S_0(μ,j;γ)` at `q = j`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- At zero phase and zero fluctuation order the kernel is the pure exponential. -/
theorem phaseKernel_zero_zero (β t : ℝ) : phaseKernel β 0 0 t = Real.exp (-(β * t)) := by
  simp [phaseKernel]

/-- **Zero-phase, zero-log Mellin moment**: `fluctMoment β 0 0 μ 0 = Γ(μ) β^{−μ}` for `μ > 0`,
`β > 0`. -/
theorem fluctMoment_population_zero_log (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) :
    fluctMoment β 0 0 μ 0 = Real.Gamma μ * β ^ (-μ) := by
  unfold fluctMoment
  rw [← integral_rpow_mul_exp_neg_mul μ β hμ hβ]
  congr 1
  funext t
  rw [phaseKernel_zero_zero]
  simp

/-- The zero-phase, zero-log moment is strictly positive. -/
theorem fluctMoment_population_zero_log_pos (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) :
    0 < fluctMoment β 0 0 μ 0 := by
  rw [fluctMoment_population_zero_log β μ hβ hμ]
  exact mul_pos (Real.Gamma_pos_of_pos hμ) (Real.rpow_pos_of_pos hβ _)

end Grammar
```

## Questions
1. Statement fidelity: does u290 deliver the population instance of `thm:TaylorTree` on the original integral `∫ η u^h e^{-βN u^{2k}}` with the complete remainder conclusion (acceptance criterion above)? Is the `(fun _ => 0)` phase the right formal rendering of `ξ = 0`, and is anything about `η`'s hypothesis (holomorphic extension on the polydisc, real-part agreement on the box) misdescribed in the docstring?
2. u291: are the identities correct as stated (no hidden convergence claim; `kernelFunctional` is a `tsum` and the docstring says so)? Is `familySpectralCoeff_population` the right "canonical coefficient collapse" and are its hypotheses (`AbsSummable cη`, `μ > 0`, `hk`, `hβ`) exactly those of the frozen `familySpectralCoeff_eq_series`? Is the claim "this is the paper's dressed-moment expansion" accurate given that `kernelS` uses the state-density coefficients of `u^{h+γ}` and the moments `fluctMoment β 0 0 μ (q−j)`?
3. u292: correct, with the right positivity hypotheses? Any issue with `Real.rpow` `β ^ (-μ)` vs the paper's `β^{-λ}`?
4. Astra #37 unit-3 check: has the zero-noise specialisation really used the population integrand, and have amplitude factorials or box scaling been duplicated anywhere? (Note `taylorFamily` already divides by `γ!`, and `TaylorTreeConclusion.coeff_eq` uses `scale cξ b`, `scale cη b`.)
5. Any blocking or nonblocking fixes before proceeding to the remaining P1 units (leading-coefficient identification by uniqueness against Headline VIII's face functional: population `CutoffExpansion` → support eliminates exponents below λ → compare with the normalised limit to kill log degrees above m−1 → identify the canonical `(λ, m−1)` coefficient with the face functional; start at `b = 1`)? Please also comment on the planned route: is uniqueness of asymptotic coefficients against `headline_normal_moment_amplitude` (a `Tendsto` of the normalised integral) enough to identify `C(λ, m−1)`, given that the `CutoffExpansion` at cutoff `L = λ + 1/(2Q)` (say) gives `Z(N) = Σ_{μ ≤ λ} N^{-μ} Σ_j C(μ,j)(log N)^j + O(N^{-L}(1+log N)^n)` with the sub-λ coefficients already known to vanish by support? What exactly must be proved to conclude `C(λ, j) = 0` for `j > m−1` and `C(λ, m−1) = A` — is dividing by `N^{-λ}(log N)^{m-1}` and taking limits sufficient (yes if the sum over `j` is a polynomial in `log N` with the top surviving degree read off by the limit), and do you see a cleaner route?

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. Note the statement extracts above are complete files, not extractor output.
