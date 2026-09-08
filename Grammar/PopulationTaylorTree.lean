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
amplitude `η` on `(0,b]^{n+1}` admitting a holomorphic function `Fη` on the polydisc of radius
`R > b` whose real part agrees with `η` on the box (real-part agreement, not a complex-valued
extension), the population integral
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
§3 population instance of Headline XXXIII): for `η` on `(0,b]^{n+1}` and a holomorphic `Fη` on
the polydisc of radius `R > b` with `Re Fη = η` on the box, the population integral `∫ η u^h e^{-βN u^{2k}}` has the
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
