/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedResonantSupport
import Grammar.SmoothResolvedLeadingOne

/-!
# The resolved expansion starts at the extremal pair of the zero fibre

Consult #128 follow-up (5), first half. Read the intrinsic wall data of Theorem D on the zero
fibre `Z₀ = π⁻¹(supp prior) ∩ {K ∘ π = 0}`: a pair `(λ*, m*)` is **extremal data** for the
resolved inputs (`IsExtremalData`) when every wall `(k, h)` through a point of `Z₀` has ratio
`(h+1)/(2k) ≥ λ*` and at most `m*` walls through any point of `Z₀` resonate with `λ*`. Then for
every index `(ν, p)` preceding `(λ*, m* − 1)` the resonant support set `Z₀ ∩ {r_ν ≥ p+1}` is
EMPTY (`resonantZeroFibre_eq_empty_of_precedes`: a wall resonating with `ν < λ*` would have
`2kν ≥ h+1 ≥ 2kλ*`, and at `ν = λ*` the count is at most `m* ≤ p`), so by the resonant support
theorem (CDXXXV) the coefficient `𝒯^U_{ν,p}[F]` vanishes for EVERY observable
(`coeff_eq_zero_of_precedes`): `(λ*, m* − 1)` is a leading index in the sense of CDXXXII
(`isLeadingIndex_of_extremalData`). Consequently, unconditionally in the leading-index
hypothesis: `N^{λ*}(log N)^{−(m*−1)} Z^U_N[F] → 𝒯^U_{λ*,m*−1}[F]` for every `F`
(`tendsto_normalised_Z_of_extremalData`), the leading functional is nonnegative on nonnegative
observables (`coeff_nonneg_of_extremalData`), and the leading coefficient of `Z^U_N[1]` is
nonnegative (`coeff_one_nonneg_of_extremalData`).

This is the "exponent lower bound" half of the RLCT identification: the expansion of every
`Z^U_N[F]` begins no earlier than `N^{−λ*}(log N)^{m*−1}`. Non-claims: that the coefficient at
`(λ*, m* − 1)` is nonzero (the positivity half, requiring a lower bound on the partition
function at a point realising the extremal pair with positive prior), or that the extremal
data is attained; the trivial data `(0, 0)` is always extremal, and the sharp statement is the
one for the largest `λ*` and then the smallest `m*`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- **Extremal data** `(λ*, m*)` of the zero fibre: every wall through a point of `Z₀` has
ratio `(h+1)/(2k) ≥ λ*`, and at most `m*` walls through any point of `Z₀` resonate with `λ*`. -/
def IsExtremalData (lam : ℝ) (m : ℕ) : Prop :=
  (∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, 2 * (p.1 : ℝ) * lam ≤ (p.2 : ℝ) + 1) ∧
    ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m

open Classical in
/-- The trivial data `(0, 0)` is extremal. -/
theorem isExtremalData_zero : Ξ.IsExtremalData 0 0 := by
  refine ⟨fun P _ p _ => by rw [mul_zero]; positivity, fun P _ => ?_⟩
  unfold resonanceCount
  rw [Nat.le_zero, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro p hp ⟨m, hm⟩
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg p.2
  linarith

variable {lam : ℝ} {m : ℕ}

open Classical in
/-- No wall through a point of the zero fibre resonates with an exponent `ν < λ*`. -/
theorem resonanceCount_eq_zero_of_lt (h : Ξ.IsExtremalData lam m) {P : Ξ.R.U}
    (hP : P ∈ Ξ.zeroFibre) {ν : ℝ} (hν : ν < lam) : resonanceCount Ξ.R Ξ.hK0 ν P = 0 := by
  unfold resonanceCount
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro p hp ⟨n, hn⟩
  have hk := fst_pos_of_mem_pairs Ξ.R Ξ.hK0 hp
  have hk' : (0 : ℝ) < p.1 := Nat.cast_pos.2 hk
  have h1 := h.1 P hP p hp
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- ★★ **Emptiness of the resonant support before the extremal pair**: for `(ν, p)` preceding
`(λ*, m* − 1)`, the support set `Z₀ ∩ {r_ν ≥ p+1}` is empty. -/
theorem resonantZeroFibre_eq_empty_of_precedes (h : Ξ.IsExtremalData lam m) {ν : ℝ} {p : ℕ}
    (hp : Precedes ν p lam (m - 1)) : Ξ.resonantZeroFibre ν p = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro P ⟨hP, hr⟩
  change p + 1 ≤ resonanceCount Ξ.R Ξ.hK0 ν P at hr
  rcases hp with hν | ⟨rfl, hq⟩
  · rw [Ξ.resonanceCount_eq_zero_of_lt h hP hν] at hr
    omega
  · have := h.2 P hP
    omega

/-- ★★★ **The expansion starts at the extremal pair**: every coefficient of every observable
at an index preceding `(λ*, m* − 1)` vanishes. -/
theorem coeff_eq_zero_of_precedes (h : Ξ.IsExtremalData lam m) {ν : ℝ} {p : ℕ}
    (hp : Precedes ν p lam (m - 1)) : Ξ.coeff Y ν p = 0 := by
  refine Ξ.coeff_eq_zero_of_eventually_zero_resonant Y ?_
  rw [Ξ.resonantZeroFibre_eq_empty_of_precedes h hp, nhdsSet_empty]
  exact Filter.eventually_bot

theorem isExtremalData_withF (h : Ξ.IsExtremalData lam m) (G : Ξ.R.U → ℝ)
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : (Ξ.withF G hG).IsExtremalData lam m := by
  unfold IsExtremalData zeroFibre withF
  exact h

/-- ★★★ **The extremal pair is a leading index** (in the sense of CDXXXII). -/
theorem isLeadingIndex_of_extremalData (h : Ξ.IsExtremalData lam m) :
    Ξ.IsLeadingIndex Y lam (m - 1) := fun _ _ hp G hG =>
  (Ξ.withF G hG).coeff_eq_zero_of_precedes Y (Ξ.isExtremalData_withF h G hG) hp

/-- ★★ **The normalised limit at the extremal pair**, unconditionally:
`N^{λ*}(log N)^{−(m*−1)} Z^U_N[G] → 𝒯^U_{λ*,m*−1}[G]`. -/
theorem tendsto_normalised_Z_of_extremalData (h : Ξ.IsExtremalData lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
      (𝓝 ((Ξ.withF G hG).coeff Y lam (m - 1))) :=
  Ξ.tendsto_normalised_Z Y (Ξ.isLeadingIndex_of_extremalData Y h) hG

/-- ★★ **Nonnegativity of the extremal functional** on observables nonnegative a.e. -/
theorem coeff_nonneg_of_extremalData (h : Ξ.IsExtremalData lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) :
    0 ≤ (Ξ.withF G hG).coeff Y lam (m - 1) :=
  Ξ.coeff_nonneg_of_leading Y (Ξ.isLeadingIndex_of_extremalData Y h) hG hG0

/-- The leading coefficient of the partition function `Z^U_N[1]` at the extremal pair is
nonnegative. -/
theorem coeff_one_nonneg_of_extremalData (h : Ξ.IsExtremalData lam m) :
    0 ≤ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) :=
  Ξ.coeff_nonneg_of_extremalData Y h contMDiff_const (Eventually.of_forall fun _ => zero_le_one)

end ResolvedData

end SmoothEngine

end Grammar
