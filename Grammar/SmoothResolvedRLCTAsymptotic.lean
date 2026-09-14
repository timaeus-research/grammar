/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedExtremalRealised

/-!
# The RLCT asymptotic of the partition function at a positive realiser

Consult #129 packaging unit: the paper-facing statement of Theorem D in one theorem. At a point
`P₀` of the zero fibre realising the extremal data `(λ*, m*)` (CDXXXIX) where the prior is
positive (★★★ `rlct_asymptotic_of_realised`):

* every coefficient of every observable preceding `(λ*, m*−1)` vanishes,
* `N^{λ*}(log N)^{−(m*−1)} Z^U_N[G] → 𝒯^U_{λ*,m*−1}[G]` for every smooth observable `G`,
* `c := 𝒯^U_{λ*,m*−1}[1] > 0`, and
* the Euclidean partition function satisfies `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`
  (`Asymptotics.IsEquivalent`), with `λ* > 0`.

The automatic-existence form (`exists_rlct_asymptotic`): for a nonempty zero fibre and a prior
positive on the zero set of the phase inside its support, there are `λ* > 0`, `m* ≥ 1` and
`c > 0` with `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`, where `(λ*, m*)` is extremal data
of the intrinsic wall data. This identifies the RLCT and its multiplicity in the
Laplace-asymptotic sense; identification with the rightmost pole of the zeta function is not
formalised. Non-claims: no explicit local formula for `c`; the realiser hypothesis is the
primary statement (positivity throughout the zero set is only a convenient sufficient condition).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The extremal exponent is positive at a realiser with `m* ≥ 1`. -/
theorem lam_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) {P₀ : Ξ.R.U}
    (hP₀ : P₀ ∈ Ξ.zeroFibre) (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) :
    0 < lam := by
  classical
  have hpos : 0 < resonanceCount Ξ.R Ξ.hK0 lam P₀ := hres ▸ hm1
  unfold resonanceCount at hpos
  obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  obtain ⟨hp, n, hn⟩ := Multiset.mem_filter.1 hp
  have hk : (0 : ℝ) < p.1 := Nat.cast_pos.2 (fst_pos_of_mem_pairs Ξ.R Ξ.hK0 hp)
  have hle := h.1 P₀ hP₀ p hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp2 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg p.2
  by_contra hlam
  have hle0 : lam ≤ 0 := le_of_not_gt hlam
  nlinarith

/-- ★★★ **The RLCT asymptotic at a positive realiser**: preceding coefficients vanish for every
observable, the normalised partition functions converge, the leading coefficient of `1` is
positive, and `∫ prior · e^{−NK} ∼ 𝒯^U_{λ*,m*−1}[1] · N^{−λ*}(log N)^{m*−1}`. -/
theorem rlct_asymptotic_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) :
    (∀ ν p, Precedes ν p lam (m - 1) → ∀ (G : Ξ.R.U → ℝ)
        (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), (Ξ.withF G hG).coeff Y ν p = 0) ∧
      (∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G),
        Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
          (𝓝 ((Ξ.withF G hG).coeff Y lam (m - 1)))) ∧
      0 < (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) ∧
      (fun N => partitionObs Ξ.K Ξ.prior (fun _ => (1 : ℝ)) N) ~[atTop]
        fun N => (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) *
          (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  have hpos := Ξ.coeff_one_pos_of_realised Y h hP₀ hprior hres hm1
  refine ⟨Ξ.isLeadingIndex_of_extremalData Y h,
    fun G hG => Ξ.tendsto_normalised_Z_of_extremalData Y h hG, hpos, ?_⟩
  set c := (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) with hc
  have hv : ∀ᶠ N : ℝ in atTop, c * (N ^ (-lam) * Real.log N ^ (m - 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact (mul_pos hpos (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hN) _))).ne'
  refine (isEquivalent_iff_tendsto_one hv).2 ?_
  have hlim := (Ξ.tendsto_normalised_Z_of_extremalData Y h (G := fun _ => (1 : ℝ))
    contMDiff_const).div_const c
  rw [div_self hpos.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN0 : 0 ≤ N := by linarith
  have hA : (N ^ lam : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log N ^ (m - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
  have hc0 : c ≠ 0 := hpos.ne'
  simp only [Pi.div_apply]
  unfold normalised
  rw [Ξ.Z_one N, Real.rpow_neg hN0]
  field_simp

include Y in
/-- ★★★ **The RLCT asymptotic without a leading-index hypothesis**: for a nonempty zero fibre and
a prior positive on the zero set of the phase inside its support, there are `λ* > 0`, `m* ≥ 1`
extremal for the wall data and `c > 0` with `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`. -/
theorem exists_rlct_asymptotic (hne : Ξ.zeroFibre.Nonempty)
    (hpos : ∀ y ∈ tsupport Ξ.prior, Ξ.K y = 0 → 0 < Ξ.prior y) :
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧
      ∃ c : ℝ, 0 < c ∧ (fun N => partitionObs Ξ.K Ξ.prior (fun _ => (1 : ℝ)) N) ~[atTop]
        fun N => c * (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  obtain ⟨lam, m, P₀, hext, hP₀, hres, hm1⟩ := Ξ.exists_realised_extremalData hne
  obtain ⟨-, -, hc, hequiv⟩ :=
    Ξ.rlct_asymptotic_of_realised Y hext hP₀ (hpos _ hP₀.1 hP₀.2) hres hm1
  exact ⟨lam, m, Ξ.lam_pos_of_realised hext hP₀ hres hm1, hm1, hext, _, hc, hequiv⟩

end ResolvedData

end SmoothEngine

end Grammar
