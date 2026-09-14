/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedResonantSupport
import Grammar.SmoothResolvedLeadingOne
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The leading resolved functional is bounded by the supremum over its support set

Consult #128, follow-up (1). At a leading index `(μ₀, q₀)` the resolved coefficient functional
`𝒯 = 𝒯^U_{μ₀,q₀}` is positive and of order zero on the carrier `L = π⁻¹(supp prior)`
(`abs_coeff_le_of_leading`). By the resonant support theorem it depends only on the germ of the
observable along the compact resonant zero fibre `S = Z₀ ∩ {r_{μ₀} ≥ q₀ + 1} ⊆ L`. Combining the
two by **smooth saturation** — replacing `G` by `θ ∘ G` with `θ` smooth, equal to the identity on
an interval containing `G(S)` and bounded by `M` (`saturate`, from a `ContDiffBump`) — gives the
sharper bound

  `|𝒯[G]| ≤ (sup_S |G|) · 𝒯[1]`   (`abs_coeff_le_sup_of_leading`),

so the leading functional depends only on the VALUES of the observable on `S` (a stronger property
than germ locality: no normal derivatives enter), and it is bounded by the supremum norm on its
support set times its mass. Also the contrapositive form of the resonant support theorem:
`𝒯^U_{μ,q}[F] ≠ 0 → S_{μ,q} ∩ tsupport F ≠ ∅` (`nonempty_inter_tsupport_of_coeff_ne_zero`).

Non-claims: no Riesz representation (the extension of the functional from smooth restrictions to
`C(S)` is not formalised); the results are conditional on the leading-index hypothesis.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

/-! ### Smooth saturation -/

/-- A smooth bump on `ℝ` equal to `1` on `[-r, r]`, supported in `(-M, M)`. -/
noncomputable def satBump {r M : ℝ} (hr : 0 < r) (hrM : r < M) : ContDiffBump (0 : ℝ) where
  rIn := r
  rOut := M
  rIn_pos := hr
  rIn_lt_rOut := hrM

/-- The smooth saturation `θ(t) = t · bump(t)`: the identity on `[-r, r]`, bounded by `M`. -/
noncomputable def saturate {r M : ℝ} (hr : 0 < r) (hrM : r < M) (t : ℝ) : ℝ :=
  t * satBump hr hrM t

theorem contDiff_saturate {r M : ℝ} (hr : 0 < r) (hrM : r < M) :
    ContDiff ℝ ∞ (saturate hr hrM) :=
  contDiff_id.mul (satBump hr hrM).contDiff

theorem saturate_eq_self {r M : ℝ} (hr : 0 < r) (hrM : r < M) {t : ℝ} (ht : |t| ≤ r) :
    saturate hr hrM t = t := by
  have h1 : satBump hr hrM t = 1 := by
    refine (satBump hr hrM).one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact ht
  unfold saturate
  rw [h1, mul_one]

theorem abs_saturate_le {r M : ℝ} (hr : 0 < r) (hrM : r < M) (t : ℝ) :
    |saturate hr hrM t| ≤ M := by
  unfold saturate
  by_cases ht : M ≤ |t|
  · have h0 : satBump hr hrM t = 0 := by
      refine (satBump hr hrM).zero_of_le_dist ?_
      rw [dist_zero_right, Real.norm_eq_abs]
      exact ht
    rw [h0, mul_zero, abs_zero]
    linarith [hr]
  · rw [abs_mul, abs_of_nonneg (satBump hr hrM).nonneg]
    calc |t| * satBump hr hrM t ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (satBump hr hrM).le_one (abs_nonneg _)
      _ ≤ M := by rw [mul_one]; exact (not_le.1 ht).le

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- **Contrapositive of the resonant support theorem**: a nonzero coefficient forces the
observable's support to meet the resonant zero fibre. -/
theorem nonempty_inter_tsupport_of_coeff_ne_zero {μ : ℝ} {q : ℕ} (h : Ξ.coeff Y μ q ≠ 0) :
    (Ξ.resonantZeroFibre μ q ∩ tsupport Ξ.F).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  refine h (Ξ.coeff_eq_zero_of_eventually_zero_resonant Y (eventually_nhdsSet_iff_exists.2
    ⟨(tsupport Ξ.F)ᶜ, (isClosed_tsupport _).isOpen_compl, fun P hP hsP => ?_,
      fun P hP => image_eq_zero_of_notMem_tsupport hP⟩))
  exact Set.eq_empty_iff_forall_notMem.1 hne P ⟨hP, hsP⟩

variable {μ₀ : ℝ} {q₀ : ℕ}

/-- One step of the saturation argument: `|𝒯[G]| ≤ M · 𝒯[1]` for every `M` strictly above a bound
of `|G|` on the resonant zero fibre. -/
theorem abs_coeff_le_mul_of_lt (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) {s M : ℝ} (hs : 0 ≤ s)
    (hGs : ∀ P ∈ Ξ.resonantZeroFibre μ₀ q₀, |G P| ≤ s) (hsM : s < M) :
    |(Ξ.withF G hG).coeff Y μ₀ q₀| ≤
      M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ := by
  set r : ℝ := (s + M) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrM : r < M := by rw [hr]; linarith
  have hsr : s < r := by rw [hr]; linarith
  set θ := saturate hr0 hrM with hθ
  have hθG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => θ (G P)) :=
    (contDiff_saturate hr0 hrM).contMDiff.comp hG
  -- `θ ∘ G = G` on the open set `{|G| < r}`, which contains the resonant zero fibre
  have hev : (fun P => θ (G P)) =ᶠ[𝓝ˢ (Ξ.resonantZeroFibre μ₀ q₀)] G := by
    refine eventually_nhdsSet_iff_exists.2 ⟨{P | |G P| < r}, ?_,
      fun P hP => (hGs P hP).trans_lt hsr, fun P hP => saturate_eq_self hr0 hrM (le_of_lt hP)⟩
    exact isOpen_lt (continuous_abs.comp hG.continuous) continuous_const
  rw [← Ξ.coeff_congr_of_eventuallyEq_resonant Y hθG hG hev]
  exact Ξ.abs_coeff_le_of_leading Y hlead hθG fun P _ => abs_saturate_le hr0 hrM (G P)

/-- ★★★ **The leading functional is bounded by the supremum over its support set**: at a leading
index, `|𝒯[G]| ≤ s · 𝒯[1]` for every bound `s` of `|G|` on the resonant zero fibre
`Z₀ ∩ {r_{μ₀} ≥ q₀+1}` — the leading functional depends only on the values of the observable on
its support set. -/
theorem abs_coeff_le_sup_of_leading (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) {s : ℝ} (hs : 0 ≤ s)
    (hGs : ∀ P ∈ Ξ.resonantZeroFibre μ₀ q₀, |G P| ≤ s) :
    |(Ξ.withF G hG).coeff Y μ₀ q₀| ≤
      s * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ := by
  set c := (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ with hc
  have hc0 : 0 ≤ c := Ξ.coeff_one_nonneg_of_leading Y hlead
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hM : s < s + ε / (c + 1) := by
    have : 0 < ε / (c + 1) := div_pos hε (by linarith)
    linarith
  calc |(Ξ.withF G hG).coeff Y μ₀ q₀| ≤ (s + ε / (c + 1)) * c :=
        Ξ.abs_coeff_le_mul_of_lt Y hlead hG hs hGs hM
    _ = s * c + ε * (c / (c + 1)) := by ring
    _ ≤ s * c + ε := by
        have : c / (c + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        nlinarith [hε.le]

/-- The values of the observable on the resonant zero fibre determine the leading coefficient:
two observables agreeing on `Z₀ ∩ {r_{μ₀} ≥ q₀+1}` have the same leading coefficient. -/
theorem coeff_eq_of_eqOn_resonantZeroFibre_of_leading (hlead : Ξ.IsLeadingIndex Y μ₀ q₀)
    {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G') (h : EqOn G G' (Ξ.resonantZeroFibre μ₀ q₀)) :
    (Ξ.withF G hG).coeff Y μ₀ q₀ = (Ξ.withF G' hG').coeff Y μ₀ q₀ := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hbound := Ξ.abs_coeff_le_sup_of_leading Y hlead hsum (s := 0) le_rfl fun P hP => by
    rw [h hP]; simp
  rw [zero_mul] at hbound
  have hzero : (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).coeff Y μ₀ q₀ = 0 :=
    abs_eq_zero.1 (le_antisymm hbound (abs_nonneg _))
  have h1 := Ξ.coeff_add Y hG hG'' μ₀ q₀
  have h2 := Ξ.coeff_smul Y hG' (-1) μ₀ q₀
  linarith

end ResolvedData

end SmoothEngine

end Grammar
