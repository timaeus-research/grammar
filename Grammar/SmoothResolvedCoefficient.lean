/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedConsumer

/-!
# The resolved coefficient functional: linearity and locality along the zero fibre

Consult #126, Unit D3. The resolved coefficient functional `𝒯^U_{μ,q}[F] = coeff Ξ Y μ q` of
`SmoothResolvedConsumer` is

* **linear** in the smooth observable `F` on the resolved manifold (`coeff_add`, `coeff_smul`,
  `coeff_zero`) — by the linearity of `Z^U_N[F]` and the uniqueness of expansion coefficients;
* **local along the zero fibre** `C₀ = D ∩ π⁻¹(supp prior)` (a compact subset of `U`): if `F`
  vanishes on a neighbourhood of `C₀` then `Z^U_N[F]` is exponentially small (the phase `K ∘ π`
  is bounded below by a positive constant on the compact `π⁻¹(supp prior) ∖ O`), so every
  coefficient vanishes (`coeff_eq_zero_of_eventually_zero`); hence `𝒯^U_{μ,q}[F]` depends only
  on the germ of `F` along `C₀` (`coeff_congr_of_eventuallyEq`) — the support of the resolved
  functional lies in `D ∩ π⁻¹(supp prior)`.

Non-claims: no distribution-theoretic bound (jet estimate) on `U` yet; the locality is stated
for germs along `C₀`, not as a sharp support equality.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Linearity -/

theorem integrable_mul_exp {G : Ξ.R.U → ℝ} (hG : Continuous G) (N : ℝ) :
    Integrable (fun P => G P * Real.exp (-N * Ξ.K (Ξ.R.gv P))) Ξ.μU :=
  Ξ.integrable_of_continuous (hG.mul (Real.continuous_exp.comp
    (continuous_const.mul (Ξ.R.continuous_K_gv Ξ.hKc))))

theorem Z_withF_add {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G') (N : ℝ) :
    (Ξ.withF (fun P => G P + G' P) (hG.add hG')).Z N =
      (Ξ.withF G hG).Z N + (Ξ.withF G' hG').Z N := by
  change ∫ P, (G P + G' P) * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU =
    ∫ P, G P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU +
      ∫ P, G' P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU
  rw [← integral_add (Ξ.integrable_mul_exp hG.continuous N)
    (Ξ.integrable_mul_exp hG'.continuous N)]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

theorem Z_withF_smul {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (r : ℝ)
    (N : ℝ) :
    (Ξ.withF (fun P => r * G P) (contMDiff_const.mul hG)).Z N = r * (Ξ.withF G hG).Z N := by
  change ∫ P, r * G P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU =
    r * ∫ P, G P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

theorem Z_withF_zero (N : ℝ) : (Ξ.withF (fun _ => (0 : ℝ)) contMDiff_const).Z N = 0 := by
  change ∫ P, (0 : ℝ) * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU = 0
  simp

/-- ★ **Additivity** of the resolved coefficient functional. -/
theorem coeff_add {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G') (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun P => G P + G' P) (hG.add hG')).coeff Y μ q =
      (Ξ.withF G hG).coeff Y μ q + (Ξ.withF G' hG').coeff Y μ q :=
  SmoothExpansionCertificate.coeff_eq ((Ξ.withF _ (hG.add hG')).certificate Y)
    ((((Ξ.withF G hG).certificate Y).add ((Ξ.withF G' hG').certificate Y)).congr
      (Eventually.of_forall fun N => (Ξ.Z_withF_add hG hG' N).symm)) μ q

/-- ★ **Homogeneity** of the resolved coefficient functional. -/
theorem coeff_smul {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (r : ℝ) (μ : ℝ)
    (q : ℕ) :
    (Ξ.withF (fun P => r * G P) (contMDiff_const.mul hG)).coeff Y μ q =
      r * (Ξ.withF G hG).coeff Y μ q :=
  SmoothExpansionCertificate.coeff_eq ((Ξ.withF _ (contMDiff_const.mul hG)).certificate Y)
    ((((Ξ.withF G hG).certificate Y).smul r).congr
      (Eventually.of_forall fun N => (Ξ.Z_withF_smul hG r N).symm)) μ q

theorem coeff_zero (μ : ℝ) (q : ℕ) : (Ξ.withF (fun _ => (0 : ℝ)) contMDiff_const).coeff Y μ q = 0 :=
  SmoothExpansionCertificate.coeff_eq ((Ξ.withF _ contMDiff_const).certificate Y)
    (SmoothExpansionCertificate.zero.congr (Eventually.of_forall fun N => (Ξ.Z_withF_zero N).symm))
    μ q

/-! ### Locality along the zero fibre -/

/-- The zero fibre over the prior support: `D ∩ π⁻¹(supp prior)`. -/
def zeroFibre : Set Ξ.R.U := Ξ.R.gv ⁻¹' tsupport Ξ.prior ∩ {P | Ξ.K (Ξ.R.gv P) = 0}

theorem isCompact_zeroFibre : IsCompact Ξ.zeroFibre :=
  (Ξ.R.isCompact_gv_preimage_tsupport Ξ.prior Ξ.prior_compact Ξ.prior_W).inter_right
    (Ξ.R.isClosed_zeroSet Ξ.hKc)

theorem withF_zeroFibre (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).zeroFibre = Ξ.zeroFibre := rfl

/-- Off an open neighbourhood `O` of the zero fibre, the phase `K ∘ π` is bounded below by a
positive constant on `π⁻¹(supp prior) ∖ O`. -/
theorem exists_phase_gap {O : Set Ξ.R.U} (hO : IsOpen O) (hCO : Ξ.zeroFibre ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → P ∉ O → δ ≤ Ξ.K (Ξ.R.gv P) := by
  set S : Set Ξ.R.U := Ξ.R.gv ⁻¹' tsupport Ξ.prior \ O with hS
  have hSc : IsCompact S :=
    (Ξ.R.isCompact_gv_preimage_tsupport Ξ.prior Ξ.prior_compact Ξ.prior_W).diff hO
  have hpos : ∀ P ∈ S, 0 < Ξ.K (Ξ.R.gv P) := fun P hP => by
    rcases (Ξ.phaseU_nonneg P).lt_or_eq with h | h
    · exact h
    · exact absurd (hCO ⟨hP.1, h.symm⟩) hP.2
  by_cases hne : S.Nonempty
  · obtain ⟨P₀, hP₀, hmin⟩ := hSc.exists_isMinOn hne (Ξ.R.continuous_K_gv Ξ.hKc).continuousOn
    exact ⟨Ξ.K (Ξ.R.gv P₀), hpos P₀ hP₀, fun P hP hPO => hmin ⟨hP, hPO⟩⟩
  · exact ⟨1, one_pos, fun P hP hPO => absurd ⟨P, hP, hPO⟩ hne⟩

/-- If `F` vanishes on a neighbourhood of the zero fibre, `Z^U_N[F]` is exponentially small. -/
theorem abs_Z_le_of_eventually_zero (hF : ∀ᶠ P in 𝓝ˢ Ξ.zeroFibre, Ξ.F P = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, 0 ≤ N → |Ξ.Z N| ≤ (∫ P, |Ξ.F P| ∂Ξ.μU) * Real.exp (-δ * N) := by
  obtain ⟨O, hO, hCO, hFO⟩ := eventually_nhdsSet_iff_exists.1 hF
  obtain ⟨δ, hδ, hgap⟩ := Ξ.exists_phase_gap hO hCO
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have hint : Integrable (fun P => |Ξ.F P| * Real.exp (-δ * N)) Ξ.μU :=
    Ξ.F_int.norm.mul_const _
  have hbound : ∀ᵐ P ∂Ξ.μU,
      ‖Ξ.F P * Real.exp (-N * Ξ.K (Ξ.R.gv P))‖ ≤ |Ξ.F P| * Real.exp (-δ * N) := by
    filter_upwards [Ξ.ae_μU_mem] with P hP
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    by_cases hPO : P ∈ O
    · rw [hFO P hPO, abs_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hgap P hP hPO]))
        (abs_nonneg _)
  have := norm_integral_le_of_norm_le hint hbound
  rw [Real.norm_eq_abs, integral_mul_const] at this
  exact this

/-- The zero certificate of an exponentially small `Z^U_N[F]`. -/
noncomputable def zeroCertificate (hF : ∀ᶠ P in 𝓝ˢ Ξ.zeroFibre, Ξ.F P = 0) :
    SmoothExpansionCertificate Ξ.Z where
  Q := 1
  Q_pos := one_pos
  D := 0
  coeff := fun _ _ => 0
  coeff_support := fun _ _ h => absurd rfl h
  expansion := by
    obtain ⟨δ, hδ, hbound⟩ := Ξ.abs_Z_le_of_eventually_zero hF
    exact cutoffExpansion_of_exp_small 1 0 (half_pos hδ)
      (tendsto_mul_exp_of_exp_bound hbound (by linarith))

/-- ★★ **Locality**: if `F` vanishes on a neighbourhood of the zero fibre `D ∩ π⁻¹(supp prior)`,
every resolved coefficient of `F` vanishes. -/
theorem coeff_eq_zero_of_eventually_zero (hF : ∀ᶠ P in 𝓝ˢ Ξ.zeroFibre, Ξ.F P = 0) (μ : ℝ)
    (q : ℕ) : Ξ.coeff Y μ q = 0 :=
  SmoothExpansionCertificate.coeff_eq (Ξ.certificate Y) (Ξ.zeroCertificate hF) μ q

/-- ★★★ **Germ locality of the resolved coefficient functional**: two smooth observables on `U`
that agree on a neighbourhood of the zero fibre `D ∩ π⁻¹(supp prior)` have the same resolved
coefficients — `𝒯^U_{μ,q}` is supported in `D ∩ π⁻¹(supp prior)`. -/
theorem coeff_congr_of_eventuallyEq {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (h : G =ᶠ[𝓝ˢ Ξ.zeroFibre] G') (μ : ℝ) (q : ℕ) :
    (Ξ.withF G hG).coeff Y μ q = (Ξ.withF G' hG').coeff Y μ q := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hev : ∀ᶠ P in 𝓝ˢ Ξ.zeroFibre, G P + (-1 : ℝ) * G' P = 0 := by
    filter_upwards [h] with P hP
    rw [hP]; ring
  have hdiff := (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).coeff_eq_zero_of_eventually_zero Y
    hev μ q
  have h1 := Ξ.coeff_add Y hG hG'' μ q
  have h2 := Ξ.coeff_smul Y hG' (-1) μ q
  linarith

/-- The locality for the observable of `Ξ` itself: `F` agreeing with `G` near the zero fibre. -/
theorem coeff_eq_of_eventuallyEq {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (h : Ξ.F =ᶠ[𝓝ˢ Ξ.zeroFibre] G) (μ : ℝ) (q : ℕ) :
    Ξ.coeff Y μ q = (Ξ.withF G hG).coeff Y μ q :=
  Ξ.coeff_congr_of_eventuallyEq Y Ξ.F_smooth hG h μ q

end ResolvedData

end SmoothEngine

end Grammar
