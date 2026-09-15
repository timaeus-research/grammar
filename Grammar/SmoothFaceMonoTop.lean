/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothExactResonance
import Grammar.SmoothLeadingTerm
import Grammar.SmoothFiniteUniqueness
import Grammar.CutoffScaling

/-!
# The top face-monomial coefficient

Consult #130, Unit E1b. For a face all of whose coordinates resonate exactly with `μ`
(`2k_iμ = e_i + 1` for every `i`), the face-monomial coefficient at the top logarithmic power
`|ι| − 1` is the explicit positive constant

  `faceMonoCoeff k e β b μ (|ι|−1) = Γ(μ) β^{−μ} / ((|ι|−1)! ∏_i 2k_i)`

(★★ `faceMonoCoeff_top`), independent of the box side `b`. Proof: the two-regime estimate of the
face monomial is a cutoff expansion with coefficients `faceMonoCoeff` (`faceMono_cutoffExpansion`),
all coefficients preceding `(μ, |ι|−1)` vanish (exact resonance, CDXLIV), so the normalised face
monomial converges to the top coefficient (`tendsto_normalised_faceMono`, via
`tendsto_normalised_of_leading`); the face monomial is the cutoff monomial box integral of the
analytic programme (`faceMono_eq_cutoff`), whose equal-ratio asymptotic is explicit
(`monomialBoxRealCutoff_equal_isEquivalent`), and limits are unique. Engine form for a face `J`:
`faceCoef_top_eq`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset Asymptotics
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

open MonoRep CoeffFamily

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The face monomial two-regime estimate is a cutoff expansion. -/
theorem faceMono_cutoffExpansion (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β)
    (hb : 0 < b) :
    CutoffExpansion (2 * ∏ i, k i) (Fintype.card ι - 1) (faceMono k e β b)
      (faceMonoCoeff k e β b) := by
  intro L hL
  obtain ⟨C, hC⟩ := faceMono_two_regime k e hk hβ hb hL
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have := hC t (by linarith)
  rw [powLog_eq_absSpectralSum, abs_of_nonneg (Real.log_nonneg ht), mul_assoc] at this
  exact this

/-- The normalised face monomial converges to its top coefficient when every coordinate resonates
exactly with `μ`. -/
theorem tendsto_normalised_faceMono (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β)
    (hb : 0 < b) {μ : ℝ} (hμ : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) :
    Tendsto (normalised μ (Fintype.card ι - 1) (faceMono k e β b)) atTop
      (𝓝 (faceMonoCoeff k e β b μ (Fintype.card ι - 1))) := by
  have hQ : 0 < 2 * ∏ i, k i := mul_pos two_pos (Finset.prod_pos fun i _ => hk i)
  refine tendsto_normalised_of_leading hQ
    (faceMono_cutoffExpansion k e hk hβ hb).hasSmoothCoordFreeExpansion ?_ ?_
  · intro ν q hne
    refine ⟨?_, ?_⟩
    · by_contra hlat
      exact hne (faceMonoCoeff_eq_zero_of_not_lattice k e hk hβ hb (fun m hm => hlat ⟨m, hm⟩) q)
    · by_contra hq
      exact hne (faceMonoCoeff_eq_zero_of_lt k e β b ν (not_le.1 hq))
  · intro ν p hp
    rcases hp with hν | ⟨rfl, hp⟩
    · refine faceMonoCoeff_eq_zero_of_exactCount_le k e hk hβ hb ?_
      unfold exactCount
      have hempty : (univ.filter fun i => 2 * (k i : ℝ) * ν = e i + 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _ hi
        have := hμ i
        have hk' : (0 : ℝ) < k i := Nat.cast_pos.2 (hk i)
        nlinarith
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · exact faceMonoCoeff_eq_zero_of_lt k e β b ν hp

/-- The face monomial is the cutoff monomial box integral of the analytic programme. -/
theorem faceMono_eq_cutoff (k e : ι → ℕ) (β b t : ℝ) :
    faceMono k e β b t = monomialBoxRealCutoff (Fintype.card ι - 1 + 1) (e ∘ (faceEquiv ι).symm)
      (k ∘ (faceEquiv ι).symm) b β t := by
  rw [faceMono_reindex (faceEquiv ι)]
  unfold faceMono monomialBoxRealCutoff
  have hset : box (Fin (Fintype.card ι - 1 + 1)) b = cutoffBox (Fintype.card ι - 1 + 1) b := rfl
  rw [hset]
  refine setIntegral_congr_fun (measurableSet_box b) fun u _ => ?_
  unfold mono
  congr 1
  congr 1
  ring

/-- ★★ **The top face-monomial coefficient**: `Γ(μ) β^{−μ} / ((|ι|−1)! ∏ 2k_i)`, independent of the
box side. -/
theorem faceMonoCoeff_top (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b)
    {μ : ℝ} (hμ : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) :
    faceMonoCoeff k e β b μ (Fintype.card ι - 1) =
      Real.Gamma μ * β ^ (-μ) / (((Fintype.card ι - 1).factorial : ℝ) * ∏ i, 2 * (k i : ℝ)) := by
  refine tendsto_nhds_unique (tendsto_normalised_faceMono k e hk hβ hb hμ) ?_
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hμpos : 0 < μ := by
    have := hμ i₀
    have hk' : (0 : ℝ) < k i₀ := Nat.cast_pos.2 (hk i₀)
    have : (0 : ℝ) ≤ e i₀ := Nat.cast_nonneg _
    nlinarith
  have hratio : ∀ i, ratioExp (e ∘ (faceEquiv ι).symm) (k ∘ (faceEquiv ι).symm) i = μ := by
    intro i
    unfold ratioExp
    have hk' : (2 * (k ((faceEquiv ι).symm i) : ℝ)) ≠ 0 := by
      have := Nat.cast_pos (α := ℝ) |>.2 (hk ((faceEquiv ι).symm i))
      positivity
    rw [Function.comp_apply, Function.comp_apply, div_eq_iff hk']
    have := hμ ((faceEquiv ι).symm i)
    linarith
  have hequiv := monomialBoxRealCutoff_equal_isEquivalent (Fintype.card ι - 1)
    (e ∘ (faceEquiv ι).symm) (k ∘ (faceEquiv ι).symm) (fun i => hk _) b μ β hb hμpos hβ hratio
  have hprod : ∏ i : Fin (Fintype.card ι - 1 + 1), 2 * ((k ∘ (faceEquiv ι).symm) i : ℝ) =
      ∏ i, 2 * (k i : ℝ) :=
    Fintype.prod_equiv (faceEquiv ι).symm _ _ fun _ => rfl
  rw [hprod] at hequiv
  set K := Real.Gamma μ * β ^ (-μ) / (((Fintype.card ι - 1).factorial : ℝ) * ∏ i, 2 * (k i : ℝ))
    with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < Real.Gamma μ := Real.Gamma_pos_of_pos hμpos
    have h2 : 0 < β ^ (-μ) := Real.rpow_pos_of_pos hβ _
    have h3 : (0 : ℝ) < ((Fintype.card ι - 1).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
    have h4 : (0 : ℝ) < ∏ i, 2 * (k i : ℝ) :=
      Finset.prod_pos fun i _ => by have := Nat.cast_pos (α := ℝ) |>.2 (hk i); positivity
    positivity
  have hv : ∀ᶠ N : ℝ in atTop, K * N ^ (-μ) * Real.log N ^ (Fintype.card ι - 1) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact (mul_pos (mul_pos hKpos (Real.rpow_pos_of_pos (by linarith) _))
      (pow_pos (Real.log_pos hN) _)).ne'
  have hlim := ((isEquivalent_iff_tendsto_one hv).1 hequiv).const_mul K
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN0 : 0 ≤ N := by linarith
  have hA : (N ^ μ : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log N ^ (Fintype.card ι - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
  have hK0 : K ≠ 0 := hKpos.ne'
  simp only [Pi.div_apply]
  unfold normalised
  rw [faceMono_eq_cutoff, Real.rpow_neg hN0]
  field_simp

/-- The top face-monomial coefficient is positive. -/
theorem faceMonoCoeff_top_pos (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β)
    (hb : 0 < b) {μ : ℝ} (hμ : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) :
    0 < faceMonoCoeff k e β b μ (Fintype.card ι - 1) := by
  rw [faceMonoCoeff_top k e hk hβ hb hμ]
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hμpos : 0 < μ := by
    have := hμ i₀
    have hk' : (0 : ℝ) < k i₀ := Nat.cast_pos.2 (hk i₀)
    have : (0 : ℝ) ≤ e i₀ := Nat.cast_nonneg _
    nlinarith
  have h1 : 0 < Real.Gamma μ := Real.Gamma_pos_of_pos hμpos
  have h2 : 0 < β ^ (-μ) := Real.rpow_pos_of_pos hβ _
  have h3 : (0 : ℝ) < ((Fintype.card ι - 1).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have h4 : (0 : ℝ) < ∏ i, 2 * (k i : ℝ) :=
    Finset.prod_pos fun i _ => by have := Nat.cast_pos (α := ℝ) |>.2 (hk i); positivity
  positivity

variable {d : ℕ}

/-- ★★ **The engine's top face coefficient of an exactly resonant face** `J`:
`Γ(μ) β^{−μ} / ((|J|−1)! ∏_{j∈J} 2k_j)`. -/
theorem faceCoef_top_eq (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b)
    (J : Finset (Fin d)) (hJ : J.Nonempty) (e : Fin d → ℕ) {μ : ℝ}
    (hres : ∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1) :
    faceCoef k β b J e μ (DJ J) =
      Real.Gamma μ * β ^ (-μ) /
        ((DJ J).factorial * ∏ i : {i // inJ J i}, 2 * (k i : ℝ)) := by
  unfold faceCoef
  rw [dif_pos hJ]
  have := nonempty_subtype_inJ hJ
  exact faceMonoCoeff_top (fun i : {i // inJ J i} => k i) (fun i => e i) (fun i => hk i.1) hβ hb
    fun i => hres i.1 (inJ_iff.1 i.2)

theorem faceCoef_top_pos (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b)
    (J : Finset (Fin d)) (hJ : J.Nonempty) (e : Fin d → ℕ) {μ : ℝ}
    (hres : ∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1) : 0 < faceCoef k β b J e μ (DJ J) := by
  unfold faceCoef
  rw [dif_pos hJ]
  have := nonempty_subtype_inJ hJ
  exact faceMonoCoeff_top_pos (fun i : {i // inJ J i} => k i) (fun i => e i) (fun i => hk i.1)
    hβ hb fun i => hres i.1 (inJ_iff.1 i.2)

end SmoothEngine

end Grammar
