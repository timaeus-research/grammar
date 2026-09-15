/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneral
import Grammar.SmoothTimeRescale
import Grammar.SmoothCoefficientLinearity
import Grammar.DiagonalBoxTransport

/-!
# The empirical expansion on a general rectangle: the exact scaling adapter
(§20 unit 5 of consult #142)

The empirical integral on a rectangle `∏ᵢ (0, bᵢ]` reduces EXACTLY to the unit box by the diagonal
scaling `v = (bᵢ uᵢ)`: with `A_b = ∏ bᵢ^{hᵢ+1}` and `B_b = ∏ bᵢ^{2kᵢ}`,
`Z_b(N; η, ζ) = A_b · Z_1(B_b N; η∘b, ζ∘b)` (★ `empIntegralRect_eq`) — the coupling transforms
correctly because `√N v^k = √(B_b N) u^k`, so NO rescaling of the field is needed. Consequently the
rectangle integral is a `CutoffExpansion` on the same lattice `(2∏kᵢ)⁻¹ℕ` with the same logarithmic
degree `d − 1` (★★ `empRect_cutoffExpansion`), with the explicit coefficients
`empCoeffRect = A_b · scaleCoeff (d−1) B_b (empCoeff (η∘b) (ζ∘b))`, i.e.
`c^b_{μq} = A_b B_b^{−μ} ∑_{j≥q} C(j,q) (log B_b)^{j−q} c^1_{μj}(η∘b, ζ∘b)` (the coefficient law of
consult #142), and they are canonical (`empCoeffRect_unique`). The cube `(0,b]^d` is the case
`bᵢ = b`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The rectangle and the diagonal scaling -/

/-- The rectangle `∏ᵢ (0, bᵢ]`. -/
def rect (b : Fin d → ℝ) : Set (Fin d → ℝ) := {z | ∀ i, 0 < z i ∧ z i ≤ b i}

theorem rect_const (b : ℝ) : rect (fun _ : Fin d => b) = box (Fin d) b := by
  ext z
  simp [rect, box, Set.mem_pi]

/-- The diagonal scaling `u ↦ (bᵢ uᵢ)` as a plain function. -/
def diag (b : Fin d → ℝ) (u : Fin d → ℝ) : Fin d → ℝ := fun i => b i * u i

theorem contDiff_diag (b : Fin d → ℝ) : ContDiff ℝ ∞ (diag b) :=
  contDiff_pi.2 fun i => contDiff_const.mul (contDiff_apply ℝ ℝ i)

theorem mono_diag (e : Fin d → ℕ) (b u : Fin d → ℝ) : mono e (diag b u) = mono e b * mono e u := by
  unfold mono diag
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _

theorem rect_eq_image (b : Fin d → ℝ) (hb : ∀ i, 0 < b i) :
    rect b = diagEquiv b (fun i => (hb i).ne') '' box (Fin d) 1 := by
  rw [box, diagEquiv_image_pi_Ioc b hb 1]
  ext z
  simp [rect]

/-- Change of variables along the diagonal scaling:
`∫_{rect b} f = (∏ bᵢ) ∫_{(0,1]^d} f ∘ diag b`. -/
theorem integral_rect_eq (b : Fin d → ℝ) (hb : ∀ i, 0 < b i) (f : (Fin d → ℝ) → ℝ) :
    ∫ z in rect b, f z = (∏ i, b i) * ∫ u in box (Fin d) 1, f (diag b u) := by
  have hp : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hb i
  rw [rect_eq_image b hb, ← map_diagEquiv_restrict_withDensity b hb,
    (diagEquiv b fun i => (hb i).ne').measurableEmbedding.integral_map, withDensity_const,
    integral_smul_measure, ENNReal.toReal_ofReal hp.le, smul_eq_mul]
  rfl

/-! ### The rectangle empirical integral -/

/-- The empirical integral on the rectangle `∏ᵢ (0, bᵢ]`. -/
noncomputable def empIntegralRect (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (b : Fin d → ℝ)
    (N : ℝ) : ℝ :=
  ∫ v in rect b, η v * mono h v *
    exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v)

theorem sqrt_mono_two_mul (k : Fin d → ℕ) {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) (N : ℝ) :
    Real.sqrt (mono (fun i => 2 * k i) b * N) = mono k b * Real.sqrt N := by
  have h2 : mono (fun i => 2 * k i) b = mono k b * mono k b := by
    rw [mono_mul_mono]
    congr 1
    funext i
    ring
  rw [h2, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (mono_pos k hb).le]

/-- ★ **The exact scaling identity**:
`Z_b(N; η, ζ) = (∏ bᵢ^{hᵢ+1}) · Z_1(B_b N; η ∘ diag b, ζ ∘ diag b)`, `B_b = ∏ bᵢ^{2kᵢ}`. -/
theorem empIntegralRect_eq (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) {b : Fin d → ℝ}
    (hb : ∀ i, 0 < b i) (N : ℝ) :
    empIntegralRect η ζ h k b N =
      ((∏ i, b i) * mono h b) *
        empIntegral (η ∘ diag b) (ζ ∘ diag b) h k (mono (fun i => 2 * k i) b * N) := by
  unfold empIntegralRect
  rw [integral_rect_eq b hb, empIntegral_eq, mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) 1) fun u _ => ?_
  rw [sqrt_mono_two_mul k hb N, mono_diag, mono_diag, mono_diag]
  simp only [Function.comp_apply]
  ring_nf

/-! ### The cutoff expansion on the rectangle -/

/-- The rectangle coefficients: `A_b · scaleCoeff (d−1) B_b (empCoeff (η∘b) (ζ∘b))`. -/
noncomputable def empCoeffRect (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (b : Fin d → ℝ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  ((∏ i, b i) * mono h b) *
    scaleCoeff (d - 1) (mono (fun i => 2 * k i) b) (empCoeff (η ∘ diag b) (ζ ∘ diag b) h k) μ q

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★★ **The empirical integral on a rectangle is a cutoff expansion** on the lattice `Q⁻¹ℕ`,
`Q = 2∏kᵢ`, of logarithmic degree `≤ d − 1`, with coefficients `empCoeffRect`. -/
theorem empRect_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegralRect η ζ h k b) (empCoeffRect η ζ h k b) := by
  have hB : 0 < mono (fun i => 2 * k i) b := mono_pos _ hb
  have hbase := emp_cutoffExpansion (h := h) (hη.comp (contDiff_diag b))
    (hζ.comp (contDiff_diag b)) hk
  have hscaled := CutoffExpansion.const_mul ((∏ i, b i) * mono h b)
    (CutoffExpansion.comp_mul_pos hbase hB)
  intro L hL
  obtain ⟨K, hK⟩ := hscaled L hL
  refine ⟨K, ?_⟩
  filter_upwards [hK] with N hN
  unfold empCoeffRect
  rw [empIntegralRect_eq η ζ h k hb N]
  exact hN

/-- ★★ **Canonicity on the rectangle.** -/
theorem empCoeffRect_unique (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {b : Fin d → ℝ} (hb : ∀ i, 0 < b i) {c : ℝ → ℕ → ℝ}
    (hc : CutoffExpansion (Qamb k) (d - 1) (empIntegralRect η ζ h k b) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = empCoeffRect η ζ h k b μ j :=
  CutoffExpansion.coeff_unique (Qamb_pos k hk) hc (empRect_cutoffExpansion hη hζ hk hb) hμ hj

/-- The unit box is the case `bᵢ = 1`: the rectangle integral is the unit-box integral. -/
theorem empIntegralRect_one (N : ℝ) :
    empIntegralRect η ζ h k (fun _ => 1) N = empIntegral η ζ h k N := by
  rw [empIntegralRect, rect_const, empIntegral_eq]

end SmoothEngine

end Grammar
