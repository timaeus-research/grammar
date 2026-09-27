/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DlnFlatProductDensity
import Grammar.BoxPeel

/-!
# The flat prior on the symmetric box `[−1, 1]^L`: evenness

The flat-prior partition function of the depth-`L` deep linear network with zero target on the
symmetric box `[−1, 1]^L` is `2^L` times its restriction to the positive box `(0, 1]^L`, the
integrand `e^{−N(∏w)²/2}` being even in every coordinate (`integral_symmBox_eq`, by induction with
the Bochner peel `integral_pi_box_succ` and the reflection `integral_Icc_even`).  Together with
`depthInt_eq_unitBox` this is the box form of the general-depth expansion:

  `∫_{[−1,1]^{m+1}} e^{−N(∏w)²/2} dw = D_m(N)`  (★★★ `depthInt_eq_symmBox`),

so `depth_flat_allOrders` reads `Z_N = √2/(m!√N) P_m(log N − log 2) − R_m(N)` for the model of
examples_slop §2 (eq. dln_flat) at every depth.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- An even function integrates over `[−1, 1]` as twice its integral over `(0, 1]`. -/
theorem integral_Icc_even {f : ℝ → ℝ} (hf : ∀ a, f (-a) = f a)
    (hi : IntervalIntegrable f volume 0 1) :
    ∫ a in Icc (-1 : ℝ) 1, f a = 2 * ∫ a in Ioc (0 : ℝ) 1, f a := by
  have hneg : IntervalIntegrable f volume (-1) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (a := 0) (b := 1) (f := fun x => f (-x))).1
      (hi.congr fun x _ => (hf x).symm)
    simp only [neg_neg, neg_zero] at this
    exact this.symm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals hneg hi]
  have e : ∫ a in (-1 : ℝ)..0, f a = ∫ a in (0 : ℝ)..1, f a := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (f := f)
    simp only [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun x _ => hf x
  rw [e]
  ring

theorem integrableOn_exp_prod_piBox (m : ℕ) (N : ℝ) {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) :
    IntegrableOn (fun w : Fin m → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2)) (piBox m S) := by
  have hc : Continuous fun w : Fin m → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2) := by
    fun_prop
  refine (hc.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).mono_set ?_
  exact pi_mono fun _ _ => hS

theorem Ioc_subset_symm : Ioc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩

/-- ★★ **Evenness**: the symmetric box integral is `2^{m+1}` times the positive box integral. -/
theorem integral_symmBox_eq (m : ℕ) (N : ℝ) :
    ∫ w in piBox (m + 1) (Icc (-1 : ℝ) 1), Real.exp (-N * (∏ i, w i) ^ 2 / 2) =
      2 ^ (m + 1) * ∫ w in unitBox (m + 1), Real.exp (-N * (∏ i, w i) ^ 2 / 2) := by
  induction m generalizing N with
  | zero =>
    rw [integral_pi_box_succ 0 (Icc (-1 : ℝ) 1) _ (integrableOn_exp_prod_piBox 1 N subset_rfl),
      show unitBox 1 = piBox 1 (Ioc 0 1) from rfl,
      integral_pi_box_succ 0 (Ioc (0 : ℝ) 1) _ (integrableOn_exp_prod_piBox 1 N Ioc_subset_symm)]
    simp only [integral_piBox_zero, Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    have h0 : ∀ a : ℝ, Real.exp (-N * (-a) ^ 2 / 2) = Real.exp (-N * a ^ 2 / 2) :=
      fun a => by rw [neg_sq]
    rw [pow_one]
    exact integral_Icc_even h0 ((by fun_prop : Continuous fun a : ℝ =>
      Real.exp (-N * a ^ 2 / 2)).intervalIntegrable 0 1)
  | succ m ih =>
    rw [integral_pi_box_succ (m + 1) (Icc (-1 : ℝ) 1) _
        (integrableOn_exp_prod_piBox (m + 2) N subset_rfl),
      show unitBox (m + 2) = piBox (m + 2) (Ioc 0 1) from rfl,
      integral_pi_box_succ (m + 1) (Ioc (0 : ℝ) 1) _
        (integrableOn_exp_prod_piBox (m + 2) N Ioc_subset_symm)]
    have e : ∀ a : ℝ, ∀ b : Fin (m + 1) → ℝ,
        Real.exp (-N * (∏ i, (Fin.cons a b : Fin (m + 2) → ℝ) i) ^ 2 / 2) =
          Real.exp (-(N * a ^ 2) * (∏ i, b i) ^ 2 / 2) := by
      intro a b
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      congr 1
      ring
    simp_rw [e]
    have hcont : Continuous fun a : ℝ => ∫ b in piBox (m + 1) (Icc (-1 : ℝ) 1),
        Real.exp (-(N * a ^ 2) * (∏ i, b i) ^ 2 / 2) :=
      continuous_parametric_integral_of_continuous (by fun_prop)
        (isCompact_univ_pi fun _ => isCompact_Icc)
    have heven : ∀ a : ℝ, (∫ b in piBox (m + 1) (Icc (-1 : ℝ) 1),
        Real.exp (-(N * (-a) ^ 2) * (∏ i, b i) ^ 2 / 2)) = ∫ b in piBox (m + 1) (Icc (-1 : ℝ) 1),
        Real.exp (-(N * a ^ 2) * (∏ i, b i) ^ 2 / 2) := fun a => by rw [neg_sq]
    rw [integral_Icc_even heven (hcont.intervalIntegrable 0 1),
      show piBox (m + 1) (Ioc 0 1) = unitBox (m + 1) from rfl]
    have hinner : ∀ a : ℝ, ∫ b in piBox (m + 1) (Icc (-1 : ℝ) 1),
        Real.exp (-(N * a ^ 2) * (∏ i, b i) ^ 2 / 2) =
        2 ^ (m + 1) * ∫ b in unitBox (m + 1), Real.exp (-(N * a ^ 2) * (∏ i, b i) ^ 2 / 2) :=
      fun a => ih (N * a ^ 2)
    simp_rw [hinner]
    rw [integral_const_mul]
    ring

/-- ★★★ **The box form of the general-depth expansion**:
`∫_{[−1,1]^{m+1}} e^{−N(∏w)²/2} dw = D_m(N)`. -/
theorem depthInt_eq_symmBox (m : ℕ) (N : ℝ) :
    ∫ w in piBox (m + 1) (Icc (-1 : ℝ) 1), Real.exp (-N * (∏ i, w i) ^ 2 / 2) = depthInt m N := by
  rw [integral_symmBox_eq, depthInt_eq_unitBox]

end Grammar
