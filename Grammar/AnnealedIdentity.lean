/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The exact annealed identity

For an i.i.d. sample `X = (X_0, …, X_{n−1})` and the partition function of the log-likelihood
ratios `Z_n(β)(X) = ∫ ∏_i e^{−β f(X_i,u)} dπ(u)`, independence and Tonelli give, in the extended
nonnegative reals,

  `E₊ Z_n(β) = ∫ (E e^{−β f(X,u)})^n dπ(u)`  (`lintegral_annealedZ`),

and under the likelihood normalisation `E e^{−f(X,u)} = 1` (`f = log q − log p`, `∫ p = 1`)

  `E Z_n(1) = π(W)`  (`lintegral_annealedZ_one`).

So the typical `n^{−λ}(log n)^{m−1}` scale of `Z_n` does not describe the raw annealed evidence at
`β = 1`: the annealed/quenched distinction is an exact identity, not a cancellation of divergent
factors.  The product formula `∫⁻ ∏_i g_i(x_i) dμ^{⊗n} = ∏_i ∫⁻ g_i dμ_i` on a finite product
(`lintegral_fin_nat_prod_eq_prod`) is proved by induction, mirroring Mathlib's Bochner version.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Grammar

/-- **Product formula on a finite product of measures** (lower integral, non-dependent
coordinates). -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] {f : Fin n → E → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ : Fin n => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [MeasurePreserving.lintegral_map_equiv (fun x => ∏ i, f i (x i))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm hmp]
    have hsymm : ∀ a : E × (Fin n → E),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm a =
          Fin.cons a.1 a.2 := by
      intro a
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
        Fin.insertNth_zero, cast_eq]
    simp_rw [hsymm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hgm : Measurable fun y : Fin n → E => ∏ j, f j.succ (y j) :=
      Finset.measurable_prod _ fun (j : Fin n) _ => (hf j.succ).comp (measurable_pi_apply j)
    change ∫⁻ a : E × (Fin n → E), f 0 a.1 * (fun y : Fin n → E => ∏ j, f j.succ (y j)) a.2
      ∂μ.prod (Measure.pi fun _ : Fin n => μ) = _
    rw [lintegral_prod_mul (hf 0).aemeasurable hgm.aemeasurable]
    congr 1
    exact ih (f := fun i => f i.succ) fun i => hf i.succ

section Annealed

variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] (P : Measure Ω)
  [IsProbabilityMeasure P] (π : Measure U) [SFinite π]

/-- The annealed partition function of the sample `x`: `Z_n(β)(x) = ∫ ∏_i e^{−β f(x_i,u)} dπ(u)`,
in the extended nonnegative reals. -/
noncomputable def annealedZ (f : Ω → U → ℝ) (β : ℝ) (n : ℕ) (x : Fin n → Ω) : ℝ≥0∞ :=
  ∫⁻ u, ∏ i, ENNReal.ofReal (Real.exp (-β * f (x i) u)) ∂π

/-- **The exact annealed identity**: `E₊ Z_n(β) = ∫ (E e^{−β f(X,u)})^n dπ(u)`. -/
theorem lintegral_annealedZ {f : Ω → U → ℝ} (hf : Measurable (Function.uncurry f)) (β : ℝ)
    (n : ℕ) :
    ∫⁻ x, annealedZ π f β n x ∂Measure.pi (fun _ : Fin n => P) =
      ∫⁻ u, (∫⁻ ω, ENNReal.ofReal (Real.exp (-β * f ω u)) ∂P) ^ n ∂π := by
  unfold annealedZ
  have hm : ∀ i : Fin n, Measurable fun p : (Fin n → Ω) × U =>
      ENNReal.ofReal (Real.exp (-β * f (p.1 i) p.2)) := by
    intro i
    have hg : Measurable fun p : (Fin n → Ω) × U => (p.1 i, p.2) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact ENNReal.measurable_ofReal.comp (Measurable.exp (measurable_const.mul (hf.comp hg)))
  rw [lintegral_lintegral_swap (Finset.measurable_prod _ fun i _ => hm i).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hg : Measurable fun ω : Ω => (ω, u) := measurable_id.prodMk measurable_const
  rw [lintegral_fin_nat_prod_eq_prod P (f := fun _ ω => ENNReal.ofReal (Real.exp (-β * f ω u)))
    fun _ => ENNReal.measurable_ofReal.comp (Measurable.exp (measurable_const.mul (hf.comp hg)))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`E Z_n(1) = π(W)`** under the likelihood normalisation `E e^{−f(X,u)} = 1`. -/
theorem lintegral_annealedZ_one {f : Ω → U → ℝ} (hf : Measurable (Function.uncurry f))
    (hnorm : ∀ u, ∫⁻ ω, ENNReal.ofReal (Real.exp (-f ω u)) ∂P = 1) (n : ℕ) :
    ∫⁻ x, annealedZ π f 1 n x ∂Measure.pi (fun _ : Fin n => P) = π univ := by
  rw [lintegral_annealedZ P π hf 1 n]
  simp only [neg_mul, one_mul, hnorm, one_pow, lintegral_one]

end Annealed

end Grammar
