/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral
import Grammar.SmoothFamilyIntegral
import Grammar.SmoothCoreDecomposition
import Grammar.SmoothBridgeConsumer

/-!
# The renormalised chart-strata formula (consult #122, Theorem B)

The canonical coefficients of a PRODUCT amplitude `D · f` (transport density × observable) are a
finite sum over the faces `J` (chart-local strata) and multi-indices `a` of DENSITY-ONLY linear
functionals applied to the observable's normal jets `∂^a_J f` on the face:
★★★ `smoothCoeffAtDepth_mul_eq`
`  C_{μ,q}(D·f) = ∑_J ∑_{a ∈ idxL J} (∏_{i∈J} 1/a_i!) · 𝓑_{J,a,μ,q}(D)[∂^a_J f]`,
with `𝓑_{J,a,μ,q}(D)[U] = ∑_{m ≥ a} (∏_{i∈J} 1/(m−a)_i!) ∑_j c^J_{m+h,μ,j} C(j,q)`
`  · ∫_{(0,b]^K} (R_K^p (∂^{m−a}_J D · U))(0_J, w) w^{h_K} (w^{2k_K})^{−μ} S(w)^{j−q} dw`
(`renormFunctional`). The functionals are FINITE-PART: the coordinate Taylor remainders `R_K^p` in
the complementary directions are kept INSIDE the functional — they are the renormalisation that
makes the face integrals converge, and the ordinary "integrable-kernel" form
`∫ 𝓚_{J,a}(w) ∂^a f(0_J, w) dw` with a kernel independent of `f` is FALSE at crossings (consult
#122): the remainder subtracts the `K`-jets of the whole product `∂^{m−a}_J D · U`, not of `D`
alone. The proof is the multi-index Leibniz rule for the iterated coordinate derivatives
(★ `pdMulti_mul`, from `pd_mul` and Pascal's rule via `Finset.sum_choose_succ_mul`), the
linearity of the iterated remainders and of the face coefficient integrals (with the engine's
integrability route through `faceAmp_bound`), the factorial identity
`1/m! · C(m,a) = 1/a! · 1/(m−a)!` and the reindexing `∑_m ∑_{a≤m} = ∑_a ∑_{m≥a}`. The
functionals are linear in `U` (`renormFunctional_add_smul`) and read only the complementary jets
`∂^α_K U`, `α ≤ p`, of the field along the face (★★ `renormFunctional_congr`, finite-jet
dependence, via `remList_congr_of_jets`); on the deepest stratum `J = univ` (all of `d = 1`) they
reduce to the classical bilinear pairing of the jets of `D` and `U` at the origin
(`renormFunctional_univ`). The canonical-depth corollary is ★★ `smoothCoeff_mul_eq`; integrated
over a compact base with a constant phase unit (`SmoothAmplitudeFamily.mul`, whose joint
continuity is again the Leibniz rule), ★★ `familyCoeff_mul_eq`; and for the resolution-bridge
producer, whose piece amplitudes are `ρ · obs∘ψ` on the box, ★★★ `BridgeInputs.coeff_eq_renormSum`
(the box congruence of the canonical coefficients is `smoothCoeff_congr_box`, from canonicity).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Linearity of the coordinate derivatives -/

theorem line_finset_sum {κ : Type*} (s : Finset κ) (c : κ → ℝ) (G : κ → (Fin d → ℝ) → ℝ)
    (i : Fin d) (v : Fin d → ℝ) :
    line (fun v => ∑ a ∈ s, c a * G a v) i v = ∑ a ∈ s, fun t => c a * line (G a) i v t := by
  funext t
  simp only [line, Finset.sum_apply]

theorem pd_finset_sum {κ : Type*} {s : Finset κ} (c : κ → ℝ) {G : κ → (Fin d → ℝ) → ℝ}
    (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (i : Fin d) :
    pd i (fun v => ∑ a ∈ s, c a * G a v) = fun v => ∑ a ∈ s, c a * pd i (G a) v := by
  funext v
  have hdiff : ∀ a ∈ s, DifferentiableAt ℝ (line (G a) i v) (v i) := fun a ha =>
    ((contDiff_line (hG a ha) i v).differentiable (by simp)).differentiableAt
  change deriv (line (fun v => ∑ a ∈ s, c a * G a v) i v) (v i) = _
  rw [line_finset_sum, deriv_sum fun a ha => (hdiff a ha).const_mul _]
  exact Finset.sum_congr rfl fun a ha => deriv_const_mul _ (hdiff a ha)

theorem pdPow_finset_sum {κ : Type*} {s : Finset κ} (c : κ → ℝ) {G : κ → (Fin d → ℝ) → ℝ}
    (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (i : Fin d) (n : ℕ) :
    pdPow i n (fun v => ∑ a ∈ s, c a * G a v) = fun v => ∑ a ∈ s, c a * pdPow i n (G a) v := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rw [pdPow_succ, pd_finset_sum c hG i, ih fun a ha => contDiff_pd (hG a ha) i]
    simp only [pdPow_succ]

theorem pdMulti_finset_sum {κ : Type*} {s : Finset κ} (c : κ → ℝ) {G : κ → (Fin d → ℝ) → ℝ}
    (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => ∑ a ∈ s, c a * G a v) =
      fun v => ∑ a ∈ s, c a * pdMulti m l (G a) v := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, ih hG, pdPow_finset_sum c (fun a ha => contDiff_pdMulti (hG a ha) m l) i]
    simp only [pdMulti_cons]

/-! ### The Leibniz rule for the coordinate derivatives -/

theorem pd_mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    pd i (fun v => D v * f v) = fun v => pd i D v * f v + D v * pd i f v := by
  funext v
  have hD' : DifferentiableAt ℝ (line D i v) (v i) :=
    ((contDiff_line hD i v).differentiable (by simp)).differentiableAt
  have hf' : DifferentiableAt ℝ (line f i v) (v i) :=
    ((contDiff_line hf i v).differentiable (by simp)).differentiableAt
  change deriv (line (fun v => D v * f v) i v) (v i) = _
  rw [show line (fun v => D v * f v) i v = line D i v * line f i v from rfl,
    deriv_mul hD' hf', line_apply_self, line_apply_self]
  rfl

/-- ★ **The one-coordinate Leibniz rule**:
`∂_i^n (D f) = ∑_{a ≤ n} C(n,a) ∂_i^{n−a} D · ∂_i^a f`. -/
theorem pdPow_mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (n : ℕ) :
    pdPow i n (fun v => D v * f v) = fun v => ∑ a ∈ range (n + 1),
      ((n.choose a : ℕ) : ℝ) * (pdPow i (n - a) D v * pdPow i a f v) := by
  induction n with
  | zero => funext v; simp [pdPow_zero]
  | succ n ih =>
    rw [pdPow_succ', ih, pd_finset_sum (fun a => ((n.choose a : ℕ) : ℝ))
      (fun a _ => (contDiff_pdPow hD i _).mul (contDiff_pdPow hf i _)) i]
    funext v
    have hpd : ∀ a : ℕ, pd i (fun v => pdPow i (n - a) D v * pdPow i a f v) =
        fun v => pdPow i (n - a + 1) D v * pdPow i a f v +
          pdPow i (n - a) D v * pdPow i (a + 1) f v := fun a => by
      rw [pd_mul (contDiff_pdPow hD i _) (contDiff_pdPow hf i _), pdPow_succ', pdPow_succ']
    simp only [hpd]
    rw [Finset.sum_choose_succ_mul (fun a c => pdPow i c D v * pdPow i a f v) n,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Nat.sub_add_comm (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha))]
    ring

theorem prod_toFinset_cons_of_not_mem {i : Fin d} {l : List (Fin d)} (hi : i ∉ l)
    (g : Fin d → ℝ) : ∏ j ∈ (i :: l).toFinset, g j = g i * ∏ j ∈ l.toFinset, g j := by
  rw [List.toFinset_cons, Finset.prod_insert (fun h => hi (List.mem_toFinset.1 h))]

/-- ★ **The multi-index Leibniz rule** over a list `l` of distinct coordinates: the Leibniz
multi-indices are `a ≤ m` on `l` and `a = 0` off `l`, i.e. `a ∈ idxL (m + 1) l`, and
`∂^m_l (D f) = ∑_a (∏_{i∈l} C(m_i,a_i)) ∂^{m−a}_l D · ∂^a_l f`. -/
theorem pdMulti_mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f)
    (m : Fin d → ℕ) {l : List (Fin d)} (hl : l.Nodup) :
    pdMulti m l (fun v => D v * f v) = fun v => ∑ a ∈ idxL (fun j => m j + 1) l,
      (∏ i ∈ l.toFinset, ((m i).choose (a i) : ℝ)) *
        (pdMulti (m - a) l D v * pdMulti a l f v) := by
  induction l with
  | nil =>
    funext v
    simp [pdMulti_nil, idxL_nil]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    rw [pdMulti_cons, ih hl', pdPow_finset_sum _
      (fun a _ => (contDiff_pdMulti hD _ l).mul (contDiff_pdMulti hf _ l)) i (m i)]
    funext v
    have hpow : ∀ a : Fin d → ℕ,
        pdPow i (m i) (fun v => pdMulti (m - a) l D v * pdMulti a l f v) =
        fun v => ∑ n ∈ range (m i + 1), (((m i).choose n : ℕ) : ℝ) *
          (pdPow i (m i - n) (pdMulti (m - a) l D) v * pdPow i n (pdMulti a l f) v) := fun a =>
      pdPow_mul (contDiff_pdMulti hD _ l) (contDiff_pdMulti hf _ l) i (m i)
    simp only [hpow]
    rw [sum_idxL_cons (fun j => m j + 1) hi, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hcongr : ∀ j ∈ l, (m - Function.update a i n) j = (m - a) j := fun j hj => by
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp only [Pi.sub_apply, Function.update_of_ne hji]
    have hprod : ∏ j ∈ l.toFinset, ((m j).choose (Function.update a i n j) : ℝ) =
        ∏ j ∈ l.toFinset, ((m j).choose (a j) : ℝ) :=
      Finset.prod_congr rfl fun j hj => by
        have hjl : j ∈ l := List.mem_toFinset.1 hj
        have hji : j ≠ i := fun h => hi (h ▸ hjl)
        rw [Function.update_of_ne hji]
    rw [prod_toFinset_cons_of_not_mem hi, Function.update_self, pdMulti_cons, pdMulti_cons,
      Pi.sub_apply, Function.update_self, pdMulti_congr hcongr, pdMulti_update_of_not_mem hi,
      hprod]
    ring

/-! ### Linearity of the coordinate remainders -/

theorem coordTaylor_finset_sum {κ : Type*} {s : Finset κ} (c : κ → ℝ)
    {G : κ → (Fin d → ℝ) → ℝ} (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (i : Fin d) (p : ℕ) :
    coordTaylor i p (fun v => ∑ a ∈ s, c a * G a v) =
      fun v => ∑ a ∈ s, c a * coordTaylor i p (G a) v := by
  funext v
  simp only [coordTaylor_apply, pdPow_finset_sum c hG i, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring

theorem coordRem_finset_sum {κ : Type*} {s : Finset κ} (c : κ → ℝ)
    {G : κ → (Fin d → ℝ) → ℝ} (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (i : Fin d) (p : ℕ) :
    coordRem i p (fun v => ∑ a ∈ s, c a * G a v) =
      fun v => ∑ a ∈ s, c a * coordRem i p (G a) v := by
  funext v
  simp only [coordRem, coordTaylor_finset_sum c hG i p, mul_sub, Finset.sum_sub_distrib]

theorem remList_finset_sum (p : Fin d → ℕ) {κ : Type*} {s : Finset κ} (c : κ → ℝ)
    {G : κ → (Fin d → ℝ) → ℝ} (hG : ∀ a ∈ s, ContDiff ℝ ∞ (G a)) (l : List (Fin d)) :
    remList p l (fun v => ∑ a ∈ s, c a * G a v) =
      fun v => ∑ a ∈ s, c a * remList p l (G a) v := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [remList_cons, ih hG, coordRem_finset_sum c (fun a ha => contDiff_remList p (hG a ha) l)]
    simp only [remList_cons]

/-! ### Linearity of the face coefficient integrals -/

theorem faceCoeffInt_finset_sum {ι : Type*} [Fintype ι] {κ : Type*} {s : Finset κ} (c : κ → ℝ)
    (G : κ → (ι → ℝ) → ℝ) (h a : ι → ℕ) (b μ : ℝ) (e : ℕ)
    (hint : ∀ x ∈ s, IntegrableOn
      (fun w => G x w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b)) :
    faceCoeffInt (fun w => ∑ x ∈ s, c x * G x w) h a b μ e =
      ∑ x ∈ s, c x * faceCoeffInt (G x) h a b μ e := by
  unfold faceCoeffInt
  have hpt : ∀ w : ι → ℝ, (∑ x ∈ s, c x * G x w) * mono h w * mono a w ^ (-μ) * logSum a w ^ e =
      ∑ x ∈ s, c x * (G x w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) := fun w => by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ fun x hx => (hint x hx).const_mul _]
  exact Finset.sum_congr rfl fun x _ => MeasureTheory.integral_const_mul _ _

variable {h k p : Fin d → ℕ} {β b μ : ℝ}

theorem zero_mem_idxL (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (l : List (Fin d)) :
    (0 : Fin d → ℕ) ∈ idxL p l := by
  rw [idxL, Fintype.mem_piFinset]
  intro i
  split_ifs
  · exact Finset.mem_range.2 (hp0 i)
  · exact Finset.mem_singleton_self _

theorem two_k_mul_lt_of_le {L : ℕ} (hp : ∀ i, p i + h i = 2 * k i * L) (hμ : μ ≤ L) (i : Fin d) :
    ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1 := by
  have h1 : ((2 * k i : ℕ) : ℝ) * L = (p i : ℝ) + h i := by exact_mod_cast (hp i).symm
  have h2 : ((2 * k i : ℕ) : ℝ) * μ ≤ ((2 * k i : ℕ) : ℝ) * L :=
    mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg _)
  linarith

/-- The engine's integrability route for the face coefficient integrand of a flat face amplitude
with no face derivative. -/
theorem integrableOn_faceCoeff_faceAmp_zero {H : (Fin d → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (hb : 0 < b) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d))
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (e : ℕ) :
    IntegrableOn (fun w : {i // ¬ inJ J i} → ℝ =>
      faceAmp p J H 0 w * mono (fun i : {i // ¬ inJ J i} => h i) w *
        mono (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (-μ) *
        logSum (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ e) (box {i // ¬ inJ J i} b) := by
  obtain ⟨M, hM⟩ := exists_rect_bound hH p b
  exact integrable_faceCoeff hb (continuous_faceAmp p J hH 0).aestronglyMeasurable
    (fun w hw => faceAmp_bound p J hH hb hp0 hM (zero_mem_idxL p hp0 (lJ J)) hw)
    (fun i => by have := hμ i; linarith) le_rfl

/-! ### The face amplitude and face coefficient integrals of a product -/

theorem prod_lJ_toFinset (J : Finset (Fin d)) (g : Fin d → ℝ) :
    ∏ i ∈ (lJ J).toFinset, g i = ∏ i : {i // inJ J i}, g i :=
  Finset.prod_subtype (lJ J).toFinset (fun i => by rw [List.mem_toFinset, mem_lJ]; rfl) g

variable {D f : (Fin d → ℝ) → ℝ}

/-- ★ **The face amplitude of a product** is the Leibniz sum of the density-only face amplitudes
of `∂^{m−a}_J D · ∂^a_J f` (no further face derivative, the `K`-remainder applied to the whole
product). -/
theorem faceAmp_mul (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (J : Finset (Fin d))
    (m : Fin d → ℕ) (w : {i // ¬ inJ J i} → ℝ) :
    faceAmp p J (fun v => D v * f v) m w = ∑ a ∈ idxL (fun j => m j + 1) (lJ J),
      (∏ i : {i // inJ J i}, ((m i).choose (a i) : ℝ)) *
        faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * pdMulti a (lJ J) f v) 0 w := by
  unfold faceAmp
  rw [pdMulti_mul hD hf m (nodup_lJ J), remList_finset_sum p _
    (fun a _ => (contDiff_pdMulti hD _ _).mul (contDiff_pdMulti hf _ _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pdMulti_zero, prod_lJ_toFinset]

theorem faceCoeffInt_faceAmp_mul (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (hb : 0 < b)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d))
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (m : Fin d → ℕ) (e : ℕ) :
    faceCoeffInt (faceAmp p J (fun v => D v * f v) m) (fun i : {i // ¬ inJ J i} => h i)
        (fun i : {i // ¬ inJ J i} => 2 * k i) b μ e =
      ∑ a ∈ idxL (fun j => m j + 1) (lJ J), (∏ i : {i // inJ J i}, ((m i).choose (a i) : ℝ)) *
        faceCoeffInt (faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * pdMulti a (lJ J) f v) 0)
          (fun i : {i // ¬ inJ J i} => h i) (fun i : {i // ¬ inJ J i} => 2 * k i) b μ e := by
  have hfun : faceAmp p J (fun v => D v * f v) m = fun w => ∑ a ∈ idxL (fun j => m j + 1) (lJ J),
      (∏ i : {i // inJ J i}, ((m i).choose (a i) : ℝ)) *
        faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * pdMulti a (lJ J) f v) 0 w :=
    funext (faceAmp_mul hD hf J m)
  rw [hfun]
  exact faceCoeffInt_finset_sum _ _ _ _ _ _ _ fun a _ => integrableOn_faceCoeff_faceAmp_zero
    ((contDiff_pdMulti hD _ _).mul (contDiff_pdMulti hf _ _)) hb hp0 J hμ e

/-! ### The renormalised face functionals -/

/-- ★★ **The density-only renormalised face functional** of index `(J, a)` at `(μ, q)`, applied to a
face field `U`: `∑_{m ≥ a} (∏_{i∈J} 1/(m−a)_i!) ∑_j c^J_{m+h,μ,j} C(j,q)`
`  · ∫_{(0,b]^K} (R_K^p (∂^{m−a}_J D · U))(0_J, w) w^{h_K} (w^{2k_K})^{−μ} S(w)^{j−q} dw`.
FINITE-PART: the complementary remainder `R_K^p` is applied to the whole product and kept inside
the integral (consult #122). -/
noncomputable def renormFunctional (D : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ)
    (J : Finset (Fin d)) (a : Fin d → ℕ) (μ : ℝ) (q : ℕ) (U : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ m ∈ (idxL p (lJ J)).filter (fun m => ∀ i, a i ≤ m i), faceW J (m - a) *
    ∑ j ∈ Finset.Ico q (DJ J + 1), faceCoef k β b J (fun i => m i + h i) μ j * (j.choose q) *
      faceCoeffInt (faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * U v) 0)
        (fun i : {i // ¬ inJ J i} => h i) (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)

/-- The reindexing `∑_{m ∈ idxL} ∑_{a ≤ m} = ∑_{a ∈ idxL} ∑_{m ∈ idxL, m ≥ a}`. -/
theorem sum_idxL_leibniz_comm (p : Fin d → ℕ) (l : List (Fin d))
    (T : (Fin d → ℕ) → (Fin d → ℕ) → ℝ) :
    ∑ m ∈ idxL p l, ∑ a ∈ idxL (fun j => m j + 1) l, T m a =
      ∑ a ∈ idxL p l, ∑ m ∈ (idxL p l).filter (fun m => ∀ i, a i ≤ m i), T m a := by
  refine Finset.sum_comm' fun m a => ?_
  simp only [idxL, Fintype.mem_piFinset, Finset.mem_filter]
  have key : ∀ i, ((m i ∈ if i ∈ l then range (p i) else {0}) ∧
      (a i ∈ if i ∈ l then range (m i + 1) else {0})) ↔
      ((a i ∈ if i ∈ l then range (p i) else {0}) ∧
        (m i ∈ if i ∈ l then range (p i) else {0}) ∧ a i ≤ m i) := fun i => by
    by_cases hi : i ∈ l <;> simp only [hi, if_true, if_false, Finset.mem_range,
      Finset.mem_singleton] <;> omega
  constructor
  · rintro ⟨hm, ha⟩
    exact ⟨⟨hm, fun i => ((key i).1 ⟨hm i, ha i⟩).2.2⟩, fun i => ((key i).1 ⟨hm i, ha i⟩).1⟩
  · rintro ⟨⟨hm, hle⟩, ha⟩
    exact ⟨hm, fun i => ((key i).2 ⟨ha i, hm i, hle i⟩).2⟩

theorem le_of_mem_idxL_succ {m a : Fin d → ℕ} {l : List (Fin d)}
    (ha : a ∈ idxL (fun j => m j + 1) l) (hm : m ∈ idxL p l) (i : Fin d) : a i ≤ m i := by
  have h1 := (Fintype.mem_piFinset.1 ha) i
  have h2 := (Fintype.mem_piFinset.1 hm) i
  by_cases hi : i ∈ l
  · simp only [hi, if_true, Finset.mem_range] at h1
    omega
  · simp only [hi, if_false, Finset.mem_singleton] at h1 h2
    omega

/-- The factorial identity `1/m! · ∏ C(mᵢ,aᵢ) = 1/a! · 1/(m−a)!` on the face. -/
theorem faceW_mul_choose (J : Finset (Fin d)) {m a : Fin d → ℕ} (hle : ∀ i, a i ≤ m i) :
    faceW J m * ∏ i : {i // inJ J i}, ((m i).choose (a i) : ℝ) = faceW J a * faceW J (m - a) := by
  unfold faceW
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := Nat.choose_mul_factorial_mul_factorial (hle i)
  have h' : ((m i).choose (a i) : ℝ) * (a i).factorial * (m i - a i).factorial =
      (m i).factorial := by exact_mod_cast h
  have ha0 : ((a i).factorial : ℝ) ≠ 0 := by positivity
  have hma0 : ((m i - a i).factorial : ℝ) ≠ 0 := by positivity
  have hm0 : ((m i).factorial : ℝ) ≠ 0 := by positivity
  have hc0 : ((m i).choose (a i) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hle i)).ne'
  rw [Pi.sub_apply, ← h']
  field_simp

/-- ★★★ **The renormalised chart-strata formula at depth `p`**: the depth-`p` coefficients of the
product amplitude `D · f` are the face sums of the density-only renormalised functionals applied
to the observable's face jets `∂^a_J f`, weighted by `∏_{i∈J} 1/aᵢ!`. -/
theorem smoothCoeffAtDepth_mul_eq (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (hb : 0 < b)
    (hp0 : ∀ i, 0 < p i) (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (q : ℕ) :
    smoothCoeffAtDepth (fun v => D v * f v) h k p β b μ q =
      ∑ J : Finset (Fin d), ∑ a ∈ idxL p (lJ J),
        faceW J a * renormFunctional D h k p β b J a μ q (pdMulti a (lJ J) f) := by
  unfold smoothCoeffAtDepth faceIndex renormFunctional
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  dsimp only
  simp only [Finset.mul_sum]
  rw [← sum_idxL_leibniz_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [faceCoeffInt_faceAmp_mul hD hf hb hp0 J hμ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun j _ => ?_
  have hW := faceW_mul_choose J (le_of_mem_idxL_succ ha hm)
  conv_rhs => rw [← mul_assoc]
  rw [← hW]
  ring

/-- ★★ **The renormalised chart-strata formula for the canonical coefficients** (depth
`2kL − h` at the deterministic cutoff `L = max(⌊μ⌋₊ + 1, L₀)`). -/
theorem smoothCoeff_mul_eq (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (hk : ∀ i, 0 < k i)
    (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff (fun v => D v * f v) h k β b μ q =
      ∑ J : Finset (Fin d), ∑ a ∈ idxL (depthOf h k (cutoffOf h μ)) (lJ J),
        faceW J a * renormFunctional D h k (depthOf h k (cutoffOf h μ)) β b J a μ q
          (pdMulti a (lJ J) f) :=
  smoothCoeffAtDepth_mul_eq hD hf hb (depthOf_pos hk (L₀_le_cutoffOf h μ))
    (two_k_mul_lt_of_le (depthOf_add hk (L₀_le_cutoffOf h μ)) (lt_cutoffOf h μ).le) q

/-! ### Linearity of the renormalised functionals in the face field -/

theorem remList_add_smul (p : Fin d → ℕ) {G₁ G₂ : (Fin d → ℝ) → ℝ} (hG₁ : ContDiff ℝ ∞ G₁)
    (hG₂ : ContDiff ℝ ∞ G₂) (c₁ c₂ : ℝ) (l : List (Fin d)) :
    remList p l (fun v => c₁ * G₁ v + c₂ * G₂ v) =
      fun v => c₁ * remList p l G₁ v + c₂ * remList p l G₂ v := by
  have h := remList_finset_sum p (s := Finset.univ) ![c₁, c₂] (G := ![G₁, G₂])
    (fun x _ => by fin_cases x <;> simp [hG₁, hG₂]) l
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem faceAmp_zero_add_smul {H₁ H₂ : (Fin d → ℝ) → ℝ} (hH₁ : ContDiff ℝ ∞ H₁)
    (hH₂ : ContDiff ℝ ∞ H₂) (c₁ c₂ : ℝ) (J : Finset (Fin d)) (w : {i // ¬ inJ J i} → ℝ) :
    faceAmp p J (fun v => c₁ * H₁ v + c₂ * H₂ v) 0 w =
      c₁ * faceAmp p J H₁ 0 w + c₂ * faceAmp p J H₂ 0 w := by
  unfold faceAmp
  rw [pdMulti_zero, pdMulti_zero, pdMulti_zero, remList_add_smul p hH₁ hH₂]

theorem faceCoeffInt_add_smul {ι : Type*} [Fintype ι] {G₁ G₂ : (ι → ℝ) → ℝ} (c₁ c₂ : ℝ)
    (h a : ι → ℕ) (b μ : ℝ) (e : ℕ)
    (h₁ : IntegrableOn (fun w => G₁ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b))
    (h₂ : IntegrableOn (fun w => G₂ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b)) :
    faceCoeffInt (fun w => c₁ * G₁ w + c₂ * G₂ w) h a b μ e =
      c₁ * faceCoeffInt G₁ h a b μ e + c₂ * faceCoeffInt G₂ h a b μ e := by
  unfold faceCoeffInt
  have hpt : ∀ w : ι → ℝ, (c₁ * G₁ w + c₂ * G₂ w) * mono h w * mono a w ^ (-μ) * logSum a w ^ e =
      c₁ * (G₁ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) +
        c₂ * (G₂ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) := fun w => by ring
  simp only [hpt]
  rw [integral_add (h₁.const_mul _) (h₂.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-- ★ **Linearity of the renormalised functional in the face field.** -/
theorem renormFunctional_add_smul (hD : ContDiff ℝ ∞ D) {U₁ U₂ : (Fin d → ℝ) → ℝ}
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂) (hb : 0 < b) (hp0 : ∀ i, 0 < p i)
    (J : Finset (Fin d)) (a : Fin d → ℕ) (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1)
    (q : ℕ) (c₁ c₂ : ℝ) :
    renormFunctional D h k p β b J a μ q (fun v => c₁ * U₁ v + c₂ * U₂ v) =
      c₁ * renormFunctional D h k p β b J a μ q U₁ +
        c₂ * renormFunctional D h k p β b J a μ q U₂ := by
  unfold renormFunctional
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  have hfun : (fun v => pdMulti (m - a) (lJ J) D v * (c₁ * U₁ v + c₂ * U₂ v)) =
      fun v => c₁ * (pdMulti (m - a) (lJ J) D v * U₁ v) +
        c₂ * (pdMulti (m - a) (lJ J) D v * U₂ v) := by
    funext v; ring
  have hamp : faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * (c₁ * U₁ v + c₂ * U₂ v)) 0 =
      fun w => c₁ * faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * U₁ v) 0 w +
        c₂ * faceAmp p J (fun v => pdMulti (m - a) (lJ J) D v * U₂ v) 0 w := by
    funext w
    rw [hfun]
    exact faceAmp_zero_add_smul ((contDiff_pdMulti hD _ _).mul hU₁)
      ((contDiff_pdMulti hD _ _).mul hU₂) c₁ c₂ J w
  rw [hamp, faceCoeffInt_add_smul c₁ c₂ _ _ _ _ _
    (integrableOn_faceCoeff_faceAmp_zero ((contDiff_pdMulti hD _ _).mul hU₁) hb hp0 J hμ _)
    (integrableOn_faceCoeff_faceAmp_zero ((contDiff_pdMulti hD _ _).mul hU₂) hb hp0 J hμ _)]
  ring

theorem renormFunctional_add (hD : ContDiff ℝ ∞ D) {U₁ U₂ : (Fin d → ℝ) → ℝ}
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂) (hb : 0 < b) (hp0 : ∀ i, 0 < p i)
    (J : Finset (Fin d)) (a : Fin d → ℕ) (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1)
    (q : ℕ) :
    renormFunctional D h k p β b J a μ q (fun v => U₁ v + U₂ v) =
      renormFunctional D h k p β b J a μ q U₁ + renormFunctional D h k p β b J a μ q U₂ := by
  have h := renormFunctional_add_smul (β := β) hD hU₁ hU₂ hb hp0 J a hμ q 1 1
  simpa only [one_mul] using h

theorem renormFunctional_smul (hD : ContDiff ℝ ∞ D) {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiff ℝ ∞ U) (hb : 0 < b) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) (a : Fin d → ℕ)
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (q : ℕ) (c : ℝ) :
    renormFunctional D h k p β b J a μ q (fun v => c * U v) =
      c * renormFunctional D h k p β b J a μ q U := by
  have h := renormFunctional_add_smul (β := β) hD hU hU hb hp0 J a hμ q c 0
  simpa only [zero_mul, add_zero] using h

/-! ### Finite-jet dependence: the functional reads the normal jets of the face field -/

/-- ★ **The iterated remainder depends only on the jets** `∂^α_l H`, `α ≤ p`, on a set stable
under the coordinate zeroings `v ↦ v[i := 0]`, `i ∈ l`. -/
theorem remList_congr_of_jets (p : Fin d → ℕ) {H H' : (Fin d → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (hH' : ContDiff ℝ ∞ H') {Z : Set (Fin d → ℝ)} {l : List (Fin d)} (hl : l.Nodup)
    (hZ : ∀ i ∈ l, ∀ v ∈ Z, Function.update v i 0 ∈ Z)
    (hjet : ∀ α : Fin d → ℕ, (∀ i ∈ l, α i ≤ p i) → (∀ i, i ∉ l → α i = 0) →
      ∀ v ∈ Z, pdMulti α l H v = pdMulti α l H' v) :
    ∀ v ∈ Z, remList p l H v = remList p l H' v := by
  induction l generalizing H H' with
  | nil =>
    intro v hv
    have := hjet 0 (fun i hi => Nat.zero_le _) (fun i _ => rfl) v hv
    simpa only [pdMulti_nil, remList_nil] using this
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    intro v hv
    have hpt : ∀ H : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ H → remList p (i :: l) H v =
        remList p l H v - ∑ n ∈ Finset.range (p i), ((n.factorial : ℝ)⁻¹ * v i ^ n) *
          remList p l (pdPow i n H) (Function.update v i 0) := fun H hH => by
      rw [remList_cons]
      change remList p l H v - coordTaylor i (p i) (remList p l H) v = _
      rw [coordTaylor_apply]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pdPow_remList p hH hi]
    rw [hpt H hH, hpt H' hH']
    have hZ' : ∀ j ∈ l, ∀ v ∈ Z, Function.update v j 0 ∈ Z := fun j hj =>
      hZ j (List.mem_cons_of_mem i hj)
    have h0 : ∀ v ∈ Z, remList p l H v = remList p l H' v := by
      refine ih hH hH' hl' hZ' fun α hα hα0 v hv => ?_
      have hαi : α i = 0 := hα0 i hi
      have := hjet α (fun j hj => by
          rcases List.mem_cons.1 hj with hji | hjl
          · subst hji; rw [hαi]; exact Nat.zero_le _
          · exact hα j hjl)
        (fun j hj => hα0 j fun h => hj (List.mem_cons_of_mem i h)) v hv
      rwa [pdMulti_cons, pdMulti_cons, hαi, pdPow_zero, pdPow_zero] at this
    have hn : ∀ n ∈ Finset.range (p i), remList p l (pdPow i n H) (Function.update v i 0) =
        remList p l (pdPow i n H') (Function.update v i 0) := fun n hn => by
      have hnp : n ≤ p i := (Finset.mem_range.1 hn).le
      refine ih (contDiff_pdPow hH i n) (contDiff_pdPow hH' i n) hl' hZ'
        (fun α hα hα0 v hv => ?_) _ (hZ i (List.mem_cons_self ..) v hv)
      have := hjet (Function.update α i n) (fun j hj => by
          rcases List.mem_cons.1 hj with hji | hjl
          · subst hji; rw [Function.update_self]; exact hnp
          · have hji : j ≠ i := fun h => hi (h ▸ hjl)
            rw [Function.update_of_ne hji]; exact hα j hjl)
        (fun j hj => by
          have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
          rw [Function.update_of_ne hji]
          exact hα0 j fun h => hj (List.mem_cons_of_mem i h)) v hv
      rwa [pdMulti_cons, pdMulti_cons, Function.update_self, pdMulti_update_of_not_mem hi,
        pdMulti_update_of_not_mem hi, pdPow_pdMulti hH, pdPow_pdMulti hH'] at this
    rw [h0 v hv, Finset.sum_congr rfl fun n hn' => by rw [hn n hn']]

/-- The face `{v ∈ [0,b]^d | v_J = 0}` is stable under the complementary zeroings. -/
theorem face_update_mem {J : Finset (Fin d)} (hb : 0 ≤ b) {i : Fin d} (hi : i ∈ lK J)
    {v : Fin d → ℝ} (hv : (∀ j, v j ∈ Icc 0 b) ∧ ∀ j ∈ J, v j = 0) :
    (∀ j, Function.update v i 0 j ∈ Icc 0 b) ∧ ∀ j ∈ J, Function.update v i 0 j = 0 := by
  have hiJ : i ∉ J := (mem_lK J).1 hi
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · by_cases hji : j = i
    · subst hji; simp [hb]
    · rw [Function.update_of_ne hji]; exact hv.1 j
  · have hji : j ≠ i := fun h => hiJ (h ▸ hj)
    rw [Function.update_of_ne hji]; exact hv.2 j hj

/-- ★★ **Finite-jet dependence**: the renormalised functional of two smooth face fields with the
same complementary jets `∂^α_K U`, `α ≤ p`, on the face `{v ∈ [0,b]^d | v_J = 0}` agree — the
functional reads only the normal jets of the field along the face. -/
theorem renormFunctional_congr (hD : ContDiff ℝ ∞ D) {U U' : (Fin d → ℝ) → ℝ}
    (hU : ContDiff ℝ ∞ U) (hU' : ContDiff ℝ ∞ U') (hb : 0 < b) (J : Finset (Fin d))
    (a : Fin d → ℕ) (q : ℕ)
    (hjet : ∀ α : Fin d → ℕ, (∀ i, α i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      (∀ i ∈ J, v i = 0) → pdMulti α (lK J) U v = pdMulti α (lK J) U' v) :
    renormFunctional D h k p β b J a μ q U = renormFunctional D h k p β b J a μ q U' := by
  unfold renormFunctional
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold faceCoeffInt
  refine setIntegral_congr_fun (measurableSet_box b) fun w hw => ?_
  congr 3
  unfold faceAmp
  rw [pdMulti_zero, pdMulti_zero]
  set Dm : (Fin d → ℝ) → ℝ := pdMulti (m - a) (lJ J) D with hDm
  have hDm' : ContDiff ℝ ∞ Dm := contDiff_pdMulti hD _ _
  have hZ : ∀ i ∈ lK J, ∀ v : Fin d → ℝ, v ∈ {v | (∀ j, v j ∈ Icc 0 b) ∧ ∀ j ∈ J, v j = 0} →
      Function.update v i 0 ∈ {v | (∀ j, v j ∈ Icc 0 b) ∧ ∀ j ∈ J, v j = 0} :=
    fun i hi v hv => face_update_mem hb.le hi hv
  have hjet' : ∀ α : Fin d → ℕ, (∀ i ∈ lK J, α i ≤ p i) → (∀ i, i ∉ lK J → α i = 0) →
      ∀ v ∈ {v : Fin d → ℝ | (∀ j, v j ∈ Icc 0 b) ∧ ∀ j ∈ J, v j = 0},
        pdMulti α (lK J) (fun v => Dm v * U v) v = pdMulti α (lK J) (fun v => Dm v * U' v) v := by
    intro α hα hα0 v hv
    rw [pdMulti_mul hDm' hU α (nodup_lK J), pdMulti_mul hDm' hU' α (nodup_lK J)]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcp : ∀ i, c i ≤ p i := fun i => by
      have h1 := (Fintype.mem_piFinset.1 hc) i
      by_cases hi : i ∈ lK J
      · simp only [hi, if_true, Finset.mem_range] at h1
        exact (Nat.lt_succ_iff.1 h1).trans (hα i hi)
      · simp only [hi, if_false, Finset.mem_singleton] at h1
        rw [h1]; exact Nat.zero_le _
    rw [hjet c hcp v hv.1 hv.2]
  exact remList_congr_of_jets p (hDm'.mul hU) (hDm'.mul hU') (nodup_lK J) hZ hjet' (glue J 0 w)
    ⟨glue_zero_mem_Icc J hb hw, fun i hi => glue_apply_of_mem J _ _ hi⟩

/-! ### Regression: the deepest stratum -/

theorem faceCoeffInt_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (G : (ι → ℝ) → ℝ) (h a : ι → ℕ)
    (b μ : ℝ) (e : ℕ) : faceCoeffInt G h a b μ e = G 0 * (0 : ℝ) ^ e := by
  unfold faceCoeffInt
  rw [box_isEmpty, Measure.restrict_univ]
  have hpt : ∀ w : ι → ℝ, G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e = G 0 * 0 ^ e :=
    fun w => by
      rw [mono_isEmpty, mono_isEmpty, Subsingleton.elim w 0]
      simp [logSum]
  simp only [hpt]
  rw [integral_const, smul_eq_mul, Measure.real, volume_pi, Measure.pi_univ]
  simp

theorem lK_univ : lK (univ : Finset (Fin d)) = [] := by
  unfold lK
  simp

theorem glue_univ_zero (w : {i // ¬ inJ (univ : Finset (Fin d)) i} → ℝ) :
    glue univ 0 w = 0 := by
  funext i
  rw [glue_apply_of_mem _ _ _ (Finset.mem_univ i)]
  rfl

/-- ★ **Regression, the deepest stratum `J = univ`** (in particular every face of `d = 1`): no
complementary coordinates, so the functional is the bilinear pairing of the jets of `D` and `U` at
the origin against the face coefficients — the classical Laplace coefficients
`∑_{m ≥ a} 1/(m−a)! · ∂^{m−a} D(0) · U(0) · c_{m+h,μ,q}`. -/
theorem renormFunctional_univ (a : Fin d → ℕ) (q : ℕ) (U : (Fin d → ℝ) → ℝ) :
    renormFunctional D h k p β b univ a μ q U =
      ∑ m ∈ (idxL p (lJ univ)).filter (fun m => ∀ i, a i ≤ m i), faceW univ (m - a) *
        ∑ j ∈ Finset.Ico q (DJ (univ : Finset (Fin d)) + 1),
          faceCoef k β b univ (fun i => m i + h i) μ j *
          (j.choose q) * (pdMulti (m - a) (lJ univ) D 0 * U 0 * (0 : ℝ) ^ (j - q)) := by
  unfold renormFunctional
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : IsEmpty {i // ¬ inJ (univ : Finset (Fin d)) i} := ⟨fun i => i.2 (Finset.mem_univ i.1)⟩
  rw [faceCoeffInt_isEmpty]
  unfold faceAmp
  rw [pdMulti_zero, lK_univ, remList_nil, glue_univ_zero]

/-! ### Box congruence of the canonical coefficients -/

/-- ★ **The canonical coefficients see the amplitude only on the box** (from canonicity): two
smooth amplitudes equal on `(0,b]^d` have the same `smoothCoeff`. -/
theorem smoothCoeff_congr_box {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (heq : ∀ v ∈ box (Fin d) b, F v = G v) (μ : ℝ)
    (q : ℕ) : smoothCoeff F h k β b μ q = smoothCoeff G h k β b μ q := by
  have hint : smoothIntegral F h k β b = smoothIntegral G h k β b := funext fun N =>
    setIntegral_congr_fun (measurableSet_box b) fun v hv => by simp only [heq v hv]
  by_cases hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · by_cases hq : q ≤ d - 1
    · have hc := smooth_cutoffExpansion hF hk hβ hb (h := h)
      rw [hint] at hc
      exact smoothCoeff_unique hG hk hβ hb hc hμ hq
    · rw [smoothCoeff_eq_zero_of_degree_gt (by omega),
        smoothCoeff_eq_zero_of_degree_gt (by omega)]
  · push Not at hμ
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ,
      smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ]

/-! ### Product families over a compact base -/

namespace SmoothAmplitudeFamily

variable {S : Type*} [TopologicalSpace S]

/-- The derivative family `s ↦ ∂^{m'} (F s)`. -/
noncomputable def pdMulti (F : SmoothAmplitudeFamily S d b) (m' : Fin d → ℕ) :
    SmoothAmplitudeFamily S d b where
  amp s := SmoothEngine.pdMulti m' (List.finRange d) (F s)
  smooth s := contDiff_pdMulti (F.smooth s) m' _
  deriv_cont := derivsCont_pdMulti F.smooth F.deriv_cont m'

theorem pdMulti_apply (F : SmoothAmplitudeFamily S d b) (m' : Fin d → ℕ) (s : S) :
    (F.pdMulti m') s = SmoothEngine.pdMulti m' (List.finRange d) (F s) := rfl

/-- The product family `s ↦ F s · G s` (jointly continuous derivatives by the Leibniz rule). -/
noncomputable def mul (F G : SmoothAmplitudeFamily S d b) : SmoothAmplitudeFamily S d b where
  amp s v := F s v * G s v
  smooth s := (F.smooth s).mul (G.smooth s)
  deriv_cont m := by
    have hpt : ∀ z : S × (Fin d → ℝ),
        SmoothEngine.pdMulti m (List.finRange d) (fun v => F z.1 v * G z.1 v) z.2 =
        ∑ a ∈ idxL (fun j => m j + 1) (List.finRange d),
          (∏ i ∈ (List.finRange d).toFinset, ((m i).choose (a i) : ℝ)) *
            (SmoothEngine.pdMulti (m - a) (List.finRange d) (F z.1) z.2 *
              SmoothEngine.pdMulti a (List.finRange d) (G z.1) z.2) := fun z => by
      rw [pdMulti_mul (F.smooth z.1) (G.smooth z.1) m (List.nodup_finRange d)]
    refine ContinuousOn.congr (continuousOn_finsetSum _ fun a _ =>
      continuousOn_const.mul ((F.deriv_cont (m - a)).mul (G.deriv_cont a))) fun z _ => hpt z

theorem mul_apply (F G : SmoothAmplitudeFamily S d b) (s : S) :
    (F.mul G) s = fun v => F s v * G s v := rfl

end SmoothAmplitudeFamily

theorem mem_idxL_of_le {l : List (Fin d)} {m a : Fin d → ℕ} (hm : m ∈ idxL p l)
    (hle : ∀ i, a i ≤ m i) : a ∈ idxL p l := by
  rw [idxL, Fintype.mem_piFinset] at hm ⊢
  intro i
  have h := hm i
  by_cases hi : i ∈ l
  · simp only [hi, if_true, Finset.mem_range] at h ⊢
    exact lt_of_le_of_lt (hle i) h
  · simp only [hi, if_false, Finset.mem_singleton] at h ⊢
    have := hle i
    omega

section Family

variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [FirstCountableTopology S]

/-- ★ **Parameter continuity of the renormalised functionals** of a pair of families. -/
theorem continuous_renormFunctional_family (Dfam ffam : SmoothAmplitudeFamily S d b) (hb : 0 < b)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {a : Fin d → ℕ} (ha : a ∈ idxL p (lJ J))
    (hμ : ∀ i, ((2 * k i : ℕ) : ℝ) * μ < p i + h i + 1) (q : ℕ) :
    Continuous fun s =>
      renormFunctional (Dfam s) h k p β b J a μ q (pdMulti a (lJ J) (ffam s)) := by
  unfold renormFunctional
  refine continuous_finsetSum _ fun m hm => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_const.mul continuous_const).mul ?_)
  have hm' : m ∈ idxL p (lJ J) := (Finset.mem_filter.1 hm).1
  have hma : m - a ∈ idxL p (lJ J) := mem_idxL_of_le hm' fun i => Nat.sub_le _ _
  have heq : ∀ s, (fun v => pdMulti (m - a) (lJ J) (Dfam s) v * pdMulti a (lJ J) (ffam s) v) =
      ((Dfam.pdMulti (m - a)).mul (ffam.pdMulti a)) s := fun s => by
    rw [SmoothAmplitudeFamily.mul_apply, SmoothAmplitudeFamily.pdMulti_apply,
      SmoothAmplitudeFamily.pdMulti_apply, pdMulti_lJ_eq_finRange hma (Dfam.smooth s),
      pdMulti_lJ_eq_finRange ha (ffam.smooth s)]
  simp only [heq]
  exact SmoothAmplitudeFamily.continuous_faceCoeffInt_family _ hb hp0 J
    (zero_mem_idxL p hp0 (lJ J)) hμ (j - q)

variable [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν]

/-- ★★ **The renormalised chart-strata formula for the integrated coefficients** of a product family
with a constant phase unit. -/
theorem familyCoeff_mul_eq (Dfam ffam : SmoothAmplitudeFamily S d b) (hk : ∀ i, 0 < k i)
    (hb : 0 < b) (β μ : ℝ) (q : ℕ) :
    familyCoeff ν (Dfam.mul ffam) h k (fun _ => β) b μ q =
      ∑ J : Finset (Fin d), ∑ a ∈ idxL (depthOf h k (cutoffOf h μ)) (lJ J), faceW J a *
        ∫ s, renormFunctional (Dfam s) h k (depthOf h k (cutoffOf h μ)) β b J a μ q
          (pdMulti a (lJ J) (ffam s)) ∂ν := by
  unfold familyCoeff
  have hpt : ∀ s, smoothCoeff ((Dfam.mul ffam) s) h k β b μ q =
      ∑ J : Finset (Fin d), ∑ a ∈ idxL (depthOf h k (cutoffOf h μ)) (lJ J), faceW J a *
        renormFunctional (Dfam s) h k (depthOf h k (cutoffOf h μ)) β b J a μ q
          (pdMulti a (lJ J) (ffam s)) := fun s => by
    rw [SmoothAmplitudeFamily.mul_apply]
    exact smoothCoeff_mul_eq (Dfam.smooth s) (ffam.smooth s) hk hb μ q
  have hint : ∀ (J : Finset (Fin d)) (a : Fin d → ℕ),
      a ∈ idxL (depthOf h k (cutoffOf h μ)) (lJ J) →
      Integrable (fun s => faceW J a * renormFunctional (Dfam s) h k
        (depthOf h k (cutoffOf h μ)) β b J a μ q (pdMulti a (lJ J) (ffam s))) ν := fun J a ha =>
    (integrable_of_continuous_compactSpace ν (continuous_renormFunctional_family Dfam ffam hb
      (depthOf_pos hk (L₀_le_cutoffOf h μ)) J ha
      (two_k_mul_lt_of_le (depthOf_add hk (L₀_le_cutoffOf h μ))
        (lt_cutoffOf h μ).le) q)).const_mul _
  simp only [hpt]
  rw [integral_finsetSum _ fun J _ => integrable_finsetSum _ fun a ha => hint J a ha]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [integral_finsetSum _ fun a ha => hint J a ha]
  exact Finset.sum_congr rfl fun a _ => MeasureTheory.integral_const_mul _ _

end Family

/-! ### The producer: transport density × observable on every piece -/

namespace BridgeInputs

open Monomialize.VolumeScaling

variable (X : BridgeInputs d)

theorem exists_obsExt (i : X.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (fun u => X.obs (X.T.ψ i u)) (centeredBox d (X.T.a i)) := by
  obtain ⟨g, hg, heq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (X.T.V_open i)
    (isCompact_centeredBox d (X.T.a i)).isClosed (X.T.box_subset_V i)
    (X.obs_smooth.comp_contDiffOn (X.contDiffOn_ψ i))
  exact ⟨g, hg, heq⟩

/-- The globally smooth observable of chart `i`, equal to `obs ∘ ψ` on the box. -/
noncomputable def obsExt (i : X.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (X.exists_obsExt i)

theorem contDiff_obsExt (i : X.T.ι) : ContDiff ℝ ∞ (X.obsExt i) :=
  (Classical.choose_spec (X.exists_obsExt i)).1

theorem obsExt_eq (i : X.T.ι) {u : Fin d → ℝ} (hu : u ∈ centeredBox d (X.T.a i)) :
    X.obsExt i u = X.obs (X.T.ψ i u) := (Classical.choose_spec (X.exists_obsExt i)).2 hu

/-- The transport-density family of a piece: `s ↦ ρ ∘ T_s`. -/
noncomputable def ρfam (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) (X.T.a p.1)) (X.da p) (X.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2 (X.contDiff_ρf p.1) (X.T.a p.1)

/-- The observable family of a piece: `s ↦ (obs ∘ ψ) ∘ T_s` (through the smooth extension). -/
noncomputable def obsfam (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) (X.T.a p.1)) (X.da p) (X.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2 (X.contDiff_obsExt p.1)
    (X.T.a p.1)

theorem ρfam_apply (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    X.ρfam p s v = X.ρf p.1 (X.Tm p s v) := rfl

theorem obsfam_apply (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    X.obsfam p s v = X.obsExt p.1 (X.Tm p s v) := rfl

/-- On the closed box the piece amplitude is the product density × observable. -/
theorem amp_eq_mul (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) {v : Fin (X.da p) → ℝ}
    (hv : ∀ j, v j ∈ Icc 0 (X.T.a p.1)) : X.amp p s v = X.ρfam p s v * X.obsfam p s v := by
  change X.G p.1 (X.Tm p s v) = X.ρf p.1 (X.Tm p s v) * X.obsExt p.1 (X.Tm p s v)
  rw [X.G_eq p.1 (X.Tm_mem_box p s hv), X.ρf_eq p.1 (X.Tm_mem_box p s hv),
    X.obsExt_eq p.1 (X.Tm_mem_box p s hv)]
  rfl

/-- ★★ **The renormalised strata formula for one piece.** -/
theorem familyCoeff_piece_eq (p : X.PIdx) (μ : ℝ) (q : ℕ) :
    familyCoeff (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)) (X.amp p) (X.hA p) (X.kA p)
        (fun _ => X.T.phaseConst p.1) (X.T.a p.1) μ q =
      ∑ J : Finset (Fin (X.da p)),
        ∑ a ∈ idxL (depthOf (X.hA p) (X.kA p) (cutoffOf (X.hA p) μ)) (lJ J), faceW J a *
          ∫ s, renormFunctional (X.ρfam p s) (X.hA p) (X.kA p)
            (depthOf (X.hA p) (X.kA p) (cutoffOf (X.hA p) μ)) (X.T.phaseConst p.1) (X.T.a p.1)
            J a μ q (pdMulti a (lJ J) (X.obsfam p s))
            ∂(baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)) := by
  rw [← familyCoeff_mul_eq _ (X.ρfam p) (X.obsfam p) (X.kA_pos p) (X.T.a_pos p.1)]
  unfold familyCoeff
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  refine smoothCoeff_congr_box ((X.amp p).smooth s) (((X.ρfam p).mul (X.obsfam p)).smooth s)
    (X.kA_pos p) (X.T.phaseConst_pos p.1) (X.T.a_pos p.1) (fun v hv => ?_) μ q
  rw [SmoothAmplitudeFamily.mul_apply]
  exact X.amp_eq_mul p s fun j => Ioc_subset_Icc_self (hv j (Set.mem_univ j))

/-- ★★★ **The renormalised chart-strata formula for the resolution-bridge producer**: the
coordinate-free coefficients of `∫ prior · obs · e^{−NK}` are, piece by piece, face by face and
jet by jet, density-only renormalised functionals of the transport density `ρ ∘ T_s` applied to
the face jets of the observable `(obs ∘ ψ) ∘ T_s`, integrated over the compact base of the piece.
The complementary Taylor remainders stay inside the functionals (finite part). -/
theorem coeff_eq_renormSum (μ : ℝ) (q : ℕ) :
    X.decomp.coeff μ q = ∑ I : Fin (Fintype.card X.PIdx),
      ∑ J : Finset (Fin (X.da (X.en I))),
        ∑ a ∈ idxL (depthOf (X.hA (X.en I)) (X.kA (X.en I)) (cutoffOf (X.hA (X.en I)) μ)) (lJ J),
          faceW J a * ∫ s, renormFunctional (X.ρfam (X.en I) s) (X.hA (X.en I)) (X.kA (X.en I))
            (depthOf (X.hA (X.en I)) (X.kA (X.en I)) (cutoffOf (X.hA (X.en I)) μ))
            (X.T.phaseConst (X.en I).1) (X.T.a (X.en I).1) J a μ q
            (pdMulti a (lJ J) (X.obsfam (X.en I) s))
            ∂(baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)) :=
  Finset.sum_congr rfl fun I _ => X.familyCoeff_piece_eq (X.en I) μ q

end BridgeInputs

end SmoothEngine

end Grammar
