/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalChartMellin
import Grammar.FiniteFacePolar
import Grammar.EmpiricalLeadingConsistency

/-!
# The meromorphic continuation of the empirical Mellin transform (route B, unit B11)

The coupled face sum at depth `p`,

  `empZetaAtDepth p η ζ h k s
     = Σ_{(J,m)} faceW · innerFactor h k J m s · coupledFaceZeta p η ζ h k J m s`,
  `coupledFaceZeta p η ζ h k J m s
     = ∫_0^∞ t^{s−1} e^{−t} chartZeta (faceAmp p J (η e^{√t ζ}) m) h_{Jᶜ} k_{Jᶜ} s dt`,

is holomorphic on the positive flat strip off the candidate poles
(`differentiableOn_empZetaAtDepth`,
from the flat growth bound `growthLE_faceAmp_fieldFam` and the coupled chart zeta functional of
`CoupledChartZeta`), equals the Mellin transform of the empirical integral on the initial strip
(`empZetaAtDepth_eq_mellin`: (B1) and the face decomposition `chartZeta_eq_sum_faces` at every
coupling), and therefore, by the identity theorem on the strip `0 < Re s < L` minus the finite set
of candidate poles and lattice points, equals the library's Mellin continuation
`mellinContinuation (Qamb k) (d−1) (empIntegral η ζ h k) (empCoeff η ζ h k) L` at the canonical
depth `p = depthOf h k L` (★★ `empZetaAtDepth_eq_mellinContinuation`).  The seed of the identity
theorem is the substrip `0 < Re s < 1/Qamb k`, below every candidate exponent, where the empirical
coefficients vanish (`empCoeff_eq_zero_of_boxLeading_lt`) so that the continuation is the plain
Mellin transform.  The local form ★ `empZetaAtDepth_eventuallyEq_mellinContinuation` on a punctured
neighbourhood of any `0 < μ < L` is the input of unit B12.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### The coupled face zeta functions and the coupled face sum -/

section Defs

/-- The coupled chart zeta functional of the face amplitude family of the field family. -/
noncomputable def coupledFaceZeta (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (s : ℂ) : ℂ :=
  coupledChartZeta (fun τ => SmoothEngine.faceAmp p J (fieldFam η ζ τ) m)
    (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s

/-- The coupled face sum at depth `p`. -/
noncomputable def empZetaAtDepth (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (s : ℂ) : ℂ :=
  ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
    innerFactor h k x.1 x.2 s * coupledFaceZeta p η ζ h k x.1 x.2 s

end Defs

/-! ### The flat growth bound of the face amplitude family -/

section Growth

variable {η ζ : (Fin d → ℝ) → ℝ}

/-- The face amplitudes of the field family are flat with uniform exponential growth in the
coupling: `|faceAmp p J (η e^{τζ}) m w| ≤ C (1+τ)^{|p|} e^{Mτ} w^{p_K}`. -/
theorem flatOn_faceAmp_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) :
    ∃ C M : ℝ, 0 ≤ C ∧ ∀ (J : Finset (Fin d)) (m : Fin d → ℕ),
      m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J) → ∀ τ, 0 ≤ τ →
        FlatOn (fun w => SmoothEngine.faceAmp p J (fieldFam η ζ τ) m w)
          (fun i : {i // ¬ inJ J i} => p i)
          (C * (1 + τ) ^ (∑ i, p i) * Real.exp (M * τ)) := by
  obtain ⟨M, _, hM⟩ := exists_abs_bound_closedBox hζ
  obtain ⟨C, hC0, hC⟩ := growthLE_faceAmp_fieldFam hη hζ one_pos hM p hp0
  refine ⟨C, M, hC0, fun J m hm τ hτ w hw => ?_⟩
  have hG := hC J m hm w hw τ hτ
  have hfact : ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹ ≤ 1 :=
    Finset.prod_le_one (fun i _ => by positivity) fun i _ =>
      inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  have hmono : 0 ≤ mono (fun i : {i // ¬ inJ J i} => p i) w :=
    mono_nonneg_of_pos (fun i => SmoothEngine.pos_of_mem_box hw i) _
  have hE : 0 ≤ (1 + τ) ^ (∑ i, p i) * Real.exp (M * τ) := by positivity
  calc |SmoothEngine.faceAmp p J (fieldFam η ζ τ) m w|
      ≤ (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
          mono (fun i : {i // ¬ inJ J i} => p i) w *
          ((1 + τ) ^ (∑ i, p i) * Real.exp (M * τ)) := by
        have := hG
        linarith [this]
    _ ≤ 1 * C * mono (fun i : {i // ¬ inJ J i} => p i) w *
          ((1 + τ) ^ (∑ i, p i) * Real.exp (M * τ)) := by
        gcongr
    _ = C * (1 + τ) ^ (∑ i, p i) * Real.exp (M * τ) *
          mono (fun i : {i // ¬ inJ J i} => p i) w := by ring

/-- The coupled face zeta functions are holomorphic on the positive flat strip. -/
theorem differentiableOn_coupledFaceZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (h k : Fin d → ℕ) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) :
    DifferentiableOn ℂ (coupledFaceZeta p η ζ h k J m) {s : ℂ | 0 < s.re ∧ FlatStrip p h k s} := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  exact (differentiableOn_coupledChartZeta (continuous_faceAmp_fieldFam_joint hη hζ p J m) hC
    (hflat J m hm) _ _).mono fun s hs => ⟨hs.1, flatStrip_subtype J hs.2⟩

/-- ★ **The coupled face sum is holomorphic** on the positive flat strip off the candidate
poles. -/
theorem differentiableOn_empZetaAtDepth (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (h k : Fin d → ℕ) :
    DifferentiableOn ℂ (empZetaAtDepth p η ζ h k)
      {s : ℂ | 0 < s.re ∧ FlatStrip p h k s ∧ ¬ PoleAt p h k s} := by
  unfold empZetaAtDepth
  refine differentiableOn_finset_sum' _ fun x hx => ?_
  have hm : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := (Finset.mem_sigma.1 hx).2
  refine DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _) ?_) ?_
  · exact differentiableOn_innerFactor h k x.1 x.2 fun s hs i hi hden =>
      hs.2.2 ⟨x, hx, i, hi, hden⟩
  · exact (differentiableOn_coupledFaceZeta hη hζ p hp0 h k x.1 hm).mono fun s hs =>
      ⟨hs.1, hs.2.1⟩

end Growth

/-! ### The marginal integrability and the identity on the initial strip -/

section Initial

variable {ι : Type*} [Fintype ι]

/-- The `t`-marginal of the coupled integrand is integrable on the positive flat strip. -/
theorem integrable_coupKernel_mul_chartZeta {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ}
    {M : ℝ} (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    Integrable (fun t : ℝ => coupKernel s t * chartZeta (H (Real.sqrt t)) h k s)
      (volume.restrict (Ioi 0)) := by
  have hint := (integrable_coupIntegrand hH hC hflat h k 0 hs0 hs).integral_prod_left
  refine hint.congr (Eventually.of_forall fun t => ?_)
  simp only
  unfold chartZeta
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun w _ => ?_
  simp only [coupIntegrand, pow_zero, mul_one]
  ring

variable {η ζ : (Fin d → ℝ) → ℝ}

theorem ZetaStrip.flatStrip_of_nonneg {h k : Fin d → ℕ} {s : ℂ} (hs : ZetaStrip h k s)
    (p : Fin d → ℕ) : FlatStrip p h k s := fun i => by
  have := hs i
  have : (0 : ℝ) ≤ p i := Nat.cast_nonneg _
  linarith

/-- ★ **The coupled face sum is the Mellin transform of the empirical integral** on the initial
strip. -/
theorem empZetaAtDepth_eq_mellin (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (h k : Fin d → ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    empZetaAtDepth p η ζ h k s = mellin (fun N => (empIntegral η ζ h k N : ℂ)) s := by
  rw [mellin_empIntegral_eq_coupledChartZeta hη hζ hs0 hs]
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hface : ∀ t : ℝ, chartZeta (fieldFam η ζ (Real.sqrt t)) h k s =
      ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
        innerFactor h k x.1 x.2 s *
        chartZeta (SmoothEngine.faceAmp p x.1 (fieldFam η ζ (Real.sqrt t)) x.2)
          (fun i : {i // ¬ inJ x.1 i} => h i) (fun i => k i) s := fun t =>
    chartZeta_eq_sum_faces p (contDiff_fieldFam hη hζ _) h k hs
  unfold coupledChartZeta empZetaAtDepth coupledFaceZeta coupledChartZeta
  simp_rw [hface, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := (Finset.mem_sigma.1 hx).2
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  · intro x hx
    have hm : x.2 ∈ SmoothEngine.idxL p (SmoothEngine.lJ x.1) := (Finset.mem_sigma.1 hx).2
    have := (integrable_coupKernel_mul_chartZeta (continuous_faceAmp_fieldFam_joint hη hζ p x.1 x.2)
      hC (hflat x.1 x.2 hm) _ _ hs0 (flatStrip_subtype x.1 (hs.flatStrip_of_nonneg p))).const_mul
      (((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * innerFactor h k x.1 x.2 s)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    ring

end Initial

/-! ### The identity theorem -/

section Continuation

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- At the canonical depth the flat strip contains `Re s < L`. -/
theorem flatStrip_depthOf_of_re_lt (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {s : ℂ}
    (hs : s.re < L) : FlatStrip (depthOf h k L) h k s := by
  intro i
  have hadd : ((depthOf h k L i : ℕ) : ℝ) + h i = 2 * k i * L := by
    exact_mod_cast depthOf_add hk hL i
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  rw [hadd]
  nlinarith

/-- Every candidate pole has real part at least the smallest ratio exponent. -/
theorem ratioExp_le_re_of_poleAt {p : Fin d → ℕ} (hk : ∀ i, 0 < k i) {s : ℂ}
    (hs : PoleAt p h k s) : ∃ i, ratioExp h k i ≤ s.re := by
  obtain ⟨x, _, i, _, hden⟩ := hs
  refine ⟨i, ?_⟩
  have hre := congrArg Complex.re hden
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, Complex.one_re, Complex.zero_re,
    mul_zero, sub_zero, zero_mul] at hre
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  unfold ratioExp
  rw [div_le_iff₀ (by positivity)]
  push_cast at hre
  have : (0 : ℝ) ≤ x.2 i := Nat.cast_nonneg _
  nlinarith

/-- The seed exponent `1/Qamb k` lies below every ratio exponent. -/
theorem inv_Qamb_le_ratioExp (hk : ∀ i, 0 < k i) (i : Fin d) :
    (1 : ℝ) / Qamb k ≤ ratioExp h k i := by
  have hQ : (0 : ℝ) < Qamb k := by exact_mod_cast Qamb_pos k hk
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  have hkQ : 2 * (k i : ℝ) ≤ Qamb k := by
    unfold Qamb
    push_cast
    have hprod : ∏ j, (k j : ℝ) = (k i : ℝ) * ∏ j ∈ Finset.univ.erase i, (k j : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun j => (k j : ℝ)) (Finset.mem_univ i)).symm
    have h1 : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (k j : ℝ) := by
      have : 0 < ∏ j ∈ Finset.univ.erase i, k j := Finset.prod_pos fun j _ => hk j
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this.ne'
    have : (k i : ℝ) ≤ ∏ j, (k j : ℝ) := by
      rw [hprod]; exact le_mul_of_one_le_right hki.le h1
    linarith
  unfold ratioExp
  rw [div_le_div_iff₀ hQ (by positivity)]
  have : (0 : ℝ) ≤ h i := Nat.cast_nonneg _
  nlinarith

theorem zetaStrip_of_re_lt_inv_Qamb (hk : ∀ i, 0 < k i) {s : ℂ} (hs : s.re < 1 / Qamb k) :
    ZetaStrip h k s := fun i => by
  have h1 := inv_Qamb_le_ratioExp (h := h) hk i
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  unfold ratioExp at h1
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

/-- The empirical coefficients vanish below the seed exponent. -/
theorem empCoeff_eq_zero_of_lt_inv_Qamb (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : μ < 1 / Qamb k)
    (q : ℕ) : empCoeff η ζ h k μ q = 0 := by
  have hBL : BoxLeading h k (1 / Qamb k) d :=
    ⟨fun i => inv_Qamb_le_ratioExp hk i,
      by simpa using multCount_le_card (ratioExp h k) (1 / Qamb k)⟩
  exact empCoeff_eq_zero_of_boxLeading_lt (η := η) (ζ := ζ) (h := h) (k := k) hk hBL hμ q

/-- The Mellin continuation is holomorphic on the strip off the lattice points. -/
theorem differentiableOn_mellinContinuation_emp (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) (U : ℝ) :
    DifferentiableOn ℂ
      (mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) U)
      {s : ℂ | (0 < s.re ∧ s.re < U) ∧ ∀ μ ∈ latticeBelow (Qamb k) U, s ≠ (μ : ℂ)} := by
  unfold mellinContinuation
  refine DifferentiableOn.add (fun s hs => ?_) ?_
  · exact (differentiableAt_mellin_cutoffRemainderFun (emp_cutoffExpansion hη hζ hk)
      (locallyIntegrableOn_empIntegral hη hζ) (empIntegral_isBigO_one_zero hη hζ) hs.1.1
      hs.1.2).differentiableWithinAt
  · unfold principalParts
    refine differentiableOn_finset_sum' _ fun μ hμ => differentiableOn_finset_sum' _ fun q _ => ?_
    refine (differentiableOn_const _).mul ((differentiableOn_const _).div
      (((differentiableOn_const _).sub differentiableOn_id).pow _) fun s hs => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 fun hsμ => hs.2 μ hμ hsμ.symm)

/-- ★★ **The coupled face sum at the canonical depth is the Mellin continuation** of the empirical
integral on the strip `0 < Re s < L`, off the candidate poles and the lattice points. -/
theorem empZetaAtDepth_eq_mellinContinuation (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {s : ℂ} (hs0 : 0 < s.re) (hsL : s.re < L)
    (hpole : ¬ PoleAt (depthOf h k L) h k s)
    (hlat : ∀ μ ∈ latticeBelow (Qamb k) L, s ≠ (μ : ℂ)) :
    empZetaAtDepth (depthOf h k L) η ζ h k s =
      mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) L s := by
  set p := depthOf h k L with hp
  have hp0 : ∀ i, 0 < p i := depthOf_pos hk hL
  set P : Set ℂ := {t | PoleAt p h k t} ∪ ((latticeBelow (Qamb k) L).image
    (fun μ : ℝ => (μ : ℂ)) : Set ℂ) with hP
  set U : Set ℂ := {t : ℂ | 0 < t.re ∧ t.re < L} \ P with hU
  have hPfin : P.Finite := (finite_poleSet p h k hk).union (Finset.finite_toSet _)
  have hUopen : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin.isClosed
  have hL1 : (1 : ℝ) ≤ L := by
    have : L₀ h ≤ L := hL
    unfold L₀ at this
    have := Nat.cast_le (α := ℝ) |>.2 this
    push_cast at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      (Nat.cast_nonneg (h i) : (0 : ℝ) ≤ h i)]
  have hUsub : ∀ t ∈ U, 0 < t.re ∧ FlatStrip p h k t ∧ ¬ PoleAt p h k t := fun t ht =>
    ⟨ht.1.1, flatStrip_depthOf_of_re_lt hk hL ht.1.2, fun hp => ht.2 (Or.inl hp)⟩
  have hUsub' : ∀ t ∈ U, (0 < t.re ∧ t.re < L) ∧
      ∀ μ ∈ latticeBelow (Qamb k) L, t ≠ (μ : ℂ) := fun t ht =>
    ⟨ht.1, fun μ hμ htμ => ht.2 (Or.inr (Finset.mem_coe.2
      (Finset.mem_image.2 ⟨μ, hμ, htμ.symm⟩)))⟩
  have hf : AnalyticOnNhd ℂ (empZetaAtDepth p η ζ h k) U :=
    ((differentiableOn_empZetaAtDepth hη hζ p hp0 h k).mono hUsub).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ
      (mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) L) U :=
    ((differentiableOn_mellinContinuation_emp hη hζ hk L).mono hUsub').analyticOnNhd hUopen
  have hconn : IsPreconnected U := isPreconnected_strip_diff_finite (by linarith) hPfin
  -- the seed point `1/(2Q)`
  have hQ : (0 : ℝ) < Qamb k := by exact_mod_cast Qamb_pos k hk
  set a : ℝ := 1 / Qamb k with ha
  have ha0 : 0 < a := by positivity
  have haL : a ≤ L := by
    rw [ha, div_le_iff₀ hQ]
    have : (1 : ℝ) ≤ Qamb k := by exact_mod_cast Qamb_pos k hk
    nlinarith
  have hz₀ : ((a / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨⟨by simp; linarith, by simp; linarith⟩, ?_⟩
    rintro (hp' | hp')
    · obtain ⟨i, hi⟩ := ratioExp_le_re_of_poleAt hk hp'
      have := inv_Qamb_le_ratioExp (h := h) hk i
      simp at hi
      linarith
    · obtain ⟨μ, hμ, hμeq⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp')
      have hμ' : μ = a / 2 := by exact_mod_cast hμeq
      obtain ⟨⟨m, hm⟩, _⟩ := (mem_latticeBelow_iff (Qamb_pos k hk)).1 hμ
      rw [hμ', ha] at hm
      field_simp at hm
      have : (2 * m : ℝ) = 1 := by linarith
      have h2 : (2 * m : ℕ) = 1 := by exact_mod_cast this
      omega
  -- the seed identity on the substrip `0 < Re s < a`
  have hfg : empZetaAtDepth p η ζ h k =ᶠ[𝓝 ((a / 2 : ℝ) : ℂ)]
      mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) L := by
    have hopen : IsOpen {t : ℂ | 0 < t.re ∧ t.re < a} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show ((a / 2 : ℝ) : ℂ) ∈ {t : ℂ | 0 < t.re ∧ t.re < a} from
      ⟨by simp; linarith, by simp; linarith⟩)] with t ht
    have hzs : ZetaStrip h k t := zetaStrip_of_re_lt_inv_Qamb hk ht.2
    rw [empZetaAtDepth_eq_mellin hη hζ p hp0 h k ht.1 hzs]
    exact mellin_eq_mellin_cutoffRemainderFun_add_principalParts (emp_cutoffExpansion hη hζ hk)
      (locallyIntegrableOn_empIntegral hη hζ) (empIntegral_isBigO_one_zero hη hζ) haL
      (fun μ _ q _ hc => not_lt.1 fun hμa => hc (empCoeff_eq_zero_of_lt_inv_Qamb hk hμa q))
      ht.1 ht.2
  have hsU : s ∈ U := by
    refine ⟨⟨hs0, hsL⟩, ?_⟩
    rintro (hp' | hp')
    · exact hpole hp'
    · obtain ⟨μ, hμ, hμeq⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp')
      exact hlat μ hμ hμeq.symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hz₀ hfg hsU

/-- ★ **Local form**: near every `0 < μ < L` the coupled face sum and the Mellin continuation
agree on a punctured neighbourhood. -/
theorem empZetaAtDepth_eventuallyEq_mellinContinuation (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ} (hμ0 : 0 < μ)
    (hμL : μ < L) :
    empZetaAtDepth (depthOf h k L) η ζ h k =ᶠ[𝓝[≠] (μ : ℂ)]
      mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) L := by
  set P : Set ℂ := {t | PoleAt (depthOf h k L) h k t} ∪ ((latticeBelow (Qamb k) L).image
    (fun μ : ℝ => (μ : ℂ)) : Set ℂ) with hP
  have hPfin : (P \ {(μ : ℂ)}).Finite :=
    ((finite_poleSet _ h k hk).union (Finset.finite_toSet _)).sdiff
  have hopen : IsOpen ({t : ℂ | 0 < t.re ∧ t.re < L} \ (P \ {(μ : ℂ)})) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin.isClosed
  have hmem : (μ : ℂ) ∈ {t : ℂ | 0 < t.re ∧ t.re < L} \ (P \ {(μ : ℂ)}) :=
    ⟨⟨by simpa using hμ0, by simpa using hμL⟩, fun hp => hp.2 rfl⟩
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin]
    with t ht htμ
  have htP : t ∉ P := fun hp => ht.2 ⟨hp, htμ⟩
  exact empZetaAtDepth_eq_mellinContinuation hη hζ hk hL ht.1.1 ht.1.2
    (fun hp => htP (Or.inl hp))
    (fun ν hν htν => htP (Or.inr (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ν, hν, htν.symm⟩))))

end Continuation

end Grammar
