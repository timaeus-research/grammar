You are Astra, consulted for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, Mathlib) of the paper "Grammar (Expectations and the Exceptional Divisor)" (Gerraty–Murfet). This is consult #144: CLOSURE AUDIT of your #143 priorities 2a and 2b, plus direction.

## What landed since #143 (main e5ea478, 818 modules, all axiom-clean [propext, Classical.choice, Quot.sound])

Priority 1 (CDXCII, already audited in #143 as accepted design): `resolvedCoeff_leading`.

Priority 2a (CDXCIII, file EmpiricalRectReplacement.lean): cube replacement rule. Exactly as you prescribed: deep-set dilation, population b-scaling law by expansion uniqueness (`smoothCoeff_eq_scaleCoeff_dilation`, reusable), population upper-degree vanishing from the resonant support theorem (`smoothCoeff_eq_zero_of_deep`), then the unit-box replacement rule; the rectangular collapse was NOT redone.

Priority 2b (CDXCIV, file EmpiricalResolvedStratumFormula.lean): the resolved graded formula as a branchwise weighted stratum sum, `resolvedCoeff_eq_empStratumSum`, plus `resolvedCoeff_eq_zero_of_deep`.

ONE DESIGN CHANGE you should audit: the deep-vanishing hypothesis of the graded empirical formulas (CDLXXXVII: `empCoeff_eq_faceSum_top`, `empCoeff_top_eq_smoothCoeff`, `empCoeff_eq_zero_of_deep`) was WEAKENED from `∀ᶠ v in 𝓝ˢ (deepSet d 1 c), η v = 0` to
  `DeepVanishing η b c := ∀ v ∈ deepSet d b c, ∀ᶠ w in 𝓝 v, w ∈ closedBox d b → η w = 0`
(vanishing near every deep point WITHIN the closed box). Reason: the chart amplitude `Ξ.G Y i` is an arbitrary smooth extension of the localised amplitude `Gloc` off the chart box (`G_eq` holds only on `centeredBox`), so nhdsSet-eventual vanishing of the piece amplitude is not derivable, while in-box vanishing follows from `Gloc_eventually_zero_deep` (F vanishing near D_{c+1} ⇒ Gloc vanishes near the chart point of a deep face point) pulled back along the continuous `facePt`. The jets then vanish by the one-sided lemma `pdMulti_eq_zero_of_eqOn_inter_closedBox` (already used in the population programme). The old hypothesis implies the new (`DeepVanishing.of_eventually`).

## The two new files (complete)

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFaceSumCollapse
import Grammar.EmpiricalBoxScaling

/-!
# The replacement rule on a general cube (§20, consult #143 priority 2a)

The graded empirical formula of `EmpiricalFaceSumCollapse` is stated on the unit box. On the cube
`(0,b]^d` it follows by the exact dilation `v = b u`, without repeating the face analysis: the deep
set of the cube is the dilated deep set of the unit box (`mapsTo_diag_deepSet`,
`DeepVanishing.diag`), the POPULATION coefficients obey the same scaling law as the
empirical ones (`smoothIntegral_eq_dilation`, ★ `smoothCoeff_eq_scaleCoeff_dilation`, by uniqueness
of cutoff expansions), the coefficients of log degree `≥ c` of a deep-vanishing amplitude vanish on
both sides (`smoothCoeff_eq_zero_of_deep`, from the population support theorem), so at the top
power the log mixing of the dilation disappears and
★★★ `empCoeffRect_top_eq_smoothCoeff`:
`empCoeffRect η ζ h k b μ (c−1) = smoothCoeff (η S_μ(ζ)/Γ(μ)) h k 1 b μ (c−1)`
for `η` vanishing near the deep set of the cube — the replacement rule `∂^α A ↦ ∂^α[A S_μ(ζ)]/Γ(μ)`
on every chart cube.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Dilation of the deep set -/

theorem mapsTo_diag_deepSet {b : ℝ} (hb : 0 < b) (c : ℕ) :
    MapsTo (diag (fun _ : Fin d => b)) (deepSet d 1 c) (deepSet d b c) := by
  intro v hv
  obtain ⟨hvbox, hcard⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [mem_closedBox] at hvbox ⊢
    intro i
    have := hvbox i
    simp only [diag]
    exact ⟨mul_nonneg hb.le this.1, by nlinarith [this.2]⟩
  · refine hcard.trans (Finset.card_le_card fun i hi => ?_)
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [diag, hi.2, mul_zero]

theorem diag_mem_closedBox {b : ℝ} (hb : 0 < b) {u : Fin d → ℝ} (hu : u ∈ closedBox d 1) :
    diag (fun _ : Fin d => b) u ∈ closedBox d b := by
  rw [mem_closedBox] at hu ⊢
  intro i
  exact ⟨mul_nonneg hb.le (hu i).1, mul_le_of_le_one_right hb.le (hu i).2⟩

/-- Deep vanishing on the cube dilates to deep vanishing on the unit box. -/
theorem DeepVanishing.diag {η : (Fin d → ℝ) → ℝ} {b : ℝ} (hb : 0 < b) {c : ℕ}
    (h : DeepVanishing η b c) : DeepVanishing (η ∘ diag (fun _ : Fin d => b)) 1 c := by
  intro v hv
  have h1 := ((contDiff_diag (fun _ : Fin d => b)).continuous.tendsto v).eventually
    (h _ (mapsTo_diag_deepSet hb c hv))
  exact h1.mono fun u hu hub => hu (diag_mem_closedBox hb hub)

/-! ### The population scaling law -/

/-- The population cube integral is the dilated unit-box integral. -/
theorem smoothIntegral_eq_dilation (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β : ℝ) {b : ℝ}
    (hb : 0 < b) (N : ℝ) :
    smoothIntegral F h k β b N =
      ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        smoothIntegral (F ∘ diag (fun _ : Fin d => b)) h k β 1
          (mono (fun i => 2 * k i) (fun _ : Fin d => b) * N) := by
  unfold smoothIntegral
  rw [← rect_const, integral_rect_eq _ (fun _ => hb), mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) 1) fun u _ => ?_
  rw [mono_diag, mono_diag]
  simp only [Function.comp_apply]
  ring_nf

variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★ **The dilation acts on the canonical population coefficients by the scaling law**:
`smoothCoeff F h k β b = A_b · scaleCoeff (d−1) B_b (smoothCoeff (F ∘ b) h k β 1)`. -/
theorem smoothCoeff_eq_scaleCoeff_dilation (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff F h k β b μ q =
      ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        scaleCoeff (d - 1) (mono (fun i => 2 * k i) (fun _ : Fin d => b))
          (smoothCoeff (F ∘ diag (fun _ : Fin d => b)) h k β 1) μ q := by
  have hQ := Qamb_pos k hk
  have hB : 0 < mono (fun i => 2 * k i) (fun _ : Fin d => b) := mono_pos _ fun _ => hb
  have hFD : ContDiff ℝ ∞ (F ∘ diag (fun _ : Fin d => b)) := hF.comp (contDiff_diag _)
  have h1 : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b)
      (fun μ j => ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        scaleCoeff (d - 1) (mono (fun i => 2 * k i) (fun _ : Fin d => b))
          (smoothCoeff (F ∘ diag (fun _ : Fin d => b)) h k β 1) μ j) := by
    have hexp := CutoffExpansion.const_mul ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b))
      (CutoffExpansion.comp_mul_pos (smooth_cutoffExpansion hFD hk hβ one_pos (h := h)) hB)
    have hfun : (fun N => ((∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)) *
        smoothIntegral (F ∘ diag (fun _ : Fin d => b)) h k β 1
          (mono (fun i => 2 * k i) (fun _ : Fin d => b) * N)) = smoothIntegral F h k β b :=
      funext fun N => (smoothIntegral_eq_dilation F h k β hb N).symm
    rwa [hfun] at hexp
  by_cases hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · by_cases hq : q ≤ d - 1
    · exact CutoffExpansion.coeff_unique hQ (smooth_cutoffExpansion hF hk hβ hb) h1 hμ hq
    · have hq' := not_le.1 hq
      rw [smoothCoeff_eq_zero_of_degree_gt hq', scaleCoeff_eq_zero_of_degree_gt hq', mul_zero]
  · have hμ' : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k := fun m hm => hμ ⟨m, hm⟩
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ' q,
      scaleCoeff_eq_zero_of_not_lattice (Q := Qamb k)
        (fun ν hν j => smoothCoeff_eq_zero_of_not_lattice hk hβ one_pos hν j) hμ' q, mul_zero]

/-! ### Upper-degree vanishing for deep-vanishing population amplitudes -/

theorem resonantCount_le_card (k e : Fin d → ℕ) (μ : ℝ) (J : Finset (Fin d)) :
    resonantCount (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) μ ≤ J.card := by
  unfold resonantCount
  exact (Finset.card_le_univ _).trans (card_subtype_inJ J).le

/-- The population coefficients of log degree `≥ c` of an amplitude with vanishing jets on the deep
set `{≥ c+1 vanishing coordinates}` vanish. -/
theorem smoothCoeff_eq_zero_of_deep (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) {c : ℕ} (hdeep : JetsZeroOn F (deepSet d b c)) (μ : ℝ) {q : ℕ}
    (hq : c ≤ q) : smoothCoeff F h k β b μ q = 0 := by
  refine smoothCoeff_eq_zero_of_resonant hF h k hk hβ hb μ q fun J hJ v hv hvJ α => ?_
  have hcard : c + 1 ≤ J.card :=
    (Nat.succ_le_succ hq).trans (hJ.trans (resonantCount_le_card _ _ μ J))
  exact hdeep α v (mem_deepSet_of_zeros hv hcard hvJ)

/-! ### The replacement rule on the cube -/

variable {η ζ : (Fin d → ℝ) → ℝ}

/-- ★ **Vanishing above the depth on the cube**: for `η` vanishing near the deep set of the cube,
the empirical cube coefficients of log degree `≥ c` vanish. -/
theorem empCoeffRect_eq_zero_of_deep (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b : ℝ}
    (hb : 0 < b) {c : ℕ} (hdeep : DeepVanishing η b c) (μ : ℝ) {q : ℕ} (hq : c ≤ q) :
    empCoeffRect η ζ h k (fun _ => b) μ q = 0 := by
  unfold empCoeffRect scaleCoeff
  rw [Finset.sum_eq_zero fun j hj => ?_, mul_zero, mul_zero]
  have hjc : c ≤ j := hq.trans (Finset.mem_Ico.1 hj).1
  rw [empCoeff_eq_zero_of_deep (hη.comp (contDiff_diag _)) (hζ.comp (contDiff_diag _))
    (hdeep.diag hb) hjc, zero_mul, zero_mul]

/-- ★★★ **The replacement rule on a general cube**: for `η` vanishing near the deep set of
`(0,b]^d`, the empirical top coefficient of the cube integral is the population coefficient, on the
same cube, of the amplitude `η · S_μ(ζ)/Γ(μ)`. -/
theorem empCoeffRect_top_eq_smoothCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hdeep : DeepVanishing η b c) :
    empCoeffRect η ζ h k (fun _ => b) μ (c - 1) =
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) h k 1 b μ (c - 1) := by
  have hB : 0 < mono (fun i => 2 * k i) (fun _ : Fin d => b) := mono_pos _ fun _ => hb
  set A : ℝ := (∏ _i : Fin d, b) * mono h (fun _ : Fin d => b) with hA
  set B : ℝ := mono (fun i => 2 * k i) (fun _ : Fin d => b) with hBdef
  have hηD : ContDiff ℝ ∞ (η ∘ diag (fun _ : Fin d => b)) := hη.comp (contDiff_diag _)
  have hζD : ContDiff ℝ ∞ (ζ ∘ diag (fun _ : Fin d => b)) := hζ.comp (contDiff_diag _)
  have hdeep1 := hdeep.diag hb
  -- the population amplitude and its dilation
  set G : (Fin d → ℝ) → ℝ := fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ with hG
  have hGc : ContDiff ℝ ∞ G := (contDiff_mul_fluctuation hη hζ hμ).div_const _
  have hGD : G ∘ diag (fun _ : Fin d => b) = fun v => (η ∘ diag (fun _ : Fin d => b)) v *
      fluctuation 1 μ ((ζ ∘ diag (fun _ : Fin d => b)) v) / Real.Gamma μ := rfl
  have hGDdeep : JetsZeroOn (G ∘ diag (fun _ : Fin d => b)) (deepSet d 1 c) :=
    jetsZeroOn_of_deepVanishing (hGc.comp (contDiff_diag _)) one_pos
      (hdeep1.mono_fun fun v hv => by rw [hGD]; simp only [hv, zero_mul, zero_div])
  by_cases hcd : c - 1 ≤ d - 1
  · -- the empirical side: only `j = c − 1` survives in the scaling law
    have hL : empCoeffRect η ζ h k (fun _ => b) μ (c - 1) =
        A * (B ^ (-μ) * empCoeff (η ∘ diag (fun _ : Fin d => b)) (ζ ∘ diag (fun _ : Fin d => b))
          h k μ (c - 1)) := by
      unfold empCoeffRect scaleCoeff
      rw [Finset.sum_eq_single (c - 1)]
      · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
      · intro j hj hne
        have hjc : c ≤ j := by
          have := (Finset.mem_Ico.1 hj).1
          omega
        rw [empCoeff_eq_zero_of_deep hηD hζD hdeep1 hjc, zero_mul, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) hnot
    -- the population side: the same collapse
    have hR : smoothCoeff G h k 1 b μ (c - 1) =
        A * (B ^ (-μ) * smoothCoeff (G ∘ diag (fun _ : Fin d => b)) h k 1 1 μ (c - 1)) := by
      rw [smoothCoeff_eq_scaleCoeff_dilation hGc hk one_pos hb]
      unfold scaleCoeff
      rw [Finset.sum_eq_single (c - 1)]
      · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
      · intro j hj hne
        have hjc : c ≤ j := by
          have := (Finset.mem_Ico.1 hj).1
          omega
        rw [smoothCoeff_eq_zero_of_deep (hGc.comp (contDiff_diag _)) hk one_pos one_pos hGDdeep μ
          hjc, zero_mul, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) hnot
    rw [hL, hR, empCoeff_top_eq_smoothCoeff hηD hζD hk hμ hc hdeep1, hGD]
  · -- log degree beyond the dimension: both sides vanish
    have hgt : d - 1 < c - 1 := not_le.1 hcd
    unfold empCoeffRect
    rw [scaleCoeff_eq_zero_of_degree_gt hgt, mul_zero, smoothCoeff_eq_zero_of_degree_gt hgt]

end SmoothEngine

end Grammar
```

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalResolvedExpansion
import Grammar.EmpiricalRectReplacement
import Grammar.SmoothResolvedStratumFormula

/-!
# The resolved graded empirical formula (§20, consult #143 priority 2b)

For a smooth root field `ξ` and an observable `F` vanishing near the deep zero fibre
`D_{c+1} = Z₀ ∩ {depth ≥ c+1}`, the coefficient of the resolved empirical expansion at the top
logarithmic power `(μ, c − 1)` is the **branchwise weighted stratum sum** (★★★
`resolvedCoeff_eq_empStratumSum`): over the pieces `p` and the base points `s`, the population
stratum term of the piece with the amplitude replaced by
`amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)` — the replacement rule `∂^α A ↦ ∂^α[A S_μ(ζ)]/Γ(μ)`
applied branch by branch (`pieceCoeff_top_eq_smoothCoeff`), where `ζ = Lψ_p ∘ Tm_{p,s}` is the
smooth branch representative of the field on the piece. The inputs are the cube replacement rule
(`empCoeffRect_top_eq_smoothCoeff`) and the deep vanishing of the chart amplitudes within the
piece boxes (`deepVanishing_amp`, from `Gloc_eventually_zero_deep`). Above the depth the
coefficients vanish (`resolvedCoeff_eq_zero_of_deep`), so the formula describes the expansion on
`𝓘_{c+1}/𝓘_c` branchwise. Non-claim: the sum is NOT asserted to be the population coefficient of
a globally defined amplitude on the resolved manifold — the branch representatives need not
descend across the walls (consult #143). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Deep vanishing of the chart amplitudes -/

/-- ★ **The piece amplitude vanishes near the deep set of the piece box, within the box**, when
`F` vanishes near the deep zero fibre. -/
theorem deepVanishing_amp {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    DeepVanishing ((Ξ.amp Y p).amp s) (Y.T.a p.1) c := by
  intro v hv
  obtain ⟨hvbox, hcard⟩ := hv
  have hvJ : ∀ i ∈ (univ : Finset (Fin ((Ξ.X Y).da p))).filter (fun i => v i = 0), v i = 0 :=
    fun i hi => (mem_filter.1 hi).2
  have h1 := ((Ξ.continuous_facePt Y p s).tendsto v).eventually
    (Ξ.Gloc_eventually_zero_deep Y hF p s _ hcard hvbox hvJ)
  refine h1.mono fun w hw hwbox => ?_
  rw [Ξ.amp_apply, Ξ.G_eq Y p.1 (Ξ.facePt_mem_box Y p s hwbox)]
  exact hw

namespace SmoothRootField

variable {Ξ Y} (ξ : Ξ.SmoothRootField Y)

/-- The smooth branch representative of the field on a piece, at a base point. -/
theorem contDiff_branch (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ContDiff ℝ ∞ fun v => ξ.Lψ p ((Ξ.X Y).Tm p s v) :=
  (ξ.Lψ_smooth p).comp (contDiff_affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s))

/-- The replaced amplitude of a piece: `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)`. -/
noncomputable def replacedAmp (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) : (Fin ((Ξ.X Y).da p) → ℝ) → ℝ :=
  fun v => (Ξ.amp Y p).amp s v * fluctuation 1 μ (ξ.Lψ p ((Ξ.X Y).Tm p s v)) / Real.Gamma μ

theorem contDiff_replacedAmp (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {μ : ℝ} (hμ : 0 < μ) : ContDiff ℝ ∞ (ξ.replacedAmp p s μ) :=
  (contDiff_mul_fluctuation ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s) hμ).div_const _

theorem jetsZeroOn_replacedAmp {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {μ : ℝ} (hμ : 0 < μ) :
    JetsZeroOn (ξ.replacedAmp p s μ) (deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) :=
  jetsZeroOn_of_deepVanishing (ξ.contDiff_replacedAmp p s hμ) (Y.T.a_pos p.1)
    ((Ξ.deepVanishing_amp Y hF p s).mono_fun fun v hv => by
      simp only [replacedAmp, hv, zero_mul, zero_div])

/-! ### The branchwise replacement rule -/

/-- ★★ **The branchwise replacement rule**: the piece coefficient at the top power is the base
integral of the population cube coefficient of the replaced amplitude. -/
theorem pieceCoeff_top_eq_smoothCoeff {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) (p : (Ξ.X Y).PIdx) :
    ξ.pieceCoeff p μ (c - 1) =
      ∫ s, smoothCoeff (ξ.replacedAmp p s μ) ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) 1 (Y.T.a p.1) μ (c - 1)
        ∂(Ξ.piecePresentation Y p).ν := by
  unfold pieceCoeff
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact empCoeffRect_top_eq_smoothCoeff ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s)
    ((Ξ.X Y).kA_pos p) (Y.T.a_pos p.1) hμ hc (Ξ.deepVanishing_amp Y hF p s)

/-- ★ **Vanishing above the depth**: the resolved empirical coefficients of log degree `≥ c`
vanish for observables vanishing near `D_{c+1}`. -/
theorem resolvedCoeff_eq_zero_of_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (μ : ℝ) {q : ℕ} (hq : c ≤ q) : ξ.resolvedCoeff μ q = 0 := by
  unfold resolvedCoeff pieceCoeff
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)]
  exact empCoeffRect_eq_zero_of_deep ((Ξ.amp Y p).smooth s) (ξ.contDiff_branch p s)
    (Y.T.a_pos p.1) (Ξ.deepVanishing_amp Y hF p s) μ hq

/-! ### The branchwise weighted stratum sum -/

/-- The empirical stratum term of a piece at a base point: the population stratum term
(`pieceStratumSum`) with the amplitude replaced by `amp · S_μ(ζ)/Γ(μ)`. -/
noncomputable def empPieceStratumSum (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter (fun J => J.card = c),
    faceW J (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) *
      (faceCoef ((Ξ.X Y).kA p) 1 (Y.T.a p.1) J
          (fun i => resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i + (Ξ.X Y).hA p i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) (lJ J)
            (ξ.replacedAmp p s μ) (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => 2 * (Ξ.X Y).kA p i)
          (Y.T.a p.1) μ 0)

/-- The branchwise weighted stratum sum: the empirical stratum terms integrated over the bases
and summed over the pieces. -/
noncomputable def empStratumSum (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ p, ∫ s, ξ.empPieceStratumSum p s μ c ∂(Ξ.piecePresentation Y p).ν

/-- ★★★ **The resolved graded empirical formula**: for an observable vanishing near the deep zero
fibre `D_{c+1}`, the resolved empirical coefficient at `(μ, c − 1)` is the branchwise weighted
stratum sum with the amplitudes `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s})/Γ(μ)`. -/
theorem resolvedCoeff_eq_empStratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    ξ.resolvedCoeff μ (c - 1) = ξ.empStratumSum μ c := by
  unfold resolvedCoeff empStratumSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ξ.pieceCoeff_top_eq_smoothCoeff hc hF hμ p]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact smoothCoeff_eq_faceSum_top (ξ.contDiff_replacedAmp p s hμ) _ _ ((Ξ.X Y).kA_pos p) one_pos
    (Y.T.a_pos p.1) μ hc (ξ.jetsZeroOn_replacedAmp hF p s hμ)

end SmoothRootField

end ResolvedData

end SmoothEngine

end Grammar
```

## Definitions referenced (for the audit)
- `empCoeffRect η ζ h k b μ q := ((∏ b) * mono h b) * scaleCoeff (d−1) (mono 2k b) (empCoeff (η∘diag b) (ζ∘diag b) h k) μ q`, with `scaleCoeff D β c μ q := β^(−μ) * Σ_{j ∈ Ico q (D+1)} c μ j * C(j,q) * (log β)^(j−q)`; `empRect_cutoffExpansion` and `empCoeffRect_unique` make these the canonical coefficients of `∫_{(0,b]^d} η v^h exp(−N v^{2k} + √N v^k ζ) dv`.
- `smoothCoeff F h k β b μ q`: the canonical population coefficients of `∫_{(0,b]^d} F v^h exp(−β N v^{2k}) dv` (cutoff expansion on `Qamb k = 2∏k`-lattice, degree ≤ d−1).
- `smoothCoeff_eq_faceSum_top (hA) (h k) (hk) (hβ) (hb) (μ) (hc : 1 ≤ c) (hdeep : JetsZeroOn A (deepSet d b c)) : smoothCoeff A h k β b μ (c−1) = Σ_{|J|=c} faceW J (resOrder h k μ J) * (faceCoef k β b J (resOrder + h) μ (c−1) * faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w)) h_K (2k_K) b μ 0)` — the population graded stratum formula on a cube (CDXLVI), used piecewise in the population `coeff_eq_stratumSum`.
- `pieceCoeff p μ q := ∫ s, empCoeffRect (fun v => Ξ.G Y p.1 (affineMap (eqv p) p.2 (sc p s) v)) (fun v => ξ.Lψ p (affineMap …)) (hA p) (kA p) (fun _ => Y.T.a p.1) μ q ∂ν_p`; `resolvedCoeff μ q := Σ_p pieceCoeff p μ q`; `(Ξ.amp Y p).amp s v = Ξ.G Y p.1 (affineMap …)` and `Tm p s v = affineMap …` are rfl.
- `deepZeroFibre c = zeroFibre ∩ depthGE (c+1)` (compact), the population hypothesis class 𝓘_{c+1}.

## Paper text now in grammar_lean_2.tex §9 (new theorem)

\begin{thm}[The resolved graded empirical formula]
Let ψ be a bounded smooth root field with branch representatives L_p, let 1 ≤ c ≤ d, μ > 0, and let F vanish on a neighbourhood of the deep zero fibre D_{c+1}. Then C^emp_{μ,q}(F;ψ) = 0 for q ≥ c, and C^emp_{μ,c−1}(F;ψ) is the stratum sum of Theorem E taken branch by branch: over the pieces p and base points s, the sum over the exactly resonant faces of size c of the piece box of the face integrals of ∂^α_J[ a_{p,s} S_μ(L_p∘T_{p,s}) / Γ(μ) ](0_J, w), where a_{p,s} is the localised amplitude of the piece and L_p∘T_{p,s} the smooth branch representative of the field in the piece coordinates. Equivalently, each piece coefficient at (μ, c−1) is the base integral of the population cube coefficient of the replaced amplitude.
\end{thm}
Following text: "This is the replacement rule ∂^α_J a ↦ ∂^α_J[a S_μ(ψ̂)]/Γ(μ) on the resolved manifold … The sum is a branchwise formula: it is not asserted to be the population coefficient of a single amplitude on the resolved manifold, since the branch representatives are only required to be smooth piece by piece and need not agree across the walls." Non-claims section updated accordingly; the box graded theorem now says η vanishes near the deep set "within the box".

## Questions
1. AUDIT 2a/2b: are the statements what you intended? Check in particular (i) the hypothesis `hc : 1 ≤ c` and the degenerate case c−1 > d−1; (ii) the normalisation: `smoothCoeff … 1 b` (β = 1) on the cube with the SAME h, k, a = Y.T.a p.1 as the piece — is Γ(μ) placement right (the population `faceCoef` carries Γ(μ)β^{−μ}, so amp·S_μ/Γ(μ) gives the S_μ-weighted stratum integral as in the paper's leading formula)? (iii) `empPieceStratumSum` being literally the population `pieceStratumSum` with `replacedAmp` — any hidden mismatch with the `(Ξ.decomp Y).chart I` indexing used by the population stratumSum (piecePresentation (en I))?
2. The `DeepVanishing` weakening: correct and sufficient? Any consequence for the paper's phrasing of Theorem thm:empgraded (box) — is "vanishes near the deep set within the box" acceptable, or should the box theorem keep the stronger phrasing and the weakening be noted only as a Lean detail?
3. What is now the highest-value next unit for the paper? Candidates: (3) coefficient continuity under compact-uniform C^r convergence of branch representatives (your #143 item 3); the lower-log-weight identification `mellinMom (τ^r e^{aτ}) μ ℓ = (−1)^ℓ ∂_ν^ℓ S_ν(a)|_{ν=μ+r/2}` (currently only ℓ = 0 formalised); the random-field limit of subleading coefficients; or declaring §20 CLOSED for the paper and returning to consolidation (docs/paper only). Give a ranked recommendation with the reason, and for the top pick a concrete Lean-level design (statement shapes, which existing engine lemmas to reuse, pitfalls).
4. Anything in the paper paragraph above that over-claims or that you would phrase differently (short, concrete edits)?

Be concrete and terse; Lean statement shapes rather than prose where possible.
