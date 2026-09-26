/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalMellinContinuation

/-!
# The polar coefficients of the empirical Mellin transform (route B, unit B12)

At a real point `μ` in the flat strip the coupled face sum of unit B11 factorises face by face as
`faceW · resConst · (μ − s)^{−c} · empFaceHolo`, with
`empFaceHolo = regularFactor · coupledFaceZeta`
holomorphic near `μ` (the coupled face zeta functions are holomorphic on the positive flat strip).
The finite-family polar lemma of unit B7 therefore gives the *integrated polar coefficients*

  `empIntegratedPolarCoeff p η ζ h k μ q
     = Σ_{x : c_x ≥ q+1} faceW · resConst · (−1)^{c_x} · empFaceHolo_x^{(c_x−1−q)}(μ) / (c_x−1−q)!`

with `empZetaAtDepth − polarPart (d−1) (empIntegratedPolarCoeff …) μ = O(1)` on a punctured
neighbourhood of `μ`; since the coupled face sum agrees there with the library's Mellin continuation
(unit B11), the uniqueness theorem `polarCoeff_unique` identifies them with the polar data of the
empirical coefficients:

  ★★★ `empIntegratedPolarCoeff_eq_polarCoeff`:
    `empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q`
    `= (−1)^{q+1} q! · empCoeff η ζ h k μ q` for lattice points `0 < μ < L`, `q ≤ d − 1`,

i.e. the empirical coefficients of `N^{−μ} (log N)^q` in the expansion of the empirical chart
integral are, up to the sign-factorial normalisation, the Laurent coefficients at `μ` of the
meromorphic function
`Σ_x faceW · innerFactor_x(s) · ∫_0^∞ t^{s−1}e^{−t} chartZeta(faceAmp(η e^{√tζ}))(s) dt`.
This is the first completion milestone of route B: the coefficients defined through the real face
construction (`empCoeffAtDepth`) are recovered from a new, purely meromorphic calculation.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### The holomorphic face factors and the integrated polar coefficients -/

section Defs

variable (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)

/-- The holomorphic factor of a face at `μ`: the non-resonant part of the inner factor times the
coupled face zeta function. -/
noncomputable def empFaceHolo (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) (s : ℂ) : ℂ :=
  regularFactor h k J m μ s * coupledFaceZeta p η ζ h k J m s

/-- ★ **The integrated polar coefficients** (the coefficient of `(s − μ)^{−(q+1)}` of the coupled
face sum at `μ`). -/
noncomputable def empIntegratedPolarCoeff (μ : ℝ) (q : ℕ) : ℂ :=
  finiteFacePolarCoeff (SmoothEngine.faceIndex p)
    (fun x => ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ)
    (fun x => poleOrder h k x.1 x.2 μ) (fun x => empFaceHolo p η ζ h k x.1 x.2 μ) (μ : ℂ) q

/-- The coupled face sum with every inner factor factorised at `μ`. -/
theorem empZetaAtDepth_eq_faceHolo (μ : ℝ) (s : ℂ) :
    empZetaAtDepth p η ζ h k s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * empFaceHolo p η ζ h k x.1 x.2 μ s) := by
  unfold empZetaAtDepth empFaceHolo
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [innerFactor_eq_res h k x.1 x.2 μ s]
  ring

end Defs

/-! ### Holomorphy of the face factors near `μ` -/

section Holo

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The face factor is holomorphic on the positive part of the regular set of the face. -/
theorem differentiableOn_empFaceHolo (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) :
    DifferentiableOn ℂ (empFaceHolo p η ζ h k J m μ)
      ({s : ℂ | 0 < s.re} ∩ faceRegSet p h k J m μ) := by
  refine DifferentiableOn.mul ?_ ?_
  · exact (differentiableOn_regularFactor h k J m μ fun s hs => hs.2).mono fun s hs => hs.2
  · exact (differentiableOn_coupledFaceZeta hη hζ p hp0 h k J hm).mono fun s hs => ⟨hs.1, hs.2.1⟩

/-- The positive regular set of a face is a neighbourhood of `μ` once `0 < μ` lies in the flat
strip. -/
theorem posFaceRegSet_mem_nhds (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ : FlatStrip p h k (μ : ℂ)) :
    ({s : ℂ | 0 < s.re} ∩ faceRegSet p h k J m μ) ∈ 𝓝 (μ : ℂ) :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_faceRegSet p h k J m μ)).mem_nhds ⟨by simpa using hμ0, mem_faceRegSet p h k J m hμ⟩

end Holo

/-! ### The polar part of the coupled face sum -/

section Polar

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★★ **The coupled face sum minus its principal part is bounded near `μ`.** -/
theorem empZetaAtDepth_sub_polarPart_isBigO_one (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ0 : 0 < μ) (hμ : FlatStrip p h k (μ : ℂ)) :
    (fun s : ℂ => empZetaAtDepth p η ζ h k s -
      polarPart (d - 1) (empIntegratedPolarCoeff p η ζ h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have key := finiteFaceSum_sub_polarPart_isBigO_one (SmoothEngine.faceIndex p)
    (fun x => ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ)
    (fun x => poleOrder h k x.1 x.2 μ) (fun x => empFaceHolo p η ζ h k x.1 x.2 μ) (μ : ℂ)
    (fun x hx => ⟨_, posFaceRegSet_mem_nhds p x.1 x.2 hμ0 hμ,
      differentiableOn_empFaceHolo hη hζ p hp0 x.1 (Finset.mem_sigma.1 hx).2 μ⟩)
    (D := d - 1) (fun x _ => by have := poleOrder_le h k x.1 x.2 μ; omega)
  refine key.congr_left fun s => ?_
  rw [empZetaAtDepth_eq_faceHolo]
  rfl

/-- The Mellin continuation of the empirical integral minus the integrated principal part is
bounded near every `0 < μ < L`. -/
theorem mellinContinuation_emp_sub_polarPart_isBigO_one (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ} (hμ0 : 0 < μ) (hμL : μ < L) :
    (fun s : ℂ => mellinContinuation (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) L s -
      polarPart (d - 1) (empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have hev := empZetaAtDepth_eventuallyEq_mellinContinuation hη hζ hk hL hμ0 hμL
  refine (empZetaAtDepth_sub_polarPart_isBigO_one hη hζ _ (depthOf_pos hk hL) hμ0
    (flatStrip_depthOf hk hL hμL)).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hev] with s hs
  rw [hs]

/-- ★★★ **The integrated polar coefficients are the polar data of the empirical coefficients**:
for a lattice point `0 < μ < L` and `q ≤ d − 1`,
`empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q`. -/
theorem empIntegratedPolarCoeff_eq_polarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q :=
  polarCoeff_unique (emp_cutoffExpansion hη hζ hk) (locallyIntegrableOn_empIntegral hη hζ)
    (empIntegral_isBigO_one_zero hη hζ) hμlat hμL hμ0
    (mellinContinuation_emp_sub_polarPart_isBigO_one hη hζ hk hL hμ0 hμL) q hq

/-- ★★★ **The empirical all-log coefficients in integrated form**:
`empCoeff η ζ h k μ q = (−1)^{q+1}/q! · empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q`. -/
theorem ofReal_empCoeff_eq_empIntegratedPolarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    (empCoeff η ζ h k μ q : ℂ) =
      (-1) ^ (q + 1) * empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q / (q ! : ℂ) := by
  rw [empIntegratedPolarCoeff_eq_polarCoeff hη hζ hk hL hμlat hμL hμ0 hq]
  exact ofReal_coeff_eq_polarCoeff _ _ _

/-- The canonical cutoff `L = cutoffOf h μ`: for a positive lattice point `μ = m/Qamb k`. -/
theorem ofReal_empCoeff_eq_empIntegratedPolarCoeff_cutoff (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k)
    (hμ0 : 0 < μ) {q : ℕ} (hq : q ≤ d - 1) :
    (empCoeff η ζ h k μ q : ℂ) =
      (-1) ^ (q + 1) *
        empIntegratedPolarCoeff (depthOf h k (cutoffOf h μ)) η ζ h k μ q / (q ! : ℂ) :=
  ofReal_empCoeff_eq_empIntegratedPolarCoeff hη hζ hk (L₀_le_cutoffOf h μ)
    ((mem_latticeBelow_iff (Qamb_pos k hk)).2 ⟨hμ, lt_cutoffOf h μ⟩) (lt_cutoffOf h μ) hμ0 hq

end Polar

end Grammar
