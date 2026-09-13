/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetAssembly
import Monomialize.Transport.ProductSectorAtlasRescale

/-!
# Centred boxes: the general producer through the rescaled atlas (consult #112 H3)

The sheet-assembly producer (CCCLXXVII) asks for symmetric chart boxes `[−a,a]^d`. A domain-sector
atlas with CENTRED boxes `∏_j [−r_{ij}, r_{ij}]` is rescaled chart by chart onto `[−a,a]^d` by
`hironaka`'s `DomainSectorAtlas.rescale` (charts `φ_i ∘ D_i`, units multiplied by the scaling
constants, images and domain unchanged). This module transports the analytic inputs: a signed
packet on an enclosing symmetric box composes with the diagonal scaling
(`HolomorphicSignedBoxExtension.compDiag`) and absorbs a positive constant (`mulConst`), and the
inputs for a centred atlas (`CentredInputs`: units bounded below on the boxes, packets on
enclosing symmetric boxes `[−a'_i, a'_i]^d ⊇ dom i`) become sheet-assembly inputs for the rescaled
atlas (`CentredInputs.toSheetInputs`). ★★ `hasCoordFreeExpansion_of_centred`: the coordinate-free
expansion of `∫_W obs · prior · e^{−nK}` for every centred-box domain-sector atlas with the stated
inputs. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling WaterFilling

/-! ### Packets along a diagonal scaling -/

/-- The complex diagonal scaling `z ↦ (c_j z_j)_j`. -/
def diagℂ {d : ℕ} (c : Fin d → ℝ) (z : Fin d → ℂ) : Fin d → ℂ := fun j => (c j : ℂ) * z j

theorem differentiable_diagℂ {d : ℕ} (c : Fin d → ℝ) : Differentiable ℂ (diagℂ c) :=
  differentiable_pi.2 fun j => (differentiable_const _).mul (differentiable_apply j)

theorem complexify_diagL {d : ℕ} (c : Fin d → ℝ) (w : Fin d → ℝ) :
    complexify (diagL c w) = diagℂ c (complexify w) := by
  funext j
  rw [complexify_apply, diagL_apply, diagℂ, complexify_apply, Complex.ofReal_mul]

theorem diagL_mem_box {d : ℕ} {c : Fin d → ℝ} (hc : ∀ j, 0 < c j) {a a' : ℝ}
    (hca : ∀ j, c j * a ≤ a') {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc (-a) a)) :
    diagL c w ∈ piBox d (Icc (-a') a') := fun j _ => by
  have hb := hw j (mem_univ _)
  rw [mem_Icc] at hb ⊢
  rw [diagL_apply]
  constructor
  · have := mul_le_mul_of_nonneg_left hb.1 (hc j).le
    rw [mul_neg] at this
    linarith [hca j]
  · exact (mul_le_mul_of_nonneg_left hb.2 (hc j).le).trans (hca j)

/-- **A signed packet composed with a positive diagonal scaling**: from `[−a',a']^d` to
`[−a,a]^d` when `c_j a ≤ a'`. -/
def _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.compDiag {d : ℕ} {a' : ℝ}
    {ϕ φ : (Fin d → ℝ) → ℝ} (P : HolomorphicSignedBoxExtension a' ϕ φ) {c : Fin d → ℝ}
    (hc : ∀ j, 0 < c j) {a : ℝ} (hca : ∀ j, c j * a ≤ a') :
    HolomorphicSignedBoxExtension a (ϕ ∘ diagL c) (φ ∘ diagL c) where
  Ω := diagℂ c ⁻¹' P.Ω
  isOpen_Ω := P.isOpen_Ω.preimage (differentiable_diagℂ c).continuous
  box_subset := fun w hw => by
    rw [mem_preimage, ← complexify_diagL]
    exact P.box_subset _ (diagL_mem_box hc hca hw)
  Hϕ := P.Hϕ ∘ diagℂ c
  Hφ := P.Hφ ∘ diagℂ c
  holϕ := P.holϕ.comp (differentiable_diagℂ c).differentiableOn fun _ hz => hz
  holφ := P.holφ.comp (differentiable_diagℂ c).differentiableOn fun _ hz => hz
  eqϕ := fun w hw => by
    rw [mem_preimage, ← complexify_diagL] at hw
    change ϕ (diagL c w) = (P.Hϕ (diagℂ c (complexify w))).re
    rw [← complexify_diagL]
    exact P.eqϕ _ hw
  eqφ := fun w hw => by
    rw [mem_preimage, ← complexify_diagL] at hw
    change φ (diagL c w) = (P.Hφ (diagℂ c (complexify w))).re
    rw [← complexify_diagL]
    exact P.eqφ _ hw

/-- **A signed packet with the prior multiplied by a real constant.** -/
def _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.mulConst {d : ℕ} {a : ℝ}
    {ϕ φ : (Fin d → ℝ) → ℝ} (P : HolomorphicSignedBoxExtension a ϕ φ) (C : ℝ) :
    HolomorphicSignedBoxExtension a (fun w => C * ϕ w) φ where
  Ω := P.Ω
  isOpen_Ω := P.isOpen_Ω
  box_subset := P.box_subset
  Hϕ := fun z => (C : ℂ) * P.Hϕ z
  Hφ := P.Hφ
  holϕ := (differentiableOn_const _).mul P.holϕ
  holφ := P.holφ
  eqϕ := fun w hw => by rw [Complex.re_ofReal_mul, P.eqϕ w hw]
  eqφ := P.eqφ

/-! ### Inputs for a centred atlas -/

/-- The inputs of the sheet assembly for a domain-sector atlas with CENTRED boxes: units bounded
below on the boxes, packets on enclosing symmetric boxes `[−a'_i, a'_i]^d ⊇ dom i`. -/
structure CentredInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  K_m : Measurable K
  /-- the resolved set of the atlas -/
  Ω : Set (Fin d → ℝ)
  /-- the domain-sector atlas -/
  A : DomainSectorAtlas d K Ω
  centred : A.toProductSectorAtlas.IsCentred
  /-- the half side of the common box -/
  a : ℝ
  ha : 0 < a
  /-- the half sides of the enclosing symmetric boxes of the charts -/
  a' : A.ι → ℝ
  hi_le : ∀ i j, A.hi i j ≤ a' i
  φ_m : ∀ i, Measurable (A.φ i)
  jacUnit_m : ∀ i, Measurable (A.jacUnit i)
  hu_cont : ∀ i, Continuous (A.phaseUnit i)
  hu_tan : ∀ i (w w' : Fin d → ℝ), (∀ j, ¬ 0 < A.k i j → w j = w' j) →
    A.phaseUnit i w = A.phaseUnit i w'
  /-- the lower bounds of the units on the boxes -/
  c : A.ι → ℝ
  hc : ∀ i, 0 < c i
  hu_lb : ∀ i, ∀ w ∈ A.dom i, c i ≤ A.phaseUnit i w
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  prior_m : Measurable prior
  prior_nonneg : ∀ w, 0 ≤ prior w
  obs_m : Measurable obs
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  /-- the packets of the charts, on the enclosing symmetric boxes -/
  P : ∀ i, HolomorphicSignedBoxExtension (a' i) (fun v => |A.jacUnit i v| * prior (A.φ i v))
    (obs ∘ A.φ i)
  signs_nonempty : ∀ i, (A.signs i).Nonempty
  ι_nonempty : Nonempty A.ι

namespace CentredInputs

variable {d : ℕ} (Y : CentredInputs d)

/-- The rescaled atlas. -/
noncomputable abbrev R : DomainSectorAtlas d Y.K Y.Ω := Y.A.rescale Y.centred Y.ha

/-- The scaling factors of chart `i`. -/
noncomputable abbrev sc (i : Y.A.ι) : Fin d → ℝ := Y.A.toProductSectorAtlas.scaleC Y.a i

theorem sc_pos (i : Y.A.ι) (j : Fin d) : 0 < Y.sc i j :=
  ProductSectorAtlas.scaleC_pos Y.centred Y.ha i j

theorem sc_mul_le (i : Y.A.ι) (j : Fin d) : Y.sc i j * Y.a ≤ Y.a' i := by
  change Y.A.hi i j / Y.a * Y.a ≤ Y.a' i
  rw [div_mul_cancel₀ _ Y.ha.ne']
  exact Y.hi_le i j

/-- The Jacobian scaling constant of chart `i`. -/
noncomputable def jacC (i : Y.A.ι) : ℝ := (∏ j, Y.sc i j ^ Y.A.h i j) * ∏ j, Y.sc i j

theorem jacC_pos (i : Y.A.ι) : 0 < Y.jacC i :=
  mul_pos (Finset.prod_pos fun j _ => pow_pos (Y.sc_pos i j) _)
    (Finset.prod_pos fun j _ => Y.sc_pos i j)

/-- The phase scaling constant of chart `i`. -/
noncomputable def phC (i : Y.A.ι) : ℝ := ∏ j, Y.sc i j ^ (2 * Y.A.k i j)

theorem phC_pos (i : Y.A.ι) : 0 < Y.phC i := Finset.prod_pos fun j _ => pow_pos (Y.sc_pos i j) _

theorem R_jacUnit (i : Y.A.ι) (v : Fin d → ℝ) :
    Y.R.jacUnit i v = Y.A.jacUnit i (diagL (Y.sc i) v) * Y.jacC i := by
  change Y.A.jacUnit i (diagL (Y.sc i) v) * (∏ j, Y.sc i j ^ Y.A.h i j) * ∏ j, Y.sc i j = _
  rw [jacC, mul_assoc]

theorem R_phaseUnit (i : Y.A.ι) (v : Fin d → ℝ) :
    Y.R.phaseUnit i v = Y.A.phaseUnit i (diagL (Y.sc i) v) * Y.phC i := rfl

theorem R_φ (i : Y.A.ι) : Y.R.φ i = Y.A.φ i ∘ diagL (Y.sc i) := rfl

theorem R_k : Y.R.k = Y.A.k := rfl

/-- The rescaled prior factor is the scaled packet's prior. -/
theorem priorFactor_eq (i : Y.A.ι) :
    (fun v => |Y.R.jacUnit i v| * Y.prior (Y.R.φ i v)) = fun v =>
      Y.jacC i * ((fun v => |Y.A.jacUnit i v| * Y.prior (Y.A.φ i v)) ∘ diagL (Y.sc i)) v := by
  funext v
  change |Y.R.jacUnit i v| * Y.prior (Y.A.φ i (diagL (Y.sc i) v)) =
    Y.jacC i * (|Y.A.jacUnit i (diagL (Y.sc i) v)| * Y.prior (Y.A.φ i (diagL (Y.sc i) v)))
  rw [R_jacUnit, abs_mul, abs_of_pos (Y.jacC_pos i)]
  ring

/-- ★★ **The sheet-assembly inputs of the rescaled atlas.** -/
noncomputable def toSheetInputs : SheetInputs d where
  K := Y.K
  K_m := Y.K_m
  Ω := Y.Ω
  A := Y.R
  a := Y.a
  ha := Y.ha
  lo_eq _ _ := rfl
  hi_eq _ _ := rfl
  φ_m i := (Y.φ_m i).comp (diagL (Y.sc i)).continuous.measurable
  jacUnit_m i := by
    have : Y.R.jacUnit i = fun v => Y.A.jacUnit i (diagL (Y.sc i) v) * Y.jacC i :=
      funext fun v => Y.R_jacUnit i v
    rw [this]
    exact ((Y.jacUnit_m i).comp (diagL (Y.sc i)).continuous.measurable).mul measurable_const
  hu_cont i := by
    change Continuous fun v => Y.A.phaseUnit i (diagL (Y.sc i) v) * Y.phC i
    exact ((Y.hu_cont i).comp (diagL (Y.sc i)).continuous).mul continuous_const
  hu_tan i w w' h := by
    change Y.A.phaseUnit i (diagL (Y.sc i) w) * Y.phC i =
      Y.A.phaseUnit i (diagL (Y.sc i) w') * Y.phC i
    congr 1
    exact Y.hu_tan i _ _ fun j hj => by rw [diagL_apply, diagL_apply, h j hj]
  c i := Y.c i * Y.phC i
  hc i := mul_pos (Y.hc i) (Y.phC_pos i)
  hu_lb i w hw := by
    change Y.c i * Y.phC i ≤ Y.A.phaseUnit i (diagL (Y.sc i) w) * Y.phC i
    refine mul_le_mul_of_nonneg_right ?_ (Y.phC_pos i).le
    refine Y.hu_lb i _ (ProductSectorAtlas.diag_mem_dom Y.centred Y.ha i ?_)
    intro j
    have := hw j (mem_univ _)
    rw [mem_Icc] at this
    exact abs_le.2 this
  prior := Y.prior
  obs := Y.obs
  prior_m := Y.prior_m
  prior_nonneg := Y.prior_nonneg
  obs_m := Y.obs_m
  obs_int := Y.obs_int
  P i := (((Y.P i).compDiag (Y.sc_pos i) (Y.sc_mul_le i)).mulConst (Y.jacC i)).congr
    (Y.priorFactor_eq i) rfl
  signs_nonempty := Y.signs_nonempty
  ι_nonempty := Y.ι_nonempty

theorem toSheetInputs_W : Y.toSheetInputs.A.W = Y.A.W := rfl

/-- ★★ **The coordinate-free expansion for a centred-box domain-sector atlas**: the general
producer applied to the rescaled atlas. -/
theorem hasCoordFreeExpansion :
    (Sheet.normalData Y.toSheetInputs.SA).HasCoordFreeExpansion
      Y.toSheetInputs.cert.stratumMeasure Y.toSheetInputs.coeffCert.field
      (spectrumLe (commonQ Y.toSheetInputs.cert.cores.k) (commonD Y.toSheetInputs.cert.n))
      Y.A.W Y.K Y.prior Y.obs :=
  Y.toSheetInputs.hasCoordFreeExpansion

end CentredInputs

/-- ★★ **Existence form for centred atlases.** -/
theorem hasCoordFreeExpansion_of_centred {d : ℕ} (Y : CentredInputs d) :
    ∃ (C : ResolvedCertificate (Sheet.geometry Y.toSheetInputs.SA)
        (Sheet.normalData Y.toSheetInputs.SA) Y.A.W Y.K Y.prior Y.obs)
      (Cc : C.CoefficientCertificate),
      (Sheet.normalData Y.toSheetInputs.SA).HasCoordFreeExpansion C.stratumMeasure Cc.field
        (spectrumLe (commonQ C.cores.k) (commonD C.n)) Y.A.W Y.K Y.prior Y.obs :=
  ⟨_, _, Y.hasCoordFreeExpansion⟩

end SheetAssembly

end Grammar
