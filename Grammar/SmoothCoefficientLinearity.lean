/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetProducer

/-!
# Linearity of the smooth expansion coefficients (consult #117 §8, optional refinement)

Certificates add and scale: `SmoothExpansionCertificate.add` (common lattice `Q₁Q₂`, degree
`max D₁ D₂`, by lattice refinement and degree padding) and `.smul`. Combined with presentation
independence (`coeff_eq`) this makes the intrinsic scalar coefficients of the smooth producer
LINEAR IN THE OBSERVABLE: for smooth sheet inputs with the same domain, phase and prior,
★★ `SmoothSheetInputs.coeff_add` (`obs = f + g ⇒ c = c_f + c_g`), ★ `coeff_smul`, `coeff_zero`.
The observable is only used for `N ≥ 0`, where the integrands are integrable
(`LocalisationData.integrable_integrand`); the expansions are eventual statements.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Grammar

/-! ### Scaling a cutoff expansion -/

theorem absSpectralSum_const_mul (Q D : ℕ) (r : ℝ) (c : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => r * c μ j) L N = r * absSpectralSum Q D c L N := by
  unfold absSpectralSum
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun j _ => by ring

theorem CutoffExpansion.const_mul {Q D : ℕ} {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} (r : ℝ)
    (h : CutoffExpansion Q D Z c) :
    CutoffExpansion Q D (fun N => r * Z N) fun μ j => r * c μ j := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨|r| * K, hK.mono fun N hN => ?_⟩
  rw [absSpectralSum_const_mul, ← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hN (abs_nonneg r)

namespace SmoothExpansionCertificate

variable {Z₁ Z₂ : ℝ → ℝ}

/-- The sum of two certificates, on the common lattice `Q₁Q₂` with degree `max D₁ D₂`. -/
noncomputable def add (C₁ : SmoothExpansionCertificate Z₁) (C₂ : SmoothExpansionCertificate Z₂) :
    SmoothExpansionCertificate fun N => Z₁ N + Z₂ N where
  Q := C₁.Q * C₂.Q
  Q_pos := Nat.mul_pos C₁.Q_pos C₂.Q_pos
  D := max C₁.D C₂.D
  coeff := fun μ j => C₁.coeff μ j + C₂.coeff μ j
  coeff_support := by
    intro μ q hne
    have hQ₁ : (C₁.Q : ℝ) ≠ 0 := by exact_mod_cast C₁.Q_pos.ne'
    have hQ₂ : (C₂.Q : ℝ) ≠ 0 := by exact_mod_cast C₂.Q_pos.ne'
    by_cases h1 : C₁.coeff μ q = 0
    · have h2 : C₂.coeff μ q ≠ 0 := fun h2 => hne (by rw [h1, h2, add_zero])
      obtain ⟨⟨m, hm⟩, hq⟩ := C₂.coeff_support μ q h2
      refine ⟨⟨C₁.Q * m, ?_⟩, hq.trans (le_max_right _ _)⟩
      rw [hm]; push_cast; field_simp
    · obtain ⟨⟨m, hm⟩, hq⟩ := C₁.coeff_support μ q h1
      refine ⟨⟨m * C₂.Q, ?_⟩, hq.trans (le_max_left _ _)⟩
      rw [hm]; push_cast; field_simp
  expansion := by
    have e₁ : CutoffExpansion (C₁.Q * C₂.Q) (max C₁.D C₂.D) Z₁ C₁.coeff :=
      (C₁.expansion.refine C₁.Q_pos (Nat.mul_pos C₁.Q_pos C₂.Q_pos) (dvd_mul_right _ _)
        (fun _ hμ j => C₁.coeff_eq_zero_of_not_lattice hμ j)).pad (le_max_left _ _)
        fun _ _ hj => C₁.coeff_eq_zero_of_degree_gt hj
    have e₂ : CutoffExpansion (C₁.Q * C₂.Q) (max C₁.D C₂.D) Z₂ C₂.coeff :=
      (C₂.expansion.refine C₂.Q_pos (Nat.mul_pos C₁.Q_pos C₂.Q_pos) (dvd_mul_left _ _)
        (fun _ hμ j => C₂.coeff_eq_zero_of_not_lattice hμ j)).pad (le_max_right _ _)
        fun _ _ hj => C₂.coeff_eq_zero_of_degree_gt hj
    exact e₁.add e₂

/-- A scalar multiple of a certificate. -/
noncomputable def smul (r : ℝ) (C : SmoothExpansionCertificate Z₁) :
    SmoothExpansionCertificate fun N => r * Z₁ N where
  Q := C.Q
  Q_pos := C.Q_pos
  D := C.D
  coeff := fun μ j => r * C.coeff μ j
  coeff_support := fun μ q hne =>
    C.coeff_support μ q fun h => hne (by rw [h, mul_zero])
  expansion := C.expansion.const_mul r

/-- The zero certificate. -/
noncomputable def zero : SmoothExpansionCertificate fun _ => (0 : ℝ) where
  Q := 1
  Q_pos := one_pos
  D := 0
  coeff := fun _ _ => 0
  coeff_support := fun _ _ hne => absurd rfl hne
  expansion := CutoffExpansion.zero 1 0

/-- Transport of a certificate along an eventual equality of functions. -/
noncomputable def congr (C : SmoothExpansionCertificate Z₁) (h : Z₁ =ᶠ[atTop] Z₂) :
    SmoothExpansionCertificate Z₂ where
  Q := C.Q
  Q_pos := C.Q_pos
  D := C.D
  coeff := C.coeff
  coeff_support := C.coeff_support
  expansion := C.expansion.congr_eventually h

end SmoothExpansionCertificate

namespace SmoothEngine

namespace SmoothSheetInputs

variable {d : ℕ}

/-- The same domain, phase and prior (hence the same localisation measure). -/
theorem D_μ_eq_of {X Y : SmoothSheetInputs d} (hW : X.A.W = Y.A.W) (hprior : X.prior = Y.prior) :
    X.D.μ = Y.D.μ := by
  rw [X.D_μ, Y.D_μ]
  unfold priorMeasure
  rw [hW, hprior]

/-- Additivity of the partition function in the observable, for `N ≥ 0`. -/
theorem Z_add {X Y Z : SmoothSheetInputs d} (hW : X.A.W = Z.A.W) (hW' : Y.A.W = Z.A.W)
    (hK : X.K = Z.K) (hK' : Y.K = Z.K) (hprior : X.prior = Z.prior) (hprior' : Y.prior = Z.prior)
    (hobs : Z.obs = fun w => X.obs w + Y.obs w) {N : ℝ} (hN : 0 ≤ N) :
    Z.D.Z N = X.D.Z N + Y.D.Z N := by
  have hμ := D_μ_eq_of hW hprior
  have hμ' := D_μ_eq_of hW' hprior'
  have hX := X.D.integrable_integrand hN
  have hY := Y.D.integrable_integrand hN
  rw [hμ] at hX
  rw [hμ'] at hY
  unfold LocalisationData.Z
  rw [hμ, hμ', ← integral_add hX hY]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [LocalisationData.integrand, X.D_obs, Y.D_obs, Z.D_obs, X.D_phase, Y.D_phase,
    Z.D_phase, hobs, hK, hK']
  ring

/-- Scaling of the partition function in the observable. -/
theorem Z_smul {X Z : SmoothSheetInputs d} (hW : X.A.W = Z.A.W) (hK : X.K = Z.K)
    (hprior : X.prior = Z.prior) {r : ℝ} (hobs : Z.obs = fun w => r * X.obs w) (N : ℝ) :
    Z.D.Z N = r * X.D.Z N := by
  have hμ := D_μ_eq_of hW hprior
  unfold LocalisationData.Z
  rw [hμ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [LocalisationData.integrand, X.D_obs, Z.D_obs, X.D_phase, Z.D_phase, hobs, hK]
  ring

theorem Z_eq_zero {Z : SmoothSheetInputs d} (hobs : Z.obs = fun _ => 0) (N : ℝ) : Z.D.Z N = 0 := by
  unfold LocalisationData.Z
  simp [LocalisationData.integrand, Z.D_obs, hobs]

/-- The certificate of the smooth producer, for the partition function `D.Z`. -/
noncomputable def certificateZ (X : SmoothSheetInputs d) : SmoothExpansionCertificate X.D.Z :=
  X.certificate.congr (Eventually.of_forall fun N => (X.Z_eq_globalLaplace N).symm)

theorem certificateZ_coeff (X : SmoothSheetInputs d) : X.certificateZ.coeff = X.decomp.coeff := rfl

/-- ★★ **Additivity in the observable**: for smooth sheet inputs with the same domain, phase and
prior, the intrinsic coefficients of `obs = f + g` are the sums of those of `f` and of `g`. -/
theorem coeff_add {X Y Z : SmoothSheetInputs d} (hW : X.A.W = Z.A.W) (hW' : Y.A.W = Z.A.W)
    (hK : X.K = Z.K) (hK' : Y.K = Z.K) (hprior : X.prior = Z.prior) (hprior' : Y.prior = Z.prior)
    (hobs : Z.obs = fun w => X.obs w + Y.obs w) (μ : ℝ) (q : ℕ) :
    Z.decomp.coeff μ q = X.decomp.coeff μ q + Y.decomp.coeff μ q := by
  have hev : (fun N => X.D.Z N + Y.D.Z N) =ᶠ[atTop] Z.D.Z :=
    (eventually_ge_atTop (0 : ℝ)).mono fun N hN =>
      (Z_add hW hW' hK hK' hprior hprior' hobs hN).symm
  exact SmoothExpansionCertificate.coeff_eq Z.certificateZ
    ((X.certificateZ.add Y.certificateZ).congr hev) μ q

/-- ★ **Homogeneity in the observable.** -/
theorem coeff_smul {X Z : SmoothSheetInputs d} (hW : X.A.W = Z.A.W) (hK : X.K = Z.K)
    (hprior : X.prior = Z.prior) {r : ℝ} (hobs : Z.obs = fun w => r * X.obs w) (μ : ℝ) (q : ℕ) :
    Z.decomp.coeff μ q = r * X.decomp.coeff μ q := by
  have hev : (fun N => r * X.D.Z N) =ᶠ[atTop] Z.D.Z :=
    Eventually.of_forall fun N => (Z_smul hW hK hprior hobs N).symm
  exact SmoothExpansionCertificate.coeff_eq Z.certificateZ
    ((X.certificateZ.smul r).congr hev) μ q

/-- The zero observable has zero coefficients. -/
theorem coeff_zero {Z : SmoothSheetInputs d} (hobs : Z.obs = fun _ => 0) (μ : ℝ) (q : ℕ) :
    Z.decomp.coeff μ q = 0 := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop] Z.D.Z :=
    Eventually.of_forall fun N => (Z_eq_zero hobs N).symm
  exact SmoothExpansionCertificate.coeff_eq Z.certificateZ
    (SmoothExpansionCertificate.zero.congr hev) μ q

end SmoothSheetInputs

end SmoothEngine

end Grammar
