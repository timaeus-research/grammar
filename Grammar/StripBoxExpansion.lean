/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ReflectedBoxExpansion
import Grammar.StripNormalisation

/-!
# The single-chart theorem with an analytic unit: the strip-normalised box (Astra #69 B1)

The phase `K = unit · ∏_j y_{n_j}^{2k_j}` on `Fin (t + (n+1)) → ℝ` (tangential coordinates first,
normal coordinates `n_j := finSumFinEquiv (inr j)` last), with `unit` analytic and positive on an
open `V`, is put into exact monomial form `β ∏ z^{2k}` by the strip normalisation
`T = rescale n_{j₀} (unit/β)^{1/2k_{j₀}}` (`StripData`, packaged from `exists_stripNormalisation`).
The **normal-form box** `zbox = prodToPi(A × [-b',b']^{n+1})` lies in the image of the strip, and
its preimage `Ω = T⁻¹(zbox)` is the adapted integration region. By the change of variables for the
analytic inverse `T⁻¹` (`integral_image_eq_integral_abs_det_fderiv_smul`) and the volume-preserving
product coordinates `prodToPi` (`MeasurePreserving.setIntegral_image_emb`),

  `∫_Ω F e^{−NK} = ∫_{A × [-b',b']^{n+1}} normalAmp(v,u) e^{−Nβ∏ u^{2k}}`

with the **normal-form amplitude** `normalAmp = |det D(T⁻¹)| · F∘T⁻¹` in product coordinates
(`integral_strip_eq_twoSidedBox`), and the two-sided box theorem gives the full power–log cutoff
expansion (`strip_cutoffExpansion`) under the joint-series hypothesis for `normalAmp` with the
dimension margin. The normal-form amplitude is continuous on the box (`continuousOn_normalAmp`).

Non-claims (Astra #69): one normalisation on one adapted region — the outer region `|y_{n_{j₀}}| >
b₀`, several normalisation charts and their ownership, and the series margin for `normalAmp`
(a hypothesis here) are not treated.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

/-! ### The strip normalisation as a package -/

section Strip

variable {d : ℕ}

/-- **Strip normalisation data** for the rescaling `rescale i ρ` over the base `Q₀`: the output
of `exists_stripNormalisation`. -/
structure StripData (i : Fin d) (V : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (Q₀ : Set (Fin d → ℝ)) where
  /-- the strip height -/
  b₀ : ℝ
  /-- the output cylinder height -/
  b : ℝ
  b₀_pos : 0 < b₀
  b_pos : 0 < b
  /-- the open strip -/
  S : Set (Fin d → ℝ)
  S_open : IsOpen S
  S_sub : S ⊆ V
  cyl_sub : cylinder i Q₀ (b₀ / 2) ⊆ S
  injOn : InjOn (rescale i ρ) S
  jac_pos : ∀ y ∈ S, 0 < ρ y + y i * fderiv ℝ ρ y (Pi.single i 1)
  image_open : IsOpen (rescale i ρ '' S)
  cyl_sub_image : cylinder i Q₀ b ⊆ rescale i ρ '' S
  inv_analytic : ∀ z ∈ rescale i ρ '' S, AnalyticAt ℝ (Function.invFunOn (rescale i ρ) S) z

theorem exists_stripData {i : Fin d} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : AnalyticOnNhd ℝ ρ V) (hρpos : ∀ y ∈ V, 0 < ρ y)
    {Q₀ : Set (Fin d → ℝ)} (hQ₀ : IsCompact Q₀) (hQ₀V : Q₀ ⊆ V) (hQ₀i : ∀ y ∈ Q₀, y i = 0) :
    Nonempty (StripData i V ρ Q₀) := by
  obtain ⟨b₀, b, S, hb₀, hb, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩ :=
    exists_stripNormalisation hV hρ hρpos hQ₀ hQ₀V hQ₀i
  exact ⟨⟨b₀, b, hb₀, hb, S, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩⟩

namespace StripData

variable {i : Fin d} {V : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {Q₀ : Set (Fin d → ℝ)}
  (SD : StripData i V ρ Q₀)

/-- The inverse of the rescaling on the strip. -/
noncomputable def inv : (Fin d → ℝ) → (Fin d → ℝ) := Function.invFunOn (rescale i ρ) SD.S

theorem inv_mem {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) : SD.inv z ∈ SD.S :=
  Function.invFunOn_mem ((Set.mem_image _ _ _).1 hz)

theorem apply_inv {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) : rescale i ρ (SD.inv z) = z :=
  Function.invFunOn_eq ((Set.mem_image _ _ _).1 hz)

theorem inv_apply {y : Fin d → ℝ} (hy : y ∈ SD.S) : SD.inv (rescale i ρ y) = y :=
  SD.injOn.leftInvOn_invFunOn hy

theorem injOn_inv : InjOn SD.inv (rescale i ρ '' SD.S) := by
  intro z₁ hz₁ z₂ hz₂ h
  rw [← SD.apply_inv hz₁, ← SD.apply_inv hz₂, h]

theorem hasFDerivAt_inv {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) :
    HasFDerivAt SD.inv (fderiv ℝ SD.inv z) z :=
  (SD.inv_analytic z hz).differentiableAt.hasFDerivAt

end StripData

end Strip

/-! ### Product coordinates on `Fin (t + (n+1)) → ℝ` -/

variable {t n : ℕ}

/-- The normal coordinate indices (the last `n+1` coordinates). -/
def nIdx (t : ℕ) (j : Fin (n + 1)) : Fin (t + (n + 1)) := finSumFinEquiv (Sum.inr j)

/-- The tangential coordinate indices (the first `t` coordinates). -/
def tIdx (n : ℕ) (i : Fin t) : Fin (t + (n + 1)) := finSumFinEquiv (Sum.inl i)

theorem nIdx_injective : Function.Injective (nIdx (n := n) t) :=
  fun _ _ h => Sum.inr_injective (finSumFinEquiv.injective h)

theorem tIdx_ne_nIdx (i : Fin t) (j : Fin (n + 1)) : tIdx n i ≠ nIdx t j := fun h =>
  Sum.inl_ne_inr (finSumFinEquiv.injective h)

/-- The product coordinates `(v, u) ↦ (v, u) ∈ Fin (t + (n+1)) → ℝ`, a volume-preserving measurable
equivalence. -/
noncomputable def prodToPi (t n : ℕ) :
    ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) ≃ᵐ (Fin (t + (n + 1)) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin t ⊕ Fin (n + 1) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv)

theorem prodToPi_apply_nIdx (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) (j : Fin (n + 1)) :
    prodToPi t n p (nIdx t j) = p.2 j := by
  unfold prodToPi nIdx
  rw [MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem prodToPi_apply_tIdx (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) (i : Fin t) :
    prodToPi t n p (tIdx n i) = p.1 i := by
  unfold prodToPi tIdx
  rw [MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem measurePreserving_prodToPi :
    MeasurePreserving (prodToPi t n) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin t ⊕ Fin (n + 1) => ℝ)).trans
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) finSumFinEquiv)

theorem continuous_prodToPi : Continuous (prodToPi t n) := by
  refine continuous_pi fun x => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
  rcases s with i | j
  · simp only [show finSumFinEquiv (Sum.inl i) = tIdx n i from rfl, prodToPi_apply_tIdx]
    exact (continuous_apply i).comp continuous_fst
  · simp only [show finSumFinEquiv (Sum.inr j) = nIdx t j from rfl, prodToPi_apply_nIdx]
    exact (continuous_apply j).comp continuous_snd

/-- The base projection at a normal coordinate acts on the normal factor. -/
theorem baseProj_prodToPi (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) (j₀ : Fin (n + 1)) :
    baseProj (nIdx t j₀) (prodToPi t n p) = prodToPi t n (p.1, Function.update p.2 j₀ 0) := by
  funext x
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
  rcases s with i | j
  · rw [show finSumFinEquiv (Sum.inl i) = tIdx n i from rfl, prodToPi_apply_tIdx, baseProj,
      Function.update_of_ne (tIdx_ne_nIdx i j₀), prodToPi_apply_tIdx]
  · rw [show finSumFinEquiv (Sum.inr j) = nIdx t j from rfl, prodToPi_apply_nIdx, baseProj]
    by_cases h : j = j₀
    · subst h
      simp
    · rw [Function.update_of_ne (fun h' => h (nIdx_injective h')), prodToPi_apply_nIdx]
      dsimp only
      rw [Function.update_of_ne h]

/-- The normal monomial of a rescaled point: rescaling the normal coordinate `j₀` by `r`
multiplies `∏_j y_{n_j}^{2k_j}` by `r^{2k_{j₀}}`. -/
theorem prod_pow_rescale_nIdx (k : Fin (n + 1) → ℕ) (j₀ : Fin (n + 1))
    (r : (Fin (t + (n + 1)) → ℝ) → ℝ) (y : Fin (t + (n + 1)) → ℝ) :
    ∏ j, rescale (nIdx t j₀) r y (nIdx t j) ^ (2 * k j) =
      r y ^ (2 * k j₀) * ∏ j, y (nIdx t j) ^ (2 * k j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
    ← Finset.mul_prod_erase Finset.univ (fun j => y (nIdx t j) ^ (2 * k j)) (Finset.mem_univ j₀),
    rescale_apply_self, mul_pow,
    Finset.prod_congr rfl fun j hj => by
      rw [rescale_apply_of_ne (fun h => Finset.ne_of_mem_erase hj (nIdx_injective h))]]
  ring

/-! ### The strip-normalised box -/

variable (t) in
/-- The strip base: tangential points of `A` with normal coordinates `u_{j₀} = 0`, `|u_j| ≤ b₁`. -/
def stripBase (A : Set (Fin t → ℝ)) (j₀ : Fin (n + 1)) (b₁ : ℝ) : Set (Fin (t + (n + 1)) → ℝ) :=
  prodToPi t n '' (A ×ˢ {u : Fin (n + 1) → ℝ | u j₀ = 0 ∧ ∀ j, |u j| ≤ b₁})

theorem isCompact_stripBase {A : Set (Fin t → ℝ)} (hA : IsCompact A) (j₀ : Fin (n + 1))
    (b₁ : ℝ) : IsCompact (stripBase t A j₀ b₁) := by
  refine (hA.prod ?_).image continuous_prodToPi
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_Icc (a := -b₁) (b := b₁)) ?_ ?_
  · have h1 : IsClosed {u : Fin (n + 1) → ℝ | u j₀ = 0} :=
      isClosed_eq (continuous_apply j₀) continuous_const
    have h2 : IsClosed {u : Fin (n + 1) → ℝ | ∀ j, |u j| ≤ b₁} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun j =>
        isClosed_le (continuous_abs.comp (continuous_apply j)) continuous_const
    exact h1.inter h2
  · intro u hu j _
    exact abs_le.1 (hu.2 j)

theorem stripBase_apply_nIdx {A : Set (Fin t → ℝ)} {j₀ : Fin (n + 1)} {b₁ : ℝ}
    {y : Fin (t + (n + 1)) → ℝ} (hy : y ∈ stripBase t A j₀ b₁) : y (nIdx t j₀) = 0 := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [prodToPi_apply_nIdx]
  exact hp.2.1

variable (t) in
/-- The normal-form box `prodToPi(A × [-b',b']^{n+1})`. -/
def zBox (A : Set (Fin t → ℝ)) (b' : ℝ) : Set (Fin (t + (n + 1)) → ℝ) :=
  prodToPi t n '' twoSidedBox A b'

theorem zBox_subset_cylinder {A : Set (Fin t → ℝ)} {j₀ : Fin (n + 1)} {b₁ b' bc : ℝ}
    (hb'b₁ : b' ≤ b₁) (hb'c : b' ≤ bc) :
    zBox t A b' ⊆ cylinder (nIdx t j₀) (stripBase t A j₀ b₁) bc := by
  rintro z ⟨p, hp, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [baseProj_prodToPi]
    refine ⟨(p.1, Function.update p.2 j₀ 0), ⟨hp.1, ?_, fun j => ?_⟩, rfl⟩
    · simp
    · have hpj := hp.2 j (mem_univ j)
      by_cases h : j = j₀
      · subst h
        simp
        linarith [hpj.1, hpj.2]
      · dsimp only
        rw [Function.update_of_ne h]
        exact (abs_le.2 ⟨hpj.1, hpj.2⟩).trans hb'b₁
  · rw [prodToPi_apply_nIdx]
    have := hp.2 j₀ (mem_univ j₀)
    exact (abs_le.2 ⟨this.1, this.2⟩).trans hb'c

theorem measurableSet_zBox {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b' : ℝ) :
    MeasurableSet (zBox (n := n) t A b') :=
  (prodToPi t n).measurableEmbedding.measurableSet_image.2 (measurableSet_twoSidedBox hA b')

section Main

variable {k : Fin (n + 1) → ℕ} {j₀ : Fin (n + 1)} {β : ℝ} {V : Set (Fin (t + (n + 1)) → ℝ)}
  {unit : (Fin (t + (n + 1)) → ℝ) → ℝ} {A : Set (Fin t → ℝ)} {b₁ : ℝ}

/-- The normal-form amplitude in product coordinates: `|det D(T⁻¹)| · F∘T⁻¹`. -/
noncomputable def normalAmp
    (SD : StripData (nIdx t j₀) V (unitRoot β (2 * k j₀) unit) (stripBase t A j₀ b₁))
    (F : (Fin (t + (n + 1)) → ℝ) → ℝ) (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  |(fderiv ℝ SD.inv (prodToPi t n p)).det| * F (SD.inv (prodToPi t n p))

variable (SD : StripData (nIdx t j₀) V (unitRoot β (2 * k j₀) unit) (stripBase t A j₀ b₁))

/-- The phase on the strip in normal-form coordinates. -/
theorem phase_inv (hβ : 0 < β) (hk : 0 < k j₀) (hpos : ∀ y ∈ V, 0 < unit y)
    {K : (Fin (t + (n + 1)) → ℝ) → ℝ}
    (hK : ∀ y ∈ V, K y = unit y * ∏ j, y (nIdx t j) ^ (2 * k j)) {z : Fin (t + (n + 1)) → ℝ}
    (hz : z ∈ rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S) :
    K (SD.inv z) = β * ∏ j, z (nIdx t j) ^ (2 * k j) := by
  set y := SD.inv z with hy
  have hyS : y ∈ SD.S := SD.inv_mem hz
  have hyV : y ∈ V := SD.S_sub hyS
  have hTy : rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) y = z := SD.apply_inv hz
  rw [← hTy, prod_pow_rescale_nIdx, unitRoot_pow hβ (by omega) (hpos y hyV), hK y hyV]
  field_simp

/-- **The change of variables to the two-sided box**: for every observable `F` and `N`,
`∫_{T⁻¹(zBox)} F e^{−NK} = ∫_{A × [-b',b']^{n+1}} normalAmp e^{−Nβ∏u^{2k}}`. -/
theorem integral_strip_eq_twoSidedBox (hβ : 0 < β) (hk : 0 < k j₀) (hpos : ∀ y ∈ V, 0 < unit y)
    {K : (Fin (t + (n + 1)) → ℝ) → ℝ}
    (hK : ∀ y ∈ V, K y = unit y * ∏ j, y (nIdx t j) ^ (2 * k j)) (hA : IsCompact A) {b' : ℝ}
    (hb'b₁ : b' ≤ b₁) (hb'b : b' ≤ SD.b) (F : (Fin (t + (n + 1)) → ℝ) → ℝ) (N : ℝ) :
    ∫ y in SD.inv '' zBox t A b', F y * Real.exp (-N * K y) =
      ∫ p in twoSidedBox A b', normalAmp SD F p * Real.exp (-N * monomialPhase k β p) := by
  have hzsub : zBox t A b' ⊆ rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S :=
    (zBox_subset_cylinder hb'b₁ hb'b).trans SD.cyl_sub_image
  have hderiv : ∀ z ∈ zBox t A b',
      HasFDerivWithinAt SD.inv (fderiv ℝ SD.inv z) (zBox t A b') z :=
    fun z hz => (SD.hasFDerivAt_inv (hzsub hz)).hasFDerivWithinAt
  have h1 : ∫ y in SD.inv '' zBox t A b', F y * Real.exp (-N * K y) =
      ∫ z in zBox t A b', |(fderiv ℝ SD.inv z).det| •
        (F (SD.inv z) * Real.exp (-N * K (SD.inv z))) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_zBox hA b') hderiv
      (SD.injOn_inv.mono hzsub) _
  have h2 : ∫ z in zBox t A b', |(fderiv ℝ SD.inv z).det| •
      (F (SD.inv z) * Real.exp (-N * K (SD.inv z))) =
      ∫ p in twoSidedBox A b', |(fderiv ℝ SD.inv (prodToPi t n p)).det| •
        (F (SD.inv (prodToPi t n p)) * Real.exp (-N * K (SD.inv (prodToPi t n p)))) := by
    unfold zBox
    exact measurePreserving_prodToPi.setIntegral_image_emb (prodToPi t n).measurableEmbedding _ _
  rw [h1, h2]
  refine setIntegral_congr_fun (measurableSet_twoSidedBox hA b') fun p hp => ?_
  have hz : prodToPi t n p ∈ zBox t A b' := ⟨p, hp, rfl⟩
  simp only [smul_eq_mul, normalAmp]
  rw [phase_inv SD hβ hk hpos hK (hzsub hz)]
  unfold monomialPhase
  simp only [prodToPi_apply_nIdx]
  ring

/-- **Continuity of the normal-form amplitude** on the box. -/
theorem continuousOn_normalAmp (hV : IsOpen V) {b' : ℝ} (hb'b₁ : b' ≤ b₁)
    (hb'b : b' ≤ SD.b) {F : (Fin (t + (n + 1)) → ℝ) → ℝ} (hF : ContinuousOn F V) :
    ContinuousOn (normalAmp SD F) (twoSidedBox A b') := by
  have hzsub : zBox t A b' ⊆ rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S :=
    (zBox_subset_cylinder hb'b₁ hb'b).trans SD.cyl_sub_image
  intro p hp
  have hz : prodToPi t n p ∈ rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S :=
    hzsub ⟨p, hp, rfl⟩
  have han := SD.inv_analytic _ hz
  have hc1 : ContinuousAt (fun z => |(fderiv ℝ SD.inv z).det| * F (SD.inv z)) (prodToPi t n p) := by
    refine ContinuousAt.mul ?_ ?_
    · exact continuous_abs.continuousAt.comp
        (ContinuousLinearMap.continuous_det.continuousAt.comp han.fderiv.continuousAt)
    · exact (hF.continuousAt (hV.mem_nhds (SD.S_sub (SD.inv_mem hz)))).comp han.continuousAt
  exact (hc1.comp continuous_prodToPi.continuousAt).continuousWithinAt

/-- **The strip-normalised single-chart expansion**: for the phase `unit · ∏ y_{n_j}^{2k_j}` with an
analytic positive unit, the integral over the adapted region `T⁻¹(zBox)` has the full power–log
cutoff expansion, given the joint series of the normal-form amplitude with the dimension margin. -/
theorem strip_cutoffExpansion (hV : IsOpen V) (hk : ∀ j, 0 < k j) (hβ : 0 < β)
    (hpos : ∀ y ∈ V, 0 < unit y) {K : (Fin (t + (n + 1)) → ℝ) → ℝ}
    (hK : ∀ y ∈ V, K y = unit y * ∏ j, y (nIdx t j) ^ (2 * k j)) (hA : IsCompact A) {B b' : ℝ}
    (hb' : 0 < b') (hb'b₁ : b' ≤ b₁) (hb'b : b' ≤ SD.b) (hb'B : b' ≤ B) (hB : 0 < B)
    (hAB : ∀ v ∈ A, ∀ i, |v i| ≤ B) {F : (Fin (t + (n + 1)) → ℝ) → ℝ} (hF : ContinuousOn F V)
    {P : FormalMultilinearSeries ℝ (Fin t ⊕ Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall (fun w => normalAmp SD F (w ∘ Sum.inl, w ∘ Sum.inr)) P 0 R)
    {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) (hBρ : ((t + (n + 1) : ℕ) : ℝ) * B < ρ) (hB1 : B < ρ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
      CutoffExpansion Q Dg
        (fun N => ∫ y in SD.inv '' zBox t A b', F y * Real.exp (-N * K y)) c := by
  have heq : (fun N => ∫ y in SD.inv '' zBox t A b', F y * Real.exp (-N * K y)) =
      fun N => ∫ p in twoSidedBox A b', normalAmp SD F p * Real.exp (-N * monomialPhase k β p) :=
    funext fun N => integral_strip_eq_twoSidedBox SD hβ (hk j₀) hpos hK hA hb'b₁ hb'b F N
  rw [heq]
  exact twoSidedBox_cutoffExpansion k hk hβ hA hb' hb'B hB hAB
    (continuousOn_normalAmp SD hV hb'b₁ hb'b hF) hG hρ hBρ hB1 hδ

end Main

end Grammar
