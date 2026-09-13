/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.NormalReflectionTransport
import Grammar.CertificateSeriesRegularity
import Grammar.ExpansionAssembly
import Grammar.PolynomialBoxInstance

/-!
# The coordinate-free expansion on the signed box (CCCXLI; phase G, unit G6)

Consult #100 §1, §7–8. For the even monomial phase on the signed box `[−a,a]^d` and a signed
analytic packet (`HolomorphicSignedBoxExtension`), each orthant piece `R_σ⁻¹ [0,a]^d` carries the
expansion transported from the positive box for the pulled-back packet (CCCXXXIV at one common
collar level, CCCXXXVIII), and the `2^d` pieces assemble (CCCXL) into ONE expansion on the signed
box with the **assembled stratum measures** `ν_I = ∑_σ (R_σ)_* ν_{σ,I}` (`signedStratumMeasure`) and
the **assembled moment field** `∑_σ w_σ • (R_σ)_* B_σ` with Radon–Nikodym weights
(`signedMomentField`) — contributions from all normal sides at a stratum point are averaged in one
(a.e. with respect to the summed measure; the assembled measures and field depend on the packet,
the collar level and the producer, and the coefficient sum is the proved specification)
fibre, on the unchanged full coordinate strata and the unchanged spectrum (the same coordinate
lattice `coordCommonQ k` and log-degree bound `d − 1` as the positive pieces — an indexing envelope,
not a claim of minimality or of nonvanishing coefficients):
★★★ `hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local` (hypotheses: the signed packet,
`0 < d`, `0 < a`, nonnegativity of the prior on the signed box) and its at-level form
`hasCoordFreeExpansion_signed_at`. Specifications: the measures are finite, supported a.e. in the
signed box (`ae_signedStratumMeasure_mem_signedBox`), given by the exact finite sum
(`signedStratumMeasure_eq`), and the coefficients are the sums of the reflected positive-box
coefficients (★ `expansionCoefficient_signed`). Polynomial instance: ★★
`hasCoordFreeExpansion_signed_polynomial` (real polynomials, prior nonnegative on the signed box
only). Not included: Jacobian orders other than `zeroOrders`; a nonconstant analytic unit; general
chart gluing. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology MvPolynomial

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} {a : ℝ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {ϕ φ : (Fin d → ℝ) → ℝ}
  (A : HolomorphicSignedBoxExtension a ϕ φ) (hd : 0 < d) (ha : 0 < a)
  (hϕ0 : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (σ : CoordSign d) (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
      ((A.pullback σ).toRep.faceSeries a I).ρ)

/-! ### The pieces -/

/-- The positive-box certificate of the orthant piece `σ` (for the pulled-back packet). -/
noncomputable def pieceCertificate (σ : CoordSign d) :
    ResolvedCertificate (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk)
      (piBox d (Icc 0 a)) (CoordModel.phase d k) (posPart (A.pullback σ).priorRep)
      (A.pullback σ).obsRep :=
  producedCertificate k hk (A.pullback σ) hd ha
    (HolomorphicSignedBoxExtension.pullback_nonneg hϕ0 σ) δ hδ hδa (hsmall σ)

/-- The coefficient certificate of the orthant piece `σ`. -/
noncomputable def pieceCoeff (σ : CoordSign d) :
    (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).CoefficientCertificate :=
  producedCoeffCertificate k hk (A.pullback σ) hd ha
    (HolomorphicSignedBoxExtension.pullback_nonneg hϕ0 σ) δ hδ hδa (hsmall σ)

/-- The stratum measures of the piece `σ`, pushed to the orthant piece: `(R_σ)_* ν_{σ,I}`. -/
noncomputable def pieceMeasure (σ : CoordSign d) :
    ∀ I : Finset (Fin d), Measure ((geometry d k (zeroOrders d) hk).Stratum I) :=
  reflMeasure k (zeroOrders d) hk σ
    (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure

/-- The moment field of the piece `σ`, transported: `(R_σ)_* B_σ`. -/
noncomputable def pieceField (σ : CoordSign d) :
    (normalData d k (zeroOrders d) hk).MomentCoefficientField :=
  reflField k (zeroOrders d) hk σ (pieceCoeff k hk A hd ha hϕ0 δ hδ hδa hsmall σ).field

theorem isFiniteMeasure_pieceStratumMeasure (σ : CoordSign d)
    (I : Finset (geometry d k (zeroOrders d) hk).Component) :
    IsFiniteMeasure ((pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure I) :=
  inferInstance

theorem isFiniteMeasure_pieceMeasure (σ : CoordSign d)
    (I : Finset (geometry d k (zeroOrders d) hk).Component) :
    IsFiniteMeasure (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall σ I) := by
  have : ∀ I : Finset (Fin d),
      IsFiniteMeasure ((pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure I) :=
    fun I => isFiniteMeasure_pieceStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall σ I
  exact isFiniteMeasure_reflMeasure k (zeroOrders d) hk σ _ I

/-- The original observable, reflected, has the germs of the piece's observable representative at
the base points. -/
theorem piece_germ (σ : CoordSign d)
    (J : Fin (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).M)
    (s : ↥((pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).base J)) :
    (φ ∘ refl σ) =ᶠ[𝓝 ((geometry d k (zeroOrders d) hk).π (s.1 : Fin d → ℝ))]
      (A.pullback σ).obsRep :=
  eventually_of_mem ((A.pullback σ).isOpen_realDomain.mem_nhds
    ((A.pullback σ).box_subset_realDomain (mem_box_of_mem_baseStratum k hk a δ ha _ s)))
    fun _ hw => ((A.pullback σ).obsRep_eq_of_mem hw).symm

/-- The piece expansion on the orthant piece `R_σ⁻¹ [0,a]^d`. -/
theorem piece_expansion (σ : CoordSign d) :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall σ)
      (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall σ)
      (spectrumLe (commonQ (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).cores.k) (d - 1))
      (orthantBox σ a) (phase d k) ϕ φ :=
  hasCoordFreeExpansion_refl k (zeroOrders d) hk a σ _ _ _ ϕ φ
    (hasCoordFreeExpansion_local_at k hk hd ha (A.pullback σ)
      (HolomorphicSignedBoxExtension.pullback_nonneg hϕ0 σ) δ hδ hδa (hsmall σ))

/-- Summability of the piece's normal-order series at every stratum point. -/
theorem piece_summable (σ : CoordSign d) (I : Finset (Fin d))
    (s : (geometry d k (zeroOrders d) hk).Stratum I) (q : PowerLogIndex) :
    Summable fun r : ℕ => (r.factorial : ℝ)⁻¹ *
      (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall σ I r q s).pair
        ((normalData d k (zeroOrders d) hk).normalDifferential φ I s r) :=
  ((pieceCoeff k hk A hd ha hϕ0 δ hδ hδa hsmall σ).summable_field_pair_of_germ (φ ∘ refl σ)
    (piece_germ k hk A hd ha hϕ0 δ hδ hδa hsmall σ) I q
      (reflStratum k (zeroOrders d) hk σ I s)).congr fun r => by
    unfold pieceField
    rw [reflField_pair k (zeroOrders d) hk _ φ σ I r q s]

/-- The pairing identity for the piece field. -/
theorem pieceField_pair (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) (q : PowerLogIndex)
    (t : (geometry d k (zeroOrders d) hk).Stratum I) :
    (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall σ I r q t).pair
      ((normalData d k (zeroOrders d) hk).normalDifferential φ I t r) =
    ((pieceCoeff k hk A hd ha hϕ0 δ hδ hδa hsmall σ).field I r q
      (reflStratum k (zeroOrders d) hk σ I t)).pair
      ((normalData d k (zeroOrders d) hk).normalDifferential (φ ∘ refl σ) I
        (reflStratum k (zeroOrders d) hk σ I t) r) :=
  reflField_pair k (zeroOrders d) hk _ φ σ I r q t

/-- Integrability of the piece's normal-order series against the piece measure. -/
theorem piece_integrable (σ : CoordSign d) (I : Finset (Fin d)) (q : PowerLogIndex) :
    Integrable (fun s => ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
      (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall σ I r q s).pair
        ((normalData d k (zeroOrders d) hk).normalDifferential φ I s r))
      (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall σ I) := by
  unfold pieceMeasure reflMeasure
  rw [integrable_map_equiv]
  refine ((pieceCoeff k hk A hd ha hϕ0 δ hδ hδa hsmall σ).integrable_field_series_of_germ
    (φ ∘ refl σ) (piece_germ k hk A hd ha hϕ0 δ hδ hδa hsmall σ) I q).congr
    (Eventually.of_forall fun s => ?_)
  simp only [Function.comp, reflStratumEquiv_apply]
  refine tsum_congr fun r => ?_
  have h := pieceField_pair k hk A hd ha hϕ0 δ hδ hδa hsmall σ I r q
    (reflStratum k (zeroOrders d) hk σ I s)
  rw [reflStratum_reflStratum k (zeroOrders d) hk σ I s] at h
  exact congrArg (fun z => (r.factorial : ℝ)⁻¹ * z) h.symm

/-! ### The assembled data -/

/-- The exponent family of the collar cores: `k` in the normal coordinates of each stratum. -/
noncomputable def coordCoresK (k : Fin d → ℕ) :
    ∀ J : Fin (numCores d), Fin (nI (coreIdx J) + 1) → ℕ :=
  fun J => NormalisedBox.kι k (coreIdx J).1 (σI (coreIdx J))

/-- The common coordinate lattice `coordCommonQ k = ∏_J Q(k_J)`. -/
noncomputable def coordCommonQ (k : Fin d → ℕ) : ℕ := commonQ (coordCoresK k)

/-- The cores' exponents of a piece do not depend on the packet. -/
theorem pieceCertificate_cores_k (σ : CoordSign d) :
    (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).cores.k = coordCoresK k := rfl

/-- ★ **Spectrum normalisation**: every piece has the common coordinate lattice. -/
theorem commonQ_piece (σ : CoordSign d) :
    commonQ (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).cores.k = coordCommonQ k := by
  rw [pieceCertificate_cores_k]
  rfl

/-- ★★ **The assembled stratum measures** `ν_I = ∑_σ (R_σ)_* ν_{σ,I}`. -/
noncomputable def signedStratumMeasure :
    ∀ I : Finset (geometry d k (zeroOrders d) hk).Component,
      Measure ((geometry d k (zeroOrders d) hk).Stratum I) :=
  ResolvedNormalData.sumMeasure (R := geometry d k (zeroOrders d) hk)
    (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall)

/-- ★★ **The assembled moment field** `∑_σ w_σ • (R_σ)_* B_σ` (Radon–Nikodym weights). -/
noncomputable def signedMomentField : (normalData d k (zeroOrders d) hk).MomentCoefficientField :=
  (normalData d k (zeroOrders d) hk).glueField (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall)
    (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall)

/-- The exact measure specification. -/
theorem signedStratumMeasure_eq (I : Finset (geometry d k (zeroOrders d) hk).Component) :
    signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall I = ∑ σ : CoordSign d,
      ((pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure I).map
        (reflStratumEquiv k (zeroOrders d) hk σ I) := rfl

theorem isFiniteMeasure_signedStratumMeasure
    (I : Finset (geometry d k (zeroOrders d) hk).Component) :
    IsFiniteMeasure (signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall I) :=
  have := isFiniteMeasure_pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall
  ResolvedNormalData.isFiniteMeasure_sumMeasure _ I

/-- ★ **Support**: the assembled stratum measures live in the signed box. -/
theorem ae_signedStratumMeasure_mem_signedBox
    (I : Finset (geometry d k (zeroOrders d) hk).Component) :
    ∀ᵐ (t : (geometry d k (zeroOrders d) hk).Stratum I)
      ∂signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall I,
      (t : Fin d → ℝ) ∈ piBox d (Icc (-a) a) := by
  refine ResolvedNormalData.ae_sumMeasure_of_forall _ I
    ((measurableSet_signedBox a).preimage measurable_subtype_coe) fun σ => ?_
  refine (ae_reflMeasure_mem_orthantBox k (zeroOrders d) hk a σ _ I ?_).mono
    fun t ht => orthantBox_subset σ a ht
  exact ae_stratumMeasure_mem_box k hk a δ hδ (posPart (A.pullback σ).priorRep)
    (A.pullback σ).obsRep (measurable_posPart (A.pullback σ).measurable_priorRep)
    (posPart_nonneg _) (integrable_posPart a ((A.pullback σ).priorRep_nonneg_on
      (HolomorphicSignedBoxExtension.pullback_nonneg hϕ0 σ)) (A.pullback σ).integrable_obsRep)
    hd ha hδa (fun I => (((A.pullback σ).toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha
      (hsmall σ I)).toPosPart k hk a δ hδ hd ha hδa ((A.pullback σ).priorRep_nonneg_on
        (HolomorphicSignedBoxExtension.pullback_nonneg hϕ0 σ))) I

/-- ★ **The coefficient-sum specification**: the assembled coefficients are the sums of the
positive-box coefficients of the reflected data. -/
theorem expansionCoefficient_signed (q : PowerLogIndex) :
    (normalData d k (zeroOrders d) hk).expansionCoefficient
      (signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall)
      (signedMomentField k hk A hd ha hϕ0 δ hδ hδa hsmall) φ q =
    ∑ σ : CoordSign d, (normalData d k (zeroOrders d) hk).expansionCoefficient
      (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure
      (pieceCoeff k hk A hd ha hϕ0 δ hδ hδa hsmall σ).field (φ ∘ refl σ) q := by
  have := isFiniteMeasure_pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall
  unfold signedStratumMeasure signedMomentField
  rw [ResolvedNormalData.expansionCoefficient_glue (normalData d k (zeroOrders d) hk)
    (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall) (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall)
    φ q (fun σ I s => piece_summable k hk A hd ha hϕ0 δ hδ hδa hsmall σ I s q)
    (fun σ I => piece_integrable k hk A hd ha hϕ0 δ hδ hδa hsmall σ I q)]
  exact Finset.sum_congr rfl fun σ _ =>
    expansionCoefficient_reflMeasure k (zeroOrders d) hk σ _ _ φ q

/-! ### Integrability of the original integrand on the signed box -/

theorem isCompact_signedBox : IsCompact (piBox d (Icc (-a) a)) :=
  isCompact_univ_pi fun _ => isCompact_Icc

include A in
theorem integrableOn_signedBox (n : ℝ) :
    IntegrableOn (fun w => φ w * ϕ w * Real.exp (-n * phase d k w)) (piBox d (Icc (-a) a)) := by
  have hφ : ContinuousOn (fun w => (A.Hφ (complexify w)).re) (piBox d (Icc (-a) a)) :=
    Complex.continuous_re.comp_continuousOn (A.holφ.continuousOn.comp
      continuous_complexify.continuousOn fun w hw => A.box_subset w hw)
  have hϕ : ContinuousOn (fun w => (A.Hϕ (complexify w)).re) (piBox d (Icc (-a) a)) :=
    Complex.continuous_re.comp_continuousOn (A.holϕ.continuousOn.comp
      continuous_complexify.continuousOn fun w hw => A.box_subset w hw)
  have hc : ContinuousOn (fun w => (A.Hφ (complexify w)).re * (A.Hϕ (complexify w)).re *
      Real.exp (-n * phase d k w)) (piBox d (Icc (-a) a)) :=
    (hφ.mul hϕ).mul ((continuous_const.mul (continuous_phase d k)).rexp).continuousOn
  refine (hc.integrableOn_compact isCompact_signedBox).congr_fun (fun w hw => ?_)
    (measurableSet_signedBox a)
  simp only
  rw [A.eqφ w (A.box_subset w hw), A.eqϕ w (A.box_subset w hw)]

/-! ### The signed-box theorem -/

/-- ★★★ **The coordinate-free expansion on the signed box, at a given collar level.** -/
theorem hasCoordFreeExpansion_signed_at :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall)
      (signedMomentField k hk A hd ha hϕ0 δ hδ hδa hsmall)
      (spectrumLe (coordCommonQ k) (d - 1)) (piBox d (Icc (-a) a)) (phase d k) ϕ φ := by
  have := isFiniteMeasure_pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall
  refine ResolvedNormalData.HasCoordFreeExpansion.sum (normalData d k (zeroOrders d) hk)
    (pieceMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall) (pieceField k hk A hd ha hϕ0 δ hδ hδa hsmall) _
    _ (fun σ => orthantBox σ a) (phase d k) ϕ φ ?_ ?_ ?_ ?_
  · intro n
    unfold globalLaplace
    exact setIntegral_signedBox_eq_sum a _ (integrableOn_signedBox k A n)
  · exact fun σ I s q => piece_summable k hk A hd ha hϕ0 δ hδ hδa hsmall σ I s q
  · exact fun σ I q => piece_integrable k hk A hd ha hϕ0 δ hδ hδa hsmall σ I q
  · intro σ
    have h := piece_expansion k hk A hd ha hϕ0 δ hδ hδa hsmall σ
    rwa [commonQ_piece k hk A hd ha hϕ0 δ hδ hδa hsmall σ] at h

omit δ hδ hδa hsmall in
/-- ★★★ **THE COORDINATE-FREE EXPANSION ON THE SIGNED BOX** from a signed analytic packet: for
some collar level, `∫_{[−a,a]^d} φ ϕ e^{−nK}` has the coordinate-free expansion on the full
coordinate strata, with the assembled stratum measures `∑_σ (R_σ)_* ν_σ` and the assembled
moment field, on the unchanged spectrum. Hypotheses: the packet, `0 < d`, `0 < a`, and
nonnegativity of the prior on the signed box. -/
theorem hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (σ : CoordSign d) (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
          ((A.pullback σ).toRep.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall)
        (signedMomentField k hk A hd ha hϕ0 δ hδ hδa hsmall)
        (spectrumLe (coordCommonQ k) (d - 1)) (piBox d (Icc (-a) a)) (phase d k) ϕ φ := by
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta_common a k hk hd ha
    (fun σ : CoordSign d => (A.pullback σ).toRep.radius a)
    fun σ => (A.pullback σ).toRep.radius_pos a
  exact ⟨δ, hδ, hδa, fun σ I i => hsm σ (σI I i).1,
    hasCoordFreeExpansion_signed_at k hk A hd ha hϕ0 δ hδ hδa fun σ I i => hsm σ (σI I i).1⟩

/-! ### Polynomial instances -/

/-- The signed polynomial packet: real polynomials on `Ω = ℂ^d`. -/
noncomputable def HolomorphicSignedBoxExtension.ofPolynomials (a : ℝ)
    (P Q : MvPolynomial (Fin d) ℝ) :
    HolomorphicSignedBoxExtension a (fun w => eval w P) (fun w => eval w Q) where
  Ω := univ
  isOpen_Ω := isOpen_univ
  box_subset := fun _ _ => mem_univ _
  Hϕ := fun z => eval z (map (algebraMap ℝ ℂ) P)
  Hφ := fun z => eval z (map (algebraMap ℝ ℂ) Q)
  holϕ := (differentiable_eval _).differentiableOn
  holφ := (differentiable_eval _).differentiableOn
  eqϕ := fun w _ => by rw [eval_complexify_map, Complex.ofReal_re]
  eqφ := fun w _ => by rw [eval_complexify_map, Complex.ofReal_re]

omit A hϕ0 δ hδ hδa hsmall in
/-- ★★ **Signed polynomial instance**: `∫_{[−a,a]^d} Q P e^{−nK}` for real polynomials `P ≥ 0` on
the signed box and `Q`. -/
theorem hasCoordFreeExpansion_signed_polynomial (P Q : MvPolynomial (Fin d) ℝ)
    (hP : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ eval w P) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (σ : CoordSign d) (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
          (((HolomorphicSignedBoxExtension.ofPolynomials a P Q).pullback σ).toRep.faceSeries a
            I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (signedStratumMeasure k hk (HolomorphicSignedBoxExtension.ofPolynomials a P Q) hd ha hP δ
          hδ hδa hsmall)
        (signedMomentField k hk (HolomorphicSignedBoxExtension.ofPolynomials a P Q) hd ha hP δ hδ
          hδa hsmall)
        (spectrumLe (coordCommonQ k) (d - 1)) (piBox d (Icc (-a) a)) (phase d k)
        (fun w => eval w P) (fun w => eval w Q) :=
  hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local k hk
    (HolomorphicSignedBoxExtension.ofPolynomials a P Q) hd ha hP

end WaterFilling

end Grammar
