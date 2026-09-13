# Consult #101 — audit of phase G (the signed box) and the direction after it

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 642 modules, zero sorry/axiom; every theorem below is axiom-clean:
`[propext, Classical.choice, Quot.sound]`). Your consult #100 designed phase G (signed coordinates
`[−a,a]^d` via the reflection cover, transport of expansions not certificates, Radon–Nikodym-weighted
assembly). All six units have LANDED as CCCXXXVI–CCCXLI. This consult asks for (A) an independent AUDIT of
what was proved against your design and stopping gate (§8 of #100), including the regression checks you
asked for (item 7), and (B) the recommended direction after G with a unit plan.

## 1. What landed

* G1 CCCXXXVI `SignedBoxPackets`: `CoordSign d = Fin d → Bool`, `sgn`, `refl σ = signReflect (sgn σ)`
  (involutive, measurable, `map_refl_volume`, `phase_refl`), `reflEquiv`, `setIntegral_refl` (unconditional
  change of variables), `orthantBox σ a = R_σ⁻¹ [0,a]^d`, `signOf`, `signedBox_eq_iUnion`,
  `eq_signOf_of_mem_orthantBox`; complex reflection `reflC`, `complexify_refl`; the signed packet
  `HolomorphicSignedBoxExtension a ϕ φ` (same fields as CCCXXX over `[−a,a]^d`) with `pullback σ :
  HolomorphicBoxExtension a (ϕ ∘ R_σ) (φ ∘ R_σ)` (on `R_σ^ℂ⁻¹ Ω`, `H ∘ R_σ^ℂ`); `exists_delta_common`
  (one collar level below finitely many radii); `hasCoordFreeExpansion_local_at` (CCCXXXIV at a supplied
  collar level).
* G2 CCCXXXVII `OrthantDecomposition`: `ae_coord_ne_zero` (`Measure.pi_hyperplane`),
  `setIntegral_signedBox_eq_sum : IntegrableOn g [−a,a]^d → ∫_{[−a,a]^d} g = ∑_σ ∫_{orthantBox σ} g`,
  `setIntegral_orthantBox`, `globalLaplace_signedBox_eq_sum` (even phase).
* G3 CCCXXXVIII `NormalReflectionTransport`: `reflAmbLin`, `reflNormal σ I : N_I ≃L[ℝ] N_I` (via
  `Submodule.map_span_le` invariance, `LinearEquiv.ofInvolutive`), `reflStratum`/`reflStratumEquiv`,
  `refl_Φ : R_σ (Φ_I s v) = Φ_I (R_σ s) (L_σ v)`, `normalDifferential_comp_refl` (UNCONDITIONAL, via
  `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right` with `s = univ`), `jetPull`
  (`compContinuousLinearMapL`), `reflTensor`, `reflField σ B (t) = B (R_σ t) ∘ P_σ`, `reflField_pair`,
  `reflMeasure`, `ae_reflMeasure_mem_orthantBox`, `expansionCoefficient_reflMeasure`,
  `hasCoordFreeExpansion_refl`.
* G5 CCCXXXIX `CertificateSeriesRegularity`: `transportTensor_pair'`, `chartTensorExt_pair_congr`,
  `field_pair_congr (hψ : ∀ J (s : base J), ψ =ᶠ[𝓝 (π s)] φ)`, `summable_field_pair_of_germ`,
  `integrable_field_series`, `integrable_field_series_of_germ`.
* G4 CCCXL `ExpansionAssembly`: `sumMeasure`, `rnWeight`, `glueField`, `integral_rnWeight_mul`,
  `expansionCoefficient_glue` (hypotheses: pointwise summability + integrability), `HasCoordFreeExpansion.sum`.
* G6 CCCXLI `SignedBoxExpansion` (full source below): pieces, `coordCoresK k`, `coordCommonQ k`,
  `pieceCertificate_cores_k … := rfl` (the cores' exponents are packet-independent — the directed `rfl`
  went through; a two-sided `rfl` between two packets' certificates timed out), `signedStratumMeasure`,
  `signedMomentField`, `signedStratumMeasure_eq`, `ae_signedStratumMeasure_mem_signedBox`,
  `expansionCoefficient_signed`, `integrableOn_signedBox`, ★★★ `hasCoordFreeExpansion_signed_at`,
  ★★★ `hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local`, `hasCoordFreeExpansion_signed_polynomial`.

## 2. Audit questions

1. Gate check (#100 §8, items 1–6, 8): confirm or refute each against the statements below. In particular:
   the measure spec is `∑_σ (R_σ)_* ν_{σ,I}` over ALL `2^d` signs (so at the deepest stratum the point mass is
   `2^d` copies of the one-sided measure — intended per your design); the field is RN-averaged. Is the
   public theorem's hypothesis list exactly what you asked (packet, `0<d`, `0<a`, prior `≥ 0` on the
   signed box)? Any hidden global assumption?
2. Regression checks (item 7): we have NOT added reflection-sensitive tests. Propose the exact statements
   (d = 1 origin; a d = 2 crossing; a test that fails if the normal-sign action on jets is omitted), in a
   form provable from the library (e.g. via the coefficient-sum spec `expansionCoefficient_signed` and the
   canonicity theorem CCCVIII `expansionCoefficient_eq_of_certificates`, or via an odd observable). Can the
   odd-observable cancellation `∫_{[−a,a]} w e^{−n w^{2k}} dw = 0` be turned into a check that the assembled
   coefficients vanish, given that the coefficient functional's linearity in the observable is NOT a
   library theorem (the certificate for `−φ` is a different certificate)? Suggest the cheapest genuinely
   discriminating check.
3. Anything a fidelity reviewer would flag (docstrings, dead hypotheses, misleading names, the
   `▸`-free convention, the `have` finiteness instances)?
4. Paper sentence: propose the mirror sentence for the signed box (the two-sided coordinate model as the
   local model for a real divisor), consistent with your §9.

## 3. Direction

Rank and give a unit plan for the top candidate: (iv) E projector blow-up instance (first geometry
beyond the coordinate model: what exactly must be discharged — Jacobian orders `h ≠ 0` need the producer
to be generalised beyond `zeroOrders d`; is that the next step?), (v) J observable-independent
functionals, (vi) general SNC gluing interface, (i) complexification, or stop. What should the paper now
claim? Note: the produced certificates carry `zeroOrders d`; the general `NormalisedBox.core` supports
Jacobian orders `h` (field `h := fun _ => 0` in the collar core) — how much of the collar chain would
change for monomial Jacobians `∏ |w_i|^{h_i}`?

## 4. Material

### SignedBoxExpansion.lean (CCCXLI, full)
```lean
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
```

### ExpansionAssembly.lean (CCCXL) statements
```lean
38:noncomputable def sumMeasure : ∀ I : Finset R.Component, Measure (R.Stratum I) := fun I =>
39-  ∑ e, ν e I
40-
41-omit D in
42:theorem le_sumMeasure (e : ι) (I : Finset R.Component) : ν e I ≤ sumMeasure ν I :=
43-  Finset.single_le_sum (f := fun e => ν e I) (fun _ _ => Measure.zero_le _) (Finset.mem_univ e)
44-
45-omit D in
46:theorem isFiniteMeasure_sumMeasure [∀ e I, IsFiniteMeasure (ν e I)] (I : Finset R.Component) :
47-    IsFiniteMeasure (sumMeasure ν I) := by
48-  refine ⟨?_⟩
49-  unfold sumMeasure
50-  rw [Measure.finsetSum_apply]
51-  exact ENNReal.sum_lt_top.2 fun e _ => measure_lt_top _ _
52-
--
55:theorem ae_sumMeasure_of_forall (I : Finset R.Component) {P : R.Stratum I → Prop}
56-    (hP : MeasurableSet {s | P s}) (h : ∀ e, ∀ᵐ (s : R.Stratum I) ∂ν e I, P s) :
57-    ∀ᵐ (s : R.Stratum I) ∂sumMeasure ν I, P s := by
58-  unfold sumMeasure
59-  rw [← Measure.sum_fintype, Measure.ae_sum_iff' hP]
60-  exact h
61-
--
63:theorem absolutelyContinuous_sumMeasure (e : ι) (I : Finset R.Component) :
64-    ν e I ≪ sumMeasure ν I :=
65-  Measure.absolutelyContinuous_of_le (le_sumMeasure ν e I)
66-
67-/-- **The Radon–Nikodym weight** `w_e = d ν_e / d(∑ ν_e)` (real-valued). -/
68:noncomputable def rnWeight (e : ι) (I : Finset R.Component) (s : R.Stratum I) : ℝ :=
69-  ((ν e I).rnDeriv (sumMeasure ν I) s).toReal
70-
71-/-- **The glued moment field** `∑_e w_e • B_e`. -/
72:noncomputable def glueField (B : ι → D.MomentCoefficientField) : D.MomentCoefficientField :=
73-  fun I r q s => ∑ e, rnWeight ν e I s • B e I r q s
74-
75-variable [∀ e I, IsFiniteMeasure (ν e I)]
76-
77-omit D in
78-/-- ★ The weighted integral identity `∫ w_e f d(∑ν) = ∫ f dν_e`. -/
79:theorem integral_rnWeight_mul (e : ι) (I : Finset R.Component) (f : R.Stratum I → ℝ) :
80-    ∫ s, rnWeight ν e I s * f s ∂sumMeasure ν I = ∫ s, f s ∂ν e I := by
81-  have := isFiniteMeasure_sumMeasure ν I
82-  have h := integral_rnDeriv_smul (absolutelyContinuous_sumMeasure ν e I) (f := f)
83-  simp only [smul_eq_mul] at h
84-  exact h
85-
--
87:theorem integrable_rnWeight_mul (e : ι) (I : Finset R.Component) (f : R.Stratum I → ℝ)
88-    (hf : Integrable f (ν e I)) :
89-    Integrable (fun s => rnWeight ν e I s * f s) (sumMeasure ν I) := by
90-  have := isFiniteMeasure_sumMeasure ν I
91-  have h := (integrable_rnDeriv_smul_iff (absolutelyContinuous_sumMeasure ν e I) (f := f)).2 hf
92-  simpa [rnWeight, smul_eq_mul] using h
93-
--
96:theorem expansionCoefficient_glue (B : ι → D.MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ)
97-    (q : PowerLogIndex)
98-    (hsum : ∀ (e : ι) (I : Finset R.Component) (s : R.Stratum I), Summable fun r : ℕ =>
99-      (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r))
100-    (hint : ∀ (e : ι) (I : Finset R.Component), Integrable (fun s => ∑' r : ℕ,
101-      (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r)) (ν e I)) :
102-    D.expansionCoefficient (sumMeasure ν) (D.glueField ν B) φ q =
--
133:theorem HasCoordFreeExpansion.sum (B : ι → D.MomentCoefficientField)
134-    (spec : ℝ → Finset PowerLogIndex) (W : Set (Fin d → ℝ)) (We : ι → Set (Fin d → ℝ))
135-    (K ϕ φ : (Fin d → ℝ) → ℝ)
136-    (hL : ∀ n : ℝ, globalLaplace W K (fun w => φ w * ϕ w) n =
137-      ∑ e, globalLaplace (We e) K (fun w => φ w * ϕ w) n)
138-    (hsum : ∀ (e : ι) (I : Finset R.Component) (s : R.Stratum I) (q : PowerLogIndex),
139-      Summable fun r : ℕ =>
```

### NormalReflectionTransport.lean (CCCXXXVIII) statements
```lean
40:def reflAmbLin (σ : CoordSign d) : Amb d →ₗ[ℝ] Amb d where
41-  toFun v := WithLp.toLp 2 fun i => sgn σ i * v.ofLp i
42-  map_add' v w := by
43-    ext i
44-    simp [mul_add]
45-  map_smul' c v := by
--
49:theorem reflAmbLin_ofLp (σ : CoordSign d) (v : Amb d) (i : Fin d) :
50-    (reflAmbLin σ v).ofLp i = sgn σ i * v.ofLp i := rfl
51-
52:theorem reflAmbLin_reflAmbLin (σ : CoordSign d) (v : Amb d) :
53-    reflAmbLin σ (reflAmbLin σ v) = v := by
54-  ext i
55-  rw [reflAmbLin_ofLp, reflAmbLin_ofLp, ← mul_assoc, sgn_mul_self, one_mul]
56-
57:theorem reflAmbLin_basisVec (σ : CoordSign d) (i : Fin d) :
58-    reflAmbLin σ (basisVec d i) = sgn σ i • basisVec d i := by
59-  ext j
60-  rw [reflAmbLin_ofLp, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp]
61-  by_cases hji : j = i
62-  · subst hji
--
66:theorem reflAmbLin_mem (σ : CoordSign d) (I : Finset (Fin d)) {v : Amb d}
67-    (hv : v ∈ normalSpace d I) : reflAmbLin σ v ∈ normalSpace d I := by
68-  have h : (normalSpace d I).map (reflAmbLin σ) ≤ normalSpace d I := by
69-    unfold normalSpace
70-    rw [Submodule.map_span_le]
71-    rintro _ ⟨i, rfl⟩
--
77:noncomputable def reflNormalLin (σ : CoordSign d) (I : Finset (Fin d)) :
78-    normalSpace d I →ₗ[ℝ] normalSpace d I :=
79-  (reflAmbLin σ).restrict fun _ hv => reflAmbLin_mem σ I hv
80-
81:theorem coe_reflNormalLin (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
82-    ((reflNormalLin σ I v : normalSpace d I) : Amb d) = reflAmbLin σ v := rfl
83-
84:theorem reflNormalLin_involutive (σ : CoordSign d) (I : Finset (Fin d)) :
85-    Function.Involutive (reflNormalLin σ I) := fun v =>
86-  Subtype.ext (by rw [coe_reflNormalLin, coe_reflNormalLin, reflAmbLin_reflAmbLin])
87-
88-/-- **The reflection on the normal space `N_I`** as a continuous linear equivalence. -/
89:noncomputable def reflNormal (σ : CoordSign d) (I : Finset (Fin d)) :
90-    normalSpace d I ≃L[ℝ] normalSpace d I :=
91-  (LinearEquiv.ofInvolutive (reflNormalLin σ I)
92-    (reflNormalLin_involutive σ I)).toContinuousLinearEquiv
93-
94:theorem reflNormal_apply (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
95-    reflNormal σ I v = reflNormalLin σ I v := rfl
96-
97:theorem reflNormal_ofLp (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) (i : Fin d) :
98-    ((reflNormal σ I v : normalSpace d I) : Amb d).ofLp i = sgn σ i * (v : Amb d).ofLp i := rfl
99-
100:theorem reflNormal_reflNormal (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
101-    reflNormal σ I (reflNormal σ I v) = v :=
102-  reflNormalLin_involutive σ I v
103-
104-/-! ### The reflection on the strata -/
105-
--
108:theorem refl_mem_stratumSet (σ : CoordSign d) (I : Finset (Fin d)) (w : Fin d → ℝ) :
109-    refl σ w ∈ (geometry d k h hk).stratumSet I ↔ w ∈ (geometry d k h hk).stratumSet I := by
110-  have hE : ∀ i, refl σ w ∈ (geometry d k h hk).E i ↔ w ∈ (geometry d k h hk).E i := fun i => by
111-    change sgn σ i * w i = 0 ↔ w i = 0
112-    have := sgn_ne_zero σ i
113-    simp [mul_eq_zero, this]
--
120:def reflStratum (σ : CoordSign d) (I : Finset (Fin d)) :
121-    (geometry d k h hk).Stratum I → (geometry d k h hk).Stratum I := fun s =>
122-  ⟨refl σ s.1, (refl_mem_stratumSet k h hk σ I s.1).2 s.2⟩
123-
124:theorem coe_reflStratum (σ : CoordSign d) (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I) :
125-    (reflStratum k h hk σ I s : Fin d → ℝ) = refl σ s.1 := rfl
126-
127:theorem reflStratum_reflStratum (σ : CoordSign d) (I : Finset (Fin d))
128-    (s : (geometry d k h hk).Stratum I) :
129-    reflStratum k h hk σ I (reflStratum k h hk σ I s) = s :=
130-  Subtype.ext (refl_refl σ s.1)
131-
132:theorem measurable_reflStratum (σ : CoordSign d) (I : Finset (Fin d)) :
133-    Measurable (reflStratum k h hk σ I) :=
134-  ((measurable_refl σ).comp measurable_subtype_coe).subtype_mk
135-
136-/-- The reflection of a stratum as a measurable equivalence. -/
137:def reflStratumEquiv (σ : CoordSign d) (I : Finset (Fin d)) :
138-    (geometry d k h hk).Stratum I ≃ᵐ (geometry d k h hk).Stratum I :=
139-  MeasurableEquiv.ofInvolutive (reflStratum k h hk σ I) (reflStratum_reflStratum k h hk σ I)
140-    (measurable_reflStratum k h hk σ I)
141-
142:theorem reflStratumEquiv_apply (σ : CoordSign d) (I : Finset (Fin d))
143-    (s : (geometry d k h hk).Stratum I) :
144-    reflStratumEquiv k h hk σ I s = reflStratum k h hk σ I s := rfl
145-
146-/-- ★ **Tubular compatibility**: `R_σ (Φ_I s v) = Φ_I (R_σ s) (L_σ v)`. -/
147:theorem refl_Φ (σ : CoordSign d) (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I)
148-    (v : normalSpace d I) :
149-    refl σ ((normalData d k h hk).Φ I s v) =
150-      (normalData d k h hk).Φ I (reflStratum k h hk σ I s) (reflNormal σ I v) := by
151-  funext i
152-  change sgn σ i * (s.1 i + (v : Amb d).ofLp i) =
--
161:theorem normalDifferential_comp_refl (φ : (Fin d → ℝ) → ℝ) (σ : CoordSign d) (I : Finset (Fin d))
162-    (s : (geometry d k h hk).Stratum I) (r : ℕ) :
163-    (normalData d k h hk).normalDifferential (φ ∘ refl σ) I s r =
164-      ((normalData d k h hk).normalDifferential φ I (reflStratum k h hk σ I s)
165-        r).compContinuousLinearMap
166-        fun _ => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I) := by
--
183:noncomputable def jetPull (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) :
184-    JetForm (normalSpace d I) r →L[ℝ] JetForm (normalSpace d I) r :=
185-  ContinuousMultilinearMap.compContinuousLinearMapL
186-    fun _ : Fin r => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I)
187-
188:theorem jetPull_apply (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
189-    (J : JetForm (normalSpace d I) r) :
190-    jetPull σ I r J = J.compContinuousLinearMap
191-      fun _ => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I) := rfl
192-
193-/-- The transported moment tensor `B ∘ P_σ`. -/
194:noncomputable def reflTensor (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
195-    (B : MomentTensor (normalSpace d I) r) : MomentTensor (normalSpace d I) r :=
196-  B.comp (jetPull σ I r)
197-
198:theorem reflTensor_pair (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
199-    (B : MomentTensor (normalSpace d I) r) (J : JetForm (normalSpace d I) r) :
200-    (reflTensor σ I r B).pair J = B.pair (jetPull σ I r J) := rfl
201-
202-/-- **The transported moment field** `(R_σ)_* B (t) = B (R_σ t) ∘ P_σ`. -/
203:noncomputable def reflField (σ : CoordSign d) (B : (normalData d k h hk).MomentCoefficientField) :
204-    (normalData d k h hk).MomentCoefficientField := fun I r q t =>
205-  reflTensor σ I r (B I r q (reflStratum k h hk σ I t))
206-
207-/-- ★ **The pairing identity**: the transported field at `t` paired with the jets of `φ` at `t`
208-equals the field at `R_σ t` paired with the jets of `φ ∘ R_σ` at `R_σ t`. -/
209:theorem reflField_pair (B : (normalData d k h hk).MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ)
210-    (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) (q : PowerLogIndex)
211-    (t : (geometry d k h hk).Stratum I) :
212-    (reflField k h hk σ B I r q t).pair ((normalData d k h hk).normalDifferential φ I t r) =
213-      (B I r q (reflStratum k h hk σ I t)).pair
214-        ((normalData d k h hk).normalDifferential (φ ∘ refl σ) I (reflStratum k h hk σ I t) r) := by
--
221:noncomputable def reflMeasure (σ : CoordSign d)
222-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) :
223-    ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I) := fun I =>
224-  (ν I).map (reflStratumEquiv k h hk σ I)
225-
226:theorem isFiniteMeasure_reflMeasure (σ : CoordSign d)
227-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
228-    [∀ I, IsFiniteMeasure (ν I)] (I : Finset (Fin d)) :
229-    IsFiniteMeasure (reflMeasure k h hk σ ν I) :=
230-  Measure.isFiniteMeasure_map _ _
231-
232:theorem integral_reflMeasure (σ : CoordSign d)
233-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
234-    (f : (geometry d k h hk).Stratum I → ℝ) :
235-    ∫ t, f t ∂reflMeasure k h hk σ ν I = ∫ s, f (reflStratum k h hk σ I s) ∂ν I :=
236-  integral_map_equiv _ _
237-
238:theorem ae_reflMeasure_iff (σ : CoordSign d)
239-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
240-    {P : (geometry d k h hk).Stratum I → Prop} (hP : MeasurableSet {t | P t}) :
241-    (∀ᵐ (t : (geometry d k h hk).Stratum I) ∂reflMeasure k h hk σ ν I, P t) ↔
242-      ∀ᵐ (s : (geometry d k h hk).Stratum I) ∂ν I, P (reflStratum k h hk σ I s) :=
243-  ae_map_iff (measurable_reflStratum k h hk σ I).aemeasurable hP
--
246:theorem ae_reflMeasure_mem_orthantBox (a : ℝ) (σ : CoordSign d)
247-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
248-    (hν : ∀ᵐ (s : (geometry d k h hk).Stratum I) ∂ν I, (s : Fin d → ℝ) ∈ piBox d (Icc 0 a)) :
249-    ∀ᵐ (t : (geometry d k h hk).Stratum I) ∂reflMeasure k h hk σ ν I,
250-      (t : Fin d → ℝ) ∈ orthantBox σ a := by
251-  rw [ae_reflMeasure_iff k h hk σ ν I
--
260:theorem expansionCoefficient_reflMeasure (σ : CoordSign d)
261-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
262-    (B : (normalData d k h hk).MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) :
263-    (normalData d k h hk).expansionCoefficient (reflMeasure k h hk σ ν) (reflField k h hk σ B) φ q =
264-      (normalData d k h hk).expansionCoefficient ν B (φ ∘ refl σ) q := by
265-  unfold ResolvedNormalData.expansionCoefficient
--
277:theorem hasCoordFreeExpansion_refl (a : ℝ) (σ : CoordSign d)
278-    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
279-    (B : (normalData d k h hk).MomentCoefficientField) (spec : ℝ → Finset PowerLogIndex)
280-    (ϕ φ : (Fin d → ℝ) → ℝ)
281-    (hexp : (normalData d k h hk).HasCoordFreeExpansion ν B spec (piBox d (Icc 0 a)) (phase d k)
282-      (ϕ ∘ refl σ) (φ ∘ refl σ)) :
```

### SignedBoxPackets.lean (CCCXXXVI): packet and pullback
```lean
structure HolomorphicSignedBoxExtension (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the complex neighbourhood -/
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc (-a) a), complexify w ∈ Ω
  /-- the holomorphic extensions -/
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re

namespace HolomorphicSignedBoxExtension

variable {a} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension a ϕ φ)

/-- ★ **Pullback along a reflection**: the packet of `(ϕ ∘ R_σ, φ ∘ R_σ)` over the positive box, on
`R_σ⁻¹ Ω` with the extensions `H ∘ R_σ`. -/
def pullback (σ : CoordSign d) : HolomorphicBoxExtension a (ϕ ∘ refl σ) (φ ∘ refl σ) where
  Ω := reflC σ ⁻¹' A.Ω
  isOpen_Ω := A.isOpen_Ω.preimage (continuous_reflC σ)
  box_subset := fun w hw => by
    rw [mem_preimage, ← complexify_refl]
    exact A.box_subset _ (refl_mem_signedBox hw)
  Hϕ := A.Hϕ ∘ reflC σ
  Hφ := A.Hφ ∘ reflC σ
  holϕ := A.holϕ.comp (differentiable_reflC σ).differentiableOn (mapsTo_preimage _ _)
  holφ := A.holφ.comp (differentiable_reflC σ).differentiableOn (mapsTo_preimage _ _)
  eqϕ := fun w hw => by
    have hw' : complexify (refl σ w) ∈ A.Ω := by rwa [complexify_refl]
    simpa [Function.comp, complexify_refl] using A.eqϕ (refl σ w) hw'
  eqφ := fun w hw => by
    have hw' : complexify (refl σ w) ∈ A.Ω := by rwa [complexify_refl]
    simpa [Function.comp, complexify_refl] using A.eqφ (refl σ w) hw'

theorem pullback_nonneg (hϕ0 : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ ϕ w) (σ : CoordSign d) :
    ∀ w ∈ piBox d (Icc 0 a), 0 ≤ (ϕ ∘ refl σ) w :=
  fun _ hw => hϕ0 _ (refl_mem_signedBox hw)

end HolomorphicSignedBoxExtension
248:theorem exists_delta_common {ι : Type*} [Finite ι] [Nonempty ι] (ρ : ι → ℝ)
249-    (hρ : ∀ j, 0 < ρ j) :
250-    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
251-      ∀ (j : ι) (i : Fin d), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ j := by
252-  cases nonempty_fintype ι
253-  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
254-  have hmin : 0 < Finset.univ.inf' hne ρ := by
255-    rw [Finset.lt_inf'_iff]
256-    exact fun j _ => hρ j
--
267:theorem hasCoordFreeExpansion_local_at :
268-    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
269-      (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).stratumMeasure
270-      (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).field
271-      (spectrumLe (commonQ (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).cores.k) (d - 1))
272-      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
273-  have h := hasCoordFreeExpansion_collar_of_nonneg_on k hk a δ A.measurable_priorRep
274-    A.measurable_obsRep A.integrable_obsRep hδ hd ha hδa (A.priorRep_nonneg_on hϕ0W)
275-    fun I => (A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)
```

### CertificateSeriesRegularity.lean (CCCXXXIX) statements
```lean
38:theorem transportTensor_pair' (ψ : (Fin d → ℝ) → ℝ) {J : Fin C.M} {I : Finset R.Component}
39-    (hJ : C.strat J = I) (r : ℕ)
40-    (T : ∀ s : R.Stratum (C.strat J), MomentTensor (D.N (C.strat J) s) r) (s : R.Stratum I) :
41-    (C.transportTensor hJ r T s).pair (D.normalDifferential ψ I s r) =
42-      (T (C.ofStratum hJ s)).pair (D.normalDifferential ψ (C.strat J) (C.ofStratum hJ s) r) := by
43-  subst hJ
--
54:theorem chartTensorExt_pair_congr (J : Fin C.M) (s : R.Stratum (C.strat J)) (r : ℕ)
55-    (q : PowerLogIndex) :
56-    (Cc.chartTensorExt J s r q).pair (D.normalDifferential ψ (C.strat J) s r) =
57-      (Cc.chartTensorExt J s r q).pair (D.normalDifferential φ (C.strat J) s r) := by
58-  by_cases hs : s ∈ C.base J
59-  · rw [D.normalDifferential_congr (C.strat J) s (hψ J ⟨s, hs⟩) r]
--
66:theorem field_pair_congr (I : Finset R.Component) (r : ℕ) (q : PowerLogIndex) (s : R.Stratum I) :
67-    (Cc.field I r q s).pair (D.normalDifferential ψ I s r) =
68-      (Cc.field I r q s).pair (D.normalDifferential φ I s r) := by
69-  unfold ResolvedCertificate.CoefficientCertificate.field MomentTensor.pair
70-  rw [sum_apply, sum_apply]
71-  refine Finset.sum_congr rfl fun J _ => ?_
--
84:theorem summable_field_pair_of_germ (I : Finset R.Component) (q : PowerLogIndex)
85-    (s : R.Stratum I) :
86-    Summable fun r : ℕ =>
87-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential ψ I s r) :=
88-  (Cc.summable_field_pair I q s).congr fun r => by rw [Cc.field_pair_congr ψ hψ I r q s]
89-
--
92:theorem integrable_field_series (I : Finset R.Component) (q : PowerLogIndex) :
93-    Integrable (fun s => ∑' r : ℕ,
94-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r))
95-      (C.stratumMeasure I) := by
96-  have heq : (fun s : R.Stratum I => ∑' r : ℕ,
97-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)) =
--
109:theorem integrable_field_series_of_germ (I : Finset R.Component) (q : PowerLogIndex) :
110-    Integrable (fun s => ∑' r : ℕ,
111-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential ψ I s r))
112-      (C.stratumMeasure I) :=
113-  (Cc.integrable_field_series I q).congr (Eventually.of_forall fun s =>
114-    tsum_congr fun r => by rw [Cc.field_pair_congr ψ hψ I r q s])
```

### CCCVIII canonicity (for the regression-check question)
```lean
```
