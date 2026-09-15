/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SmoothStratumApprox
import Grammar.SmoothResolvedResidue
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The stratum measure: an intrinsic positive Radon measure carried by the exact stratum

Units 4–10 of the residue programme (Astra #132). Under the zero-order condition, the positive
linear functional `Λ` on `C_c(X, ℝ)`, `X = U ∖ D_{c+1}` (`SmoothStratumApprox`), is represented
by the Riesz–Markov–Kakutani theorem as integration against a regular Borel measure `ν` on `X`,
the **stratum measure**. It integrates every smooth test function to the `(μ, c−1)` coefficient
(`integral_stratumMeasure_test`), it is carried by the exact stratum `S^μ_c`
(`stratumMeasure_compl_exactStratum`), it represents the coefficient of every observable
vanishing near the deep zero fibre, compactly supported or not (`coeff_eq_integral_stratumMeasure`,
`observableCoeff_eq_integral_stratumMeasure`), it is independent of the transport
(`stratumMeasure_eq_of_transports`), and it is the unique regular measure integrating smooth
tests to the coefficient functional (`eq_stratumMeasure_of_tests`). In normal-crossings
coordinates its integrals are the residue sums of `SmoothResolvedResidue`
(`integral_stratumMeasure_eq_residueSum`); the **weighted residue measure**
`ℛ = ((c−1)!/Γ(μ)) ν` integrates an observable to the bare sum of the multiplicity-weighted
logarithmic residue integrals (`integral_residueMeasure_eq`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold CompactlySupported
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Topology of the stratum open set -/

instance (c : ℕ) : LocallyCompactSpace (Ξ.stratumOpen c) :=
  (Ξ.isOpen_stratumOpen c).locallyCompactSpace

/-- Within `X`, the exact stratum is cut out by the closed depth and resonance filtrations. -/
theorem stratumOpen_inter_exactStratum (μ : ℝ) (c : ℕ) :
    Ξ.stratumOpen c ∩ Ξ.exactStratum μ c =
      Ξ.stratumOpen c ∩ (Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 c ∩ resonanceGE Ξ.R Ξ.hK0 μ c) := by
  ext P
  simp only [mem_inter_iff, exactStratum, mem_ofPred_eq, depthGE, resonanceGE]
  constructor
  · rintro ⟨hX, hZ, hd, hr⟩
    exact ⟨hX, ⟨hZ, hd.ge⟩, hr.ge⟩
  · rintro ⟨hX, ⟨hZ, hd⟩, hr⟩
    have hdle : depth Ξ.R Ξ.hK0 P ≤ c := by
      by_contra h
      exact hX ⟨hZ, show c + 1 ≤ depth Ξ.R Ξ.hK0 P from not_le.1 h⟩
    have hdeq : depth Ξ.R Ξ.hK0 P = c := le_antisymm hdle hd
    refine ⟨hX, hZ, hdeq, le_antisymm ?_ hr⟩
    exact (resonanceCount_le_depth Ξ.R Ξ.hK0 μ P).trans hdle

theorem isClosed_zeroFibre : IsClosed Ξ.zeroFibre := Ξ.isCompact_zeroFibre.isClosed

/-- The complement of the exact stratum inside `X` is open in `U`. -/
theorem isOpen_stratumOpen_diff_exactStratum (μ : ℝ) (c : ℕ) :
    IsOpen (Ξ.stratumOpen c \ Ξ.exactStratum μ c) := by
  have h : Ξ.stratumOpen c \ Ξ.exactStratum μ c =
      Ξ.stratumOpen c \ (Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 c ∩ resonanceGE Ξ.R Ξ.hK0 μ c) := by
    have key := Ξ.stratumOpen_inter_exactStratum μ c
    ext P
    constructor
    · rintro ⟨hX, hP⟩
      refine ⟨hX, fun hC => hP ?_⟩
      have hmem : P ∈ Ξ.stratumOpen c ∩ Ξ.exactStratum μ c := key ▸ ⟨hX, hC⟩
      exact hmem.2
    · rintro ⟨hX, hP⟩
      refine ⟨hX, fun hE => hP ?_⟩
      have hmem : P ∈ Ξ.stratumOpen c ∩
          (Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 c ∩ resonanceGE Ξ.R Ξ.hK0 μ c) := key ▸ ⟨hX, hE⟩
      exact hmem.2
  rw [h]
  exact (Ξ.isOpen_stratumOpen c).sdiff
    ((Ξ.isClosed_zeroFibre.inter (isClosed_depthGE Ξ.R Ξ.hK0 Ξ.hKc c)).inter
      (isClosed_resonanceGE Ξ.R Ξ.hK0 Ξ.hKc μ c))

/-- ★ **Cutoffs with prescribed support**: a smooth test function equal to `1` on a compact set
`K`, with values in `[0, 1]` and support inside a given open `V ⊆ X` containing `K`. -/
theorem exists_cutoff_subset (c : ℕ) {K V : Set Ξ.R.U} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVX : V ⊆ Ξ.stratumOpen c) :
    ∃ χ : Ξ.R.U → ℝ, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ ∧ Ξ.IsTest c χ ∧ tsupport χ ⊆ V ∧
      (∀ P ∈ K, χ P = 1) ∧ ∀ P, χ P ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨f, hf1, hf0, hf01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin d → ℝ) (n := ⊤) hK.isClosed hKL
  have hsupp : Function.support f ⊆ L := fun P hP => by_contra fun h => hP (hf0 P h)
  have hts : tsupport f ⊆ L := closure_minimal hsupp hLc.isClosed
  refine ⟨f, f.contMDiff, ⟨hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans (hLV.trans hVX)⟩, hts.trans hLV, fun P hP => hf1.self_of_nhdsSet P hP, hf01⟩

/-! ### The stratum measure -/

/-- ★★★ **The stratum measure** `ν^μ_c` on `X = U ∖ D_{c+1}`: the Riesz measure of the positive
linear functional `Λ`. -/
noncomputable def stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  RealRMK.rieszMeasure (Ξ.Λ Y hc hzero)

instance {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    (Ξ.stratumMeasure Y hc hzero).Regular :=
  RealRMK.regular_rieszMeasure _

/-- The stratum measure integrates every element of `C_c(X, ℝ)` to `Λ`. -/
theorem integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f : C_c(Ξ.stratumOpen c, ℝ)) :
    ∫ x, f x ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.Λ Y hc hzero f :=
  RealRMK.integral_rieszMeasure _ f

/-- ★★★ **Smooth integral representation**: the stratum measure integrates every smooth test
function to the `(μ, c−1)` coefficient of the corresponding observable. -/
theorem integral_stratumMeasure_test {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.T Y μ c G hG := by
  rw [← Ξ.Λ_toCc Y hc hzero hG hGt]
  exact Ξ.integral_stratumMeasure Y hc hzero (Ξ.toCc c hG hGt)

/-! ### Support -/

/-- ★★★ **The stratum measure is carried by the exact stratum**: the complement of `S^μ_c` in
`X` is a null set. -/
theorem stratumMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0 := by
  set ν := Ξ.stratumMeasure Y hc hzero with hν
  have hopen : IsOpen (Subtype.val ⁻¹' Ξ.exactStratum μ c : Set (Ξ.stratumOpen c))ᶜ := by
    have : (Subtype.val ⁻¹' Ξ.exactStratum μ c : Set (Ξ.stratumOpen c))ᶜ =
        Subtype.val ⁻¹' (Ξ.stratumOpen c \ Ξ.exactStratum μ c) := by
      ext x
      simp only [mem_compl_iff, mem_preimage, Set.mem_sdiff]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [this]
    exact (Ξ.isOpen_stratumOpen_diff_exactStratum μ c).preimage continuous_subtype_val
  rw [Measure.Regular.innerRegular.measure_eq_iSup hopen]
  refine le_antisymm (iSup₂_le fun K hKV => iSup_le fun hK => ?_) bot_le
  have hKc : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hKV' : Subtype.val '' K ⊆ Ξ.stratumOpen c \ Ξ.exactStratum μ c := by
    rintro P ⟨x, hx, rfl⟩
    exact ⟨x.2, hKV hx⟩
  obtain ⟨χ, hχ, hχt, hχV, hχ1, hχ01⟩ := Ξ.exists_cutoff_subset c hKc
    (Ξ.isOpen_stratumOpen_diff_exactStratum μ c) hKV' sdiff_subset
  have hTχ : Ξ.T Y μ c χ hχ = 0 :=
    Ξ.T_eq_zero_of_eqOn_zero Y hc hzero hχ hχt fun P hP =>
      image_eq_zero_of_notMem_tsupport fun h => (hχV h).2 hP
  have hint : ∫ x, χ x.1 ∂ν = 0 := by
    rw [hν, Ξ.integral_stratumMeasure_test Y hc hzero hχ hχt, hTχ]
  have hle : ν.real K ≤ ∫ x, χ x.1 ∂ν := by
    rw [← integral_indicator_one hK.measurableSet]
    refine integral_mono ?_ ?_ fun x => ?_
    · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    · exact (Ξ.toCc c hχ hχt).continuous.integrable_of_hasCompactSupport
        (Ξ.toCc c hχ hχt).hasCompactSupport
    · by_cases hx : x ∈ K
      · simp [hx, hχ1 x.1 ⟨x, hx, rfl⟩]
      · simp [hx, (hχ01 x.1).1]
  have hreal : ν.real K = 0 := le_antisymm (hint ▸ hle) measureReal_nonneg
  exact ((measureReal_eq_zero_iff hK.measure_lt_top.ne).1 hreal).le

/-! ### Localisation: observables vanishing near the deep zero fibre -/

/-- ★★★ **Representation for observables vanishing near the deep zero fibre**, compactly supported
in `X` or not: the `(μ, c−1)` coefficient is the integral against the stratum measure. -/
theorem coeff_withF_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) := by
  obtain ⟨O, hO, hDO, hGO⟩ := eventually_nhdsSet_iff_exists.1 hG0
  have hK0c : IsCompact (Ξ.zeroFibre \ O) := Ξ.isCompact_zeroFibre.diff hO
  have hK0X : Ξ.zeroFibre \ O ⊆ Ξ.stratumOpen c := fun P hP hD => hP.2 (hDO hD)
  obtain ⟨χ, hχ, hχt, hχ1, hχ01⟩ := Ξ.exists_cutoff c hK0c hK0X
  have hGχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P * χ P) := hG.mul hχ
  have hGχt : Ξ.IsTest c (fun P => G P * χ P) :=
    ⟨hχt.1.mul_left, tsupport_mul_subset_right.trans hχt.2⟩
  have heq : EqOn G (fun P => G P * χ P) (Ξ.exactStratum μ c) := fun P hP => by
    by_cases hPO : P ∈ O
    · simp [hGO P hPO]
    · simp [hχ1 P ⟨hP.1, hPO⟩]
  rw [Ξ.coeff_eq_of_eqOn_exactStratum Y hc hzero hG hGχ hG0 hGχt.eventually_zero heq]
  change Ξ.T Y μ c _ hGχ = _
  rw [← Ξ.integral_stratumMeasure_test Y hc hzero hGχ hGχt]
  refine integral_congr_ae ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ (Ξ.stratumMeasure_compl_exactStratum Y hc hzero)
  intro x hx hxE
  exact hx (heq hxE).symm

/-- The coefficient of `Ξ` itself, when `F` vanishes near the deep zero fibre. -/
theorem coeff_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) :
    Ξ.coeff Y μ (c - 1) = ∫ x, Ξ.F x.1 ∂(Ξ.stratumMeasure Y hc hzero) :=
  Ξ.coeff_withF_eq_integral_stratumMeasure Y hc hzero Ξ.F_smooth hF

/-- ★★★ **Euclidean corollary**: the `(μ, c−1)` coefficient of a base observable vanishing near
the image of the deep zero fibre is the integral of its pull-back against the stratum measure. -/
theorem observableCoeff_eq_integral_stratumMeasure {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), f (Ξ.R.gv P) = 0) :
    (Ξ.X Y).observableCoeff μ (c - 1) f hf =
      ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.stratumMeasure Y hc hzero) := by
  rw [← Ξ.coeff_comp_gv Y hf μ (c - 1)]
  exact Ξ.coeff_withF_eq_integral_stratumMeasure Y hc hzero (Ξ.contMDiff_comp_gv hf) h0

/-! ### The residue formula -/

/-- ★★★ **Stratum-measure integrals are residue sums**: in normal-crossings coordinates, the
integral of an observable vanishing near the deep zero fibre against the stratum measure is
`Γ(μ)/(c−1)!` times the sum over simple faces of the `d log`-residue integrals. -/
theorem integral_stratumMeasure_eq_residueSum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = (Ξ.withF G hG).residueSum Y μ c := by
  rw [← Ξ.coeff_withF_eq_integral_stratumMeasure Y hc hzero hG hG0]
  exact (Ξ.withF G hG).coeff_eq_residueSum Y hc hzero hG0

/-! ### The weighted residue measure -/

/-- ★★★ **The weighted residue measure** `ℛ^μ_c = ((c−1)!/Γ(μ)) · ν^μ_c`. -/
noncomputable def residueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal ((c - 1).factorial / Real.Gamma μ) • Ξ.stratumMeasure Y hc hzero

theorem residueMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.residueMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0 := by
  unfold residueMeasure
  rw [Measure.smul_apply, Ξ.stratumMeasure_compl_exactStratum Y hc hzero, smul_zero]

theorem integral_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) (g : Ξ.stratumOpen c → ℝ) :
    ∫ x, g x ∂(Ξ.residueMeasure Y hc hzero) =
      ((c - 1).factorial / Real.Gamma μ) * ∫ x, g x ∂(Ξ.stratumMeasure Y hc hzero) := by
  unfold residueMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal
    (div_nonneg (Nat.cast_nonneg _) (Real.Gamma_pos_of_pos hμ).le), smul_eq_mul]

/-- ★★★ **The weighted residue measure integrates an observable to the bare residue sum**:
`∫ G dℛ = Σ_I ∫ Σ_{simple faces J} (∏_{j∈J} (2k_j)⁻¹) ∫ A ∏ w^h (∏ w^{2k})^{−μ}`. -/
theorem integral_residueMeasure_eq {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∫ x, G x.1 ∂(Ξ.residueMeasure Y hc hzero) =
      ∑ I, ∫ s, (Ξ.withF G hG).pieceResidueSum Y I s μ c
        ∂(((Ξ.withF G hG).decomp Y).chart I).ν := by
  rw [Ξ.integral_residueMeasure Y hμ hc hzero,
    Ξ.integral_stratumMeasure_eq_residueSum Y hc hzero hG hG0]
  unfold residueSum residueConst
  have hΓ := Real.Gamma_pos_of_pos hμ
  have hfac : (0 : ℝ) < (c - 1).factorial := Nat.cast_pos.2 (Nat.factorial_pos _)
  field_simp

/-! ### Naturality -/

theorem Λ₀_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) (μ : ℝ) (c : ℕ)
    (f : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.Λ₀ Y μ c f = Ξ.Λ₀ Y' μ c f := by
  unfold Λ₀
  congr 1
  funext n
  exact Ξ.T_eq_of_transports Y Y' μ c _

/-- ★★ **Transport independence**: the stratum measure does not depend on the chosen resolved
core transport. -/
theorem stratumMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) {μ : ℝ}
    {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero = Ξ.stratumMeasure Y' hc hzero := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  rw [Ξ.integral_stratumMeasure Y hc hzero f, Ξ.integral_stratumMeasure Y' hc hzero f]
  exact Ξ.Λ₀_eq_of_transports Y Y' μ c f

/-! ### Uniqueness -/

/-- The preimage in `X` of a compact subset of `X ⊆ U` is compact. -/
theorem isCompact_preimage_val {c : ℕ} {L : Set Ξ.R.U} (hL : IsCompact L)
    (hLX : L ⊆ Ξ.stratumOpen c) : IsCompact (Subtype.val ⁻¹' L : Set (Ξ.stratumOpen c)) := by
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hLX]
  exact hL

/-- ★★★ **Uniqueness**: a regular measure on `X` integrating every smooth test function to the
coefficient functional is the stratum measure. -/
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  rw [Ξ.integral_stratumMeasure Y hc hzero f]
  change _ = Ξ.Λ₀ Y μ c f
  refine tendsto_nhds_unique ?_ (Ξ.tendsto_T_approx Y hc hzero f)
  have hrew : ∀ n, Ξ.T Y μ c (Ξ.approx c f n) (Ξ.approx_smooth c f n) =
      ∫ x, Ξ.approx c f n x.1 ∂ν' := fun n => (h _ _ (Ξ.approx_spec c f n).2.1).symm
  refine (tendsto_congr fun n => (hrew n).symm).1 ?_
  set L : Set Ξ.R.U := Ξ.approxL c f ∪ Subtype.val '' tsupport f with hL
  have hLc : IsCompact L := (Ξ.approxL_spec c f).1.union (Ξ.isCompact_image_tsupport c f)
  have hLX : L ⊆ Ξ.stratumOpen c := by
    refine union_subset (Ξ.approxL_spec c f).2.1 ?_
    rintro P ⟨x, -, rfl⟩
    exact x.2
  have hL'c : IsCompact (Subtype.val ⁻¹' L : Set (Ξ.stratumOpen c)) :=
    Ξ.isCompact_preimage_val hLc hLX
  have hint : ∀ n, Integrable (fun x : Ξ.stratumOpen c => Ξ.approx c f n x.1) ν' := fun n =>
    Continuous.integrable_of_hasCompactSupport
      (Ξ.toCc c (Ξ.approx_smooth c f n) (Ξ.approx_spec c f n).2.1).continuous
      (Ξ.toCc c (Ξ.approx_smooth c f n) (Ξ.approx_spec c f n).2.1).hasCompactSupport
  have hfint : Integrable (fun x => f x) ν' :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hbound : ∀ n : ℕ, ‖(∫ x, Ξ.approx c f n x.1 ∂ν') - ∫ x, f x ∂ν'‖ ≤
      1 / ((n : ℝ) + 1) * ν'.real (Subtype.val ⁻¹' L) := by
    intro n
    rw [← integral_sub (hint n) hfint]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Subtype.val ⁻¹' L) ?_]
    · refine norm_setIntegral_le_of_norm_le_const hL'c.measure_lt_top fun x _ => ?_
      rw [Real.norm_eq_abs]
      have := (Ξ.approx_spec c f n).2.2.2 x.1
      rwa [Ξ.ext_val] at this
    · intro x hx
      have h1 : Ξ.approx c f n x.1 = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
        exact Or.inl ((Ξ.approx_spec c f n).2.2.1 hmem)
      have h2 : f x = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
        exact Or.inr ⟨x, hmem, rfl⟩
      rw [h1, h2, sub_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ν'.real (Subtype.val ⁻¹' L)) atTop
      (𝓝 0) := by
    have := tendsto_one_div_succ.mul_const (ν'.real (Subtype.val ⁻¹' L))
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

end ResolvedData

end SmoothEngine

end Grammar
