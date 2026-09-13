/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeCertificate
import Grammar.BlowUpCubeSupport

/-!
# Transport fidelity of the genuine blow-up certificate (B5)

The certificate `cubeCert` on the genuine blow-up (CCCLXVII) expands the cube integral with the
cut-off representatives `pM`, `FM`; by congruence (the stratum measures live on the exceptional
divisor, over `0`, an interior point of the cube) it expands the ORIGINAL integral
`∫_{[−1,1]^d} F p e^{−nK}` (`cube_hasCoordFreeExpansion_blowUp_original`). Both this expansion and
the landed chart-model expansion `cube_hasExpansion` (CCCXLVII) are finite log-free power sums
approximating the same function to every order, so their coefficients agree at every index
(`coeff_eq_of_isLittleO_two_spectra`): ★★★ `blowUpCoefficient_eq_cubeCoefficient`. Hence the
coordinate-free coefficients of the genuine geometry inherit the leading value `π^{d/2} F(0) p(0)`
and the vanishing below `d/2` of CCCXLVIII.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Uniqueness of a log-free expansion across two spectra -/

open scoped Classical in
theorem exponent_injOn_union_spectrumLe_zero {Q Q' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (A : ℝ) :
    Set.InjOn PowerLogIndex.exponent
      ((spectrumLe Q 0 A ∪ spectrumLe Q' 0 A : Finset PowerLogIndex) : Set PowerLogIndex) := by
  have hlog : ∀ q ∈ spectrumLe Q 0 A ∪ spectrumLe Q' 0 A, q.logDegree = 0 := fun q hq => by
    rcases Finset.mem_union.1 hq with h | h
    · exact ((mem_spectrumLe_zero_iff hQ A q).1 h).2.1
    · exact ((mem_spectrumLe_zero_iff hQ' A q).1 h).2.1
  intro q hq q' hq' h
  have h1 := hlog q hq
  have h2 := hlog q' hq'
  cases q; cases q'
  simp only at h h1 h2
  subst h h1 h2
  rfl

open scoped Classical in
theorem sum_mul_eq_sum_union {S T : Finset PowerLogIndex} (c f : PowerLogIndex → ℝ) :
    ∑ q ∈ S, c q * f q = ∑ q ∈ S ∪ T, (if q ∈ S then c q else 0) * f q :=
  calc ∑ q ∈ S, c q * f q = ∑ q ∈ S, (if q ∈ S then c q else 0) * f q :=
        Finset.sum_congr rfl fun q hq => by rw [if_pos hq]
    _ = ∑ q ∈ S ∪ T, (if q ∈ S then c q else 0) * f q :=
        Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [if_neg hq, zero_mul]

open scoped Classical in
/-- ★★ **Two log-free expansions of one function agree coefficientwise**: if
`Z − ∑_{S} c_q q(n) = o(n^{−A})` and `Z − ∑_{S'} c'_q q(n) = o(n^{−A})` for the log-free
spectra `S = spectrumLe Q 0 A`, `S' = spectrumLe Q' 0 A`, then the coefficient systems (extended
by `0`) agree on `S ∪ S'`. -/
theorem coeff_eq_of_isLittleO_two_spectra {Q Q' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') {A : ℝ}
    {Z : ℝ → ℝ} {c c' : PowerLogIndex → ℝ}
    (h : (fun n : ℝ => Z n - ∑ q ∈ spectrumLe Q 0 A, c q * q.scale n) =o[atTop]
      fun n : ℝ => n ^ (-A))
    (h' : (fun n : ℝ => Z n - ∑ q ∈ spectrumLe Q' 0 A, c' q * q.scale n) =o[atTop]
      fun n : ℝ => n ^ (-A)) :
    ∀ q ∈ spectrumLe Q 0 A ∪ spectrumLe Q' 0 A,
      (if q ∈ spectrumLe Q 0 A then c q else 0) =
        (if q ∈ spectrumLe Q' 0 A then c' q else 0) := by
  set S := spectrumLe Q 0 A with hS
  set S' := spectrumLe Q' 0 A with hS'
  have hlog : ∀ q ∈ S ∪ S', q.logDegree = 0 := fun q hq => by
    rcases Finset.mem_union.1 hq with h | h
    · exact ((mem_spectrumLe_zero_iff hQ A q).1 h).2.1
    · exact ((mem_spectrumLe_zero_iff hQ' A q).1 h).2.1
  have hle : ∀ q ∈ S ∪ S', q.exponent ≤ A := fun q hq => by
    rcases Finset.mem_union.1 hq with h | h
    · exact ((mem_spectrumLe_zero_iff hQ A q).1 h).2.2
    · exact ((mem_spectrumLe_zero_iff hQ' A q).1 h).2.2
  have h3 := h'.sub h
  have key := coeff_eq_zero_of_isLittleO_powSum (S := S ∪ S') (e := PowerLogIndex.exponent)
    (c := fun q => (if q ∈ S then c q else 0) - (if q ∈ S' then c' q else 0))
    (exponent_injOn_union_spectrumLe_zero hQ hQ' A) hle (h3.congr_left fun n => ?_)
  · intro q hq
    exact sub_eq_zero.1 (key q hq)
  · rw [sub_sub_sub_cancel_left, sum_mul_eq_sum_union (T := S') c (fun q => q.scale n),
      sum_mul_eq_sum_union (T := S) c' (fun q => q.scale n), Finset.union_comm S' S,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [scale_of_logDegree_zero (hlog q hq)]
    ring

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox CoordModel

variable {d : ℕ} [NeZero d] {p F : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension 1 p F)
  (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

/-! ### The certificate expands the original packet -/

theorem cubeCert_strat (k : Fin (cubeCert A hp0).M) :
    (cubeCert A hp0).strat k = Finset.univ := rfl

theorem cubeCert_n (k : Fin (cubeCert A hp0).M) : (cubeCert A hp0).n k = 0 := rfl

theorem commonD_cubeCert : commonD (cubeCert A hp0).n = 0 :=
  le_antisymm (Finset.sup_le fun k _ => le_of_eq (cubeCert_n A hp0 k)) (Nat.zero_le _)

/-- Every stratum other than the exceptional divisor carries the zero measure. -/
theorem cubeCert_stratumMeasure_of_ne {I : Finset (blowUpGeometry d).Component}
    (hI : I ≠ Finset.univ) : (cubeCert A hp0).stratumMeasure I = 0 := by
  unfold ResolvedCertificate.stratumMeasure
  exact Finset.sum_eq_zero fun k _ =>
    dif_neg fun h => hI (h.symm.trans (cubeCert_strat A hp0 k))

omit [NeZero d] in
/-- Points of the divisor stratum project to the origin. -/
theorem π_eq_zero_of_mem_stratum_univ (s : (blowUpGeometry d).Stratum Finset.univ) :
    π (s : BlowUpSpace d) = 0 :=
  (mem_E_iff _ ()).1 ((s.2 ()).2 (Finset.mem_univ ()))

omit [NeZero d] in
theorem cube_mem_nhds_zero : cube d ∈ 𝓝 (0 : Fin d → ℝ) := by
  rw [cube_eq_piBox]
  exact set_pi_mem_nhds finite_univ fun i _ => Icc_mem_nhds (by simp) (by simp)

omit [NeZero d] in
/-- The cut-off observable has the germ of `F` at every point of the divisor stratum. -/
theorem FM_eventuallyEq_F (s : (blowUpGeometry d).Stratum Finset.univ) :
    FM A =ᶠ[𝓝 ((blowUpGeometry d).π (s : BlowUpSpace d))] F := by
  rw [blowUpGeometry_π, π_eq_zero_of_mem_stratum_univ s]
  filter_upwards [cube_mem_nhds_zero (d := d)] with x hx
  exact FM_of_mem A hx

/-- The germ hypothesis of the congruence theorem: a.e. on every stratum measure, the cut-off
observable has the germ of `F`. -/
theorem FM_germ (I : Finset (blowUpGeometry d).Component) :
    ∀ᵐ (s : (blowUpGeometry d).Stratum I) ∂(cubeCert A hp0).stratumMeasure I,
      FM A =ᶠ[𝓝 ((blowUpGeometry d).π (s : BlowUpSpace d))] F := by
  by_cases hI : I = Finset.univ
  · subst hI
    exact Eventually.of_forall fun s => FM_eventuallyEq_F A s
  · rw [cubeCert_stratumMeasure_of_ne A hp0 hI, ae_zero]
    exact Filter.eventually_bot

/-- ★★★ **The coordinate-free expansion of the ORIGINAL cube integral on the genuine blow-up**:
`∫_{[−1,1]^d} F p e^{−nK}` has the expansion of CCCIII with the certificate `cubeCert`, the
observable `F` and the prior `p` themselves. -/
theorem cube_hasCoordFreeExpansion_blowUp_original :
    (blowUpNormalData d).HasCoordFreeExpansion (cubeCert A hp0).stratumMeasure
      (cubeCoeffCert A hp0).field
      (spectrumLe (commonQ (cubeCert A hp0).cores.k) (commonD (cubeCert A hp0).n)) (cube d) K
      p F :=
  ResolvedNormalData.HasCoordFreeExpansion.congr
    (by rw [cube_eq_piBox]; exact measurableSet_piBox d _ measurableSet_Icc)
    (fun w hw => by rw [FM_of_mem A hw, pM_of_mem A hw]) (FM_germ A hp0)
    (cube_hasCoordFreeExpansion_blowUp A hp0)

/-! ### Scalar canonicity: the genuine coefficients are the cube coefficients -/

/-- The coordinate-free coefficients of the genuine blow-up certificate, for the original
observable `F`. -/
noncomputable def blowUpCoefficient (q : PowerLogIndex) : ℝ :=
  (blowUpNormalData d).expansionCoefficient (cubeCert A hp0).stratumMeasure
    (cubeCoeffCert A hp0).field F q

/-- The genuine coefficients may be computed with the cut-off observable of the certificate. -/
theorem blowUpCoefficient_eq_FM (q : PowerLogIndex) :
    blowUpCoefficient A hp0 q = (blowUpNormalData d).expansionCoefficient
      (cubeCert A hp0).stratumMeasure (cubeCoeffCert A hp0).field (FM A) q :=
  ((blowUpNormalData d).expansionCoefficient_congr _ _ (FM_germ A hp0) q).symm

theorem blowUpCoefficient_eq_zero_of_not_lattice {q : PowerLogIndex}
    (hμ : ∀ m : ℕ, q.exponent ≠ (m : ℝ) / commonQ (cubeCert A hp0).cores.k) :
    blowUpCoefficient A hp0 q = 0 := by
  rw [blowUpCoefficient_eq_FM, (cubeCoeffCert A hp0).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_not_lattice _ _ _ _ _ _ (cubeCert A hp0).cores.k_pos
    (cubeCert A hp0).β_pos (cubeCert A hp0).cores.b_pos hμ _

theorem blowUpCoefficient_eq_zero_of_logDegree_pos {q : PowerLogIndex} (hj : 0 < q.logDegree) :
    blowUpCoefficient A hp0 q = 0 := by
  rw [blowUpCoefficient_eq_FM, (cubeCoeffCert A hp0).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_lt _ _ _ _ _ _ (by rw [commonD_cubeCert]; exact hj)

omit [NeZero d] in
theorem pieceCert_n (β : Fin d) (σ : CoordSign d) (k : Fin (pieceCert β A σ hp0).M) :
    (pieceCert β A σ hp0).n k = 0 := rfl

omit [NeZero d] in
theorem commonD_pieceCert (β : Fin d) (σ : CoordSign d) :
    commonD (pieceCert β A σ hp0).n = 0 :=
  le_antisymm (Finset.sup_le fun k _ => le_of_eq (pieceCert_n A hp0 β σ k)) (Nat.zero_le _)

omit [NeZero d] in
theorem pieceCoefficient_eq_zero_of_logDegree_pos (β : Fin d) (σ : CoordSign d)
    {q : PowerLogIndex} (hj : 0 < q.logDegree) : pieceCoefficient β A σ hp0 q = 0 := by
  unfold pieceCoefficient
  rw [(pieceCoeff β A σ hp0).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_lt _ _ _ _ _ _ (by rw [commonD_pieceCert]; exact hj)

omit [NeZero d] in
theorem cubeCoefficient_eq_zero_of_logDegree_pos {q : PowerLogIndex} (hj : 0 < q.logDegree) :
    cubeCoefficient A hp0 q = 0 :=
  Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun σ _ =>
    pieceCoefficient_eq_zero_of_logDegree_pos A hp0 β σ hj

/-- The genuine expansion, as a log-free power sum with the blow-up coefficients. -/
theorem cube_isLittleO_blowUp (A' : ℝ) :
    (fun n : ℝ => (∫ x in cube d, F x * p x * Real.exp (-n * K x)) -
      ∑ q ∈ spectrumLe (commonQ (cubeCert A hp0).cores.k) 0 A',
        blowUpCoefficient A hp0 q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-A') := by
  have h := cube_hasCoordFreeExpansion_blowUp_original A hp0 A'
  rw [commonD_cubeCert] at h
  exact h

open scoped Classical in
theorem blowUpCoefficient_eq_cubeCoefficient_of_mem {A' : ℝ} {q : PowerLogIndex}
    (hq : q ∈ spectrumLe 2 0 A') : blowUpCoefficient A hp0 q = cubeCoefficient A hp0 q := by
  have h := coeff_eq_of_isLittleO_two_spectra two_pos
    (commonQ_pos _ (cubeCert A hp0).cores.k_pos)
    (Z := fun n : ℝ => ∫ x in cube d, F x * p x * Real.exp (-n * K x))
    (cube_hasExpansion A hp0 A') (cube_isLittleO_blowUp A hp0 A') q (Finset.mem_union_left _ hq)
  rw [if_pos hq] at h
  by_cases hq' : q ∈ spectrumLe (commonQ (cubeCert A hp0).cores.k) 0 A'
  · rw [if_pos hq'] at h
    exact h.symm
  · rw [if_neg hq'] at h
    rw [h]
    refine blowUpCoefficient_eq_zero_of_not_lattice A hp0 fun m hm => hq' ?_
    obtain ⟨-, hj, hle⟩ := (mem_spectrumLe_zero_iff two_pos A' q).1 hq
    exact (mem_spectrumLe_zero_iff (commonQ_pos _ (cubeCert A hp0).cores.k_pos) A' q).2
      ⟨⟨m, hm⟩, hj, hle⟩

open scoped Classical in
theorem blowUpCoefficient_eq_zero_of_not_mem {A' : ℝ} {q : PowerLogIndex}
    (hq : q ∈ spectrumLe (commonQ (cubeCert A hp0).cores.k) 0 A') (hq2 : q ∉ spectrumLe 2 0 A') :
    blowUpCoefficient A hp0 q = 0 := by
  have h := coeff_eq_of_isLittleO_two_spectra two_pos
    (commonQ_pos _ (cubeCert A hp0).cores.k_pos)
    (Z := fun n : ℝ => ∫ x in cube d, F x * p x * Real.exp (-n * K x))
    (cube_hasExpansion A hp0 A') (cube_isLittleO_blowUp A hp0 A') q (Finset.mem_union_right _ hq)
  rwa [if_neg hq2, if_pos hq, eq_comm] at h

/-- ★★★ **Transport fidelity**: at EVERY power–log index the coordinate-free coefficient of the
genuine blow-up certificate equals the landed cube coefficient (the sum of the `d · 2^d` chart
coefficients of CCCXLVII). -/
theorem blowUpCoefficient_eq_cubeCoefficient (q : PowerLogIndex) :
    blowUpCoefficient A hp0 q = cubeCoefficient A hp0 q := by
  by_cases hj : q.logDegree = 0
  · by_cases hm : ∃ m : ℕ, q.exponent = (m : ℝ) / 2
    · exact blowUpCoefficient_eq_cubeCoefficient_of_mem A hp0
        ((mem_spectrumLe_zero_iff two_pos q.exponent q).2 ⟨hm, hj, le_rfl⟩)
    · have hc : cubeCoefficient A hp0 q = 0 :=
        cubeCoefficient_eq_zero_of_not_support A hp0 fun r hr =>
          hm ⟨d + r, by rw [hr, Nat.cast_add]⟩
      rw [hc]
      by_cases hQ : ∃ m : ℕ, q.exponent = (m : ℝ) / commonQ (cubeCert A hp0).cores.k
      · refine blowUpCoefficient_eq_zero_of_not_mem A hp0
          ((mem_spectrumLe_zero_iff (commonQ_pos _ (cubeCert A hp0).cores.k_pos)
            q.exponent q).2 ⟨hQ, hj, le_rfl⟩)
          fun h => hm ((mem_spectrumLe_zero_iff two_pos _ q).1 h).1
      · exact blowUpCoefficient_eq_zero_of_not_lattice A hp0 fun m hm' => hQ ⟨m, hm'⟩
  · rw [blowUpCoefficient_eq_zero_of_logDegree_pos A hp0 (Nat.pos_of_ne_zero hj),
      cubeCoefficient_eq_zero_of_logDegree_pos A hp0 (Nat.pos_of_ne_zero hj)]

/-! ### Consequences for the genuine geometry -/

/-- ★★ **The leading coefficient on the genuine blow-up is `π^{d/2} F(0) p(0)`** (the mass of the
leading measure `π^{d/2} δ₀` of CCXCV, through CCCXLVIII). -/
theorem blowUpCoefficient_leading (hd : 1 < d) :
    blowUpCoefficient A hp0 (leadingIndex d) = Real.pi ^ (d / 2 : ℝ) * (F 0 * p 0) := by
  rw [blowUpCoefficient_eq_cubeCoefficient, cubeCoefficient_leading hd A hp0]

/-- ★ **Vanishing below `d/2`** on the genuine blow-up, for every `d ≥ 1`. -/
theorem blowUpCoefficient_eq_zero_of_lt {q : PowerLogIndex} (hlt : q.exponent < d / 2) :
    blowUpCoefficient A hp0 q = 0 := by
  rw [blowUpCoefficient_eq_cubeCoefficient]
  refine cubeCoefficient_eq_zero_of_not_support A hp0 fun r hr => ?_
  rw [hr] at hlt
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith

/-- ★ **Support**: the genuine coefficients vanish unless the exponent is `(d + ℓ)/2`. -/
theorem blowUpCoefficient_eq_zero_of_not_support {q : PowerLogIndex}
    (hμ : ∀ r : ℕ, q.exponent ≠ ((d : ℝ) + r) / 2) : blowUpCoefficient A hp0 q = 0 := by
  rw [blowUpCoefficient_eq_cubeCoefficient]
  exact cubeCoefficient_eq_zero_of_not_support A hp0 hμ

end BlowUpCube

end Grammar
