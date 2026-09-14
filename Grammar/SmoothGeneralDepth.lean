/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceSplit
import Grammar.SmoothFaceMonomial
import Grammar.SmoothAssemblyAlgebra

/-!
# The smooth expansion in general dimension at a fixed depth (consult #116 U3)

For a smooth amplitude `F` on `[0,b]^d` with the rectangular mixed-derivative bound
`|∂^m F| ≤ M` (`m ≤ p`), Jacobian exponents `h`, phase `Nβ v^{2k}`, a natural cutoff `L` and
depths `pᵢ + hᵢ = 2kᵢL`, the subset formula splits the integral into the face terms
`T_J R_K F`; each is a finite sum of one-flat-complement face integrals (`faceTerm_integral`),
whose inner function is the face monomial integral `Z^J_e` with its global two-regime estimate
(`faceMono_two_regime`; for the empty face `Z^∅(t) = e^{−βt}`, `faceMono_empty_two_regime`) and
whose outer amplitude is the flat face amplitude (`faceAmp_bound`). The generic face theorem
(`face_expansion`) expands each, and `reorganise` collects everything into ONE coefficient system
`smoothCoeffAtDepth` on the ambient lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, of logarithmic degree `≤ d − 1`:
★★★ `smooth_expansion_at_depth`:
`|∫ F v^h e^{−Nβ v^{2k}} − absSpectralSum Q (d−1) (smoothCoeffAtDepth p F) L N|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` for all `N ≥ 1`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Face data: lattice, degree, coefficients -/

section FaceData

variable (k : Fin d → ℕ) (β b : ℝ) (L : ℕ) (J : Finset (Fin d))

/-- The ambient lattice denominator `Q = 2 ∏ᵢ kᵢ`. -/
def Qamb : ℕ := 2 * ∏ i, k i

/-- The face lattice denominator `Q_J = 2 ∏_{i∈J} kᵢ`. -/
def QJ : ℕ := 2 * ∏ i : {i // inJ J i}, k i

/-- The face logarithmic degree `|J| − 1`. -/
def DJ : ℕ := Fintype.card {i // inJ J i} - 1

/-- The face lattice below the cutoff (empty for the empty face). -/
noncomputable def ΛJ : Finset ℝ := if J.Nonempty then latticeBelow (QJ k J) L else ∅

theorem nonempty_subtype_inJ {J : Finset (Fin d)} (hJ : J.Nonempty) : Nonempty {i // inJ J i} :=
  hJ.elim fun x hx => ⟨⟨x, hx⟩⟩

/-- The face power–log coefficients (zero for the empty face). -/
noncomputable def faceCoef (e : Fin d → ℕ) : ℝ → ℕ → ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceMonoCoeff (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) β b
  else fun _ _ => 0

theorem Qamb_pos (hk : ∀ i, 0 < k i) : 0 < Qamb k := by
  unfold Qamb; exact Nat.mul_pos two_pos (Finset.prod_pos fun i _ => hk i)

theorem QJ_pos (hk : ∀ i, 0 < k i) : 0 < QJ k J := by
  unfold QJ; exact Nat.mul_pos two_pos (Finset.prod_pos fun i _ => hk i)

theorem QJ_dvd_Qamb : QJ k J ∣ Qamb k := by
  unfold QJ Qamb
  refine mul_dvd_mul_left 2 ?_
  have hprod : ∏ i : {i // inJ J i}, k i = ∏ i ∈ J, k i :=
    (Finset.prod_subtype J (p := inJ J) (fun i => Iff.rfl) k).symm
  rw [hprod]
  exact Finset.prod_dvd_prod_of_subset J univ k (Finset.subset_univ J)

theorem DJ_le : DJ J ≤ d - 1 := by
  unfold DJ
  have := Fintype.card_subtype_le (inJ J)
  rw [Fintype.card_fin] at this
  omega

theorem ΛJ_subset (hk : ∀ i, 0 < k i) : ΛJ k L J ⊆ latticeBelow (Qamb k) L := by
  unfold ΛJ
  split_ifs
  · exact latticeBelow_subset_of_dvd (QJ_pos k J hk) (Qamb_pos k hk) (QJ_dvd_Qamb k J) L
  · exact Finset.empty_subset _

theorem le_of_mem_ΛJ (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : μ ∈ ΛJ k L J) : μ ≤ L := by
  unfold ΛJ at hμ
  split_ifs at hμ with hJ
  · exact ((mem_latticeBelow_iff (QJ_pos k J hk)).1 hμ).2.le
  · exact absurd hμ (Finset.notMem_empty μ)

/-- The face coefficients vanish on ambient lattice points outside the face lattice. -/
theorem faceCoef_eq_zero (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (e : Fin d → ℕ)
    {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) (hμJ : μ ∉ ΛJ k L J) (j : ℕ) :
    faceCoef k β b J e μ j = 0 := by
  unfold faceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    refine faceMonoCoeff_eq_zero_of_not_lattice (ι := {i // inJ J i}) (fun i => k i) (fun i => e i)
      (fun i => hk i) hβ hb (fun m hm => ?_) j
    have hlt : μ < L := ((mem_latticeBelow_iff (Qamb_pos k hk)).1 hμ).2
    apply hμJ
    unfold ΛJ
    rw [if_pos hJ]
    exact (mem_latticeBelow_iff (QJ_pos k J hk)).2 ⟨⟨m, hm⟩, hlt⟩
  · rfl

/-! ### The two-regime estimate for every face, including the empty one -/

theorem box_isEmpty {ι : Type*} [IsEmpty ι] (b : ℝ) : box ι b = Set.univ := by
  ext u
  simp [box]

theorem mono_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (e : ι → ℕ) (u : ι → ℝ) :
    mono e u = 1 := by
  simp [mono]

/-- On the empty index type the face monomial integral is `e^{−βt}`. -/
theorem faceMono_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (k e : ι → ℕ) (β b t : ℝ) :
    faceMono k e β b t = exp (-(β * t)) := by
  unfold faceMono
  rw [box_isEmpty, Measure.restrict_univ]
  simp only [mono_isEmpty, one_mul, mul_one]
  rw [integral_const, smul_eq_mul, Measure.real, volume_pi, Measure.pi_univ]
  simp

/-- The two-regime estimate for the empty face: `|e^{−βt}| ≤ max(1, L!/β^L) t^{−L}`. -/
theorem exp_neg_two_regime {β : ℝ} (hβ : 0 < β) (L : ℕ) {t : ℝ} (ht : 0 < t) :
    |exp (-(β * t))| ≤ max 1 ((L.factorial : ℝ) / β ^ L) * t ^ (-(L : ℝ)) := by
  rw [abs_of_pos (exp_pos _)]
  rcases le_or_gt 1 t with h1 | h1
  · have h := exp_neg_mul_le L hβ ht
    have hrp : t ^ (-(L : ℝ)) = (t ^ L)⁻¹ := by rw [rpow_neg ht.le, rpow_natCast]
    rw [hrp]
    calc exp (-(β * t)) ≤ (L.factorial : ℝ) / β ^ L / t ^ L := h
      _ = (L.factorial : ℝ) / β ^ L * (t ^ L)⁻¹ := by ring
      _ ≤ max 1 ((L.factorial : ℝ) / β ^ L) * (t ^ L)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hpow : 1 ≤ t ^ (-(L : ℝ)) :=
      one_le_rpow_of_pos_of_le_one_of_nonpos ht h1.le (by simp)
    calc exp (-(β * t)) ≤ 1 := by
          rw [exp_le_one_iff]; nlinarith
      _ ≤ 1 * t ^ (-(L : ℝ)) := by linarith
      _ ≤ max 1 ((L.factorial : ℝ) / β ^ L) * t ^ (-(L : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg ht.le _)

theorem isEmpty_subtype_inJ_of_empty {J : Finset (Fin d)} (hJ : ¬ J.Nonempty) :
    IsEmpty {i // inJ J i} :=
  ⟨fun i => hJ ⟨i.1, i.2⟩⟩

/-- ★ **The two-regime estimate for every face**: spectrum `ΛJ`, degree `DJ`, coefficients
`faceCoef`, with SOME constant. -/
theorem face_two_regime (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (hL : 0 < L)
    (e : Fin d → ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      |faceMono (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) β b t -
        powLog (ΛJ k L J) (DJ J) (faceCoef k β b J e) t| ≤
        C * t ^ (-(L : ℝ)) * (1 + |log t|) ^ DJ J := by
  by_cases hJ : J.Nonempty
  · have := nonempty_subtype_inJ hJ
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    obtain ⟨C, hC⟩ := faceMono_two_regime (fun i : {i // inJ J i} => k i)
      (fun i : {i // inJ J i} => e i) (fun i => hk i) hβ hb hL'
    refine ⟨C, fun t ht => ?_⟩
    have h := hC t ht
    unfold ΛJ faceCoef DJ
    rw [if_pos hJ, dif_pos hJ]
    exact h
  · have := isEmpty_subtype_inJ_of_empty hJ
    refine ⟨max 1 ((L.factorial : ℝ) / β ^ L), fun t ht => ?_⟩
    unfold ΛJ faceCoef DJ
    rw [if_neg hJ, dif_neg hJ, faceMono_isEmpty]
    simp only [powLog, Finset.sum_empty, sub_zero, Fintype.card_eq_zero, Nat.zero_sub, pow_zero,
      mul_one]
    exact exp_neg_two_regime hβ L ht

end FaceData

/-! ### The per-face bound -/

variable {F : (Fin d → ℝ) → ℝ} {h k p : Fin d → ℕ} {β b : ℝ} {L : ℕ}

/-- The weight `∏_{i∈J} 1/m_i!` of a face multi-index. -/
noncomputable def faceW (J : Finset (Fin d)) (m : Fin d → ℕ) : ℝ :=
  ∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹

theorem faceW_nonneg (J : Finset (Fin d)) (m : Fin d → ℕ) : 0 ≤ faceW J m :=
  Finset.prod_nonneg fun i _ => by positivity

/-- The face expansion of the `(J, m)` term: exponents `μ ∈ ΛJ`, log degree `DJ`. -/
noncomputable def faceExpansion (F : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ) (L : ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∑ μ ∈ ΛJ k L J, N ^ (-μ) * ∑ j ∈ range (DJ J + 1), ∑ q ∈ range (j + 1),
    faceCoef k β b J (fun i => m i + h i) μ j * (j.choose q) * log N ^ q *
      faceCoeffInt (faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i)
        (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)

/-- The `(J, m)` face integral. -/
noncomputable def faceIntegral (F : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ w in box {i // ¬ inJ J i} b, faceAmp p J F m w * mono (fun i : {i // ¬ inJ J i} => h i) w *
    faceMono (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => m i + h i) β b
      (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)

/-- The `(J, m)` remainder constant (without the two-regime constant). -/
noncomputable def faceRem (h k p : Fin d → ℕ) (b : ℝ) (L : ℕ) (M : ℝ) (J : Finset (Fin d)) : ℝ :=
  ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M) *
    faceRemWeight (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
      (fun i : {i // ¬ inJ J i} => 2 * k i) b L (DJ J)

/-- ★ **The per-face bound**: the generic face theorem applied to the `(J, m)` term. -/
theorem face_bound (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M)
    {J : Finset (Fin d)} {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {C : ℝ}
    (hC : ∀ t : ℝ, 0 < t →
      |faceMono (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => m i + h i) β b t -
        powLog (ΛJ k L J) (DJ J) (faceCoef k β b J fun i => m i + h i) t| ≤
        C * t ^ (-(L : ℝ)) * (1 + |log t|) ^ DJ J)
    {N : ℝ} (hN : 1 ≤ N) :
    |faceIntegral F h k p β b J m N - faceExpansion F h k p β b L J m N| ≤
      C * faceRem h k p b L M J * (1 + log N) ^ DJ J * N ^ (-(L : ℝ)) := by
  have key := face_expansion (ι := {i // ¬ inJ J i}) (G := faceAmp p J F m)
    (Z' := faceMono (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => m i + h i) β b)
    (p := fun i => p i) (h := fun i => h i) (a := fun i => 2 * k i) (b := b)
    (M := (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M)
    (C := C) (L := (L : ℝ)) (Λ := ΛJ k L J) (D := DJ J) (c := faceCoef k β b J fun i => m i + h i)
    hb (continuous_faceAmp p J hF m).aestronglyMeasurable
    (fun w hw => faceAmp_bound p J hF hb hp0 hM hm hw) (measurable_faceMono _ _ _ _) hC
    (fun μ hμ => le_of_mem_ΛJ k L J hk hμ) (fun i => convergence_of_eq (hp i)) hN
  unfold faceIntegral faceExpansion faceRem
  refine key.trans (le_of_eq ?_)
  ring

/-! ### The assembly -/

/-- The index set of the face sums: pairs `(J, m)` with `m ∈ idxL p (lJ J)`. -/
def faceIndex (p : Fin d → ℕ) : Finset (Σ _ : Finset (Fin d), Fin d → ℕ) :=
  (univ : Finset (Finset (Fin d))).sigma fun J => idxL p (lJ J)

/-- ★ **The smooth coefficient system at depth `p`** on the ambient lattice: for each face
`(J, m)`, the binomially reindexed face coefficients times the face coefficient integrals. -/
noncomputable def smoothCoeffAtDepth (F : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1),
    faceCoef k β b x.1 (fun i => x.2 i + h i) μ j * (j.choose q) *
      faceCoeffInt (faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
        (fun i : {i // ¬ inJ x.1 i} => 2 * k i) b μ (j - q)

/-- The integral as a sum of face integrals over `faceIndex`. -/
theorem integral_eq_sum_faceIntegral (hF : ContDiff ℝ ∞ F) (b N : ℝ) :
    ∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v) =
      ∑ x ∈ faceIndex p, faceW x.1 x.2 * faceIntegral F h k p β b x.1 x.2 N := by
  have hpt : ∀ v : Fin d → ℝ, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))), faceOp p J (List.finRange d) F v * mono h v *
        exp (-(N * β) * mono (fun i => 2 * k i) v) := by
    intro v
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.powerset_univ, ← List.toFinset_finRange,
      ← sum_faceOp p (List.nodup_finRange d) F v]
  have hint : ∀ J ∈ (univ : Finset (Finset (Fin d))), IntegrableOn
      (fun v => faceOp p J (List.finRange d) F v * mono h v *
        exp (-(N * β) * mono (fun i => 2 * k i) v)) (box (Fin d) b) := fun J _ =>
    integrableOn_box_of_continuous
      (((contDiff_faceOp p hF J _).continuous.mul (continuous_mono h)).mul
        (continuous_exp.comp (continuous_const.mul (continuous_mono _)))) b
  rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v, integral_finsetSum _ hint,
    faceIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [faceTerm_integral p J hF h k]
  rfl

/-- The expansion sums over `faceIndex` are the ambient `absSpectralSum`. -/
theorem sum_faceExpansion_eq (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (N : ℝ) :
    ∑ x ∈ faceIndex p, faceW x.1 x.2 * faceExpansion F h k p β b L x.1 x.2 N =
      absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth F h k p β b) L N := by
  unfold faceExpansion smoothCoeffAtDepth
  exact reorganise (faceIndex p) (fun x => faceW x.1 x.2) (fun x => ΛJ k L x.1) (fun x => DJ x.1)
    (fun x => faceCoef k β b x.1 fun i => x.2 i + h i)
    (fun x μ e => faceCoeffInt (faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
      (fun i : {i // ¬ inJ x.1 i} => 2 * k i) b μ e)
    (fun x _ => ΛJ_subset k L x.1 hk)
    (fun x _ μ hμ hμJ j => faceCoef_eq_zero k β b L x.1 hk hβ hb _ hμ hμJ j)
    (fun x _ => DJ_le x.1)

theorem faceRemWeight_nonneg {ι : Type*} [Fintype ι] (p h a : ι → ℕ) (b L : ℝ) (D : ℕ) :
    0 ≤ faceRemWeight p h a b L D :=
  setIntegral_nonneg (measurableSet_box b) fun w hw => by
    have hpos := pos_of_mem_box hw
    exact mul_nonneg (Finset.prod_nonneg fun i _ => rpow_nonneg (hpos i).le _) (by positivity)

theorem faceRem_nonneg (h k p : Fin d → ℕ) (b : ℝ) (L : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (J : Finset (Fin d)) : 0 ≤ faceRem h k p b L M J := by
  unfold faceRem
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) hM)
    (faceRemWeight_nonneg _ _ _ _ _ _)

/-- ★★★ **The smooth expansion in general dimension at depth `p`**: for smooth `F` with
`|∂^m F| ≤ M` on `[0,b]^d` (`m ≤ p`), Jacobian exponents `h`, phase `Nβ v^{2k}`, cutoff `L ≥ 1`
and depths `pᵢ + hᵢ = 2kᵢL`,
`|∫_{(0,b]^d} F v^h e^{−Nβ v^{2k}} − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} C_{μ,q} (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` for all `N ≥ 1`, `Q = 2∏kᵢ`, with the explicit coefficient system
`C = smoothCoeffAtDepth p F` (face coefficient integrals of the flat remainders against the box
engine's face monomial coefficients). -/
theorem smooth_expansion_at_depth (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |(∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)) -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth F h k p β b) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  have hM0 : 0 ≤ M := by
    have := hM 0 (fun i => Nat.zero_le _) 0 (fun i => by simp [hb.le])
    exact (abs_nonneg _).trans this
  choose C hC using fun (J : Finset (Fin d)) (e : Fin d → ℕ) =>
    face_two_regime k β b L J hk hβ hb hL e
  refine ⟨∑ x ∈ faceIndex p, faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) *
    faceRem h k p b L M x.1), fun N hN => ?_⟩
  have hlog : 0 ≤ log N := log_nonneg hN
  rw [integral_eq_sum_faceIntegral hF b N, ← sum_faceExpansion_eq hk hβ hb N,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hb' := face_bound hF hk hb hp hp0 hM hm (hC x.1 (fun i => x.2 i + h i)) hN
  have hC0 : 0 ≤ C x.1 (fun i => x.2 i + h i) :=
    nonneg_of_two_regime (hC x.1 (fun i => x.2 i + h i))
  have hR0 := faceRem_nonneg h k p b L hM0 x.1
  have hpow : (1 + log N) ^ DJ x.1 ≤ (1 + log N) ^ (d - 1) :=
    pow_le_pow_right₀ (by linarith) (DJ_le x.1)
  have hW := faceW_nonneg x.1 x.2
  rw [← mul_sub, abs_mul, abs_of_nonneg hW]
  calc faceW x.1 x.2 * |faceIntegral F h k p β b x.1 x.2 N - faceExpansion F h k p β b L x.1 x.2 N|
      ≤ faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) * faceRem h k p b L M x.1 *
          (1 + log N) ^ DJ x.1 * N ^ (-(L : ℝ))) := mul_le_mul_of_nonneg_left hb' hW
    _ ≤ faceW x.1 x.2 * (C x.1 (fun i => x.2 i + h i) * faceRem h k p b L M x.1 *
          (1 + log N) ^ (d - 1) * N ^ (-(L : ℝ))) := by
        gcongr
    _ = _ := by ring

end SmoothEngine

end Grammar
