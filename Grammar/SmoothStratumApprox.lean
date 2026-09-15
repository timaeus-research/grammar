/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumTest

/-!
# Extension of the stratum test functional to compactly supported continuous functions

Residue programme (consult #132), units 2–3. A compactly supported continuous function on
`X = U ∖ D_{c+1}` extends by zero to a compactly supported continuous function on `U`
(`ext`, `continuous_ext`, `hasCompactSupport_ext`), and is uniformly approximated by smooth test
functions with supports in ONE fixed compact `L ⊆ X` (`exists_approx`: a smooth uniform
approximant from the convex local-to-global gluing theorem, multiplied by a cutoff equal to `1`
on the support). The values `T[G_n]` along such an approximating sequence converge, by the local
bound `|T[G] − T[G']| ≤ ‖G − G'‖_∞ · T[χ_L]`, and the limit does not depend on the sequence
(`tendsto_T_of_approx`). The resulting functional `Λ` on `C_c(X, ℝ)` is linear and positive
(`Λ`, a `PositiveLinearMap`), and agrees with `T` on smooth test functions (`Λ_toCc`). This is
the functional to which the Riesz–Markov–Kakutani theorem is applied. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold CompactlySupported
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Extension by zero -/

open Classical in
/-- Extension by zero of a function on `X = U ∖ D_{c+1}` to `U`. -/
noncomputable def ext (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.R.U → ℝ := fun P =>
  if h : P ∈ Ξ.stratumOpen c then f ⟨P, h⟩ else 0

theorem ext_apply_mem (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) {P : Ξ.R.U} (h : P ∈ Ξ.stratumOpen c) :
    Ξ.ext c f P = f ⟨P, h⟩ := dif_pos h

theorem ext_apply_not_mem (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) {P : Ξ.R.U}
    (h : P ∉ Ξ.stratumOpen c) : Ξ.ext c f P = 0 := dif_neg h

theorem ext_val (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (x : Ξ.stratumOpen c) :
    Ξ.ext c f x.1 = f x := dif_pos x.2

theorem ext_add (c : ℕ) (f g : C_c(Ξ.stratumOpen c, ℝ)) (P : Ξ.R.U) :
    Ξ.ext c (f + g) P = Ξ.ext c f P + Ξ.ext c g P := by
  unfold ext
  split_ifs with h
  · rfl
  · rw [add_zero]

theorem ext_smul (c : ℕ) (r : ℝ) (f : C_c(Ξ.stratumOpen c, ℝ)) (P : Ξ.R.U) :
    Ξ.ext c (r • f) P = r * Ξ.ext c f P := by
  unfold ext
  split_ifs with h
  · rfl
  · rw [mul_zero]

theorem isCompact_image_tsupport (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    IsCompact (Subtype.val '' tsupport f) :=
  f.hasCompactSupport.image continuous_subtype_val

theorem support_ext_subset (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    Function.support (Ξ.ext c f) ⊆ Subtype.val '' tsupport f := by
  intro P hP
  by_cases h : P ∈ Ξ.stratumOpen c
  · refine ⟨⟨P, h⟩, subset_tsupport _ ?_, rfl⟩
    rwa [Function.mem_support, Ξ.ext_apply_mem c f h] at hP
  · exact absurd (Ξ.ext_apply_not_mem c f h) hP

theorem tsupport_ext_subset (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    tsupport (Ξ.ext c f) ⊆ Subtype.val '' tsupport f :=
  closure_minimal (Ξ.support_ext_subset c f) (Ξ.isCompact_image_tsupport c f).isClosed

theorem hasCompactSupport_ext (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    HasCompactSupport (Ξ.ext c f) :=
  (Ξ.isCompact_image_tsupport c f).of_isClosed_subset (isClosed_tsupport _)
    (Ξ.tsupport_ext_subset c f)

theorem tsupport_ext_subset_stratumOpen (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    tsupport (Ξ.ext c f) ⊆ Ξ.stratumOpen c :=
  (Ξ.tsupport_ext_subset c f).trans (by
    rintro P ⟨x, -, rfl⟩
    exact x.2)

theorem continuous_ext (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : Continuous (Ξ.ext c f) := by
  rw [continuous_iff_continuousAt]
  intro P
  by_cases h : P ∈ Ξ.stratumOpen c
  · have hres : ContinuousOn (Ξ.ext c f) (Ξ.stratumOpen c) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Ξ.stratumOpen c).domRestrict (Ξ.ext c f) = f := funext fun x => Ξ.ext_val c f x
      rw [this]
      exact f.continuous
    exact hres.continuousAt ((Ξ.isOpen_stratumOpen c).mem_nhds h)
  · have hopen : IsOpen (Subtype.val '' tsupport f)ᶜ :=
      (Ξ.isCompact_image_tsupport c f).isClosed.isOpen_compl
    have hPmem : P ∈ (Subtype.val '' tsupport f)ᶜ := fun ⟨x, _, hx⟩ => h (hx ▸ x.2)
    have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 P] Ξ.ext c f :=
      eventually_of_mem (hopen.mem_nhds hPmem) fun Q hQ =>
        (image_eq_zero_of_notMem_tsupport fun hQt => hQ (Ξ.tsupport_ext_subset c f hQt)).symm
    exact continuousAt_const.congr hev

/-! ### Fixed-support smooth approximation -/

/-- ★ **Uniform approximation by smooth tests with a common compact support**: for every
`f ∈ C_c(X, ℝ)` there is a compact `L ⊆ X` such that for every `ε > 0` some smooth test function
supported in `L` is uniformly `ε`-close to the extension by zero of `f`. -/
theorem exists_approx (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    ∃ L : Set Ξ.R.U, IsCompact L ∧ L ⊆ Ξ.stratumOpen c ∧ ∀ ε > 0, ∃ G : Ξ.R.U → ℝ,
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ Ξ.IsTest c G ∧ tsupport G ⊆ L ∧
        ∀ P, |G P - Ξ.ext c f P| ≤ ε := by
  obtain ⟨L, hLc, hKL, hLX⟩ := exists_compact_between (Ξ.hasCompactSupport_ext c f)
    (Ξ.isOpen_stratumOpen c) (Ξ.tsupport_ext_subset_stratumOpen c f)
  refine ⟨L, hLc, hLX, fun ε hε => ?_⟩
  obtain ⟨η, hη1, hη0, hη01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin d → ℝ)
    (n := ⊤) (isClosed_tsupport (Ξ.ext c f)) hKL
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, Fin d → ℝ)
    (t := fun P => Ioo (Ξ.ext c f P - ε) (Ξ.ext c f P + ε)) (n := ⊤) (fun P => convex_Ioo _ _)
    fun P => ⟨Ξ.ext c f P, by
      have hcont : Tendsto (Ξ.ext c f) (𝓝 P) (𝓝 (Ξ.ext c f P)) :=
        (Ξ.continuous_ext c f).continuousAt
      filter_upwards [hcont.eventually (Metric.ball_mem_nhds _ hε)] with Q hQ
      rw [Real.dist_eq] at hQ
      obtain ⟨h1, h2⟩ := abs_lt.1 hQ
      exact ⟨by linarith, by linarith⟩⟩
  have hsuppη : Function.support (fun P => η P * g P) ⊆ L := fun P hP => by
    by_contra h
    exact hP (by
      change η P * g P = 0
      rw [hη0 P h, zero_mul])
  have hts : tsupport (fun P => η P * g P) ⊆ L := closure_minimal hsuppη hLc.isClosed
  refine ⟨fun P => η P * g P, η.contMDiff.mul g.contMDiff,
    ⟨hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLX⟩, hts, fun P => ?_⟩
  have hgP := hg P
  rw [Set.mem_Ioo] at hgP
  change |η P * g P - Ξ.ext c f P| ≤ ε
  by_cases hP : P ∈ tsupport (Ξ.ext c f)
  · rw [hη1.self_of_nhdsSet P hP, one_mul, abs_le]
    constructor <;> linarith
  · rw [image_eq_zero_of_notMem_tsupport hP] at hgP ⊢
    rw [sub_zero, abs_mul, abs_of_nonneg (hη01 P).1]
    calc η P * |g P| ≤ 1 * |g P| := mul_le_mul_of_nonneg_right (hη01 P).2 (abs_nonneg _)
      _ ≤ ε := by
        rw [one_mul, abs_le]
        constructor <;> linarith

/-! ### The chosen approximating sequence -/

/-- The common support compact of the chosen approximants. -/
noncomputable def approxL (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : Set Ξ.R.U :=
  Classical.choose (Ξ.exists_approx c f)

theorem approxL_spec (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    IsCompact (Ξ.approxL c f) ∧ Ξ.approxL c f ⊆ Ξ.stratumOpen c ∧ ∀ ε > 0, ∃ G : Ξ.R.U → ℝ,
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ Ξ.IsTest c G ∧ tsupport G ⊆ Ξ.approxL c f ∧
        ∀ P, |G P - Ξ.ext c f P| ≤ ε :=
  Classical.choose_spec (Ξ.exists_approx c f)

theorem one_div_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- The `n`-th chosen approximant, uniformly `1/(n+1)`-close to the extension of `f`. -/
noncomputable def approx (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (n : ℕ) : Ξ.R.U → ℝ :=
  Classical.choose ((Ξ.approxL_spec c f).2.2 (1 / ((n : ℝ) + 1)) (one_div_succ_pos n))

theorem approx_spec (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (n : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (Ξ.approx c f n) ∧ Ξ.IsTest c (Ξ.approx c f n) ∧
      tsupport (Ξ.approx c f n) ⊆ Ξ.approxL c f ∧
        ∀ P, |Ξ.approx c f n P - Ξ.ext c f P| ≤ 1 / ((n : ℝ) + 1) :=
  Classical.choose_spec ((Ξ.approxL_spec c f).2.2 (1 / ((n : ℝ) + 1)) (one_div_succ_pos n))

theorem approx_smooth (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (n : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (Ξ.approx c f n) := (Ξ.approx_spec c f n).1

/-! ### The difference bound -/

/-- The cutoff of a compact subset of `X`. -/
noncomputable def cutoff (c : ℕ) {L : Set Ξ.R.U} (hL : IsCompact L) (hLX : L ⊆ Ξ.stratumOpen c) :
    Ξ.R.U → ℝ :=
  Classical.choose (Ξ.exists_cutoff c hL hLX)

theorem cutoff_spec (c : ℕ) {L : Set Ξ.R.U} (hL : IsCompact L) (hLX : L ⊆ Ξ.stratumOpen c) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (Ξ.cutoff c hL hLX) ∧ Ξ.IsTest c (Ξ.cutoff c hL hLX) ∧
      (∀ P ∈ L, Ξ.cutoff c hL hLX P = 1) ∧ ∀ P, Ξ.cutoff c hL hLX P ∈ Icc (0 : ℝ) 1 :=
  Classical.choose_spec (Ξ.exists_cutoff c hL hLX)

/-- `|T[G] − T[G']| ≤ M · T[χ_L]` for tests supported in `L` with `|G − G'| ≤ M`. -/
theorem abs_T_sub_le {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) {L : Set Ξ.R.U}
    (hL : IsCompact L) (hLX : L ⊆ Ξ.stratumOpen c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hGt : Ξ.IsTest c G) (hG't : Ξ.IsTest c G') (hGL : tsupport G ⊆ L) (hG'L : tsupport G' ⊆ L)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ P, |G P - G' P| ≤ M) :
    |Ξ.T Y μ c G hG - Ξ.T Y μ c G' hG'| ≤
      M * Ξ.T Y μ c (Ξ.cutoff c hL hLX) (Ξ.cutoff_spec c hL hLX).1 := by
  obtain ⟨hχs, hχt, hχ1, hχ01⟩ := Ξ.cutoff_spec c hL hLX
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hdiff : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hdt : Ξ.IsTest c (fun P => G P + (-1 : ℝ) * G' P) :=
    IsTest.add Ξ hGt (IsTest.smul Ξ hG't (-1))
  have hsupp : tsupport (fun P => G P + (-1 : ℝ) * G' P) ⊆ L := by
    refine closure_minimal (fun P hP => ?_) hL.isClosed
    by_contra h
    exact hP (by
      change G P + (-1 : ℝ) * G' P = 0
      rw [image_eq_zero_of_notMem_tsupport fun h' => h (hGL h'),
        image_eq_zero_of_notMem_tsupport fun h' => h (hG'L h')]
      ring)
  have hb := Ξ.abs_T_le Y hc hzero hdiff hdt hχs hχt (fun P => (hχ01 P).1)
    (fun P hP => (hχ1 P (hsupp hP)).ge) hM0 fun P => by
      rw [neg_one_mul, ← sub_eq_add_neg]
      exact hM P
  rw [Ξ.T_add Y μ c hG hG'', Ξ.T_smul Y μ c hG' (-1), neg_one_mul, ← sub_eq_add_neg] at hb
  exact hb

/-! ### The limit functional -/

/-- The limit of `T` along the chosen approximating sequence. -/
noncomputable def Λ₀ (μ : ℝ) (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : ℝ :=
  limUnder atTop fun n => Ξ.T Y μ c (Ξ.approx c f n) (Ξ.approx_smooth c f n)

theorem tendsto_one_div_succ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- ★★ **Convergence along any fixed-support approximating sequence**: if smooth tests `G n`
supported in a compact `L' ⊆ X` are uniformly `ε n`-close to the extension of `f`, with
`ε n → 0`, then `T[G n] → Λ₀ f`. -/
theorem tendsto_T_of_approx {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f : C_c(Ξ.stratumOpen c, ℝ)) {L' : Set Ξ.R.U} (hL'c : IsCompact L')
    (hL'X : L' ⊆ Ξ.stratumOpen c) {G : ℕ → Ξ.R.U → ℝ}
    (hGs : ∀ n, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (G n)) (hGt : ∀ n, Ξ.IsTest c (G n))
    (hGL : ∀ n, tsupport (G n) ⊆ L') {ε : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) (hG : ∀ n P, |G n P - Ξ.ext c f P| ≤ ε n) :
    Tendsto (fun n => Ξ.T Y μ c (G n) (hGs n)) atTop (𝓝 (Ξ.Λ₀ Y μ c f)) := by
  obtain ⟨hLc, hLX, -⟩ := Ξ.approxL_spec c f
  set L := L' ∪ Ξ.approxL c f with hLdef
  have hLcU : IsCompact L := hL'c.union hLc
  have hLXU : L ⊆ Ξ.stratumOpen c := Set.union_subset hL'X hLX
  set Tχ := Ξ.T Y μ c (Ξ.cutoff c hLcU hLXU) (Ξ.cutoff_spec c hLcU hLXU).1 with hTχ
  have hTχ0 : 0 ≤ Tχ :=
    Ξ.T_nonneg Y hc hzero _ (Ξ.cutoff_spec c hLcU hLXU).2.1 fun P =>
      ((Ξ.cutoff_spec c hLcU hLXU).2.2.2 P).1
  -- the two-index bound
  have hbound : ∀ n m, |Ξ.T Y μ c (G n) (hGs n) -
      Ξ.T Y μ c (Ξ.approx c f m) (Ξ.approx_smooth c f m)| ≤ (ε n + 1 / ((m : ℝ) + 1)) * Tχ := by
    intro n m
    refine Ξ.abs_T_sub_le Y hc hzero hLcU hLXU (hGs n) (Ξ.approx_smooth c f m) (hGt n)
      (Ξ.approx_spec c f m).2.1 ((hGL n).trans Set.subset_union_left)
      ((Ξ.approx_spec c f m).2.2.1.trans Set.subset_union_right)
      (add_nonneg (hε0 n) (one_div_succ_pos m).le) fun P => ?_
    calc |G n P - Ξ.approx c f m P|
        = |(G n P - Ξ.ext c f P) - (Ξ.approx c f m P - Ξ.ext c f P)| := by ring_nf
      _ ≤ |G n P - Ξ.ext c f P| + |Ξ.approx c f m P - Ξ.ext c f P| := abs_sub _ _
      _ ≤ ε n + 1 / ((m : ℝ) + 1) := add_le_add (hG n P) ((Ξ.approx_spec c f m).2.2.2 P)
  -- the chosen sequence is Cauchy, hence converges to `Λ₀ f`
  have hcauchy : CauchySeq fun m => Ξ.T Y μ c (Ξ.approx c f m) (Ξ.approx_smooth c f m) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)) * Tχ)
      (fun n m N hn hm => ?_) ?_
    · rw [Real.dist_eq]
      have h1 := Ξ.abs_T_sub_le Y hc hzero hLcU hLXU (Ξ.approx_smooth c f n)
        (Ξ.approx_smooth c f m) (Ξ.approx_spec c f n).2.1 (Ξ.approx_spec c f m).2.1
        ((Ξ.approx_spec c f n).2.2.1.trans Set.subset_union_right)
        ((Ξ.approx_spec c f m).2.2.1.trans Set.subset_union_right)
        (M := 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))
        (add_nonneg (one_div_succ_pos n).le (one_div_succ_pos m).le) fun P => by
          calc |Ξ.approx c f n P - Ξ.approx c f m P|
              = |(Ξ.approx c f n P - Ξ.ext c f P) - (Ξ.approx c f m P - Ξ.ext c f P)| := by
                ring_nf
            _ ≤ _ := abs_sub _ _
            _ ≤ _ := add_le_add ((Ξ.approx_spec c f n).2.2.2 P) ((Ξ.approx_spec c f m).2.2.2 P)
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hTχ0)
      have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have hm' : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
      linarith
    · have := (tendsto_one_div_succ.const_mul 2).mul_const Tχ
      simpa using this
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hΛ : Ξ.Λ₀ Y μ c f = ℓ := hℓ.limUnder_eq
  rw [hΛ]
  -- letting `m → ∞` in the two-index bound
  have hlim : ∀ n, |Ξ.T Y μ c (G n) (hGs n) - ℓ| ≤ ε n * Tχ := by
    intro n
    have h1 : Tendsto (fun m => |Ξ.T Y μ c (G n) (hGs n) -
        Ξ.T Y μ c (Ξ.approx c f m) (Ξ.approx_smooth c f m)|) atTop
        (𝓝 |Ξ.T Y μ c (G n) (hGs n) - ℓ|) := (tendsto_const_nhds.sub hℓ).abs
    have h2 : Tendsto (fun m : ℕ => (ε n + 1 / ((m : ℝ) + 1)) * Tχ) atTop (𝓝 (ε n * Tχ)) := by
      have := (tendsto_one_div_succ.const_add (ε n)).mul_const Tχ
      simpa using this
    exact le_of_tendsto_of_tendsto' h1 h2 fun m => hbound n m
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hεT : Tendsto (fun n => ε n * Tχ) atTop (𝓝 0) := by simpa using hε.mul_const Tχ
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hεT
  rw [Real.norm_eq_abs]
  exact hlim n

/-- `T` along the chosen sequence converges to `Λ₀ f`. -/
theorem tendsto_T_approx {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f : C_c(Ξ.stratumOpen c, ℝ)) :
    Tendsto (fun n => Ξ.T Y μ c (Ξ.approx c f n) (Ξ.approx_smooth c f n)) atTop
      (𝓝 (Ξ.Λ₀ Y μ c f)) :=
  Ξ.tendsto_T_of_approx Y hc hzero f (Ξ.approxL_spec c f).1 (Ξ.approxL_spec c f).2.1
    (Ξ.approx_smooth c f) (fun n => (Ξ.approx_spec c f n).2.1)
    (fun n => (Ξ.approx_spec c f n).2.2.1) (fun n => (one_div_succ_pos n).le)
    tendsto_one_div_succ fun n P => (Ξ.approx_spec c f n).2.2.2 P

theorem Λ₀_add {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f g : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.Λ₀ Y μ c (f + g) = Ξ.Λ₀ Y μ c f + Ξ.Λ₀ Y μ c g := by
  have h1 := Ξ.tendsto_T_approx Y hc hzero f
  have h2 := Ξ.tendsto_T_approx Y hc hzero g
  have hs : ∀ n, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun P => Ξ.approx c f n P + Ξ.approx c g n P) := fun n =>
    (Ξ.approx_smooth c f n).add (Ξ.approx_smooth c g n)
  have h3 := Ξ.tendsto_T_of_approx Y hc hzero (f + g)
    ((Ξ.approxL_spec c f).1.union (Ξ.approxL_spec c g).1)
    (Set.union_subset (Ξ.approxL_spec c f).2.1 (Ξ.approxL_spec c g).2.1) hs
    (fun n => IsTest.add Ξ (Ξ.approx_spec c f n).2.1 (Ξ.approx_spec c g n).2.1)
    (fun n => ?_) (ε := fun n => 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1))
    (fun n => add_nonneg (one_div_succ_pos n).le (one_div_succ_pos n).le)
    (by simpa using tendsto_one_div_succ.add tendsto_one_div_succ) fun n P => ?_
  · have h4 : Tendsto (fun n => Ξ.T Y μ c (fun P => Ξ.approx c f n P + Ξ.approx c g n P) (hs n))
        atTop (𝓝 (Ξ.Λ₀ Y μ c f + Ξ.Λ₀ Y μ c g)) := by
      refine (h1.add h2).congr fun n => ?_
      rw [Ξ.T_add Y μ c (Ξ.approx_smooth c f n) (Ξ.approx_smooth c g n)]
    exact tendsto_nhds_unique h3 h4
  · refine closure_minimal (fun P hP => ?_) ((Ξ.approxL_spec c f).1.union
      (Ξ.approxL_spec c g).1).isClosed
    by_contra h
    rw [Set.mem_union, not_or] at h
    exact hP (by
      change Ξ.approx c f n P + Ξ.approx c g n P = 0
      rw [image_eq_zero_of_notMem_tsupport fun h' => h.1 ((Ξ.approx_spec c f n).2.2.1 h'),
        image_eq_zero_of_notMem_tsupport fun h' => h.2 ((Ξ.approx_spec c g n).2.2.1 h'),
        add_zero])
  · rw [Ξ.ext_add]
    calc |Ξ.approx c f n P + Ξ.approx c g n P - (Ξ.ext c f P + Ξ.ext c g P)|
        = |(Ξ.approx c f n P - Ξ.ext c f P) + (Ξ.approx c g n P - Ξ.ext c g P)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add ((Ξ.approx_spec c f n).2.2.2 P) ((Ξ.approx_spec c g n).2.2.2 P)

theorem Λ₀_smul {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) (r : ℝ)
    (f : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.Λ₀ Y μ c (r • f) = r * Ξ.Λ₀ Y μ c f := by
  have h1 := Ξ.tendsto_T_approx Y hc hzero f
  have hs : ∀ n, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => r * Ξ.approx c f n P) := fun n =>
    contMDiff_const.mul (Ξ.approx_smooth c f n)
  have h3 := Ξ.tendsto_T_of_approx Y hc hzero (r • f) (Ξ.approxL_spec c f).1
    (Ξ.approxL_spec c f).2.1 hs (fun n => IsTest.smul Ξ (Ξ.approx_spec c f n).2.1 r)
    (fun n => ?_) (ε := fun n => |r| * (1 / ((n : ℝ) + 1)))
    (fun n => mul_nonneg (abs_nonneg r) (one_div_succ_pos n).le)
    (by simpa using tendsto_one_div_succ.const_mul |r|) fun n P => ?_
  · have h4 : Tendsto (fun n => Ξ.T Y μ c (fun P => r * Ξ.approx c f n P) (hs n)) atTop
        (𝓝 (r * Ξ.Λ₀ Y μ c f)) := by
      refine (h1.const_mul r).congr fun n => ?_
      rw [Ξ.T_smul Y μ c (Ξ.approx_smooth c f n) r]
    exact tendsto_nhds_unique h3 h4
  · refine closure_minimal (fun P hP => ?_) (Ξ.approxL_spec c f).1.isClosed
    by_contra h
    exact hP (by
      change r * Ξ.approx c f n P = 0
      rw [image_eq_zero_of_notMem_tsupport fun h' => h ((Ξ.approx_spec c f n).2.2.1 h'), mul_zero])
  · rw [Ξ.ext_smul, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left ((Ξ.approx_spec c f n).2.2.2 P) (abs_nonneg r)

theorem Λ₀_nonneg {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f : C_c(Ξ.stratumOpen c, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ Ξ.Λ₀ Y μ c f := by
  obtain ⟨hLc, hLX, -⟩ := Ξ.approxL_spec c f
  obtain ⟨hχs, hχt, hχ1, hχ01⟩ := Ξ.cutoff_spec c hLc hLX
  set Tχ := Ξ.T Y μ c (Ξ.cutoff c hLc hLX) hχs with hTχ
  have hext0 : ∀ P, 0 ≤ Ξ.ext c f P := fun P => by
    unfold ext
    split_ifs with h
    · exact hf _
    · exact le_rfl
  -- `T[approx n] + (1/(n+1)) T[χ] ≥ 0`
  have hlow : ∀ n : ℕ, -(1 / ((n : ℝ) + 1)) * Tχ ≤
      Ξ.T Y μ c (Ξ.approx c f n) (Ξ.approx_smooth c f n) := by
    intro n
    have hεχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞
        (fun P => (1 / ((n : ℝ) + 1)) * Ξ.cutoff c hLc hLX P) := contMDiff_const.mul hχs
    have hpos := Ξ.T_nonneg Y hc hzero
      (G := fun P => Ξ.approx c f n P + (1 / ((n : ℝ) + 1)) * Ξ.cutoff c hLc hLX P)
      ((Ξ.approx_smooth c f n).add hεχ)
      (IsTest.add Ξ (Ξ.approx_spec c f n).2.1 (IsTest.smul Ξ hχt _)) fun P => by
        by_cases hP : P ∈ tsupport (Ξ.approx c f n)
        · rw [hχ1 P ((Ξ.approx_spec c f n).2.2.1 hP), mul_one]
          have := (abs_le.1 ((Ξ.approx_spec c f n).2.2.2 P)).1
          have := hext0 P
          linarith
        · rw [image_eq_zero_of_notMem_tsupport hP, zero_add]
          exact mul_nonneg (one_div_succ_pos n).le (hχ01 P).1
    rw [Ξ.T_add Y μ c (Ξ.approx_smooth c f n) hεχ, Ξ.T_smul Y μ c hχs] at hpos
    linarith
  have hzero' : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)) * Tχ) atTop (𝓝 0) := by
    have := (tendsto_one_div_succ.neg).mul_const Tχ
    simpa using this
  exact le_of_tendsto_of_tendsto' hzero' (Ξ.tendsto_T_approx Y hc hzero f) hlow

/-- ★★ **The positive linear functional on `C_c(X, ℝ)`** extending the stratum test functional. -/
noncomputable def Λ {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    C_c(Ξ.stratumOpen c, ℝ) →ₚ[ℝ] ℝ where
  toFun := Ξ.Λ₀ Y μ c
  map_add' := Ξ.Λ₀_add Y hc hzero
  map_smul' := fun r f => by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact Ξ.Λ₀_smul Y hc hzero r f
  monotone' := fun f g hfg => by
    have h := Ξ.Λ₀_nonneg Y hc hzero (g + (-1 : ℝ) • f) fun x => by
      have := CompactlySupportedContinuousMap.le_def.1 hfg x
      simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    rw [Ξ.Λ₀_add Y hc hzero, Ξ.Λ₀_smul Y hc hzero] at h
    change Ξ.Λ₀ Y μ c f ≤ Ξ.Λ₀ Y μ c g
    linarith

/-! ### Smooth tests as elements of `C_c(X, ℝ)` -/

/-- A smooth test function restricted to `X`, as a compactly supported continuous function. -/
noncomputable def toCc (c : ℕ) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hGt : Ξ.IsTest c G) : C_c(Ξ.stratumOpen c, ℝ) where
  toFun := fun x => G x.1
  continuous_toFun := hG.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    have hsub : tsupport (fun x : Ξ.stratumOpen c => G x.1) ⊆ Subtype.val ⁻¹' tsupport G := by
      refine closure_minimal (fun x hx => subset_tsupport _ hx) ?_
      exact (isClosed_tsupport G).preimage continuous_subtype_val
    refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hsub
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hGt.2]
    exact hGt.1

theorem ext_toCc (c : ℕ) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hGt : Ξ.IsTest c G) (P : Ξ.R.U) : Ξ.ext c (Ξ.toCc c hG hGt) P = G P := by
  unfold ext
  split_ifs with h
  · rfl
  · exact (image_eq_zero_of_notMem_tsupport fun h' => h (hGt.2 h')).symm

/-- ★★ `Λ` agrees with the stratum test functional on smooth tests. -/
theorem Λ_toCc {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    Ξ.Λ Y hc hzero (Ξ.toCc c hG hGt) = Ξ.T Y μ c G hG := by
  change Ξ.Λ₀ Y μ c (Ξ.toCc c hG hGt) = Ξ.T Y μ c G hG
  have h := Ξ.tendsto_T_of_approx Y hc hzero (Ξ.toCc c hG hGt) hGt.1 hGt.2 (G := fun _ => G)
    (fun _ => hG) (fun _ => hGt) (fun _ => le_rfl) (ε := fun _ => 0) (fun _ => le_rfl)
    tendsto_const_nhds fun n P => by rw [Ξ.ext_toCc, sub_self, abs_zero]
  exact tendsto_nhds_unique h tendsto_const_nhds

end ResolvedData

end SmoothEngine

end Grammar
