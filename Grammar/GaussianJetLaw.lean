/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDerivativeProcess
import Grammar.AmplitudeJetSpace
import Grammar.JetPowerBound
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# The cube jet of a smooth Gaussian field is a Gaussian random element of the jet space

For a random field `ζ_o`, smooth for every `o`, whose value process on an open set
`U ⊇ closedBox d b` is Gaussian, the cube jet `o ↦ cubeJet R b (ζ o)` has a Gaussian law in the
Banach space `CubeJetSpace d R b` (`hasGaussianLaw_cubeJet`), provided the jet map is measurable.
Route (Astra #161): every strong-dual functional `L` of the jet space is the everywhere limit of
`L (T_n J)` where `T_n` are finite-rank partition-of-unity interpolants on nodes of mesh `1/(n+1)`
(`exists_finite_partition`, `tendsto_jetInterp`); `L (T_n J_o)` is a finite linear combination of
derivative evaluations `∂^r ζ_o(c)(e_k)` (every linear functional on a space of multilinear maps
is a combination of evaluations at basis tuples, `exists_eq_sum_eval_of_linear`), hence Gaussian by
the joint derivative process of DXLVI; Gaussian laws are closed under limits (DXLV).  Fernique then
gives every moment of the jet norm (`memLp_cubeJet`), the hypothesis of DXLIV, so the Wick series
of the expected empirical coefficient holds for every smooth field with a Gaussian value process
(`integral_empCoeff_gaussian_wick_of_isGaussianProcess`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ContDiff ENNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### A finite partition of unity with small supports on a compact set -/

/-- On a compact set `K`, for every `ε > 0` there are finitely many nodes `t ⊆ K` and weights
`φ_c ≥ 0`, continuous on `K`, summing to `1` on `K`, with `φ_c x ≠ 0 → dist x c < ε`. -/
theorem exists_finite_partition {E : Type*} [MetricSpace E] {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset E, (∀ c ∈ t, c ∈ K) ∧ ∃ φ : E → E → ℝ, (∀ c, ContinuousOn (φ c) K) ∧
      (∀ c x, 0 ≤ φ c x) ∧ (∀ x ∈ K, ∑ c ∈ t, φ c x = 1) ∧
      ∀ c x, φ c x ≠ 0 → dist x c < ε := by
  obtain ⟨s, hsK, hsfin, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hε)
  classical
  let t := hsfin.toFinset
  let ψ : E → E → ℝ := fun c x => max 0 (ε - dist x c)
  have hψc : ∀ c, Continuous (ψ c) := fun c => by fun_prop
  have hψnn : ∀ c x, 0 ≤ ψ c x := fun c x => le_max_left _ _
  let D : E → ℝ := fun x => ∑ c ∈ t, ψ c x
  have hDpos : ∀ x ∈ K, 0 < D x := fun x hx => by
    obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (hcover hx)
    refine Finset.sum_pos' (fun c _ => hψnn c x) ⟨c, hsfin.mem_toFinset.2 hct, ?_⟩
    have : dist x c < ε / 2 := mem_ball.1 hxc
    exact lt_max_of_lt_right (by linarith)
  have hDc : Continuous D := continuous_finsetSum _ fun c _ => hψc c
  refine ⟨t, fun c hc => hsK (hsfin.mem_toFinset.1 hc), fun c x => ψ c x / D x, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (hψc c).continuousOn.div hDc.continuousOn fun x hx => (hDpos x hx).ne'
  · intro c x
    exact div_nonneg (hψnn c x) (Finset.sum_nonneg fun c _ => hψnn c x)
  · intro x hx
    rw [← Finset.sum_div, div_self (hDpos x hx).ne']
  · intro c x h
    have hne : ψ c x ≠ 0 := fun h0 => h (by simp [h0])
    have hpos : 0 < ε - dist x c := by
      by_contra hle
      exact hne (max_eq_left (not_lt.1 hle))
    linarith

/-! ### Finite-rank interpolation of cube jets -/

variable {R : ℕ} {b : ℝ}

/-- The interpolation kernel `x ↦ Σ_c φ_c(x) • A_c` is continuous on the cube. -/
theorem continuous_interpFun {r : ℕ} (t : Finset (Fin d → ℝ)) (φ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hφ : ∀ c, ContinuousOn (φ c) (closedBox d b))
    (A : ↥t → ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin d → ℝ) ℝ) :
    Continuous fun x : closedBox d b => ∑ c : ↥t, φ c x • A c :=
  continuous_finsetSum _ fun c _ => ((hφ c).domRestrict).smul continuous_const

/-- The finite-rank interpolant of the cube jet of `f` on the nodes `t` with weights `φ`. -/
noncomputable def jetInterp (R : ℕ) (b : ℝ) (t : Finset (Fin d → ℝ))
    (φ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (hφ : ∀ c, ContinuousOn (φ c) (closedBox d b))
    (f : (Fin d → ℝ) → ℝ) : CubeJetSpace d R b :=
  fun r => ⟨fun x => ∑ c : ↥t, φ c x • iteratedFDeriv ℝ r.1 f c,
    continuous_interpFun t φ hφ fun c => iteratedFDeriv ℝ r.1 f c⟩

/-- ★ **Convergence of the interpolants**: for nodes of mesh `1/(n+1)` the interpolants of the jet
of a smooth `f` converge to the jet in the jet space (uniform continuity on the compact cube). -/
theorem tendsto_jetInterp {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (t : ℕ → Finset (Fin d → ℝ)) (ht : ∀ n, ∀ c ∈ t n, c ∈ closedBox d b)
    (φ : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hφ : ∀ n c, ContinuousOn (φ n c) (closedBox d b)) (hnn : ∀ n c x, 0 ≤ φ n c x)
    (hsum : ∀ n, ∀ x ∈ closedBox d b, ∑ c ∈ t n, φ n c x = 1)
    (hnode : ∀ n c x, φ n c x ≠ 0 → dist x c < 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => jetInterp R b (t n) (φ n) (hφ n) f) atTop (𝓝 (cubeJet R b f hf)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  -- uniform continuity of every derivative on the compact cube
  have hK := isCompact_closedBox (d := d) b
  have hunif : ∀ r : Fin (R + 1), ∃ δ > 0, ∀ x ∈ closedBox d b, ∀ y ∈ closedBox d b,
      dist x y < δ → dist (iteratedFDeriv ℝ r.1 f x) (iteratedFDeriv ℝ r.1 f y) < η / 2 :=
    fun r => Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous
      (hf.continuous_iteratedFDeriv (natCast_le_infty _)).continuousOn) (η / 2) (half_pos hη)
  choose δ hδpos hδ using hunif
  have hev : ∀ᶠ n : ℕ in atTop, ∀ r : Fin (R + 1), 1 / ((n : ℝ) + 1) < δ r := by
    rw [Filter.eventually_all]
    intro r
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (hδpos r))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hη)
  have hη2 : 0 ≤ η / 2 := (half_pos hη).le
  change ‖(jetInterp R b (t n) (φ n) (hφ n) f - cubeJet R b f hf).toPi‖ ≤ η / 2
  rw [pi_norm_le_iff_of_nonneg hη2]
  intro r
  rw [ContinuousMap.norm_le _ hη2]
  intro x
  -- the pointwise estimate through the partition of unity
  have hx := x.2
  have h1 : (jetInterp R b (t n) (φ n) (hφ n) f - cubeJet R b f hf).toPi r x =
      ∑ c : ↥(t n), φ n c x • (iteratedFDeriv ℝ r.1 f c - iteratedFDeriv ℝ r.1 f x) := by
    have hs : ∑ c : ↥(t n), φ n c x = 1 := by
      rw [Finset.sum_coe_sort (t n) fun c => φ n c x]
      exact hsum n x hx
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
    rfl
  rw [h1]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : ↥(t n),
      ‖φ n c x • (iteratedFDeriv ℝ r.1 f c - iteratedFDeriv ℝ r.1 f x)‖ ≤ φ n c x * (η / 2) := by
    intro c
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn n c x)]
    by_cases hc : φ n c x = 0
    · simp [hc]
    · refine mul_le_mul_of_nonneg_left ?_ (hnn n c x)
      have hdist := hnode n c x hc
      have hc' : (c : Fin d → ℝ) ∈ closedBox d b := ht n c c.2
      have := hδ r c hc' x hx (by rw [dist_comm]; exact hdist.trans (hn' r))
      rw [dist_eq_norm] at this
      exact this.le
  refine (Finset.sum_le_sum fun c _ => hterm c).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, Finset.sum_coe_sort (t n) fun c => φ n c x, hsum n x hx, one_mul]

/-! ### Linear functionals on multilinear maps are combinations of basis evaluations -/

/-- The coordinate map of a multilinear form on `ℝ^d`: its values on the basis tuples. -/
noncomputable def multilinearCoord (r : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin d → ℝ) ℝ →ₗ[ℝ] ((Fin r → Fin d) → ℝ) where
  toFun A k := A fun j => Pi.single (k j) 1
  map_add' A B := by
    ext k
    simp
  map_smul' a A := by
    ext k
    simp

theorem multilinearCoord_injective (r : ℕ) : Function.Injective (multilinearCoord (d := d) r) := by
  classical
  intro A B hAB
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℝ (Fin d)) fun k => ?_
  have := congrFun hAB k
  simpa [multilinearCoord, Pi.basisFun_apply] using this

/-- ★ Every linear functional on the multilinear forms on `ℝ^d` is a finite combination of the
evaluations at basis tuples. -/
theorem exists_eq_sum_eval_of_linear {r : ℕ}
    (Λ : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin d → ℝ) ℝ →ₗ[ℝ] ℝ) :
    ∃ a : (Fin r → Fin d) → ℝ, ∀ A, Λ A = ∑ k, a k * A fun j => Pi.single (k j) 1 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (multilinearCoord (d := d) r)
    (LinearMap.ker_eq_bot.2 (multilinearCoord_injective r))
  refine ⟨fun k => (Λ.comp g) fun j => if k = j then 1 else 0, fun A => ?_⟩
  have h1 : g (multilinearCoord r A) = A := by
    have := LinearMap.congr_fun hg A
    simpa using this
  calc Λ A = (Λ.comp g) (multilinearCoord r A) := by rw [LinearMap.comp_apply, h1]
    _ = ∑ k, multilinearCoord r A k • (Λ.comp g) fun j => if k = j then 1 else 0 :=
        LinearMap.pi_apply_eq_sum_univ _ _
    _ = ∑ k, ((Λ.comp g) fun j => if k = j then 1 else 0) * A fun j => Pi.single (k j) 1 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [multilinearCoord, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
        ring

/-- The multilinear forms on `ℝ^d` are finite-dimensional. -/
instance instFiniteDimensionalMultilinear (r : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin d → ℝ) ℝ) :=
  Module.Finite.of_injective (multilinearCoord (d := d) r) (multilinearCoord_injective r)

instance instSecondCountableTopologyCubeJetSpace (R : ℕ) (b : ℝ) :
    SecondCountableTopology (CubeJetSpace d R b) :=
  inferInstanceAs (SecondCountableTopology (∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

/-! ### The interpolant through a strong-dual functional -/

/-- The injection of a jet component into the jet space. -/
noncomputable def jetSingle (R : ℕ) (b : ℝ) (r : Fin (R + 1))
    (g : C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) :
    CubeJetSpace d R b :=
  Pi.single r g

theorem jetSingle_add (r : Fin (R + 1))
    (g h : C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) :
    jetSingle R b r (g + h) = jetSingle R b r g + jetSingle R b r h := by
  unfold jetSingle
  exact Pi.single_add (f := fun j : Fin (R + 1) =>
    C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin j.1 => Fin d → ℝ) ℝ)) r g h

theorem jetSingle_smul (r : Fin (R + 1)) (a : ℝ)
    (g : C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) :
    jetSingle R b r (a • g) = a • jetSingle R b r g := by
  unfold jetSingle
  exact Pi.single_smul (f := fun j : Fin (R + 1) =>
    C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin j.1 => Fin d → ℝ) ℝ)) r a g

theorem sum_jetSingle (z : CubeJetSpace d R b) : ∑ r, jetSingle R b r (z r) = z :=
  Finset.univ_sum_single z

/-- The functional `A ↦ L (single r (x ↦ Σ_c φ_c(x) • A_c))` on tuples of multilinear forms. -/
noncomputable def interpFunctional (L : StrongDual ℝ (CubeJetSpace d R b))
    (t : Finset (Fin d → ℝ)) (φ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hφ : ∀ c, ContinuousOn (φ c) (closedBox d b)) (r : Fin (R + 1)) :
    (↥t → ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ) →ₗ[ℝ] ℝ where
  toFun A := L (jetSingle R b r ⟨fun x => ∑ c : ↥t, φ c x • A c, continuous_interpFun t φ hφ A⟩)
  map_add' A B := by
    have hX : (⟨fun x => ∑ c : ↥t, φ c x • (A + B) c, continuous_interpFun t φ hφ (A + B)⟩ :
        C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) =
        ⟨fun x => ∑ c : ↥t, φ c x • A c, continuous_interpFun t φ hφ A⟩ +
          ⟨fun x => ∑ c : ↥t, φ c x • B c, continuous_interpFun t φ hφ B⟩ := by
      ext x
      simp [Finset.sum_add_distrib, smul_add]
    rw [hX, jetSingle_add, map_add]
  map_smul' a A := by
    have hX : (⟨fun x => ∑ c : ↥t, φ c x • (a • A) c, continuous_interpFun t φ hφ (a • A)⟩ :
        C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) =
        a • ⟨fun x => ∑ c : ↥t, φ c x • A c, continuous_interpFun t φ hφ A⟩ := by
      ext x
      simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply, Finset.smul_sum,
        smul_comm a]
    rw [RingHom.id_apply, hX, jetSingle_smul, map_smul]

/-- ★★ **The interpolant through `L` is a finite combination of derivative evaluations at the
nodes**, with coefficients independent of `f`. -/
theorem exists_jetInterp_repr (L : StrongDual ℝ (CubeJetSpace d R b))
    (t : Finset (Fin d → ℝ)) (φ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hφ : ∀ c, ContinuousOn (φ c) (closedBox d b)) :
    ∃ a : (Σ r : Fin (R + 1), ↥t × (Fin r.1 → Fin d)) → ℝ, ∀ f : (Fin d → ℝ) → ℝ,
      L (jetInterp R b t φ hφ f) = ∑ q, a q *
        iteratedFDeriv ℝ q.1.1 f q.2.1 fun j => Pi.single (q.2.2 j) 1 := by
  classical
  -- the functional at a single node
  let Λc : ∀ r : Fin (R + 1), ↥t →
      ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ →ₗ[ℝ] ℝ := fun r c =>
    { toFun := fun A => interpFunctional L t φ hφ r (Pi.single c A)
      map_add' := fun A B => by rw [Pi.single_add, map_add]
      map_smul' := fun a A => by rw [Pi.single_smul, map_smul, RingHom.id_apply] }
  have hΛ : ∀ (r : Fin (R + 1)) (c : ↥t), ∃ a : (Fin r.1 → Fin d) → ℝ, ∀ A,
      Λc r c A = ∑ k, a k * A fun j => Pi.single (k j) 1 :=
    fun r c => exists_eq_sum_eval_of_linear (Λc r c)
  choose a ha using hΛ
  refine ⟨fun q => a q.1 q.2.1 q.2.2, fun f => ?_⟩
  have h1 : L (jetInterp R b t φ hφ f) =
      ∑ r : Fin (R + 1), interpFunctional L t φ hφ r fun c => iteratedFDeriv ℝ r.1 f c := by
    conv_lhs => rw [← sum_jetSingle (jetInterp R b t φ hφ f), map_sum]
    rfl
  have h2 : ∀ r : Fin (R + 1),
      interpFunctional L t φ hφ r (fun c => iteratedFDeriv ℝ r.1 f c) =
        ∑ c : ↥t, ∑ k : Fin r.1 → Fin d,
          a r c k * iteratedFDeriv ℝ r.1 f c fun j => Pi.single (k j) 1 := fun r => by
    conv_lhs => rw [← Finset.univ_sum_single (fun c : ↥t => iteratedFDeriv ℝ r.1 f c), map_sum]
    exact Finset.sum_congr rfl fun c _ => ha r c _
  rw [h1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h2 r, Fintype.sum_prod_type]

/-! ### Gaussian combinations -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A finite linear combination of values of a real Gaussian process is Gaussian. -/
theorem hasGaussianLaw_sum_of_isGaussianProcess {T : Type*} {X : T → Ω → ℝ}
    (hX : IsGaussianProcess X P) {ι : Type*} [Fintype ι] (a : ι → ℝ) (idx : ι → T) :
    HasGaussianLaw (fun o => ∑ q, a q * X (idx q) o) P := by
  classical
  have h := hX.of_isGaussianProcess (Y := fun (_ : Unit) o => ∑ q, a q * X (idx q) o) fun _ =>
    ⟨Finset.univ.image idx,
      { toFun := fun y => ∑ q, a q * y ⟨idx q, by simp⟩
        map_add' := fun y z => by
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c y => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          ring }, fun o => by simp [Finset.restrict]⟩
  exact h.hasGaussianLaw_eval ()

/-! ### The Gaussian law of the cube jet -/

/-- ★★★ **The cube jet of a smooth Gaussian field is Gaussian in the jet space**: if the value
process of `ζ` on an open `U ⊇ closedBox d b` is Gaussian and the jet map is measurable, the law
of `o ↦ cubeJet R b (ζ o)` on `CubeJetSpace d R b` is Gaussian. -/
theorem hasGaussianLaw_cubeJet {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : closedBox d b ⊆ U)
    {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o))
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) (R : ℕ)
    (hJ : AEMeasurable (fun o => cubeJet R b (ζ o) (hζ o)) P) :
    HasGaussianLaw (fun o => cubeJet R b (ζ o) (hζ o)) P := by
  classical
  have hK := isCompact_closedBox (d := d) b
  have hpart : ∀ n : ℕ, ∃ t : Finset (Fin d → ℝ), (∀ c ∈ t, c ∈ closedBox d b) ∧
      ∃ φ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ, (∀ c, ContinuousOn (φ c) (closedBox d b)) ∧
      (∀ c x, 0 ≤ φ c x) ∧ (∀ x ∈ closedBox d b, ∑ c ∈ t, φ c x = 1) ∧
      ∀ c x, φ c x ≠ 0 → dist x c < 1 / ((n : ℝ) + 1) :=
    fun n => exists_finite_partition hK (by positivity)
  choose t ht φ hφ hnn hsum hnode using hpart
  have hconv : ∀ o, Tendsto (fun n => jetInterp R b (t n) (φ n) (hφ n) (ζ o)) atTop
      (𝓝 (cubeJet R b (ζ o) (hζ o))) := fun o =>
    tendsto_jetInterp (hζ o) t ht φ hφ hnn hsum hnode
  have hjoint := isGaussianProcess_jetEval_le hU hζ hG R
  refine ⟨⟨fun L => ?_⟩⟩
  -- every functional of the jet is Gaussian
  have hLG : HasGaussianLaw (⇑L ∘ fun o => cubeJet R b (ζ o) (hζ o)) P := by
    refine hasGaussianLaw_of_tendsto_ae (X := fun n o => L (jetInterp R b (t n) (φ n) (hφ n) (ζ o)))
      (fun n => ?_) (Eventually.of_forall fun o => (L.continuous.tendsto _).comp (hconv o))
    obtain ⟨a, ha⟩ := exists_jetInterp_repr L (t n) (φ n) (hφ n)
    -- the index of each evaluation in the joint derivative process
    let idx : (Σ r : Fin (R + 1), ↥(t n) × (Fin r.1 → Fin d)) →
        {p : ℕ × U × (ℕ → (Fin d → ℝ)) // p.1 ≤ R} := fun q =>
      ⟨(q.1.1, ⟨q.2.1.1, hb (ht n _ q.2.1.2)⟩,
        fun j => if h : j < q.1.1 then Pi.single (q.2.2 ⟨j, h⟩) 1 else 0),
        Nat.lt_succ_iff.1 q.1.2⟩
    have hrepr : ∀ o, L (jetInterp R b (t n) (φ n) (hφ n) (ζ o)) = ∑ q, a q *
        iteratedFDeriv ℝ (idx q).1.1 (ζ o) (idx q).1.2.1
          (fun j : Fin (idx q).1.1 => (idx q).1.2.2 j) := fun o => by
      rw [ha (ζ o)]
      refine Finset.sum_congr rfl fun q _ => ?_
      dsimp only [idx]
      congr 1
      congr 1
      funext j
      rw [dif_pos j.2]
    exact (hasGaussianLaw_sum_of_isGaussianProcess hjoint a idx).congr
      (Eventually.of_forall fun o => (hrepr o).symm)
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hJ,
    hLG.map_eq_gaussianReal, integral_map hJ L.continuous.aestronglyMeasurable,
    variance_map L.continuous.measurable.aemeasurable hJ]
  rfl

/-- ★★ **Every moment of the jet norm of a smooth Gaussian field is finite** (Fernique). -/
theorem memLp_cubeJet {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : closedBox d b ⊆ U)
    {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o))
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) (R : ℕ)
    (hJ : AEMeasurable (fun o => cubeJet R b (ζ o) (hζ o)) P) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun o => cubeJet R b (ζ o) (hζ o)) p P :=
  (hasGaussianLaw_cubeJet hU hb hζ hG R hJ).memLp hp

/-- ★★ **The moment hypothesis of DXLIV for a Gaussian field**: `E ‖J_R ζ_o‖^r < ∞`. -/
theorem integrable_norm_cubeJet_pow {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hb : closedBox d b ⊆ U) {ζ : Ω → (Fin d → ℝ) → ℝ} (hζ : ∀ o, ContDiff ℝ ∞ (ζ o))
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) (R : ℕ)
    (hJ : AEMeasurable (fun o => cubeJet R b (ζ o) (hζ o)) P) (r : ℕ) :
    Integrable (fun o => ‖cubeJet R b (ζ o) (hζ o)‖ ^ r) P := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp
  · have h := memLp_cubeJet hU hb hζ hG R hJ (p := r) (by simp)
    exact h.integrable_norm_pow (by exact_mod_cast hr.ne')

/-- ★★★ **The Wick series for a smooth field with a Gaussian value process**: `hint` of the Wick
theorem is discharged by the Gaussian law of the jets (Fernique); what remains explicit is the
measurability of the jet maps, the pointwise variance profile `W` and the absolute-moment
envelope `habs`. -/
theorem integral_empCoeff_gaussian_wick_of_isGaussianProcess {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1)
    {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {ζ : Ω → (Fin d → ℝ) → ℝ}
    (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : closedBox d 1 ⊆ U)
    (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P) {W : (Fin d → ℝ) → ℝ}
    (hW : ContDiff ℝ ∞ W) (hW0 : ∀ x, 0 ≤ W x)
    (hlaw : ∀ x ∈ closedBox d 1,
      HasLaw (fun o => mono k x * ζ o x) (gaussianReal 0 ⟨W x, hW0 x⟩) P)
    (hJ : ∀ R : ℕ, AEMeasurable
      (fun o => cubeJet R 1 (fun v => mono k v * ζ o v) ((contDiff_mono k).mul (hζ o))) P)
    (hmeas : ∀ r R : ℕ, AEStronglyMeasurable
      (fun o => cubeJet R 1 (fun v => η v * (mono k v * ζ o v) ^ r)
        (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) P)
    (habs : Summable fun r : ℕ => ∫ o, |(1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P) :
    Integrable (fun o => empCoeff η (ζ o) h k μ q) P ∧
    ∫ o, empCoeff η (ζ o) h k μ q ∂P = ∑' j : ℕ, (1 / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q := by
  have hG' : IsGaussianProcess (fun (x : U) o => mono k x * ζ o x) P :=
    hG.smul fun x : U => mono k x
  exact integral_empCoeff_gaussian_wick_of_moments hk hμ hq hη hζ hW hW0 hlaw hmeas
    (fun r R => integrable_norm_cubeJet_pow hU hb (fun o => (contDiff_mono k).mul (hζ o)) hG' R
      (hJ R) r) habs

end Grammar
