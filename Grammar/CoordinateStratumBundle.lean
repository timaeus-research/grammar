import Grammar.GlobalNormalSections

/-!
# The normal bundle of a coordinate stratum (Astra #64 units 14–15, coordinate case)

The strata of the paper's normal-crossing divisor are, in an adapted chart `ℝ^{m+k} = ℝ^m × ℝ^k`,
the coordinate subspaces `{u = 0}` with labelled defining equations `u_l(v, u) = u_l`. We
instantiate the bundle layer there:

* the labelled equations are the last `k` coordinate functionals; their differentials are
  independent and there is a single chart (`stratumEquations`);
* the normal field is constant — the last `k` coordinate directions (`normal_eq`) — and the
  gradient frame is the constant coordinate frame `c ↦ (0, c)` (`frame_eq`), so the normal bundle
  is the trivial bundle `ℝ^m × ℝ^k` (`contMDiffVectorBundle` from CLXXVI);
* **the tubular equivalence** (unit 14 in the coordinate case): `(v, n) ↦ v + n` is a
  diffeomorphism from the total space of the normal bundle onto the ambient chart
  (`tubeDiffeomorph`), with inverse `y ↦ (foot y, normal coordinate y)` — the coordinate-stratum
  tube at infinite radius; StrucDual's `stratum_tube` (CLXXIII) supplies the finite-radius analytic
  tubes on the same stratum;
* the invariant contraction of an observable through this normal bundle is CLXXII's chart
  contraction with `Φ₀ v c = G(v, c)` (`normalContraction_eq_chart`).

Non-claims: no cross-chart gluing of the resolved space; the connection to the resolution charts
of `hironaka` stays through the chart-local statements of CXIII/CLXXII.
-/

open scoped Manifold ContDiff InnerProductSpace
open Bundle Set Function

namespace Grammar

namespace CoordinateStratum

variable (m k : ℕ)

local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)
local notation "ℝᵏ" => EuclideanSpace ℝ (Fin k)
local notation "ℝᵐᵏ" => EuclideanSpace ℝ (Fin (m + k))

/-- The embedding of the stratum `v ↦ (v, 0)`. -/
noncomputable def emb : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + k)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.append (WithLp.ofLp v) 0)
      map_add' := fun v w => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun l => ?_) j <;>
          simp [Fin.append_left, Fin.append_right]
      map_smul' := fun c v => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun l => ?_) j <;>
          simp [Fin.append_left, Fin.append_right] }

/-- The normal directions `c ↦ (0, c)`. -/
noncomputable def nrm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (m + k)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => WithLp.toLp 2 (Fin.append 0 (WithLp.ofLp c))
      map_add' := fun v w => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun l => ?_) j <;>
          simp [Fin.append_left, Fin.append_right]
      map_smul' := fun c v => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun l => ?_) j <;>
          simp [Fin.append_left, Fin.append_right] }

/-- The foot `(v, u) ↦ v`. -/
noncomputable def foot : EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => x (Fin.castAdd k i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

/-- The normal coordinate `(v, u) ↦ u`. -/
noncomputable def ncoord : EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun l => x (Fin.natAdd m l)
      map_add' := fun x y => by ext l; simp
      map_smul' := fun c x => by ext l; simp }

@[simp] theorem emb_apply_castAdd (v : ℝᵐ) (i : Fin m) : emb m k v (Fin.castAdd k i) = v i := by
  simp [emb, Fin.append_left]

@[simp] theorem emb_apply_natAdd (v : ℝᵐ) (l : Fin k) : emb m k v (Fin.natAdd m l) = 0 := by
  simp [emb, Fin.append_right]

@[simp] theorem nrm_apply_castAdd (c : ℝᵏ) (i : Fin m) : nrm m k c (Fin.castAdd k i) = 0 := by
  simp [nrm, Fin.append_left]

@[simp] theorem nrm_apply_natAdd (c : ℝᵏ) (l : Fin k) : nrm m k c (Fin.natAdd m l) = c l := by
  simp [nrm, Fin.append_right]

@[simp] theorem foot_apply (x : ℝᵐᵏ) (i : Fin m) : foot m k x i = x (Fin.castAdd k i) := rfl

@[simp] theorem ncoord_apply (x : ℝᵐᵏ) (l : Fin k) : ncoord m k x l = x (Fin.natAdd m l) := rfl

theorem foot_emb_add_nrm (v : ℝᵐ) (c : ℝᵏ) : foot m k (emb m k v + nrm m k c) = v := by
  ext i
  simp

theorem ncoord_emb_add_nrm (v : ℝᵐ) (c : ℝᵏ) : ncoord m k (emb m k v + nrm m k c) = c := by
  ext l
  simp

theorem emb_foot_add_nrm_ncoord (x : ℝᵐᵏ) : emb m k (foot m k x) + nrm m k (ncoord m k x) = x := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun l => ?_) j <;> simp

/-! ### The labelled defining equations of the stratum -/

theorem natAdd_inj {a b : Fin k} : Fin.natAdd m a = Fin.natAdd m b ↔ a = b := by
  constructor
  · intro h
    ext
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    omega
  · rintro rfl
    rfl

theorem castAdd_ne_natAdd (i : Fin m) (l : Fin k) : Fin.castAdd k i ≠ Fin.natAdd m l := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- The coordinate functionals `u_l(x) = x_{m+l}`. -/
noncomputable def uCoord (l : Fin k) : EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.natAdd m l)

theorem linearIndependent_uCoord : LinearIndependent ℝ fun l => uCoord m k l := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have := congrArg (fun f : EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] ℝ =>
    f (EuclideanSpace.single (Fin.natAdd m l) 1)) hg
  simp only [sum_apply, smul_apply, smul_eq_mul, uCoord, zero_apply] at this
  have h2 : ∀ x : Fin k, g x * EuclideanSpace.proj (Fin.natAdd m x)
      (EuclideanSpace.single (Fin.natAdd m l) (1 : ℝ)) = if x = l then g x else 0 := by
    intro x
    change g x * (EuclideanSpace.single (Fin.natAdd m l) (1 : ℝ)) (Fin.natAdd m x) = _
    simp only [PiLp.single_apply, natAdd_inj]
    split_ifs with h <;> simp [h]
  simp_rw [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

/-- **The stratum as labelled defining equations** (a single chart, everything constant). -/
noncomputable def stratumEquations :
    LabelledDefiningEquations 𝓘(ℝ, ℝᵐ) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin (m + k))) k Unit where
  emb := emb m k
  contMDiff_emb := (emb m k).contDiff.contMDiff
  baseSet := fun _ => univ
  isOpen_baseSet := fun _ => isOpen_univ
  indexAt := fun _ => ()
  mem_baseSet_at := fun _ => mem_univ _
  u := fun _ l => uCoord m k l
  contDiff_u := fun _ l => (uCoord m k l).contDiff
  indep := fun _ x _ => by
    simp only [ContinuousLinearMap.fderiv]
    exact linearIndependent_uCoord m k
  unit := fun _ _ _ _ l => ⟨1, one_ne_zero, by simp⟩

/-- The gradient of a coordinate functional is the coordinate vector. -/
theorem rieszCLM_proj (j : Fin (m + k)) :
    rieszCLM (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] ℝ) =
      EuclideanSpace.single j 1 := by
  apply (InnerProductSpace.toDual ℝ _).injective
  rw [toDual_rieszCLM]
  ext x
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- **The gradient frame is the constant coordinate frame** `c ↦ (0, c)`. -/
theorem frame_eq (v : ℝᵐ) : (stratumEquations m k).frame () v = nrm m k := by
  ext c j
  rw [LabelledDefiningEquations.frame_apply]
  simp only [LabelledDefiningEquations.grad, LabelledDefiningEquations.diff, stratumEquations,
    ContinuousLinearMap.fderiv, uCoord, rieszCLM_proj]
  refine Fin.addCases (fun i => ?_) (fun l => ?_) j
  · simp [castAdd_ne_natAdd]
  · simp only [nrm_apply_natAdd, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, natAdd_inj, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The normal field is constant**: the last `k` coordinate directions. -/
theorem normal_eq (v : ℝᵐ) :
    (stratumEquations m k).normal v = LinearMap.range (nrm m k : ℝᵏ →ₗ[ℝ] ℝᵐᵏ) := by
  rw [← (stratumEquations m k).range_frame () (mem_univ v), frame_eq]

/-- The normal bundle of the coordinate stratum is a `C^∞` vector bundle (CLXXVI). -/
theorem contMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin k))
      (stratumEquations m k).normalAtlas.toCore.Fiber 𝓘(ℝ, ℝᵐ) :=
  (stratumEquations m k).contMDiffVectorBundle

/-! ### The tubular equivalence -/

/-- The total space of the normal bundle of the coordinate stratum. -/
abbrev NB : Type :=
  TotalSpace (EuclideanSpace ℝ (Fin k)) (stratumEquations m k).normalAtlas.toCore.Fiber

theorem realise_eq (p : NB m k) : (stratumEquations m k).normalAtlas.realise p = nrm m k p.2 := by
  rw [NormalFrameAtlas.realise, LabelledDefiningEquations.normalAtlas_frame, frame_eq]

/-- **The tubular map** `(v, n) ↦ v + n` from the normal bundle to the ambient chart. -/
noncomputable def tubeMap (p : NB m k) : ℝᵐᵏ :=
  emb m k p.1 + (stratumEquations m k).normalAtlas.realise p

/-- **The inverse tubular map** `y ↦ (foot y, normal coordinate y)`. -/
noncomputable def tubeInv (y : ℝᵐᵏ) : NB m k := ⟨foot m k y, ncoord m k y⟩

theorem tubeInv_tubeMap (p : NB m k) : tubeInv m k (tubeMap m k p) = p := by
  unfold tubeInv tubeMap
  rw [realise_eq]
  erw [foot_emb_add_nrm, ncoord_emb_add_nrm]

theorem tubeMap_tubeInv (y : ℝᵐᵏ) : tubeMap m k (tubeInv m k y) = y := by
  unfold tubeInv tubeMap
  rw [realise_eq]
  exact emb_foot_add_nrm_ncoord m k y

theorem contMDiff_tubeMap : ContMDiff (𝓘(ℝ, ℝᵐ).prod 𝓘(ℝ, ℝᵏ)) 𝓘(ℝ, ℝᵐᵏ) ∞ (tubeMap m k) :=
  (((emb m k).contDiff.contMDiff).comp (Bundle.contMDiff_proj _)).add
    (stratumEquations m k).normalAtlas.contMDiff_realise

theorem contMDiff_tubeInv : ContMDiff 𝓘(ℝ, ℝᵐᵏ) (𝓘(ℝ, ℝᵐ).prod 𝓘(ℝ, ℝᵏ)) ∞ (tubeInv m k) := by
  have hsrc : ∀ y, tubeInv m k y ∈ (trivializationAt (EuclideanSpace ℝ (Fin k))
      (stratumEquations m k).normalAtlas.toCore.Fiber (0 : ℝᵐ)).source :=
    fun y => (Trivialization.mem_source _).2 (mem_univ _)
  rw [Trivialization.contMDiff_iff hsrc]
  refine ⟨(foot m k).contDiff.contMDiff, ?_⟩
  have h : ∀ y, ((trivializationAt (EuclideanSpace ℝ (Fin k))
      (stratumEquations m k).normalAtlas.toCore.Fiber (0 : ℝᵐ)) (tubeInv m k y)).2 =
        ncoord m k y := by
    intro y
    change ((stratumEquations m k).normalAtlas.toCore.localTriv _ (tubeInv m k y)).2 = _
    rw [VectorBundleCore.localTriv_apply]
    exact (stratumEquations m k).normalAtlas.coordChange_self () (mem_univ _) _
  simp_rw [h]
  exact (ncoord m k).contDiff.contMDiff

/-- **The tubular equivalence of the coordinate stratum**: `(v, n) ↦ v + n` is a diffeomorphism
from the total space of the normal bundle onto the ambient chart. -/
noncomputable def tubeDiffeomorph :
    Diffeomorph (𝓘(ℝ, ℝᵐ).prod 𝓘(ℝ, ℝᵏ)) 𝓘(ℝ, ℝᵐᵏ) (NB m k) ℝᵐᵏ ∞ where
  toFun := tubeMap m k
  invFun := tubeInv m k
  left_inv := tubeInv_tubeMap m k
  right_inv := tubeMap_tubeInv m k
  contMDiff_toFun := contMDiff_tubeMap m k
  contMDiff_invFun := contMDiff_tubeInv m k

theorem tubeDiffeomorph_apply (p : NB m k) : tubeDiffeomorph m k p = tubeMap m k p := rfl

/-- The tubular map restricts to the embedding on the zero section and the foot is the base
projection: the retraction equations. -/
theorem tubeMap_zero (v : ℝᵐ) : tubeMap m k ⟨v, 0⟩ = emb m k v := by
  unfold tubeMap
  rw [realise_eq]
  erw [map_zero, add_zero]

theorem foot_tubeMap (p : NB m k) : foot m k (tubeMap m k p) = p.1 := by
  unfold tubeMap
  rw [realise_eq]
  erw [foot_emb_add_nrm]

/-! ### Agreement with the chart contraction -/

/-- **The invariant contraction through the coordinate normal bundle is CLXXII's chart contraction**
with `Φ₀ v c = G(v, c)`: for an observable `G` on the ambient chart and fibre measures `η v` on
the normal spaces, the contraction equals the frame-coordinate pairing of the normal jet of
`c ↦ G(emb v + nrm c)`. -/
theorem normalContraction_eq_chart (G : ℝᵐᵏ → ℝ) {r : ℕ}
    (η : ∀ v : ℝᵐ, MeasureTheory.Measure ((stratumEquations m k).normal v))
    (hr : ∀ v, MeasureTheory.Integrable (fun ξ : (stratumEquations m k).normal v => ‖ξ‖ ^ r) (η v))
    (v : ℝᵐ) :
    normalContraction (stratumEquations m k).normal η hr
        (fun v n => emb m k v + (n : ℝᵐᵏ)) G v =
      momentFunctional
        ((η v).map (((stratumEquations m k).normalAtlas.frameEquiv () (mem_univ v)).symm :
          (stratumEquations m k).normal v →L[ℝ] ℝᵏ))
        (integrable_norm_pow_map' _ (hr v))
        ((r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun c : ℝᵏ => G (emb m k v + nrm m k c)) 0) := by
  rw [normalContraction_frame' _ _ _ _ η hr ((stratumEquations m k).normalAtlas.frameEquiv ()
    (mem_univ v))]
  have h : ∀ c : ℝᵏ, (((stratumEquations m k).normalAtlas.frameEquiv () (mem_univ v)) c : ℝᵐᵏ) =
      nrm m k c := by
    intro c
    rw [show ((stratumEquations m k).normalAtlas.frameEquiv () (mem_univ v)) c =
      (stratumEquations m k).normalAtlas.frameToN () v c from rfl,
      NormalFrameAtlas.coe_frameToN _ _ (mem_univ v), LabelledDefiningEquations.normalAtlas_frame,
      frame_eq]
  simp only [h]

end CoordinateStratum

end Grammar
