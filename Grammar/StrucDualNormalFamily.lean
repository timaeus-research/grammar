import Grammar.ChartNormalFamily
import StrucDual.Geometry.EmbeddedTubular
import StrucDual.Geometry.ChartLocalTubular
import StrucDual.Geometry.TangentWellDefined

/-!
# The StrucDual realisation of the chosen normal family (Astra #64 unit 8)

`timaeus-research/strucdual` (Mathlib v4.33.1) proves the ambient-Euclidean tubular neighbourhood
theorem: a compact set `S ⊆ ℝ^d` with a compatible analytic LCI atlas has an analytic normal tubular
chart (`exists_analyticNormalTubularChart_of_atlas`), i.e. a radius `ε`, an open tube `U`, a foot
map `proj` and the normal coordinate `ncoord x = x − proj x ∈ N (proj x)`, with uniqueness of the
decomposition inside the radius. This file realises the chosen normal family of CLXVI on such a
tube:

* **the additive family** `Φ_s n = s + n` on the normal field `N` (`additiveFamily`); on the
  certified domain (`s ∈ S`, `‖n‖ < ε`) the tube map inverts it — `proj (s + n) = s`,
  `ncoord (s + n) = n` (`proj_additiveFamily`, `ncoord_additiveFamily`), the point lies in the tube
  (`additiveFamily_mem_tube`), every point of the tube decomposes (`additiveFamily_decomp`), and the
  family is injective on the certified domain (`additiveFamily_injective`); smoothness and
  analyticity of the inverse coordinates are StrucDual's (`contDiffAt_proj`, `analyticAt_proj`);
* **jets**: the chosen-normal jet of the additive family is the ambient jet restricted to `N s`
  (`rawNormalJet_additiveFamily`, from CLXVI), and its contraction with a normal-fibre moment is the
  restricted ambient pairing (`normalContraction_additiveFamily`);
* **existence**: for a compact `S` with a compatible analytic LCI atlas the additive family on
  `N = A.normal` carries an analytic tube (`exists_analyticTube_of_atlas`), and a coordinate stratum
  `{u = 0}` in an ambient chart carries one at every radius (`stratum_tube`);
* **the chart-local coefficient bridge**: StrucDual's mixed normal derivative
  `normalCoeff F γ v = ∂^γ_u F(v,0)` (a fixed-order fold of directional derivatives) equals the
  weight component `∂^γ` of CLXVIII of the fibre jet `D^{|γ|}(F(v,·))(0)` for analytic `F`
  (`normalCoeff_eq_weightComponent`), so StrucDual's analyticity of the normal coefficients in the
  tangential variable (`analyticAt_normalCoeff`) transfers to the weight components of the fibre
  jets (`analyticAt_weightComponent_fibre`) — the chart-local content of `rem:analytic_tubular`.

Non-claims: no inverse function theorem is reproved; StrucDual's hypotheses (compactness, the LCI
atlas) are kept verbatim; no bundle topology; no existence statement on the paper's resolved `U`.
-/

open scoped ContDiff
open Finset StrucDual.Geometry

namespace Grammar

/-! ### The additive family on a normal tubular chart -/

section Tube

variable {d : ℕ} (N : (Fin d → ℝ) → Submodule ℝ (Fin d → ℝ)) {S : Set (Fin d → ℝ)}

/-- **The additive normal family** `Φ_s n = s + n` of a normal field `N`. -/
def additiveFamily : ∀ s : Fin d → ℝ, N s → (Fin d → ℝ) := fun s n => s + (n : Fin d → ℝ)

@[simp] theorem additiveFamily_apply (s : Fin d → ℝ) (n : N s) :
    additiveFamily N s n = s + (n : Fin d → ℝ) := rfl

variable {N} (T : NormalTubularChart N S)

/-- On the certified domain the tube map inverts the additive family: the foot of `s + n` is `s`. -/
theorem proj_additiveFamily {s : Fin d → ℝ} (hs : s ∈ S) (n : N s)
    (hn : ‖(n : Fin d → ℝ)‖ < T.eps) : T.proj (additiveFamily N s n) = s := by
  have hx : additiveFamily N s n ∈ T.U := (T.mem_U_iff _).2 ⟨s, hs, n, n.2, hn, rfl⟩
  exact (T.proj_eq_of_decomp hx hs n.2 hn rfl).1

/-- On the certified domain the normal coordinate of `s + n` is `n`. -/
theorem ncoord_additiveFamily {s : Fin d → ℝ} (hs : s ∈ S) (n : N s)
    (hn : ‖(n : Fin d → ℝ)‖ < T.eps) : T.ncoord (additiveFamily N s n) = n := by
  have hx : additiveFamily N s n ∈ T.U := (T.mem_U_iff _).2 ⟨s, hs, n, n.2, hn, rfl⟩
  exact (T.proj_eq_of_decomp hx hs n.2 hn rfl).2

theorem additiveFamily_mem_tube {s : Fin d → ℝ} (hs : s ∈ S) (n : N s)
    (hn : ‖(n : Fin d → ℝ)‖ < T.eps) : additiveFamily N s n ∈ T.U :=
  (T.mem_U_iff _).2 ⟨s, hs, n, n.2, hn, rfl⟩

/-- Every point of the tube is the additive family applied to its foot and normal coordinate. -/
theorem additiveFamily_decomp {y : Fin d → ℝ} (hy : y ∈ T.U) :
    additiveFamily N (T.proj y) ⟨T.ncoord y, T.ncoord_mem hy⟩ = y := by
  simp only [additiveFamily_apply]
  exact (T.decomp y).symm

/-- **Injectivity of the additive family on the certified domain.** -/
theorem additiveFamily_injective {s₁ s₂ : Fin d → ℝ} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (n₁ : N s₁)
    (n₂ : N s₂) (hn₁ : ‖(n₁ : Fin d → ℝ)‖ < T.eps) (hn₂ : ‖(n₂ : Fin d → ℝ)‖ < T.eps)
    (h : additiveFamily N s₁ n₁ = additiveFamily N s₂ n₂) :
    s₁ = s₂ ∧ (n₁ : Fin d → ℝ) = n₂ :=
  T.unique hs₁ hs₂ n₁.2 n₂.2 hn₁ hn₂ h

/-- The chosen-normal jet of the additive family is the ambient jet restricted to `N s`. -/
theorem rawNormalJet_additiveFamily {F : (Fin d → ℝ) → ℝ} {r : ℕ} (hF : ContDiff ℝ r F)
    (s : Fin d → ℝ) :
    rawNormalJet N (additiveFamily N) F s r =
      (iteratedFDeriv ℝ r F s).compContinuousLinearMap fun _ => (N s).subtypeL :=
  rawNormalJet_additive N hF s

/-- The invariant contraction of the additive family is the restricted ambient pairing
`(1/r!) ∫ D^rF(s)(ξ,…,ξ) dη_s`. -/
theorem normalContraction_additiveFamily {F : (Fin d → ℝ) → ℝ} {r : ℕ} (hF : ContDiff ℝ r F)
    (η : ∀ s : Fin d → ℝ, MeasureTheory.Measure (N s))
    (hr : ∀ s, MeasureTheory.Integrable (fun ξ : N s => ‖ξ‖ ^ r) (η s)) (s : Fin d → ℝ) :
    normalContraction N η hr (additiveFamily N) F s =
      ∫ ξ, (r.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ r F s (fun _ => (ξ : Fin d → ℝ)) ∂η s := by
  rw [normalContraction_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  unfold homogeneousTaylor
  rw [← rawNormalJet_eq_normalJet, rawNormalJet_additiveFamily hF s,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

end Tube

/-! ### Existence of tubes -/

section Existence

variable {d r : ℕ} {S : Set (Fin d → ℝ)}

/-- **StrucDual's embedded tubular theorem for the additive family**: a compact set with a
compatible analytic LCI atlas carries an analytic normal tubular chart for its orthogonal normal
field. -/
theorem exists_analyticTube_of_atlas (hS : IsCompact S) (A : CompatibleAnalyticLCIAtlas r S) :
    Nonempty (AnalyticNormalTubularChart A.normal S) :=
  exists_analyticNormalTubularChart_of_atlas hS A

/-- A coordinate stratum `{u = 0}` of an ambient chart `ℝ^{m+k}` is an analytic tube at every
radius, for the normal field `range (stratumJ)ᵀ` (the last `k` coordinates). -/
theorem stratum_tube (m k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (AnalyticNormalTubularChart (fun _ => normalSpaceOf (stratumJ m k))
      {x : Fin (m + k) → ℝ | stratumProj m k x = 0}) :=
  (stratum_analyticTubularChart m k ε hε).map fun T => T.toAnalyticNormalTubularChart

end Existence

/-! ### The chart-local coefficient bridge -/

section Bridge

variable {m k : ℕ}

/-- The direction tuple of a list of normal labels. -/
def dirsOf (L : List (Fin k)) : Fin L.length → (Fin m → ℝ) × (Fin k → ℝ) :=
  fun s => normalDir m (L.get s)

/-- The iterated directional derivative along a list of normal labels. -/
noncomputable def iterD (L : List (Fin k)) (g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ) :
    (Fin m → ℝ) × (Fin k → ℝ) → ℝ :=
  fun q => iteratedFDeriv ℝ L.length g q (dirsOf L)

theorem iterD_nil (g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ) : iterD ([] : List (Fin k)) g = g := by
  funext q
  simp [iterD, iteratedFDeriv_zero_apply]

theorem dirsOf_cons (j : Fin k) (L : List (Fin k)) :
    dirsOf (j :: L) = Fin.cons (normalDir m j) (dirsOf L) := by
  funext s
  refine Fin.cases rfl (fun t => rfl) s

/-- One directional derivative of an iterated derivative is the next iterated derivative. -/
theorem fderiv_iteratedFDeriv_apply_dir {g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (q v : (Fin m → ℝ) × (Fin k → ℝ)) (w : Fin n → (Fin m → ℝ) × (Fin k → ℝ)) :
    fderiv ℝ (fun p => iteratedFDeriv ℝ n g p w) q v =
      iteratedFDeriv ℝ (n + 1) g q (Fin.cons v w) := by
  rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons,
    fderiv_continuousMultilinear_apply_const_apply]
  exact hg.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top n)) q

theorem normalPDeriv_iterD {g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (j : Fin k)
    (L : List (Fin k)) :
    normalPDeriv j (iterD L g) = iterD (j :: L) g := by
  funext q
  unfold normalPDeriv iterD
  rw [fderiv_iteratedFDeriv_apply_dir hg, dirsOf_cons]
  rfl

theorem iterate_normalPDeriv_iterD {g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (j : Fin k) (a : ℕ) (L : List (Fin k)) :
    (normalPDeriv j)^[a] (iterD L g) = iterD (List.replicate a j ++ L) g := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, normalPDeriv_iterD hg]
    rfl

/-- The label list accumulated by StrucDual's fold. -/
def foldLabels (γ : Fin k →₀ ℕ) (l : List (Fin k)) (L : List (Fin k)) : List (Fin k) :=
  l.foldl (fun M j => List.replicate (γ j) j ++ M) L

theorem foldl_normalPDeriv_iterD {g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (γ : Fin k →₀ ℕ) :
    ∀ (l L : List (Fin k)),
      l.foldl (fun h j => (normalPDeriv j)^[γ j] h) (iterD L g) = iterD (foldLabels γ l L) g := by
  intro l
  induction l with
  | nil => intro L; rfl
  | cons a t ih =>
    intro L
    rw [List.foldl_cons, iterate_normalPDeriv_iterD hg]
    exact ih _

/-- **StrucDual's mixed normal derivative is an iterated directional derivative** along the label
list `foldLabels γ (finRange k) []`. -/
theorem normalDeriv_eq_iterD {g : (Fin m → ℝ) × (Fin k → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (γ : Fin k →₀ ℕ) :
    normalDeriv γ g = iterD (foldLabels γ (List.finRange k) []) g := by
  unfold normalDeriv
  rw [← iterD_nil g]
  exact foldl_normalPDeriv_iterD hg γ _ _

theorem count_foldLabels (γ : Fin k →₀ ℕ) (i : Fin k) :
    ∀ (l : List (Fin k)), l.Nodup → ∀ L : List (Fin k),
      (foldLabels γ l L).count i = L.count i + if i ∈ l then γ i else 0 := by
  intro l
  induction l with
  | nil => intro _ L; simp [foldLabels]
  | cons a t ih =>
    intro hnd L
    rw [List.nodup_cons] at hnd
    have h := ih hnd.2 (List.replicate (γ a) a ++ L)
    unfold foldLabels at h ⊢
    rw [List.foldl_cons, h, List.count_append, List.count_replicate]
    by_cases hia : i = a
    · subst hia
      simp [hnd.1, add_comm]
    · have hia' : a ≠ i := Ne.symm hia
      simp [hia', hia]

theorem count_foldLabels_finRange (γ : Fin k →₀ ℕ) (i : Fin k) :
    (foldLabels γ (List.finRange k) []).count i = γ i := by
  rw [count_foldLabels γ i _ (List.nodup_finRange k), List.count_nil, zero_add,
    if_pos (List.mem_finRange i)]

/-- The number of slots of a list carrying a given label is its count. -/
theorem card_filter_get_eq_count (L : List (Fin k)) (i : Fin k) :
    #{s : Fin L.length | L.get s = i} = L.count i := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [Finset.card_filter] at ih ⊢
    change ∑ s : Fin (t.length + 1), (if (a :: t).get s = i then 1 else 0) = _
    have h0 : (a :: t).get 0 = a := rfl
    have hs : ∀ s : Fin t.length, (a :: t).get (Fin.succ s) = t.get s := fun s => rfl
    rw [Fin.sum_univ_succ, List.count_cons]
    simp only [h0, hs, beq_iff_eq]
    rw [ih]
    split_ifs <;> omega

/-- The weight of the accumulated label list is `γ`. -/
theorem weightOf_foldLabels (γ : Fin k →₀ ℕ) :
    weightOf (fun s => (foldLabels γ (List.finRange k) []).get s) = fun i => γ i := by
  funext i
  unfold weightOf
  rw [card_filter_get_eq_count, count_foldLabels_finRange]

variable {F : (Fin m → ℝ) × (Fin k → ℝ) → ℝ}

/-- StrucDual's `normalDeriv` at `(v, 0)` is a jet component of the fibre jet of `u ↦ F (v, u)`. -/
theorem normalCoeff_eq_jetComponent (hF : ContDiff ℝ ∞ F) (γ : Fin k →₀ ℕ) (v : Fin m → ℝ) :
    normalCoeff F γ v =
      jetComponent
        (normalJet (fun u : Fin k → ℝ => F (v, u)) (foldLabels γ (List.finRange k) []).length)
        (fun s => (foldLabels γ (List.finRange k) []).get s) := by
  unfold normalCoeff jetComponent normalJet
  rw [normalDeriv_eq_iterD hF γ, iteratedFDeriv_fibre_eq hF _ v,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **The chart-local coefficient bridge**: for analytic `F`, StrucDual's mixed normal derivative
`∂^γ_u F(v,0)` is the weight component `∂^γ` of the fibre jet `D^{|γ|}(F(v,·))(0)`. -/
theorem normalCoeff_eq_weightComponent (hF : ∀ p, AnalyticAt ℝ F p) (γ : Fin k →₀ ℕ)
    (v : Fin m → ℝ) {r : ℕ} (hr : r = ∑ j, γ j) :
    normalCoeff F γ v =
      weightComponent (normalJet (fun u : Fin k → ℝ => F (v, u)) r) (fun j => γ j) := by
  have hF' : ContDiff ℝ ∞ F := contDiff_iff_contDiffAt.2 fun p => (hF p).contDiffAt
  have hlen : (foldLabels γ (List.finRange k) []).length = ∑ j, γ j := by
    rw [← weightOf_foldLabels γ]
    exact (sum_weightOf _).symm
  have key : ∀ n (hn : n = (foldLabels γ (List.finRange k) []).length),
      weightComponent (normalJet (fun u : Fin k → ℝ => F (v, u)) n) (fun j => γ j) =
        normalCoeff F γ v := by
    intro n hn
    subst hn
    rw [normalCoeff_eq_jetComponent hF' γ v, ← weightOf_foldLabels γ]
    exact weightComponent_eq _ (isSymmForm_normalJet ((analyticAt_fibre hF v 0).contDiffAt)) _
  exact (key r (hr.trans hlen.symm)).symm

/-- **Analyticity of the fibre weight components in the tangential variable** (the chart-local
content of `rem:analytic_tubular`): transported from StrucDual's `analyticAt_normalCoeff`. -/
theorem analyticAt_weightComponent_fibre (hF : ∀ p, AnalyticAt ℝ F p) (γ : Fin k →₀ ℕ) {r : ℕ}
    (hr : r = ∑ j, γ j) (v₀ : Fin m → ℝ) :
    AnalyticAt ℝ
      (fun v => weightComponent (normalJet (fun u : Fin k → ℝ => F (v, u)) r) (fun j => γ j))
      v₀ := by
  have h : (fun v => weightComponent (normalJet (fun u : Fin k → ℝ => F (v, u)) r) (fun j => γ j)) =
      normalCoeff F γ := by
    funext v
    exact (normalCoeff_eq_weightComponent hF γ v hr).symm
  rw [h]
  exact analyticAt_normalCoeff hF γ v₀

end Bridge

end Grammar
