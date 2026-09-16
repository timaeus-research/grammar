/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CubeJets

/-!
# Holonomy of the closed jet range

The cube jets `cubeJet R b η` of smooth amplitudes form a subset of the jet space
`CubeJetSpace d R b = ∀ r ≤ R, C([0,b]^d, E^{⊗r} → ℝ)`.  On its closure the derivative relations
survive: for `z` in the closure, the ambient extension by zero of the component `r` is
differentiable on the open box with derivative the (curried) component `r+1`
(`hasFDerivAt_jetExt_of_mem_closure`, from `hasFDerivAt_of_tendstoUniformlyOn`).  Consequently
two elements of the closure with the same zeroth-order component agree at every order
(`eq_of_mem_closure_jetRange_of_zero_eq`): zeroth-order evaluations separate the points of the
closed jet range — the holonomicity lemma of consult #160 (A2), which lets Bochner integrals of
random jets be identified from pointwise laws alone.

Zero `sorry`/`axiom`.
-/

open Filter Topology Set
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-- The open box `(0,b)^d`. -/
def openBox (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioo 0 b

theorem isOpen_openBox (b : ℝ) : IsOpen (openBox d b) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem openBox_subset_closedBox (b : ℝ) : openBox d b ⊆ closedBox d b :=
  Set.pi_mono fun _ _ => Ioo_subset_Icc_self

theorem closure_openBox {b : ℝ} (hb : 0 < b) : closure (openBox d b) = closedBox d b := by
  unfold openBox closedBox
  rw [closure_pi_set]
  simp only [closure_Ioo hb.ne]

/-- The set of cube jets of smooth amplitudes. -/
def jetSet (d R : ℕ) (b : ℝ) : Set (CubeJetSpace d R b) :=
  Set.range fun p : {η : (Fin d → ℝ) → ℝ // ContDiff ℝ ∞ η} => cubeJet R b p.1 p.2

theorem cubeJet_mem_jetSet (R : ℕ) (b : ℝ) {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) :
    cubeJet R b η hη ∈ jetSet d R b := ⟨⟨η, hη⟩, rfl⟩

open Classical in
/-- The ambient extension by zero of a jet component. -/
noncomputable def jetExt {R : ℕ} {b : ℝ} (z : CubeJetSpace d R b) (r : Fin (R + 1))
    (y : Fin d → ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ :=
  if hy : y ∈ closedBox d b then z.toPi r ⟨y, hy⟩ else 0

theorem jetExt_of_mem {R : ℕ} {b : ℝ} (z : CubeJetSpace d R b) (r : Fin (R + 1))
    {y : Fin d → ℝ} (hy : y ∈ closedBox d b) : jetExt z r y = z.toPi r ⟨y, hy⟩ := by
  unfold jetExt
  exact dif_pos hy

/-- Component convergence of jets, pointwise on the closed box. -/
theorem tendsto_toPi_apply {R : ℕ} {b : ℝ} {zs : ℕ → CubeJetSpace d R b} {z : CubeJetSpace d R b}
    (hz : Tendsto zs atTop (𝓝 z)) (r : Fin (R + 1)) (x : closedBox d b) :
    Tendsto (fun n => (zs n).toPi r x) atTop (𝓝 (z.toPi r x)) := by
  have h1 : Tendsto (fun n => (zs n).toPi r) atTop (𝓝 (z.toPi r)) :=
    ((continuous_apply r).tendsto (CubeJetSpace.toPi z)).comp hz
  exact ((continuous_eval_const x).tendsto _).comp h1

/-- Component convergence of jets, uniformly on the open box (ambient form). -/
theorem tendstoUniformlyOn_jetExt {R : ℕ} {b : ℝ} {zs : ℕ → CubeJetSpace d R b}
    {z : CubeJetSpace d R b} (hz : Tendsto zs atTop (𝓝 z)) (r : Fin (R + 1)) :
    TendstoUniformlyOn (fun n => jetExt (zs n) r) (jetExt z r) atTop (openBox d b) := by
  have h1 : Tendsto (fun n => (zs n).toPi r) atTop (𝓝 (z.toPi r)) :=
    ((continuous_apply r).tendsto (CubeJetSpace.toPi z)).comp hz
  have h2 := ContinuousMap.tendsto_iff_tendstoUniformly.1 h1
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 h2 ε hε] with n hn y hy
  have hy' : y ∈ closedBox d b := openBox_subset_closedBox b hy
  rw [jetExt_of_mem z r hy', jetExt_of_mem (zs n) r hy']
  exact hn ⟨y, hy'⟩

/-- ★★ **The derivative relation survives in the closure**: for `z` in the closure of the jet set,
the ambient extension of the component `r` has derivative the curried component `r + 1` at every
point of the open box. -/
theorem hasFDerivAt_jetExt_of_mem_closure {R : ℕ} {b : ℝ} {z : CubeJetSpace d R b}
    (hz : z ∈ closure (jetSet d R b)) {r : ℕ} (hr : r + 1 ≤ R) {y : Fin d → ℝ}
    (hy : y ∈ openBox d b) :
    HasFDerivAt (jetExt z ⟨r, by omega⟩)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ
        (jetExt z ⟨r + 1, by omega⟩ y)) y := by
  obtain ⟨zs, hzs, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  choose η hη using hzs
  -- the approximating jets are jets of smooth amplitudes
  have hzs' : ∀ n, zs n = cubeJet R b (η n).1 (η n).2 := fun n => (hη n).symm
  have hf : ∀ n, ∀ x ∈ openBox d b, HasFDerivAt (jetExt (zs n) ⟨r, by omega⟩)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ
        (jetExt (zs n) ⟨r + 1, by omega⟩ x)) x := by
    intro n x hx
    have hsm := (η n).2
    have hdiff : HasFDerivAt (iteratedFDeriv ℝ r (η n).1)
        (fderiv ℝ (iteratedFDeriv ℝ r (η n).1) x) x :=
      ((hsm.differentiable_iteratedFDeriv (m := r) (by exact_mod_cast WithTop.coe_lt_top _)) x
        ).hasFDerivAt
    have hcurry : continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ
        (iteratedFDeriv ℝ (r + 1) (η n).1 x) = fderiv ℝ (iteratedFDeriv ℝ r (η n).1) x := by
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp, LinearIsometryEquiv.apply_symm_apply]
    -- transfer to the ambient extensions, which agree with the iterated derivatives near `x`
    have hopen := (isOpen_openBox b).mem_nhds hx
    have hcongr : jetExt (zs n) ⟨r, by omega⟩ =ᶠ[𝓝 x] iteratedFDeriv ℝ r (η n).1 := by
      filter_upwards [hopen] with w hw
      rw [jetExt_of_mem _ _ (openBox_subset_closedBox b hw), hzs' n]
      rfl
    have hval : jetExt (zs n) ⟨r + 1, by omega⟩ x = iteratedFDeriv ℝ (r + 1) (η n).1 x := by
      rw [jetExt_of_mem _ _ (openBox_subset_closedBox b hx), hzs' n]
      rfl
    rw [hval, hcurry]
    exact hdiff.congr_of_eventuallyEq hcongr
  have hUC : UniformContinuous
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ) :=
    (LinearIsometryEquiv.isometry _).uniformContinuous
  have hf' : TendstoUniformlyOn
      (fun n x => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ
        (jetExt (zs n) ⟨r + 1, by omega⟩ x))
      (fun x => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ
        (jetExt z ⟨r + 1, by omega⟩ x)) atTop (openBox d b) :=
    hUC.comp_tendstoUniformlyOn (tendstoUniformlyOn_jetExt hlim _)
  have hfg : ∀ x ∈ openBox d b, Tendsto (fun n => jetExt (zs n) ⟨r, by omega⟩ x) atTop
      (𝓝 (jetExt z ⟨r, by omega⟩ x)) := by
    intro x hx
    have hx' : x ∈ closedBox d b := openBox_subset_closedBox b hx
    have h := tendsto_toPi_apply hlim ⟨r, by omega⟩ ⟨x, hx'⟩
    simp only [jetExt_of_mem _ _ hx']
    exact h
  exact hasFDerivAt_of_tendstoUniformlyOn (isOpen_openBox b) hf' hf hfg hy

/-- ★★★ **Holonomy of the closed jet range**: two elements of the closure of the jet set with the
same zeroth-order component are equal. -/
theorem eq_of_mem_closure_jetRange_of_zero_eq {R : ℕ} {b : ℝ} (hb : 0 < b)
    {z z' : CubeJetSpace d R b} (hz : z ∈ closure (jetSet d R b))
    (hz' : z' ∈ closure (jetSet d R b))
    (h0 : ∀ x : closedBox d b, z.toPi ⟨0, Nat.succ_pos R⟩ x = z'.toPi ⟨0, Nat.succ_pos R⟩ x) :
    z = z' := by
  have key : ∀ r (hr : r ≤ R), ∀ x : closedBox d b,
      z.toPi ⟨r, Nat.lt_succ_of_le hr⟩ x = z'.toPi ⟨r, Nat.lt_succ_of_le hr⟩ x := by
    intro r
    induction r with
    | zero => intro _ x; exact h0 x
    | succ r ih =>
      intro hr x
      have hr' : r ≤ R := by omega
      have hopen : ∀ y ∈ openBox d b,
          jetExt z ⟨r + 1, by omega⟩ y = jetExt z' ⟨r + 1, by omega⟩ y := by
        intro y hy
        have hz1 := hasFDerivAt_jetExt_of_mem_closure hz hr hy
        have hz2 := hasFDerivAt_jetExt_of_mem_closure hz' hr hy
        have hfun : jetExt z ⟨r, by omega⟩ = jetExt z' ⟨r, by omega⟩ := by
          funext w
          by_cases hw : w ∈ closedBox d b
          · rw [jetExt_of_mem z _ hw, jetExt_of_mem z' _ hw]
            exact ih hr' ⟨w, hw⟩
          · unfold jetExt
            rw [dif_neg hw, dif_neg hw]
        rw [hfun] at hz1
        exact LinearIsometryEquiv.injective
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Fin d → ℝ) ℝ)
          (hz1.unique hz2)
      have hxcl : (x : Fin d → ℝ) ∈ closure (openBox d b) := by
        rw [closure_openBox hb]
        exact x.2
      obtain ⟨ys, hys, hlim⟩ := mem_closure_iff_seq_limit.1 hxcl
      have hmem : ∀ n, ys n ∈ closedBox d b := fun n => openBox_subset_closedBox b (hys n)
      have hlim' : Tendsto (fun n => (⟨ys n, hmem n⟩ : closedBox d b)) atTop (𝓝 x) :=
        tendsto_subtype_rng.2 hlim
      have h1 := ((z.toPi ⟨r + 1, by omega⟩).continuous.tendsto x).comp hlim'
      have h2 := ((z'.toPi ⟨r + 1, by omega⟩).continuous.tendsto x).comp hlim'
      refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
      have h := hopen (ys n) (hys n)
      rw [jetExt_of_mem _ _ (hmem n), jetExt_of_mem _ _ (hmem n)] at h
      exact h.symm
  funext r
  exact ContinuousMap.ext fun x => key r.1 (Nat.lt_succ_iff.1 r.2) x

end Grammar
