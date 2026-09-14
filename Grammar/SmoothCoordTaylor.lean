/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Coordinate Taylor subtraction for smooth amplitudes on a box (consult #114 U1)

The one-coordinate subtraction operators of the smooth-amplitude engine. For a smooth
`G : ℝ^d → ℝ`, the coordinate derivative `pd i G v = d/dt G(v with v_i := t)|_{t = v_i}`
(`pd`, iterated `pdPow`), which commute (`pd_comm`, `pdPow_comm`, from the symmetry of the second
derivative); the coordinate Taylor polynomial of order `p` at `v_i = 0` and its remainder
(`coordTaylor`, `coordRem`, `G = T_i G + R_i G`); the remainder bound along the coordinate line
(★ `coordRem_bound`: `|R_i^{p+1} G (v)| ≤ C v_i^{p+1}/p!` when `|∂_i^{p+1} G| ≤ C` on the line
through `v`), from Mathlib's Taylor theorem; the commutation of the subtraction operators with the
derivatives in the OTHER coordinates (`pdPow_coordRem`); and the iterated remainder over a list
of distinct coordinates (`remList`, ★ `remList_bound`:
`|(∏_{i∈l} R_i) G (v)| ≤ ∏_{i∈l} v_i^{p_i}/(p_i−1)! · sup_box |∏_{i∈l} ∂_i^{p_i} G|`) — the
flatness that makes the facewise Mellin integrals of the smooth engine converge (Astra #114
§1.3–1.4). Zero `sorry`/`axiom`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Coordinate lines and derivatives -/

/-- The coordinate line through `v` in direction `i`. -/
def line (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) : ℝ → ℝ :=
  fun t => G (Function.update v i t)

theorem line_update (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) (s : ℝ) :
    line G i (Function.update v i s) = line G i v := by
  funext t
  simp only [line, Function.update_idem]

theorem line_apply_self (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) :
    line G i v (v i) = G v := by
  simp only [line, Function.update_eq_self]

theorem contDiff_line {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (v : Fin d → ℝ) :
    ContDiff ℝ ∞ (line G i v) :=
  hG.comp (contDiff_update ∞ v i)

/-- The coordinate derivative `∂_i G`. -/
noncomputable def pd (i : Fin d) (G : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun v => deriv (line G i v) (v i)

theorem line_pd (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) :
    line (pd i G) i v = deriv (line G i v) := by
  funext t
  change pd i G (Function.update v i t) = _
  simp only [pd, Function.update_self]
  rw [line_update]

theorem pd_eq_fderiv {G : (Fin d → ℝ) → ℝ} (hG : Differentiable ℝ G) (i : Fin d)
    (v : Fin d → ℝ) : pd i G v = fderiv ℝ G v (Pi.single i 1) := by
  unfold pd line
  have h := (hG (Function.update v i (v i))).hasFDerivAt.comp_hasDerivAt (v i)
    (hasDerivAt_update v i (v i))
  rw [Function.update_eq_self] at h
  exact h.deriv

theorem contDiff_pd {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) :
    ContDiff ℝ ∞ (pd i G) := by
  have h : pd i G = fun v => fderiv ℝ G v (Pi.single i 1) :=
    funext fun v => pd_eq_fderiv (hG.differentiable (by simp)) i v
  rw [h]
  exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The iterated coordinate derivative `∂_i^m G`. -/
noncomputable def pdPow (i : Fin d) (m : ℕ) (G : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  (pd i)^[m] G

theorem pdPow_zero (i : Fin d) (G : (Fin d → ℝ) → ℝ) : pdPow i 0 G = G := rfl

theorem pdPow_succ (i : Fin d) (m : ℕ) (G : (Fin d → ℝ) → ℝ) :
    pdPow i (m + 1) G = pdPow i m (pd i G) := Function.iterate_succ_apply _ _ _

theorem pdPow_succ' (i : Fin d) (m : ℕ) (G : (Fin d → ℝ) → ℝ) :
    pdPow i (m + 1) G = pd i (pdPow i m G) := Function.iterate_succ_apply' _ _ _

theorem contDiff_pdPow {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (m : ℕ) :
    ContDiff ℝ ∞ (pdPow i m G) := by
  induction m generalizing G with
  | zero => exact hG
  | succ m ih => rw [pdPow_succ]; exact ih (contDiff_pd hG i)

/-- The iterated derivative of the coordinate line is the line of the iterated coordinate
derivative. -/
theorem iteratedDeriv_line (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) (m : ℕ) :
    iteratedDeriv m (line G i v) = line (pdPow i m G) i v := by
  induction m generalizing G with
  | zero => simp [pdPow_zero]
  | succ m ih => rw [iteratedDeriv_succ', ← line_pd, ih, pdPow_succ]

/-! ### Symmetry -/

theorem pd_comm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i j : Fin d) :
    pd i (pd j G) = pd j (pd i G) := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  have hpd : ∀ k, pd k G = fun v => fderiv ℝ G v (Pi.single k 1) :=
    fun k => funext fun v => pd_eq_fderiv hd k v
  have hdf : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  funext v
  have hsymm : IsSymmSndFDerivAt ℝ G v := hG.contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [pd_eq_fderiv ((contDiff_pd hG j).differentiable (by simp)) i v,
    pd_eq_fderiv ((contDiff_pd hG i).differentiable (by simp)) j v, hpd j, hpd i,
    fderiv_clm_apply (hdf v) (differentiableAt_const _),
    fderiv_clm_apply (hdf v) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

theorem pdPow_pd_comm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i j : Fin d) (m : ℕ) :
    pdPow i m (pd j G) = pd j (pdPow i m G) := by
  induction m generalizing G with
  | zero => rfl
  | succ m ih => rw [pdPow_succ', pdPow_succ', ih hG, pd_comm (contDiff_pdPow hG i m)]

theorem pdPow_comm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i j : Fin d) (m q : ℕ) :
    pdPow i m (pdPow j q G) = pdPow j q (pdPow i m G) := by
  induction q generalizing G with
  | zero => rfl
  | succ q ih => rw [pdPow_succ', pdPow_succ', pdPow_pd_comm (contDiff_pdPow hG j q), ih hG]

/-! ### The coordinate projection `v ↦ v[i := 0]` -/

theorem contDiff_setZero (i : Fin d) :
    ContDiff ℝ ∞ fun v : Fin d → ℝ => Function.update v i 0 := by
  rw [contDiff_pi]
  intro k
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self]
    exact contDiff_const
  · simp only [Function.update_of_ne hk]
    exact contDiff_apply _ _ k

/-- Lines in direction `j ≠ i` pass through the projection to `v_i = 0`. -/
theorem line_setZero (H : (Fin d → ℝ) → ℝ) {i j : Fin d} (hij : j ≠ i) (v : Fin d → ℝ) :
    line (fun w => H (Function.update w i 0)) j v =
      line H j (Function.update v i 0) := by
  funext t
  simp only [line, Function.update_comm hij]

theorem pd_setZero {H : (Fin d → ℝ) → ℝ} {i j : Fin d} (hij : j ≠ i) (v : Fin d → ℝ) :
    pd j (fun w => H (Function.update w i 0)) v = pd j H (Function.update v i 0) := by
  unfold pd
  rw [line_setZero H hij, Function.update_of_ne hij]

/-! ### Coordinate Taylor subtraction -/

/-- The coordinate Taylor polynomial of order `p` at `v_i = 0`:
`T_i^p G (v) = ∑_{m<p} v_i^m/m! · ∂_i^m G (v[i := 0])`. -/
noncomputable def coordTaylor (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun v => ∑ m ∈ Finset.range p,
    ((m.factorial : ℝ)⁻¹ * v i ^ m) * pdPow i m G (Function.update v i 0)

/-- The coordinate Taylor remainder `R_i^p G = G − T_i^p G`. -/
noncomputable def coordRem (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun v => G v - coordTaylor i p G v

theorem coordTaylor_add_coordRem (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) :
    coordTaylor i p G v + coordRem i p G v = G v := by
  unfold coordRem
  ring

theorem contDiff_coordTaylor {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (p : ℕ) :
    ContDiff ℝ ∞ (coordTaylor i p G) := by
  unfold coordTaylor
  refine ContDiff.sum fun m _ => ContDiff.mul (contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow m))
    ((contDiff_pdPow hG i m).comp (contDiff_setZero i))

theorem contDiff_coordRem {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (p : ℕ) :
    ContDiff ℝ ∞ (coordRem i p G) :=
  hG.sub (contDiff_coordTaylor hG i p)

/-- ★ **The coordinate remainder bound**: if `|∂_i^{p+1} G| ≤ C` on the coordinate line through `v`
inside `[0,b]`, then `|R_i^{p+1} G (v)| ≤ C v_i^{p+1} / p!`. -/
theorem coordRem_bound {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin d) (p : ℕ) {b : ℝ}
    (hb : 0 < b) {v : Fin d → ℝ} (hv : v i ∈ Icc 0 b) {C : ℝ}
    (hC : ∀ t ∈ Icc 0 b, |pdPow i (p + 1) G (Function.update v i t)| ≤ C) :
    |coordRem i (p + 1) G v| ≤ C * v i ^ (p + 1) / p.factorial := by
  have hl : ContDiff ℝ ∞ (line G i v) := contDiff_line hG i v
  have hcast : ((p + 1 : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hl' : ContDiff ℝ (p + 1) (line G i v) := hl.of_le hcast
  have hbnd : ∀ y ∈ Icc (0 : ℝ) b, ‖iteratedDerivWithin (p + 1) (line G i v) (Icc 0 b) y‖ ≤ C := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb) hl'.contDiffAt hy,
      iteratedDeriv_line, Real.norm_eq_abs]
    exact hC y hy
  have h := taylor_mean_remainder_bound hb.le hl'.contDiffOn hv hbnd
  rw [taylor_within_apply] at h
  have hT : ∑ k ∈ Finset.range (p + 1), (((k.factorial : ℝ)⁻¹ * (v i - 0) ^ k) •
      iteratedDerivWithin k (line G i v) (Icc 0 b) 0) = coordTaylor i (p + 1) G v := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb) (hl.of_le
      (by exact_mod_cast le_top : ((k : ℕ) : ℕ∞ω) ≤ ∞)).contDiffAt (left_mem_Icc.2 hb.le),
      iteratedDeriv_line, smul_eq_mul, sub_zero]
    rfl
  rw [hT, line_apply_self, Real.norm_eq_abs, sub_zero] at h
  exact h

/-! ### Commutation with the derivatives in the other coordinates -/

theorem pd_coordTaylor {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {i j : Fin d} (hij : j ≠ i)
    (p : ℕ) : pd j (coordTaylor i p G) = coordTaylor i p (pd j G) := by
  funext v
  have hdiff : ∀ m : ℕ, DifferentiableAt ℝ (line (pdPow i m G) j (Function.update v i 0)) (v j) :=
    fun m => ((contDiff_line (contDiff_pdPow hG i m) j _).differentiable (by simp)).differentiableAt
  have hline : line (coordTaylor i p G) j v = fun t => ∑ m ∈ Finset.range p,
      ((m.factorial : ℝ)⁻¹ * v i ^ m) * line (pdPow i m G) j (Function.update v i 0) t := by
    funext t
    simp only [line, coordTaylor, Function.update_of_ne hij.symm, Function.update_comm hij]
  change deriv (line (coordTaylor i p G) j v) (v j) = _
  rw [hline, show (fun t => ∑ m ∈ Finset.range p,
      ((m.factorial : ℝ)⁻¹ * v i ^ m) * line (pdPow i m G) j (Function.update v i 0) t) =
      ∑ m ∈ Finset.range p, fun t =>
        ((m.factorial : ℝ)⁻¹ * v i ^ m) * line (pdPow i m G) j (Function.update v i 0) t from
      funext fun t => (Finset.sum_apply t (Finset.range p) fun m => fun t =>
        ((m.factorial : ℝ)⁻¹ * v i ^ m) * line (pdPow i m G) j (Function.update v i 0) t).symm,
    deriv_sum fun m _ => (hdiff m).const_mul _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [deriv_const_mul _ (hdiff m)]
  congr 1
  rw [pdPow_pd_comm hG i j m]
  change _ = deriv (line (pdPow i m G) j (Function.update v i 0)) (Function.update v i 0 j)
  rw [Function.update_of_ne hij]

theorem pd_coordRem {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {i j : Fin d} (hij : j ≠ i)
    (p : ℕ) : pd j (coordRem i p G) = coordRem i p (pd j G) := by
  funext v
  have hlineG : DifferentiableAt ℝ (line G j v) (v j) :=
    ((contDiff_line hG j v).differentiable (by simp)).differentiableAt
  have hlineT : DifferentiableAt ℝ (line (coordTaylor i p G) j v) (v j) :=
    ((contDiff_line (contDiff_coordTaylor hG i p) j v).differentiable (by simp)).differentiableAt
  have hline : line (coordRem i p G) j v = line G j v - line (coordTaylor i p G) j v := by
    funext t
    simp only [line, coordRem, Pi.sub_apply]
  change deriv (line (coordRem i p G) j v) (v j) = _
  rw [hline, deriv_sub hlineG hlineT]
  change pd j G v - pd j (coordTaylor i p G) v = _
  rw [pd_coordTaylor hG hij p]
  rfl

theorem pdPow_coordRem {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {i j : Fin d} (hij : j ≠ i)
    (p q : ℕ) : pdPow j q (coordRem i p G) = coordRem i p (pdPow j q G) := by
  induction q generalizing G with
  | zero => rfl
  | succ q ih => rw [pdPow_succ, pd_coordRem hG hij, ih (contDiff_pd hG j), pdPow_succ]

/-! ### Iterated remainders over a list of coordinates -/

variable (p : Fin d → ℕ)

/-- The iterated coordinate remainder `R_{i₁}^{p_{i₁}} ⋯ R_{iₖ}^{p_{iₖ}} G` over a list of
coordinates. -/
noncomputable def remList : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => coordRem i (p i) (remList l G)

/-- The iterated coordinate derivative `∂_{i₁}^{p_{i₁}} ⋯ ∂_{iₖ}^{p_{iₖ}} G` over a list. -/
noncomputable def pdList : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => pdPow i (p i) (pdList l G)

theorem remList_nil (G : (Fin d → ℝ) → ℝ) : remList p [] G = G := rfl

theorem remList_cons (i : Fin d) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    remList p (i :: l) G = coordRem i (p i) (remList p l G) := rfl

theorem pdList_nil (G : (Fin d → ℝ) → ℝ) : pdList p [] G = G := rfl

theorem pdList_cons (i : Fin d) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    pdList p (i :: l) G = pdPow i (p i) (pdList p l G) := rfl

theorem contDiff_remList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (l : List (Fin d)) :
    ContDiff ℝ ∞ (remList p l G) := by
  induction l with
  | nil => exact hG
  | cons i l ih => exact contDiff_coordRem ih i (p i)

theorem contDiff_pdList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (l : List (Fin d)) :
    ContDiff ℝ ∞ (pdList p l G) := by
  induction l with
  | nil => exact hG
  | cons i l ih => exact contDiff_pdPow ih i (p i)

theorem pdPow_remList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {j : Fin d} {l : List (Fin d)}
    (hj : j ∉ l) (q : ℕ) : pdPow j q (remList p l G) = remList p l (pdPow j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    change pdPow j q (coordRem i (p i) (remList p l G)) =
      coordRem i (p i) (remList p l (pdPow j q G))
    rw [pdPow_coordRem (contDiff_remList p hG l) hji, ih hG hjl]

theorem pdPow_pdList {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {j : Fin d} {l : List (Fin d)}
    (hj : j ∉ l) (q : ℕ) : pdPow j q (pdList p l G) = pdList p l (pdPow j q G) := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    rw [pdList_cons, pdList_cons, pdPow_comm (contDiff_pdList p hG l), ih hG hjl]

theorem remList_pdList_comm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {l l' : List (Fin d)}
    (hdisj : ∀ j ∈ l', j ∉ l) : remList p l (pdList p l' G) = pdList p l' (remList p l G) := by
  induction l' generalizing G with
  | nil => rfl
  | cons j l' ih =>
    change remList p l (pdPow j (p j) (pdList p l' G)) =
      pdPow j (p j) (pdList p l' (remList p l G))
    rw [← pdPow_remList p (contDiff_pdList p hG l') (hdisj j (List.mem_cons_self ..)),
      ih hG fun k hk => hdisj k (List.mem_cons_of_mem j hk)]

/-- ★ **The iterated remainder bound**: for distinct coordinates `l` with orders `p_i ≥ 1`, if
`|∂_l^p G| ≤ M` on the box `[0,b]^d`, then `|R_l^p G (v)| ≤ ∏_{i∈l} v_i^{p_i}/(p_i − 1)! · M` on
the box. -/
theorem remList_bound {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {b : ℝ} (hb : 0 < b)
    (hp : ∀ i, 0 < p i) (l : List (Fin d)) (hl : l.Nodup) {M : ℝ}
    (hM : ∀ w : Fin d → ℝ, (∀ i, w i ∈ Icc 0 b) → |pdList p l G w| ≤ M) (v : Fin d → ℝ)
    (hv : ∀ i, v i ∈ Icc 0 b) :
    |remList p l G v| ≤ (l.map fun i => v i ^ p i / ((p i - 1).factorial : ℝ)).prod * M := by
  induction l generalizing G v with
  | nil =>
    rw [remList_nil, List.map_nil, List.prod_nil, one_mul]
    have := hM v hv
    rwa [pdList_nil] at this
  | cons i l ih =>
    have hil : i ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    obtain ⟨q, hq⟩ : ∃ q, p i = q + 1 := ⟨p i - 1, (Nat.succ_pred_eq_of_pos (hp i)).symm⟩
    rw [remList_cons, List.map_cons, List.prod_cons, hq, Nat.add_sub_cancel, mul_assoc]
    have hcomm : pdPow i (q + 1) (remList p l G) = remList p l (pdPow i (q + 1) G) :=
      pdPow_remList p hG hil (q + 1)
    have hM' : ∀ w : Fin d → ℝ, (∀ k, w k ∈ Icc 0 b) →
        |pdList p l (pdPow i (q + 1) G) w| ≤ M := by
      intro w hw
      have h1 := hM w hw
      rwa [pdList_cons, hq, pdPow_pdList p hG hil] at h1
    have hC : ∀ t ∈ Icc (0 : ℝ) b, |pdPow i (q + 1) (remList p l G) (Function.update v i t)| ≤
        (l.map fun k => v k ^ p k / ((p k - 1).factorial : ℝ)).prod * M := by
      intro t ht
      rw [hcomm]
      have hw : ∀ k, Function.update v i t k ∈ Icc 0 b := fun k => by
        by_cases hk : k = i
        · subst hk
          simpa using ht
        · rw [Function.update_of_ne hk]
          exact hv k
      have h := ih (contDiff_pdPow hG i (q + 1)) hl' hM' (Function.update v i t) hw
      rwa [List.map_congr_left fun k hk => by
        rw [Function.update_of_ne fun (h : k = i) => hil (h ▸ hk)]] at h
    have hb' := coordRem_bound (contDiff_remList p hG l) i q hb (hv i) hC
    calc |coordRem i (q + 1) (remList p l G) v|
        ≤ (l.map fun k => v k ^ p k / ((p k - 1).factorial : ℝ)).prod * M * v i ^ (q + 1) /
          q.factorial := hb'
      _ = v i ^ (q + 1) / (q.factorial : ℝ) *
          ((l.map fun k => v k ^ p k / ((p k - 1).factorial : ℝ)).prod * M) := by ring

end SmoothEngine

end Grammar
