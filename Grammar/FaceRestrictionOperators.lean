/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceSplit
import Grammar.CoordinateFrechetBridge

/-!
# Face restriction commutes with the tangential Taylor operators (consult #124 unit C5a)

The smooth engine differentiates and Taylor-subtracts amplitudes `F : ℝ^d → ℝ` one coordinate at
a time: `pd i F v = d/dt F(v with v_i := t)|_{t = v_i}`, the coordinate Taylor polynomial
`coordTaylor i p F` at `v_i = 0`, its remainder `coordRem i p F = F − coordTaylor i p F`, and the
iterated remainder `remList p l F = R_{l₀} R_{l₁} ⋯ F` over a list of coordinates. For a Taylor
set `J ⊆ Fin d` with complement `K`, the flat face amplitude of `SmoothFaceSplit` is

  `faceAmp p J F m w = (R_K^p ∂^m_J F)(0_J, w)`,

the `K`-remainder of the normal derivative `∂^m_J F`, evaluated on the face `v_J = 0` and read as
a function of the `K`-coordinates `w : {i // ¬ inJ J i} → ℝ`. The chart-face distributions of
consult #124 need this amplitude to be a Taylor remainder OF A FUNCTION ON THE FACE: the
restriction `faceRes J F = F ∘ glue J 0` should absorb the `K`-operators.

## The operators on a general index type

The engine's operators are defined on `Fin d → ℝ`; the face space `{i // ¬ inJ J i} → ℝ` is a pi
type over a subtype. The definitions only use `Function.update`, so they make sense for any
index type with decidable equality: `lineι`, `pdι`, `pdPowι`, `coordTaylorι`, `coordRemι`,
`remListι`, `pdMultiι`. On `Fin d` they are the engine's operators by `rfl`
(`pdι_fin`, `remListι_fin`, …), and for a finite index type they preserve smoothness exactly as
before (`contDiff_pdι`, `contDiff_remListι`, `contDiff_pdMultiι`, from `hasDerivAt_update` and
`contDiff_update`).

## Restriction commutes with the tangential operators

The one identity everything rests on is `glue_update_of_not_mem`: for `i ∉ J`, changing the
`i`-th coordinate of a glued point `glue J u w` is gluing the changed face coordinate,
`(glue J u w)[i := t] = glue J u (w[⟨i,_⟩ := t])`. Hence the coordinate line of `F` through a face
point in a tangential direction is the coordinate line of the restriction (`lineι_faceRes`), and
so, writing `k : {i // ¬ inJ J i}` for a face coordinate,

  `faceRes J (pd k F) = pdι k (faceRes J F)`                         (`faceRes_pd`)
  `faceRes J (pdPow k m F) = pdPowι k m (faceRes J F)`               (`faceRes_pdPow`)
  `faceRes J (coordTaylor k q F) = coordTaylorι k q (faceRes J F)`   (`faceRes_coordTaylor`)
  `faceRes J (coordRem k q F) = coordRemι k q (faceRes J F)`         (`faceRes_coordRem`)

and, for any list `l` of face coordinates, ★★ `faceRes_remList`:
`faceRes J (remList p (l.map val) F) = remListι (p ∘ val) l (faceRes J F)`. The flat coordinate
list `lK J` is the value list of the face list `lKface J` (all face coordinates, once, in the
standard order: `lKface_map_val`, `nodup_lKface`, `mem_lKface`), which gives the face amplitude
identity ★★★ `faceAmp_eq`:

  `faceAmp p J F m w = remListι (p ∘ val) (lKface J) (faceRes J (∂^m_J F)) w`.

The `J`-derivatives are normal to the face and stay outside as the restriction of `∂^m_J F`.

## Order independence

Remainders in distinct coordinates commute (`coordRem_comm`, from the commutation of the Taylor
polynomials with each other and with the remainders in `SmoothCoordTaylor`), so the iterated
remainder of a smooth function over a list does not depend on the order of the list
(`remList_perm`, by induction on the permutation). Transported through the restriction, the face
remainder `remListι` is order independent for every smooth function on the face space
(`remListι_perm_face`: every smooth `G` on the face is the restriction of the smooth `G ∘ projK`),
and the face amplitude is the face remainder over ANY enumeration of the face coordinates
(`faceAmp_eq_remListι`).

## The face inclusion as a continuous linear map

`glue J 0` is a continuous linear map `glueZeroCLM J` of operator norm at most one for the sup
norms (`norm_glueZeroCLM_le`), so restriction preserves smoothness (`contDiff_faceRes`) and
does not increase the Fréchet jets: ★ `norm_iteratedFDeriv_faceRes_le`,
`‖D^r (faceRes J F) w‖ ≤ ‖D^r F (glue J 0 w)‖`, from `iteratedFDeriv_comp_right` and the
multilinear operator-norm bound. The closed box in face coordinates is
`glue_zero_mem_closedBox_iff`. Zero `sorry`/`axiom`.
-/

open Set
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### The coordinate operators on a general index type -/

section General

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate line through `v` in direction `i`. -/
def lineι (G : (ι → ℝ) → ℝ) (i : ι) (v : ι → ℝ) : ℝ → ℝ :=
  fun t => G (Function.update v i t)

/-- The coordinate derivative `∂_i G`. -/
noncomputable def pdι (i : ι) (G : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun v => deriv (lineι G i v) (v i)

/-- The iterated coordinate derivative `∂_i^m G`. -/
noncomputable def pdPowι (i : ι) (m : ℕ) (G : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  (pdι i)^[m] G

/-- The coordinate Taylor polynomial of order `p` at `v_i = 0`. -/
noncomputable def coordTaylorι (i : ι) (p : ℕ) (G : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun v => ∑ m ∈ Finset.range p,
    ((m.factorial : ℝ)⁻¹ * v i ^ m) * pdPowι i m G (Function.update v i 0)

/-- The coordinate Taylor remainder `R_i^p G = G − T_i^p G`. -/
noncomputable def coordRemι (i : ι) (p : ℕ) (G : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun v => G v - coordTaylorι i p G v

variable (p : ι → ℕ)

/-- The iterated coordinate remainder over a list of coordinates. -/
noncomputable def remListι : List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], G => G
  | i :: l, G => coordRemι i (p i) (remListι l G)

/-- The iterated coordinate derivative `∏_{i ∈ l} ∂_i^{m_i}` over a list of coordinates. -/
noncomputable def pdMultiι : List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], G => G
  | i :: l, G => pdPowι i (p i) (pdMultiι l G)

theorem pdPowι_zero (i : ι) (G : (ι → ℝ) → ℝ) : pdPowι i 0 G = G := rfl

theorem pdPowι_succ (i : ι) (m : ℕ) (G : (ι → ℝ) → ℝ) :
    pdPowι i (m + 1) G = pdPowι i m (pdι i G) := Function.iterate_succ_apply _ _ _

theorem pdPowι_succ' (i : ι) (m : ℕ) (G : (ι → ℝ) → ℝ) :
    pdPowι i (m + 1) G = pdι i (pdPowι i m G) := Function.iterate_succ_apply' _ _ _

theorem coordTaylorι_apply (i : ι) (p : ℕ) (G : (ι → ℝ) → ℝ) (v : ι → ℝ) :
    coordTaylorι i p G v = ∑ m ∈ Finset.range p,
      ((m.factorial : ℝ)⁻¹ * v i ^ m) * pdPowι i m G (Function.update v i 0) := rfl

theorem coordRemι_apply (i : ι) (p : ℕ) (G : (ι → ℝ) → ℝ) (v : ι → ℝ) :
    coordRemι i p G v = G v - coordTaylorι i p G v := rfl

theorem remListι_nil (G : (ι → ℝ) → ℝ) : remListι p [] G = G := rfl

theorem remListι_cons (i : ι) (l : List ι) (G : (ι → ℝ) → ℝ) :
    remListι p (i :: l) G = coordRemι i (p i) (remListι p l G) := rfl

theorem pdMultiι_nil (G : (ι → ℝ) → ℝ) : pdMultiι p [] G = G := rfl

theorem pdMultiι_cons (i : ι) (l : List ι) (G : (ι → ℝ) → ℝ) :
    pdMultiι p (i :: l) G = pdPowι i (p i) (pdMultiι p l G) := rfl

/-! ### Regularity -/

variable [Fintype ι]

theorem contDiff_lineι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) (v : ι → ℝ) :
    ContDiff ℝ ∞ (lineι G i v) :=
  hG.comp (contDiff_update ∞ v i)

theorem pdι_eq_fderiv {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) (v : ι → ℝ) :
    pdι i G v = fderiv ℝ G v (Pi.single i 1) := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  unfold pdι lineι
  have h := (hd (Function.update v i (v i))).hasFDerivAt.comp_hasDerivAt (v i)
    (hasDerivAt_update v i (v i))
  rw [Function.update_eq_self] at h
  exact h.deriv

theorem contDiff_pdι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) :
    ContDiff ℝ ∞ (pdι i G) := by
  have h : pdι i G = fun v => fderiv ℝ G v (Pi.single i 1) :=
    funext fun v => pdι_eq_fderiv hG i v
  rw [h]
  exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_pdPowι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) (m : ℕ) :
    ContDiff ℝ ∞ (pdPowι i m G) := by
  induction m generalizing G with
  | zero => exact hG
  | succ m ih => rw [pdPowι_succ]; exact ih (contDiff_pdι hG i)

theorem contDiff_setZeroι (i : ι) :
    ContDiff ℝ ∞ fun v : ι → ℝ => Function.update v i 0 := by
  rw [contDiff_pi]
  intro k
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self]
    exact contDiff_const
  · simp only [Function.update_of_ne hk]
    exact contDiff_apply _ _ k

theorem contDiff_coordTaylorι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) (p : ℕ) :
    ContDiff ℝ ∞ (coordTaylorι i p G) := by
  unfold coordTaylorι
  exact ContDiff.sum fun m _ => ContDiff.mul (contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow m))
    ((contDiff_pdPowι hG i m).comp (contDiff_setZeroι i))

theorem contDiff_coordRemι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i : ι) (p : ℕ) :
    ContDiff ℝ ∞ (coordRemι i p G) :=
  hG.sub (contDiff_coordTaylorι hG i p)

theorem contDiff_remListι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (l : List ι) :
    ContDiff ℝ ∞ (remListι p l G) := by
  induction l with
  | nil => exact hG
  | cons i l ih => exact contDiff_coordRemι ih i (p i)

theorem contDiff_pdMultiι {G : (ι → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (l : List ι) :
    ContDiff ℝ ∞ (pdMultiι p l G) := by
  induction l with
  | nil => exact hG
  | cons i l ih => exact contDiff_pdPowι ih i (p i)

end General

variable {d : ℕ}

/-! ### On `Fin d` the general operators are the engine's -/

theorem lineι_fin (G : (Fin d → ℝ) → ℝ) (i : Fin d) (v : Fin d → ℝ) :
    lineι G i v = line G i v := rfl

theorem pdι_fin (i : Fin d) (G : (Fin d → ℝ) → ℝ) : pdι i G = pd i G := rfl

theorem pdPowι_fin (i : Fin d) (m : ℕ) (G : (Fin d → ℝ) → ℝ) : pdPowι i m G = pdPow i m G := rfl

theorem coordTaylorι_fin (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ) :
    coordTaylorι i p G = coordTaylor i p G := rfl

theorem coordRemι_fin (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ) :
    coordRemι i p G = coordRem i p G := rfl

theorem remListι_fin (p : Fin d → ℕ) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    remListι p l G = remList p l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih => rw [remListι_cons, remList_cons, ih]; rfl

theorem pdMultiι_fin (m : Fin d → ℕ) (l : List (Fin d)) (G : (Fin d → ℝ) → ℝ) :
    pdMultiι m l G = pdMulti m l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih => rw [pdMultiι_cons, pdMulti_cons, ih]; rfl

/-! ### Remainders in distinct coordinates commute -/

theorem coordRem_comm {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {i j : Fin d} (hij : j ≠ i)
    (p q : ℕ) : coordRem j q (coordRem i p G) = coordRem i p (coordRem j q G) := by
  funext v
  have h1 := coordTaylor_coordRem hG hij p q v
  have h2 := coordTaylor_coordRem hG hij.symm q p v
  have h3 := coordTaylor_comm hG hij p q
  change coordRem i p G v - coordTaylor j q (coordRem i p G) v =
    coordRem j q G v - coordTaylor i p (coordRem j q G) v
  rw [h1, h2, ← h3]
  simp only [coordRem]
  ring

/-- The iterated remainder of a smooth function does not depend on the order of the list. -/
theorem remList_perm (p : Fin d → ℕ) {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    {l l' : List (Fin d)} (hl : l.Perm l') : remList p l G = remList p l' G := by
  induction hl generalizing G with
  | nil => rfl
  | cons i _ ih => rw [remList_cons, remList_cons, ih hG]
  | swap i j l =>
    rw [remList_cons, remList_cons, remList_cons, remList_cons]
    by_cases hij : i = j
    · subst hij; rfl
    · exact coordRem_comm (contDiff_remList p hG l) (Ne.symm hij) _ _
  | trans _ _ ih₁ ih₂ => rw [ih₁ hG, ih₂ hG]

/-! ### The face restriction and the face inclusion -/

variable (J : Finset (Fin d))

/-- The restriction of `F` to the face `v_J = 0`, as a function of the face coordinates. -/
def faceRes (F : (Fin d → ℝ) → ℝ) : ({i // ¬ inJ J i} → ℝ) → ℝ := fun w => F (glue J 0 w)

theorem faceRes_apply (F : (Fin d → ℝ) → ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    faceRes J F w = F (glue J 0 w) := rfl

/-- Changing a face coordinate of a glued point is gluing the changed face coordinate. -/
theorem glue_update_of_not_mem (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) {i : Fin d}
    (hi : i ∉ J) (t : ℝ) :
    Function.update (glue J u w) i t = glue J u (Function.update w ⟨i, hi⟩ t) := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, glue_apply_of_not_mem J _ _ hi, Function.update_self]
  · rw [Function.update_of_ne hji]
    by_cases hj : j ∈ J
    · rw [glue_apply_of_mem J _ _ hj, glue_apply_of_mem J _ _ hj]
    · rw [glue_apply_of_not_mem J _ _ hj, glue_apply_of_not_mem J _ _ hj,
        Function.update_of_ne fun h => hji (congrArg Subtype.val h)]

theorem glue_update_subtype' (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ)
    (k : {i // ¬ inJ J i}) (t : ℝ) :
    Function.update (glue J u w) k t = glue J u (Function.update w k t) :=
  glue_update_of_not_mem J u w k.2 t

/-- The projection of `ℝ^d` onto the face coordinates. -/
def projK (v : Fin d → ℝ) : {i // ¬ inJ J i} → ℝ := fun k => v k

theorem projK_glue (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    projK J (glue J u w) = w := by
  funext k
  exact glue_apply_subtype' J u w k

theorem faceRes_comp_projK (G : ({i // ¬ inJ J i} → ℝ) → ℝ) : faceRes J (G ∘ projK J) = G := by
  funext w
  simp only [faceRes, Function.comp_apply, projK_glue]

theorem contDiff_comp_projK {G : ({i // ¬ inJ J i} → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (G ∘ projK J) :=
  hG.comp (contDiff_pi.2 fun k => contDiff_apply ℝ ℝ (k : Fin d))

/-- The face inclusion `w ↦ glue J 0 w` as a continuous linear map. -/
noncomputable def glueZeroCLM : ({i // ¬ inJ J i} → ℝ) →L[ℝ] (Fin d → ℝ) where
  toFun := fun w => glue J 0 w
  map_add' := fun w w' => by
    funext i
    by_cases hi : i ∈ J
    · simp only [glue_apply_of_mem J _ _ hi, Pi.add_apply, Pi.zero_apply, add_zero]
    · simp only [glue_apply_of_not_mem J _ _ hi, Pi.add_apply]
  map_smul' := fun c w => by
    funext i
    by_cases hi : i ∈ J
    · simp only [glue_apply_of_mem J _ _ hi, Pi.smul_apply, Pi.zero_apply, smul_zero]
    · simp only [glue_apply_of_not_mem J _ _ hi, Pi.smul_apply, RingHom.id_apply]
  cont := continuous_glue_zero J

theorem glueZeroCLM_apply (w : {i // ¬ inJ J i} → ℝ) : glueZeroCLM J w = glue J 0 w := rfl

theorem faceRes_eq_comp (F : (Fin d → ℝ) → ℝ) : faceRes J F = F ∘ glueZeroCLM J := rfl

theorem contDiff_faceRes {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (faceRes J F) := by
  rw [faceRes_eq_comp]
  exact hF.comp (glueZeroCLM J).contDiff

/-- The face inclusion has operator norm at most one for the sup norms. -/
theorem norm_glueZeroCLM_le : ‖glueZeroCLM J‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, glueZeroCLM_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi, Pi.zero_apply, norm_zero]
    exact norm_nonneg w
  · rw [glue_apply_of_not_mem J _ _ hi]
    exact norm_le_pi_norm w _

/-- The closed box `[0,b]^d` in face coordinates. -/
theorem glue_zero_mem_closedBox_iff {b : ℝ} (hb : 0 ≤ b) (w : {i // ¬ inJ J i} → ℝ) :
    glue J 0 w ∈ closedBox d b ↔ ∀ k, w k ∈ Icc 0 b := by
  simp only [closedBox, Set.mem_univ_pi]
  constructor
  · intro h k
    have := h k
    rwa [glue_apply_subtype'] at this
  · intro h i
    by_cases hi : i ∈ J
    · rw [glue_apply_of_mem J _ _ hi, Pi.zero_apply]
      exact ⟨le_rfl, hb⟩
    · rw [glue_apply_of_not_mem J _ _ hi]
      exact h _

/-! ### Restriction commutes with the tangential operators -/

theorem lineι_faceRes (F : (Fin d → ℝ) → ℝ) (k : {i // ¬ inJ J i}) (w : {i // ¬ inJ J i} → ℝ) :
    lineι (faceRes J F) k w = line F k (glue J 0 w) := by
  funext t
  simp only [lineι, line, faceRes, glue_update_subtype']

theorem faceRes_pd (F : (Fin d → ℝ) → ℝ) (k : {i // ¬ inJ J i}) :
    faceRes J (pd k F) = pdι k (faceRes J F) := by
  funext w
  change deriv (line F k (glue J 0 w)) (glue J 0 w k) = deriv (lineι (faceRes J F) k w) (w k)
  rw [lineι_faceRes, glue_apply_subtype']

theorem faceRes_pdPow (F : (Fin d → ℝ) → ℝ) (k : {i // ¬ inJ J i}) (m : ℕ) :
    faceRes J (pdPow k m F) = pdPowι k m (faceRes J F) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih => rw [pdPow_succ, pdPowι_succ, ih, faceRes_pd]

theorem faceRes_coordTaylor (F : (Fin d → ℝ) → ℝ) (k : {i // ¬ inJ J i}) (q : ℕ) :
    faceRes J (coordTaylor k q F) = coordTaylorι k q (faceRes J F) := by
  funext w
  change coordTaylor k q F (glue J 0 w) = _
  rw [coordTaylor_apply, coordTaylorι_apply, glue_apply_subtype']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [glue_update_subtype']
  exact congrArg _ (congrFun (faceRes_pdPow J F k m) _)

theorem faceRes_coordRem (F : (Fin d → ℝ) → ℝ) (k : {i // ¬ inJ J i}) (q : ℕ) :
    faceRes J (coordRem k q F) = coordRemι k q (faceRes J F) := by
  funext w
  change F (glue J 0 w) - coordTaylor k q F (glue J 0 w) =
    faceRes J F w - coordTaylorι k q (faceRes J F) w
  rw [← faceRes_coordTaylor]
  rfl

/-- ★★ Restriction to the face turns the iterated remainder over a list of face coordinates into
the iterated remainder of the restriction, in the face coordinates. -/
theorem faceRes_remList (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (l : List {i // ¬ inJ J i}) :
    faceRes J (remList p (l.map Subtype.val) F) =
      remListι (fun k : {i // ¬ inJ J i} => p k) l (faceRes J F) := by
  induction l generalizing F with
  | nil => rfl
  | cons k l ih => rw [List.map_cons, remList_cons, remListι_cons, faceRes_coordRem, ih]

theorem faceRes_pdMulti (m : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (l : List {i // ¬ inJ J i}) :
    faceRes J (pdMulti m (l.map Subtype.val) F) =
      pdMultiι (fun k : {i // ¬ inJ J i} => m k) l (faceRes J F) := by
  induction l generalizing F with
  | nil => rfl
  | cons k l ih => rw [List.map_cons, pdMulti_cons, pdMultiι_cons, faceRes_pdPow, ih]

/-! ### The face coordinate list and the face amplitude -/

/-- The face coordinates, in the order of the flat coordinate list `lK J`. -/
def lKface : List {i // ¬ inJ J i} := (lK J).attach.map fun x => ⟨x.1, (mem_lK J).1 x.2⟩

theorem lKface_map_val : (lKface J).map Subtype.val = lK J := by
  unfold lKface
  rw [List.map_map]
  exact List.attach_map_subtype_val (lK J)

theorem mem_lKface (k : {i // ¬ inJ J i}) : k ∈ lKface J :=
  List.mem_map.2 ⟨⟨k, (mem_lK J).2 k.2⟩, List.mem_attach _ _, rfl⟩

theorem nodup_lKface : (lKface J).Nodup :=
  (List.nodup_attach.2 (nodup_lK J)).map fun _ _ h => Subtype.ext (Subtype.mk.inj h)

theorem faceRes_remList_lK (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) :
    faceRes J (remList p (lK J) F) =
      remListι (fun k : {i // ¬ inJ J i} => p k) (lKface J) (faceRes J F) := by
  rw [← lKface_map_val, faceRes_remList]

/-- ★★★ **The face amplitude is a Taylor remainder on the face**: `faceAmp p J F m` is the
iterated remainder, in the face coordinates, of the restriction of the normal derivative
`∂^m_J F` to the face. -/
theorem faceAmp_eq (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (m : Fin d → ℕ)
    (w : {i // ¬ inJ J i} → ℝ) :
    faceAmp p J F m w =
      remListι (fun k : {i // ¬ inJ J i} => p k) (lKface J) (faceRes J (pdMulti m (lJ J) F)) w :=
  congrFun (faceRes_remList_lK J p (pdMulti m (lJ J) F)) w

/-! ### Order independence on the face -/

theorem remListι_perm_faceRes (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    {l l' : List {i // ¬ inJ J i}} (hl : l.Perm l') :
    remListι (fun k : {i // ¬ inJ J i} => p k) l (faceRes J F) =
      remListι (fun k : {i // ¬ inJ J i} => p k) l' (faceRes J F) := by
  rw [← faceRes_remList, ← faceRes_remList, remList_perm p hF (hl.map Subtype.val)]

/-- The extension of a face multi-index by zero on the Taylor coordinates. -/
def extIdx (q : {i // ¬ inJ J i} → ℕ) (i : Fin d) : ℕ :=
  if h : inJ J i then 0 else q ⟨i, h⟩

theorem extIdx_val (q : {i // ¬ inJ J i} → ℕ) (k : {i // ¬ inJ J i}) : extIdx J q k = q k :=
  dif_neg k.2

/-- The face remainder of a smooth function on the face space does not depend on the order of
the coordinate list. -/
theorem remListι_perm_face {G : ({i // ¬ inJ J i} → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : {i // ¬ inJ J i} → ℕ) {l l' : List {i // ¬ inJ J i}} (hl : l.Perm l') :
    remListι q l G = remListι q l' G := by
  have hq : q = fun k : {i // ¬ inJ J i} => extIdx J q k := funext fun k => (extIdx_val J q k).symm
  have h := remListι_perm_faceRes J (extIdx J q) (contDiff_comp_projK J hG) hl
  rw [faceRes_comp_projK, ← hq] at h
  exact h

/-- ★★★ The face amplitude is the face remainder of the restricted normal derivative over ANY
enumeration of the face coordinates. -/
theorem faceAmp_eq_remListι (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (m : Fin d → ℕ) {l : List {i // ¬ inJ J i}} (hl : l.Nodup) (hall : ∀ k, k ∈ l)
    (w : {i // ¬ inJ J i} → ℝ) :
    faceAmp p J F m w =
      remListι (fun k : {i // ¬ inJ J i} => p k) l (faceRes J (pdMulti m (lJ J) F)) w := by
  rw [faceAmp_eq, remListι_perm_faceRes J p (contDiff_pdMulti hF m _)
    ((List.perm_ext_iff_of_nodup (nodup_lKface J) hl).2 fun k =>
      ⟨fun _ => hall k, fun _ => mem_lKface J k⟩)]

/-! ### Restriction does not increase the Fréchet jets -/

/-- ★ `‖D^r (F ∘ glue J 0) w‖ ≤ ‖D^r F (glue J 0 w)‖`. -/
theorem norm_iteratedFDeriv_faceRes_le {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (r : ℕ)
    (w : {i // ¬ inJ J i} → ℝ) :
    ‖iteratedFDeriv ℝ r (faceRes J F) w‖ ≤ ‖iteratedFDeriv ℝ r F (glue J 0 w)‖ := by
  rw [faceRes_eq_comp, (glueZeroCLM J).iteratedFDeriv_comp_right hF w
    (by exact_mod_cast le_top : ((r : ℕ) : ℕ∞ω) ≤ ∞)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [glueZeroCLM_apply]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_glueZeroCLM_le J)

end SmoothEngine

end Grammar
