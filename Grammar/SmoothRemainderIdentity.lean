/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResonantSupport

/-!
# The Taylor remainder of a function flat along the coordinate hyperplanes

Consult #130, Unit E1a. The iterated coordinate Taylor remainder `remList p l G` (the engine's
face amplitude is such a remainder of a normal derivative) FIXES `G` at a point `v` whenever all
jets of `G` vanish on a set `S` closed under `v ↦ v[i := 0]` that contains every coordinate
truncation `v[i := 0]`, `i ∈ l` (★ `remList_eq_self_of_jetsZeroOn`): each coordinate Taylor
polynomial of `G` at `v` is a sum of `∂_i^m G (v[i := 0])`, which vanish, so each remainder
operator is the identity. In the graded stratum formula the face amplitude of a size-`c` face is
therefore the honest normal derivative `∂_J^α A` on the face, with no Taylor subtraction, as soon as
`A` vanishes near the faces of size `≥ c + 1`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

theorem coordTaylor_eq_zero_of_pdPow_eq_zero (i : Fin d) (p : ℕ) (G : (Fin d → ℝ) → ℝ)
    (v : Fin d → ℝ) (h : ∀ m, pdPow i m G (Function.update v i 0) = 0) :
    coordTaylor i p G v = 0 := by
  unfold coordTaylor
  exact Finset.sum_eq_zero fun m _ => by rw [h m, mul_zero]

/-- ★ **The remainder fixes a function flat along the coordinate hyperplanes**: on a set `S`
closed under coordinate truncation on which all jets of `G` vanish, `remList p l G v = G v` for
every `v` whose truncations `v[i := 0]`, `i ∈ l`, lie in `S`. -/
theorem remList_eq_self_of_jetsZeroOn (p : Fin d → ℕ) {S : Set (Fin d → ℝ)}
    (hS : ∀ v ∈ S, ∀ i, Function.update v i 0 ∈ S) :
    ∀ l : List (Fin d), l.Nodup → ∀ G : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G → JetsZeroOn G S →
      ∀ v : Fin d → ℝ, (∀ i ∈ l, Function.update v i 0 ∈ S) → remList p l G v = G v := by
  intro l
  induction l with
  | nil =>
    intro _ G _ _ v _
    rfl
  | cons i l ih =>
    intro hnd G hG hJ v hv
    have hnd' : l.Nodup := (List.nodup_cons.1 hnd).2
    have hil : i ∉ l := (List.nodup_cons.1 hnd).1
    have hv' : ∀ i' ∈ l, Function.update v i' 0 ∈ S := fun i' hi' =>
      hv i' (List.mem_cons_of_mem i hi')
    have hvi : Function.update v i 0 ∈ S := hv i (List.mem_cons_self ..)
    change coordRem i (p i) (remList p l G) v = G v
    unfold coordRem
    rw [ih hnd' G hG hJ v hv', coordTaylor_eq_zero_of_pdPow_eq_zero, sub_zero]
    intro m
    have hcomm := pdMulti_remList (p := p) hG (fun _ => m) (l := [i]) (l' := l)
      (fun j hj => by rw [List.mem_singleton] at hj; rw [hj]; exact hil)
    rw [pdMulti_cons, pdMulti_nil, pdMulti_cons, pdMulti_nil] at hcomm
    rw [hcomm]
    exact remList_eq_zero_of_jetsZeroOn p hS l hnd' (pdPow i m G) (contDiff_pdPow hG i m)
      (hJ.pdPow hG i m) _ hvi

end SmoothEngine

end Grammar
