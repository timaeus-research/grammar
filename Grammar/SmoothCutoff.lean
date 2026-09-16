/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Smooth cutoffs and globalisation of locally smooth fields

For a compact `K` inside an open `U ⊆ ℝ^d` there is a smooth `χ` equal to `1` on a neighbourhood of
`K` with `tsupport χ ⊆ U`. Multiplying a field that is smooth only on `U` by `χ` gives a globally
smooth field with the same jets on `K` (consult #151, M2).
-/

open Set Filter Topology
open scoped ContDiff Manifold

namespace Grammar

variable {d : ℕ}

/-- **A smooth cutoff**: `χ ≡ 1` on an open neighbourhood of the compact `K`, `tsupport χ ⊆ U`. -/
theorem exists_smooth_cutoff {K U : Set (Fin d → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ (∃ V, IsOpen V ∧ K ⊆ V ∧ EqOn χ 1 V) ∧
      tsupport χ ⊆ U := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L', hL'c, hLL', hL'U⟩ := exists_compact_between hLc hU hLU
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, Fin d → ℝ)
    (n := ⊤) isOpen_interior.isClosed_compl hLc.isClosed
    (disjoint_compl_left_iff_subset.2 hLL')
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, ⟨interior L, isOpen_interior, hKL,
    fun u hu => hf1 (interior_subset hu)⟩, ?_⟩
  have hsupp : Function.support f ⊆ interior L' :=
    Function.support_subset_iff'.2 fun u hu => hf0 hu
  exact (closure_mono hsupp).trans ((closure_mono interior_subset).trans
    (hL'c.isClosed.closure_eq.le.trans hL'U))

/-- A field smooth on the open set `U`, multiplied by a smooth cutoff supported in `U`, is
globally smooth. -/
theorem contDiff_cutoff_mul {χ ζ : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ U) (hζ : ContDiffOn ℝ ∞ ζ U) :
    ContDiff ℝ ∞ fun u => χ u * ζ u := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ U
  · exact hχ.contDiffAt.mul (hζ.contDiffAt (hU.mem_nhds hu))
  · have h0 : (fun u => χ u * ζ u) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      have hmem : (tsupport χ)ᶜ ∈ 𝓝 u :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds fun h => hu (hsupp h)
      filter_upwards [hmem] with v hv
      rw [image_eq_zero_of_notMem_tsupport hv, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- On the open set where the cutoff is `1`, the cutoff field has the jets of the field. -/
theorem iteratedFDeriv_cutoff_mul {χ ζ : (Fin d → ℝ) → ℝ} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
    (hχ1 : EqOn χ 1 V) {u : Fin d → ℝ} (hu : u ∈ V) (r : ℕ) :
    iteratedFDeriv ℝ r (fun u => χ u * ζ u) u = iteratedFDeriv ℝ r ζ u := by
  have h : (fun u => χ u * ζ u) =ᶠ[𝓝 u] ζ := by
    filter_upwards [hV.mem_nhds hu] with v hv
    rw [hχ1 hv, Pi.one_apply, one_mul]
  exact (h.iteratedFDeriv ℝ r).eq_of_nhds

end Grammar
