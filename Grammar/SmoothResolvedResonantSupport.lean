/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedResonant
import Grammar.SmoothResonantSupport

/-!
# The resonant support of the resolved coefficient functionals

Consult #127, Unit D6 (assembly). The resolved coefficient functional `𝒯^U_{μ,q}` vanishes on
every smooth observable that vanishes on a neighbourhood of the **resonant zero fibre**
`Z₀ ∩ {r_μ ≥ q + 1}` — the divisor points over the prior support at which at least `q + 1` of
the walls resonate with the exponent `μ` (`coeff_eq_zero_of_eventually_zero_resonant`). Hence
`𝒯^U_{μ,q}` depends only on the germ of the observable along `Z₀ ∩ {r_μ ≥ q+1}`
(`coeff_congr_of_eventuallyEq_resonant`), a fortiori along `Z₀ ∩ D_{≥ q+1}`
(`coeff_eq_zero_of_eventually_zero_depth`), and an observable supported in the shallow locus
`U_c = U ∖ D_{≥ c+1}` has vanishing coefficients at all logarithmic powers `q ≥ c`
(`coeff_eq_zero_of_tsupport_subset_shallowOpen`): the logarithmic power `q` requires `q + 1`
resonant walls through a point of the support.

Proof: the coefficient is the sum over the pieces of the integrated engine coefficients
`∫ smoothCoeff (amp s) … dν`; the engine's resonant-support lemma
(`smoothCoeff_eq_zero_of_resonant`, CDXXXIII) kills each of them once the amplitude jets vanish on
every face of the active box with at least `q + 1` resonant coordinates, which is the geometric
statement of
`SmoothResolvedResonant` (`pdMulti_amp_eq_zero_on_face`); the engine's resonant count of a face is
the piece's face resonance count (`resonantCount_eq_faceResonant`).

Non-claims: no sharp support equality (the resonance count is an upper bound on the logarithmic
multiplicity), no stratum-kernel presentation, no Riesz representation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The engine's resonant count of a face of the active box is the face resonance count of the
piece. -/
theorem resonantCount_eq_faceResonant (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))
    (μ : ℝ) :
    resonantCount (fun i : {i // inJ J i} => (Ξ.X Y).kA p i) (fun i => (Ξ.X Y).hA p i) μ =
      Ξ.faceResonant Y p J μ := by
  classical
  unfold resonantCount faceResonant
  rw [Multiset.filter_map, Multiset.card_map]
  change _ = (Multiset.filter (fun i => Resonates μ ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i)) J.val).card
  rw [← Finset.filter_val, ← Finset.card_def]
  refine Finset.card_bij (fun i _ => i.1) (fun i hi => ?_) (fun i _ j _ h => Subtype.ext h)
    (fun j hj => ?_)
  · rw [Finset.mem_filter] at hi ⊢
    exact ⟨inJ_iff.1 i.2, hi.2⟩
  · rw [Finset.mem_filter] at hj
    exact ⟨⟨j, inJ_iff.2 hj.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.2⟩, rfl⟩

/-- ★★★ **Resonant support of the resolved coefficient functional**: an observable vanishing on a
neighbourhood of the resonant zero fibre `Z₀ ∩ {r_μ ≥ q + 1}` has vanishing `(μ, q)` coefficient. -/
theorem coeff_eq_zero_of_eventually_zero_resonant {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) : Ξ.coeff Y μ q = 0 := by
  unfold coeff SmoothCoreDecomposition.coeff
  refine Finset.sum_eq_zero fun I _ => ?_
  unfold familyCoeff
  refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
  refine smoothCoeff_eq_zero_of_resonant (((Ξ.decomp Y).chart I).amp.smooth s) _ _
    ((Ξ.decomp Y).chart I).k_pos (((Ξ.decomp Y).chart I).β_pos s) ((Ξ.decomp Y).chart I).b_pos μ q
    fun J hJ v hv hvJ α => ?_
  have hJ' : q + 1 ≤ Ξ.faceResonant Y ((Ξ.X Y).en I) J μ := by
    rw [← Ξ.resonantCount_eq_faceResonant Y]
    exact hJ
  exact Ξ.pdMulti_amp_eq_zero_on_face Y hF ((Ξ.X Y).en I) s J hJ' hv hvJ α

theorem withF_resonantZeroFibre (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (μ : ℝ) (q : ℕ) : (Ξ.withF G hG).resonantZeroFibre μ q = Ξ.resonantZeroFibre μ q := rfl

/-- ★★★ **Germ locality along the resonant zero fibre**: two smooth observables agreeing on a
neighbourhood of `Z₀ ∩ {r_μ ≥ q + 1}` have the same `(μ, q)` coefficient. -/
theorem coeff_congr_of_eventuallyEq_resonant {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    {μ : ℝ} {q : ℕ} (h : G =ᶠ[𝓝ˢ (Ξ.resonantZeroFibre μ q)] G') :
    (Ξ.withF G hG).coeff Y μ q = (Ξ.withF G' hG').coeff Y μ q := by
  have hG'' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G' P) :=
    contMDiff_const.mul hG'
  have hsum : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => G P + (-1 : ℝ) * G' P) :=
    hG.add hG''
  have hev : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), G P + (-1 : ℝ) * G' P = 0 := by
    filter_upwards [h] with P hP
    rw [hP]; ring
  have hdiff :=
    (Ξ.withF (fun P => G P + (-1 : ℝ) * G' P) hsum).coeff_eq_zero_of_eventually_zero_resonant Y hev
  have h1 := Ξ.coeff_add Y hG hG'' μ q
  have h2 := Ξ.coeff_smul Y hG' (-1) μ q
  linarith

/-- The resonant zero fibre lies in the depth filtration. -/
theorem resonantZeroFibre_subset (μ : ℝ) (q : ℕ) :
    Ξ.resonantZeroFibre μ q ⊆ Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (q + 1) :=
  inter_subset_inter_right _ (resonanceGE_subset_depthGE Ξ.R Ξ.hK0 μ (q + 1))

/-- ★★ **Support in the depth filtration**: an observable vanishing near `Z₀ ∩ D_{≥ q+1}` has
vanishing `(μ, q)` coefficients for every exponent `μ`. -/
theorem coeff_eq_zero_of_eventually_zero_depth {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (q + 1)), Ξ.F P = 0) :
    Ξ.coeff Y μ q = 0 :=
  Ξ.coeff_eq_zero_of_eventually_zero_resonant Y
    (hF.filter_mono (nhdsSet_mono (Ξ.resonantZeroFibre_subset μ q)))

/-- ★★ **Restriction to the shallow locus**: an observable supported in `U_c = U ∖ D_{≥ c+1}` has
vanishing coefficients at every logarithmic power `q ≥ c` and every exponent. -/
theorem coeff_eq_zero_of_tsupport_subset_shallowOpen {c : ℕ}
    (hsupp : tsupport Ξ.F ⊆ shallowOpen Ξ.R Ξ.hK0 c) {μ : ℝ} {q : ℕ} (hq : c ≤ q) :
    Ξ.coeff Y μ q = 0 := by
  refine Ξ.coeff_eq_zero_of_eventually_zero_depth Y (eventually_nhdsSet_iff_exists.2
    ⟨(tsupport Ξ.F)ᶜ, (isClosed_tsupport _).isOpen_compl, fun P hP hsP => ?_,
      fun P hP => image_eq_zero_of_notMem_tsupport hP⟩)
  have h1 : P ∈ depthGE Ξ.R Ξ.hK0 (c + 1) := depthGE_antitone Ξ.R Ξ.hK0 (by omega) hP.2
  exact (hsupp hsP) h1

end ResolvedData

end SmoothEngine

end Grammar
