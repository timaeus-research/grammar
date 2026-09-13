# Consult #109 — the coordinate-free expansion plan: remaining gaps, ranked, with unit designs

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 661 modules, zero sorry/axiom, headline theorems axiom-clean). The user has
redirected the work: the companion note `averaging_dataset.tex` is OFF the table (its programme is closed and is
not to be extended), and the instruction is "continue finishing the coordinate-free expansion plan, there are
still gaps in this". The plan is `tide-log/plan_coordinate_free_expansion.md` (target statement §1: the all-order
expansion `∫_W φϕe^{−nK} = Σ_{α≤A,j} n^{−α}(log n)^j Σ_I ∫_{S_I} Σ'_r (1/r!)⟨D^r_⊥(φ∘π), B_{I,r,α,j}⟩ dν_I + o(n^{−A})`
on a resolved space with divisor strata, conormal splitting and tubular germs, with the leading corollary
`n^λ/(log n)^{m−1} ∫ → ∫ φ dμ_lead`). Please rank the gaps below for closing that plan against the PAPER's
claims (Gerraty–Murfet, §3 "expectations" / thm:expectation_expansion and its Lean mirror), and design the first
units.

## 1. What stands (all landed, axiom-clean; consults #92–#105)

* ★★★ `ResolvedCertificate.CoefficientCertificate.hasCoordFreeExpansion` (CCCIII/CCCIV): the target expansion,
  CONDITIONAL on a `ResolvedCertificate` (localisation datum on `U`, measure pushing to `φ dw`, analytic core
  decomposition on compact stratum pieces with frames `ℝ^{n+1} ≃ N_s`) and a `CoefficientCertificate`; normal
  series summed pointwise inside the stratum integral; scalar-coefficient canonicity across certificates (CCCVIII);
  leading term + bridge to the CCXC leading measure (CCCX); instances: 1D `∫_0^ρ P e^{−nx²}` with
  `Γ((m+1)/2)/2·f_m`, tied crossing `∫∫ P e^{−nx²y²}` with `√π/4·P(0)` at `n^{−1/2}log n`.
* Producers (no certificate hypotheses left): rectangular series box (CCCXVIII), water-filling collar for the
  positive coordinate box `[0,a]^d` with monomial phase `∏u_i^{2k_i}` (CCCXXIV/CCCXXV), from a holomorphic packet
  near the box (CCCXXXII, CCCXXXIV: hypotheses = packet, `0<d`, `0<a`, prior ≥ 0 on the box); signed box
  `[−a,a]^d` by reflection transport and RN-glued fields (CCCXLI); cube blow-up CHART MODEL (`π = id`, active set
  `A`, unit through inactive coordinates, Jacobian order `d−1`) assembled into the original cube integral
  `∫_{[−1,1]^d} F p e^{−n|x|²}` at all orders (CCCXLVII), coefficient fidelity: vanishing below `d/2`, leading
  `π^{d/2}F(0)p(0)` (`d≥2`), support `(d+ℓ)/2`, packet independence (CCCXLVIII–IX).
* J-min: observable-free kernel `MomentKernelData`, `withObs` producer identity, ★★★ `jetFunctional : obsSpace →ₗ ℝ`
  (analytic jet functional; finite-order/distribution target rejected, CCCL–CCCLIII).
* Leading-measure programme CCXC–CCXCVI (canonical finite measure on `W`, concentration on `{K=0}`, cube
  regression `π^{d/2}δ₀`, unconditional Θ-exponent `laplace_pair_eq_resolution_pair` over compact regions).
* Upstream `hironaka` exposes `PartialResolution`: compact chart domains with analytic maps into `W`, images
  covering a compact set a.e. with finite multiplicity, `IsMonomialChart` per chart; NO common resolved space,
  `π`, transition maps, global divisor components or strata.

## 2. The recorded gaps (plan §5 unit 9, §6, §5e–5h deferrals; mirror "not formalised" remarks; your #104/#105)

A. **Unit 9, projector blow-up model** `U = {(x,P) : P symmetric idempotent of trace 1, Px = x}` as a
   `ResolvedGeometry` with a certificate (your #93 estimate 6–12 modules). Phase E did the cube blow-up only as a
   chart model with `π = id`; there is NO global resolved geometry for any blow-up, hence no instance of the
   target theorem on a genuine `(U, π)` with `π ≠ id`.
B. **General resolved application / intrinsic gluing / SNC atlas** (plan §6; your #104 (iv)): a compatible
   monomial atlas (a.e.-disjoint or multiplicity-corrected change of variables, exact core transport, tail gap,
   unit handling) producing a `ResolvedCertificate` for a resolved geometry; making the certificate theorem apply
   to a genuine `π`.
C. **Unconditional theorem from hironaka** (your #92 §5): needs hironaka to expose `U`, proper analytic `π`, atlas
   with overlaps, labelled `E_i`, incidence — an upstream programme.
D. **Complexification from real analyticity** (#104 (v), research-sized): the packet API takes holomorphic
   extensions as hypotheses; the paper says "real analytic".
E. **Analytic tubular neighbourhood** (mirror rem:analytic_tubular): the paper needs a real-analytic `Φ`; in Lean
   the tubular germs are CHOSEN data in `ResolvedNormalData`, and the producers build them explicitly for
   coordinate strata only.
F. **E5** general partial-active water-filling collar (recovers G and E3).
G. **F2 parity cancellation** (odd total orders vanish on symmetric normal pieces; mirror rem:parity),
   **F3 Gamma coefficient formula**, the missing `d = 1` cube leading value.
H. **Leading-density relation** `M̃_γ(v,n) = c₀(v)M_γ(n) + subleading` (mirror line "this leading-density relation
   is not formalised") and the identification `∫_K q(v)·dv = ∫_{S_I} c₀|dv|` (charts, densities, partition of
   unity; mirror: "not formalised").
I. **The normalised expectation** `E_n[φ] = N_n[φ]/N_n[1]` (your #105 (c)(ii)): the paper's theorem is about
   expectations; Lean has the numerator expansion only (plus leading quotient limits `headline_phase_posterior`
   and the chart-assembly quotient). A quotient-expansion theorem (denominator = `N_n[1]`, positive leading
   coefficient, remainder control, division of power–log series) is not formalised.
J. **Box-only agreement theorem** (chosen extensions) and the **optimal spectral lattice** (plan §6, "not produced").
K. **I (curved sublevel sets)**: core + phase-gap certificate for curved sublevel sets (#94 candidate).
L. "Otherwise larger" leading exponent and the `λ+Q/2 = 1/2` number-operator case (Programme P/§4 remarks; not
   part of this plan unless you say so).

## 3. Questions

1. Which of A–L are genuine gaps OF THE COORDINATE-FREE EXPANSION PLAN (as opposed to research beyond the paper),
   and in what order should they be closed for the paper's §3 claims? Rank with one-line justifications.
2. For the top-ranked item(s), give a unit design in your usual form (structures, producer sequence, gates,
   stopping rule, 3–8 units), reusing the landed API (`ResolvedGeometry`, `ResolvedNormalData`,
   `ResolvedCertificate` with `cores : AnalyticCoreDecomposition`, `CoefficientCertificate`, the collar producers,
   `ChartModel.geometry`, `SingletonChartCertificate`, `BlowUpCube.cube_hasExpansion`, `MomentKernelData`).
   In particular, for A/B: how should a genuine `(U, π)` for the cube blow-up be presented so that the existing
   chart certificates transport to a `ResolvedCertificate` on `U` (what is `U` concretely — projector space,
   `Fin d → ℝ` with the blow-up coordinates, a subtype of `ℝ^d × ℝP^{d−1}`?), what replaces `π = id`, and which
   compatibility fields (`incident_eq`, labelled equations, tubular map from the total normal bundle) are needed?
3. For I (the normalised expectation): is a quotient-expansion theorem for power–log series with a positive
   leading denominator coefficient a bounded unit here (the numerator and denominator share the certificate), and
   what exactly should it state so that the mirror can put a dot on `E_n[φ]`?
4. Which of A–L should stay explicit NON-CLAIMS of the paper (reword rather than formalise), and the exact wording.
5. Anything in the plan that is stated but not yet true (a gap between the plan's §1 target statement and CCCIII),
   e.g. the adapted partition of unity `ρ_I`, `n`-independent `ν_I`, the leading corollary's `μ_lead` equality.

Answer in your usual structured form: Decision, ranked gap list, unit designs for the top items with gates,
non-claims, and a stopping rule for this phase.
