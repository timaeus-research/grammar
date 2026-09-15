You are auditing a Lean 4 formalisation (Mathlib) of Section 4 of the paper "Expectations and the Exceptional Divisor" (Gerraty–Murfet), repo timaeus-research/grammar. Consults #133–#136 closed the residue programme (stratum measure ν^μ_c via Riesz, weighted residue measure ℛ^μ_c, chart-pushforward identity, positivity/finiteness, monomial regression). The user then asked: in the pairing C_{μ,c−1}(f) = ⟨Res^α_{S^μ_c}[(K∘π)^{−μ}μ_U], j^α_S(f∘π)⟩, is the transverse jet a coordinate-free object and is the pairing formalised? They want this description in the paper. A new unit (CDLXVII, module SmoothStratumJetDependence) has landed. Audit it.

Setting (already formalised): resolved data Ξ (Watanabe modification π: U → W, prior, smooth observable F : U → ℝ), resolved chart transport Y; intrinsic wall pairs `pairs P : Multiset (ℕ × ℕ)` of (k_j, h_j) through P; depth, resonanceCount (Resonates μ (k,h) ↔ ∃ m : ℕ, 2kμ = h + 1 + m); exact stratum S^μ_c = Z_0 ∩ {depth = c} ∩ {r_μ = c}; deep zero fibre D_{c+1}; coefficients Ξ.coeff Y μ q of the expansion of ∫ prior·F∘π⁻¹… in N^{−μ}(log N)^q, transport-independent; `coeff_eq_stratumSum` (Theorem E: for F vanishing near D_{c+1}, the (μ,c−1) coefficient is a finite sum over pieces and faces J with |J| = c of faceW · faceCoef · ∫_{face} ∂^{resOrder}_J amp · weight, where resOrder h k μ J j = if j ∈ J then ⌊2k_jμ⌋₊ − h_j − 1 else 0 and non-exactly-resonant faces contribute 0 (`faceCoef_top_eq_zero_of_not_exact`)); the piece amplitude amp s v = ρloc(Tm s v) · F(divPt s v) on the closed box, divPt = φ⁻¹ ∘ Tm (chart inverse of an affine chart map); `pdMulti_mul` Leibniz rule for iterated coordinate derivatives; zero-order condition ZeroOrder μ c := ∀ P ∈ S^μ_c, ∀ (k,h) ∈ pairs P, 2kμ = h+1; the previous values-only theorem `coeff_eq_of_eqOn_exactStratum` needed ZeroOrder.

New definitions and theorems (Lean, verbatim signatures):

```
def VanishesToOrderAt (n : ℕ) (H : Ξ.R.U → ℝ) (P : Ξ.R.U) : Prop :=
  ∃ N ∈ 𝓝 P, ∃ (m : ℕ) (g : Fin m → Fin n → Ξ.R.U → ℝ),
    (∀ i l, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (g i l)) ∧ (∀ i l, g i l P = 0) ∧
    ∀ Q ∈ N, H Q = ∑ i, ∏ l, g i l Q

def MemIdealPowNear (S : Set Ξ.R.U) (n : ℕ) (H : Ξ.R.U → ℝ) (P : Ξ.R.U) : Prop :=
  ∃ N ∈ 𝓝 P, ∃ (m : ℕ) (g : Fin m → Fin n → Ξ.R.U → ℝ),
    (∀ i l, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (g i l)) ∧ (∀ i l, ∀ Q ∈ S, g i l Q = 0) ∧
    ∀ Q ∈ N, H Q = ∑ i, ∏ l, g i l Q

theorem MemIdealPowNear.vanishesToOrderAt (h : Ξ.MemIdealPowNear S n H P) (hP : P ∈ S) : Ξ.VanishesToOrderAt n H P
theorem vanishesToOrderAt_one_of_eq_zero (hH : smooth H) (h0 : H P = 0) : Ξ.VanishesToOrderAt 1 H P

noncomputable def stratumJetOrder (μ : ℝ) (P : Ξ.R.U) : ℕ :=
  ((pairs Ξ.R Ξ.hK0 P).map fun q => ⌊2 * (q.1 : ℝ) * μ⌋₊ - q.2 - 1).sum

theorem stratumJetOrder_eq_zero_of_zeroOrder (hzero : Ξ.ZeroOrder μ c) (hP : P ∈ Ξ.exactStratum μ c) : Ξ.stratumJetOrder μ P = 0
theorem stratumJetOrder_divPt_eq (p) (s) {J : Finset (Fin da)} {w} (hw : w ∈ box (Y.T.a p.1)) (μ : ℝ) :
    Ξ.stratumJetOrder μ (Ξ.divPt Y p s (glue J 0 w)) = ∑ i, resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i

theorem pdMulti_prod_eq_zero_of_forall_eq_zero {n : ℕ} {G : Fin n → (Fin d → ℝ) → ℝ} (hG : ∀ l, ContDiff ℝ ∞ (G l)) {v₀}
    (h0 : ∀ l, G l v₀ = 0) {α : Fin d → ℕ} (hα : ∑ i, α i < n) : pdMulti α (List.finRange d) (fun v => ∏ l, G l v) v₀ = 0

theorem pdMulti_amp_eq_zero_of_vanishesToOrder (p) (s) {v₀} (hv : v₀ ∈ closedBox _ (Y.T.a p.1)) {α}
    (hF : Ξ.VanishesToOrderAt (∑ i, α i + 1) Ξ.F (Ξ.divPt Y p s v₀)) :
    pdMulti α (List.finRange _) ((Ξ.amp Y p).amp s) v₀ = 0

theorem coeff_eq_zero_of_vanishesToOrder (hc : 1 ≤ c) (hF0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0)
    (hF : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) Ξ.F P) : Ξ.coeff Y μ (c - 1) = 0

theorem coeff_eq_of_vanishesToOrder (hc : 1 ≤ c) {G G'} (hG hG' : smooth) (hG0 hG0' : vanish near deepZeroFibre c)
    (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.VanishesToOrderAt (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1)

theorem coeff_eq_of_memIdealPow … (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.MemIdealPowNear (Ξ.exactStratum μ c) (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) : same conclusion
theorem T_eq_of_memIdealPow (tests version)
theorem coeff_eq_of_eqOn_exactStratum' (hzero : ZeroOrder) … (heq : EqOn G G' (exactStratum μ c)) : same conclusion   -- recovered via order 0
```
All axiom-clean ([propext, Classical.choice, Quot.sound]). Proof: coeff_eq_stratumSum; non-exact faces vanish; at an exactly resonant face the face point is either in S^μ_c (then F is locally Σ_i ∏_l g_il with the g_il vanishing at the point; amp = ρloc(Tm)·F(divPt) on the box; extend g_il∘chartInv and ρloc smoothly from the closed box; derivatives of two smooth functions agreeing on O ∩ closedBox agree at points of O ∩ closedBox; Leibniz, and a derivative of total order < n of a product of n functions vanishing at the point vanishes) or off the prior support (all jets of amp vanish). Note only vanishing AT the point is used; the S-version is the ideal-theoretic packaging.

Mirror sentence added to the paper's Lean-annotated mirror (grammar_lean.tex), after the sentence on the order-zero positive stratum functional:

"Without the zero-order condition the functional depends on F ∈ 𝓘_{c+1} only through a finite transverse jet along S^μ_c, of intrinsic order n(P) = Σ_j (⌊2k_jμ⌋ − h_j − 1) summed over the walls through P (the total resonant Taylor order of the face formula): if F − F′ lies in 𝓘_{S^μ_c}^{n(P)+1} near every P ∈ S^μ_c, meaning that it is locally a finite sum of products of n(P)+1 smooth functions vanishing on S^μ_c, then 𝒯^U_{μ,c−1}[F] = 𝒯^U_{μ,c−1}[F′]. Both the ideal-power condition and the order n(P) are defined without coordinates, so C_{μ,c−1}(f) is a pairing between data determined by (K, π, μ, c) alone and the transverse n-jet of f∘π along S^μ_c; a presentation of this pairing as a sum of normal derivatives against densities exists in normal-crossings coordinates but is not canonical."

Questions:
(a) Signature audit: are the definitions the right chart-free notion (is "locally a finite sum of products of n smooth functions vanishing on S" the correct rendering of 𝓘_S^n for the closed submanifold-with-corners-like set S^μ_c? note S^μ_c is a locally closed smooth submanifold of U of codimension c, a union of open faces of the divisor; is the local finiteness (finite m) a restriction?). Is "n(P) = Σ(⌊2kμ⌋₊ − h − 1)" correctly the total order |α| (note ⌊·⌋₊ is the natural floor and at exact-stratum points all walls resonate so ⌊2kμ⌋₊ = h+1+α_j)? Is the statement "depends only on the transverse n-jet" justified by coeff_eq_of_memIdealPow, given that 𝓘_S^{n+1}-equivalence is exactly equality of n-jets along S for smooth functions (Hadamard / Whitney; is that true for a closed submanifold S — yes for 𝓘_S^{n+1} = functions vanishing to order n+1 along S, by Taylor expansion in normal coordinates; but does the Lean hypothesis, being the a-priori STRONGER "finite sum of products" condition, cover all functions with vanishing n-jet along S? Is the asymmetry a concern for the paper sentence "depends only on the jet"?). Should the mirror say "n-jet" or "(n)-jet along S transverse", and is "transverse jet" standard here (the tangential derivatives don't matter because they are absorbed in the density integration — the jet along S of order n modulo 𝓘_S^{n+1} is the normal n-jet)?
(b) Is the mirror sentence correct and precise as paper text? Give a replacement wording if not. Flag any overclaim (e.g. "pairing between data determined by (K,π,μ,c) alone" — the left factor is the functional on 𝓘_{c+1}/𝓘_S^{n+1}; is it right to say it depends on (K,π,μ,c) only? It also depends on the prior φ — we said "twisted prior density"; the mirror sentence says "data determined by (K, π, μ, c) alone" — this omits φ. Please fix.)
(c) Direction: is the finer per-wall version (F − F′ ∈ Σ_j 𝓘_{E_j}^{α_j+1}, orders α_j per wall) worth formalising, or is the total-order statement the right paper-level statement? Anything else this unit should assert for the paper (e.g. that the pairing descends to 𝓘_{c+1}/(𝓘_c + 𝓘_S^{n+1}), or that the map F ↦ 𝒯[F] is a "conormal distribution of order n" in a precise sense)? Keep to a verdict, corrections, and a ranked short list.
