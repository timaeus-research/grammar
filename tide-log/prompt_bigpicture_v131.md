# Consult #131 — AUDIT of Theorem E as landed (graded stratum formulas, Units E0–E4 of your #130 design) and CLOSURE

All eight units of your #130 plan LANDED in grammar (main `b370f6d`, 765 modules, axiom-clean). Please (A) audit the statements below against the #130 design for over-claims, (B) give the paper paragraph for Theorem E as landed (we adopted your #130 §10 draft; correct it against what is actually proved), and (C) CLOSE Theorem E or name the one unit you would still do. Be direct.

## 1. Verbatim signatures (namespace `Grammar.SmoothEngine`; engine level first, then `…ResolvedData` with `Ξ : ResolvedData d`, `Y : ResolvedCoreTransport …`, `Ξ.coeff Y μ q = 𝒯^U_{μ,q}[F]`)
```
-- SmoothExactResonance (E0, CDXLIV)
noncomputable def exactCount (k e : ι → ℕ) (μ : ℝ) : ℕ := #{i | 2 * k i * μ = e i + 1}
theorem faceMonoCoeff_eq_zero_of_exactCount_le [Nonempty ι] (k e) (hk : ∀ i, 0 < k i) (hβ hb) (hj : exactCount k e μ ≤ j) : faceMonoCoeff k e β b μ j = 0
   -- exact-support rerun of the chain coeffTerm → spectralCoeff → familySpectralCoeff → boxCoeff (support of monoFam e is exactly {e}; the fluctuation family is 0)
theorem faceMonoCoeff_top_eq_zero_of_not_exact (hi : 2 * k i * μ ≠ e i + 1) : faceMonoCoeff k e β b μ (card ι − 1) = 0
theorem faceCoef_top_eq_zero_of_not_exact (k) (hk) (hβ hb) (J) (e) (hj : j ∈ J) (hne : 2 * k j * μ ≠ e j + 1) : faceCoef k β b J e μ (DJ J) = 0     -- DJ J = |J| − 1
theorem taylorOrder_unique (h1 : 2kμ = m + h + 1) (h2 : 2kμ = m' + h + 1) : m = m'
-- SmoothRemainderIdentity (E1a, CDXLV)
theorem remList_eq_self_of_jetsZeroOn (p) {S} (hS : ∀ v ∈ S, ∀ i, update v i 0 ∈ S) : ∀ l, l.Nodup → ∀ G, ContDiff ℝ ∞ G → JetsZeroOn G S → ∀ v, (∀ i ∈ l, update v i 0 ∈ S) → remList p l G v = G v
-- SmoothFaceSumCollapse (E1d, CDXLVI)
def deepSet (d) (b) (c) : Set (Fin d → ℝ) := {v ∈ closedBox d b | c + 1 ≤ #{i | v i = 0}}
noncomputable def resOrder (h k) (μ) (J) : Fin d → ℕ := fun j => if j ∈ J then ⌊2 * k j * μ⌋₊ − h j − 1 else 0
theorem smoothCoeff_eq_faceSum_top (hA : ContDiff ℝ ∞ A) (h k) (hk : ∀ i, 0 < k i) (hβ hb) (μ) (hc : 1 ≤ c) (hdeep : JetsZeroOn A (deepSet d b c)) :
  smoothCoeff A h k β b μ (c − 1) = ∑ J ∈ univ.filter (#J = c), faceW J (resOrder h k μ J) * (faceCoef k β b J (fun i => resOrder h k μ J i + h i) μ (c − 1) *
     faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w)) (h|Jᶜ) (2k|Jᶜ) b μ 0)
   -- faceCoeffInt G h a b μ 0 = ∫_{(0,b]^{Jᶜ}} G w · ∏ w^h · (∏ w^{2k})^{−μ} dw ; faceW J m = ∏_{j∈J} 1/m_j! ; the engine's smoothCoeff (all coordinates active)
-- SmoothFaceMonoTop (E1b, CDXLVII)
theorem faceMonoCoeff_top [Nonempty ι] (k e) (hk) (hβ hb) (hμ : ∀ i, 2 * k i * μ = e i + 1) : faceMonoCoeff k e β b μ (card ι − 1) = Γ(μ) * β^(−μ) / ((card ι − 1)! * ∏ i, 2 * k i)
theorem faceCoef_top_eq (k) (hk) (hβ hb) (J) (hJ : J.Nonempty) (e) (hres : ∀ j ∈ J, 2 * k j * μ = e j + 1) : faceCoef k β b J e μ (DJ J) = Γ(μ) β^(−μ) / ((DJ J)! * ∏_{i ∈ J} 2 k i) ; faceCoef_top_pos
-- SmoothResolvedStratumFormula (E2, CDXLVIII; ResolvedData)
def deepZeroFibre (c) : Set Ξ.R.U := Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (c + 1)          -- compact
theorem coeff_eq_zero_of_deep (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (hq : c ≤ q) (μ) : Ξ.coeff Y μ q = 0
theorem jetsZeroOn_amp_deep (hF) (p s) : JetsZeroOn ((Ξ.amp Y p).amp s) (deepSet (da p) (a p.1) c)   -- via card_le_depth_divPt, Gloc_eventually_zero_deep (F = 0 near the divisor point, or it is off supp prior)
noncomputable def pieceStratumSum (I s μ c) : ℝ := ∑ J ∈ univ.filter (#J = c), faceW J α_J * (faceCoef (chart I).k (βf s) (b) J (α_J + h) μ (c−1) * faceCoeffInt (fun w => pdMulti α_J (lJ J) ((chart I).amp.amp s) (glue J 0 w)) … μ 0)
noncomputable def stratumSum (μ c) : ℝ := ∑ I, ∫ s, Ξ.pieceStratumSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν
theorem coeff_eq_stratumSum (hc : 1 ≤ c) (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (μ) : Ξ.coeff Y μ (c − 1) = Ξ.stratumSum Y μ c
theorem wallsAt_facePt_eq (p s) (hJ : ∀ i, v i = 0 ↔ i ∈ J) : wallsAt (Y.evenChartBox p.1) (Ξ.facePt Y p s v) = J.map e   -- e : face coordinates ↪ chart coordinates
theorem depth_divPt_eq (hv : v ∈ closedBox) (hJ) : depth Ξ.R Ξ.hK0 (Ξ.divPt Y p s v) = #J
theorem resonanceCount_divPt_eq (hv) (hJ) (hres : ∀ i ∈ J, Resonates μ (kA p i, hA p i)) : resonanceCount Ξ.R Ξ.hK0 μ (Ξ.divPt Y p s v) = #J
-- SmoothResolvedStratumPositive (E3, CDXLIX)
def exactStratum (μ c) : Set Ξ.R.U := {P | P ∈ Ξ.zeroFibre ∧ depth P = c ∧ resonanceCount μ P = c}
def ZeroOrder (μ c) : Prop := ∀ P ∈ Ξ.exactStratum μ c, ∀ q ∈ pairs Ξ.R Ξ.hK0 P, 2 * q.1 * μ = q.2 + 1
theorem stratum_or_jets_zero (hc) (hzero : ZeroOrder μ c) (p s) (hJc : #J = c) (hex : ∀ i ∈ J, 2 kA_i μ = α_J i + hA_i + 1) (hw : w ∈ box) :
  (Ξ.divPt Y p s (glue J 0 w) ∈ Ξ.exactStratum μ c ∧ α_J = 0) ∨ ∀ α, pdMulti α (finRange) ((Ξ.amp Y p).amp s) (glue J 0 w) = 0
theorem coeff_nonneg_of_deep (hc) (hzero) (hF : F = 0 near deepZeroFibre c) (hF0 : ∀ P, 0 ≤ Ξ.F P) : 0 ≤ Ξ.coeff Y μ (c − 1)
theorem coeff_eq_of_eqOn_exactStratum (hc) (hzero) (hG hG') (hG0 : G = 0 near deepZeroFibre c) (hG0') (heq : EqOn G G' (Ξ.exactStratum μ c)) : (Ξ.withF G).coeff Y μ (c−1) = (Ξ.withF G').coeff Y μ (c−1)
-- SmoothResolvedStratumEuclidean (E4, CDL)
theorem observableCoeff_eq_zero_of_eventually_zero_image (hf) (h0 : ∀ᶠ y in 𝓝ˢ (Ξ.R.gv '' Ξ.resonantZeroFibre μ q), f y = 0) : (Ξ.X Y).observableCoeff μ q f hf = 0
theorem observableCoeff_eq_stratumSum (hf) (hc) (h0 : ∀ᶠ P in 𝓝ˢ (deepZeroFibre c), f (gv P) = 0) (μ) : observableCoeff μ (c−1) f hf = (Ξ.withF (f ∘ gv)).stratumSum Y μ c ; observableCoeff_nonneg_of_deep ; observableCoeff_eq_of_eqOn_image (heq : EqOn f g (gv '' exactStratum μ c))
-- SmoothStratumIntegrable (E1c, CDLI)
theorem integrableOn_stratum_integrand (hA) (h k) (hb) {O} (hO : IsOpen O) (hAO : ∀ v ∈ O ∩ closedBox d b, A v = 0) (hdeep : deepSet d b c ⊆ O) (J) (hJc : #J = c) (α) (hα : ∀ i ∉ J, α i = 0) (μ) : IntegrableOn (fun w => pdMulti α (lJ J) A (glue J 0 w) * mono h w * mono (2k) w ^ (−μ) * logSum (2k) w ^ 0) (box Jᶜ b)
theorem exists_open_amp_zero (hF) (p s) : ∃ O, IsOpen O ∧ deepSet … c ⊆ O ∧ ∀ v ∈ O ∩ closedBox, (Ξ.amp Y p).amp s v = 0
theorem integrableOn_pieceStratum_integrand (hF) (p s J) (hJc : #J = c) (μ) : IntegrableOn (face integrand of pieceStratumSum) (box Jᶜ (a p.1))
```
Notes. (i) The engine collapse takes `JetsZeroOn A (deepSet)` (jets vanish on the closed deep set); the resolved application supplies it from neighbourhood vanishing of `F`. Integrability (E1c) takes the relatively open vanishing set, also supplied on `U`. (ii) `α_J = resOrder` uses `⌊2k_jμ⌋₊ − h_j − 1`; on an exactly resonant coordinate this is the `m` with `2k_jμ = m + h_j + 1`; on other coordinates the face coefficient vanishes anyway. (iii) In `pieceStratumSum` the derivative acts on the WHOLE amplitude `ω|b|·prior∘π·F∘φ⁻¹` (Leibniz not expanded), as you specified. (iv) The interpretation lemmas identify the face points `glue J 0 w` (w in the open face box) with divisor points of depth exactly `|J|`; membership in `Z₀` needs `π(divPt) ∈ supp prior`, which is exactly the case where the amplitude does not vanish identically nearby (the dichotomy in `stratum_or_jets_zero`). (v) E3 needs `ZeroOrder` on the whole exact stratum `S^μ_c`; it does not assume `μ` is the global minimum ratio.

## 2. Questions
(A) Audit: any over-claim in the HEADLINES-style summary "for observables vanishing near the deep zero fibre, the (μ, c−1) coefficient is a finite sum of absolutely convergent integrals over the exact stratum S^μ_c of the α-normal derivatives of the localised amplitude against the local top Mellin-residue weight, with the explicit constants Γ(μ)β^{−μ}/((c−1)!∏2k_j α_j!)"? Note faceW J α = ∏ 1/α_j! and faceCoef top = Γ(μ)β^{−μ}/((c−1)!∏_{j∈J}2k_j) — is the product of the two the constant you intended? (β here is the piece's normalised phase unit, = 1 for the resolved transport's charts.)
(B) The zero-order condition `ZeroOrder μ c` (every wall through S^μ_c has ratio exactly μ) — is this the right hypothesis for the paper's positivity/measure statement, and is the reading "each stratum whose incident wall ratios coincide carries its own positive density on 𝓘_{c+1}" now fully justified? Is there a simpler sufficient condition worth recording (e.g. μ = λ* forces ZeroOrder λ* c for every c by extremality)?
(C) Paper paragraph for Theorem E as landed (one paragraph), and the non-claims list.
(D) CLOSE Theorem E? Or one more unit: candidates — (1) `ZeroOrder λ* c` from extremality (S, cheap corollary linking E3 to Theorem D's leading functional: at μ = λ*, c = m*, 𝓘_{m*+1} is everything near… actually depth ≥ m*+1 points may exist; the leading functional restricted to observables vanishing near them is the stratum measure); (2) the x²y² regression through the graded formula (S–M, needs an identity modification constructor); (3) flatness instead of neighbourhood vanishing (M); (4) lower log powers as Taylor-subtracted chart-face formulas stated explicitly (S, restatement of smoothCoeffAtDepth). Rank.
