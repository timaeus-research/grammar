## Recommendation

The most valuable missing author-facing theorem is now a **joint random next-log theorem for posterior observables**, led by the posterior Laplace transform:
\[
\left(X_j,\,
\left[\log N_j\left(
\mathbb E_{Q_{N_j}(X_j)}e^{-s_\ell N_jK}
-\frac{A_{s_\ell}(X_j)}{F(X_j)}
\right)\right]_{\ell<r}
\right)
\Rightarrow
\left(X,\,[C_{s_\ell}(X)]_{\ell<r}\right).
\]

It should allow energy mean and free energy as additional coordinates. This turns the present coefficient machinery into a theorem about **joint random posterior observables**, rather than another isolated asymptotic expansion.

I recommend **six bounded theorem units**, followed by a theorem-map consolidation as the block’s closing editorial task. No new geometric work, no all-orders division, and no function-space-valued Laplace-transform theorem in this block.

---

## 1. Data tilt and physical admissibility

**Priority:** essential infrastructure for the highest-value missing theorem.

For fixed \(\beta>0\) and \(s\ge0\), construct the bounded linear map
```lean
dataTilt (β s : ℝ) : DataSpace d →L[ℝ] DataSpace d
```
with the intended coordinate action
```lean
xiCoord (dataTilt β s x) = (β / (β + s)) • xiCoord x
etaCoord (dataTilt β s x) = etaCoord x
```
under the appropriate parameter hypotheses.

Prove:

1. The represented phase/amplitude identities.
2. The exact tilted-integral identity:
   \[
   Z^{\beta+s}_N(\operatorname{tilt}_{\beta,s}x)
   =
   \text{the numerator integral for }
   \mathbb E_{Q_N(x)}e^{-sNK}.
   \]
3. Compact images under the tilt, giving the immediate route into XCV at temperature \(\beta+s\).
4. A physical admissibility criterion:
   ```lean
   dataLead_pos_of_nonneg_of_faceWeight_pos
   ```
   whose hypotheses are precisely those required by `spatialFace_pos_of_faceWeight`, transported through `dataBoxCoeff_spatialFace`.

**Inputs:** XCV, coordinate evaluation lemmas, `spatialFace_pos_of_faceWeight`.

**Trap:** prove the exact integral identity before naming the numerator coefficient. Do not insert a guessed temperature prefactor: any \(\beta\)-dependence belongs in the coefficients supplied by the theorem at temperature \(\beta+s\).

**Non-claim:** membership in `AdmissibleData` is not a characterization of physical nonnegative data. It only records positivity of the leading coefficient.

---

## 2. Uniform and random next-log posterior Laplace transforms

**Priority:** highest-value new observable.

For fixed \(s\ge0\), define
\[
A_s(x):=F_{\beta+s}(\operatorname{tilt}_{\beta,s}x),
\qquad
B_s(x):=B_{\beta+s}(\operatorname{tilt}_{\beta,s}x),
\]
and
\[
P_s(x)=\frac{A_s(x)}{F_\beta(x)},\qquad
C_s(x)=\frac{B_s(x)F_\beta(x)-A_s(x)B_\beta(x)}
                 {F_\beta(x)^2}.
\]

Here and below, use an explicit **zero second-coefficient convention when the multiplicity is one**.

Targets:
```lean
tendstoUniformlyOn_laplaceNextLog
    (s_nonneg : 0 ≤ s)
    (hK : IsCompact K) :
  TendstoUniformlyOn
    (fun N x =>
      Real.log N * (laplaceStat β s N x - laplaceLead β s x))
    (laplaceCorrection β s) atTop K
```
where `K` is a compact subset of `AdmissibleData`.

Then:
```lean
continuouslyConverges_laplaceNextLog
randomLaplaceNextLog_graphLaw_tendsto
```
giving, without an explicit tightness hypothesis,
\[
(X_j,L_j(\mathrm{Lap}_{N_j,s}(X_j)-P_s(X_j)))
\Rightarrow (X,C_s(X)).
\]

Include the exact physical identification of `laplaceStat` with the posterior expectation under the hypotheses needed to define that posterior.

**Inputs:** Unit 1, XCV, `tendstoUniformlyOn_nextLog_div`, XCVIII.

**Useful theorem checks:** at \(s=0\), the leading ratio is \(1\) and the correction is \(0\). Exact finite-\(N\) equality to \(1\) requires a nonzero denominator; otherwise state it eventually on compacts.

**Non-claims:** fixed \(s\), and subsequently finitely many fixed \(s\)’s. Do not claim locally uniform convergence in \(s\): that needs temperature-uniform input not supplied merely by compactness of the data tilt.

---

## 3. Uniform logarithmic delta theorem and random next-log free energy

**Priority:** the cleanest author-facing complement to the Laplace theorem.

First prove a reusable compact/uniform logarithmic lemma. Its schematic shape is:
```lean
tendstoUniformlyOn_nextLog_log
    (hL : Tendsto L atTop atTop)
    (hnext :
      TendstoUniformlyOn
        (fun n x => L n * (g n x - F x)) B atTop K)
    (hfloor : ∀ x ∈ K, δ ≤ F x)
    (hδ : 0 < δ)
    (hB : ∀ x ∈ K, |B x| ≤ MB) :
  TendstoUniformlyOn
    (fun n x => L n * (Real.log (g n x) - Real.log (F x)))
    (fun x => B x / F x) atTop K
```
Include the eventual uniform positivity conclusion for `g`.

Apply it to normalized evidence. With \(L=\log N\) and
\(\mathcal F_N(x)=-\log Z_N(x)\), prove
\[
L\left[
\mathcal F_N(x)-\lambda L+(m-1)\log L+\log F(x)
\right]
\longrightarrow -\frac{B(x)}{F(x)}
\]
uniformly on admissible compacts, then continuously, then in the random graph law.

Suggested endpoints:
```lean
tendstoUniformlyOn_freeEnergyNextLog
continuouslyConverges_freeEnergyNextLog
randomFreeEnergyNextLog_graphLaw_tendsto
```

**Inputs:** XCV, the uniform floor machinery, XCVIII, and the deterministic logarithmic expansion where reusable.

**Trap:** Lean’s total `Real.log` does not certify physical positivity. Prove eventual positivity on compacts and use it in the algebra identifying the normalized logarithm with free energy.

**Non-claim:** admissibility alone need not imply positivity for every finite \(N\). The asymptotic theorem only needs eventual positivity along convergent data sequences.

---

## 4. Evidence ratios under a joint random data law

**Priority:** closes the remaining quotient-statistic gap.

Use the domain
\[
D\times D_+,
\]
with numerator datum first and admissible denominator second. This is slightly stronger than requiring both data to be admissible.

For \(y=(x',x)\), define
\[
R_N(y)=\frac{Z_N(x')}{Z_N(x)},\quad
R_0(y)=\frac{F(x')}{F(x)},\quad
R_1(y)=\frac{B(x')F(x)-F(x')B(x)}{F(x)^2}.
\]

Prove:
```lean
tendstoUniformlyOn_evidenceRatioNextLog
continuouslyConverges_evidenceRatioNextLog
randomEvidenceRatioNextLog_graphLaw_tendsto
```
with the random endpoint
\[
\bigl(Y_j,L_j(R_{N_j}(Y_j)-R_0(Y_j))\bigr)
\Rightarrow (Y,R_1(Y))
\]
whenever \(Y_j\Rightarrow Y\) on the product domain.

Add the fixed-numerator corollary \(x'=x_\star\), obtained by a continuous embedding rather than a second proof.

**Inputs:** XCV, u387, XCVIII; compactness of the two projections.

**Traps:**
- Assume **joint** convergence of the pair. Marginal convergence is insufficient.
- Use the same normalization regime for numerator and denominator. Different \(\lambda\) or multiplicity requires an explicitly renormalized ratio.
- Signed numerator data give an algebraic ratio theorem, not automatically a physical evidence comparison.

---

## 5. One finite-vector random-observable theorem

**Priority:** the block’s author-facing capstone.

Prove finite assembly at the continuous-convergence level:
```lean
continuouslyConverges_fin
    (h : ∀ i : Fin r,
      ContinuouslyConverges (fun n x => T n x i) (fun x => C x i)) :
  ContinuouslyConverges T C
```
using the actual signature of the existing predicate.

Then expose a graph-law theorem with codomain `Fin r → ℝ`:
\[
(X_j,T_{N_j}(X_j))\Rightarrow(X,C(X)),
\]
with weak convergence of the input laws as the only probabilistic compactness hypothesis.

Instantiate it for a **concrete mixed vector** containing:

- normalized-evidence next-log remainder;
- energy-mean next-log correction;
- free-energy next-log correction;
- any prescribed finite list of Laplace-transform corrections.

All coordinates should use the same admissible random datum. Evidence ratios can have a companion instantiation on the product domain from Unit 4.

**Inputs:** XCVI–XCVIII and Units 2–4.

**Trap:** assembling already-proved marginal weak limits does **not** establish joint convergence. Assemble the deterministic maps first, then apply the graph-law engine once.

**Non-claims:** no independence of coordinates; no process convergence indexed by \(s\); no convergence of random posterior measures. This is a finite-dimensional theorem about posterior functionals.

---

## 6. Expectations under law-based uniform integrability

**Priority:** valuable closure, but strictly conditional.

Prefer a law-level theorem, allowing the random variables to live on different probability spaces.

For probability laws \(\nu_j\Rightarrow\nu\) on \(\mathbb R\), assume every coordinate is integrable and
\[
\forall\varepsilon>0\ \exists R>0\ \forall j,\qquad
\int |t|\mathbf1_{\{|t|>R\}}\,d\nu_j(t)<\varepsilon.
\]
Prove
\[
\int |t|\,d\nu(t)<\infty,
\qquad
\int t\,d\nu_j(t)\longrightarrow\int t\,d\nu(t).
\]

A suitable public name is:
```lean
integrable_and_tendsto_integral_of_weakly_of_uniformIntegrable
```
though reuse Mathlib’s existing UI formulation if it already fits the moving-law setting.

Then give at least two application corollaries, for example:
\[
\mathbb E[\text{energy next-log statistic}_j]\to\mathbb E[c_2(X)]
\]
and
\[
\mathbb E[\text{free-energy next-log statistic}_j]
\to\mathbb E[-B(X)/F(X)].
\]

**Inputs:** the marginal laws from the graph theorems; bounded continuous truncations.

**Traps:** tightness is not UI, and compact-uniform asymptotics do not control rare excursions toward \(F=0\). Do not present UI as something already obtained from XCVIII.

**Scope limit:** scalar expectations, then coordinatewise finite-vector corollaries. No general unbounded-test-function framework.

---

## How the block should end

**End with consolidation.** After these six units, the missing ingredient is unlikely to be another quotient calculation. It will be visibility of what has actually been proved.

The theorem map should distinguish:

| Layer | Public guarantee |
|---|---|
| Deterministic | Two-term spatial expansions, including multiplicity one |
| Uniform | Compact-uniform evidence and transformed statistics |
| Random | Graph laws from weakly converging data, no separate tightness assumption |
| Physical | Exact posterior identifications under explicit positivity hypotheses |
| Expectations | Only with an additional UI hypothesis |

The headline should be the **joint random next-log posterior-observable theorem**, with free energy and evidence ratios listed as companion consequences.

I would defer finite-chart assembly, transverse sensitivity, and stronger \(s\)-indexed results until after that consolidation. Those are genuine next directions; they should not obscure the substantial spatial/random theorem package now within one bounded block of completion.
