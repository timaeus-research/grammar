## (A) Mathematical errors and misstatements

### Normalisations and the paper’s terminology

1. **“For the normalised Gaussian prior … \(\int\prod_i|w_i|^{2z}\varphi(w)\,dw=\pi^{-L/2}2^{(L-1)z}\Gamma(z+\tfrac12)^L\).”**  
   For independent standard Gaussian weights, the left side has factor \(2^{Lz}\). The displayed right side is instead \(\int K^z\varphi\,dw\), with \(K=(\prod_iw_i)^2/2\). Change the left side; the subsequent Gaussian expansion uses the latter convention correctly.

2. **“The flat prior … \(\rho_2(t)=\tfrac12\log(1/|t|)\).”**  
   This is the **normalised uniform** prior. Earlier flat-prior evidence, and the formal theorems, use **Lebesgue measure**, whose density is \(2\log(1/|t|)\). Accordingly, `eq:dln_frozen` is one quarter of the Lebesgue-normalised formula. Explicitly announce the change or multiply that equation by four.

   Likewise, the survey’s mixed-monomial coefficients \(\Gamma(1/6)/4,-\sqrt\pi/4\) concern \([0,1]^2\); `eq:mixed_flat` concerns \([-1,1]^2\). The “boundary walls, no parity cancellation” description belongs only to the former.

3. **“The polar distribution of the model is exactly …”; “against the polar distribution \(2\log(1/|t|)\).”**  
   These are **pushforward/state densities**. They encode scalar zeta functionals for insertions depending on the output, but are not themselves the paper’s parameter-space polar coefficient distributions \(A_{\mu,r}\). In particular, the unweighted output density does not determine insertions such as \(w_1^2\).

4. **“\(\mathbb E[w_1w_2\mid\xi]\) … the partially vanishing regime”; “\(\mathbb E[w_1^2]\) … the fully vanishing regime.”**  
   These classifications are reversed relative to the distinction correctly illustrated in the blow-up section:
   - \(w_1^2\): **partially vanishing**—a lower logarithmic coefficient remains at the leading exponent;
   - \(w_1w_2\), for depth two: **fully vanishing**—it vanishes on the entire zero fibre and the frozen numerator starts at a shifted exponent.

   The same correction applies to naive Bayes: \(\mu\) is fully vanishing; \(t(1-t)\) is partially vanishing, not generic. Label-antisymmetric \(t-\tfrac12\) has an exactly zero posterior by symmetry, despite being nonzero at both leading atoms.

### Survey and DLN

5. **“Comparability fixes the exponents and logarithmic degrees.”**  
   Comparability determines the **leading pair**, not the complete exponent/logarithm structure. Also, for a general smooth monomial amplitude, coefficients need not be finite sums of Taylor coefficients at the origin: finite parts depend on amplitude restrictions along whole faces.

6. **“For \(\lambda=\tfrac12\) everything reduces to derivatives of \(S_{1/2}\), which is an error function”; “the empirical theory is closed in elementary functions.”**  
   Argument derivatives generate the half-integer orbit. **Index derivatives** introduce logarithmic moments and do not thereby reduce to that orbit. Moreover, \(S_{1/2}\) is an exponential times an error-function expression, not an elementary function.

7. **“\(f=\prod w_i^2\) is the model’s own output.”**  
   It is the **squared** output, equal to \(2K\) under the section’s normalisation.

   **“\(\mathbb E[K]\sim1/(2N)\) is regular.”**  
   Correct at zero field. For the frozen DLN regression field,
   \[
   \mathbb E[K\mid\xi]\sim\frac{1+\xi^2}{2N}.
   \]

8. **“\(N(\mathrm{ratio}-1)\to0.25,-0.14,0.09\).”**  
   The next pole gives the actual limits
   \[
   \frac{(-1)^L}{2^L}=\frac14,\;-\frac18,\;\frac1{16}
   \quad(L=2,3,4).
   \]
   The quoted finite-range estimates retain logarithmic corrections. Likewise, **“\(\mathbb E[w_1^2]=2/(\log N+3\log2-\gamma)\) to all shown digits”** is inconsistent with the displayed table: it is an asymptotic leading-pole ratio, not that finite-\(N\) equality.

9. **“A harmonic polynomial … [is] seen instead at the shifted exponent through \(|w|^2\)-multiples.”**  
   For a radial prior/domain, a positive-degree harmonic polynomial—and every radial multiple of it—has zero spherical mean, hence zero integral at every order. Nonzero corrections require nonradial amplitude components.

   The table’s **“\(K=|w|^2\): identity”** is also not a monomial resolution when \(d>1\); use the radial blow-up.

### Cone

10. **“A two-sheeted hyperboloid”; “overlaps of measure zero on the divisor”; “the conic \(E\cap\widetilde C\).”**  
    Here \(z^2+t^2-y^2=1\) is **one-sheeted**. Standard blow-up charts overlap on open subsets, including on the divisor; assembly requires a partition of unity or explicitly disjoint sectors. The intersection in \(\mathbb{RP}^3\) is a **quadric surface**, not a conic.

11. **“The next candidate exponent … \(\tfrac54\) … is realised for a constant amplitude: the expansion continues in steps of \(\tfrac14\).”**  
    False. For this constant-amplitude chart, setting \(t=x^2v\) gives exactly
    \[
    Z_N(1;a)=\frac12\int_0^1(1-t)e^{-Nt^2+\sqrt N at}\,dt.
    \]
    Thus there are only the two displayed algebraic terms; the remainder is exponentially small for fixed \(a\). The \(\tfrac54\) coefficient is zero.

12. **“The resonant \(v\)-derivatives … are derivatives of functions pulled back from \(\mathbb R^4\), which are constant along \(E\).”**  
    This does not establish cancellation of all chart double poles. Chart amplitudes also contain Jacobian units and cutoffs, and higher exceptional derivatives of pullbacks need not be tangentially constant. The global Leray-density argument establishes the cancellation; do not replace it with this unsupported chartwise explanation.

13. **“The vertex is the exceptional divisor’s leading measure at exponent \(1\) … negative.”**  
    Call it the **signed correction distribution**
    \[
    -4\pi^2\varphi(0)\delta_0.
    \]
    It is not a positive leading measure in the paper’s leading-measure theorem.

14. **“The tilt \(e^{\sqrt Nva}\) is odd in \(v\)”**, and `eq:cone_frozen`.  
    The tilt is not odd; it breaks reflection symmetry. More importantly, the \(B\)-series must be
    \[
    \sum_{i\ge0}b_iN^{-(i+2)/2}
       \int_{\mathbb R}t^i|t|e^{-t^2/2+at}\,dt,
    \]
    not \(b_i m_{i+1}(a)\) for every \(i\). The displayed absolute moment is correct only for even \(i\). Odd \(i\) require signed absolute moments.

15. **“`eq:cone_posterior_field` is bounded and its average …”**  
    It is not bounded as a function of \(a\); neither is the exact Gaussian-prior posterior mean uniformly bounded in \(a\). Averaging a fixed-field expansion requires a separate domination/uniform-remainder argument. The proposed averaged first coefficient, if justified, simplifies to \(1/\sqrt\pi\).

### Blow-up example

16. **“Both walls resonate at every half-integer \(\tfrac12+j\) (orders \((2j,2j)\)) … the expansion is therefore … [with all logarithms realised].”**  
    At \(\mu=\tfrac12+j\), the orders are
    \[
    (\alpha_u,\alpha_v)=(4j,2j).
    \]
    At integers \(\mu=1+j\), the exceptional-wall order \(2+4j\) is even, so simple integer poles can survive. Odd exceptional orders occur at \(3/4+j/2\). The Gaussian constant-amplitude calculation has additional integer-pole cancellations; parity alone does not establish them. Your \(x^2\) insertion already exhibits a surviving integer pole.

17. **“\(s=r^2\) … a normal-crossing form … with a smooth amplitude”; “every coefficient statement … applies.”**  
    \(s=r^2\) is not a smooth boundary coordinate change on the oriented blow-up. A general pulled-back smooth amplitude contains terms such as \(\sqrt{s}\cos\theta\). The \(r\)-coordinate gives the ordinary smooth oriented blow-up; using \(s\) requires additional evenness or an antipodal assembly argument. The radial Gaussian has that additional structure.

18. **“The finite parts sum to the \(5\log2\) and the Gamma derivative to the \(-\gamma_E\).”**  
    For the global Gaussian zeta functional in the stated normalisation,
    \[
    A_{1/2,2}=\frac1{\sqrt2},\qquad
    A_{1/2,1}=\frac{3\log2-2\gamma_E}{\sqrt2}.
    \]
    Thus the finite-part contribution is \(3\log2-2\gamma_E\), and the Gamma-derivative contribution is \(\gamma_E+2\log2\). Their sum is correctly \(5\log2-\gamma_E\).

19. **“\(\xi_1\) … enter[s] only at the constant term through the ladder, via \(\partial_w\zeta\) … and \(S_1\).”**  
    Its first appearance is indeed in the constant term, but that coefficient involves the **whole field trace along the exceptional wall**, through finite-part integrals—not merely its first derivative at the crossing.

    **“\(e^{\xi_2^2/2}\) integrable … only marginally.”**  
    It is **not integrable** against \(N(0,1)\); cancellation of the Gaussian density leaves a constant over the whole real line.

### Rank-one truth

20. **“The data first enter the posterior expectation at order \(1/N\).”**  
    Generally false: frozen fields restore \(N^{-1/2}\) corrections. For your named observable
    \[
    f=\langle x,a\rangle\langle y,b\rangle=\langle xy^{\mathsf T},A\rangle,
    \]
    the normal Gaussian calculation gives
    \[
    \mathbb E[f\mid\Xi]
       =c+N^{-1/2}\langle A,\Xi\rangle+O(N^{-1}),
    \]
    since \(A\in T_A\). A constant leading tilt does not eliminate first-order normal shifts. The integer-step statement is a **population**, not general frozen-field, statement.

### Naive Bayes

21. **“Four … faces … meeting pairwise along intervals and all together at the two points \(P_0,P_1\).”**  
    The faces \(t=0\) and \(t=1\) are disjoint. At each \(P_i\), **three** components meet. The two \(\eta\)-components intersect along the interval parametrised by \(t\).

22. **“\(\Gamma(s)T_f(s)\) … has its leading pole \(2c_3[f]/(\Gamma(\tfrac32)(\tfrac32-s)^3)\).”**  
    The correct distinction is
    \[
    \Gamma(s)T_f(s)\sim\frac{2c_3[f]}{(\tfrac32-s)^3},
    \qquad
    T_f(s)\sim\frac{2c_3[f]}{\Gamma(\tfrac32)(\tfrac32-s)^3}.
    \]

23. **“The \(\log V\) terms cancel”** in the standardised coordinates.  
    Only at leading order: the density contains \(V(\lambda)\), whereas the scaling uses \(V(\lambda^*)\). Retain
    \[
    \frac12\log\frac{V(\lambda)}{V(\lambda^*)}
    \]
    when discussing higher coefficients. This does not invalidate the displayed leading polynomial.

24. **`eq:nb_frozen`: “\(\to\)” an expression containing \(L=\log N\).**  
    Replace it by equality to the displayed expression **plus \(o(1)\)**, with bounded standardised empirical fields specified. It is not convergence to a fixed limit.

---

## (B) Fidelity to the supplied theorem headlines

These conclusions concern the headlines, not an inspection of the Lean source.

1. **Crossing normalisation:** DXCI–DXCV use Lebesgue measure. They support the later Lebesgue formula, not `eq:dln_frozen` verbatim; that equation needs division by four explicitly identified.

2. **Cone chart asymptotics:** DLXXXII supplies polar and empirical **coefficient identities**. The quoted headline does not itself supply the stated \(O(N^{-5/4})\) asymptotic theorem. Cite the general asymptotic theorem used to turn those identities into an expansion. It certainly does not support a nonzero \(N^{-5/4}\) coefficient.

3. **“Both polar coefficients” in the crossing all-orders statement:** DXCII directly evaluates **population coefficients**. For the full-square phase \(K=(xy)^2/2\), the actual polar data are
   \[
   A_{1/2,2}=\sqrt2,\qquad A_{1/2,1}=-\sqrt2\log2.
   \]
   The constants \(\sqrt{2\pi}\) and \(\sqrt{2\pi}(\gamma+\log2)\) are their Gamma-transformed population coefficients.

4. **Exact identities versus formal asymptotics:** DXCV proves exact evidence/numerator identities; the quoted statements do not separately state the tail estimates and quotient limit. Similarly, DXCIII proves the cone’s closed form, not a formally stated all-orders Taylor expansion. Distinguish “formally exact formula from which we derive the expansion” from “formal expansion theorem.”

5. **Blow-up zeta:** DXC proves a real integral identity for \(w>-\tfrac12\). Complex meromorphic continuation, Laurent coefficients and Mellin-contour asymptotics remain additional arguments. The note mostly acknowledges this correctly; avoid presenting “double poles are formal” as part of that particular theorem.

6. **Naive Bayes leading measure:** DLXXXIX controls insertions depending on the **moments**. It does not establish the weighted asymptotic for arbitrary parameter observables \(f\), nor concentration at \(P_0,P_1\). Label symmetry proves equal weights once concentration there is established, not the concentration itself.

The later headlines do close the earlier advertised gaps in the angular Beta integral and naive Bayes density. Those are **not** remaining formalisation gaps.

---

## (C) Exposition — five changes

1. Put a normalisation box first: phase \(K\), prior mass, one-sided versus two-sided chart, and \(A\)- versus \(C\)-convention.
2. Replace most of the long candidate survey with a one-page status table; move speculative candidates and duplicated derivations to an appendix.
3. Give each example a compact opening result: leading pair, leading measure, first correction, and one observable for each applicable vanishing regime.
4. Separate three statuses visibly: **Lean theorem**, **analytic derivation**, **numerical check**. Narrow the abstract’s “complete” claim: the rank-one example currently has an exact reduction and leading asymptotics, not a complete expansion.
5. Distinguish state densities, polar distributions, population coefficients and leading measures before using them interchangeably. This would remove several substantive ambiguities above.

---

## (D) What next

### Ranked gaps by value to the paper

1. **Blow-up nonconstant-amplitude tie coefficient and chart assembly.** Most direct missing demonstration of unequal-wall finite parts.
2. **Naive Bayes leading Laplace term and parameter-space leading measure.** The log-square amplitude and two leading atoms are distinctive.
3. **Cone correction distribution for nonconstant insertions/general priors.** This would substantiate the signed vertex correction beyond the unweighted Gaussian evidence.
4. **Rank-one leading normal integral and tilt identification**, then the Morse–Bott expansion.
5. **Depth-\(\ge3\) flat DLN Laplace evaluations.** Useful regression tests, but less new machinery.
6. **Gaussian DLN/Bessel evaluations.** Lowest marginal value; a special-function detour is unnecessary for the central examples.

### At most three day-sized formal targets

1. **Unequal-wall tie formula for polynomial amplitudes.**  
   For the unit positive chart \(h=(1,0),k=(2,1)\), prove
   \[
   A_{1/2,2}[\eta]=\frac{\eta(0,0)}8,
   \]
   \[
   A_{1/2,1}[\eta]
   =\frac12\int_0^1\frac{\eta(u,0)-\eta(0,0)}u\,du
    +\frac14\int_0^1\frac{\eta(0,v)-\eta(0,0)}v\,dv.
   \]
   Polynomial amplitudes make this finite rational-function algebra using existing monomial lemmas. This is genuinely new lower polar data; defer the general smooth remainder argument.

2. **Naive Bayes quadratic log-square surrogate.**  
   Formalise Gaussian scaling for the quadratic Fisher phase with the displayed log-square/sign amplitude, obtaining the exact polynomial in \(\log N\), with the second logarithmic moment initially left as an integral. Prove its leading coefficient \(c_3=\pi\sqrt{2\pi}V\). This isolates the missing logarithmic-amplitude mechanism without claiming the nonlinear KL remainder is already controlled.

3. **Rank-one normal tilt in explicit adapted coordinates.**  
   Prove the finite product Gaussian integral with normal eigenvalues
   \[
   |y|^2\;(M-1\text{ times}),\quad
   |x|^2\;(N-1\text{ times}),\quad |x|^2+|y|^2,
   \]
   including the linear field. Identify the resulting factor as
   \(e^{\|P\Xi\|^2/2}\), independent of gauge position. Keep the scope to the normal integral and leading-measure weight—not a full noncompact Morse–Bott remainder theorem.