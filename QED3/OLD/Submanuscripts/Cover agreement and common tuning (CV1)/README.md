**Cover agreement and common tuning (CV1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **CV1**.

- **[CVO1](CVO1.pdf)** — [Agreement across covers and common tuning](CVO1.pdf).
- **AI-written manuscript:** **[CVM1](CVM1.pdf)** — [Agreement across covers and common tuning for lattice QED in three dimensions](CVM1.pdf) · [TeX source](CVM1.tex).
- **Human-written manuscript:** to be added.

**Main statements**

The setting and principal theorem below are reproduced from **[CVM1](CVM1.pdf)**. Notation and numbered references follow that manuscript; references to other documents use their codenames. The referenced activity spaces, maps and imported hypotheses remain part of the statement.

Fix $`0<\rho<1`$, the chamber weights $`(6,6\sqrt2,6\sqrt2,6)`$,
and an odd integer $`L\ge4^8`$, an integral power $`M`$ of $`L`$ with
$`M\ge L^2`$, integers $`r\ge2`$ and $`p_0,p>0`$, $`0<\varepsilon\le1/200`$,
$`1-\varepsilon<\alpha<1`$, $`c_{\rm fl}\ge1`$, and $`0<\bar m\le1`$.
The photon is periodic and the four-component chamber spinors are
antiperiodic in all three directions. Each photon site has 48 chamber
labels, with measure $`\eta_k^3/48`$ at mesh $`\eta_k=L^{-k}`$.
For an integer $`N\ge0`$, set

<!-- display-math:eq-038-1b1b96ff6c
h=L^{\lfloor\log_L(1/\bar m)\rfloor},\qquad
 \eta=L^{-N},\quad K=N+\log_Lh,\quad
 a_j=L^{j-N},\quad e_j=e\sqrt{a_j},\quad \mu_j=\bar m a_j.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-038-1b1b96ff6c.dark.svg">
    <img src="../../../../assets/eq-038-1b1b96ff6c.light.svg" alt="h=L^{\lfloor\log_L(1/\bar m)\rfloor},\qquad \eta=L^{-N},\quad K=N+\log_Lh,\quad a_j=L^{j-N},\quad e_j=e\sqrt{a_j},\quad \mu_j=\bar m a_j." width="627">
  </picture>
</p>

Here $`0\le j\le K`$, and $`q=e\sqrt\eta`$ denotes the charge at
level zero. We write $`\bar e_0,\bar e_1`$ for the fixed charge
ceilings, to distinguish them from the running charges $`e_j`$.
Put $`v_j=-\log e_j`$, and let $`r_j`$ be the least power $`L^i`$,
$`i\in\mathbb Z_{\ge0}`$, with $`r_j\ge v_j^r`$. The physical sides are

<!-- display-math:eq-039-1eb7b89538
R_{\rm top}=hMr_K,\quad R^*=R_{\rm top}/L,\qquad
 \mathcal T(e)=\{hL^T:T\in\mathbb N\cup\{0\},\ hL^T\le R_{\rm top}\}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-039-1eb7b89538.dark.svg">
    <img src="../../../../assets/eq-039-1eb7b89538.light.svg" alt="R_{\rm top}=hMr_K,\quad R^*=R_{\rm top}/L,\qquad \mathcal T(e)=\{hL^T:T\in\mathbb N\cup\{0\},\ hL^T\le R_{\rm top}\}." width="549">
  </picture>
</p>

They are independent of $`N`$. For $`R\in\mathcal T(e)`$, define
$`\ell_j=R/a_j`$ and
$`\mathfrak n_j=\log_L(\ell_j/(Mr_j))`$. The stopping level $`k_*(R)`$
is the first $`j`$ with $`\mathfrak n_j=0`$, when it exists.
Write $`k_{\rm top}=k_*(R_{\rm top})`$. A star denotes evaluation
at $`k_*(R)`$: for example $`a_*=a_{k_*(R)}`$ and
$`\mu_*=\mu_{k_*(R)}`$.

**Numerical hypotheses.**

Assume

<!-- display-math:eq-040-912104fc4f
\begin{gathered}
 0<e\sqrt h\le\bar e_1\le\min(\bar e_0,1/3),\qquad
 \bar e_0^\varepsilon\le1/4,\\[0pt]
 c_{\rm fl}L^{-3/8+6/200}\le1/16,\qquad L^{-5/8}\le1/4,
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-040-912104fc4f.dark.svg">
    <img src="../../../../assets/eq-040-912104fc4f.light.svg" alt="\begin{gathered} 0&lt;e\sqrt h\le\bar e_1\le\min(\bar e_0,1/3),\qquad \bar e_0^\varepsilon\le1/4,\\[0pt] c_{\rm fl}L^{-3/8+6/200}\le1/16,\qquad L^{-5/8}\le1/4, \end{gathered}" width="313">
  </picture>
</p>

and, for every $`v\ge-\log\bar e_1`$,

<!-- display-math:eq-041-a5530b901e
\begin{gathered}
 v\ge8,\qquad
 \left(1+\frac{3\log L}{2v}\right)^r<L,\qquad
 v^r>31L+16,\\[0pt]
 (c_{\rm fl}+2)e^{-\varepsilon v}
       \le\frac{1-L^{-\varepsilon/2}}{16}.
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-041-a5530b901e.dark.svg">
    <img src="../../../../assets/eq-041-a5530b901e.light.svg" alt="\begin{gathered} v\ge8,\qquad \left(1+\frac{3\log L}{2v}\right)^r&lt;L,\qquad v^r&gt;31L+16,\\[0pt] (c_{\rm fl}+2)e^{-\varepsilon v} \le\frac{1-L^{-\varepsilon/2}}{16}. \end{gathered}" width="368">
  </picture>
</p>

**The activity maps.**

Use the real chamber activity spaces, with independent connection
arguments, defined in [Section 2](CVM1.pdf). Write $`\mathscr E_j`$ for an activity
with external connection $`\mathscr C`$, and $`E_j=\mathscr E_j|_{\mathscr C=0}`$.
At every used scale impose all the simultaneous hypotheses
(i)–(iv) of [NLM1](../Nonlinear%20renormalization%20step%20%28NL1%29/NLM1.pdf) ([Theorem A](../Nonlinear%20renormalization%20step%20%28NL1%29/NLM1.pdf)), including its
primitive, inverse-domain, determinant, extraction, reconstruction,
contour and connected-logarithm conditions. The constants, norms and
operators are those of that theorem and of
[RNM1](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) ([Theorems A](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)–[B](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)); their definitions and the
parts used below are recalled in [Section 2](CVM1.pdf) and [Section 3](CVM1.pdf).
These are hypotheses on the actual chamber maps. In particular the
following tuning inequalities do not replace their domain or numerical
conditions. The decay weight satisfies $`\kappa\ge7\kappa_0+7`$, where
$`\kappa_0=54\log72`$; the constants are calibrated together as in the
[cited step theorem](../Nonlinear%20renormalization%20step%20%28NL1%29/NLM1.pdf).

On the top torus choose the photon and fermion families of
[Section 4.3](CVM1.pdf), with polymer decay
$`\kappa_w+\kappa_0`$, where $`\kappa_w=\kappa+\kappa_0+3`$.
On each smaller odd quotient use their projections, with common
constant $`C_w=64K_0C_w^{(1)}`$, $`K_0=\exp(\kappa_0)/36`$.
Both incoming and outgoing sides are required to have
$`\ell/(LM)`$ odd and at least 13. The step comparison requires
$`\ell_{\rm small}/L>(31L+16)M`$; the stopping calculation verifies
these side conditions at all steps used in the theorem.

For a comparison with smaller unit side $`\ell_1`$, a connected
covering polymer $`\widetilde X`$ is admissible when its smallest
rectangular box has largest side at most $`\ell_1-14(2L+1)M`$.
Its two torus images are called flat. Local agreement means equality
under the common covering generators for connection pairs agreeing
on $`\mathrm{box}(\widetilde X)^{\sim6(2L+1)}`$.
Here the superscript denotes enlargement by that number of $`M`$-cube
layers. [Proposition 5.1](CVM1.pdf) justifies this identification.

The estimates used for tuning take the following form.
Set $`w_j^{\mathrm m}=e_j^{3/4-8\varepsilon}`$ and
$`w_j^{\mathrm E}=e_j^{1/4-7\varepsilon}`$.
The no-slot data norm is
$`\max\{|m|/w_j^{\mathrm m},\|E\|_j/w_j^{\mathrm E}\}`$; with an external slot,
replace $`\|E\|_j`$ by $`\|\mathscr E\|_j^x`$.
Radius-four data balls mean the corresponding closed balls in the
complexified spaces. Unit balls below are closed balls in their real
subspaces. At zero the activity coordinate is fixed to zero.
The maps preserve reality and obey

<!-- display-math:eq-042-4e7e72252d
\begin{aligned}
m_{j+1}&=L(m_j+m(E_j)),&
 \varepsilon_{j+1}^v&=L^3(\varepsilon_j^v+\varepsilon_v(E_j)+\delta\varepsilon_j^0),
 \\[0pt]
 E_{j+1}&=\Phi_j(m_j,E_j),&
 \Phi_j(m,E)&=\mathcal L(RE)^{\rm nat}
                  +\mathcal LE_j^{\det}+E_j^*(m,E).
\end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-042-4e7e72252d.dark.svg">
    <img src="../../../../assets/eq-042-4e7e72252d.light.svg" alt="\begin{aligned} m_{j+1}&amp;=L(m_j+m(E_j)),&amp; \varepsilon_{j+1}^v&amp;=L^3(\varepsilon_j^v+\varepsilon_v(E_j)+\delta\varepsilon_j^0), \\[0pt] E_{j+1}&amp;=\Phi_j(m_j,E_j),&amp; \Phi_j(m,E)&amp;=\mathcal L(RE)^{\rm nat} +\mathcal LE_j^{\det}+E_j^*(m,E). \end{aligned}" width="509">
  </picture>
</p>

Restriction to $`\mathscr C=0`$ commutes with the full external-slot recursion
and does not increase its norm. Scalar extraction is linear and real,

<!-- display-math:eq-043-16fbc07414
|m(E)|\le c_{\rm fl}e_j^{1/2}\|E\|_j,\qquad
 |\varepsilon_v(E)|\le c_{\rm fl}\|E\|_j,\qquad
 0\le\delta\varepsilon_j^0\le e_j^7.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-043-16fbc07414.dark.svg">
    <img src="../../../../assets/eq-043-16fbc07414.light.svg" alt="|m(E)|\le c_{\rm fl}e_j^{1/2}\|E\|_j,\qquad |\varepsilon_v(E)|\le c_{\rm fl}\|E\|_j,\qquad 0\le\delta\varepsilon_j^0\le e_j^7." width="441">
  </picture>
</p>

On the unit ball the normalized size and difference estimates are

<!-- display-math:eq-044-1f4c44bd21
\begin{aligned}
 L^{-1}w_{j+1}^m/w_j^{\mathrm m}&\le1/4,\\[0pt]
 \|\Phi_j(m,E)\|_{j+1}/w_{j+1}^E
   &\le\tfrac1{16}\|E\|_j/w_j^{\mathrm E}+2e_{j+1}^{\varepsilon},\\[0pt]
 |m(E)-m(\widetilde E)|/w_j^{\mathrm m}
   &\le c_{\rm fl}e_j^\varepsilon d_E,\\[0pt]
 \|\Phi_j(m,E)-\Phi_j(\widetilde m,\widetilde E)\|_{j+1}/w_{j+1}^E
   &\le\tfrac1{16}d_E+e_{j+1}^\varepsilon(d_m+d_E),
 \end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-044-1f4c44bd21.dark.svg">
    <img src="../../../../assets/eq-044-1f4c44bd21.light.svg" alt="\begin{aligned} L^{-1}w_{j+1}^m/w_j^{\mathrm m}&amp;\le1/4,\\[0pt] \|\Phi_j(m,E)\|_{j+1}/w_{j+1}^E &amp;\le\tfrac1{16}\|E\|_j/w_j^{\mathrm E}+2e_{j+1}^{\varepsilon},\\[0pt] |m(E)-m(\widetilde E)|/w_j^{\mathrm m} &amp;\le c_{\rm fl}e_j^\varepsilon d_E,\\[0pt] \|\Phi_j(m,E)-\Phi_j(\widetilde m,\widetilde E)\|_{j+1}/w_{j+1}^E &amp;\le\tfrac1{16}d_E+e_{j+1}^\varepsilon(d_m+d_E), \end{aligned}" width="411">
  </picture>
</p>

where $`d_m=|m-\widetilde m|/w_j^{\mathrm m}`$ and
$`d_E=\|E-\widetilde E\|_j/w_j^{\mathrm E}`$.
The same size estimate holds for the external-slot norm. The
fixed-point argument uses the no-slot difference estimate.
Initially $`E_0=\mathscr E_0=\mathfrak P_0=0`$, where
$`\mathfrak P_j`$ is the scalar external family in [Section 3](CVM1.pdf).
The first step uses the chamber definitions in [Section 3](CVM1.pdf).

**[Theorem A](CVM1.pdf) (A common mass and vacuum pair).**

Under the hypotheses above, the following assertions hold.
For each $`R\in\mathcal T(e)`$ there is a finite threshold
$`N_{\min}(R,e)`$ such that the first stop exists for
$`N\ge N_{\min}(R,e)`$. Its physical quantities are then independent
of $`N`$. The thresholds are nonincreasing and the stopping levels
nondecreasing
with $`R`$; their precise formulas are in [(52)](CVM1.pdf).

For $`N\ge N_{\min}(R_{\rm top},e)`$, there is exactly one real
pair $`P_N(e)=(m_{0,N}(e),\varepsilon_{0,N}^v(e))`$ whose top-torus
trajectory is controlled and has
$`m_{k_{\rm top}}=\varepsilon_{k_{\rm top}}^v=0`$.
Controlled means that each preceding step is defined in its
radius-four data ball and $`|m_j|\le w_j^{\mathrm m}`$ through the stop.
For every $`R\in\mathcal T(e)`$ with $`N\ge N_{\min}(R,e)`$,
the same pair is controlled on $`R`$. Up to its stop, the scalar
mass and vacuum sequences equal the top sequences, while the
activities and external scalar families agree on admissible flat
lifts under the algebra identification of [Proposition 5.1](CVM1.pdf). On each such torus,

<!-- display-math:eq-045-e53f5891ec
|m_j|\le\tfrac18e_j^{3/4-8\varepsilon},\qquad
 \|E_j\|_j\le\|\mathscr E_j\|_j^x\le4e_j^{1/4-6\varepsilon},\qquad
 |\varepsilon_j^v|\le5c_{\rm fl}e_j^{1/4-6\varepsilon}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-045-e53f5891ec.dark.svg">
    <img src="../../../../assets/eq-045-e53f5891ec.light.svg" alt="|m_j|\le\tfrac18e_j^{3/4-8\varepsilon},\qquad \|E_j\|_j\le\|\mathscr E_j\|_j^x\le4e_j^{1/4-6\varepsilon},\qquad |\varepsilon_j^v|\le5c_{\rm fl}e_j^{1/4-6\varepsilon}." width="488">
  </picture>
</p>

The smaller terminal couplings need not vanish.

Within the fixed construction, the pair is determined by
$`(N,e,\bar m)`$ and is independent of the smaller side, twist,
external connection and probe. Define only $`m_{0,N}(e)=0`$ below
the top definition threshold. For every $`N\ge0`$,

<!-- display-math:eq-046-6515f1be90
m_{0,N}(e)\in\mathbb R,\qquad
 |m_{0,N}(e)|\le\tfrac18q^{3/4-8\varepsilon}<\tfrac18 .
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-046-6515f1be90.dark.svg">
    <img src="../../../../assets/eq-046-6515f1be90.light.svg" alt="m_{0,N}(e)\in\mathbb R,\qquad |m_{0,N}(e)|\le\tfrac18q^{3/4-8\varepsilon}&lt;\tfrac18 ." width="315">
  </picture>
</p>

The total bare mass $`\boldsymbol\mu_N=\bar mL^{-N}+m_{0,N}(e)`$
has no asserted sign. On $`R^*`$, for
$`N\ge N_{\rm ref}(e):=N_{\min}(R^*,e)`$,

<!-- display-math:eq-047-19fd70f498
a_*\in\{h/L,h/L^2\},\qquad
 \ell_*=Mr_*,\qquad r_*>31L+16,\qquad
 L^{-3}<\mu_*\le L^{-1}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-047-19fd70f498.dark.svg">
    <img src="../../../../assets/eq-047-19fd70f498.light.svg" alt="a_*\in\{h/L,h/L^2\},\qquad \ell_*=Mr_*,\qquad r_*&gt;31L+16,\qquad L^{-3}&lt;\mu_*\le L^{-1}." width="528">
  </picture>
</p>
