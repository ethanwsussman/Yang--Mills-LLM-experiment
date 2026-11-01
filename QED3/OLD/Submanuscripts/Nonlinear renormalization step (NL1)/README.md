**Nonlinear renormalization step (NL1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **NL1**.

- **[NLO1](NLO1.pdf)** — [The exact nonlinear renormalization step](NLO1.pdf).
- **AI-written manuscript:** **[NLM1](NLM1.pdf)** — [The exact nonlinear renormalization step for lattice QED in three dimensions](NLM1.pdf) · [TeX source](NLM1.tex).
- **Human-written manuscript:** to be added.

**Main statements**

The setting and principal theorem below are reproduced from **[NLM1](NLM1.pdf)**. Notation and numbered references follow that manuscript; references to other documents use their codenames. The referenced activity spaces, maps and imported hypotheses remain part of the statement.

We consider one block transformation of noncompact lattice QED with
four-component chamber fermions. The photon field is periodic on
$`\eta\mathbb{Z}^3/\ell\mathbb{Z}^3`$, and spinors are antiperiodic in every coordinate.
Each photon site carries $`48`$ chamber labels. The chamber measure is
$`\eta^3/48`$; barred and unbarred Grassmann generators are independent.
The Dirac stencil, block averages and weighted transposes are those of
[FBM1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) ([Section 1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf)).

Fix $`0<\rho<1`$, odd $`L\ge4^8`$, an integer power $`M`$ of $`L`$ with $`M\ge L^2`$ and $`M>4L`$,
and $`k\in\mathbb{Z}_{\ge0}`$. Put $`\eta=L^{-k}`$, $`e=e_k\in(0,1)`$,
$`e_{k+1}=\sqrt L e_k`$, and $`0<\mu\le1/L`$; the scaled reference
mass is $`L\mu`$. Both charges are at most the common ceiling $`e_{\mathrm{prim}}`$ of the
photon and fermion estimates specified in the theorem below. Require
$`\ell/(LM)`$ and $`\ell/(L^2M)`$ to be odd integers at least $`13`$.
Fix an integer $`r\ge2`$. For $`v=-\log e`$, put

<!-- display-math:eq-066-eb673b6bba
r_k=\min\{L^i:i\ge0\text{ an integer},\ L^i\ge v^r\},
 \qquad \ell\ge Mr_k .
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-066-eb673b6bba.dark.svg">
    <img src="../../../../assets/eq-066-eb673b6bba.light.svg" alt="r_k=\min\{L^i:i\ge0\text{ an integer},\ L^i\ge v^r\}, \qquad \ell\ge Mr_k ." width="390">
  </picture>
</p>

An activity in $`K_k^{x,\mathbb{C}}`$ is a balanced family of Grassmann
polynomials in ordinary and ordered-pair generators, holomorphic on
$`\widetilde R_k\times\mathfrak X_k`$, local in its polymer and its
connection bonds, and covariant under the lattice, independent local
real-gauge and charge-conjugation actions. The real space $`K_k^x`$
also satisfies the antilinear reality identity. We use exactly the
domains, pair support and actions of [RNM1](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) ([Section 2](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)),
recalled in [Section 2](NLM1.pdf). In particular, $`\widetilde R_k`$
permits independent local real gauges; it imposes no bound on a real
harmonic part. With $`d_M(X)`$ the connected-net length divided by $`M`$,
the weights and norm are

<!-- display-math:eq-067-5b82623aa8
h_k=(e_k^{-1/4},e_k^{-1/4+\varepsilon}),\qquad
 \|\mathscr E\|_k^x=\sup_X\exp(\kappa d_M(X))
       \sup_{\widetilde R_k\times\mathfrak X_k}\|\mathscr E(X)\|_{h_k}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-067-5b82623aa8.dark.svg">
    <img src="../../../../assets/eq-067-5b82623aa8.light.svg" alt="h_k=(e_k^{-1/4},e_k^{-1/4+\varepsilon}),\qquad \|\mathscr E\|_k^x=\sup_X\exp(\kappa d_M(X)) \sup_{\widetilde R_k\times\mathfrak X_k}\|\mathscr E(X)\|_{h_k}." width="477">
  </picture>
</p>

The coefficient norm is the sum of absolute ordered coefficients
times their generator weights. Set

<!-- display-math:eq-068-74abf43b1d
w_k^{\mathrm m}=e_k^{3/4-8\varepsilon},\quad
 w_k^{\mathrm E}=e_k^{1/4-7\varepsilon},\quad
 \mathrm{Ball}_k^x(c)=
 \{(m,\mathscr E):|m|\le cw_k^{\mathrm m},\ {}
                 \|\mathscr E\|_k^x\le cw_k^{\mathrm E}\}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-068-74abf43b1d.dark.svg">
    <img src="../../../../assets/eq-068-74abf43b1d.light.svg" alt="w_k^{\mathrm m}=e_k^{3/4-8\varepsilon},\quad w_k^{\mathrm E}=e_k^{1/4-7\varepsilon},\quad \mathrm{Ball}_k^x(c)= \{(m,\mathscr E):|m|\le cw_k^{\mathrm m},\ {} \|\mathscr E\|_k^x\le cw_k^{\mathrm E}\}." width="555">
  </picture>
</p>

At $`k=0`$ the activity is required to be zero. The interaction mass
$`m`$ is distinct from the positive reference mass $`\mu`$. Put
$`n_k=\ell^3`$, $`n_{k+1}=(\ell/L)^3`$, and $`q=e_k`$ at $`k=0`$.
The real photon domain is
$`\mathrm{Dom}_j=\{A:H_j^{\mathrm{ph}}A\in\frac14\widetilde R_j\}`$.
The density $`\mathscr F_j^x`$ and normalized block operator $`\mathbf T_k^x`$
are defined by [(38)](NLM1.pdf) and
[(39)](NLM1.pdf); the latter integrates over
$`\mathrm{Box}_k=\{\sup_\Upsilon|\zeta(\Upsilon)|\le p_{0,k}\}`$.

The quantitative constants are

<!-- display-math:eq-069-b3a69df398
\begin{gathered}
 \bar\varepsilon=1/200,\qquad
 0<\varepsilon\le\bar\varepsilon,\qquad 1-\varepsilon<\alpha<1,\\[0pt]
 c_X=54,\quad \kappa_0=54\log72,\quad K_0=\exp(\kappa_0)/36,\quad
 c_{\rm rb}=c_XK_0,\quad c_{\rm fl}=61c_{\rm rb},\\[0pt]
 c_C=3L^{9/2},\quad b=1,\quad b_L=b/L,\quad b_-=1-L^{-1},\\[0pt]
 C_T=2\exp(3/2)
       [1+b_-^{-1}(54L\exp(6)+12\exp(1)+1)],\\[0pt]
 c_S=10^5c_X^5K_0^5\exp(6\kappa),\qquad
 \kappa_w=\kappa+\kappa_0+3 .
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-069-b3a69df398.dark.svg">
    <img src="../../../../assets/eq-069-b3a69df398.light.svg" alt="\begin{gathered} \bar\varepsilon=1/200,\qquad 0&lt;\varepsilon\le\bar\varepsilon,\qquad 1-\varepsilon&lt;\alpha&lt;1,\\[0pt] c_X=54,\quad \kappa_0=54\log72,\quad K_0=\exp(\kappa_0)/36,\quad c_{\rm rb}=c_XK_0,\quad c_{\rm fl}=61c_{\rm rb},\\[0pt] c_C=3L^{9/2},\quad b=1,\quad b_L=b/L,\quad b_-=1-L^{-1},\\[0pt] C_T=2\exp(3/2) [1+b_-^{-1}(54L\exp(6)+12\exp(1)+1)],\\[0pt] c_S=10^5c_X^5K_0^5\exp(6\kappa),\qquad \kappa_w=\kappa+\kappa_0+3 . \end{gathered}" width="526">
  </picture>
</p>

The primitive constants $`C_w,\gamma_w,\alpha_0>0`$, the photon
local-gauge constant $`C_B`$, and the two exponential-sum bounds
$`c_\gamma`$ are those of the photon and fermion families in hypothesis (i) below; $`C_w,c_\gamma\ge1`$.

**[Theorem A](NLM1.pdf) (The exact nonlinear step).**

In the setting above, assume the following simultaneous hypotheses.

**(i)**  Use a single system of photon and fermion primitives on this
torus. Assume the full hypotheses and conclusions of
[MBM1](../Maxwell%20block%20analysis%20%28MB1%29/MBM1.pdf) ([Theorems A](../Maxwell%20block%20analysis%20%28MB1%29/MBM1.pdf)–[B](../Maxwell%20block%20analysis%20%28MB1%29/MBM1.pdf) and [Proposition 5.1](../Maxwell%20block%20analysis%20%28MB1%29/MBM1.pdf))
and
[FBM1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) ([Theorem A](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf), [Propositions 4.1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf),
[4.2](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf),
[4.3](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf),
[6.1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) and
[6.2](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf)).
Use common constants $`(\alpha_0,\gamma_w,\kappa_w;C_w)`$ for their
analytic kernel and short Hölder bounds on
$`|s_a|\le M^{\alpha_0}`$. This assumption includes component
restriction, row vanishing, local read bonds, the exact operators at
$`s=1`$, and their lattice, gauge, transpose and reality identities.
At $`k=0`$ retain the stated diagonal families and chamber covariance.
Use the weighted integration conventions of
[FBM1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) ([Theorem B](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) and [Proposition 5.1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf))
and the extraction, reconstruction and geometry of
[RNM1](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) ([Theorems A](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)–[B](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) and [Appendix B](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)).
The fine inverses required for reconstruction exist at both signs
of every total connection in $`\widetilde G_k`$ by the fermion hypothesis.

**(ii)**  The extraction and scaling parameters satisfy

<!-- display-math:eq-070-b79472d206
\begin{gathered}
 L^{1/8-3\bar\varepsilon/2}\ge2400,\qquad e^\varepsilon\le\tfrac14,\qquad
 160L^{1+3\varepsilon/2}Me^\varepsilon\le1,\\[0pt]
 9ML^\varepsilon e^{2\varepsilon}\le1,\qquad
 90c_XLMe^\varepsilon\le1,\\[0pt]
 \kappa\ge7\kappa_0+7,\qquad
 L(\kappa-6\kappa_0-4)-1\ge\kappa .
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-070-b79472d206.dark.svg">
    <img src="../../../../assets/eq-070-b79472d206.light.svg" alt="\begin{gathered} L^{1/8-3\bar\varepsilon/2}\ge2400,\qquad e^\varepsilon\le\tfrac14,\qquad 160L^{1+3\varepsilon/2}Me^\varepsilon\le1,\\[0pt] 9ML^\varepsilon e^{2\varepsilon}\le1,\qquad 90c_XLMe^\varepsilon\le1,\\[0pt] \kappa\ge7\kappa_0+7,\qquad L(\kappa-6\kappa_0-4)-1\ge\kappa . \end{gathered}" width="386">
  </picture>
</p>

**(iii)**  The weakening radius and constants satisfy

<!-- display-math:eq-071-87bcb12e46
C_w\ge4\exp(2\gamma_w)M^{27\alpha_0},\qquad
 M^{\alpha_0}-1\ge\exp\big((2L+1)^3\kappa+\log(6c_X)\big).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-071-87bcb12e46.dark.svg">
    <img src="../../../../assets/eq-071-87bcb12e46.light.svg" alt="C_w\ge4\exp(2\gamma_w)M^{27\alpha_0},\qquad M^{\alpha_0}-1\ge\exp\big((2L+1)^3\kappa+\log(6c_X)\big)." width="485">
  </picture>
</p>

For the localizations, connected expansion, scaling and determinant
reblocking, assume

<!-- display-math:eq-072-a73ec1b42d
\begin{aligned}
&p_{0,k}\le e^{-\varepsilon/4},\qquad
       12\exp(-p_{0,k}^2/2)\le e^7,\qquad
       2e^{5\varepsilon/2}\le1,\qquad
       c_{\mathrm{fl}}e^\varepsilon\le1,\qquad3Me^\varepsilon\le1,
                                                        \\[0pt]
 &2c_CC_w^2c_\gamma^2e^{\varepsilon/4}\le1,\qquad
       16c_Xc_\gamma C_wC_T^2M^3e^{\varepsilon/2}\le1,\qquad
       96M^3e^{1/4}\le1,                                \\[0pt]
 &32C_wC_Te^{3\varepsilon/2}\le1,\qquad
       88M^3e^{1/4-6\varepsilon}\le1,\qquad
       112C_w^2c_\gamma e^{2\varepsilon}\le3,             \\[0pt]
 &c_Se^{1/4-5\varepsilon}\le1,\qquad
       c_SL^3e^\varepsilon\le1,\qquad e^\varepsilon\le\tfrac14,\qquad
       8c_{\mathrm{rb}}L^3C_dM^3e^{2\varepsilon}\le1.
\end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-072-a73ec1b42d.dark.svg">
    <img src="../../../../assets/eq-072-a73ec1b42d.light.svg" alt="\begin{aligned} &amp;p_{0,k}\le e^{-\varepsilon/4},\qquad 12\exp(-p_{0,k}^2/2)\le e^7,\qquad 2e^{5\varepsilon/2}\le1,\qquad c_{\mathrm{fl}}e^\varepsilon\le1,\qquad3Me^\varepsilon\le1, \\[0pt] &amp;2c_CC_w^2c_\gamma^2e^{\varepsilon/4}\le1,\qquad 16c_Xc_\gamma C_wC_T^2M^3e^{\varepsilon/2}\le1,\qquad 96M^3e^{1/4}\le1, \\[0pt] &amp;32C_wC_Te^{3\varepsilon/2}\le1,\qquad 88M^3e^{1/4-6\varepsilon}\le1,\qquad 112C_w^2c_\gamma e^{2\varepsilon}\le3, \\[0pt] &amp;c_Se^{1/4-5\varepsilon}\le1,\qquad c_SL^3e^\varepsilon\le1,\qquad e^\varepsilon\le\tfrac14,\qquad 8c_{\mathrm{rb}}L^3C_dM^3e^{2\varepsilon}\le1. \end{aligned}" width="588">
  </picture>
</p>

Here $`C_d`$ is the local determinant constant in hypothesis (i).

**(iv)**  For fixed positive exponents $`p_0,p`$, put
$`p_{0,k}=v^{p_0}`$, $`p_k=v^p`$. The photon box and domain bounds
and the determinant gain require

<!-- display-math:eq-073-33863004e0
\begin{gathered}
 p_{0,k}\le e^{-\varepsilon/4},\qquad
 12\exp(-p_{0,k}^2/2)\le e^7,\qquad
 8C_Bp_k\le e^{-3/4+3\varepsilon},\\[0pt]
 8e^{3/4-7\varepsilon/2}\le1,\qquad L^{3/4}\ge8/3,\qquad
 v\ge9,\qquad 8M(v/4+4)e^\varepsilon\le1,\\[0pt]
 e^{1/4}+e^\varepsilon<1,\qquad
 4e^{1/4+2\varepsilon}+2e^{3\varepsilon}\le1 .
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-073-33863004e0.dark.svg">
    <img src="../../../../assets/eq-073-33863004e0.light.svg" alt="\begin{gathered} p_{0,k}\le e^{-\varepsilon/4},\qquad 12\exp(-p_{0,k}^2/2)\le e^7,\qquad 8C_Bp_k\le e^{-3/4+3\varepsilon},\\[0pt] 8e^{3/4-7\varepsilon/2}\le1,\qquad L^{3/4}\ge8/3,\qquad v\ge9,\qquad 8M(v/4+4)e^\varepsilon\le1,\\[0pt] e^{1/4}+e^\varepsilon&lt;1,\qquad 4e^{1/4+2\varepsilon}+2e^{3\varepsilon}\le1 . \end{gathered}" width="468">
  </picture>
</p>

There is a local connected logarithm $`E_k^\#(m,\mathscr E)`$ on
$`\widetilde R_k^-\times\mathfrak X_k`$ for every complex datum in
$`\mathrm{Ball}_k^x(4)`$. It has the lattice symmetry with
$`LM`$ translations, independent local real-gauge covariance and
charge conjugation. Each monomial is balanced; real data give the
reality identity. Its scaled sum

<!-- display-math:eq-074-286915a9ef
E_k^*(m,\mathscr E)(Y;A,C)
   =\sum_{\bar X^L=LY}S_LE_k^\#(m,\mathscr E)(X;A_L,C_L)
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-074-286915a9ef.dark.svg">
    <img src="../../../../assets/eq-074-286915a9ef.light.svg" alt="E_k^*(m,\mathscr E)(Y;A,C) =\sum_{\bar X^L=LY}S_LE_k^\#(m,\mathscr E)(X;A_L,C_L)" width="372">
  </picture>
</p>

belongs to $`K_{k+1}^{x,\mathbb{C}}`$ and has norm at most
$`e_k^{1/4-6\varepsilon}`$. Here $`A_L(b)=L^{-1/2}A(b/L)`$;
$`S_L`$ scales ordinary legs by $`L^{-1}`$ and pair legs by
$`L^{-1-\alpha}`$, and $`\bar X^L`$ is the union of $`LM`$-cubes
containing $`X`$. The correction is norm continuous on each affine
complex line's closed allowed set and norm analytic in its interior.
For two data in $`\mathrm{Ball}_k^x(1)`$,

<!-- display-math:eq-075-1dc6a7257e
\|E_k^*(m_1,\mathscr E_1)-E_k^*(m_2,\mathscr E_2)\|_{k+1}^x
 \le e_k^{1/4-6\varepsilon}
 \left(\frac{|m_1-m_2|}{w_k^{\mathrm m}}+
       \frac{\|\mathscr E_1-\mathscr E_2\|_k^x}{w_k^{\mathrm E}}\right).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-075-1dc6a7257e.dark.svg">
    <img src="../../../../assets/eq-075-1dc6a7257e.light.svg" alt="\|E_k^*(m_1,\mathscr E_1)-E_k^*(m_2,\mathscr E_2)\|_{k+1}^x \le e_k^{1/4-6\varepsilon} \left(\frac{|m_1-m_2|}{w_k^{\mathrm m}}+ \frac{\|\mathscr E_1-\mathscr E_2\|_k^x}{w_k^{\mathrm E}}\right)." width="498">
  </picture>
</p>

The second quotient is omitted at $`k=0`$.

For the local determinant terms of
[Proposition 6.1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf) of [FBM1](../Chamber%20fermion%20block%20analysis%20%28FB1%29/FBM1.pdf), put

<!-- display-math:eq-076-8a559e0c8a
\delta E_k^{\mathrm{det}}(X;\mathscr A,\mathscr C)
       =E_k^d(X,\mathscr A+\mathscr C)-E_k^d(X,\mathscr C),
 \qquad
 E_k^{\mathrm{det}}(X,\mathscr C)
       =E_k^d(X,\mathscr C)-E_k^d(X,0).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-076-8a559e0c8a.dark.svg">
    <img src="../../../../assets/eq-076-8a559e0c8a.light.svg" alt="\delta E_k^{\mathrm{det}}(X;\mathscr A,\mathscr C) =E_k^d(X,\mathscr A+\mathscr C)-E_k^d(X,\mathscr C), \qquad E_k^{\mathrm{det}}(X,\mathscr C) =E_k^d(X,\mathscr C)-E_k^d(X,0)." width="614">
  </picture>
</p>

These are scalar activities. We use reblocking
$`\mathcal L`$ from [(34)](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) of [RNM1](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf).
The maps $`R`$, $`(\cdot)^{\mathrm{nat}}`$, $`m(\cdot)`$ and
$`\varepsilon_{\mathrm v}(\cdot)`$ are the subtraction, adjustment and
extraction maps of [RNM1](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf) ([Theorem A](../Relevant%20extraction%20and%20normalized%20contraction%20%28RN1%29/RNM1.pdf)).
The outgoing maps are

<!-- display-math:eq-077-7b2328ce83
\begin{aligned}
\mathscr E^+&=\mathcal L(R\mathscr E)^{\mathrm{nat}}
                        +\mathcal L\delta E_k^{\mathrm{det}}
                        +E_k^*(m,\mathscr E), \\[0pt]
 m^+&=L(m+m(\mathscr E)),\\[0pt]
 \varepsilon^{\mathrm v,+}
       &=L^3(\varepsilon^{\mathrm v}
                  +\varepsilon_{\mathrm v}(\mathscr E)
                                      +\delta\varepsilon_k^0),\\[0pt]
 \mathfrak P_{k+1}(Y,\mathscr C')
       &=\sum_{\bar X^L=LY}
           \big(\mathfrak P_k(X,\mathscr C'_L)
                          +E_k^{\mathrm{det}}(X,\mathscr C'_L)\big).
\end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-077-7b2328ce83.dark.svg">
    <img src="../../../../assets/eq-077-7b2328ce83.light.svg" alt="\begin{aligned} \mathscr E^+&amp;=\mathcal L(R\mathscr E)^{\mathrm{nat}} +\mathcal L\delta E_k^{\mathrm{det}} +E_k^*(m,\mathscr E), \\[0pt] m^+&amp;=L(m+m(\mathscr E)),\\[0pt] \varepsilon^{\mathrm v,+} &amp;=L^3(\varepsilon^{\mathrm v} +\varepsilon_{\mathrm v}(\mathscr E) +\delta\varepsilon_k^0),\\[0pt] \mathfrak P_{k+1}(Y,\mathscr C&#x27;) &amp;=\sum_{\bar X^L=LY} \big(\mathfrak P_k(X,\mathscr C&#x27;_L) +E_k^{\mathrm{det}}(X,\mathscr C&#x27;_L)\big). \end{aligned}" width="354">
  </picture>
</p>

Here $`\mathfrak P_k`$ is any given family of scalar
functions of the external slot.

Let $`\varepsilon^{\mathrm v},m`$ be real,
$`\mathscr E\in K_k^x`$, and
$`(m,\mathscr E)\in\mathrm{Ball}_k^x(1)`$, with
$`\mathscr E=0`$ at $`k=0`$. For $`A'\in\mathrm{Dom}_{k+1}`$
with arbitrary harmonic part and
$`\mathscr C'\in\mathfrak X_{k+1}`$, the exact density satisfies

<!-- display-math:eq-078-9d45b31e84
\mathbf T_k^x\mathscr F_k^x[\varepsilon^{\mathrm v},m,\mathscr E]
   =\mathscr F_{k+1}^x
            [\varepsilon^{\mathrm v,+},m^+,\mathscr E^+],
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-078-9d45b31e84.dark.svg">
    <img src="../../../../assets/eq-078-9d45b31e84.light.svg" alt="\mathbf T_k^x\mathscr F_k^x[\varepsilon^{\mathrm v},m,\mathscr E] =\mathscr F_{k+1}^x [\varepsilon^{\mathrm v,+},m^+,\mathscr E^+]," width="275">
  </picture>
</p>

with external scalar families $`\mathfrak P_k`$ and
$`\mathfrak P_{k+1}`$ on the respective sides.
Its integral satisfies

<!-- display-math:eq-079-e2729a84eb
y_{k+1}^x(A';\mathscr C')
  =\int_{\mathrm{Box}_k}\mathrm{d}\mu_I(\zeta)\,
        y_k^x(A_k^{\min}(A')+\mathrm{Sq}_k\zeta;\mathscr C'_L),
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-079-e2729a84eb.dark.svg">
    <img src="../../../../assets/eq-079-e2729a84eb.light.svg" alt="y_{k+1}^x(A&#x27;;\mathscr C&#x27;) =\int_{\mathrm{Box}_k}\mathrm{d}\mu_I(\zeta)\, y_k^x(A_k^{\min}(A&#x27;)+\mathrm{Sq}_k\zeta;\mathscr C&#x27;_L)," width="372">
  </picture>
</p>

where $`y_j^x=\int\mathrm D\Psi\,\mathscr F_j^x`$ with the
data and scalar family of that level. The photon integral uses the
unnormalized Gaussian restriction to the box.
Moreover $`\mathscr E^+\in K_{k+1}^x`$ and

<!-- display-math:eq-080-4d29521a9d
\begin{aligned}
\|\mathscr E^+\|_{k+1}^x
 &\le c_{\mathrm{fl}}L^{-1/4+2\varepsilon}\|\mathscr E\|_k^x
           +e_{k+1}^{1/4-2\varepsilon}+e_k^{1/4-6\varepsilon},
                                      \\[0pt]
 |m^+-Lm|
 &\le Lc_{\mathrm{fl}}e_k^{1/2}\|\mathscr E\|_k^x,
                                      \\[0pt]
 |\varepsilon^{\mathrm v,+}-L^3\varepsilon^{\mathrm v}|
 &\le L^3(c_{\mathrm{fl}}\|\mathscr E\|_k^x+e_k^7).
\end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-080-4d29521a9d.dark.svg">
    <img src="../../../../assets/eq-080-4d29521a9d.light.svg" alt="\begin{aligned} \|\mathscr E^+\|_{k+1}^x &amp;\le c_{\mathrm{fl}}L^{-1/4+2\varepsilon}\|\mathscr E\|_k^x +e_{k+1}^{1/4-2\varepsilon}+e_k^{1/4-6\varepsilon}, \\[0pt] |m^+-Lm| &amp;\le Lc_{\mathrm{fl}}e_k^{1/2}\|\mathscr E\|_k^x, \\[0pt] |\varepsilon^{\mathrm v,+}-L^3\varepsilon^{\mathrm v}| &amp;\le L^3(c_{\mathrm{fl}}\|\mathscr E\|_k^x+e_k^7). \end{aligned}" width="360">
  </picture>
</p>

At level zero this formula integrates all $`192n_0`$
incoming pairs of generators, with chamber measure $`1/48`$,
and leaves $`4n_1`$ outgoing pairs. Its data are

<!-- display-math:eq-081-b4ac02ab03
\mathscr E^+=\mathcal L\delta E_0^{\mathrm{det}}+E_0^*(m,0),
 \quad m^+=Lm,\quad
 \varepsilon^{\mathrm v,+}
                         =L^3(\varepsilon^{\mathrm v}+\delta\varepsilon_0^0).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-081-b4ac02ab03.dark.svg">
    <img src="../../../../assets/eq-081-b4ac02ab03.light.svg" alt="\mathscr E^+=\mathcal L\delta E_0^{\mathrm{det}}+E_0^*(m,0), \quad m^+=Lm,\quad \varepsilon^{\mathrm v,+} =L^3(\varepsilon^{\mathrm v}+\delta\varepsilon_0^0)." width="437">
  </picture>
</p>

In particular
$`0\le\varepsilon^{\mathrm v,+}-L^3\varepsilon^{\mathrm v} \le L^3q^7`$.
All maps commute with setting the external connection to zero.
The estimates are independent of the side and harmonic part, for
one primitive system satisfying the stated hypotheses. The theorem
asserts one step on the two admitted sides; it makes no assertion
that the outgoing datum lies in the next unit ball.
