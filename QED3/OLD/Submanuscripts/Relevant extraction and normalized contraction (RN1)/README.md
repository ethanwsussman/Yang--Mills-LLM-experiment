**Relevant extraction and normalized contraction (RN1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **RN1**.

- **[RNO1](RNO1.pdf)** — [Relevant extraction and contraction of local interactions](RNO1.pdf).
- **AI-written manuscript:** **[RNM1](RNM1.pdf)** — [Relevant extraction and contraction of local interactions](RNM1.pdf) · [TeX source](RNM1.tex).
- **Human-written manuscript:** to be added.

**Main statements**

The setting and principal theorem below are reproduced from **[RNM1](RNM1.pdf)**. Notation and numbered references follow that manuscript; references to other documents use their codenames. The referenced activity spaces, maps and imported hypotheses remain part of the statement.

Let $`L\ge5`$ be odd, let $`M=L^m`$ with $`m\in\mathbb{Z}_{\ge2}`$, and put
$`\eta_k=L^{-k}`$, $`k\in\mathbb{Z}_{\ge0}`$. We use the photon torus
$`\eta_k\mathbb{Z}^3/\ell\mathbb{Z}^3`$ and its chamber sites $`(c,g)`$, where $`g`$
is one of the $`48`$ signed permutation matrices. Spinors have four
components and are antiperiodic in each coordinate. A polymer is a
face-connected union of the partition $`M`$-cubes. Its size parameter
$`Md_M(X)`$ is the infimum of the lengths of connected finite nets
meeting every cube of $`X`$; it is called small if $`d_M(X)\le L`$.
The net convention and its estimates are given in
[Appendix B](RNM1.pdf).

An activity is a family of Grassmann polynomials in independent
ordinary generators $`\psi,\bar\psi`$ and ordered-pair generators
$`\chi,\bar\chi`$. The latter represent covariant Hölder differences
only when the fields are evaluated. We work with the space
$`K_k^{x,\mathbb{C}}(\ell)`$ defined in
[Section 2](RNM1.pdf): its families are balanced, holomorphic
on $`\widetilde R_k\times\mathfrak X_k`$, local in the stated
ordinary and pair indices and in the connection bonds, and covariant
under the specified lattice, independent real-gauge and charge
actions. The real subspace $`K_k^x`$ satisfies the additional
antilinear identity there. The two generator weights and family norm are

<!-- display-math:eq-115-8e93bf6797
h_{k,1}=e_k^{-1/4},\qquad h_{k,2}=e_k^{-1/4+\varepsilon},\qquad
 \|\mathscr E\|_k^x
 =\sup_X e^{\kappa d_M(X)}
   \sup_{\widetilde R_k\times\mathfrak X_k}
                 \|\mathscr E(X)\|_{h_k}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-115-8e93bf6797.dark.svg">
    <img src="../../../../assets/eq-115-8e93bf6797.light.svg" alt="h_{k,1}=e_k^{-1/4},\qquad h_{k,2}=e_k^{-1/4+\varepsilon},\qquad \|\mathscr E\|_k^x =\sup_X e^{\kappa d_M(X)} \sup_{\widetilde R_k\times\mathfrak X_k} \|\mathscr E(X)\|_{h_k}." width="507">
  </picture>
</p>

Here $`0<e_k<1`$; the weighted coefficient norm and the two
connection domains are specified in
[(5)](RNM1.pdf) and
[(3)](RNM1.pdf). There is no smallness assumption
on the activity in the following linear theorem.

Set

<!-- display-math:eq-116-c6c3720168
\bar\varepsilon=\frac1{200},\quad c_X=54,\quad
 \kappa_0=54\log72,\quad K_0=\frac{e^{\kappa_0}}{36},\quad
 c_{\mathrm{rb}}=c_XK_0,\quad c_{\mathrm{fl}}=61c_{\mathrm{rb}}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-116-c6c3720168.dark.svg">
    <img src="../../../../assets/eq-116-c6c3720168.light.svg" alt="\bar\varepsilon=\frac1{200},\quad c_X=54,\quad \kappa_0=54\log72,\quad K_0=\frac{e^{\kappa_0}}{36},\quad c_{\mathrm{rb}}=c_XK_0,\quad c_{\mathrm{fl}}=61c_{\mathrm{rb}}." width="558">
  </picture>
</p>

**[Theorem A](RNM1.pdf) (Extraction and normalized contraction).**

Assume that both $`\ell/(LM)`$ and $`\ell/(L^2M)`$ are odd
integers at least $`13`$. Suppose

<!-- display-math:eq-117-12b9af66c6
\begin{gathered}
 0<\varepsilon\le\bar\varepsilon,\qquad 1-\varepsilon<\alpha<1,
 \qquad L^{1/8-3\bar\varepsilon/2}\ge2400,\qquad e_k^\varepsilon\le1/4,\\[0pt]
 160L^{1+3\varepsilon/2}Me_k^\varepsilon\le1,\qquad
 9ML^\varepsilon e_k^{2\varepsilon}\le1,\qquad
 90c_XLMe_k^\varepsilon\le1,
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-117-12b9af66c6.dark.svg">
    <img src="../../../../assets/eq-117-12b9af66c6.light.svg" alt="\begin{gathered} 0&lt;\varepsilon\le\bar\varepsilon,\qquad 1-\varepsilon&lt;\alpha&lt;1, \qquad L^{1/8-3\bar\varepsilon/2}\ge2400,\qquad e_k^\varepsilon\le1/4,\\[0pt] 160L^{1+3\varepsilon/2}Me_k^\varepsilon\le1,\qquad 9ML^\varepsilon e_k^{2\varepsilon}\le1,\qquad 90c_XLMe_k^\varepsilon\le1, \end{gathered}" width="465">
  </picture>
</p>

and

<!-- display-math:eq-118-6775e9bcae
\kappa\ge7\kappa_0+7,\qquad
 L(\kappa-6\kappa_0-4)-1\ge\kappa.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-118-6775e9bcae.dark.svg">
    <img src="../../../../assets/eq-118-6775e9bcae.light.svg" alt="\kappa\ge7\kappa_0+7,\qquad L(\kappa-6\kappa_0-4)-1\ge\kappa." width="296">
  </picture>
</p>

Let $`\mathscr E\in K_k^{x,\mathbb{C}}(\ell)`$ and
$`e_{k+1}=L^{1/2}e_k`$.

**(i)**  There are complex-linear vacuum and mass maps, real on
$`K_k^x`$, with

<!-- display-math:eq-119-8c9df07089
|\varepsilon_{\mathrm v}(\mathscr E)|
       \le K_0M^{-3}\|\mathscr E\|_k^x,\qquad
 |m(\mathscr E)|
       \le K_0M^{-3}e_k^{1/2}\|\mathscr E\|_k^x .
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-119-8c9df07089.dark.svg">
    <img src="../../../../assets/eq-119-8c9df07089.light.svg" alt="|\varepsilon_{\mathrm v}(\mathscr E)| \le K_0M^{-3}\|\mathscr E\|_k^x,\qquad |m(\mathscr E)| \le K_0M^{-3}e_k^{1/2}\|\mathscr E\|_k^x ." width="394">
  </picture>
</p>

The extracted mass matrix is $`m(\mathscr E)1_4`$.
The local subtraction $`R`$ of [(17)](RNM1.pdf)
satisfies $`\|R\mathscr E\|_k^x\le2\|\mathscr E\|_k^x`$ and the
exact independent-generator identity

<!-- display-math:eq-120-0f84a221aa
\sum_X\mathscr E(X)
 =-\varepsilon_{\mathrm v}(\mathscr E)\ell^3
       -m(\mathscr E)\langle\bar\psi,\psi\rangle
       +\sum_X(R\mathscr E)(X).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-120-0f84a221aa.dark.svg">
    <img src="../../../../assets/eq-120-0f84a221aa.light.svg" alt="\sum_X\mathscr E(X) =-\varepsilon_{\mathrm v}(\mathscr E)\ell^3 -m(\mathscr E)\langle\bar\psi,\psi\rangle +\sum_X(R\mathscr E)(X)." width="365">
  </picture>
</p>

On a small polymer its zero-field vacuum kernel and the integral
of its zero-field ordinary quadratic kernel vanish.

**(ii)**  The shortest-chain adjustment of
[(23)](RNM1.pdf) gives
$`E=(R\mathscr E)^{\mathrm{nat}}\in K_k^{x,\mathbb{C}}(\ell)`$, with
$`\|E\|_k^x\le20\|\mathscr E\|_k^x`$. It leaves the evaluated
value of $`R\mathscr E`$ unchanged whenever
$`\chi=\delta_{\alpha,\mathscr A+\mathscr C}\psi`$ and
$`\bar\chi=\delta_{\alpha,-(\mathscr A+\mathscr C)}\bar\psi`$.
On every small polymer it has the stronger normalization

<!-- display-math:eq-121-02b74ae9ed
E_{00}(X;0,0)=0,\qquad E_{20}(X;0,0;\cdot,\cdot)=0
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-121-02b74ae9ed.dark.svg">
    <img src="../../../../assets/eq-121-02b74ae9ed.light.svg" alt="E_{00}(X;0,0)=0,\qquad E_{20}(X;0,0;\cdot,\cdot)=0" width="291">
  </picture>
</p>

as full antisymmetric kernels. Both subtraction and adjustment
leave large-polymer activities unchanged.

**(iii)**  Scale connections by
$`A_L(b)=L^{-1/2}A(b/L)`$, ordinary generators by $`L^{-1}`$,
and pair generators by $`L^{-1-\alpha}`$.
Let $`\bar X^L`$ be the union of $`LM`$-cubes containing $`X`$, and set

<!-- display-math:eq-122-ffd8ab8139
(\mathcal LE)(Y;\mathscr A,\mathscr C)
       =\sum_{\bar X^L=LY}S_LE(X;\mathscr A_L,\mathscr C_L).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-122-ffd8ab8139.dark.svg">
    <img src="../../../../assets/eq-122-ffd8ab8139.light.svg" alt="(\mathcal LE)(Y;\mathscr A,\mathscr C) =\sum_{\bar X^L=LY}S_LE(X;\mathscr A_L,\mathscr C_L)." width="296">
  </picture>
</p>

Then $`\mathscr E\mapsto\mathcal L(R\mathscr E)^{\mathrm{nat}}`$
is a linear map into $`K_{k+1}^{x,\mathbb{C}}(\ell/L)`$ and

<!-- display-math:eq-123-0c85ce4de3
\|\mathcal LE\|_{k+1}^x
       \le c_{\mathrm{fl}}L^{-1/4+3\varepsilon/2}\|\mathscr E\|_k^x.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-123-0c85ce4de3.dark.svg">
    <img src="../../../../assets/eq-123-0c85ce4de3.light.svg" alt="\|\mathcal LE\|_{k+1}^x \le c_{\mathrm{fl}}L^{-1/4+3\varepsilon/2}\|\mathscr E\|_k^x." width="214">
  </picture>
</p>

For $`w_j^{\mathrm E}=e_j^{1/4-7\varepsilon}`$, the relative estimate is

<!-- display-math:eq-124-0cf832d897
\frac{\|\mathcal LE\|_{k+1}^x}{w_{k+1}^{\mathrm E}}
 \le c_{\mathrm{fl}}L^{-3/8+11\varepsilon/2}
                 \frac{\|\mathscr E\|_k^x}{w_k^{\mathrm E}}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-124-0cf832d897.dark.svg">
    <img src="../../../../assets/eq-124-0cf832d897.light.svg" alt="\frac{\|\mathcal LE\|_{k+1}^x}{w_{k+1}^{\mathrm E}} \le c_{\mathrm{fl}}L^{-3/8+11\varepsilon/2} \frac{\|\mathscr E\|_k^x}{w_k^{\mathrm E}}." width="234">
  </picture>
</p>

Its factor is at most $`1/16`$ if, in addition,
$`c_{\mathrm{fl}}L^{-3/8+6\bar\varepsilon}\le1/16`$.

All the stated maps preserve the real subspaces and commute with
setting the second connection argument to zero.

[Theorem B](RNM1.pdf) of [RNM1](RNM1.pdf) ([Section 7](RNM1.pdf), “Local reconstruction of a mean field”) gives local reconstruction under its separate hypotheses; the final mean-field recovery clause additionally requires the stated fine inverses.
