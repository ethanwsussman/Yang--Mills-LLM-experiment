**Continuum existence (CE1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **CE1**.

- **[CEO1](CEO1.pdf)** — [Continuum limits from second-moment bounds](CEO1.pdf).
- **AI-written manuscript:** **[CEM1](CEM1.pdf)** — [Gaussian domination and structural properties of continuum limits](CEM1.pdf) · [TeX source](CEM1.tex).
- **Human-written manuscript:** to be added.

**Main statements**

The setting and principal theorems below are reproduced from **[CEM1](CEM1.pdf)**. Notation and numbered references follow that manuscript; references to other documents use their codenames.

Let $`\mathcal S=\mathcal S(\mathbb{R}^d;\mathbb{R}^r)`$ be the real Schwartz space
and $`\mathcal S'`$ its continuous dual. Write $`e_\alpha`$ for the
standard basis of $`\mathbb{R}^r`$. For the normalized real Hermite functions
$`h_k`$, $`k\in\mathbb{N}_0^d`$, set

<!-- display-math:eq-021-d4cf338b25
(1-\Delta+|y|^2)h_k=\lambda_k h_k,\qquad
 \lambda_k=2|k|_1+d+1,\qquad |k|_1=k_1+\cdots+k_d.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-021-d4cf338b25.dark.svg">
    <img src="../../../../assets/eq-021-d4cf338b25.light.svg" alt="(1-\Delta+|y|^2)h_k=\lambda_k h_k,\qquad \lambda_k=2|k|_1+d+1,\qquad |k|_1=k_1+\cdots+k_d." width="518">
  </picture>
</p>

For $`t>0`$ we use the separable Hilbert space

<!-- display-math:eq-022-bfa43a93ba
H_{-t}=\{F\in\mathcal S':\|F\|_{-t}<\infty\},\qquad
 \|F\|_{-t}^2=
 \sum_{\alpha=1}^r\sum_{k\in\mathbb{N}_0^d}
       \lambda_k^{-2t}|F(h_ke_\alpha)|^2.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-022-bfa43a93ba.dark.svg">
    <img src="../../../../assets/eq-022-bfa43a93ba.light.svg" alt="H_{-t}=\{F\in\mathcal S&#x27;:\|F\|_{-t}&lt;\infty\},\qquad \|F\|_{-t}^2= \sum_{\alpha=1}^r\sum_{k\in\mathbb{N}_0^d} \lambda_k^{-2t}|F(h_ke_\alpha)|^2." width="478">
  </picture>
</p>

All weak convergence of probability laws on this space refers to
its norm topology.

Extend each real distribution complex linearly to
$`\mathcal S_{\mathbb C}=\mathcal S(\mathbb{R}^d;\mathbb C^r)`$.
For a law $`P`$, its smeared $`n`$-point correlation is
$`S_n^P(f_1,\ldots,f_n)=\mathbb{E}_P\prod_{j=1}^n F(f_j)`$ whenever
this expectation exists.

**[Theorem A](CEM1.pdf) (Gaussian domination and convergence of correlations).**

Fix integers $`d,r\ge1`$ and a real number $`t>0`$. Let $`P_j`$ and $`P`$ be Borel probability
laws on $`H_{-t}`$ such that $`P_j\Longrightarrow P`$. Suppose

<!-- display-math:eq-023-fe6870479e
\mathbb{E}_{P_j}e^{F(f)}\le e^{\|f\|_2^2/2}
 \qquad(j\ge1,\ f\in\mathcal S).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-023-fe6870479e.dark.svg">
    <img src="../../../../assets/eq-023-fe6870479e.light.svg" alt="\mathbb{E}_{P_j}e^{F(f)}\le e^{\|f\|_2^2/2} \qquad(j\ge1,\ f\in\mathcal S)." width="263">
  </picture>
</p>

Then

<!-- display-math:eq-024-7f2fdaa92e
\mathbb{E}_P e^{F(f)}\le e^{\|f\|_2^2/2}
 \qquad(f\in\mathcal S).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-024-7f2fdaa92e.dark.svg">
    <img src="../../../../assets/eq-024-7f2fdaa92e.light.svg" alt="\mathbb{E}_P e^{F(f)}\le e^{\|f\|_2^2/2} \qquad(f\in\mathcal S)." width="213">
  </picture>
</p>

For every finite family $`f_1,\ldots,f_m\in\mathcal S_{\mathbb C}`$,
the functions

<!-- display-math:eq-025-7fe52c1fb2
Z_j(z)=\mathbb{E}_{P_j}\exp\left(\sum_{a=1}^m z_aF(f_a)\right),
 \qquad
 Z(z)=\mathbb{E}_P\exp\left(\sum_{a=1}^m z_aF(f_a)\right)
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-025-7fe52c1fb2.dark.svg">
    <img src="../../../../assets/eq-025-7fe52c1fb2.light.svg" alt="Z_j(z)=\mathbb{E}_{P_j}\exp\left(\sum_{a=1}^m z_aF(f_a)\right), \qquad Z(z)=\mathbb{E}_P\exp\left(\sum_{a=1}^m z_aF(f_a)\right)" width="473">
  </picture>
</p>

are entire on $`\mathbb C^m`$. They satisfy $`Z_j\to Z`$ locally
uniformly, with every complex derivative. In particular, for
every $`n\ge1`$ and $`f_1,\ldots,f_n\in\mathcal S_{\mathbb C}`$,

<!-- display-math:eq-026-0062473dbb
S_n^{P_j}(f_1,\ldots,f_n)\longrightarrow
 S_n^P(f_1,\ldots,f_n).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-026-0062473dbb.dark.svg">
    <img src="../../../../assets/eq-026-0062473dbb.light.svg" alt="S_n^{P_j}(f_1,\ldots,f_n)\longrightarrow S_n^P(f_1,\ldots,f_n)." width="251">
  </picture>
</p>

On the common domain

<!-- display-math:eq-027-764a0fa30a
D_f=\left\{z\in\mathbb C^m:
                 \sum_{a=1}^m|z_a|\|f_a\|_2<2/5\right\},
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-027-764a0fa30a.dark.svg">
    <img src="../../../../assets/eq-027-764a0fa30a.light.svg" alt="D_f=\left\{z\in\mathbb C^m: \sum_{a=1}^m|z_a|\|f_a\|_2&lt;2/5\right\}," width="277">
  </picture>
</p>

all $`Z_j`$ and $`Z`$ satisfy $`|Z_j-1|<1/2`$ and $`|Z-1|<1/2`$.
Their principal logarithms converge locally uniformly on $`D_f`$,
with every derivative. Thus all joint cumulants converge, where

<!-- display-math:eq-028-232b3ee118
\kappa_n^P(f_1,\ldots,f_n)
 =\left.\partial_{z_1}\cdots\partial_{z_n}
       \log\mathbb{E}_P\exp\left(\sum_{a=1}^n z_aF(f_a)\right)
   \right|_{z=0},
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-028-232b3ee118.dark.svg">
    <img src="../../../../assets/eq-028-232b3ee118.light.svg" alt="\kappa_n^P(f_1,\ldots,f_n) =\left.\partial_{z_1}\cdots\partial_{z_n} \log\mathbb{E}_P\exp\left(\sum_{a=1}^n z_aF(f_a)\right) \right|_{z=0}," width="405">
  </picture>
</p>

and $`\kappa_n^{P_j}`$ is defined in the same way.

**[Theorem B](CEM1.pdf) (Continuum limits of lattice fields).**

Fix integers $`d,r\ge1`$, offsets $`t_1,\ldots,t_r\in[0,1]^d`$,
and a set $`I\subset(0,1]`$ with $`0`$ in its closure. For each
$`a\in I`$, let $`\nu_a`$ be a Borel probability law on
$`\mathbb{R}^{\mathbb{Z}^d\times\{1,\ldots,r\}}`$ with the coordinate product
topology. Suppose there is a constant $`0\le C<\infty`$ such that

<!-- display-math:eq-029-66301abc28
\mathbb{E}_{\nu_a}\left|\sum_{\alpha,x}b_\alpha(x)u_\alpha(x)\right|^2
 \le C\sum_{\alpha,x}|b_\alpha(x)|^2
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-029-66301abc28.dark.svg">
    <img src="../../../../assets/eq-029-66301abc28.light.svg" alt="\mathbb{E}_{\nu_a}\left|\sum_{\alpha,x}b_\alpha(x)u_\alpha(x)\right|^2 \le C\sum_{\alpha,x}|b_\alpha(x)|^2" width="266">
  </picture>
</p>

for every $`a\in I`$ and every finitely supported real coefficient
array $`b`$. Define

<!-- display-math:eq-030-274d616518
(F_a)_\alpha(y)=a^{-d/2}u_\alpha(x)
 \quad\text{for }y\in Q_{a,\alpha,x}
 :=a\bigl(x+t_\alpha+[-1/2,1/2)^d\bigr).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-030-274d616518.dark.svg">
    <img src="../../../../assets/eq-030-274d616518.light.svg" alt="(F_a)_\alpha(y)=a^{-d/2}u_\alpha(x) \quad\text{for }y\in Q_{a,\alpha,x} :=a\bigl(x+t_\alpha+[-1/2,1/2)^d\bigr)." width="472">
  </picture>
</p>

Then $`F_a`$ is almost surely a real tempered distribution, and

<!-- display-math:eq-031-7941393065
\mathbb{E}_{\nu_a}|F_a(f)|^2\le C\|f\|_{L^2(\mathbb{R}^d;\mathbb{R}^r)}^2
 \qquad(f\in\mathcal S).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-031-7941393065.dark.svg">
    <img src="../../../../assets/eq-031-7941393065.light.svg" alt="\mathbb{E}_{\nu_a}|F_a(f)|^2\le C\|f\|_{L^2(\mathbb{R}^d;\mathbb{R}^r)}^2 \qquad(f\in\mathcal S)." width="284">
  </picture>
</p>

For every fixed $`t>d/2`$, these fields have Borel realizations in
$`H_{-t}`$ whose laws are uniformly tight. Consequently, for every
sequence $`a_j\in I`$ tending to zero there are a subsequence
$`a_{j_\ell}`$ and a Borel probability measure $`\mu`$ on $`H_{-t}`$
such that

<!-- display-math:eq-032-f884c549b2
\mathcal L(F_{a_{j_\ell}})\ \Longrightarrow\ \mu.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-032-f884c549b2.dark.svg">
    <img src="../../../../assets/eq-032-f884c549b2.light.svg" alt="\mathcal L(F_{a_{j_\ell}})\ \Longrightarrow\ \mu." width="115">
  </picture>
</p>

Along this subsequence the pairings with every finite family of
Schwartz tests converge jointly in distribution to their pairings
under $`\mu`$.

For the structural assertion, identify the component space $`\mathbb{R}^r`$ with a real inner-product space $`V`$, and let $`W`$ be another
finite-dimensional real inner-product space.
Fix an orthogonal representation $`\rho:O(d)\to O(V)`$.
For $`g(x)=Qx+b`$, use the actions

<!-- display-math:eq-033-b969e8456a
(g\cdot f)(x)=\rho(Q)f(Q^{-1}(x-b)),\qquad
 (g\cdot F)(f)=F(g^{-1}\cdot f).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-033-b969e8456a.dark.svg">
    <img src="../../../../assets/eq-033-b969e8456a.light.svg" alt="(g\cdot f)(x)=\rho(Q)f(Q^{-1}(x-b)),\qquad (g\cdot F)(f)=F(g^{-1}\cdot f)." width="421">
  </picture>
</p>

Invariance concerns the law as a random tempered distribution,
with the sigma-algebra generated by evaluations.
For an open set $`O`$, write $`\Sigma_O`$ for the sigma-algebra
generated by $`F(f)`$, $`f\in C_c^\infty(O;V)`$ real.
For an open half-space $`H^+`$ and an $`r`$-invariant law $`P`$,
where $`r`$ reflects in its
boundary, reflection positivity means

<!-- display-math:eq-034-67aa422441
\mathbb{E}_P[\overline{B(r\cdot F)}B(F)]\ge0
 \qquad\bigl(B\in L^2(\Sigma_{H^+},P)\bigr).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-034-67aa422441.dark.svg">
    <img src="../../../../assets/eq-034-67aa422441.light.svg" alt="\mathbb{E}_P[\overline{B(r\cdot F)}B(F)]\ge0 \qquad\bigl(B\in L^2(\Sigma_{H^+},P)\bigr)." width="322">
  </picture>
</p>

**[Theorem C](CEM1.pdf) (Identities, symmetries and reflection positivity).**

Let $`P_j\Rightarrow P`$ weakly on $`H_{-t}`$, and suppose

<!-- display-math:eq-035-36f7f4ffb2
\mathbb{E}_{P_j}e^{F(f)}\le e^{\|f\|_2^2/2}
 \qquad(j\ge1,\ f\in\mathcal S\text{ real}).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-035-36f7f4ffb2.dark.svg">
    <img src="../../../../assets/eq-035-36f7f4ffb2.light.svg" alt="\mathbb{E}_{P_j}e^{F(f)}\le e^{\|f\|_2^2/2} \qquad(j\ge1,\ f\in\mathcal S\text{ real})." width="293">
  </picture>
</p>

Let $`D^*:C_c^\infty(\mathbb{R}^d;W)\to\mathcal S`$ be continuous and
linear. Let $`\mathcal G`$ be a group of Euclidean isometries
containing all translations and a finite set $`\mathcal R`$ of
reflections through the origin. Choose an open side $`H_r^+`$ for
each $`r\in\mathcal R`$. Assume:

**(i)**

For each $`\xi\in C_c^\infty(\mathbb{R}^d;W)`$ there are real
$`v_j(\xi)\in\mathcal S`$ such that $`F(v_j(\xi))=0`$,
$`P_j`$-almost surely, and
$`\|v_j(\xi)-D^*\xi\|_2\to0`$.

**(ii)**

For each $`g\in\mathcal G`$ there are real linear maps
$`T_{j,g}:\mathcal S\to\mathcal S`$ satisfying

<!-- display-math:eq-036-d539ccfd98
\mathbb{E}_{P_j}e^{iF(T_{j,g}f)}=\mathbb{E}_{P_j}e^{iF(f)},\qquad
 \|T_{j,g}f-g\cdot f\|_2\longrightarrow0
 \quad(f\in\mathcal S).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-036-d539ccfd98.dark.svg">
    <img src="../../../../assets/eq-036-d539ccfd98.light.svg" alt="\mathbb{E}_{P_j}e^{iF(T_{j,g}f)}=\mathbb{E}_{P_j}e^{iF(f)},\qquad \|T_{j,g}f-g\cdot f\|_2\longrightarrow0 \quad(f\in\mathcal S)." width="423">
  </picture>
</p>

**(iii)**

For every $`r\in\mathcal R`$, every finite family of real
$`f_a\in C_c^\infty(H_r^+;V)`$, and every $`z_a\in\mathbb{C}`$,

<!-- display-math:eq-037-b59b194b66
\sum_{a,b}\overline z_a z_b
 \mathbb{E}_{P_j}e^{iF(f_b-r\cdot f_a)}\ge0
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-037-b59b194b66.dark.svg">
    <img src="../../../../assets/eq-037-b59b194b66.light.svg" alt="\sum_{a,b}\overline z_a z_b \mathbb{E}_{P_j}e^{iF(f_b-r\cdot f_a)}\ge0" width="184">
  </picture>
</p>

for all sufficiently large $`j`$, depending on the family.

Then $`P`$ satisfies $`\mathbb{E}_Pe^{F(f)}\le e^{\|f\|_2^2/2}`$
for every real $`f\in\mathcal S`$, is
$`\mathcal G`$-invariant, and almost every $`F`$ satisfies
$`F(D^*\xi)=0`$ simultaneously for all $`\xi`$.
The law is reflection invariant and reflection positive at every
translate of every plane in $`\mathcal R`$.
Along the same sequence, all joint moments and cumulants of every
fixed finite family of Schwartz evaluations converge to those of $`P`$.

[CEO1](CEO1.pdf) covers compactness only. The current compact-link IVM1 is not the real-curvature input. The selected common bare sequence is required in the QED3 application.
