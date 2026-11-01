**Infinite-lattice reflection positivity (LP1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **LP1**.

- **[LPO1](LPO1.pdf)** — [Reflection positivity on the infinite lattice: expanded proof outline](LPO1.pdf).
- **AI-written manuscript:** **[LPM1](LPM1.pdf)** — [Reflection positivity for chamber QED on the infinite lattice](LPM1.pdf) · [TeX source](LPM1.tex).
- **Human-written manuscript:** to be added.

**Main theorem**

The statement and setting below are reproduced from the introduction of **[LPM1](LPM1.pdf)**, with TeX macros and formatting adapted for GitHub.

We fix the lattice spacing and use unit lattice coordinates. The photon
field is a real one-cochain on $`\mathbb{Z}^3`$. Write $`d`$ for the lattice
coboundary, orient a plaquette by the ordered pair $`(e_j,e_k)`$, $`j<k`$,
and let $`\mathcal P_2`$ contain the plaquettes with these orientations.
The space in which the volume limit is taken is

<!-- display-math:eq-048-d91e313ae7
\Omega=\{F\in\mathbb{R}^{\mathcal P_2}:dF=0\},
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-048-d91e313ae7.dark.svg">
    <img src="../../../../assets/eq-048-d91e313ae7.light.svg" alt="\Omega=\{F\in\mathbb{R}^{\mathcal P_2}:dF=0\}," width="182">
  </picture>
</p>

with the product topology. Reversing a plaquette's orientation negates
its field value. In particular, pullback by a lattice isometry acts on
$`F`$ as a two-cochain, including the orientation sign.

Here is the finite model. Let
$`W=\mathbb{Z}^3\rtimes\bigl(O(3)\cap\mathrm{GL}(3,\mathbb{Z})\bigr)`$ and
$`C_0=\{0<x_3<x_2<x_1<1/2\}`$. Fix $`v_0\in C_0`$, and let
$`s_0,s_1,s_2,s_3`$ be the reflections in its walls
$`x_3=0`$, $`x_2=x_3`$, $`x_1=x_2`$, $`x_1=1/2`$, respectively.
The fermion sites are $`\mathcal X=Wv_0`$, and the four neighbours
of $`x=gv_0`$ are $`x^{(i)}=gs_iv_0`$. Write $`\pi(x)`$ for the nearest
point of $`\mathbb{Z}^3`$ to $`x`$. With $`\gamma_j=\mathrm{diag}(\sigma_j,-\sigma_j)`$,
where $`\sigma_j`$ are the Pauli matrices, put $`\gamma_v=\sum_jv_j\gamma_j`$.
For charge $`q`$, Wilson parameter $`\rho`$, weights $`w_i`$, and mass
parameter $`M`$, the chamber operator is

<!-- display-math:eq-049-093157b5d0
(\mathcal D_A\psi)(x)
 =M\psi(x)-\sum_{i=0}^3\frac{w_i}{2}
   \left(\rho-\gamma_{(x^{(i)}-x)/|x^{(i)}-x|}\right)
   e^{iqA(\pi(x),\pi(x^{(i)}))}\psi(x^{(i)}),
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-049-093157b5d0.dark.svg">
    <img src="../../../../assets/eq-049-093157b5d0.light.svg" alt="(\mathcal D_A\psi)(x) =M\psi(x)-\sum_{i=0}^3\frac{w_i}{2} \left(\rho-\gamma_{(x^{(i)}-x)/|x^{(i)}-x|}\right) e^{iqA(\pi(x),\pi(x^{(i)}))}\psi(x^{(i)})," width="493">
  </picture>
</p>

where $`A(y,x)=-A(x,y)`$ and $`A(x,x)=0`$.

On the cubic torus $`(\mathbb{Z}/n\mathbb{Z})^3`$, the photons are periodic and
$`\mathcal D_A^{C(n)}`$ acts on spinors satisfying
$`\psi(x+ne_j)=-\psi(x)`$ for $`j=1,2,3`$. Put $`r_q=2\pi/q`$.
For a bounded Borel function $`G`$ on $`\Omega`$, define

<!-- display-math:eq-050-c9fc9bcf4f
\mu_n(G)=\frac1{Z_{C(n)}[1]}
 \sum_{\substack{z\in C^2((\mathbb{Z}/n\mathbb{Z})^3;\mathbb{Z})\\dz=0}}
 \int_{[0,r_q)^{3n^3}}
 G(\widetilde F)\,e^{-\|F\|^2/2}
       \det\mathcal D_A^{C(n)}\,\mathrm{d} A,
 \qquad F=dA+r_qz.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-050-c9fc9bcf4f.dark.svg">
    <img src="../../../../assets/eq-050-c9fc9bcf4f.light.svg" alt="\mu_n(G)=\frac1{Z_{C(n)}[1]} \sum_{\substack{z\in C^2((\mathbb{Z}/n\mathbb{Z})^3;\mathbb{Z})\\dz=0}} \int_{[0,r_q)^{3n^3}} G(\widetilde F)\,e^{-\|F\|^2/2} \det\mathcal D_A^{C(n)}\,\mathrm{d} A, \qquad F=dA+r_qz." width="600">
  </picture>
</p>

Here $`\widetilde F`$ is the periodic extension of $`F`$, the norm sums
over the torus plaquettes, and $`Z_{C(n)}[1]`$ is the same expression
without $`G`$. Thus every closed integer cochain is summed, with no
restriction on its flux.

**[Theorem A](LPM1.pdf) (Reflection positivity in infinite volume).**

Fix $`q>0`$, $`0<\rho<1`$, $`M\in\mathbb{R}`$ and $`w_0,\ldots,w_3>0`$.
The family $`(\mu_n)_{n\ge4}`$ is tight on $`\Omega`$. Let
$`n_i\ge4`$ be any sequence of integers tending to infinity, and let
$`\nu`$ be any subsequential weak limit of $`(\mu_{n_i})`$. Then:

**(i)** For every finitely supported real two-cochain $`\beta`$,

<!-- display-math:eq-051-cce45913ee
\int_\Omega e^{\langle\beta,F\rangle}\,\mathrm{d}\nu(F)
       \le e^{\|\beta\|^2/2},
 \qquad
 \langle\beta,F\rangle=\sum_{\sigma\in\mathcal P_2}\beta_\sigma F_\sigma,
 \qquad \|\beta\|^2=\sum_{\sigma\in\mathcal P_2}\beta_\sigma^2.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-051-cce45913ee.dark.svg">
    <img src="../../../../assets/eq-051-cce45913ee.light.svg" alt="\int_\Omega e^{\langle\beta,F\rangle}\,\mathrm{d}\nu(F) \le e^{\|\beta\|^2/2}, \qquad \langle\beta,F\rangle=\sum_{\sigma\in\mathcal P_2}\beta_\sigma F_\sigma, \qquad \|\beta\|^2=\sum_{\sigma\in\mathcal P_2}\beta_\sigma^2." width="482">
  </picture>
</p>

**(ii)** The law $`\nu`$ is invariant under lattice translations,
signed coordinate permutations, and $`F\mapsto-F`$.

**(iii)** The law $`\nu`$ is invariant and reflection positive
at every mirror

<!-- display-math:eq-052-f1a0de3590
x_j=c\quad(c\in\tfrac12\mathbb{Z}),\qquad
 x_j\pm x_k=c\quad(c\in\mathbb{Z},\ j<k).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-052-f1a0de3590.dark.svg">
    <img src="../../../../assets/eq-052-f1a0de3590.light.svg" alt="x_j=c\quad(c\in\tfrac12\mathbb{Z}),\qquad x_j\pm x_k=c\quad(c\in\mathbb{Z},\ j&lt;k)." width="366">
  </picture>
</p>

More precisely, write a mirror as $`\Pi=\{\ell(x)=c\}`$ and let

<!-- display-math:eq-053-f3e98c0268
\theta_\Pi x
 =x-\frac{2(\ell(x)-c)}{|\nabla\ell|^2}\nabla\ell.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-053-f3e98c0268.dark.svg">
    <img src="../../../../assets/eq-053-f3e98c0268.light.svg" alt="\theta_\Pi x =x-\frac{2(\ell(x)-c)}{|\nabla\ell|^2}\nabla\ell." width="192">
  </picture>
</p>

Choose either open side $`H`$ of $`\Pi`$, and let $`\Sigma_H`$ be the
sigma-algebra generated by the values $`F_\sigma`$ for which every
corner of $`\sigma`$ lies in $`H`$. Then

<!-- display-math:eq-054-2e8d27235f
\int_\Omega\overline{A(\theta_\Pi^*F)}A(F)\,\mathrm{d}\nu(F)\ge0
 \qquad\bigl(A\in L^2(\Sigma_H,\nu)\bigr).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-054-2e8d27235f.dark.svg">
    <img src="../../../../assets/eq-054-2e8d27235f.light.svg" alt="\int_\Omega\overline{A(\theta_\Pi^*F)}A(F)\,\mathrm{d}\nu(F)\ge0 \qquad\bigl(A\in L^2(\Sigma_H,\nu)\bigr)." width="345">
  </picture>
</p>

There are three coordinate and six diagonal mirror families in
(iii). The support convention excludes plaquettes on or
crossing the mirror. For example, reflection in $`x_1=0`$ changes the
signs of $`F_{12}`$ and $`F_{13}`$ and preserves the sign of $`F_{23}`$.
These signs occur both in invariance of the law and in its reflected
form.

The coordinate construction used by the outline is proved in [LPM1, Section 5.3](LPM1.pdf), following [Proposition 5.1](LPM1.pdf).
