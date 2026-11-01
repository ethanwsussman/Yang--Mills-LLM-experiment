**Reference response (RR1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **RR1**.

- **[RRO1](RRO1.pdf)** — [Exact sources and normalized reference response](RRO1.pdf).
- **AI-written manuscript:** **[RRM1](RRM1.pdf)** — [Exact source identities and normalized reference response for lattice QED in three dimensions](RRM1.pdf) · [TeX source](RRM1.tex).
- **Human-written manuscript:** to be added.

**Principal statements**

Notation and numbered references below follow **[RRM1](RRM1.pdf)**. The imported construction and estimates are part of the hypotheses.

**Setting**

We use the chamber regulator with weights $`(6,6\sqrt2,6\sqrt2,6)`$ and Wilson parameter $`0<\rho<1`$. The operator $`D^{\rm ch}[B]`$ acts on four-component spinors with $`48`$ chamber labels per site, antiperiodic in every coordinate; its argument $`B`$ is the bond phase. The stencil is recalled in [Section 1.1](RRM1.pdf).

Fix the block construction of (**[QEM1](../../QEM1.pdf)**, [Proposition 4.1](../../QEM1.pdf) and [Section 4.1–4.4](../../QEM1.pdf)), with its positive charge ceilings $`e_1\le e_0<1`$ and the common-pair theorem (**[CVM1](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)**, [Theorem D](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)). Thus $`L\ge13`$ is odd, $`M=L^m`$ with $`m\in\mathbb{Z}_{\ge2}`$, $`0<\alpha<1`$, $`1-\alpha<\varepsilon\le1/200`$, and the localization and cutoff powers are $`r_{\rm loc}=2`$, $`p_0=9`$, $`p=19`$. The fixed ceilings denoted by $`e_0,e_1`$ here are the $`\bar e_0,\bar e_1`$ of (**[QEM1](../../QEM1.pdf)**); they are distinct from the running charge $`e_j`$ at $`j=0`$. These fixed constants include the photon and fermion inverse bounds, the exact block step and the terminal conditions. The parameter input is [Proposition 4.1](../../QEM1.pdf) of (**[QEM1](../../QEM1.pdf)**), which supplies the construction and charge ceilings before any probe-dependent restriction. The response estimates are proved here.

For $`0<\bar m\le1`$ put

<!-- display-math:eq-095-73586fe3c8
h=L^{\lfloor\log_L\bar m^{-1}\rfloor},\qquad
 \eta=L^{-N},\qquad q=e\sqrt\eta,\qquad K=N+\log_Lh.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-095-73586fe3c8.dark.svg">
    <img src="../../../../assets/eq-095-73586fe3c8.light.svg" alt="h=L^{\lfloor\log_L\bar m^{-1}\rfloor},\qquad \eta=L^{-N},\qquad q=e\sqrt\eta,\qquad K=N+\log_Lh." width="456">
  </picture>
</p>

Let $`r_K`$ be the least nonnegative integer power of $`L`$ at least $`[-\log(e\sqrt h)]^2`$, and set

<!-- display-math:eq-096-a09fa32640
R_{\rm top}=hMr_K,\qquad R^*=R_{\rm top}/L,\qquad
 n_*=R^*/\eta,\qquad \ell_c=R^*/(2L),\qquad N_*=8L^3.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-096-a09fa32640.dark.svg">
    <img src="../../../../assets/eq-096-a09fa32640.light.svg" alt="R_{\rm top}=hMr_K,\qquad R^*=R_{\rm top}/L,\qquad n_*=R^*/\eta,\qquad \ell_c=R^*/(2L),\qquad N_*=8L^3." width="587">
  </picture>
</p>

The finite threshold $`N_{\rm ref}(e)`$ and stopping level on $`R^*`$ are those of (**[CVM1](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)**, [Proposition 6.1](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf) and [(53)](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)). For $`N\ge N_{\rm ref}(e)`$ use the real pair $`P_N(e)=(m_{0,N},\varepsilon_{0,N}^{\rm v})`$ selected on $`R_{\rm top}`$ by (**[CVM1](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)**, [Theorem D](../Cover%20agreement%20and%20common%20tuning%20%28CV1%29/CVM1.pdf)), and write $`\boldsymbol\mu_N=\bar m\eta+m_{0,N}`$. This same pair is used for every source and every twist. Its vacuum factor cancels from the normalized response below.

Fix a real nonzero $`\beta\in C_c^\infty(\mathbb{R}^3;\Lambda^2)`$, put $`f=dd^*\beta`$, and let $`D_\beta`$ be the side of a least coordinate cube containing $`\mathrm{supp}\beta`$. Enlarge that cube by two in each direction to obtain $`Q_\beta`$ of side $`D_\beta^{\rm buf}=D_\beta+4`$ and center $`z_\beta`$. With $`J_\eta`$ denoting cube averaging and $`\delta_{\eta,\mu}`$ the centered difference, define the covering bond cochain

<!-- display-math:eq-097-709c8c6e1f
\widehat a^o_\nu(x)=
 -\eta^{1/2}\sum_{\mu\ne\nu}
 (\delta_{\eta,\mu}J_\eta\beta_{\mu\nu})
                         (\eta x+\eta e_\nu/2).
\tag{1}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-097-709c8c6e1f.dark.svg">
    <img src="../../../../assets/eq-097-709c8c6e1f.light.svg" alt="\widehat a^o_\nu(x)= -\eta^{1/2}\sum_{\mu\ne\nu} (\delta_{\eta,\mu}J_\eta\beta_{\mu\nu}) (\eta x+\eta e_\nu/2). \tag{1}" width="366">
  </picture>
</p>

A placement $`v\in\eta\mathbb{Z}^3`$ is admitted when $`v+Q_\beta\subset[\ell_c/8,7\ell_c/8]^3`$. Translate the probe by $`v`$, reflect it into the cells indexed by $`\mathcal C_*=(\mathbb{Z}/2L\mathbb{Z})^3`$, and periodize on $`C(n_*)`$. The resulting cochains are $`\widehat a_c`$; the reflection maps and their orientation action are specified in [Section 2](RRM1.pdf). They have mutually orthogonal curvatures, all of squared norm $`v_\eta=\|d\widehat a^o\|_{\ell^2}^2`$.

Write $`C(n_*)=\mathbb{Z}^3/n_*\mathbb{Z}^3`$ with its oriented cubical cells. Let $`\gamma_{n_*}`$ be the standard Gaussian on its exact real two-cochains, with counting inner product. For such a curvature $`u`$, let $`A(u)`$ be its mean-zero transverse potential. Set $`H_{\theta,\nu}=\theta_\nu/(qn_*)`$ and $`a(t)=e^{-1}\sum_ct_c\widehat a_c`$. Define

<!-- display-math:eq-098-b07fb3269a
\mathring\Phi(t)=
 \frac{\displaystyle\int_{[-\pi,\pi]^3}\frac{\mathrm{d}\theta}{(2\pi)^3}
       \int\det\bigl(D^{\rm ch}[q(A(u)+H_\theta+a(t))]
                         +\boldsymbol\mu_N\bigr)\,\mathrm{d}\gamma_{n_*}(u)}
      {\displaystyle\int_{[-\pi,\pi]^3}\frac{\mathrm{d}\theta}{(2\pi)^3}
       \int\det\bigl(D^{\rm ch}[q(A(u)+H_\theta)]
                         +\boldsymbol\mu_N\bigr)\,\mathrm{d}\gamma_{n_*}(u)}.
\tag{2}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-098-b07fb3269a.dark.svg">
    <img src="../../../../assets/eq-098-b07fb3269a.light.svg" alt="\mathring\Phi(t)= \frac{\displaystyle\int_{[-\pi,\pi]^3}\frac{\mathrm{d}\theta}{(2\pi)^3} \int\det\bigl(D^{\rm ch}[q(A(u)+H_\theta+a(t))] +\boldsymbol\mu_N\bigr)\,\mathrm{d}\gamma_{n_*}(u)} {\displaystyle\int_{[-\pi,\pi]^3}\frac{\mathrm{d}\theta}{(2\pi)^3} \int\det\bigl(D^{\rm ch}[q(A(u)+H_\theta)] +\boldsymbol\mu_N\bigr)\,\mathrm{d}\gamma_{n_*}(u)}. \tag{2}" width="558">
  </picture>
</p>

The denominator is positive, including when the tuned total mass has either sign. The free one-cell ratio uses the positive reference mass:

<!-- display-math:eq-099-6c29b79b33
N_0(t)=\frac{\det\bigl(D^{\rm ch}[q(t/e)\widehat a_0]
                                      +\bar m\eta\bigr)}
                   {\det\bigl(D^{\rm ch}[0]+\bar m\eta\bigr)},
 \qquad c_m=N_0^{(m)}(0),\quad m=2,4.
\tag{3}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-099-6c29b79b33.dark.svg">
    <img src="../../../../assets/eq-099-6c29b79b33.light.svg" alt="N_0(t)=\frac{\det\bigl(D^{\rm ch}[q(t/e)\widehat a_0] +\bar m\eta\bigr)} {\det\bigl(D^{\rm ch}[0]+\bar m\eta\bigr)}, \qquad c_m=N_0^{(m)}(0),\quad m=2,4. \tag{3}" width="531">
  </picture>
</p>

These are ordinary derivatives of the ratio. Put

<!-- display-math:eq-100-fd8e82eff9
\Theta_m^{(0)}=
 \left|\left[\prod_{c\in\mathcal C_*}
           (\partial_{t_c}^m-c_m)\right]\mathring\Phi(0)
                                      \right|^{1/N_*},\qquad
 \mathfrak e=\tfrac12(1/4-9\varepsilon)-12\varepsilon>0.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-100-fd8e82eff9.dark.svg">
    <img src="../../../../assets/eq-100-fd8e82eff9.light.svg" alt="\Theta_m^{(0)}= \left|\left[\prod_{c\in\mathcal C_*} (\partial_{t_c}^m-c_m)\right]\mathring\Phi(0) \right|^{1/N_*},\qquad \mathfrak e=\tfrac12(1/4-9\varepsilon)-12\varepsilon&gt;0." width="469">
  </picture>
</p>

**Regulator and elementary conventions**

Let $`\sigma_\mu`$ be the Pauli matrices and $`\gamma_\mu=\sigma_3\otimes\sigma_\mu`$. The labels $`g\in O_{\rm cub}=O(3)\cap\mathrm{GL}(3,\mathbb{Z})`$ are the signed permutation matrices. Let $`s_0`$ reverse coordinate three, $`s_1,s_2`$ exchange $`(2,3)`$ and $`(1,2)`$, and let $`r_{e_1}`$ reverse coordinate one. Put

<!-- display-math:eq-101-5483fd7e18
n_0=e_3,\quad n_1=(e_2-e_3)/\sqrt2,\quad
 n_2=(e_1-e_2)/\sqrt2,\quad n_3=-e_1,\qquad
 M_i(g)=\tfrac12w_i(\rho+\gamma\cdot gn_i).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-101-5483fd7e18.dark.svg">
    <img src="../../../../assets/eq-101-5483fd7e18.light.svg" alt="n_0=e_3,\quad n_1=(e_2-e_3)/\sqrt2,\quad n_2=(e_1-e_2)/\sqrt2,\quad n_3=-e_1,\qquad M_i(g)=\tfrac12w_i(\rho+\gamma\cdot gn_i)." width="670">
  </picture>
</p>

On a unit torus the chamber operator is

<!-- display-math:eq-102-7d60e13fb1
\begin{split}
 (D^{\rm ch}[B]\psi)(c,g)={}&
 \sum_{i=0}^2M_i(g)\bigl(\psi(c,g)-\psi(c,gs_i)\bigr)\\[0pt]
 &+M_3(g)\bigl(\psi(c,g)
       -\mathrm e^{iB(c,c+ge_1)}\psi(c+ge_1,gr_{e_1})\bigr).
 \end{split}
\tag{6}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-102-7d60e13fb1.dark.svg">
    <img src="../../../../assets/eq-102-7d60e13fb1.light.svg" alt="\begin{split} (D^{\rm ch}[B]\psi)(c,g)={}&amp; \sum_{i=0}^2M_i(g)\bigl(\psi(c,g)-\psi(c,gs_i)\bigr)\\[0pt] &amp;+M_3(g)\bigl(\psi(c,g) -\mathrm e^{iB(c,c+ge_1)}\psi(c+ge_1,gr_{e_1})\bigr). \end{split} \tag{6}" width="518">
  </picture>
</p>

Reversed bonds carry the negative cochain value. We write $`D_A=D^{\rm ch}[qA]`$ in the unit-lattice source identities. At mesh $`\eta_j`$, the external hop and the bond phase have the corresponding factors $`\eta_j^{-1}`$ and $`e_j\eta_j`$. The spinor pairing has weight $`1/48`$ per chamber label; its constant weight does not change a finite-dimensional determinant.

For smooth functions,

<!-- display-math:eq-103-f32840df14
J_\eta v(y)=\eta^{-3}\int_{[-\eta/2,\eta/2]^3}v(y+z)\,\mathrm{d} z,
 \qquad
 \delta_{\eta,\mu}v(y)=
 \frac{v(y+\eta e_\mu/2)-v(y-\eta e_\mu/2)}{\eta}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-103-f32840df14.dark.svg">
    <img src="../../../../assets/eq-103-f32840df14.light.svg" alt="J_\eta v(y)=\eta^{-3}\int_{[-\eta/2,\eta/2]^3}v(y+z)\,\mathrm{d} z, \qquad \delta_{\eta,\mu}v(y)= \frac{v(y+\eta e_\mu/2)-v(y-\eta e_\mu/2)}{\eta}." width="562">
  </picture>
</p>

We use $`\tau_vf(x)=f(x-v)`$ and the seminorm $`|\beta|_{C^j}=\max_{\mu<\nu,|\alpha|\le j} \|\partial^\alpha\beta_{\mu\nu}\|_\infty`$. Counting cochain pairings are bilinear after complexification. Distances are periodic sup distances. The symbol $`e`$ is the physical charge; numerical exponentials are written $`\exp(\cdot)`$ or $`\mathrm e`$.

**Cell geometry and probe constants**

Put

<!-- display-math:eq-104-e169d9e420
\begin{aligned}
 a'_{\eta,\nu}&=-\sum_{\mu\ne\nu}\delta_{\eta,\mu}\beta_{\mu\nu},\\[0pt]
 f^\eta_{\mu\nu}&=\delta_{\eta,\mu}a'_{\eta,\nu}
                         -\delta_{\eta,\nu}a'_{\eta,\mu}.
\end{aligned}
\tag{7}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-104-e169d9e420.dark.svg">
    <img src="../../../../assets/eq-104-e169d9e420.light.svg" alt="\begin{aligned} a&#x27;_{\eta,\nu}&amp;=-\sum_{\mu\ne\nu}\delta_{\eta,\mu}\beta_{\mu\nu},\\[0pt] f^\eta_{\mu\nu}&amp;=\delta_{\eta,\mu}a&#x27;_{\eta,\nu} -\delta_{\eta,\nu}a&#x27;_{\eta,\mu}. \end{aligned} \tag{7}" width="242">
  </picture>
</p>

On the physical lattice $`\eta\mathbb{Z}^3`$ set

<!-- display-math:eq-105-ceeda23d82
 b_{\eta,\mu\nu}(c)
       =(J_\eta\beta_{\mu\nu})
                       (c+\eta(e_\mu+e_\nu)/2),\qquad
 a_\eta^o=d_\eta^*b_\eta.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-105-ceeda23d82.dark.svg">
    <img src="../../../../assets/eq-105-ceeda23d82.light.svg" alt="b_{\eta,\mu\nu}(c) =(J_\eta\beta_{\mu\nu}) (c+\eta(e_\mu+e_\nu)/2),\qquad a_\eta^o=d_\eta^*b_\eta." width="365">
  </picture>
</p>

Here $`d_\eta`$ is the mesh-normalized forward cochain differential and $`d_\eta^*`$ its adjoint for the pairing $`\eta^3\sum`$. The adjoint formula gives

<!-- display-math:eq-106-b0bcb7fff3
 a_{\eta,\nu}^o(c)=(J_\eta a'_{\eta,\nu})(c+\eta e_\nu/2).
\tag{8}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-106-b0bcb7fff3.dark.svg">
    <img src="../../../../assets/eq-106-b0bcb7fff3.light.svg" alt="a_{\eta,\nu}^o(c)=(J_\eta a&#x27;_{\eta,\nu})(c+\eta e_\nu/2). \tag{8}" width="275">
  </picture>
</p>

Transport to the unit lattice and define

<!-- display-math:eq-107-7c1a5c790f
 \hat{\mathfrak a}_\eta^o(x,x+e_\nu)
                    =\eta^{1/2}a_{\eta,\nu}^o(\eta x).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-107-7c1a5c790f.dark.svg">
    <img src="../../../../assets/eq-107-7c1a5c790f.light.svg" alt="\hat{\mathfrak a}_\eta^o(x,x+e_\nu) =\eta^{1/2}a_{\eta,\nu}^o(\eta x)." width="202">
  </picture>
</p>

Its coboundary uses unscaled unit-lattice differences.

Form $`\widehat{\mathfrak a}`$ with $`\tau_v\beta`$ as in [(8)](RRM1.pdf), and periodize it on $`C(n_*)`$, $`n_*=R^*/\eta`$. For $`c\in\mathcal C_*=\{0,\ldots,2L-1\}^3`$, write $`\widehat{\mathfrak a}_c`$ for its cell copy; thus $`\widehat{\mathfrak a}_c=\widehat a_c`$ in the introduction. In physical coordinates the wall map carrying the first cell to cell $`c`$ acts in coordinate $`\mu`$ by translation through $`2i\ell_c`$ if $`c_\mu=2i`$, and by reflection $`y_\mu\mapsto(2i+2)\ell_c-y_\mu`$ if $`c_\mu=2i+1`$.

For a level-$`j`$ bond function $`A`$, $`\partial A`$ uses forward differences divided by $`\eta_j`$, and

<!-- display-math:eq-108-d8e2f5124d
|\delta_\alpha\partial A|_\infty
  =\sup_{\mu,\nu}\sup_{0<d(x,x')\le1}
     \frac{|\partial_\nu A_\mu(x')-\partial_\nu A_\mu(x)|}
          {d(x,x')^\alpha}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-108-d8e2f5124d.dark.svg">
    <img src="../../../../assets/eq-108-d8e2f5124d.light.svg" alt="|\delta_\alpha\partial A|_\infty =\sup_{\mu,\nu}\sup_{0&lt;d(x,x&#x27;)\le1} \frac{|\partial_\nu A_\mu(x&#x27;)-\partial_\nu A_\mu(x)|} {d(x,x&#x27;)^\alpha}." width="340">
  </picture>
</p>

We define the uniform probe constants over both possible stop scales. For $`\eta'=L^{-N'}`$ put

<!-- display-math:eq-109-b8a03c83f0
g_\nu^{\eta'}[\beta']
      =-\sum_{\mu\ne\nu}\delta_{\eta',\mu}J_{\eta'}\beta'_{\mu\nu}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-109-b8a03c83f0.dark.svg">
    <img src="../../../../assets/eq-109-b8a03c83f0.light.svg" alt="g_\nu^{\eta&#x27;}[\beta&#x27;] =-\sum_{\mu\ne\nu}\delta_{\eta&#x27;,\mu}J_{\eta&#x27;}\beta&#x27;_{\mu\nu}." width="185">
  </picture>
</p>

This is the smooth vector field $`J_{\eta'}a'_{\eta'}`$ in the midpoint formula. Let $`\mathcal I_\beta`$ consist of triples $`(N',a_{\rm s},r')`$ with $`N'\ge0`$, $`a_{\rm s}\in\{h/L,h/L^2\}`$, $`N'+\log_La_{\rm s}\ge1`$, and $`r'\in\{\pm1\}^3`$. $`r'`$ is identified with its diagonal orthogonal matrix, and $`U_{r'}\beta(x)=(\wedge^2r')\beta(r'^{-1}x)`$. At such a triple set $`\eta''=\eta'/a_{\rm s}`$, $`g^0=g^{\eta'}[U_{r'}\beta]`$, and

<!-- display-math:eq-110-c0d4d3a108
G_\nu(c)=\sqrt{a_{\rm s}}\,
                  g_\nu^0(a_{\rm s}c+\eta'e_\nu/2)
                       \quad(c\in\eta''\mathbb{Z}^3),\qquad
 W_\nu(x)=\sqrt{\eta'}\,g_\nu^0(\eta'x+\eta'e_\nu/2)
                       \quad(x\in\mathbb{Z}^3).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-110-c0d4d3a108.dark.svg">
    <img src="../../../../assets/eq-110-c0d4d3a108.light.svg" alt="G_\nu(c)=\sqrt{a_{\rm s}}\, g_\nu^0(a_{\rm s}c+\eta&#x27;e_\nu/2) \quad(c\in\eta&#x27;&#x27;\mathbb{Z}^3),\qquad W_\nu(x)=\sqrt{\eta&#x27;}\,g_\nu^0(\eta&#x27;x+\eta&#x27;e_\nu/2) \quad(x\in\mathbb{Z}^3)." width="626">
  </picture>
</p>

The three norms of $`G`$ are taken at mesh $`\eta''`$. Set

<!-- display-math:eq-111-244ba4b6b9
C_\beta=\sup_{\mathcal I_\beta}
              (|G|_\infty+|\partial G|_\infty+
                                    |\delta_\alpha\partial G|_\infty),
 \qquad
 \mathbf D=\sup_{\mathcal I_\beta}\|dW\|_{\ell^2(\text{plaquettes})}^2.
\tag{58}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-111-244ba4b6b9.dark.svg">
    <img src="../../../../assets/eq-111-244ba4b6b9.light.svg" alt="C_\beta=\sup_{\mathcal I_\beta} (|G|_\infty+|\partial G|_\infty+ |\delta_\alpha\partial G|_\infty), \qquad \mathbf D=\sup_{\mathcal I_\beta}\|dW\|_{\ell^2(\text{plaquettes})}^2. \tag{58}" width="561">
  </picture>
</p>

These suprema depend on $`\bar m,L,\alpha,\beta`$, and contain no charge, torus, or placement. They have the finite bounds

<!-- display-math:eq-112-616721460f
C_\beta\le2\sqrt h(1+h+3h^2)|\beta|_{C^3},
 \qquad
 \mathbf D\le48|\beta|_{C^2}^2(D_\beta^{\rm buf}+3)^3 .
\tag{59}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-112-616721460f.dark.svg">
    <img src="../../../../assets/eq-112-616721460f.light.svg" alt="C_\beta\le2\sqrt h(1+h+3h^2)|\beta|_{C^3}, \qquad \mathbf D\le48|\beta|_{C^2}^2(D_\beta^{\rm buf}+3)^3 . \tag{59}" width="496">
  </picture>
</p>

**[Theorem A](RRM1.pdf) (Normalized reference response).**

For the fixed construction, mass $`0<\bar m\le1`$, and probe $`\beta`$ above, there is $`e_{\rm RR}>0`$ such that for every $`0<e\le e_{\rm RR}`$ and every integer $`N\ge N_{\rm ref}(e)`$, the function [(2)](RRM1.pdf) is entire and

<!-- display-math:eq-113-05dd993ab9
\Theta_4^{(0)}\le C e^{\mathfrak e},\qquad
 (1+|c_2|)\Theta_2^{(0)}\le C e^{\mathfrak e}.
\tag{4}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-113-05dd993ab9.dark.svg">
    <img src="../../../../assets/eq-113-05dd993ab9.light.svg" alt="\Theta_4^{(0)}\le C e^{\mathfrak e},\qquad (1+|c_2|)\Theta_2^{(0)}\le C e^{\mathfrak e}. \tag{4}" width="331">
  </picture>
</p>

The constants are independent of $`N`$ and of the admitted placement. Every centered placement, $`|v+z_\beta-(\ell_c/2)(1,1,1)|_\infty\le\eta/2`$, is admitted in this range. One may take $`C=3\cdot10^5(1+\sqrt h\,C_\beta)^4h^{1/8}`$, where the finite, charge-independent $`C_\beta`$ is defined in [(58)](RRM1.pdf).

Let $`\mathbb E^{(0)}`$ denote the normalized zero-flux curvature law on this same reference torus and at the same tuned mass. Equivalently it is the probability law of $`F^{\rm u}=u`$ obtained by weighting $`\gamma_{n_*}`$ with the zero-source twist-averaged determinant in [(2)](RRM1.pdf). For $`X_c=\langle d\widehat a_c,F^{\rm u}\rangle`$ and $`H_2(y)=y^2-v_\eta`$, $`H_4(y)=y^4-6v_\eta y^2+3v_\eta^2`$,

<!-- display-math:eq-114-3c4a086e1c
\mathbb E^{(0)}\prod_{c\in\mathcal C_*}
             (e^{-m}H_m(X_c)-c_m)
       =\left[\prod_{c\in\mathcal C_*}
           (\partial_{t_c}^m-c_m)\right]\mathring\Phi(0),
 \qquad m=2,4.
\tag{5}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-114-3c4a086e1c.dark.svg">
    <img src="../../../../assets/eq-114-3c4a086e1c.light.svg" alt="\mathbb E^{(0)}\prod_{c\in\mathcal C_*} (e^{-m}H_m(X_c)-c_m) =\left[\prod_{c\in\mathcal C_*} (\partial_{t_c}^m-c_m)\right]\mathring\Phi(0), \qquad m=2,4. \tag{5}" width="530">
  </picture>
</p>

All expectations are finite. The response estimate concerns the full fixed family of $`N_*=8L^3`$ cells and the harmonic-averaged zero-flux law.

[RRM1](RRM1.pdf) also contains **[Theorem B](RRM1.pdf) in [Section 10](RRM1.pdf)**, the quantitative terminal reference-error estimate under the factor, mass, one-cell, tree and jet conditions. **[Proposition 11.1](RRM1.pdf)** admits those conditions on a positive charge interval.

Early zero-flux/Wick identities feed [TPM1](../Terminal%20measure%20and%20pressure%20%28TP1%29/TPM1.pdf); later response results import terminal bounds.
