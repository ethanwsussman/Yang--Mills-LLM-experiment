**Positive probes and free response (PR1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **PR1**.

- **[PRO1](PRO1.pdf)** — [Positive compact probes and free response coefficients](PRO1.pdf).
- **AI-written manuscript:** **[PRM1](PRM1.pdf)** — [Positive compact probes and free response coefficients for lattice QED in three dimensions](PRM1.pdf) · [TeX source](PRM1.tex).
- **Human-written manuscript:** to be added.

**Principal statements**

Notation and numbered references below follow **[PRM1](PRM1.pdf)**.

**Continuum setting**

Let $`\sigma_\nu`$ be the Pauli matrices and $`\gamma_\nu=\mathrm{diag}(\sigma_\nu,-\sigma_\nu)`$, $`1\le\nu\le3`$. Thus $`\gamma_\nu\gamma_\mu+\gamma_\mu\gamma_\nu=2\delta_{\mu\nu}`$. On $`L^2(\mathbb{R}^3;\mathbb{C}^4)`$, for $`M>0`$ and real $`a\in C_c^\infty(\mathbb{R}^3;\mathbb{R}^3)`$, write

<!-- display-math:eq-082-8bdf14f34f
S_M=(M+\gamma\cdot\partial)^{-1},\qquad
 V_a=i\gamma\cdot a,\qquad
 q_{4,M}(a)=-\tfrac14\mathrm{tr}[(S_MV_a)^4].
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-082-8bdf14f34f.dark.svg">
    <img src="../../../../assets/eq-082-8bdf14f34f.light.svg" alt="S_M=(M+\gamma\cdot\partial)^{-1},\qquad V_a=i\gamma\cdot a,\qquad q_{4,M}(a)=-\tfrac14\mathrm{tr}[(S_MV_a)^4]." width="479">
  </picture>
</p>

For a real compact smooth two-form $`\beta`$, use the Euclidean codifferential $`(d^*\beta)_\nu=-\sum_{\mu\ne\nu}\partial_\mu\beta_{\mu\nu}`$, put $`f=dd^*\beta`$, and define, at fixed mass $`\bar m>0`$,

<!-- display-math:eq-083-428df9f559
b(f)=-6\mathrm{tr}[(S_{\bar m}i\gamma\cdot d^*\beta)^4]
      =24q_{4,\bar m}(d^*\beta).
\tag{1}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-083-428df9f559.dark.svg">
    <img src="../../../../assets/eq-083-428df9f559.light.svg" alt="b(f)=-6\mathrm{tr}[(S_{\bar m}i\gamma\cdot d^*\beta)^4] =24q_{4,\bar m}(d^*\beta). \tag{1}" width="363">
  </picture>
</p>

This depends only on $`f`$: two choices of $`d^*\beta`$ with the same exterior derivative differ by a compactly supported smooth one-form that is closed and coclosed, hence harmonic and therefore zero.

**[Theorem A](PRM1.pdf) (A positive continuum probe).**

For every real $`a\in C_c^\infty(\mathbb{R}^3;\mathbb{R}^3)`$ and $`M>0`$, the operator $`(S_MV_a)^4`$ is trace class and its trace is real. There is $`C_a<\infty`$ such that, for $`M\ge1`$,

<!-- display-math:eq-084-d5118983c1
\left|q_{4,M}(a)-\frac1{240\pi M^5}
       \int_{\mathbb{R}^3}|\mathrm{curl}a|^4\,\mathrm{d} x\right|
 \le C_aM^{-7}.
\tag{2}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-084-d5118983c1.dark.svg">
    <img src="../../../../assets/eq-084-d5118983c1.light.svg" alt="\left|q_{4,M}(a)-\frac1{240\pi M^5} \int_{\mathbb{R}^3}|\mathrm{curl}a|^4\,\mathrm{d} x\right| \le C_aM^{-7}. \tag{2}" width="399">
  </picture>
</p>

In particular, for every $`\bar m>0`$ there is a real $`\beta\in C_c^\infty(\mathbb{R}^3;\Lambda^2)`$ for which $`f=dd^*\beta`$ satisfies $`b(f)>0`$.

**Lattice setting**

Fix $`0<\rho<1`$ and $`0<\bar m\le1`$. Let $`\beta`$ be a real nonzero compactly supported smooth two-form, and put $`a=d^*\beta`$, $`f=dd^*\beta`$. Thus $`a_\nu=-\sum_{\mu\ne\nu}\partial_\mu\beta_{\mu\nu}`$. Let $`Q_\beta`$ be a closed coordinate cube of least side $`D_\beta`$ containing $`\mathrm{supp}\beta`$; this side includes no buffer. For $`0<\eta\le1`$ define

<!-- display-math:eq-085-bf2b636dcf
J_\eta v(y)=\eta^{-3}\int_{[-\eta/2,\eta/2]^3}v(y+z)\,\mathrm{d} z,
 \qquad
 \delta_{\eta,\mu}v(y)=
      \frac{v(y+\eta e_\mu/2)-v(y-\eta e_\mu/2)}{\eta}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-085-bf2b636dcf.dark.svg">
    <img src="../../../../assets/eq-085-bf2b636dcf.light.svg" alt="J_\eta v(y)=\eta^{-3}\int_{[-\eta/2,\eta/2]^3}v(y+z)\,\mathrm{d} z, \qquad \delta_{\eta,\mu}v(y)= \frac{v(y+\eta e_\mu/2)-v(y-\eta e_\mu/2)}{\eta}." width="562">
  </picture>
</p>

The interpolating functions

<!-- display-math:eq-086-d54813d5b9
a_{\eta,\nu}^0(y)=-\sum_{\mu\ne\nu}
               \delta_{\eta,\mu}J_\eta\beta_{\mu\nu}(y)
\tag{3}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-086-d54813d5b9.dark.svg">
    <img src="../../../../assets/eq-086-d54813d5b9.light.svg" alt="a_{\eta,\nu}^0(y)=-\sum_{\mu\ne\nu} \delta_{\eta,\mu}J_\eta\beta_{\mu\nu}(y) \tag{3}" width="265">
  </picture>
</p>

are defined without periodization. If $`n=R/\eta\in\mathbb{N}`$, $`n\ge2`$, the lattice one-cochain on the physical torus is

<!-- display-math:eq-087-7b51010c56
a_{\eta,\nu}(\eta c)=\sum_{z\in\mathbb{Z}^3}
       a_{\eta,\nu}^0(\eta c+\eta e_\nu/2+Rz).
\tag{4}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-087-7b51010c56.dark.svg">
    <img src="../../../../assets/eq-087-7b51010c56.light.svg" alt="a_{\eta,\nu}(\eta c)=\sum_{z\in\mathbb{Z}^3} a_{\eta,\nu}^0(\eta c+\eta e_\nu/2+Rz). \tag{4}" width="330">
  </picture>
</p>

It is the adjoint lattice coboundary of the cube-averaged probe at plaquette centers. In lattice units the external connection is $`B_t(c,c+e_\nu)=t\eta a_{\eta,\nu}(\eta c)`$, extended with the orientation sign to reversed bonds. The free mass in these units is $`m=\bar m\eta`$.

The chamber labels are the $`48`$ signed permutation matrices $`g\in O_{\mathrm{cub}}=O(3)\cap\mathrm{GL}(3,\mathbb{Z})`$. Let $`s_0`$ change the sign of the third coordinate, let $`s_1,s_2`$ interchange coordinates $`(2,3)`$ and $`(1,2)`$, respectively, and let $`r_{e_1}`$ change the sign of the first coordinate. Set

<!-- display-math:eq-088-3712a64dff
\begin{gathered}
n_0=e_3,\quad n_1=(e_2-e_3)/\sqrt2,\quad
 n_2=(e_1-e_2)/\sqrt2,\quad n_3=-e_1,\\[0pt]
 (w_0,w_1,w_2,w_3)=(6,6\sqrt2,6\sqrt2,6).
\end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-088-3712a64dff.dark.svg">
    <img src="../../../../assets/eq-088-3712a64dff.light.svg" alt="\begin{gathered} n_0=e_3,\quad n_1=(e_2-e_3)/\sqrt2,\quad n_2=(e_1-e_2)/\sqrt2,\quad n_3=-e_1,\\[0pt] (w_0,w_1,w_2,w_3)=(6,6\sqrt2,6\sqrt2,6). \end{gathered}" width="456">
  </picture>
</p>

For a spinor $`\psi:\mathbb{Z}^3\times O_{\mathrm{cub}}\to\mathbb{C}^4`$ with $`\psi(c+ne_\nu,g)=-\psi(c,g)`$, put $`M_i(g)=\frac{w_i}{2}(\rho+\gamma\cdot gn_i)`$ and define

<!-- display-math:eq-089-941869c8ea
\begin{split}
 (D^{\mathrm{ch}}[B]\psi)(c,g)
 ={}&\sum_{i=0}^2M_i(g)\bigl(\psi(c,g)-\psi(c,gs_i)\bigr)\\[0pt]
 &+M_3(g)\bigl(\psi(c,g)
       -e^{iB(c,c+ge_1)}\psi(c+ge_1,gr_{e_1})\bigr).
\end{split}
\tag{5}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-089-941869c8ea.dark.svg">
    <img src="../../../../assets/eq-089-941869c8ea.light.svg" alt="\begin{split} (D^{\mathrm{ch}}[B]\psi)(c,g) ={}&amp;\sum_{i=0}^2M_i(g)\bigl(\psi(c,g)-\psi(c,gs_i)\bigr)\\[0pt] &amp;+M_3(g)\bigl(\psi(c,g) -e^{iB(c,c+ge_1)}\psi(c+ge_1,gr_{e_1})\bigr). \end{split} \tag{5}" width="518">
  </picture>
</p>

Here $`B`$ is an $`n\mathbb{Z}^3`$-periodic cochain on the oriented nearest-neighbor edges of the covering lattice, with $`B(c',c)=-B(c,c')`$ for $`c,c'\in\mathbb{Z}^3`$. The operator is determined by its values for $`c\in\{0,\ldots,n-1\}^3`$; when $`n=2`$, edges with the same quotient endpoints remain distinct. This is the chamber operator of (**[LPM1](../Infinite-lattice%20reflection%20positivity%20%28LP1%29/LPM1.pdf)**, [Section 2](../Infinite-lattice%20reflection%20positivity%20%28LP1%29/LPM1.pdf)) in lattice units. The spinor pairing uses counting measure in $`c`$ and $`48^{-1}\sum_g`$ in the labels.

Let

<!-- display-math:eq-090-9945683ac5
N_0(t)=\frac{\det(D^{\mathrm{ch}}[B_t]+m)}
                  {\det(D^{\mathrm{ch}}[0]+m)},\qquad
 c_j=N_0^{(j)}(0),\qquad
 a_{\mathrm{ch}}=(\log N_0)''(0),\quad
 b_{\mathrm{ch}}=(\log N_0)^{(4)}(0).
\tag{6}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-090-9945683ac5.dark.svg">
    <img src="../../../../assets/eq-090-9945683ac5.light.svg" alt="N_0(t)=\frac{\det(D^{\mathrm{ch}}[B_t]+m)} {\det(D^{\mathrm{ch}}[0]+m)},\qquad c_j=N_0^{(j)}(0),\qquad a_{\mathrm{ch}}=(\log N_0)&#x27;&#x27;(0),\quad b_{\mathrm{ch}}=(\log N_0)^{(4)}(0). \tag{6}" width="711">
  </picture>
</p>

The logarithm is the holomorphic branch equal to zero at the origin. Its denominator is nonzero: the real part of $`D^{\mathrm{ch}}[0]+m`$ is at least $`m>0`$. For comparison with the charge convention, for $`e>0`$ put $`q=e\eta^{1/2}`$; the normalized probe is $`\widehat a=\eta^{1/2}a_\eta`$, so $`B_t=q(t/e)\widehat a`$. The free ratio and its coefficients are independent of $`e`$.

On $`T_R=\mathbb{R}^3/R\mathbb{Z}^3`$ use spinors antiperiodic in all three directions. Their momentum set is $`\mathcal P_R=\frac{2\pi}{R}(\mathbb{Z}+\frac12)^3`$, and $`S^R`$ is the multiplier $`s_{\bar m}(P)`$ there, where $`s_m(p)=(m+i\gamma\cdot p)^{-1}`$. For $`R\ge D_\beta+1`$ let $`a^R=\sum_za(\,\cdot+Rz)`$, and put

<!-- display-math:eq-091-553d9175c1
b_R(f)=-6\mathrm{Tr}(S^Ri\gamma\cdot a^R)^4,
 \qquad b(f)=-6\mathrm{Tr}(S_{\bar m}i\gamma\cdot a)^4.
\tag{7}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-091-553d9175c1.dark.svg">
    <img src="../../../../assets/eq-091-553d9175c1.light.svg" alt="b_R(f)=-6\mathrm{Tr}(S^Ri\gamma\cdot a^R)^4, \qquad b(f)=-6\mathrm{Tr}(S_{\bar m}i\gamma\cdot a)^4. \tag{7}" width="463">
  </picture>
</p>

**[Theorem B](PRM1.pdf) (Free lattice response).**

For the operator and sampled probe above, fix $`0<\rho<1`$, $`0<\bar m\le1`$, and real nonzero $`\beta\in C_c^\infty(\mathbb{R}^3;\Lambda^2)`$. For all $`0<\eta\le1`$ and $`n=R/\eta\in\mathbb{N}`$ with $`n\ge2`$, the following assertions hold.

If $`R\ge D_\beta+1`$, the operators $`S^Ri\gamma\cdot a^R`$ and $`S_{\bar m}i\gamma\cdot a`$ belong to the Schatten class of order four; their fourth-power traces are real. There are constants $`C_1(\rho,\bar m,\beta)`$ and $`C_2(\bar m,\beta)`$ such that

<!-- display-math:eq-092-e044840ceb
\begin{aligned}
|b_{\mathrm{ch}}(\eta,R)-b_R(f)|&\le C_1\eta^{1/4},\\[0pt]
 |b_R(f)-b(f)|&\le C_2e^{-\bar m(R-D_\beta)},
 \qquad R\ge D_\beta+1,\quad0<\eta\le1,\quad R/\eta\in\mathbb{N}.
\end{aligned}
\tag{8}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-092-e044840ceb.dark.svg">
    <img src="../../../../assets/eq-092-e044840ceb.light.svg" alt="\begin{aligned} |b_{\mathrm{ch}}(\eta,R)-b_R(f)|&amp;\le C_1\eta^{1/4},\\[0pt] |b_R(f)-b(f)|&amp;\le C_2e^{-\bar m(R-D_\beta)}, \qquad R\ge D_\beta+1,\quad0&lt;\eta\le1,\quad R/\eta\in\mathbb{N}. \end{aligned} \tag{8}" width="607">
  </picture>
</p>

The constants are unchanged by every real translate of the probe. In particular $`b_{\mathrm{ch}}(\eta,R)`$ tends to $`b(f)`$ whenever $`\eta\to0`$ and $`R\to\infty`$.

The function $`N_0`$ is entire, even, and positive on the real axis. Its derivatives at zero are real and satisfy

<!-- display-math:eq-093-37943aa200
c_{2j+1}=0,\qquad c_2=a_{\mathrm{ch}},\qquad
 c_4=b_{\mathrm{ch}}+3c_2^2 .
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-093-37943aa200.dark.svg">
    <img src="../../../../assets/eq-093-37943aa200.light.svg" alt="c_{2j+1}=0,\qquad c_2=a_{\mathrm{ch}},\qquad c_4=b_{\mathrm{ch}}+3c_2^2 ." width="306">
  </picture>
</p>

There is $`C_{\rho,\bar m,\beta}<\infty`$, unchanged by real translations of $`\beta`$, such that

<!-- display-math:eq-094-598563ac28
|c_2|\le C_{\rho,\bar m,\beta}\quad(R\ge1),\qquad
 |c_4|\le C_{\rho,\bar m,\beta}\quad(R\ge D_\beta+1).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-094-598563ac28.dark.svg">
    <img src="../../../../assets/eq-094-598563ac28.light.svg" alt="|c_2|\le C_{\rho,\bar m,\beta}\quad(R\ge1),\qquad |c_4|\le C_{\rho,\bar m,\beta}\quad(R\ge D_\beta+1)." width="403">
  </picture>
</p>

All coefficients are independent of $`e`$ in the charge convention above. They are unchanged by translating the probe through $`\eta\mathbb{Z}^3`$ or by replacing its external cochain by a cubic reflected cochain.
