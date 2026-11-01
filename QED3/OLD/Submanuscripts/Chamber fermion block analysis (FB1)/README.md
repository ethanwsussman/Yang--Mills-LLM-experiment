**Chamber fermion block analysis (FB1)**

**Disclaimer:** these documents are largely LLM-created. Their correctness has not been satisfactorily verified.

Project codename: **FB1**.

- **[FBO1](FBO1.pdf)** — [Chamber fermion locality and local integration](FBO1.pdf).
- **AI-written manuscript:** **[FBM1](FBM1.pdf)** — [Chamber fermion locality and local integration](FBM1.pdf) · [TeX source](FBM1.tex).
- **Human-written manuscript:** to be added.

**Main statements**

The setting and principal theorem below are reproduced from **[FBM1](FBM1.pdf)**. Notation and numbered references follow that manuscript; references to other documents use their codenames.

Fix $`0<\rho<1`$, an odd integer $`L\ge5`$, $`0<\alpha<1`$, and
$`\varepsilon>0`$. At level $`k\ge0`$, put $`\eta=\eta_k=L^{-k}`$.
A photon site is $`c\in\eta\mathbb{Z}^3/\ell\mathbb{Z}^3`$; a chamber site is
$`x=(c,g)`$, where $`g\in O_{\mathrm{cub}}`$ is a signed permutation
matrix. There are $`48`$ labels $`g`$ and four spin components at
each photon site. Connections are periodic complex oriented bond
functions, with $`A(c',c)=-A(c,c')`$; spinors are antiperiodic in
each coordinate. The chamber measure is $`\eta^3/48`$, while the
photon-site spinor measure is $`\eta^3`$.
Operator kernels use the chamber measure in their column variable;
the identity kernel is $`48\eta^{-3}\mathbf1[x=x']1_4`$.
The cluster injection and mean are

<!-- display-math:eq-001-7f72201f4c
(J\xi)(c,g)=\xi(c),\qquad J^*f(c)=48^{-1}\sum_g f(c,g).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-001-7f72201f4c.dark.svg">
    <img src="../../../../assets/eq-001-7f72201f4c.light.svg" alt="(J\xi)(c,g)=\xi(c),\qquad J^*f(c)=48^{-1}\sum_g f(c,g)." width="334">
  </picture>
</p>

Adjoints use these Hermitian pairings. Transposes use the corresponding
bilinear pairings, without complex conjugation.

Use the Pauli and Dirac matrices

<!-- display-math:eq-002-64d4aaed16
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 \sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
 \sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 \gamma_j=\sigma_3\otimes\sigma_j,\quad
 \gamma_5=\sigma_1\otimes1_2.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-002-64d4aaed16.dark.svg">
    <img src="../../../../assets/eq-002-64d4aaed16.light.svg" alt="\sigma_1=\begin{pmatrix}0&amp;1\\1&amp;0\end{pmatrix},\quad \sigma_2=\begin{pmatrix}0&amp;-i\\i&amp;0\end{pmatrix},\quad \sigma_3=\begin{pmatrix}1&amp;0\\0&amp;-1\end{pmatrix},\qquad \gamma_j=\sigma_3\otimes\sigma_j,\quad \gamma_5=\sigma_1\otimes1_2." width="597">
  </picture>
</p>

Let $`s_0`$ reverse the third coordinate, $`s_1`$ interchange
coordinates $`2,3`$, and $`s_2`$ interchange $`1,2`$; let $`r_{e_1}`$
reverse the first coordinate. The four neighbours, inward normals,
and weights are

<!-- display-math:eq-003-f80f6a8262
\begin{gathered}
 x^{(i)}=(c,gs_i)\quad(0\le i\le2),\qquad
 x^{(3)}=(c+\eta ge_1,gr_{e_1}),\\[0pt]
 (n_0,n_1,n_2,n_3)
   =(e_3,(e_2-e_3)/\sqrt2,(e_1-e_2)/\sqrt2,-e_1),\\[0pt]
 (w_0,w_1,w_2,w_3)=(6,6\sqrt2,6\sqrt2,6).
 \end{gathered}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-003-f80f6a8262.dark.svg">
    <img src="../../../../assets/eq-003-f80f6a8262.light.svg" alt="\begin{gathered} x^{(i)}=(c,gs_i)\quad(0\le i\le2),\qquad x^{(3)}=(c+\eta ge_1,gr_{e_1}),\\[0pt] (n_0,n_1,n_2,n_3) =(e_3,(e_2-e_3)/\sqrt2,(e_1-e_2)/\sqrt2,-e_1),\\[0pt] (w_0,w_1,w_2,w_3)=(6,6\sqrt2,6\sqrt2,6). \end{gathered}" width="391">
  </picture>
</p>

For a charge $`e_k>0`$, the chamber operator is

<!-- display-math:eq-004-bf68354232
(D_Af)(x)=-\eta^{-1}\sum_{i=0}^3
       \frac{w_i}{2}(\rho+\gamma\cdot gn_i)
       \bigl(U_A(x,x^{(i)})f(x^{(i)})-f(x)\bigr),
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-004-bf68354232.dark.svg">
    <img src="../../../../assets/eq-004-bf68354232.light.svg" alt="(D_Af)(x)=-\eta^{-1}\sum_{i=0}^3 \frac{w_i}{2}(\rho+\gamma\cdot gn_i) \bigl(U_A(x,x^{(i)})f(x^{(i)})-f(x)\bigr)," width="453">
  </picture>
</p>

where internal transports are one and the external transport is
$`\exp(ie_k\eta A(c,c+\eta ge_1))`$.

The unit blocks are
$`\Delta_z=\{c:|c-z|_\infty<1/2\}`$, $`z\in\mathbb{Z}^3/\ell\mathbb{Z}^3`$.
For $`c\in\Delta_z`$, let $`c=c_0,c_1,\ldots,c_k=z`$ be the
centres of its nested blocks of sides $`L^j\eta`$.
Write $`\tau A(u,v)`$ for the arithmetic mean of the oriented
fine-bond sums along the six coordinate-order paths from $`u`$ to $`v`$.
Set

<!-- display-math:eq-005-2ef18ad27b
\begin{aligned}
 \varphi_A(z,c)&=\exp\!\left(ie_k\eta
                    \sum_{j<k}\tau A(c_{j+1},c_j)\right),&
 (Q_k(A)\xi)(z)&=\eta^3\sum_{c\in\Delta_z}\varphi_A(z,c)\xi(c),\\[0pt]
 (Q_k^T(-A)v)(c)&=\varphi_A(z,c)^{-1}v(z).&&
 \end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-005-2ef18ad27b.dark.svg">
    <img src="../../../../assets/eq-005-2ef18ad27b.light.svg" alt="\begin{aligned} \varphi_A(z,c)&amp;=\exp\!\left(ie_k\eta \sum_{j&lt;k}\tau A(c_{j+1},c_j)\right),&amp; (Q_k(A)\xi)(z)&amp;=\eta^3\sum_{c\in\Delta_z}\varphi_A(z,c)\xi(c),\\[0pt] (Q_k^T(-A)v)(c)&amp;=\varphi_A(z,c)^{-1}v(z).&amp;&amp; \end{aligned}" width="588">
  </picture>
</p>

For $`z'\in L\mathbb{Z}^3/\ell\mathbb{Z}^3`$, put $`B(z')=\{z:|z-z'|_\infty<L/2\}`$.
The next average and its algebraic reverse are

<!-- display-math:eq-006-17e6649757
\begin{aligned}
 U_A(z',z)&=\exp(ie_k\eta\tau A(z',z)),\\[0pt]
 (Q(A)v)(z')&=L^{-3}\sum_{z\in B(z')}U_A(z',z)v(z),&
 (Q^T(-A)v')(z)&=U_A(z',z)^{-1}v'(z').
 \end{aligned}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-006-17e6649757.dark.svg">
    <img src="../../../../assets/eq-006-17e6649757.light.svg" alt="\begin{aligned} U_A(z&#x27;,z)&amp;=\exp(ie_k\eta\tau A(z&#x27;,z)),\\[0pt] (Q(A)v)(z&#x27;)&amp;=L^{-3}\sum_{z\in B(z&#x27;)}U_A(z&#x27;,z)v(z),&amp; (Q^T(-A)v&#x27;)(z)&amp;=U_A(z&#x27;,z)^{-1}v&#x27;(z&#x27;). \end{aligned}" width="547">
  </picture>
</p>

The target pairing has measure $`L^3`$. These maps act componentwise
in spin. For $`k\ge1`$, define

<!-- display-math:eq-007-353767c8fa
\Pi_1(A)=JQ_k^T(-A)Q_k(A)J^*,\qquad
 \Pi_L(A)=JQ_k^T(-A)Q^T(-A)Q(A)Q_k(A)J^*.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-007-353767c8fa.dark.svg">
    <img src="../../../../assets/eq-007-353767c8fa.light.svg" alt="\Pi_1(A)=JQ_k^T(-A)Q_k(A)J^*,\qquad \Pi_L(A)=JQ_k^T(-A)Q^T(-A)Q(A)Q_k(A)J^*." width="542">
  </picture>
</p>

At $`k=0`$ use only $`\Pi_L(A)=JQ^T(-A)Q(A)J^*`$.
Let $`b=1`$, $`b_L=L^{-1}`$, $`b_-=1-L^{-1}`$, and

<!-- display-math:eq-008-47c4a94800
b_k=\frac{1-L^{-1}}{1-L^{-k}}\quad(k\ge1),\qquad
 \alpha_y=\frac{b_ki\gamma_5y}{b_k+i\gamma_5y},\qquad
 \beta_y=\frac{b_k^2b_L}{(b_k+b_L+i\gamma_5y)(b_k+i\gamma_5y)}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-008-47c4a94800.dark.svg">
    <img src="../../../../assets/eq-008-47c4a94800.light.svg" alt="b_k=\frac{1-L^{-1}}{1-L^{-k}}\quad(k\ge1),\qquad \alpha_y=\frac{b_ki\gamma_5y}{b_k+i\gamma_5y},\qquad \beta_y=\frac{b_k^2b_L}{(b_k+b_L+i\gamma_5y)(b_k+i\gamma_5y)}." width="591">
  </picture>
</p>

At $`y=\infty`$, put $`\alpha_\infty=b_k`$, $`\beta_\infty=0`$.
For $`0<\mu\le1`$, the penalized operators are

<!-- display-math:eq-009-4bbb8b32af
F_y(A)=
 \begin{cases}
 D_A+\mu+\alpha_y\Pi_1(A)+\beta_y\Pi_L(A),
      & k\ge1,\ y\in\mathbb{R}\cup\{\infty\},\\[0pt]
 D_A+\mu+b_L\Pi_L(A)+i\gamma_5y,
      & k=0,\ y\in\mathbb{R}.
 \end{cases}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-009-4bbb8b32af.dark.svg">
    <img src="../../../../assets/eq-009-4bbb8b32af.light.svg" alt="F_y(A)= \begin{cases} D_A+\mu+\alpha_y\Pi_1(A)+\beta_y\Pi_L(A), &amp; k\ge1,\ y\in\mathbb{R}\cup\{\infty\},\\[0pt] D_A+\mu+b_L\Pi_L(A)+i\gamma_5y, &amp; k=0,\ y\in\mathbb{R}. \end{cases}" width="459">
  </picture>
</p>

The data $`k,\mu,\ell,e_k`$ are independent.

Let $`M\ge L^2`$ be a power of $`L`$, with partition $`M`$-cubes
centred in $`M\mathbb{Z}^3/\ell\mathbb{Z}^3`$, and assume $`\ell/(LM)`$ is odd
and at least $`13`$. A connection belongs to
$`\widetilde{\mathcal G}_k`$ if $`A=A_0+A_1`$, $`A_0`$ is real,
$`\|A_1\|_\infty<e_k^{-1+\varepsilon}`$, and on every concentric
$`11M`$ enlargement of a partition cube,

<!-- display-math:eq-010-44a710159d
A_0=B_0+d\lambda,\qquad B_0,\lambda\ \hbox{real},\qquad
 \|B_0\|_\infty<e_k^{-1+\varepsilon},\qquad
 d\lambda(c,c')=\eta^{-1}(\lambda(c')-\lambda(c)).
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-010-44a710159d.dark.svg">
    <img src="../../../../assets/eq-010-44a710159d.light.svg" alt="A_0=B_0+d\lambda,\qquad B_0,\lambda\ \hbox{real},\qquad \|B_0\|_\infty&lt;e_k^{-1+\varepsilon},\qquad d\lambda(c,c&#x27;)=\eta^{-1}(\lambda(c&#x27;)-\lambda(c))." width="593">
  </picture>
</p>

The local gauges may be chosen independently.

Distances are periodic sup distances. For distinct chamber sites set
$`d_X(x,x')=\max(d(c,c'),\eta)`$, and, on pairs with $`0<d_X<1`$, put

<!-- display-math:eq-011-990426311a
U_A(x,x')=\exp(ie_k\eta\tau A(c,c')),\qquad
 (\delta_{\alpha,A}v)(x,x')
 =\frac{U_A(x,x')v(x')-v(x)}
        {d_X(x,x')^\alpha}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-011-990426311a.dark.svg">
    <img src="../../../../assets/eq-011-990426311a.light.svg" alt="U_A(x,x&#x27;)=\exp(ie_k\eta\tau A(c,c&#x27;)),\qquad (\delta_{\alpha,A}v)(x,x&#x27;) =\frac{U_A(x,x&#x27;)v(x&#x27;)-v(x)} {d_X(x,x&#x27;)^\alpha}." width="524">
  </picture>
</p>

Thus distinct labels over one photon site are included when $`k\ge1`$.
For an operator $`T`$, define

<!-- display-math:eq-012-b966f382d9
N_\gamma(T)=\sup_z\sum_{z'}e^{\gamma d(z,z')}
       \|\mathbf1_{\Delta_z}T\mathbf1_{\Delta_{z'}}\|_{\infty\to\infty}.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-012-b966f382d9.dark.svg">
    <img src="../../../../assets/eq-012-b966f382d9.light.svg" alt="N_\gamma(T)=\sup_z\sum_{z&#x27;}e^{\gamma d(z,z&#x27;)} \|\mathbf1_{\Delta_z}T\mathbf1_{\Delta_{z&#x27;}}\|_{\infty\to\infty}." width="292">
  </picture>
</p>

The sup norm uses Euclidean spinor norms; for pair outputs the left
indicator restricts the first point. At level zero,
$`N_\gamma^{\mathrm{ker}}`$ replaces the localized operator norm by
the supremum of the normalized chamber kernel on the two clusters.

**[Theorem A](FBM1.pdf).**

There are $`a'>0`$ and $`0<\gamma\le(6L)^{-1}`$, depending only on
$`\rho,L,\alpha`$, with the following property. Set
$`C_V=2\exp(1)(42+6b)`$ and
$`q(p)=54\pi C_Va'p/M`$. Assume

<!-- display-math:eq-013-c4bcd85512
M>4L,\qquad q(1)\le\tfrac12,\qquad
 0<e_k\le e_0,\qquad
 6Le_0^\varepsilon\le1,\qquad 4C_Va'e_0^\varepsilon\le1.
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-013-c4bcd85512.dark.svg">
    <img src="../../../../assets/eq-013-c4bcd85512.light.svg" alt="M&gt;4L,\qquad q(1)\le\tfrac12,\qquad 0&lt;e_k\le e_0,\qquad 6Le_0^\varepsilon\le1,\qquad 4C_Va&#x27;e_0^\varepsilon\le1." width="517">
  </picture>
</p>

For every $`A\in\widetilde{\mathcal G}_k`$, all the operators
[(2)](FBM1.pdf) are invertible. Their inverses
$`S_y(A)`$ are analytic in the connection and satisfy

<!-- display-math:eq-014-23f4c9aaea
N_\gamma(S_y(A))\le32a'w_k(y),\qquad
 N_\gamma(\delta_{\alpha,A}S_y(A))\le304a',\qquad
 w_k(y)=
 \begin{cases}1,&k\ge1,\\(1+|y|)^{-1},&k=0.\end{cases}
-->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../../assets/eq-014-23f4c9aaea.dark.svg">
    <img src="../../../../assets/eq-014-23f4c9aaea.light.svg" alt="N_\gamma(S_y(A))\le32a&#x27;w_k(y),\qquad N_\gamma(\delta_{\alpha,A}S_y(A))\le304a&#x27;,\qquad w_k(y)= \begin{cases}1,&amp;k\ge1,\\(1+|y|)^{-1},&amp;k=0.\end{cases}" width="617">
  </picture>
</p>

At level zero the first bound also holds in
$`N_\gamma^{\mathrm{ker}}`$; there are no short pairs at that level.
The constants are independent of the level, mesh, volume,
permitted connection, reference mass $`\mu\in(0,1]`$, and resolvent
parameter in its stated range.

[Theorem B](FBM1.pdf) of [FBM1](FBM1.pdf) ([Section 5](FBM1.pdf), “Weighted Grassmann block integration”) gives the block-integration identity and determinant localization under [Theorem A](FBM1.pdf) and the additional weakened-walk hypotheses stated there.
