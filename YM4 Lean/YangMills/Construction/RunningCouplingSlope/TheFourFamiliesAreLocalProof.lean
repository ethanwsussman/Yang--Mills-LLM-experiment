import YangMills.Construction.RunningCouplingSlope.SandwichesAlongTheBackgroundAreLocalProof
import YangMills.Construction.RunningCouplingSlope.TheFourFamiliesAreLocal
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOneProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FourFamiliesLocality
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
variable {L n k : ℕ}
private lemma conj_inv_conj_eq {T T' F : Type} [Fintype F] [DecidableEq F] [Fintype T']
    (u : ℂ) (P : Matrix T F ℂ) (P' : Matrix T' F ℂ) (g X : Matrix F F ℂ) (hg : IsUnit g.det)
    (hgt : g.transpose = g) :
    ((u • P) * g) * (g * X * g)⁻¹ * ((u • P') * g).transpose =
      P * X⁻¹ * ((u * u) • P'.transpose) := by
  have h1 : g * (g * X * g)⁻¹ * g = X⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    have a : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hg
    have b : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc g * (g⁻¹ * (X⁻¹ * g⁻¹)) * g = (g * g⁻¹) * X⁻¹ * (g⁻¹ * g) := by
          simp only [Matrix.mul_assoc]
      _ = X⁻¹ := by rw [a, b, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.transpose_mul, hgt, Matrix.transpose_smul]
  calc (u • P) * g * (g * X * g)⁻¹ * (g * (u • P'.transpose))
      = (u * u) • (P * (g * (g * X * g)⁻¹ * g) * P'.transpose) := by
        simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = P * X⁻¹ * ((u * u) • P'.transpose) := by
        rw [h1, Matrix.mul_smul]
private lemma meshTranspose_eq_smul_transpose {σ σ' : Type}
    (K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k) K) =
      (unitNormScale L k * unitNormScale L k) • (Matrix.of K).transpose := by apply _root_.YangMills.SharedProofs.p28483 <;> assumption
private lemma twoSourceBackground_zero (z : Fin 4 → ℤ) :
    twoSourceBackground L n k z 0 0 = trivialField L n k 0 := by apply _root_.YangMills.SharedProofs.p56412 <;> assumption
private lemma finite_face [Finite (Vertex L n k 0)] : Finite (Face L n k 0) := by apply _root_.YangMills.SharedProofs.p14127 <;> assumption
private lemma cellDist_self (y : Vertex L n k k) : cellDist y y = 0 := by apply _root_.YangMills.SharedProofs.p28613 <;> assumption
private lemma isLocalOnCells_one {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
    (θ : ℝ) : IsLocalOnCells c c (1 : Matrix ι ι ℂ) 1 θ (fun _ => 1) := by
  classical
  intro y' y
  by_cases h : y' = y
  · subst h
    have e : blockBetween c c (1 : Matrix ι ι ℂ) y' y' =
        Matrix.diagonal fun p => if c p = y' then (1 : ℂ) else 0 := by
      ext p q
      simp only [blockBetween, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · simp [hpq]
    rw [e, Matrix.l2_opNorm_diagonal, cellDist_self]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    split_ifs <;> simp
  · have e : blockBetween c c (1 : Matrix ι ι ℂ) y' y = 0 := by
      ext p q
      simp only [blockBetween, Matrix.one_apply, Matrix.zero_apply]
      by_cases hpq : p = q
      · subst hpq
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact h (h1.symm.trans h2)
      · simp [hpq]
    rw [e, norm_zero]
    positivity
private lemma weaken_along (hC : LocalFamiliesClosed) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ} {z : Fin 4 → ℤ} {M M' θ θ' : ℝ}
    (hM : 0 ≤ M) (hMM : M ≤ M') (hθ' : 0 < θ') (hθθ : θ' ≤ θ)
    (h : IsLocalAlongBackground c c' T z M θ) : IsLocalAlongBackground c c' T z M' θ' := by
  obtain ⟨S, -, hS⟩ := hC θ (hθ'.trans_le hθθ)
  exact (hS L n k hL hn).mono c c' T z M M' θ' hM hMM hθ' hθθ h
private lemma along_of_constant (hC : LocalFamiliesClosed)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} (z : Fin 4 → ℤ) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ)
    (h : IsLocalOnCells c c' A M θ fun _ => 1) : IsLocalAlongBackground c c' (fun _ _ => A) z M θ := by
  obtain ⟨S, -, hS⟩ := hC θ hθ
  exact (hS L n k hL hn).ofConstant c c' A z M hM h
private lemma isLocalOnCells_weaken (hC : LocalFamiliesClosed)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} {M M' θ θ' : ℝ} (hM : 0 ≤ M) (hMM : M ≤ M') (hθ' : 0 < θ') (hθθ : θ' ≤ θ)
    (h : IsLocalOnCells c c' A M θ fun _ => 1) : IsLocalOnCells c c' A M' θ' fun _ => 1 :=
  (weaken_along hC hL hn (z := 0) hM hMM hθ' hθθ
    (along_of_constant hC hL hn 0 hM (hθ'.trans_le hθθ) h)).value_local
private lemma conjugate_word_local {r S₂ S₃ : ℝ} (cl₂ : LocalFamilyClosure r S₂ L n k)
    (cl₃ : LocalFamilyClosure (r / 4) S₃ L n k) {F T T' : Type} [Fintype F] [Fintype T]
    [Fintype T'] [DecidableEq F] [DecidableEq T'] {cF : F → Vertex L n k k}
    {cT : T → Vertex L n k k} {cT' : T' → Vertex L n k k} {P : ℝ → ℝ → Matrix T F ℂ}
    {Z : ℝ → ℝ → Matrix F F ℂ} {P' : ℝ → ℝ → Matrix T' F ℂ} {z : Fin 4 → ℤ} {c : ℝ}
    (hr : 0 < r) (hS₂ : 0 ≤ S₂) (hc : 0 ≤ c) (hP : IsLocalAlongBackground cF cT P z c r)
    (hZ : IsLocalAlongBackground cF cF Z z c r) (hP' : IsLocalAlongBackground cF cT' P' z c r) :
    IsLocalAlongBackground cT' cT (fun s t => P s t * Z s t * (P' s t).transpose) z
      (S₃ * (S₂ * c * c + c) * (S₂ * c * c + c)) (r / 4 / 4) := by
  have h1 := cl₂.mul cF cF cT P Z z c c hc hc hP hZ
  have h2 := cl₂.transpose cF cT' P' z c hc hP'
  have hd0 : 0 ≤ S₂ * c * c := by positivity
  have h3 := cl₃.mono cF cT _ z _ (S₂ * c * c + c) (r / 4) hd0 (by linarith) (by positivity) le_rfl h1
  have h4 := cl₃.mono cT' cF _ z c (S₂ * c * c + c) (r / 4) hc (by linarith) (by positivity) le_rfl h2
  exact cl₃.mul cT' cF cT _ _ z _ _ (by positivity) (by positivity) h3 h4
private lemma isLocalFamily_of_along {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → Vertex L n k k}
    {T : ℝ → ℝ → Matrix ι ι ℂ} {z : Fin 4 → ℤ} {M θ : ℝ} (hF : IsLocalAlongBackground c c T z M θ)
    (hdet : IsUnit (Matrix.det (T 0 0))) (hinv : IsLocalOnCells c c (T 0 0)⁻¹ M θ fun _ => 1) :
    IsLocalFamily c T z M θ :=
  ⟨hF.contDiffAt_entry, hdet, hinv, hF.derivFirst_local, hF.derivSecond_local, hF.derivMixed_local⟩
theorem fourFamiliesLocal_of_components (hC : LocalFamiliesClosed)
    (hR : PeriodicResolventSqrtsLocal) (hI : FreeInversesLocal)
    (hN : NoiseMatrixAtTrivialLocalInverse) (hA : BackgroundMeansAreLocal)
    (hS : ConjugatedFamiliesLocal) :
    FourFamiliesLocal := by
  intro a ha L hL
  obtain ⟨M₁, θ₁, hM₁, hθ₁, hR'⟩ := hR L hL
  obtain ⟨M₂, θ₂, hM₂, hθ₂, hI'⟩ := hI L hL
  obtain ⟨M₃, θ₃, hM₃, hθ₃, hN'⟩ := hN a ha L hL
  obtain ⟨M₄, θ₄, hM₄, hθ₄, hA'⟩ := hA a ha L hL
  obtain ⟨M₅, θ₅, hM₅, hθ₅, hS'⟩ := hS L hL
  obtain ⟨θ, hθ, l₁, l₂, l₃, l₄, l₅⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₁ ∧ θ ≤ θ₂ ∧ θ ≤ θ₃ ∧ θ ≤ θ₄ ∧ θ ≤ θ₅ :=
    ⟨min (min (min (min θ₁ θ₂) θ₃) θ₄) θ₅,
      lt_min (lt_min (lt_min (lt_min hθ₁ hθ₂) hθ₃) hθ₄) hθ₅,
      (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))),
      (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))),
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨M₀, hM₀, m₁, m₂, m₃, m₄, m₅⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ M₁ ≤ M₀ ∧ M₂ ≤ M₀ ∧ M₃ ≤ M₀ ∧
      M₄ ≤ M₀ ∧ M₅ ≤ M₀ :=
    ⟨M₁ + M₂ + M₃ + M₄ + M₅, by positivity, by linarith, by linarith, by linarith, by linarith,
      by linarith⟩
  have r1 : 0 < θ / 256 := by positivity
  have r3 : 0 < θ / 256 / 4 := by positivity
  have r2 : 0 < θ / 256 / 4 / 4 := by positivity
  have q1 : θ / 256 ≤ θ := by linarith
  have q2 : θ / 256 / 4 / 4 ≤ θ / 256 := by linarith
  have q3 : θ / 256 / 4 / 4 ≤ θ := by linarith
  obtain ⟨S₁, hS₁, hc₁⟩ := hC θ hθ
  obtain ⟨S₂, hS₂, hc₂⟩ := hC (θ / 256) r1
  obtain ⟨S₃, hS₃, hc₃⟩ := hC (θ / 256 / 4) r3
  obtain ⟨S₄, hS₄, hc₄⟩ := hC (θ / 256 / 4 / 4) r2
  obtain ⟨c, hc0, c₁, c₂, c₃⟩ : ∃ c : ℝ, 0 ≤ c ∧ S₁ * M₀ * M₀ ≤ c ∧
      S₁ ^ 4 * (M₀ + 1) ^ 5 ≤ c ∧ M₀ ≤ c := by
    have a1 : 0 ≤ S₁ * M₀ * M₀ := by positivity
    have a2 : 0 ≤ S₁ ^ 4 * (M₀ + 1) ^ 5 := by positivity
    exact ⟨S₁ * M₀ * M₀ + S₁ ^ 4 * (M₀ + 1) ^ 5 + M₀, by positivity, by linarith, by linarith,
      by linarith⟩
  obtain ⟨e, he, he0⟩ : ∃ e : ℝ, e = S₃ * (S₂ * c * c + c) * (S₂ * c * c + c) ∧ 0 ≤ e :=
    ⟨_, rfl, by positivity⟩
  refine ⟨4 * (M₀ + e + 1), θ / 256 / 4 / 4, by positivity, r2, fun k hk => ?_⟩
  obtain ⟨n₁, h₁⟩ := hR' k hk
  obtain ⟨n₂, h₂⟩ := hI' k hk
  obtain ⟨n₃, h₃⟩ := hN' k hk
  obtain ⟨n₄, h₄⟩ := hA' k hk
  obtain ⟨n₅, h₅⟩ := hS' k hk
  refine ⟨n₁ + n₂ + n₃ + n₄ + n₅, fun n hn hn0 => ?_⟩
  intro _ _ _ _ _ _ _ _ z
  haveI : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun x : Vertex L n k 0 => ((0 : Fin 3), x)) fun x y h => (Prod.ext_iff.1 h).2
  haveI : Finite (Face L n k 0) := finite_face
  haveI : Fintype (Fin 3 × Face L n k 0) := Fintype.ofFinite _
  obtain ⟨gt, gst, gu, gsu, gl, gsl, -, -, -⟩ := h₁ n (by omega) hn0
  obtain ⟨Zu, Zl, Yu, Yl, Cu, Cl, Wu, Wl, Vu, Vl⟩ := h₂ n (by omega) hn0
  obtain ⟨Nu, Nl⟩ := h₃ n (by omega) hn0
  obtain ⟨fq, fqu, fr, fru, fg⟩ := h₄ n (by omega) hn0 z
  obtain ⟨fZ, fY⟩ := h₅ n (by omega) hn0 z
  have cl₁ := hc₁ L n k hL hn0
  have cl₂ := hc₂ L n k hL hn0
  have cl₃ := hc₃ L n k hL hn0
  have cl₄ := hc₄ L n k hL hn0
  have hS₁0 : 0 ≤ S₁ := by linarith
  have hS₂0 : 0 ≤ S₂ := by linarith
  have hM₀0 := hM₀.le
  have G : IsLocalAlongBackground colouredEdgeCell colouredEdgeCell
      (fun _ _ => periodicEdgeResolventSqrt L n k) z M₀ θ :=
    weaken_along hC hL hn0 hM₁.le m₁ hθ l₁ (along_of_constant hC hL hn0 z hM₁.le hθ₁ gl)
  have Gs : IsLocalAlongBackground colouredVertexCell colouredVertexCell
      (fun _ _ => periodicVertexResolventSqrt L n k) z M₀ θ :=
    weaken_along hC hL hn0 hM₁.le m₁ hθ l₁ (along_of_constant hC hL hn0 z hM₁.le hθ₁ gsl)
  have wq := weaken_along hC hL hn0 hM₄.le m₄ hθ l₄ fq
  have wqu := weaken_along hC hL hn0 hM₄.le m₄ hθ l₄ fqu
  have wr := weaken_along hC hL hn0 hM₄.le m₄ hθ l₄ fr
  have wru := weaken_along hC hL hn0 hM₄.le m₄ hθ l₄ fru
  have wZ := weaken_along hC hL hn0 hM₅.le m₅ hθ l₅ fZ
  have wY := weaken_along hC hL hn0 hM₅.le m₅ hθ l₅ fY
  have zero_z : xiConjugated L n k z 0 0 = xiConjugated L n k 0 0 0 := by
    simp only [xiConjugated, twoSourceBackground_zero]
  have zero_y : yConjugated L n k z 0 0 = yConjugated L n k 0 0 0 := by
    simp only [yConjugated, twoSourceBackground_zero]
  have Zi := cl₁.inv _ _ z M₀ hM₀0 wZ (by rw [zero_z]; exact Zu)
    (by rw [zero_z]; exact isLocalOnCells_weaken hC hL hn0 hM₂.le m₂ hθ l₂ Zl)
  have Yi := cl₁.inv _ _ z M₀ hM₀0 wY (by rw [zero_y]; exact Yu)
    (by rw [zero_y]; exact isLocalOnCells_weaken hC hL hn0 hM₂.le m₂ hθ l₂ Yl)
  have AQ := weaken_along hC hL hn0 (by positivity) c₁ r1 (by linarith)
    (cl₁.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wq G)
  have AQu := weaken_along hC hL hn0 (by positivity) c₁ r1 (by linarith)
    (cl₁.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wqu G)
  have AR := weaken_along hC hL hn0 (by positivity) c₁ r1 (by linarith)
    (cl₁.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wr Gs)
  have ARu := weaken_along hC hL hn0 (by positivity) c₁ r1 (by linarith)
    (cl₁.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wru Gs)
  have Zc := weaken_along hC hL hn0 (by positivity) c₂ r1 le_rfl Zi
  have Yc := weaken_along hC hL hn0 (by positivity) c₂ r1 le_rfl Yi
  have X₁ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 AQu Zc AQu
  have X₂ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 AQu Zc AQ
  have X₃ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 AQ Zc AQu
  have X₄ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 AQ Zc AQ
  have X₅ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 ARu Yc AR
  have X₆ := conjugate_word_local cl₂ cl₃ r1 hS₂0 hc0 AR Yc AR
  rw [← he] at X₁ X₂ X₃ X₄ X₅ X₆
  have eC : (fun s t => topCovariance (twoSourceBackground L n k z s t)) =
      fun s t => rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k *
        (xiConjugated L n k z s t)⁻¹ *
        (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose := by
    funext s t
    show Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Q *
        (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Xi)⁻¹ *
        Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
          (rescaledOperators L n k (twoSourceBackground L n k z s t)).Q) = _
    rw [meshTranspose_eq_smul_transpose]
    exact (conj_inv_conj_eq _ _ _ _ _ gu gt).symm
  have eW₁ : (fun s t => Matrix.of (meanKernelR L n k (twoSourceBackground L n k z s t)) *
      yInv (twoSourceBackground L n k z s t) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt) =
      fun s t => meanRAlong L n k z s t * periodicVertexResolventSqrt L n k *
        (yConjugated L n k z s t)⁻¹ *
        (rescaledRAlong L n k z s t * periodicVertexResolventSqrt L n k).transpose := by
    funext s t
    show Matrix.of (meanKernelR L n k (twoSourceBackground L n k z s t)) *
        (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Y)⁻¹ *
        Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
          (rescaledOperators L n k (twoSourceBackground L n k z s t)).R) = _
    rw [meshTranspose_eq_smul_transpose]
    exact (conj_inv_conj_eq _ _ _ _ _ gsu gst).symm
  have eW₂ : (fun s t => Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).R *
      yInv (twoSourceBackground L n k z s t) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt) =
      fun s t => rescaledRAlong L n k z s t * periodicVertexResolventSqrt L n k *
        (yConjugated L n k z s t)⁻¹ *
        (rescaledRAlong L n k z s t * periodicVertexResolventSqrt L n k).transpose := by
    funext s t
    show Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).R *
        (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Y)⁻¹ *
        Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
          (rescaledOperators L n k (twoSourceBackground L n k z s t)).R) = _
    rw [meshTranspose_eq_smul_transpose]
    exact (conj_inv_conj_eq _ _ _ _ _ gsu gst).symm
  have eN : (fun s t => noiseBlockMatrix a (twoSourceBackground L n k z s t)) =
      fun s t => Matrix.fromBlocks
        ((-1 : ℂ) • noiseAlong a L n k z s t + (-1 : ℂ) •
          (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k * (xiConjugated L n k z s t)⁻¹ *
            (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose))
        ((-1 : ℂ) • (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k *
            (xiConjugated L n k z s t)⁻¹ *
            (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose))
        ((-1 : ℂ) • (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k *
            (xiConjugated L n k z s t)⁻¹ *
            (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose))
        (1 + (-1 : ℂ) • (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k *
            (xiConjugated L n k z s t)⁻¹ *
            (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose)) := by
    funext s t
    have w₁ : Matrix.of (meanKernelQ L n k (twoSourceBackground L n k z s t)) *
        xiInv (twoSourceBackground L n k z s t) * meanQTranspose L n k (twoSourceBackground L n k z s t) =
        meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k * (xiConjugated L n k z s t)⁻¹ *
          (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose := by
      show Matrix.of (meanKernelQ L n k (twoSourceBackground L n k z s t)) *
          (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Xi)⁻¹ *
          Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
            (meanKernelQ L n k (twoSourceBackground L n k z s t))) = _
      rw [meshTranspose_eq_smul_transpose]
      exact (conj_inv_conj_eq _ _ _ _ _ gu gt).symm
    have w₂ : Matrix.of (meanKernelQ L n k (twoSourceBackground L n k z s t)) *
        xiInv (twoSourceBackground L n k z s t) *
        Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Qt =
        meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k * (xiConjugated L n k z s t)⁻¹ *
          (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose := by
      show Matrix.of (meanKernelQ L n k (twoSourceBackground L n k z s t)) *
          (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Xi)⁻¹ *
          Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
            (rescaledOperators L n k (twoSourceBackground L n k z s t)).Q) = _
      rw [meshTranspose_eq_smul_transpose]
      exact (conj_inv_conj_eq _ _ _ _ _ gu gt).symm
    have w₃ : Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Q *
        xiInv (twoSourceBackground L n k z s t) * meanQTranspose L n k (twoSourceBackground L n k z s t) =
        rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k * (xiConjugated L n k z s t)⁻¹ *
          (meanQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose := by
      show Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Q *
          (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Xi)⁻¹ *
          Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k)
            (meanKernelQ L n k (twoSourceBackground L n k z s t))) = _
      rw [meshTranspose_eq_smul_transpose]
      exact (conj_inv_conj_eq _ _ _ _ _ gu gt).symm
    have w₄ : topCovariance (twoSourceBackground L n k z s t) =
        rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k * (xiConjugated L n k z s t)⁻¹ *
          (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose :=
      congrFun (congrFun eC s) t
    unfold noiseBlockMatrix
    rw [w₁, w₂, w₃, w₄]
    simp only [neg_smul, one_smul, noiseAlong, sub_eq_add_neg]
  have n1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have Ipos : (0 : ℝ) ≤ 1 := zero_le_one
  have Γw := weaken_along hC hL hn0 hM₄.le m₄ r2 (q3.trans l₄) fg
  have B₁₁ := cl₄.mono _ _ _ z _ (M₀ + e + 1) _ (by rw [n1]; positivity)
    (by rw [n1]; linarith) r2 le_rfl (cl₄.add _ _ _ _ z _ _ (cl₄.smul _ _ _ z _ (-1 : ℂ) Γw)
      (cl₄.smul _ _ _ z _ (-1 : ℂ) X₁))
  have B₁₂ := cl₄.mono _ _ _ z _ (M₀ + e + 1) _ (by rw [n1]; positivity)
    (by rw [n1]; linarith) r2 le_rfl (cl₄.smul _ _ _ z _ (-1 : ℂ) X₂)
  have B₂₁ := cl₄.mono _ _ _ z _ (M₀ + e + 1) _ (by rw [n1]; positivity)
    (by rw [n1]; linarith) r2 le_rfl (cl₄.smul _ _ _ z _ (-1 : ℂ) X₃)
  have One := along_of_constant hC hL hn0 z Ipos r2
    (isLocalOnCells_one (edgeCell (L := L) (n := n) (k := k)) (θ / 256 / 4 / 4))
  have B₂₂ := cl₄.mono _ _ _ z _ (M₀ + e + 1) _ (by rw [n1]; positivity)
    (by rw [n1]; linarith) r2 le_rfl (cl₄.add _ _ _ _ z _ _ One (cl₄.smul _ _ _ z _ (-1 : ℂ) X₄))
  have NF := cl₄.fromBlocks _ _ _ _ _ _ _ _ z _ B₁₁ B₁₂ B₂₁ B₂₂
  have bigE : e ≤ 4 * (M₀ + e + 1) := by linarith
  have bigM : M₀ ≤ 4 * (M₀ + e + 1) := by linarith
  have bigM₂ : M₂ ≤ 4 * (M₀ + e + 1) := by linarith
  have bigM₃ : M₃ ≤ 4 * (M₀ + e + 1) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine isLocalFamily_of_along ?_ ?_ ?_
    · rw [eN]
      exact NF
    · simp only [twoSourceBackground_zero]
      exact Nu
    · simp only [twoSourceBackground_zero]
      exact isLocalOnCells_weaken hC hL hn0 hM₃.le bigM₃ r2 (q3.trans l₃) Nl
  · refine isLocalFamily_of_along ?_ ?_ ?_
    · rw [eC]
      exact cl₄.mono _ _ _ z _ _ _ he0 bigE r2 le_rfl X₄
    · simp only [twoSourceBackground_zero]
      exact Cu
    · simp only [twoSourceBackground_zero]
      exact isLocalOnCells_weaken hC hL hn0 hM₂.le bigM₂ r2 (q3.trans l₂) Cl
  · refine isLocalFamily_of_along ?_ ?_ ?_
    · rw [eW₁]
      exact cl₄.mono _ _ _ z _ _ _ he0 bigE r2 le_rfl X₅
    · simp only [twoSourceBackground_zero]
      exact Vu
    · simp only [twoSourceBackground_zero]
      exact isLocalOnCells_weaken hC hL hn0 hM₂.le bigM₂ r2 (q3.trans l₂) Vl
  · refine isLocalFamily_of_along ?_ ?_ ?_
    · rw [eW₂]
      exact cl₄.mono _ _ _ z _ _ _ he0 bigE r2 le_rfl X₆
    · simp only [twoSourceBackground_zero]
      exact Wu
    · simp only [twoSourceBackground_zero]
      exact isLocalOnCells_weaken hC hL hn0 hM₂.le bigM₂ r2 (q3.trans l₂) Wl
end YangMills.Construction.RunningCouplingSlope.FourFamiliesLocality
end
