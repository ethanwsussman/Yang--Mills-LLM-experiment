import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealForm
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace GroupLieProduct
namespace Subspaces
namespace RealForm
section
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedSpace ℝ A]
  [IsScalarTower ℝ ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedSpace ℝ B]
  [IsScalarTower ℝ ℂ B]
def straightenMap (G : A → B) (R : B →L[ℂ] A) (D : A →L[ℂ] B) (Z : A) : A :=
  Z - R (D Z) + R (G Z)
omit [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A] [NormedSpace ℝ B] [IsScalarTower ℝ ℂ B] in
theorem straightenMap_analyticAt {G : A → B} {R : B →L[ℂ] A} {D : A →L[ℂ] B}
    (hGa : AnalyticAt ℂ G 0) : AnalyticAt ℂ (straightenMap G R D) 0 := by
  have h₁ : AnalyticAt ℂ (fun Z : A => Z) 0 := analyticAt_id
  have h₂ : AnalyticAt ℂ (fun Z : A => R (D Z)) 0 := (R.comp D).analyticAt 0
  have h₃ : AnalyticAt ℂ (fun Z : A => R (G Z)) 0 := R.analyticAt _ |>.comp hGa
  exact (h₁.sub h₂).add h₃
omit [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A] [NormedSpace ℝ B] [IsScalarTower ℝ ℂ B] in
theorem straightenMap_hasFDerivAt {G : A → B} {R : B →L[ℂ] A} {D : A →L[ℂ] B}
    (hG : HasFDerivAt G D 0) :
    HasFDerivAt (straightenMap G R D) (ContinuousLinearMap.id ℂ A) 0 := by
  have h₁ : HasFDerivAt (fun Z : A => Z) (ContinuousLinearMap.id ℂ A) 0 := hasFDerivAt_id 0
  have h₂ : HasFDerivAt (fun Z : A => R (D Z)) (R.comp D) 0 := (R.comp D).hasFDerivAt
  have h₃ : HasFDerivAt (fun Z : A => R (G Z)) (R.comp D) 0 := R.hasFDerivAt.comp 0 hG
  exact ((h₁.sub h₂).add h₃).congr_fderiv (by ext; simp)
theorem exists_analytic_localInverse [FiniteDimensional ℝ A] (V : Submodule ℝ A)
    (W : Submodule ℝ B) (G : A → B) (R : B →L[ℂ] A)
    (D : A →L[ℂ] B) (hG : HasFDerivAt G D 0) (hGa : AnalyticAt ℂ G 0) (G0 : G 0 = 0)
    (hV : ∀ᶠ Z in 𝓝 (0 : A), Z ∈ V → G Z ∈ W) (hR : ∀ Y ∈ W, R Y ∈ V) (hD : ∀ X ∈ V, D X ∈ W) :
    ∃ g : A → A, g 0 = 0 ∧ HasFDerivAt g (ContinuousLinearMap.id ℂ A) 0 ∧
      (∀ᶠ Z in 𝓝 (0 : A), AnalyticAt ℂ g Z) ∧
      (∀ᶠ Z in 𝓝 (0 : A), g (straightenMap G R D Z) = Z) ∧
      (∀ᶠ Y in 𝓝 (0 : A), straightenMap G R D (g Y) = Y) ∧
      ∀ᶠ Y in 𝓝 (0 : A), Y ∈ V → g Y ∈ V := by
  have : CompleteSpace A := FiniteDimensional.complete ℝ A
  set Θ := straightenMap G R D with hΘ
  have Θ0 : Θ 0 = 0 := by simp [hΘ, straightenMap, G0]
  have hΘc : ContDiffAt ℂ ω Θ 0 := (straightenMap_analyticAt hGa).contDiffAt
  have hΘd : HasFDerivAt Θ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) 0 := by
    exact (straightenMap_hasFDerivAt (R := R) hG).congr_fderiv (by ext; simp)
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hΘc.hasStrictFDerivAt' hΘd hn
  have hgc := hΘc.to_localInverse hΘd hn
  set g := hΘc.localInverse hΘd hn with hg
  have g0 : g 0 = 0 := by
    have := hΘc.localInverse_apply_image hΘd hn
    rwa [Θ0] at this
  have hleft : ∀ᶠ Z in 𝓝 (0 : A), g (Θ Z) = Z := hs.eventually_left_inverse
  have hright : ∀ᶠ Y in 𝓝 (0 : A), Θ (g Y) = Y := by
    have := hs.eventually_right_inverse
    rwa [Θ0] at this
  refine ⟨g, g0, ?_, ?_, hleft, hright, ?_⟩
  · have := hs.to_localInverse
    rw [Θ0] at this
    exact this.hasFDerivAt.congr_fderiv (by ext; simp)
  · rw [Θ0] at hgc
    have := hgc.eventually (by simp)
    filter_upwards [this] with Z hZ
    exact hZ.analyticAt
  · obtain ⟨π₀, hπ₀⟩ := LinearMap.exists_leftInverse_of_injective V.subtype (Submodule.ker_subtype _)
    have hπ₁ : ∀ x : V, π₀ (x : A) = x := fun x => LinearMap.congr_fun hπ₀ x
    let π : A →L[ℝ] V := π₀.toContinuousLinearMap
    have hπ : ∀ x : V, π (x : A) = x := hπ₁
    let Θr : V → V := fun x => π (Θ x)
    have : CompleteSpace V := FiniteDimensional.complete ℝ V
    have hsr : HasStrictFDerivAt Θ (ContinuousLinearMap.id ℝ A) ((V.subtypeL 0 : A)) := by
      have := hs.restrictScalars ℝ
      exact HasStrictFDerivAt.congr_fderiv (by simpa using this) (by ext; simp)
    have hr : HasStrictFDerivAt Θr
        ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0 := by
      have h₁ := hsr.comp (0 : V) V.subtypeL.hasStrictFDerivAt
      have h₂ := π.hasStrictFDerivAt.comp (0 : V) h₁
      refine HasStrictFDerivAt.congr_fderiv h₂ ?_
      ext x
      simp [hπ]
    have Θr0 : Θr 0 = 0 := by simp [Θr, Θ0]
    set gr := hr.localInverse Θr _ 0 with hgr
    have r₁ : ∀ᶠ v in 𝓝 (0 : V), Θr (gr v) = v := by
      have := hr.eventually_right_inverse
      rwa [Θr0] at this
    have r₂ : Tendsto gr (𝓝 (0 : V)) (𝓝 0) := by
      have := hr.localInverse_tendsto
      rwa [Θr0] at this
    have hval : Tendsto (fun x : V => (x : A)) (𝓝 0) (𝓝 0) :=
      continuous_subtype_val.tendsto' 0 0 rfl
    have good : ∀ᶠ x : V in 𝓝 (0 : V), g (Θ (x : A)) = x ∧ ((x : A) ∈ V → G x ∈ W) :=
      hval.eventually (hleft.and hV)
    have hv : ∀ᶠ v : V in 𝓝 (0 : V), g (v : A) ∈ V := by
      filter_upwards [r₁, r₂.eventually good] with v h₁ h₂
      have hmem : Θ (gr v : A) ∈ V := by
        have hx := (gr v).2
        have hy := h₂.2 hx
        simp only [hΘ, straightenMap]
        exact V.add_mem (V.sub_mem hx (hR _ (hD _ hx))) (hR _ hy)
      have h₃ : Θ (gr v : A) = v := by
        have : π (Θ (gr v : A)) = v := h₁
        have h₄ := hπ ⟨_, hmem⟩
        simp only at h₄
        rw [this] at h₄
        exact (congrArg Subtype.val h₄).symm
      rw [← h₃, h₂.1]
      exact (gr v).2
    rw [nhds_subtype_eq_comap] at hv
    have := (eventually_comap.1 hv)
    filter_upwards [this] with Y hY hYV
    exact hY ⟨Y, hYV⟩ rfl
def realKernel (V : Submodule ℝ A) (D : A →L[ℂ] B) : Submodule ℝ A :=
  V ⊓ LinearMap.ker ((D.restrictScalars ℝ : A →L[ℝ] B) : A →ₗ[ℝ] B)
def realImage (W : Submodule ℝ B) (R : B →L[ℂ] A) : Submodule ℝ A :=
  W.map ((R.restrictScalars ℝ : B →L[ℝ] A) : B →ₗ[ℝ] A)
theorem mem_realKernel {V : Submodule ℝ A} {D : A →L[ℂ] B} {X : A} :
    X ∈ realKernel V D ↔ X ∈ V ∧ D X = 0 := by
  simp [realKernel]
theorem mem_realImage {W : Submodule ℝ B} {R : B →L[ℂ] A} {X : A} :
    X ∈ realImage W R ↔ ∃ Y ∈ W, R Y = X := by
  simp [realImage]
theorem realKernel_sup_realImage {V : Submodule ℝ A} {W : Submodule ℝ B} {R : B →L[ℂ] A}
    {D : A →L[ℂ] B} (hR : ∀ Y ∈ W, R Y ∈ V) (hD : ∀ X ∈ V, D X ∈ W)
    (hDR : ∀ Y ∈ W, D (R Y) = Y) :
    realKernel V D ⊔ realImage W R = V := by
  apply le_antisymm
  · refine sup_le (fun X hX => (mem_realKernel.1 hX).1) fun X hX => ?_
    obtain ⟨Y, hY, rfl⟩ := mem_realImage.1 hX
    exact hR Y hY
  · intro X hX
    have h₁ : X - R (D X) ∈ realKernel V D := by
      refine mem_realKernel.2 ⟨V.sub_mem hX (hR _ (hD _ hX)), ?_⟩
      rw [map_sub, hDR _ (hD _ hX), sub_self]
    have h₂ : R (D X) ∈ realImage W R := mem_realImage.2 ⟨_, hD _ hX, rfl⟩
    have := Submodule.add_mem_sup h₁ h₂
    simpa using this
theorem realKernel_inf_realImage {V : Submodule ℝ A} {W : Submodule ℝ B} {R : B →L[ℂ] A}
    {D : A →L[ℂ] B} (hDR : ∀ Y ∈ W, D (R Y) = Y) :
    realKernel V D ⊓ realImage W R = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨h₁, h₂⟩
  obtain ⟨Y, hY, rfl⟩ := mem_realImage.1 h₂
  have := (mem_realKernel.1 h₁).2
  rw [hDR Y hY] at this
  simp [this]
theorem zeroSet_local_graph [FiniteDimensional ℝ A] (V : Submodule ℝ A) (W : Submodule ℝ B)
    (G : A → B) (R : B →L[ℂ] A)
    (D : A →L[ℂ] B) (hG : HasFDerivAt G D 0) (hGa : AnalyticAt ℂ G 0) (G0 : G 0 = 0)
    (hV : ∀ᶠ Z in 𝓝 (0 : A), Z ∈ V → G Z ∈ W) (hR : ∀ Y ∈ W, R Y ∈ V) (hD : ∀ X ∈ V, D X ∈ W)
    (hDR : ∀ Y ∈ W, D (R Y) = Y) (N : Set A) (hN : N ∈ 𝓝 (0 : A)) :
    ∃ (U₁ U₂ : Set A) (g : A → A), IsOpen U₁ ∧ IsOpen U₂ ∧ (0 : A) ∈ U₁ ∧ (0 : A) ∈ U₂ ∧
      (∀ X ∈ U₁, X ∈ realKernel V D → ∀ X' ∈ U₂, X' ∈ realImage W R →
        X + X' ∈ N ∧ (G (X + X') = 0 ↔ X' = R (D (g X)))) ∧
      (∀ X ∈ U₁, X ∈ realKernel V D → R (D (g X)) ∈ U₂ ∧ R (D (g X)) ∈ realImage W R) ∧
      g 0 = 0 ∧ (∀ X ∈ U₁, AnalyticAt ℂ g X) ∧
      HasFDerivAt g (ContinuousLinearMap.id ℂ A) 0 := by
  obtain ⟨g, g0, gd, ga, gl, gr, gv⟩ := exists_analytic_localInverse V W G R D hG hGa G0 hV hR hD
  set Θ := straightenMap G R D with hΘ
  have hQ : ∀ᶠ Z in 𝓝 (0 : A), Z ∈ N ∧ (Z ∈ V → G Z ∈ W) ∧ g (Θ Z) = Z :=
    (eventually_of_mem hN fun _ h => h).and (hV.and gl)
  obtain ⟨ε, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hQ
  have gt : Tendsto g (𝓝 0) (𝓝 0) := by
    have := gd.continuousAt.tendsto
    rwa [g0] at this
  have Ft : Tendsto (fun X => R (D (g X))) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun Z => R (D Z)) (𝓝 (0 : A)) (𝓝 0) := by
      have := (R.comp D).continuous.tendsto 0
      rw [map_zero] at this
      exact this
    exact h.comp gt
  have small : ∀ᶠ X in 𝓝 (0 : A), X ∈ Metric.ball (0 : A) (ε / 2) :=
    Metric.ball_mem_nhds _ (by positivity)
  have hF : ∀ᶠ X in 𝓝 (0 : A), R (D (g X)) ∈ Metric.ball (0 : A) (ε / 2) :=
    Ft.eventually small
  have hg : ∀ᶠ X in 𝓝 (0 : A), g X ∈ Metric.ball (0 : A) ε :=
    gt.eventually (Metric.ball_mem_nhds _ ε0)
  have all := small.and (hF.and (hg.and (gv.and (gr.and ga))))
  refine ⟨interior {X | _}, Metric.ball 0 (ε / 2), g, isOpen_interior, Metric.isOpen_ball,
    mem_interior_iff_mem_nhds.2 all, Metric.mem_ball_self (by positivity), ?_, ?_, g0,
    fun X hX => (interior_subset hX).2.2.2.2.2, gd⟩
  · intro X hX hXE X' hX' hXE'
    obtain ⟨hs, hFX, hgX, hgV, hgr, -⟩ := interior_subset hX
    have hXV := (mem_realKernel.1 hXE).1
    have hDX := (mem_realKernel.1 hXE).2
    obtain ⟨Y, hY, rfl⟩ := mem_realImage.1 hXE'
    have hZb : X + R Y ∈ Metric.ball (0 : A) ε := by
      rw [Metric.mem_ball, dist_zero_right] at *
      calc ‖X + R Y‖ ≤ ‖X‖ + ‖R Y‖ := norm_add_le _ _
        _ < ε := by linarith
    obtain ⟨hN', -, hgl⟩ := hε _ hZb
    refine ⟨hN', ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
    · have hΘX : Θ (X + R Y) = X := by
        simp only [hΘ, straightenMap, h0, map_zero, add_zero, map_add, hDX, hDR Y hY, zero_add]
        abel
      rw [hΘX] at hgl
      rw [hgl, map_add, hDX, hDR Y hY, zero_add]
    · set Z := g X with hZ
      have hZV : Z ∈ V := hgV hXV
      obtain ⟨-, hZW, -⟩ := hε _ hgX
      have hGW := hZW hZV
      have h₁ : Z - R (D Z) + R (G Z) = X := hgr
      have h₂ : G Z = 0 := by
        have := congrArg D h₁
        simp only [map_add, map_sub, hDR _ (hD _ hZV), hDR _ hGW, hDX] at this
        simpa using this
      have h₃ : Z = X + R Y := by
        rw [h₂, map_zero, add_zero] at h₁
        rw [h0, ← h₁]
        abel
      rw [← h₃, h₂]
  · intro X hX hXE
    obtain ⟨-, hFX, -, hgV, -, -⟩ := interior_subset hX
    exact ⟨hFX, mem_realImage.2 ⟨_, hD _ (hgV (mem_realKernel.1 hXE).1), rfl⟩⟩
end
def hermitianTracelessPart : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2 where
  toFun X := (1 / 2 : ℝ) • (X + X.conjTranspose) -
    ((1 / 4 : ℝ) • Matrix.trace (X + X.conjTranspose)) • (1 : ComplexMatrix2)
  map_add' X Y := by
    simp only [Matrix.conjTranspose_add, Matrix.trace_add, smul_add, add_smul]
    abel
  map_smul' r X := by
    have h : (r • X).conjTranspose = r • X.conjTranspose := by
      rw [Matrix.conjTranspose_smul, star_trivial]
    simp only [h, ← smul_add, Matrix.trace_smul, RingHom.id_apply, smul_sub]
    rw [smul_comm (1 / 4 : ℝ) r, smul_assoc r _ (1 : ComplexMatrix2), smul_comm (1 / 2 : ℝ) r]
theorem hermitianTracelessPart_mem (X : ComplexMatrix2) :
    hermitianTracelessPart X ∈ ComplexMatrix2.hermitianTraceless := by
  set H := X + X.conjTranspose with hH
  have hherm : H.conjTranspose = H := by
    simp [hH, add_comm]
  have htr : star (Matrix.trace H) = Matrix.trace H := by
    rw [← Matrix.trace_conjTranspose, hherm]
  have hval : hermitianTracelessPart X =
      (1 / 2 : ℝ) • H - ((1 / 4 : ℝ) • Matrix.trace H) • (1 : ComplexMatrix2) := rfl
  refine ⟨?_, ?_⟩
  · rw [hval, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      hherm, Matrix.conjTranspose_one, star_trivial, star_smul, star_trivial, htr]
  · rw [hval]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin]
    simp only [Complex.real_smul, smul_eq_mul]
    push_cast
    ring
theorem hermitianTracelessPart_of_mem {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : hermitianTracelessPart X = X := by
  obtain ⟨h₁, h₂⟩ := hX
  have hval : hermitianTracelessPart X = (1 / 2 : ℝ) • (X + X.conjTranspose) -
    ((1 / 4 : ℝ) • Matrix.trace (X + X.conjTranspose)) • (1 : ComplexMatrix2) := rfl
  have h₃ : Matrix.trace X = 0 := h₂
  rw [hval, ← h₁, Matrix.trace_add, h₃, add_zero, smul_zero, zero_smul, sub_zero, ← two_smul ℝ X,
    smul_smul]
  norm_num
theorem hermitianTracelessPart_neg_I_smul {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    hermitianTracelessPart (-Complex.I • X) = 0 := by
  obtain ⟨h₁, -⟩ := hX
  have h₂ : (-Complex.I • X).conjTranspose = -(-Complex.I • X) := by
    rw [Matrix.conjTranspose_smul, ← h₁]
    simp
  have hval : hermitianTracelessPart (-Complex.I • X) =
    (1 / 2 : ℝ) • ((-Complex.I • X) + (-Complex.I • X).conjTranspose) -
    ((1 / 4 : ℝ) • Matrix.trace ((-Complex.I • X) + (-Complex.I • X).conjTranspose)) •
      (1 : ComplexMatrix2) := rfl
  rw [hval, h₂]
  simp
theorem complex_smul_eq_re_add_im {σ : Type} (c : ℂ) (Z : σ → ComplexMatrix2) :
    c • Z = c.re • Z + c.im • (Complex.I • Z) := by
  funext s i j
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring
def complexifyLinear {S S' : Type} (Q : (S' → ComplexMatrix2) →ₗ[ℝ] (S → ComplexMatrix2)) :
    (S' → ComplexMatrix2) →ₗ[ℂ] (S → ComplexMatrix2) where
  toFun Y := Q Y + Complex.I • Q (-Complex.I • Y)
  map_add' Y Y' := by
    simp only [smul_add, map_add]
    abel
  map_smul' c Y := by
    have hadd : ∀ Y Y' : S' → ComplexMatrix2,
        Q (Y + Y') + Complex.I • Q (-Complex.I • (Y + Y')) =
        (Q Y + Complex.I • Q (-Complex.I • Y)) + (Q Y' + Complex.I • Q (-Complex.I • Y')) := by
      intro Y Y'
      simp only [smul_add, map_add]
      abel
    have hreal : ∀ (a : ℝ) (Y : S' → ComplexMatrix2),
        Q (a • Y) + Complex.I • Q (-Complex.I • a • Y) =
          a • (Q Y + Complex.I • Q (-Complex.I • Y)) := by
      intro a Y
      rw [smul_comm (-Complex.I) a Y, map_smul, map_smul, smul_add, smul_comm Complex.I a]
    have hI : ∀ Y : S' → ComplexMatrix2,
        Q (Complex.I • Y) + Complex.I • Q (-Complex.I • Complex.I • Y) =
          Complex.I • (Q Y + Complex.I • Q (-Complex.I • Y)) := by
      intro Y
      have h₁ : Q (-Complex.I • Y) = -Q (Complex.I • Y) := by
        rw [neg_smul, map_neg]
      have h₂ : -Complex.I • Complex.I • Y = Y := by
        rw [smul_smul]
        simp
      rw [h₁, h₂, smul_add, smul_smul, Complex.I_mul_I, smul_neg, neg_smul, one_smul, neg_neg]
      abel
    rw [RingHom.id_apply, complex_smul_eq_re_add_im c Y, hadd, hreal, hreal, hI,
      complex_smul_eq_re_add_im c (Q Y + Complex.I • Q (-Complex.I • Y))]
section EmptyGroupFactors
variable {S : Type}
def inclAlgebra : (S → ComplexMatrix2) →ₗ[ℂ] (Empty ⊕ S → ComplexMatrix2) where
  toFun Z := ofParts Empty.elim Z
  map_add' Z Z' := by
    funext q
    rcases q with q | q
    · exact q.elim
    · rfl
  map_smul' c Z := by
    funext q
    rcases q with q | q
    · exact q.elim
    · rfl
def algebraComponentLinear : (Empty ⊕ S → ComplexMatrix2) →ₗ[ℂ] (S → ComplexMatrix2) where
  toFun q := algebraComponent q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem continuous_algebraComponent :
    Continuous (algebraComponent : (Empty ⊕ S → ComplexMatrix2) → S → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_inclAlgebra :
    Continuous (inclAlgebra : (S → ComplexMatrix2) → Empty ⊕ S → ComplexMatrix2) := by
  refine continuous_pi fun q => ?_
  rcases q with q | q
  · exact q.elim
  · exact continuous_apply q
def tracelessPart : (S → ComplexMatrix2) →ₗ[ℂ] (S → ComplexMatrix2) where
  toFun Z s := Z s - ((1 / 2 : ℂ) * Matrix.trace (Z s)) • (1 : ComplexMatrix2)
  map_add' Z Z' := by
    funext s
    simp only [Pi.add_apply, Matrix.trace_add, mul_add, add_smul]
    abel
  map_smul' c Z := by
    funext s
    simp only [Pi.smul_apply, Matrix.trace_smul, RingHom.id_apply, smul_sub, smul_smul, smul_eq_mul]
    congr 2
    ring
theorem tracelessPart_mem (Z : S → ComplexMatrix2) : tracelessPart Z ∈ tracelessPi S := by
  intro s
  show Matrix.trace (Z s - ((1 / 2 : ℂ) * Matrix.trace (Z s)) • (1 : ComplexMatrix2)) = 0
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring
theorem tracelessPart_of_mem {Z : S → ComplexMatrix2} (hZ : Z ∈ tracelessPi S) :
    tracelessPart Z = Z := by
  funext s
  have h : Matrix.trace (Z s) = 0 := hZ s
  show Z s - ((1 / 2 : ℂ) * Matrix.trace (Z s)) • (1 : ComplexMatrix2) = Z s
  rw [h]
  simp
theorem inclAlgebra_mem {Z : S → ComplexMatrix2} (hZ : Z ∈ tracelessPi S) :
    inclAlgebra Z ∈ tracelessPi (Empty ⊕ S) := by
  intro q
  rcases q with q | q
  · exact q.elim
  · exact hZ q
theorem mem_tracelessPi_of_hermitian {Z : S → ComplexMatrix2}
    (hZ : Z ∈ hermitianTracelessFunctions S) : Z ∈ tracelessPi S :=
  fun s => (hZ s (mem_univ s)).2
theorem expChartAt_zero (q : Empty ⊕ S → ComplexMatrix2) : expChartAt 0 q = q := by
  funext x
  rcases x with x | x
  · exact x.elim
  · simp [expChartAt]
end EmptyGroupFactors
def matrixEquivLinear : ComplexMatrix2 →ₗ[ℂ] Coordinates.ComplexCoordinates 4 where
  toFun := Coordinates.ComplexCoordinates.matrixEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def matrixEquivSymmLinear : Coordinates.ComplexCoordinates 4 →ₗ[ℂ] ComplexMatrix2 where
  toFun := Coordinates.ComplexCoordinates.matrixEquiv.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def tupleOfCoordsLinear {σ : Type} [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    Coordinates.ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → ComplexMatrix2) where
  toFun := tupleOfCoords b ν
  map_add' w w' := by
    funext i
    simp [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, add_smul,
      Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, Finset.smul_sum, mul_smul]
theorem tupleOfCoords_mem {σ : Type} [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    tupleOfCoords b ν w ∈ tracelessPi σ := fun _ =>
  show _ ∈ ComplexMatrix2.traceless from
    ComplexMatrix2.traceless.sum_mem fun c _ => ComplexMatrix2.traceless.smul_mem _ (b c).2
theorem exists_linear_coords {σ : Type} [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    ∃ C : (σ → ComplexMatrix2) →ₗ[ℂ] Coordinates.ComplexCoordinates (Fintype.card σ * 3),
      ∀ x ∈ tracelessPi σ, tupleOfCoords b ν (C x) = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ComplexMatrix2.traceless.subtype
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.pi fun j => (b.coord (finProdFinEquiv.symm j).2) ∘ₗ g ∘ₗ
    LinearMap.proj (ν.symm (finProdFinEquiv.symm j).1), fun x hx => ?_⟩
  funext i
  have hxi : x i ∈ ComplexMatrix2.traceless := hx i
  have hgx : g (x i) = ⟨x i, hxi⟩ := by
    have := LinearMap.congr_fun hg ⟨x i, hxi⟩
    simpa using this
  have hsum := congrArg ComplexMatrix2.traceless.subtype (b.sum_repr ⟨x i, hxi⟩)
  rw [map_sum] at hsum
  simp only [map_smul, Submodule.subtype_apply] at hsum
  show ∑ c, (b.coord (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2
      (g (x (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1)))) • (b c : ComplexMatrix2)
      = x i
  simp only [Equiv.symm_apply_apply, hgx, Module.Basis.coord_apply]
  exact hsum
theorem traceless_basis_nonempty : Nonempty (Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) := by
  let t : ComplexMatrix2 →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin 2) ℂ ℂ
  have hker : ComplexMatrix2.traceless = LinearMap.ker t := by
    ext X
    exact Iff.rfl
  have hsurj : LinearMap.range t = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / 2) • (1 : ComplexMatrix2), ?_⟩
    simp only [t, Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have hdim := LinearMap.finrank_range_add_finrank_ker t
  rw [hsurj, finrank_top, ← hker] at hdim
  have h₄ : Module.finrank ℂ ComplexMatrix2 = 4 := by
    simp [Module.finrank_matrix]
  have h₁ : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  exact ⟨Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless (by omega)⟩
theorem analyticAt_of_isHolomorphicToCoords
    (h₁ : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h₂ : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {S : Type} [Fintype S] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝒳 : Set (Empty ⊕ S → ComplexMatrix2)} (Ψk : (Empty ⊕ S → ComplexMatrix2) → ComplexMatrix2)
    (h0 : (0 : Empty ⊕ S → ComplexMatrix2) ∈ 𝒳)
    (hk : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv 𝒳 Ψk) :
    AnalyticAt ℂ (fun Z : S → ComplexMatrix2 => Ψk (inclAlgebra (tracelessPart Z))) 0 := by
  obtain ⟨-, -, hloc⟩ := hk
  obtain ⟨O₀, hO₀, -, -, hν⟩ := hloc 0 h0
  let ν := Fintype.equivFin (Empty ⊕ S)
  have hf := hν ν
  obtain ⟨C, hC⟩ := exists_linear_coords b ν
  let L : (S → ComplexMatrix2) →ₗ[ℂ]
      Coordinates.ComplexCoordinates (Fintype.card (Empty ⊕ S) * 3) :=
    C ∘ₗ inclAlgebra ∘ₗ tracelessPart
  have hTL : ∀ Z, tupleOfCoords b ν (L Z) = inclAlgebra (tracelessPart Z) := fun Z =>
    hC _ (inclAlgebra_mem (tracelessPart_mem Z))
  let h := Coordinates.ComplexCoordinates.matrixEquiv ∘ (Ψk ∘ expChartAt 0) ∘ tupleOfCoords b ν
  let F : (S → ComplexMatrix2) → ComplexMatrix2 := fun Z => matrixEquivSymmLinear (h (L Z))
  have hFeq : (fun Z : S → ComplexMatrix2 => Ψk (inclAlgebra (tracelessPart Z))) = F := by
    funext Z
    show _ = Coordinates.ComplexCoordinates.matrixEquiv.symm
      (Coordinates.ComplexCoordinates.matrixEquiv
        (Ψk (expChartAt 0 (tupleOfCoords b ν (L Z)))))
    rw [Equiv.symm_apply_apply, hTL, expChartAt_zero]
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hopen : IsOpen (L ⁻¹' (tupleOfCoords b ν ⁻¹' O₀)) := hf.1.preimage hLc
  have hdiff : DifferentiableOn ℂ F (L ⁻¹' (tupleOfCoords b ν ⁻¹' O₀)) := by
    intro Z hZ
    obtain ⟨Lc, hLd⟩ := ((h₁.1 _ _ hf.1).1 4 h hf).2.2.1 (L Z) hZ
    have hd : HasFDerivAt h Lc (L Z) := hasFDerivAt_of_restrictScalars ℝ hLd rfl
    have hL' : DifferentiableAt ℂ L Z := (L.toContinuousLinearMap).differentiableAt
    have he : DifferentiableAt ℂ matrixEquivSymmLinear (h (L Z)) :=
      (matrixEquivSymmLinear.toContinuousLinearMap).differentiableAt
    exact (he.comp Z (hd.differentiableAt.comp Z hL')).differentiableWithinAt
  rw [hFeq]
  refine h₂ S _ F hopen hdiff 0 ?_
  show tupleOfCoords b ν (L 0) ∈ O₀
  rw [map_zero, show tupleOfCoords b ν 0 = 0 from map_zero (tupleOfCoordsLinear b ν)]
  exact hO₀
theorem isHolomorphicToCoords_of_analyticOn {S : Type} [Fintype S]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {U : Set (S → ComplexMatrix2)} (hU : IsOpen U) (F : (S → ComplexMatrix2) → ComplexMatrix2)
    (hF : ∀ X ∈ U, AnalyticAt ℂ F X) :
    IsHolomorphicToCoords (ι := Empty) (κ := S) b Coordinates.ComplexCoordinates.matrixEquiv
      (algebraComponent ⁻¹' U ∩ GroupLieProduct Empty S) (fun q => F (algebraComponent q)) := by
  have hal := continuous_algebraComponent (S := S)
  have hFc : ContinuousOn F U := fun X hX => (hF X hX).continuousAt.continuousWithinAt
  have hec : Continuous matrixEquivLinear := matrixEquivLinear.continuous_of_finiteDimensional
  refine ⟨⟨_, hU.preimage hal, rfl⟩, ?_, fun p hp => ?_⟩
  · exact hec.comp_continuousOn (hFc.comp hal.continuousOn fun _ h => h.1)
  · have hpU : algebraComponent p ∈ U := hp.1
    have hz : algebraComponent (expChartAt p (0 : Empty ⊕ S → ComplexMatrix2)) =
        algebraComponent p := by
      funext s
      simp [algebraComponent, expChartAt]
    refine ⟨{A | A ∈ tracelessPi (Empty ⊕ S) ∧ algebraComponent (expChartAt p A) ∈ U},
      ⟨fun _ => ComplexMatrix2.traceless.zero_mem, by rwa [hz]⟩, ?_, ?_⟩
    · rintro A ⟨hA, hAU⟩
      refine ⟨hAU, ?_⟩
      intro q
      rcases q with q | q
      · exact q.elim
      · exact ComplexMatrix2.traceless.add_mem (hp.2 (.inr q)) (hA (.inr q))
    · refine ⟨⟨fun A hA => hA.1, ?_⟩, fun ν => ?_⟩
      · rintro A ⟨hA, hAU⟩
        obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 hU _ hAU
        refine ⟨ε, ε0, fun B hB hBA => ⟨hB, hε ?_⟩⟩
        rw [Metric.mem_ball, dist_pi_lt_iff ε0]
        intro s
        have hle : ComplexMatrix2.operatorNorm ((B - A) (.inr s)) ≤ supNorm (B - A) :=
          le_ciSup (f := fun i => ComplexMatrix2.operatorNorm ((B - A) i))
            (Set.finite_range _).bddAbove (.inr s)
        have hd : dist (algebraComponent (expChartAt p B) s)
            (algebraComponent (expChartAt p A) s) = ‖(B - A) (.inr s)‖ := by
          show dist (p (.inr s) + B (.inr s)) (p (.inr s) + A (.inr s)) = _
          rw [dist_add_left, dist_eq_norm]
          rfl
        rw [hd]
        exact lt_of_le_of_lt hle hBA
      · let Ml : Coordinates.ComplexCoordinates (Fintype.card (Empty ⊕ S) * 3) →ₗ[ℂ]
            (S → ComplexMatrix2) :=
          algebraComponentLinear ∘ₗ tupleOfCoordsLinear b ν
        let m : Coordinates.ComplexCoordinates (Fintype.card (Empty ⊕ S) * 3) →
            S → ComplexMatrix2 :=
          fun w => algebraComponent p + Ml w
        have hmc : Continuous m := continuous_const.add Ml.continuous_of_finiteDimensional
        have hmd : Differentiable ℂ m :=
          (differentiable_const _).add (Ml.toContinuousLinearMap).differentiable
        have hpre : tupleOfCoords b ν ⁻¹'
            {A | A ∈ tracelessPi (Empty ⊕ S) ∧ algebraComponent (expChartAt p A) ∈ U} =
            m ⁻¹' U := by
          ext w
          exact ⟨fun h => h.2, fun h => ⟨tupleOfCoords_mem b ν w, h⟩⟩
        rw [hpre]
        refine ⟨hU.preimage hmc, ?_, fun w hw j => ?_⟩
        · exact hec.comp_continuousOn (hFc.comp hmc.continuousOn fun _ h => h)
        · have hline : Continuous fun ζ : ℂ =>
              w + ζ • Coordinates.ComplexCoordinates.stdBasisVector j :=
            continuous_const.add (continuous_id.smul continuous_const)
          have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ),
              m (w + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ∈ U := by
            refine (hmc.comp hline).continuousAt.eventually_mem (hU.mem_nhds ?_)
            simpa using hw
          filter_upwards [hev] with ζ hζ
          have hl : DifferentiableAt ℂ
              (fun ζ : ℂ => w + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ :=
            (differentiableAt_const _).add (differentiableAt_id.smul_const _)
          have hc : DifferentiableAt ℂ matrixEquivLinear
              (F (m (w + ζ • Coordinates.ComplexCoordinates.stdBasisVector j))) :=
            (matrixEquivLinear.toContinuousLinearMap).differentiableAt
          have hd : DifferentiableAt ℂ
              (fun ζ : ℂ => F (m (w + ζ • Coordinates.ComplexCoordinates.stdBasisVector j))) ζ :=
            (hF _ hζ).differentiableAt.comp ζ ((hmd _).comp ζ hl)
          exact hc.comp ζ hd
theorem isAnalyticOnSubspace_of_analyticOn {S S' : Type} [Fintype S]
    {E : Submodule ℝ (S → ComplexMatrix2)} {E' : Submodule ℝ (S' → ComplexMatrix2)} [Fintype S']
    (hE : E ≤ hermitianTracelessFunctions S) (hE' : E' ≤ hermitianTracelessFunctions S')
    {U : Set (S → ComplexMatrix2)} (hU : IsOpen U) (f : (S → ComplexMatrix2) → S' → ComplexMatrix2)
    (hf : ∀ X ∈ U, AnalyticAt ℂ f X) (hsl : ∀ X k, f X k ∈ ComplexMatrix2.traceless)
    (hmaps : MapsTo f (U ∩ E) E') : IsAnalyticOnSubspace E E' (U ∩ E) f := by
  have hal := continuous_algebraComponent (S := S)
  have hopen : {q : Empty ⊕ S → ComplexMatrix2 | algebraComponent q ∈ U ∩ E} =
      (algebraComponent ⁻¹' U) ∩ subspaceTimesGroup E Empty := by
    ext q
    exact ⟨fun h => ⟨h.1, h.2, fun i => i.elim⟩, fun h => ⟨h.1, h.2.1⟩⟩
  refine ⟨⟨hE, _, hU.preimage hal, hopen⟩, hE', ?_, fun p hp => ?_⟩
  · intro q hq
    exact ⟨hmaps hq, fun i => i.elim⟩
  · have hpG : p ∈ GroupLieProduct Empty S := by
      intro q
      rcases q with q | q
      · exact q.elim
      · exact mem_tracelessPi_of_hermitian (hE hp.2) q
    have hop : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty S)
        (algebraComponent ⁻¹' U ∩ GroupLieProduct Empty S) := ⟨_, hU.preimage hal, rfl⟩
    refine ⟨algebraComponent ⁻¹' U ∩ GroupLieProduct Empty S, ⟨hp.1, hpG⟩, hop, ?_,
      fun q => ofParts Empty.elim (f (algebraComponent q)), fun b => ?_, fun _ _ => rfl⟩
    · rintro q ⟨⟨hq, -⟩, hq', -⟩
      exact ⟨hq, hq'⟩
    · refine ⟨hop, fun i => i.elim, fun k => ⟨fun q _ => hsl _ k, ?_⟩⟩
      exact isHolomorphicToCoords_of_analyticOn b hU (fun X => f X k)
        fun X hX => analyticAt_pi_iff.1 (hf X hX) k
theorem implicitFunctionStatement_holds
    (h₁ : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h₂ : ComplexMatrix2.DifferentiableOnFamiliesAnalytic) : ImplicitFunctionStatement := by
  intro S S' _ _ O Φ h0 hΦ hΦ0 hsurj
  obtain ⟨⟨-, -⟩, -, hmaps, hloc⟩ := hΦ
  obtain ⟨𝒳, hp, ⟨U, hU, rfl⟩, h𝒳sub, Ψ, hΨ, hEq⟩ := hloc 0 h0
  obtain ⟨b⟩ := traceless_basis_nonempty
  set V := hermitianTracelessFunctions S with hVdef
  set W := hermitianTracelessFunctions S' with hWdef
  let G : (S → ComplexMatrix2) → S' → ComplexMatrix2 := fun Z k =>
    Ψ (inclAlgebra (tracelessPart Z)) (.inr k)
  let N : Set (S → ComplexMatrix2) := inclAlgebra ⁻¹' U
  have hNo : IsOpen N := hU.preimage continuous_inclAlgebra
  have hN0 : (0 : S → ComplexMatrix2) ∈ N := by
    show inclAlgebra 0 ∈ U
    rw [map_zero]
    exact hp.1
  have hGeq : ∀ Z ∈ N, Z ∈ V → Z ∈ O ∧ G Z = Φ Z ∧ Φ Z ∈ W := by
    intro Z hZ hZV
    have hZa := mem_tracelessPi_of_hermitian hZV
    have hZ𝒳 : inclAlgebra Z ∈ (U ∩ GroupLieProduct Empty S) ∩ subspaceTimesGroup V Empty :=
      ⟨⟨hZ, fun q => by
        rcases q with q | q
        · exact q.elim
        · exact hZa q⟩, hZV, fun i => i.elim⟩
    have hZO : Z ∈ O := h𝒳sub hZ𝒳
    have hval := hEq hZ𝒳
    refine ⟨hZO, ?_, (hmaps (show inclAlgebra Z ∈ _ from hZO)).1⟩
    funext k
    show Ψ (inclAlgebra (tracelessPart Z)) (.inr k) = Φ Z k
    rw [tracelessPart_of_mem hZa, hval]
    rfl
  have hGa : AnalyticAt ℂ G 0 := by
    refine analyticAt_pi_iff.2 fun k => ?_
    exact analyticAt_of_isHolomorphicToCoords h₁ h₂ b (fun p => Ψ p (.inr k)) hp
      ((hΨ b).2.2 k).2
  have G0 : G 0 = 0 := by
    rw [(hGeq 0 hN0 V.zero_mem).2.1, hΦ0]
  set D := fderiv ℂ G 0 with hDdef
  have hG : HasFDerivAt G D 0 := hGa.differentiableAt.hasFDerivAt
  have hderiv : ∀ X ∈ V, HasDerivAt (fun t : ℝ => Φ (t • X)) (D X) 0 := by
    intro X hX
    have hline : HasDerivAt (fun t : ℝ => t • X) X 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
    have hG' : HasFDerivAt G (D.restrictScalars ℝ) ((0 : ℝ) • X) := by
      rw [zero_smul]
      exact hG.restrictScalars ℝ
    have hc := hG'.comp_hasDerivAt (0 : ℝ) hline
    refine HasDerivAt.congr_of_eventuallyEq hc ?_
    have ht : ContinuousAt (fun t : ℝ => t • X) 0 := hline.continuousAt
    have hev : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ N := by
      refine ht.eventually_mem (hNo.mem_nhds ?_)
      simpa using hN0
    filter_upwards [hev] with t htN
    exact ((hGeq _ htN (V.smul_mem t hX)).2.1).symm
  have hWclosed : IsClosed (W : Set (S' → ComplexMatrix2)) := Submodule.closed_of_finiteDimensional W
  have hD : ∀ X ∈ V, D X ∈ W := by
    intro X hX
    have hs := (hderiv X hX).tendsto_slope_zero
    refine hWclosed.mem_of_tendsto hs ?_
    have ht : ContinuousAt (fun t : ℝ => (0 + t) • X) 0 := by fun_prop
    have hev : ∀ᶠ t : ℝ in 𝓝 0, (0 + t) • X ∈ N := by
      refine ht.eventually_mem (hNo.mem_nhds ?_)
      simpa using hN0
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with t htN
    have hmem := (hGeq _ htN (V.smul_mem _ hX)).2.2
    simp only [zero_smul, hΦ0, sub_zero]
    exact W.smul_mem _ hmem
  let Dr : V →ₗ[ℝ] W := ((D.restrictScalars ℝ : (S → ComplexMatrix2) →L[ℝ] S' → ComplexMatrix2) :
    (S → ComplexMatrix2) →ₗ[ℝ] S' → ComplexMatrix2).restrict hD
  have hDr : ∀ x : V, (Dr x : S' → ComplexMatrix2) = D x := fun _ => rfl
  have hrange : LinearMap.range Dr = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Y, hY⟩
    obtain ⟨X, hX, hXY⟩ := hsurj Y hY
    refine ⟨⟨X, hX⟩, Subtype.ext ?_⟩
    show D X = Y
    rw [← hXY]
    exact (hderiv X hX).deriv.symm
  obtain ⟨r, hr⟩ := Dr.exists_rightInverse_of_surjective hrange
  have hrr : ∀ y : W, D (r y : S → ComplexMatrix2) = y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun hr y)
  let ρ : (S' → ComplexMatrix2) →ₗ[ℝ] W := LinearMap.codRestrict W
    (LinearMap.pi fun k => hermitianTracelessPart ∘ₗ LinearMap.proj k)
    fun Y k _ => hermitianTracelessPart_mem (Y k)
  have hρ : ∀ Y (hY : Y ∈ W), ρ Y = ⟨Y, hY⟩ := by
    intro Y hY
    refine Subtype.ext ?_
    funext k
    exact hermitianTracelessPart_of_mem (hY k (mem_univ k))
  have hρI : ∀ Y ∈ W, ρ (-Complex.I • Y) = 0 := by
    intro Y hY
    refine Subtype.ext ?_
    funext k
    exact hermitianTracelessPart_neg_I_smul (hY k (mem_univ k))
  let Q : (S' → ComplexMatrix2) →ₗ[ℝ] (S → ComplexMatrix2) := V.subtype ∘ₗ r ∘ₗ ρ
  let R : (S' → ComplexMatrix2) →L[ℂ] (S → ComplexMatrix2) :=
    (complexifyLinear Q).toContinuousLinearMap
  have hRval : ∀ Y, R Y = Q Y + Complex.I • Q (-Complex.I • Y) := fun _ => rfl
  have hRW : ∀ Y (hY : Y ∈ W), R Y = (r ⟨Y, hY⟩ : S → ComplexMatrix2) := by
    intro Y hY
    have hq : Q Y = (r ⟨Y, hY⟩ : S → ComplexMatrix2) := by
      show ((r (ρ Y)) : S → ComplexMatrix2) = _
      rw [hρ Y hY]
    have hq' : Q (-Complex.I • Y) = 0 := by
      show ((r (ρ (-Complex.I • Y))) : S → ComplexMatrix2) = 0
      rw [hρI Y hY, map_zero]
      rfl
    rw [hRval, hq, hq', smul_zero, add_zero]
  have hR : ∀ Y ∈ W, R Y ∈ V := fun Y hY => by
    rw [hRW Y hY]
    exact (r ⟨Y, hY⟩).2
  have hDR : ∀ Y ∈ W, D (R Y) = Y := fun Y hY => by
    rw [hRW Y hY]
    exact hrr ⟨Y, hY⟩
  have hRsl : ∀ Y k, R Y k ∈ ComplexMatrix2.traceless := by
    intro Y k
    have hQ : ∀ Y, Q Y ∈ tracelessPi S := fun Y => mem_tracelessPi_of_hermitian (r (ρ Y)).2
    rw [hRval]
    exact ComplexMatrix2.traceless.add_mem (hQ Y k) (ComplexMatrix2.traceless.smul_mem _ (hQ _ k))
  have hVev : ∀ᶠ Z in 𝓝 (0 : S → ComplexMatrix2), Z ∈ V → G Z ∈ W := by
    filter_upwards [hNo.mem_nhds hN0] with Z hZ hZV
    obtain ⟨-, h₂', h₃⟩ := hGeq Z hZ hZV
    rwa [h₂']
  obtain ⟨U₁, U₂, g, hU₁, hU₂, h0₁, h0₂, hiff, hmapsF, g0, ga, gd⟩ :=
    zeroSet_local_graph V W G R D hG hGa G0 hVev hR hD hDR N (hNo.mem_nhds hN0)
  have hEV : realKernel V D ≤ V := fun X hX => (mem_realKernel.1 hX).1
  have hE'V : realImage W R ≤ V := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := mem_realImage.1 hX
    exact hR Y hY
  let f : (S → ComplexMatrix2) → S → ComplexMatrix2 := fun X => R (D (g X))
  have hfa : ∀ X ∈ U₁, AnalyticAt ℂ f X := fun X hX =>
    ((R.comp D).analyticAt _).comp (ga X hX)
  have hf0 : HasFDerivAt f (R.comp D) 0 := by
    have h := (R.comp D).hasFDerivAt (x := g 0)
    exact (h.comp (0 : S → ComplexMatrix2) gd).congr_fderiv (by ext; simp)
  refine ⟨realKernel V D, realImage W R, U₁ ∩ realKernel V D, U₂ ∩ realImage W R, f,
    realKernel_sup_realImage hR hD hDR,
    realKernel_inf_realImage hDR, ?_, ⟨U₁, hU₁, rfl⟩, ⟨U₂, hU₂, rfl⟩, ⟨h0₁, Submodule.zero_mem _⟩,
    ⟨h0₂, Submodule.zero_mem _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    rw [mem_realKernel]
    exact ⟨fun h => ⟨h.1, (hderiv X h.1).deriv.trans h.2⟩,
      fun h => ⟨h.1, (hderiv X h.1).deriv.symm.trans h.2⟩⟩
  · rintro X ⟨hX, hXE⟩ X' ⟨hX', hXE'⟩
    obtain ⟨hN', hi⟩ := hiff X hX hXE X' hX' hXE'
    obtain ⟨hO, hGΦ, -⟩ := hGeq _ hN' (V.add_mem (hEV hXE) (hE'V hXE'))
    exact ⟨hO, by rw [← hGΦ]; exact hi⟩
  · rintro X ⟨hX, hXE⟩
    exact hmapsF X hX hXE
  · show R (D (g 0)) = 0
    rw [g0, map_zero, map_zero]
  · exact isAnalyticOnSubspace_of_analyticOn hEV hE'V hU₁ f hfa (fun X k => hRsl _ k)
      fun X hX => (hmapsF _ hX.1 hX.2).2
  · intro d ι hι u hu
    have hX : ι u ∈ U₁ := hu.1
    have c₁ : ContDiffAt ℂ ω f (ι u) := (hfa _ hX).contDiffAt
    have c₂ : ContDiffAt ℝ ∞ f (ι u) := (c₁.restrict_scalars ℝ).of_le le_top
    exact (c₂.comp u ι.contDiff.contDiffAt).contDiffWithinAt
  · intro X hX
    have hline : HasDerivAt (fun t : ℝ => t • X) X 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
    have hf' : HasFDerivAt f ((R.comp D).restrictScalars ℝ) ((0 : ℝ) • X) := by
      rw [zero_smul]
      exact hf0.restrictScalars ℝ
    have hc := hf'.comp_hasDerivAt (0 : ℝ) hline
    have he : ((R.comp D).restrictScalars ℝ) X = 0 := by
      simp [(mem_realKernel.1 hX).2]
    rw [he] at hc
    exact hc
end RealForm
end Subspaces
end GroupLieProduct
end Matrices
end YangMills.Construction
