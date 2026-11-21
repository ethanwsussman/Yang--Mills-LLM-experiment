import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiableHolds
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBond
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscsProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AsDifferentials
section Taylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
theorem taylor_quadratic_remainder (H : E → F) (hH : ContDiffAt ℂ 3 H 0) :
    IsSymmSndFDerivAt ℂ H 0 ∧ ∃ K δ : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ z : E, ‖z‖ < δ →
      ‖H z - H 0 - fderiv ℂ H 0 z - (1 / 2 : ℂ) • fderiv ℂ (fderiv ℂ H) 0 z z‖ ≤ K * ‖z‖ ^ 3 := by
  have hsym : IsSymmSndFDerivAt ℂ H 0 :=
    hH.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
  refine ⟨hsym, ?_⟩
  set G := fderiv ℂ H with hGdef
  set G2 := fderiv ℂ G with hG2def
  have hG : ContDiffAt ℂ 2 G 0 := hH.fderiv_right (m := 2) (by norm_num)
  have hG2 : ContDiffAt ℂ 1 G2 0 := hG.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hG2.exists_lipschitzOnWith
  have h1 : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℂ H w := by
    have := hH.eventually (by simp)
    filter_upwards [this] with w hw
    exact hw.differentiableAt (by norm_num)
  have h2 : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℂ G w := by
    have := hG.eventually (by simp)
    filter_upwards [this] with w hw
    exact hw.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((h1.and h2).and ht)
  refine ⟨K, δ, hδ, K.2, fun z hz => ?_⟩
  have hmem : ∀ w : E, ‖w‖ ≤ ‖z‖ → w ∈ Metric.ball (0 : E) δ := fun w hw => by
    simpa using lt_of_le_of_lt hw hz
  have h0t : (0 : E) ∈ t := (hball 0 (Metric.mem_ball_self hδ)).2
  have hb2 : ∀ w : E, ‖w‖ ≤ ‖z‖ → ‖G2 w - G2 0‖ ≤ K * ‖z‖ := fun w hw => by
    have := hK.dist_le_mul w (hball w (hmem w hw)).2 0 h0t
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hw K.2)
  let e : E → E →L[ℂ] F := fun w => G w - G 0 - G2 0 w
  have he : ∀ w : E, ‖w‖ ≤ ‖z‖ → HasFDerivAt e (G2 w - G2 0) w := fun w hw => by
    have := (hball w (hmem w hw)).1.2.hasFDerivAt
    exact (this.sub_const (G 0)).sub (G2 0).hasFDerivAt
  have hb1 : ∀ w : E, ‖w‖ ≤ ‖z‖ → ‖e w‖ ≤ K * ‖z‖ * ‖w‖ := fun w hw => by
    have hconv : Convex ℝ (Metric.closedBall (0 : E) ‖w‖) := convex_closedBall _ _
    have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := e)
      (f' := fun v => G2 v - G2 0) (C := K * ‖z‖) (x := 0) (y := w)
      (fun v hv => by
        have hv' : ‖v‖ ≤ ‖w‖ := by simpa using hv
        exact (he v (hv'.trans hw)).hasFDerivWithinAt)
      (fun v hv => by
        have hv' : ‖v‖ ≤ ‖w‖ := by simpa using hv
        exact hb2 v (hv'.trans hw))
      (by simp) (by simp)
    have he0 : e 0 = 0 := by simp [e]
    simpa [he0] using this
  let B : E →L[ℂ] E →L[ℂ] F := G2 0
  let r : E → F := fun w => H w - H 0 - G 0 w - (1 / 2 : ℂ) • B w w
  have hr : ∀ w : E, ‖w‖ ≤ ‖z‖ → HasFDerivAt r (e w) w := fun w hw => by
    have hH' := (hball w (hmem w hw)).1.1.hasFDerivAt
    have hq : HasFDerivAt (fun y => B y y)
        (B.precompR E w (ContinuousLinearMap.id ℂ E) +
          B.precompL E (ContinuousLinearMap.id ℂ E) w) w :=
      B.hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)
    have := ((hH'.sub_const (H 0)).sub (G 0).hasFDerivAt).sub (hq.const_smul (1 / 2 : ℂ))
    refine this.congr_fderiv ?_
    ext v
    have hs : B v w = B w v := hsym v w
    have e1 : (B.precompR E w (ContinuousLinearMap.id ℂ E)) v = B w v := rfl
    have e2 : (B.precompL E (ContinuousLinearMap.id ℂ E) w) v = B v w := rfl
    have e3 : (1 / 2 : ℂ) • (B w v + B w v) = B w v := by
      rw [← two_smul ℂ (B w v), smul_smul]; norm_num
    show fderiv ℂ H w v - G 0 v - (1 / 2 : ℂ) • ((B.precompR E w (ContinuousLinearMap.id ℂ E)) v +
      (B.precompL E (ContinuousLinearMap.id ℂ E) w) v) = G w v - G 0 v - B w v
    rw [e1, e2, hs, e3]
  have hconv : Convex ℝ (Metric.closedBall (0 : E) ‖z‖) := convex_closedBall _ _
  have hfin := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := r)
      (f' := e) (C := K * ‖z‖ * ‖z‖) (x := 0) (y := z)
      (fun v hv => by
        have hv' : ‖v‖ ≤ ‖z‖ := by simpa using hv
        exact (hr v hv').hasFDerivWithinAt)
      (fun v hv => by
        have hv' : ‖v‖ ≤ ‖z‖ := by simpa using hv
        exact (hb1 v hv').trans
          (mul_le_mul_of_nonneg_left hv' (mul_nonneg K.2 (norm_nonneg _))))
      (by simp) (by simp)
  have hr0 : r 0 = 0 := by simp [r]
  have : ‖r z‖ ≤ K * ‖z‖ * ‖z‖ * ‖z‖ := by simpa [hr0] using hfin
  calc _ = ‖r z‖ := rfl
    _ ≤ _ := this
    _ = K * ‖z‖ ^ 3 := by ring
end Taylor
section Tuples
variable {σ : Type} [Fintype σ]
omit [Fintype σ] in
theorem mem_tracelessPi_iff {A : σ → ComplexMatrix2} :
    A ∈ tracelessPi σ ↔ ∀ s, A s ∈ ComplexMatrix2.traceless := by
  simp [tracelessPi, ComplexMatrix2.complexifiedProduct, ComplexMatrix2.FactorKind.complexified]
theorem supNorm_eq_norm (A : σ → ComplexMatrix2) : supNorm A = ‖A‖ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.supNorm_eq_norm <;> assumption
def tracelessProj : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := X - ComplexMatrix2.halfTrace X • (1 : ComplexMatrix2)
  map_add' X Y := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add]
    module
  map_smul' z X := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply]
    module
theorem tracelessProj_mem (X : ComplexMatrix2) : tracelessProj X ∈ ComplexMatrix2.traceless := by
  show ComplexMatrix2.fullTrace (X - ComplexMatrix2.halfTrace X • (1 : ComplexMatrix2)) = 0
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring
theorem tracelessProj_of_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    tracelessProj X = X := by
  have h : ComplexMatrix2.fullTrace X = 0 := hX
  show X - ComplexMatrix2.halfTrace X • (1 : ComplexMatrix2) = X
  simp [ComplexMatrix2.halfTrace, h]
def tracelessPiProj (σ : Type) [Fintype σ] :
    (σ → ComplexMatrix2) →L[ℂ] ↥(tracelessPiSubmodule σ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ⟨fun s => tracelessProj (A s), fun s _ => tracelessProj_mem _⟩
      map_add' := fun A B => by ext1; funext s; simp
      map_smul' := fun z A => by ext1; funext s; simp }
theorem tracelessPiProj_of_mem {A : σ → ComplexMatrix2} (hA : A ∈ tracelessPi σ) :
    ((tracelessPiProj σ A : ↥(tracelessPiSubmodule σ)) : σ → ComplexMatrix2) = A := by
  funext s
  exact tracelessProj_of_mem (mem_tracelessPi_iff.1 hA s)
omit [Fintype σ] in
theorem tracelessPi_add {A B : σ → ComplexMatrix2} (hA : A ∈ tracelessPi σ)
    (hB : B ∈ tracelessPi σ) : A + B ∈ tracelessPi σ :=
  mem_tracelessPi_iff.2 fun s =>
    ComplexMatrix2.traceless.add_mem (mem_tracelessPi_iff.1 hA s) (mem_tracelessPi_iff.1 hB s)
omit [Fintype σ] in
theorem tracelessPi_smul (z : ℂ) {A : σ → ComplexMatrix2} (hA : A ∈ tracelessPi σ) :
    z • A ∈ tracelessPi σ :=
  mem_tracelessPi_iff.2 fun s => ComplexMatrix2.traceless.smul_mem z (mem_tracelessPi_iff.1 hA s)
structure QuadraticTaylorData (O : Set (σ → ComplexMatrix2)) (h : (σ → ComplexMatrix2) → ComplexMatrix2)
    (D : (σ → ComplexMatrix2) →L[ℂ] ComplexMatrix2)
    (Q : (σ → ComplexMatrix2) →L[ℂ] (σ → ComplexMatrix2) →L[ℂ] ComplexMatrix2) : Prop where
  ball_subset : ∃ δ : ℝ, 0 < δ ∧ ∀ A ∈ tracelessPi σ, supNorm A < δ → A ∈ O
  hasDerivAt_line : ∀ A ∈ tracelessPi σ, HasDerivAt (fun t : ℂ => h (t • A)) (D A) 0
  symm : ∀ A A' : σ → ComplexMatrix2, Q A A' = Q A' A
  mixed_deriv : ∀ A ∈ tracelessPi σ, ∀ A' ∈ tracelessPi σ,
    deriv (fun s : ℂ => deriv (fun t : ℂ => h (s • A + t • A')) 0) 0 = Q A A'
  remainder : ∃ K δ : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ A ∈ tracelessPi σ, supNorm A < δ →
    ComplexMatrix2.operatorNorm (h A - h 0 - D A - (1 / 2 : ℂ) • Q A A) ≤ K * supNorm A ^ 3
  mem_traceless : MapsTo h O (ComplexMatrix2.traceless : Set ComplexMatrix2) →
    ∀ A ∈ tracelessPi σ,
    D A ∈ ComplexMatrix2.traceless ∧ ∀ A' ∈ tracelessPi σ, Q A A' ∈ ComplexMatrix2.traceless
theorem matrixEquiv_isLinearMap : IsLinearMap ℂ Coordinates.ComplexCoordinates.matrixEquiv :=
  ⟨fun X Y => by ext k; simp [Coordinates.ComplexCoordinates.matrixEquiv],
    fun z X => by ext k; simp [Coordinates.ComplexCoordinates.matrixEquiv]⟩
def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
theorem exists_quadraticTaylorData
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {O : Set (σ → ComplexMatrix2)}
    {h : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hh : IsHolomorphicOnTraceless b Coordinates.ComplexCoordinates.matrixEquiv O h)
    (h0 : (0 : σ → ComplexMatrix2) ∈ O) :
    ∃ D Q, QuadraticTaylorData O h D Q := by
  classical
  have hd := ((hT σ ComplexMatrix2 4 b Coordinates.ComplexCoordinates.matrixEquiv
    matrixEquiv_isLinearMap O h).1 hh).2
  have hopen : IsOpen (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ)) := by
    refine Metric.isOpen_iff.2 fun A hA' => ?_
    obtain ⟨s, hs, hb⟩ := hh.1.2 A hA'
    refine ⟨s, hs, fun B hB => hb B ?_ ?_⟩
    · exact mem_tracelessPi_iff.2 fun i => B.2 i (mem_univ i)
    · rw [supNorm_eq_norm]
      simpa [dist_eq_norm] using hB
  let P := tracelessPiProj σ
  let O₁ : Set (σ → ComplexMatrix2) := P ⁻¹' (Subtype.val ⁻¹' O)
  have hO₁ : IsOpen O₁ := hopen.preimage P.continuous
  let H : (σ → ComplexMatrix2) → ComplexMatrix2 := fun A => h (P A : σ → ComplexMatrix2)
  have hH : DifferentiableOn ℂ H O₁ :=
    hd.comp P.differentiable.differentiableOn fun A hA' => hA'
  have hz : (0 : σ → ComplexMatrix2) ∈ O₁ := by
    show ((P 0 : ↥(tracelessPiSubmodule σ)) : σ → ComplexMatrix2) ∈ O
    simpa using h0
  have hc : ContDiffAt ℂ 3 H 0 := (hA σ O₁ H hO₁ hH 0 hz).contDiffAt
  obtain ⟨hsym, K, δ, hδ, hK, hb⟩ := taylor_quadratic_remainder H hc
  have hHA : ∀ A ∈ tracelessPi σ, H A = h A := fun A hA' => by
    show h (P A : σ → ComplexMatrix2) = h A
    rw [tracelessPiProj_of_mem hA']
  have h0alg : (0 : σ → ComplexMatrix2) ∈ tracelessPi σ :=
    mem_tracelessPi_iff.2 fun _ => ComplexMatrix2.traceless.zero_mem
  have hdiff : ∀ᶠ w in 𝓝 (0 : σ → ComplexMatrix2), DifferentiableAt ℂ H w := by
    filter_upwards [hc.eventually (by simp)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hG : ContDiffAt ℂ 2 (fderiv ℂ H) 0 := hc.fderiv_right (m := 2) (by norm_num)
  have hderG : HasFDerivAt (fderiv ℂ H) (fderiv ℂ (fderiv ℂ H) 0) 0 :=
    (hG.differentiableAt (by norm_num)).hasFDerivAt
  have hderH : HasFDerivAt H (fderiv ℂ H 0) 0 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hline : ∀ A : σ → ComplexMatrix2, HasDerivAt (fun t : ℂ => t • A) A 0 := fun A => by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const A
  have hline0 : ∀ A : σ → ComplexMatrix2, Tendsto (fun t : ℂ => t • A) (𝓝 0) (𝓝 0) := fun A => by
    have := (hline A).continuousAt.tendsto
    simpa using this
  have hfirst : ∀ A : σ → ComplexMatrix2,
      HasDerivAt (fun t : ℂ => H (t • A)) (fderiv ℂ H 0 A) 0 :=
    fun A => by
      have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hderH (hline A) (by simp)
      exact this
  have hg : ∀ A A' : σ → ComplexMatrix2, HasDerivAt (fun s : ℂ => fderiv ℂ H (s • A) A')
      (fderiv ℂ (fderiv ℂ H) 0 A A') 0 := fun A A' => by
    have h₁ : HasDerivAt (fun s : ℂ => fderiv ℂ H (s • A)) (fderiv ℂ (fderiv ℂ H) 0 A) 0 := by
      have hderG' : HasFDerivAt (fderiv ℂ H) (fderiv ℂ (fderiv ℂ H) 0) ((0 : ℂ) • A) := by
        simpa using hderG
      have := HasFDerivAt.comp_hasDerivAt (E := (σ → ComplexMatrix2) →L[ℂ] ComplexMatrix2)
        (F := σ → ComplexMatrix2) (0 : ℂ) hderG' (hline A)
      exact this
    exact h₁.clm_apply (hasDerivAt_const _ _) |>.congr_deriv (by simp)
  have hinner : ∀ A A' : σ → ComplexMatrix2, ∀ᶠ s : ℂ in 𝓝 0,
      HasDerivAt (fun t : ℂ => H (s • A + t • A')) (fderiv ℂ H (s • A) A') 0 := fun A A' => by
    filter_upwards [(hline0 A).eventually hdiff] with s hs
    have hl : HasDerivAt (fun t : ℂ => s • A + t • A') A' 0 :=
      (hline A').const_add (s • A)
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hs.hasFDerivAt hl (by simp)
    exact this
  refine ⟨fderiv ℂ H 0, fderiv ℂ (fderiv ℂ H) 0, ?_, ?_, fun A A' => hsym A A', ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hball⟩ := hh.1.2 0 h0
    exact ⟨s, hs, fun A hA' hn => hball A hA' (by simpa using hn)⟩
  · intro A hA'
    refine (hfirst A).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact (hHA _ (tracelessPi_smul t hA')).symm
  · intro A hA' A' hA''
    have heq : (fun s : ℂ => deriv (fun t : ℂ => h (s • A + t • A')) 0) =ᶠ[𝓝 0]
        fun s : ℂ => fderiv ℂ H (s • A) A' := by
      filter_upwards [hinner A A'] with s hs
      have : (fun t : ℂ => h (s • A + t • A')) = fun t : ℂ => H (s • A + t • A') := by
        funext t
        exact (hHA _ (tracelessPi_add (tracelessPi_smul s hA') (tracelessPi_smul t hA''))).symm
      rw [this]
      exact hs.deriv
    rw [heq.deriv_eq]
    exact (hg A A').deriv
  · refine ⟨K, δ, hδ, hK, fun A hA' hn => ?_⟩
    rw [supNorm_eq_norm] at hn ⊢
    have := hb A hn
    rwa [hHA A hA', hHA 0 h0alg] at this
  · intro hmaps A hA'
    have hzero : ∀ᶠ w in 𝓝 (0 : σ → ComplexMatrix2), traceCLM (H w) = 0 := by
      filter_upwards [hO₁.mem_nhds hz] with w hw
      exact hmaps hw
    have hT0 : ∀ (f : ℂ → ComplexMatrix2) (v : ComplexMatrix2), HasDerivAt f v 0 →
        (∀ᶠ t : ℂ in 𝓝 0, traceCLM (f t) = 0) → traceCLM v = 0 := fun f v hf he => by
      have h₁ : HasDerivAt (fun t => traceCLM (f t)) (traceCLM v) 0 :=
        traceCLM.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hf
      have h₂ : HasDerivAt (fun t => traceCLM (f t)) 0 0 :=
        (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq he
      exact h₁.unique h₂
    refine ⟨hT0 _ _ (hfirst A) ((hline0 A).eventually hzero), fun A' hA'' => ?_⟩
    refine hT0 _ _ (hg A A') ?_
    have hopen₂ : ∀ᶠ s : ℂ in 𝓝 0, s • A ∈ O₁ := (hline0 A).eventually (hO₁.mem_nhds hz)
    filter_upwards [hinner A A', hopen₂] with s hs hso
    have hl : Tendsto (fun t : ℂ => s • A + t • A') (𝓝 0) (𝓝 (s • A)) := by
      have := (hline0 A').const_add (s • A)
      simpa using this
    have hev : ∀ᶠ t : ℂ in 𝓝 0, traceCLM (H (s • A + t • A')) = 0 := by
      filter_upwards [hl.eventually (hO₁.mem_nhds hso)] with t ht
      exact hmaps ht
    exact hT0 _ _ hs hev
end Tuples
section Charts
open YangMills.Construction.Tower.DoubleBlockPolydisc (leftComponents)
variable {σ τ : Type} [Fintype σ] [Fintype τ]
omit [Fintype σ] in
theorem isOpen_of_isSupOpen [Fintype σ] {O : Set (σ → ComplexMatrix2)} (hO : IsSupOpen O) :
    IsOpen (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ)) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.isOpen_subtype_of_isSupOpen <;> assumption
theorem isSupOpen_of_isOpen {O : Set (σ → ComplexMatrix2)} (hs : O ⊆ tracelessPi σ)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ))) : IsSupOpen O := by
  refine ⟨hs, fun A hA => ?_⟩
  have hAm : A ∈ tracelessPiSubmodule σ := fun i _ => mem_tracelessPi_iff.1 (hs hA) i
  obtain ⟨s, hs', hb⟩ := Metric.isOpen_iff.1 hO ⟨A, hAm⟩ hA
  refine ⟨s, hs', fun B hB hn => ?_⟩
  have hBm : B ∈ tracelessPiSubmodule σ := fun i _ => mem_tracelessPi_iff.1 hB i
  refine hb (a := ⟨B, hBm⟩) ?_
  rw [supNorm_eq_norm] at hn
  simpa [dist_eq_norm] using hn
def expChartFamily (ε : σ ≃ τ) (u : τ → ComplexMatrix2) (A : σ → ComplexMatrix2) :
    τ → ComplexMatrix2 :=
  fun t => ComplexMatrix2.matExp (Complex.I • A (ε.symm t)) * u t
def expChartLog (ε : σ ≃ τ) (Φ : (τ → ComplexMatrix2) → ComplexMatrix2) (u : τ → ComplexMatrix2)
    (A : σ → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (expChartFamily ε u A) * (Φ u)⁻¹)
structure ExpChartLogData (ε : σ ≃ τ) (𝔇 : Set (τ → ComplexMatrix2))
    (Φ : (τ → ComplexMatrix2) → ComplexMatrix2) (u : τ → ComplexMatrix2)
    (O : Set (σ → ComplexMatrix2)) : Prop where
  zero_mem : (0 : σ → ComplexMatrix2) ∈ O
  holomorphic : ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    IsHolomorphicOnTraceless b Coordinates.ComplexCoordinates.matrixEquiv O (expChartLog ε Φ u)
  mem_traceless : MapsTo (expChartLog ε Φ u) O (ComplexMatrix2.traceless : Set ComplexMatrix2)
  family_mem : ∀ A ∈ O, expChartFamily ε u A ∈ 𝔇
  norm_sub_one_lt : ∀ A ∈ O,
    ComplexMatrix2.operatorNorm (Φ (expChartFamily ε u A) * (Φ u)⁻¹ - 1) < 1
  isUnit : IsUnit (Φ u)
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
omit [Fintype σ] [Fintype τ] in
theorem expChartFamily_zero (ε : σ ≃ τ) (u : τ → ComplexMatrix2) : expChartFamily ε u 0 = u := by
  funext t
  simp [expChartFamily, ComplexMatrix2.matExp]
omit [Fintype σ] [Fintype τ] in
theorem expChartLog_zero (ε : σ ≃ τ) (Φ : (τ → ComplexMatrix2) → ComplexMatrix2)
    {u : τ → ComplexMatrix2} (hu : IsUnit (Φ u)) : expChartLog ε Φ u 0 = 0 := by
  have : Φ u * (Φ u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  simp [expChartLog, expChartFamily_zero, this, logSeries_one]
theorem mul_inv_mem_unitDeterminant {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.unitDeterminant)
    (hY : Y ∈ ComplexMatrix2.unitDeterminant) : X * Y⁻¹ ∈ ComplexMatrix2.unitDeterminant := by
  have hX' : X.det = 1 := hX
  have hY' : Y.det = 1 := hY
  show (X * Y⁻¹).det = 1
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, hX', hY']
  simp
def expChartArg (ε : σ ≃ τ) (A : σ → ComplexMatrix2) : τ ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun t => Complex.I • A (ε.symm t)) Empty.elim
def expChartArgCLM (ε : σ ≃ τ) :
    ↥(tracelessPiSubmodule σ) →L[ℂ] ↥(tracelessPiSubmodule (τ ⊕ Empty)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ⟨expChartArg ε A,
        fun s _ => by
          rcases s with t | e
          · exact ComplexMatrix2.traceless.smul_mem _ (A.2 _ (mem_univ _))
          · exact e.elim⟩
      map_add' := fun A B => by
        ext1
        funext s
        rcases s with t | e
        · simp [expChartArg, smul_add]
        · exact e.elim
      map_smul' := fun z A => by
        ext1
        funext s
        rcases s with t | e
        · simp [expChartArg, smul_comm z Complex.I]
        · exact e.elim }
omit [Fintype τ] in
theorem expChartArgCLM_coe (ε : σ ≃ τ) (A : ↥(tracelessPiSubmodule σ)) :
    ((expChartArgCLM ε A : ↥(tracelessPiSubmodule (τ ⊕ Empty))) : τ ⊕ Empty → ComplexMatrix2) =
      expChartArg ε A := rfl
omit [Fintype σ] [Fintype τ] in
theorem leftComponents_expChartAt (ε : σ ≃ τ) (u : τ → ComplexMatrix2) (A : σ → ComplexMatrix2) :
    leftComponents (expChartAt (Sum.elim u Empty.elim : τ ⊕ Empty → ComplexMatrix2)
      (expChartArg ε A)) = expChartFamily ε u A := by
  funext t
  rfl
set_option maxHeartbeats 1000000 in
theorem exists_expChartLogData
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hV : ComplexMeanLiesInComplexGaugeGroup) (ε : σ ≃ τ)
    {𝔇 : Set (τ → ComplexMatrix2)} {Φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    {u : τ → ComplexMatrix2} (hu : u ∈ 𝔇)
    {b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (hΦ : IsHolomorphicToUnimodular b₀ (leftComponents ⁻¹' 𝔇) (Φ ∘ leftComponents)) :
    ∃ O : Set (σ → ComplexMatrix2), ExpChartLogData ε 𝔇 Φ u O := by
  classical
  obtain ⟨-, hmaps, -, hloc⟩ := hΦ
  let p : τ ⊕ Empty → ComplexMatrix2 := Sum.elim u Empty.elim
  have hgp : leftComponents p = u := rfl
  have hp : p ∈ leftComponents ⁻¹' 𝔇 := by
    show leftComponents p ∈ 𝔇
    rwa [hgp]
  obtain ⟨O₀, h0, hO₀, hh⟩ := hloc p hp
  have hdiff := (hT (τ ⊕ Empty) ComplexMatrix2 4 b₀ Coordinates.ComplexCoordinates.matrixEquiv
    matrixEquiv_isLinearMap O₀ _).1 hh
  have hopen₀ := isOpen_of_isSupOpen hdiff.1
  let J := expChartArgCLM ε
  let O : Set (σ → ComplexMatrix2) := {A | A ∈ tracelessPiSubmodule σ ∧ expChartArg ε A ∈ O₀}
  have hOval : (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ)) =
      J ⁻¹' (Subtype.val ⁻¹' O₀) := by
    ext A
    exact ⟨fun h => h.2, fun h => ⟨A.2, h⟩⟩
  have hOsub : O ⊆ tracelessPi σ := fun A hA =>
    mem_tracelessPi_iff.2 fun i => hA.1 i (mem_univ i)
  have hOopen : IsSupOpen O :=
    isSupOpen_of_isOpen hOsub (by rw [hOval]; exact hopen₀.preimage J.continuous)
  have hmem : ∀ A ∈ O, expChartFamily ε u A ∈ 𝔇 ∧
      Φ (expChartFamily ε u A) ∈ ComplexMatrix2.unitDeterminant ∧
      Φ (expChartFamily ε u A) * (Φ u)⁻¹ ∈ ComplexMatrix2.logBall := fun A hA => by
    obtain ⟨h₁, h₂⟩ := hO₀ _ hA.2
    have e := leftComponents_expChartAt ε u A
    have h₃ := hmaps h₁
    simp only [mem_preimage, Function.comp_apply] at h₁ h₂ h₃
    change leftComponents (expChartAt p (expChartArg ε A)) = _ at e
    rw [e] at h₁ h₂ h₃
    rw [hgp] at h₂
    exact ⟨h₁, h₃, h₂⟩
  have hval : ∀ A ∈ O, expChartLog ε Φ u A ∈ ComplexMatrix2.traceless := fun A hA => by
    obtain ⟨-, hX, hq⟩ := hmem A hA
    have hY : Φ u ∈ ComplexMatrix2.unitDeterminant := hmaps hp
    exact ComplexMatrix2.traceless.smul_mem _ (hV.1 _ (mul_inv_mem_unitDeterminant hX hY) hq).2
  refine ⟨O, ?_, fun b => ?_, fun A hA => hval A hA, fun A hA => (hmem A hA).1,
    fun A hA => (hmem A hA).2.2, ?_⟩
  · refine ⟨Submodule.zero_mem _, ?_⟩
    have : expChartArg ε (0 : σ → ComplexMatrix2) = 0 := by
      funext s
      rcases s with t | e
      · simp [expChartArg]
      · exact e.elim
    rw [this]
    exact h0
  · refine (hT σ ComplexMatrix2 4 b Coordinates.ComplexCoordinates.matrixEquiv
      matrixEquiv_isLinearMap O _).2 ⟨hOopen, ?_⟩
    have hcomp := (hdiff.2.comp J.differentiable.differentiableOn
      (s := (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ))) (by rw [hOval]; exact fun A h => h))
    refine (hcomp.const_smul Complex.I⁻¹).congr fun A _ => ?_
    have e := leftComponents_expChartAt ε u (A : σ → ComplexMatrix2)
    change leftComponents (expChartAt p (expChartArg ε (A : σ → ComplexMatrix2))) = _ at e
    simp only [expChartLog, Pi.smul_apply, Function.comp_apply, expChartArgCLM_coe, J, e, hgp]
  · have hY : (Φ u).det = 1 := hmaps hp
    exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hY]; exact isUnit_one)
end Charts
section EvaluationMaps
variable {β γ : Type}
def restrictFinset (F : Finset β) (C : β → ComplexMatrix2) : F → ComplexMatrix2 := fun b => C b
theorem restrictFinset_add (F : Finset β) (C C' : β → ComplexMatrix2) :
    restrictFinset F (C + C') = restrictFinset F C + restrictFinset F C' := rfl
theorem restrictFinset_smul (F : Finset β) (z : ℂ) (C : β → ComplexMatrix2) :
    restrictFinset F (z • C) = z • restrictFinset F C := rfl
structure FinsetLocalForm (P : Submodule ℂ (β → ComplexMatrix2))
    (v : (β → ComplexMatrix2) → ComplexMatrix2)
    (F : Finset β) (O : Set (F → ComplexMatrix2)) (h : (F → ComplexMatrix2) → ComplexMatrix2)
    (D : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2)
    (Q : (F → ComplexMatrix2) →L[ℂ] (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2) : Prop where
  restrict_mem : ∀ C ∈ P, restrictFinset F C ∈ tracelessPi F
  taylor : QuadraticTaylorData O h D Q
  map_zero : h 0 = 0
  mapsTo : MapsTo h O (ComplexMatrix2.traceless : Set ComplexMatrix2)
  eq_comp : ∀ C ∈ P, restrictFinset F C ∈ O → v C = h (restrictFinset F C)
variable {P : Submodule ℂ (β → ComplexMatrix2)} {v : (β → ComplexMatrix2) → ComplexMatrix2}
  {F : Finset β} {O : Set (F → ComplexMatrix2)}
  {h : (F → ComplexMatrix2) → ComplexMatrix2} {D : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2}
  {Q : (F → ComplexMatrix2) →L[ℂ] (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2}
theorem FinsetLocalForm.eventually_mem (e : FinsetLocalForm P v F O h D Q)
    (A A' : F → ComplexMatrix2) (hA : A ∈ tracelessPi F) (hA' : A' ∈ tracelessPi F) :
    ∀ᶠ s : ℂ in 𝓝 0, ∀ᶠ t : ℂ in 𝓝 0, s • A + t • A' ∈ O := by
  obtain ⟨δ, hδ, hb⟩ := e.taylor.ball_subset
  have hc : Continuous fun p : ℂ × ℂ => p.1 • A + p.2 • A' := by fun_prop
  have h0 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), ‖p.1 • A + p.2 • A'‖ < δ := by
    have := (hc.tendsto (0, 0)).norm
    simp only [zero_smul, add_zero, norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  rw [nhds_prod_eq] at h0
  have h1 := h0.curry
  filter_upwards [h1] with s hs
  filter_upwards [hs] with t ht
  exact hb _ (tracelessPi_add (tracelessPi_smul s hA) (tracelessPi_smul t hA'))
    (by rwa [supNorm_eq_norm])
theorem FinsetLocalForm.hasDerivAtZeroAlong (e : FinsetLocalForm P v F O h D Q)
    {B : β → ComplexMatrix2} (hB : B ∈ P) : HasDerivAtZeroAlong v B (D (restrictFinset F B)) := by
  have hA := e.restrict_mem B hB
  have h0 : (0 : F → ComplexMatrix2) ∈ tracelessPi F :=
    mem_tracelessPi_iff.2 fun _ => ComplexMatrix2.traceless.zero_mem
  have hev : ∀ᶠ s : ℂ in 𝓝 0, s • restrictFinset F B ∈ O := by
    filter_upwards [e.eventually_mem (restrictFinset F B) 0 hA h0] with s hs
    obtain ⟨t, ht⟩ := hs.exists
    simpa using ht
  refine (e.taylor.hasDerivAt_line _ hA).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact e.eq_comp (t • B) (P.smul_mem t hB) ht
theorem FinsetLocalForm.mixed_eq (e : FinsetLocalForm P v F O h D Q) {B B' : β → ComplexMatrix2}
    (hB : B ∈ P) (hB' : B' ∈ P) :
    mixedDirectionalDeriv ℂ v B B' = Q (restrictFinset F B) (restrictFinset F B') := by
  have hA := e.restrict_mem B hB
  have hA' := e.restrict_mem B' hB'
  rw [← e.taylor.mixed_deriv _ hA _ hA']
  unfold mixedDirectionalDeriv
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [e.eventually_mem _ _ hA hA'] with s hs
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hs] with t ht
  exact e.eq_comp (s • B + t • B') (P.add_mem (P.smul_mem s hB) (P.smul_mem t hB')) ht
theorem FinsetLocalForm.mem_traceless (e : FinsetLocalForm P v F O h D Q) {B : β → ComplexMatrix2}
    (hB : B ∈ P) :
    D (restrictFinset F B) ∈ ComplexMatrix2.traceless ∧
      ∀ B' ∈ P, Q (restrictFinset F B) (restrictFinset F B') ∈ ComplexMatrix2.traceless := by
  have := e.taylor.mem_traceless e.mapsTo _ (e.restrict_mem B hB)
  exact ⟨this.1, fun B' hB' => this.2 _ (e.restrict_mem B' hB')⟩
theorem exists_finsetLocalForm
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    {τ : Type} [Fintype τ] (ε : F ≃ τ) {𝔇 : Set (τ → ComplexMatrix2)}
    {Φ : (τ → ComplexMatrix2) → ComplexMatrix2}
    {u : τ → ComplexMatrix2} (hu : u ∈ 𝔇) {b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (hΦ : IsHolomorphicToUnimodular b₀ (DoubleBlockPolydisc.leftComponents ⁻¹' 𝔇)
      (Φ ∘ DoubleBlockPolydisc.leftComponents))
    {pos : β → Prop} (hF : F.Nonempty) (hpos : ∀ b ∈ F, pos b)
    (hP : ∀ C ∈ P, ∀ b, pos b → C b ∈ ComplexMatrix2.traceless)
    {Defined : (β → ComplexMatrix2) → Prop} {a : (β → ComplexMatrix2) → ComplexMatrix2}
    (hform : ∀ C ∈ P, expChartFamily ε u (restrictFinset F C) ∈ 𝔇 →
      Defined C ∧ a C = Φ (expChartFamily ε u (restrictFinset F C)) * (Φ u)⁻¹)
    (hv : ∀ C, v C = Complex.I⁻¹ • ComplexMatrix2.logSeries (a C)) :
    IsLocallyHolomorphicLog pos P Defined a v ∧
      ∃ O h D Q, FinsetLocalForm P v F O h D Q := by
  obtain ⟨O, hO⟩ := exists_expChartLogData hT hV ε hu hΦ
  obtain ⟨D, Q, hDQ⟩ := exists_quadraticTaylorData hT hA (hO.holomorphic b₀) hO.zero_mem
  have hval : ∀ C ∈ P, restrictFinset F C ∈ O →
      Defined C ∧ ComplexMatrix2.operatorNorm (a C - 1) < 1 ∧
        v C = expChartLog ε Φ u (restrictFinset F C) := by
    intro C hC hCO
    obtain ⟨h₁, h₂⟩ := hform C hC (hO.family_mem _ hCO)
    refine ⟨h₁, ?_, ?_⟩
    · rw [h₂]
      exact hO.norm_sub_one_lt _ hCO
    · rw [hv, h₂]
      rfl
  refine ⟨⟨F, O, expChartLog ε Φ u, hF, hpos, hO.zero_mem, hO.holomorphic, hO.mem_traceless, hval⟩,
    O, expChartLog ε Φ u, D, Q, ?_⟩
  exact ⟨fun C hC => mem_tracelessPi_iff.2 fun b => hP C hC b (hpos b b.2), hDQ,
    expChartLog_zero ε Φ hO.isUnit, hO.mem_traceless, fun C hC hCO => (hval C hC hCO).2.2⟩
end EvaluationMaps
section SecondOrder
variable {β γ : Type}
theorem bddAbove_range_of_mem_bounded {P : Submodule ℂ (β → ComplexMatrix2)}
    {B : β → ComplexMatrix2} (hB : B ∈ boundedSubmodule P) :
    BddAbove (range fun b => ComplexMatrix2.operatorNorm (B b)) := by
  obtain ⟨-, C, hC⟩ := hB
  exact ⟨C, by rintro _ ⟨b, rfl⟩; exact hC b⟩
theorem supNorm_restrictFinset_le {P : Submodule ℂ (β → ComplexMatrix2)} {B : β → ComplexMatrix2}
    (hB : B ∈ boundedSubmodule P) (F : Finset β) : supNorm (restrictFinset F B) ≤ supNorm B := by
  refine Real.iSup_le (fun b => ?_) (Real.iSup_nonneg fun _ => norm_nonneg _)
  exact le_ciSup (f := fun b => ComplexMatrix2.operatorNorm (B b))
    (bddAbove_range_of_mem_bounded hB) b.1
theorem supNorm_nonneg {σ : Type} (A : σ → ComplexMatrix2) : 0 ≤ supNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supNorm_real_smul_le {P : Submodule ℂ (β → ComplexMatrix2)} {B : β → ComplexMatrix2}
    (hB : B ∈ boundedSubmodule P) {t : ℝ} (ht : 0 ≤ t) :
    supNorm ((t : ℂ) • B) ≤ t * supNorm B := by
  refine Real.iSup_le (fun b => ?_) (mul_nonneg ht (supNorm_nonneg _))
  have h₁ : ComplexMatrix2.operatorNorm (B b) ≤ supNorm B :=
    le_ciSup (f := fun b => ComplexMatrix2.operatorNorm (B b)) (bddAbove_range_of_mem_bounded hB) b
  show ‖(t : ℂ) • B b‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left h₁ ht
theorem quadraticExpansion_diag_eq {P : Submodule ℂ (β → ComplexMatrix2)}
    {v : γ → (β → ComplexMatrix2) → ComplexMatrix2}
    {Qd : (β → ComplexMatrix2) → γ → ComplexMatrix2} {q q' : BoundedBilinear P γ}
    (hq : IsQuadraticExpansion P v Qd q) (hq' : IsQuadraticExpansion P v Qd q')
    (B : boundedSubmodule P) (c : γ) : q B B c = q' B B c := by
  obtain ⟨K, δ, hδ, hK⟩ := hq.2 c
  obtain ⟨K', δ', hδ', hK'⟩ := hq'.2 c
  set T := supNorm (B : β → ComplexMatrix2) with hT
  have hT0 : 0 ≤ T := supNorm_nonneg _
  set d := q B B c - q' B B c with hd
  have key : ∀ t : ℝ, 0 < t → t * T < min δ δ' →
      ‖d‖ ≤ 2 * (|K| + |K'|) * T ^ 3 * t := by
    intro t ht htT
    let Bt : boundedSubmodule P := (t : ℂ) • B
    have hX : supNorm (Bt : β → ComplexMatrix2) ≤ t * T := supNorm_real_smul_le B.2 ht.le
    have hX0 : 0 ≤ supNorm (Bt : β → ComplexMatrix2) := supNorm_nonneg _
    have hlt : supNorm (Bt : β → ComplexMatrix2) < min δ δ' := lt_of_le_of_lt hX htT
    have h₁ := hK Bt (lt_of_lt_of_le hlt (min_le_left _ _))
    have h₂ := hK' Bt (lt_of_lt_of_le hlt (min_le_right _ _))
    have hcube : supNorm (Bt : β → ComplexMatrix2) ^ 3 ≤ (t * T) ^ 3 := pow_le_pow_left₀ hX0 hX 3
    have hb : ∀ K₀ : ℝ, K₀ * supNorm (Bt : β → ComplexMatrix2) ^ 3 ≤ |K₀| * (t * T) ^ 3 :=
      fun K₀ =>
      (mul_le_mul_of_nonneg_right (le_abs_self K₀) (pow_nonneg hX0 3)).trans
        (mul_le_mul_of_nonneg_left hcube (abs_nonneg _))
    have hqt : ∀ r : BoundedBilinear P γ, r Bt Bt c = ((t : ℂ) * t) • r B B c := fun r => by
      simp only [Bt, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_smul]
    have hdiff : ((1 / 2 : ℂ) * ((t : ℂ) * t)) • d =
        (v c (Bt : β → ComplexMatrix2) - Qd (Bt : β → ComplexMatrix2) c -
            (1 / 2 : ℂ) • q' Bt Bt c) -
          (v c (Bt : β → ComplexMatrix2) - Qd (Bt : β → ComplexMatrix2) c -
            (1 / 2 : ℂ) • q Bt Bt c) := by
      rw [hqt q, hqt q', hd]
      module
    have hn : ‖((1 / 2 : ℂ) * ((t : ℂ) * t)) • d‖ ≤ (|K| + |K'|) * (t * T) ^ 3 := by
      rw [hdiff]
      refine (norm_sub_le _ _).trans ?_
      have := (h₂.trans (hb K')).trans_eq rfl
      have := (h₁.trans (hb K)).trans_eq rfl
      nlinarith [(h₂.trans (hb K')), (h₁.trans (hb K))]
    have hnorm : ‖((1 / 2 : ℂ) * ((t : ℂ) * t)) • d‖ = (1 / 2) * (t * t) * ‖d‖ := by
      rw [norm_smul]
      simp [abs_of_pos ht]
    rw [hnorm] at hn
    have ht2 : 0 < t * t := mul_pos ht ht
    have : (1 / 2) * (t * t) * ‖d‖ ≤ (1 / 2) * (t * t) * (2 * (|K| + |K'|) * T ^ 3 * t) := by
      calc _ ≤ _ := hn
        _ = _ := by ring
    exact le_of_mul_le_mul_left this (by positivity)
  set M := 2 * (|K| + |K'|) * T ^ 3 with hM
  have hlim : Tendsto (fun t : ℝ => M * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => M * t) (𝓝 0) (𝓝 (M * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t * T < min δ δ' := by
    have : Tendsto (fun t : ℝ => t * T) (𝓝 0) (𝓝 (0 * T)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (lt_min hδ hδ'))
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖d‖ ≤ M * t := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hts
    exact key t ht hts
  have hle : ‖d‖ ≤ 0 := ge_of_tendsto hlim hev
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)
theorem quadraticExpansion_unique {P : Submodule ℂ (β → ComplexMatrix2)}
    {v : γ → (β → ComplexMatrix2) → ComplexMatrix2}
    {Qd : (β → ComplexMatrix2) → γ → ComplexMatrix2} {q q' : BoundedBilinear P γ}
    (hq : IsQuadraticExpansion P v Qd q) (hq' : IsQuadraticExpansion P v Qd q') :
    q = q' := by
  have hdiag := quadraticExpansion_diag_eq hq hq'
  refine LinearMap.ext₂ fun B B' => ?_
  funext c
  have h₁ := hdiag (B + B') c
  simp only [map_add, LinearMap.add_apply, Pi.add_apply] at h₁
  have s := congrFun (hq.1 B' B) c
  have s' := congrFun (hq'.1 B' B) c
  rw [hdiag B c, hdiag B' c, s, s'] at h₁
  have h₂ : (2 : ℂ) • q B B' c = (2 : ℂ) • q' B B' c := by
    rw [two_smul, two_smul]
    have e₁ := add_left_cancel (a := q' B B c) (by simpa [add_assoc] using h₁)
    simpa [add_assoc] using add_right_cancel (b := q' B' B' c) (by simpa [add_assoc] using e₁)
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h₂
theorem hasUniqueQuadraticTerm_of_local {P : Submodule ℂ (β → ComplexMatrix2)}
    {v : γ → (β → ComplexMatrix2) → ComplexMatrix2}
    {Qd : (β → ComplexMatrix2) → γ → ComplexMatrix2}
    (hdata : ∀ c : γ, ∃ (F : Finset β) (O : Set (F → ComplexMatrix2))
      (h : (F → ComplexMatrix2) → ComplexMatrix2)
      (D : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2)
      (Q : (F → ComplexMatrix2) →L[ℂ] (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2),
      FinsetLocalForm P (v c) F O h D Q ∧ ∀ B ∈ P, Qd B c = D (restrictFinset F B)) :
    HasUniqueQuadraticTerm P v Qd := by
  choose F O h D Q he hQ using hdata
  let q : BoundedBilinear P γ := LinearMap.mk₂ ℂ
    (fun B B' c => Q c (restrictFinset (F c) (B : β → ComplexMatrix2))
      (restrictFinset (F c) (B' : β → ComplexMatrix2)))
    (fun B B' B'' => by funext c; simp [restrictFinset_add])
    (fun z B B' => by funext c; simp [restrictFinset_smul])
    (fun B B' B'' => by funext c; simp [restrictFinset_add])
    (fun z B B' => by funext c; simp [restrictFinset_smul])
  have hqv : ∀ (B B' : boundedSubmodule P) (c : γ),
      q B B' c = Q c (restrictFinset (F c) (B : β → ComplexMatrix2))
        (restrictFinset (F c) (B' : β → ComplexMatrix2)) :=
    fun _ _ _ => rfl
  have hexp : IsQuadraticExpansion P v Qd q := by
    refine ⟨fun B B' => ?_, fun c => ?_⟩
    · funext c
      rw [hqv, hqv]
      exact (he c).taylor.symm _ _
    · obtain ⟨K, δ₁, hδ₁, hK0, hK⟩ := (he c).taylor.remainder
      obtain ⟨δ₂, hδ₂, hb⟩ := (he c).taylor.ball_subset
      refine ⟨K, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun B hB => ?_⟩
      have hle := supNorm_restrictFinset_le B.2 (F c)
      have hlt₁ := lt_of_le_of_lt hle (lt_of_lt_of_le hB (min_le_left _ _))
      have hlt₂ := lt_of_le_of_lt hle (lt_of_lt_of_le hB (min_le_right _ _))
      have hA := (he c).restrict_mem _ B.2.1
      have hval := (he c).eq_comp _ B.2.1 (hb _ hA hlt₂)
      have := hK _ hA hlt₁
      rw [(he c).map_zero, sub_zero] at this
      rw [hval, hQ c _ B.2.1, hqv]
      exact this.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (supNorm_nonneg _) hle 3) hK0)
  have hterm : quadraticTerm P v Qd = q :=
    quadraticExpansion_unique
      (Classical.epsilon_spec (p := IsQuadraticExpansion P v Qd) ⟨q, hexp⟩) hexp
  refine ⟨⟨q, hexp, fun q' hq' => quadraticExpansion_unique hq' hexp⟩, hterm ▸ hexp, fun B B' c => ?_⟩
  rw [hterm, hqv]
  exact ⟨(he c).mixed_eq B.2.1 B'.2.1, ((he c).mem_traceless B.2.1).2 _ B'.2.1⟩
end SecondOrder
section Matrices
theorem expChart_mem_unitDeterminant (hEL : ComplexMatrix2.ExpLogEstimates) {X g : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.LeftChartFields.leftExpMul_mem_complexGroup <;> assumption
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem asGroupFactors_image {σ : Type} (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = DoubleBlockPolydisc.leftComponents ⁻¹' O := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem eventually_expChart_near (hEL : ComplexMatrix2.ExpLogEstimates) (X g : ComplexMatrix2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℂ in 𝓝 0,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • (t • X)) * g - g) < ε := by
  have hbound : ∀ t : ℂ,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • (t • X)) * g - g) ≤
      (Real.exp ‖Complex.I • (t • X)‖ - 1) * ‖g‖ := fun t => by
    have e : ComplexMatrix2.matExp (Complex.I • (t • X)) * g - g =
        (ComplexMatrix2.matExp (Complex.I • (t • X)) - 1) * g := by
      rw [sub_mul, one_mul]
    rw [e]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hEL.1 (Complex.I • (t • X))).2 (norm_nonneg _))
  have hc : Continuous fun t : ℂ => (Real.exp ‖Complex.I • (t • X)‖ - 1) * ‖g‖ := by fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_smul, smul_zero, norm_zero, Real.exp_zero, sub_self, zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with t ht
  exact (hbound t).trans_lt ht
theorem smul_deriv_eq_of_hasDerivAt {f g : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt (fun t => Complex.I⁻¹ • f t) D 0) (he : g =ᶠ[𝓝 0] f) :
    Complex.I⁻¹ • deriv g 0 = D := by
  have hI : Complex.I * Complex.I⁻¹ = 1 := mul_inv_cancel₀ Complex.I_ne_zero
  have hf : HasDerivAt f (Complex.I • D) 0 := by
    have := h.const_smul Complex.I
    have e : (Complex.I • fun t => Complex.I⁻¹ • f t) = f := by
      funext t
      simp [smul_smul]
    rwa [e] at this
  rw [he.deriv_eq, hf.deriv, smul_smul, mul_comm, hI, one_smul]
end Matrices
section FiniteSide
variable {L n k : ℕ}
open YangMills.Construction.Tower.LevelwiseMeans (levelwiseMean valuesOrOne IsDefinedAt)
def meanFamily (U : Edge L n k 0 → ComplexMatrix2) : ∀ i : ℕ, Edge L n k i → ComplexMatrix2 :=
  fun i => PeriodicLattice.complexBlockFieldAtLevel i U
theorem isMeanSequenceFrom_of_small (hO : IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k) :
    MeanStableFields.IsMeanSequenceFrom k U (meanFamily U) := by
  refine ⟨⟨fun i hi => ?_, fun i hi b => (hU.2 i hi).2 b, fun i hi c hc => rfl⟩, rfl⟩
  cases i with
  | zero => exact hU.1
  | succ i => exact hO.meanStep_mem i (by omega) _ (hU.2 i (by omega))
theorem small_of_meanStable (hO : IteratedMeans.TorusConditions L n k)
    {W : Edge L n k 0 → ComplexMatrix2}
    (hW : W ∈ MeanStableFields.meanStableFields L n k k) :
    W ∈ smallIterateFields L n k := by
  obtain ⟨V, hV, rfl⟩ := hW
  have key : ∀ i ≤ k, V i = meanFamily (V 0) i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hwr : V i ∈ MeanStableFields.fieldsNearOne L n k i :=
        ⟨hV.mem_fields i (by omega), hV.norm_sub_one_lt i (by omega)⟩
      have := (hO.meanStep_unique i (by omega) (V i) hwr (V (i + 1))
        (hV.mem_fields _ hi)).1 (hV.eq_mean i (by omega))
      rw [this, ih (by omega)]
      rfl
  refine ⟨hV.mem_fields 0 (Nat.zero_le _), fun j hj => ?_⟩
  have := key j hj.le
  show meanFamily (V 0) j ∈ _
  rw [← this]
  exact ⟨hV.mem_fields j hj.le, hV.norm_sub_one_lt j hj⟩
theorem levelwiseMean_of_small (hP : MeanStableFields.MeanStableConditions L n k)
    (hO : IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k) {i : ℕ} (hi : i ≤ k)
    (c : Edge L n k i) :
    levelwiseMean U i c = some (PeriodicLattice.complexBlockFieldAtLevel i U c) :=
  hP.eq_levelwiseMean k le_rfl U _ (isMeanSequenceFrom_of_small hO hU) i hi c
theorem iterMean_of_small (hP : MeanStableFields.MeanStableConditions L n k)
    (hO : IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k) {i : ℕ} (hi : i ≤ k)
    (c : Edge L n k i) : iterMean U i c = PeriodicLattice.complexBlockFieldAtLevel i U c := by
  simp [iterMean, valuesOrOne, levelwiseMean_of_small hP hO hU hi c]
structure OrientationFacts (L n k : ℕ) : Prop where
  xor_opposite : ∀ i ≤ k, ∀ b : Edge L n k i,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  opposite_opposite : ∀ i ≤ k, ∀ b : Edge L n k i, b.opposite.opposite = b
theorem orientationFacts (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    OrientationFacts L n k :=
  ⟨fun i hi b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.2.2,
    fun i hi b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.1⟩
theorem OrientationFacts.opposite_pos (hor : OrientationFacts L n k) {i : ℕ} (hi : i ≤ k)
    {b : Edge L n k i} (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases hor.xor_opposite i hi b with h | h
  exacts [absurd h.1 hb, h.1]
theorem OrientationFacts.not_opposite_pos (hor : OrientationFacts L n k) {i : ℕ} (hi : i ≤ k)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases hor.xor_opposite i hi b with h | h
  exacts [h.2, absurd hb h.2]
theorem expTwist_mem (hEL : ComplexMatrix2.ExpLogEstimates) (hor : OrientationFacts L n k)
    {i : ℕ} (hi : i ≤ k) {U C : Edge L n k i → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hC : C ∈ complexEdgeForms L n k i) :
    PeriodicLattice.expTwist C U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  classical
  have hval : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => expChart_mem_unitDeterminant hEL (hC.1 b hb) (hU.1 b (mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hval b hb
    · have hr : b.opposite.IsPositivelyOriented := hor.opposite_pos hi hb
      simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_unitDeterminant (hval _ hr)
  · by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented := hor.not_opposite_pos hi hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hr, hor.opposite_opposite i hi b]
    · have hr : b.opposite.IsPositivelyOriented := hor.opposite_pos hi hb
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hr]
      exact (inv_inv_of_mem_unitDeterminant (hval _ hr)).symm
theorem form_mem_traceless {j : ℕ} {C : Edge L n k j → ComplexMatrix2}
    (hC : C ∈ complexEdgeForms L n k j)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) : C b ∈ ComplexMatrix2.traceless := hC.1 b hb
structure AnalyticInputs : Prop where
  traceless : HolomorphicOnTracelessIffDifferentiable
  analytic : ComplexMatrix2.DifferentiableOnFamiliesAnalytic
  unimodular : ComplexMeanLiesInComplexGaugeGroup
  expLog : ComplexMatrix2.ExpLogEstimates
structure SideInputs (L n k : ℕ) : Prop where
  levelwise : LevelwiseMeans.PeriodicConditions L n k
  meanStable : MeanStableFields.MeanStableConditions L n k
  iterated : IteratedMeans.TorusConditions L n k
  orientation : OrientationFacts L n k
  doubleBlock : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    DoubleBlockPolydisc.PolydiscPropertiesAt (polydiscRadius L) c
  smoothing_congr : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ V V' : Edge L n k j → ComplexMatrix2,
    (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), V b = V' b) →
    PeriodicLattice.complexBlockAverage V c = PeriodicLattice.complexBlockAverage V' c
  contour_congr : ∀ j < k, ∀ y : Vertex L n k (j + 1),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) →
    ∀ V' : Edge L n k j → ComplexMatrix2, V' ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c,
      ComplexMatrix2.operatorNorm (V' b - 1) < polydiscRadius L) →
    ∀ W : Edge L n k j → ComplexMatrix2, (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W b = V' b) →
    PeriodicLattice.complexMeanContourHolonomy W y x =
      PeriodicLattice.complexMeanContourHolonomy V' y x
  edges_finite : ∀ j ≤ k, (univ : Set (Edge L n k j)).Finite
theorem iter_localForm (cal : AnalyticInputs) (s : SideInputs L n k)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) {i : ℕ} (hi : i ≤ k) (c : Edge L n k i) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k 0)
        (fun C => IsDefinedAt (PeriodicLattice.expTwist C U) i c)
        (iterRatio U i c) (iterLogRatio U i c) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k 0) (iterLogRatio U i c) F O h D Q := by
  have hf : IsDefinedAt U i c := by
    simp [IsDefinedAt, levelwiseMean_of_small s.meanStable s.iterated hU hi c]
  obtain ⟨F, O, f, hw⟩ := s.levelwise.exists_representation i hi c U hU.1 hf
  have hfU : iterMean U i c = f (LevelwiseMeans.edgeEntries F U) := by
    have := hw.eq_some U hU.1 hw.mem
    simp [iterMean, valuesOrOne, this]
  suffices hr : IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k 0)
        (fun C => IsDefinedAt (PeriodicLattice.expTwist C U) i c)
        (iterRatio U i c) (iterLogRatio U i c) ∧
      ∃ O h D Q, FinsetLocalForm (complexEdgeForms L n k 0) (iterLogRatio U i c) F O h D Q from
    ⟨hr.1, F, hr.2⟩
  refine exists_finsetLocalForm cal.traceless cal.analytic cal.unimodular (Equiv.refl _) (𝔇 := O)
    (Φ := f) (u := LevelwiseMeans.edgeEntries F U) hw.mem
    (b₀ := OneLoop.pauliBasis) ?_ hw.nonempty hw.positive
    (fun C hC b hb => form_mem_traceless hC hb) ?_ (fun C => rfl)
  · rw [← asGroupFactors_image]
    exact hw.holomorphic _
  · intro C hC hCO
    have e : expChartFamily (Equiv.refl _) (LevelwiseMeans.edgeEntries F U)
        (restrictFinset F C) =
        LevelwiseMeans.edgeEntries F (PeriodicLattice.expTwist C U) := by
      funext b
      simp [expChartFamily, LevelwiseMeans.edgeEntries, restrictFinset,
        PeriodicLattice.expTwist, if_pos (hw.positive b b.2)]
    rw [e] at hCO ⊢
    have hv := hw.eq_some _ (expTwist_mem cal.expLog s.orientation (Nat.zero_le _) hU.1 hC) hCO
    refine ⟨by simp [IsDefinedAt, hv], ?_⟩
    simp only [iterRatio, hfU]
    simp [iterMean, valuesOrOne, hv]
theorem eqOn_of_positive (hor : OrientationFacts L n k) {j : ℕ} (hj : j ≤ k)
    {P : Set (Edge L n k j)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {W W' : Edge L n k j → ComplexMatrix2}
    (hW : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup P W)
    (hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup P W')
    (hag : ∀ b ∈ P, b.IsPositivelyOriented → W b = W' b) : ∀ b ∈ P, W b = W' b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · exact hag b hb hp
  · have hr := hor.opposite_pos hj hp
    have h₁ := hW.2 _ (hrev b hb)
    have h₂ := hW'.2 _ (hrev b hb)
    rw [hor.opposite_opposite j hj b] at h₁ h₂
    rw [h₁, h₂, hag _ (hrev b hb) hr]
theorem extendFromPositive_eq (hor : OrientationFacts L n k) {j : ℕ} (hj : j ≤ k)
    {P : Set (Edge L n k j)} (hrev : ∀ b ∈ P, b.opposite ∈ P) {W : Edge L n k j → ComplexMatrix2}
    (hW : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup P W) :
    ∀ b ∈ P, PeriodicLattice.extendFromPositive P
      (fun b : PeriodicLattice.PositiveBondOf P => W b.1) b = W b := by
  classical
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp [PeriodicLattice.extendFromPositive, hb, hp]
  · have hr := hor.opposite_pos hj hp
    have h₁ := hW.2 _ (hrev b hb)
    rw [hor.opposite_opposite j hj b] at h₁
    simp [PeriodicLattice.extendFromPositive, hb, hp, hrev b hb, hr, h₁]
theorem polydisc_localForm (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j)
    {G : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hG : ∃ _ : Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c),
      DoubleBlockPolydisc.IsHolomorphicWithEntries
        (DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c)
        fun v => G (DoubleBlockPolydisc.fieldOfValues c v))
    (hloc : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc (polydiscRadius L) c →
      ∀ W' : Edge L n k j → ComplexMatrix2,
        (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) → G W' = G W)
    {Defined : (Edge L n k j → ComplexMatrix2) → Prop}
    (hDefined : ∀ W ∈ nearIdentityPolydisc (polydiscRadius L) c, Defined W)
    {a v : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (ha : ∀ C, a C = G (PeriodicLattice.expTwist C V) * (G V)⁻¹)
    (hv : ∀ C, v C = Complex.I⁻¹ • ComplexMatrix2.logSeries (a C)) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k j)
        (fun C => Defined (PeriodicLattice.expTwist C V)) a v ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k j) v F O h D Q := by
  classical
  obtain ⟨inst, hhol⟩ := hG
  have hd := s.doubleBlock j hj c hc
  have hfo := hd.finite_open
  let ρ := polydiscRadius L
  let P := DoubleBlockPolydisc.doubleBlockBonds c
  let F : Finset (Edge L n k j) := hfo.positive_finite.toFinset
  have hFmem : ∀ b, b ∈ F ↔ b ∈ DoubleBlockPolydisc.positiveDoubleBlockBonds c := fun b => by
    simp [F]
  let ε : F ≃ DoubleBlockPolydisc.positiveDoubleBlockBonds c := Equiv.subtypeEquivRight hFmem
  let u : DoubleBlockPolydisc.positiveDoubleBlockBonds c → ComplexMatrix2 := fun b => V b.1
  have hVp : V ∈ nearIdentityPolydisc ρ c := s.meanStable.mem_polydisc j hj c hc V hV
  have hu : u ∈ DoubleBlockPolydisc.polydiscPositive ρ c :=
    ⟨BondSetFields.restrictTo P V, ⟨V, hVp, rfl⟩, rfl⟩
  have hconf : ∀ {W : Edge L n k j → ComplexMatrix2},
      W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup P W :=
    fun hW => ⟨fun b _ => hW.1 b (mem_univ b), fun b _ => hW.2 b (mem_univ b)⟩
  have hrev : ∀ b ∈ P, b.opposite ∈ P := hfo.opposite_mem
  have hjk : j ≤ k := hj.le
  have hGval : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc ρ c →
      G (DoubleBlockPolydisc.fieldOfValues c fun b => W b.1) = G W := fun W hW hWp =>
    hloc W hW hWp _ (extendFromPositive_eq s.orientation hjk hrev (hconf hW))
  suffices hr : IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k j)
        (fun C => Defined (PeriodicLattice.expTwist C V)) a v ∧
      ∃ O h D Q, FinsetLocalForm (complexEdgeForms L n k j) v F O h D Q from ⟨hr.1, F, hr.2⟩
  refine exists_finsetLocalForm cal.traceless cal.analytic cal.unimodular ε
    (𝔇 := DoubleBlockPolydisc.polydiscPositive ρ c)
    (Φ := fun v => G (DoubleBlockPolydisc.fieldOfValues c v)) (u := u) hu
    (b₀ := OneLoop.pauliBasis) (hhol.toUnimodular _) ?_ ?_
    (fun C hC b hb => form_mem_traceless hC hb) ?_ hv
  · obtain ⟨b, hb⟩ := hfo.positive_nonempty
    exact ⟨b, (hFmem b).2 hb⟩
  · exact fun b hb => ((hFmem b).1 hb).2
  · intro C hC hCO
    set W := PeriodicLattice.expTwist C V with hWdef
    have hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
      expTwist_mem cal.expLog s.orientation hjk hV.1 hC
    have e : expChartFamily ε u (restrictFinset F C) = fun b => W b.1 := by
      funext b
      simp [expChartFamily, restrictFinset, u, ε, hWdef, PeriodicLattice.expTwist, if_pos b.2.2]
    rw [e] at hCO ⊢
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, h⟩ := hCO
    have hag : ∀ b ∈ P, W₀ b = W b := by
      refine eqOn_of_positive s.orientation hjk hrev hW₀.1 (hconf hW) fun b hb hp => ?_
      exact congrFun h ⟨b, hb, hp⟩
    have hWp : W ∈ nearIdentityPolydisc ρ c :=
      ⟨hconf hW, fun b hb => by rw [← hag b hb]; exact hW₀.2 b hb⟩
    refine ⟨hDefined W hWp, ?_⟩
    rw [ha C, hGval W hW hWp]
    exact congrArg (fun X => G W * X⁻¹) (hGval V hV.1 hVp).symm
theorem mean_localForm (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k j)
        (fun C => PeriodicLattice.expTwist C V ∈ nearIdentityPolydisc (polydiscRadius L) c)
        (meanRatio V c) (meanLogRatio V c) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k j) (meanLogRatio V c) F O h D Q :=
  polydisc_localForm cal s hj hc hV (G := fun W => PeriodicLattice.complexBlockAverage W c)
    (s.doubleBlock j hj c hc).holomorphic_smoothing
    (fun W _ _ W' h => s.smoothing_congr j hj c hc W' W h)
    (Defined := fun W => W ∈ nearIdentityPolydisc (polydiscRadius L) c)
    (fun W hW => hW) (fun _ => rfl) (fun _ => rfl)
theorem exists_positive_incident {j : ℕ} (y : Vertex L n k j) :
    ∃ c : Edge L n k j, c.IsPositivelyOriented ∧
      y ∈ ({c.source, c.target} : Set (Vertex L n k j)) :=
  ⟨PeriodicLattice.Bond.forwardFrom y 0, ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩, Or.inl rfl⟩
theorem contour_localForm (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L n k j)
        (fun C => ContourDefined y (PeriodicLattice.expTwist C V))
        (contourRatio V y x) (contourLogRatio V y x) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k j) (contourLogRatio V y x) F O h D Q := by
  obtain ⟨c, hc, hy⟩ := exists_positive_incident y
  exact polydisc_localForm cal s hj hc hV
    (G := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((s.doubleBlock j hj c hc).holomorphic_contourMean y hy x hx)
    (fun W hW hWp W' h => s.contour_congr j hj y x hx c hc hy W hW hWp.2 W' h)
    (Defined := ContourDefined y) (fun W hW => ⟨c, hc, hy, hW⟩) (fun _ => rfl) (fun _ => rfl)
theorem eventually_expTwist_small (cal : AnalyticInputs) (s : SideInputs L n k)
    {U B : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) (hB : B ∈ complexEdgeForms L n k 0) :
    ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • B) U ∈ smallIterateFields L n k := by
  classical
  have hS : U ∈ MeanStableFields.meanStableFields L n k k :=
    ⟨meanFamily U, isMeanSequenceFrom_of_small s.iterated hU⟩
  let F : Finset (Edge L n k 0) :=
    ((s.edges_finite 0 (Nat.zero_le _)).toFinset).filter (·.IsPositivelyOriented)
  obtain ⟨ε, hε, hmv⟩ :=
    s.meanStable.small_perturbation U hS F (fun b hb => (Finset.mem_filter.1 hb).2)
  have hall : ∀ᶠ t : ℂ in 𝓝 0, ∀ b ∈ F,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • (t • B b)) * U b - U b) < ε :=
    (Finset.eventually_all F).2 fun b _ => eventually_expChart_near cal.expLog (B b) (U b) hε
  filter_upwards [hall] with t ht
  refine small_of_meanStable s.iterated (hmv _ (expTwist_mem cal.expLog s.orientation
    (Nat.zero_le _) hU.1 ((complexEdgeForms L n k 0).smul_mem t hB)) (fun b hb hbF => ?_)
    (fun b hb => ?_))
  · exact absurd (Finset.mem_filter.2 ⟨by simp, hb⟩) hbF
  · have hp : b.IsPositivelyOriented := (Finset.mem_filter.1 hb).2
    simpa [PeriodicLattice.expTwist, if_pos hp] using ht b hb
theorem complexIterDeriv_eq (cal : AnalyticInputs) (s : SideInputs L n k)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) {i : ℕ} (hi : i ≤ k) {c : Edge L n k i}
    (hc : c.IsPositivelyOriented) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0)
    {D : ComplexMatrix2} (hD : HasDerivAtZeroAlong (iterLogRatio U i c) B D) :
    complexIterDeriv L n k i U B c = D := by
  classical
  simp only [complexIterDeriv, holLeftDifferential, extendOddly, if_pos hc,
    logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  refine smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (iterRatio U i c (t • B))) hD ?_
  filter_upwards [eventually_expTwist_small cal s hU hB] with t ht
  simp only [iterRatio, iterMean_of_small s.meanStable s.iterated ht hi,
    iterMean_of_small s.meanStable s.iterated hU hi]
theorem complexSmoothingDeriv_eq {j : ℕ} {V B : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {D : ComplexMatrix2}
    (hD : HasDerivAtZeroAlong (meanLogRatio V c) B D) :
    complexSmoothingDeriv V B c = D := by
  classical
  simp only [complexSmoothingDeriv, holLeftDifferential, extendOddly, if_pos hc,
    logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  exact smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (meanRatio V c (t • B))) hD
    (Filter.EventuallyEq.of_eq rfl)
theorem contourDeriv_eq {j : ℕ} {V B : Edge L n k j → ComplexMatrix2} {y : Vertex L n k (j + 1)}
    {x : Vertex L n k j} {D : ComplexMatrix2}
    (hD : HasDerivAtZeroAlong (contourLogRatio V y x) B D) :
    logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
      (PeriodicLattice.complexMeanContourHolonomy V y x) B = D := by
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  exact smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (contourRatio V y x (t • B))) hD
    (Filter.EventuallyEq.of_eq rfl)
end FiniteSide
section Linear
variable {β δ ι : Type} {P : Submodule ℂ (β → ComplexMatrix2)}
theorem isLinearOn_of_positive {m : (β → ComplexMatrix2) → δ → ComplexMatrix2} (pos : δ → Prop)
    (rev : δ → δ)
    (hrev : ∀ c, ¬ pos c → pos (rev c))
    (hneg : ∀ B c, ¬ pos c → m B c = -m B (rev c))
    (hpos : ∀ c, pos c → ∃ (F : Finset β) (D : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2),
      ∀ B ∈ P, m B c = D (restrictFinset F B)) :
    IsLinearOn P m := by
  have hadd : ∀ B ∈ P, ∀ B' ∈ P, ∀ c, pos c → m (B + B') c = m B c + m B' c :=
    fun B hB B' hB' c hc => by
    obtain ⟨F, D, h⟩ := hpos c hc
    rw [h _ (P.add_mem hB hB'), h _ hB, h _ hB', restrictFinset_add, map_add]
  have hsmul : ∀ B ∈ P, ∀ z : ℂ, ∀ c, pos c → m (z • B) c = z • m B c := fun B hB z c hc => by
    obtain ⟨F, D, h⟩ := hpos c hc
    rw [h _ (P.smul_mem z hB), h _ hB, restrictFinset_smul, map_smul]
  refine fun B hB B' hB' z => ⟨funext fun c => ?_, funext fun c => ?_⟩
  · by_cases hc : pos c
    · exact hadd B hB B' hB' c hc
    · show m (B + B') c = m B c + m B' c
      rw [hneg _ c hc, hneg B c hc, hneg B' c hc, hadd B hB B' hB' _ (hrev c hc), neg_add]
  · by_cases hc : pos c
    · exact hsmul B hB z c hc
    · show m (z • B) c = z • m B c
      rw [hneg _ c hc, hneg B c hc, hsmul B hB z _ (hrev c hc), smul_neg]
theorem finsum_linear_of_local {S : Set ι} (hS : S.Finite)
    {g : ι → (β → ComplexMatrix2) → ComplexMatrix2}
    (h : ∀ x ∈ S, ∃ (F : Finset β) (D : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2),
      ∀ B ∈ P, g x B = D (restrictFinset F B)) {B B' : β → ComplexMatrix2} (hB : B ∈ P)
    (hB' : B' ∈ P) (z : ℂ) :
    ∑ᶠ x ∈ S, g x (B + B') = ∑ᶠ x ∈ S, g x B + ∑ᶠ x ∈ S, g x B' ∧
      ∑ᶠ x ∈ S, g x (z • B) = z • ∑ᶠ x ∈ S, g x B := by
  have hadd : ∀ x ∈ S, g x (B + B') = g x B + g x B' := fun x hx => by
    obtain ⟨F, D, hD⟩ := h x hx
    rw [hD _ (P.add_mem hB hB'), hD _ hB, hD _ hB', restrictFinset_add, map_add]
  have hsmul : ∀ x ∈ S, g x (z • B) = z • g x B := fun x hx => by
    obtain ⟨F, D, hD⟩ := h x hx
    rw [hD _ (P.smul_mem z hB), hD _ hB, restrictFinset_smul, map_smul]
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS]
  constructor
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x hx => hadd x (hS.mem_toFinset.1 hx)
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x hx => hsmul x (hS.mem_toFinset.1 hx)
theorem finsum_mem_traceless {S : Set ι} {g : ι → ComplexMatrix2}
    (h : ∀ x ∈ S, g x ∈ ComplexMatrix2.traceless) :
    ∑ᶠ x ∈ S, g x ∈ ComplexMatrix2.traceless :=
  finsum_mem_induction (fun X => X ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
    (fun _ _ => ComplexMatrix2.traceless.add_mem) h
end Linear
section FiniteSide
variable {L n k : ℕ}
open YangMills.Construction.Tower.LevelwiseMeans (levelwiseMean valuesOrOne IsDefinedAt)
theorem SideInputs.vertex_finite (s : SideInputs L n k) {j : ℕ} (hj : j ≤ k) :
    Finite (Vertex L n k j) := by
  have : Finite (Edge L n k j) := Set.finite_univ_iff.1 (s.edges_finite j hj)
  exact Finite.of_injective
    (fun y : Vertex L n k j => (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k j))
    (fun y y' h => congrArg (fun b : Edge L n k j => b.source) h)
theorem extendOddly_of_not_positive (hor : OrientationFacts L n k) {i : ℕ} (hi : i ≤ k)
    (f : Edge L n k i → ComplexMatrix2) {c : Edge L n k i} (hc : ¬ c.IsPositivelyOriented) :
    extendOddly f c = -extendOddly f c.opposite := by
  classical
  simp [extendOddly, if_neg hc, if_pos (hor.opposite_pos hi hc)]
theorem iter_deriv_local (cal : AnalyticInputs) (s : SideInputs L n k)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) {i : ℕ} (hi : i ≤ k) {c : Edge L n k i}
    (hc : c.IsPositivelyOriented) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k 0) (iterLogRatio U i c) F O h D Q ∧
      ∀ B ∈ complexEdgeForms L n k 0,
        complexIterDeriv L n k i U B c = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := iter_localForm cal s hU hi c
  exact ⟨F, O, h, D, Q, e, fun B hB =>
    complexIterDeriv_eq cal s hU hi hc hB (e.hasDerivAtZeroAlong hB)⟩
theorem mean_deriv_local (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k j) (meanLogRatio V c) F O h D Q ∧
      ∀ B ∈ complexEdgeForms L n k j, complexSmoothingDeriv V B c = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := mean_localForm cal s hj hc hV
  exact ⟨F, O, h, D, Q, e, fun B hB => complexSmoothingDeriv_eq hc (e.hasDerivAtZeroAlong hB)⟩
theorem contour_deriv_local (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms L n k j) (contourLogRatio V y x) F O h D Q ∧
      ∀ B ∈ complexEdgeForms L n k j, logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := contour_localForm cal s hj hx hV
  exact ⟨F, O, h, D, Q, e, fun B hB => contourDeriv_eq (e.hasDerivAtZeroAlong hB)⟩
theorem stepProperties_holds (cal : AnalyticInputs) (s : SideInputs L n k) {j : ℕ} (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L n k) :
    StepConditions j V U := by
  have hi : j + 1 ≤ k := hj
  have hcontour : ∀ y : Vertex L n k (j + 1), ∀ B ∈ complexEdgeForms L n k j,
      ∀ B' ∈ complexEdgeForms L n k j,
      ∀ z : ℂ, contourLogDrift V (B + B') y = contourLogDrift V B y + contourLogDrift V B' y ∧
        contourLogDrift V (z • B) y = z • contourLogDrift V B y := fun y B hB B' hB' z => by
    have := finsum_linear_of_local (P := complexEdgeForms L n k j)
      (S := PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
      (haveI := s.vertex_finite hj.le; Set.toFinite _)
      (g := fun x B => logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B)
      (fun x hx => by
        obtain ⟨F, O, h, D, Q, -, hD⟩ := contour_deriv_local cal s hj hx hV
        exact ⟨F, D, hD⟩) hB hB' z
    simp only [contourLogDrift]
    rw [this.1, this.2, smul_add, smul_comm]
    exact ⟨rfl, rfl⟩
  refine ⟨fun c hc => (iter_localForm cal s hU hi c).1, fun c hc => (mean_localForm cal s hj hc hV).1,
    fun y x hx => (contour_localForm cal s hj hx hV).1, fun c hc B hB => ?_, fun c hc B hB => ?_,
    fun y x hx B hB => ?_, ?_, ?_,
    fun B hB B' hB' z => ⟨funext fun y => (hcontour y B hB B' hB' z).1,
      funext fun y => (hcontour y B hB B' hB' z).2⟩, fun c hc B hB => ?_, fun c hc B hB => ?_,
    fun y B hB => ?_⟩
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU hi hc
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := mean_deriv_local cal s hj hc hV
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := contour_deriv_local cal s hj hx hV
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · refine isLinearOn_of_positive (fun c : Edge L n k (j + 1) => c.IsPositivelyOriented)
      (fun c => c.opposite) (fun c hc => s.orientation.opposite_pos hi hc)
      (fun B c hc => by
        unfold complexIterDeriv holLeftDifferential
        exact extendOddly_of_not_positive s.orientation hi _ hc) fun c hc => ?_
    obtain ⟨F, O, h, D, Q, -, hD⟩ := iter_deriv_local cal s hU hi hc
    exact ⟨F, D, hD⟩
  · refine isLinearOn_of_positive (fun c : Edge L n k (j + 1) => c.IsPositivelyOriented)
      (fun c => c.opposite) (fun c hc => s.orientation.opposite_pos hi hc)
      (fun B c hc => by
        unfold complexSmoothingDeriv holLeftDifferential
        exact extendOddly_of_not_positive s.orientation hi _ hc) fun c hc => ?_
    obtain ⟨F, O, h, D, Q, -, hD⟩ := mean_deriv_local cal s hj hc hV
    exact ⟨F, D, hD⟩
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU hi hc
    rw [hD B hB]
    exact (e.mem_traceless hB).1
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := mean_deriv_local cal s hj hc hV
    rw [hD B hB]
    exact (e.mem_traceless hB).1
  · refine ComplexMatrix2.traceless.smul_mem _ (finsum_mem_traceless fun x hx => ?_)
    obtain ⟨F, O, h, D, Q, e, hD⟩ := contour_deriv_local cal s hj hx hV
    rw [hD B hB]
    exact (e.mem_traceless hB).1
theorem hasUniqueQuadraticTerm_top (cal : AnalyticInputs) (s : SideInputs L n k)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) :
    HasUniqueQuadraticTerm (complexEdgeForms L n k 0) (topLogRatio L n k U)
      (topDeriv L n k U) :=
  hasUniqueQuadraticTerm_of_local fun c => by
    obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU le_rfl c.2
    exact ⟨F, O, h, D, Q, e, fun B hB => hD B hB⟩
theorem ofReal_smul_matrix (r : ℝ) (X : ComplexMatrix2) : (r : ℂ) • X = r • X := by
  ext i j
  simp
theorem ofReal_smul_pi {γ : Type} (r : ℝ) (X : γ → ComplexMatrix2) : (r : ℂ) • X = r • X := by
  funext c
  exact ofReal_smul_matrix r (X c)
theorem halfTrace_mul_self (hp : OneLoop.PauliMatrixRelations) {X : ComplexMatrix2}
    (hsu : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.halfTrace (X * X) = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
  have hsl : X ∈ ComplexMatrix2.traceless := hsu.2
  have h8 := hp.2.2.2.2.2.2.2.1 ⟨X, hsl⟩ hsu
  exact h8.symm
theorem traceFinsumPairing_self_re {ι : Type} [Fintype ι] (f : ι → ComplexMatrix2)
    (h : ∀ i, ComplexMatrix2.halfTrace (f i * f i) = ((‖f i‖ ^ 2 : ℝ) : ℂ)) :
    (traceFinsumPairing f f).re = ∑ i, ‖f i‖ ^ 2 := by
  simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, h, Complex.re_sum, Complex.ofReal_re]
theorem norm_le_traceFinsumNorm {ι : Type} [Fintype ι] (f : ι → ComplexMatrix2)
    (h : ∀ i, ComplexMatrix2.halfTrace (f i * f i) = ((‖f i‖ ^ 2 : ℝ) : ℂ)) (i : ι) :
    ‖f i‖ ≤ traceFinsumNorm f := by
  have hle : ‖f i‖ ^ 2 ≤ ∑ i, ‖f i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)
  unfold traceFinsumNorm
  rw [traceFinsumPairing_self_re f h]
  exact Real.le_sqrt_of_sq_le hle
theorem norm_le_edgeFormNorm (hp : OneLoop.PauliMatrixRelations)
    (hfin : Finite (Edge L n k 0)) {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    {b : Edge L n k 0} (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.operatorNorm (B b) ≤ edgeFormNorm B := by
  have hf : Finite (PositiveEdge L n k 0) := Subtype.finite
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  exact norm_le_traceFinsumNorm (restrictToPositiveEdges B)
    (fun i => halfTrace_mul_self hp (hB.1 i.1 i.2)) (⟨b, hb⟩ : PositiveEdge L n k 0)
theorem supNorm_le_edgeFormNorm (hp : OneLoop.PauliMatrixRelations)
    (hfin : Finite (Edge L n k 0)) (hor : OrientationFacts L n k) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k 0) : supNorm B ≤ edgeFormNorm B := by
  refine Real.iSup_le (fun b => ?_) (Real.sqrt_nonneg _)
  by_cases hb : b.IsPositivelyOriented
  · exact norm_le_edgeFormNorm hp hfin hB hb
  · have r := hB.2 b.opposite
    rw [hor.opposite_opposite 0 (Nat.zero_le _)] at r
    rw [r]
    show ‖-B b.opposite‖ ≤ _
    rw [norm_neg]
    exact norm_le_edgeFormNorm hp hfin hB (hor.opposite_pos (Nat.zero_le _) hb)
theorem eventually_supNorm_lt (hfin : Finite (Edge L n k 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0, supNorm (B : Edge L n k 0 → ComplexMatrix2) < δ := by
  have h₁ : ∀ b : Edge L n k 0, ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0,
      ComplexMatrix2.operatorNorm ((B : Edge L n k 0 → ComplexMatrix2) b) < δ / 2 := fun b => by
    have hc : Continuous fun B : edgeFormSpace L n k 0 => ((B : Edge L n k 0 → ComplexMatrix2) b) :=
      (continuous_apply b).comp continuous_subtype_val
    have := (hc.tendsto 0).norm
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, norm_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [eventually_all.2 h₁] with B hB
  exact lt_of_le_of_lt (Real.iSup_le (fun b => (hB b).le) (half_pos hδ).le) (half_lt_self hδ)
theorem complexQuadraticTerm_eq (cal : AnalyticInputs) (hp : OneLoop.PauliMatrixRelations)
    (s : SideInputs L n k) {U : Edge L n k 0 → ComplexMatrix2} (h₁ : IterLogRatioAnalytic U)
    (h₃ : IterHasUniqueQuadraticExpansion U) (B B' : edgeFormSpace L n k 0) :
    complexQuadraticTerm L n k U B B' = iterQuadraticTerm U B B' := by
  classical
  have hU := h₁.1
  have hfin : Finite (Edge L n k 0) := Set.finite_univ_iff.1 (s.edges_finite 0 (Nat.zero_le _))
  have hspec := (hasUniqueQuadraticTerm_top cal s hU).2.1
  set T := quadraticTerm (complexEdgeForms L n k 0) (topLogRatio L n k U)
    (topDeriv L n k U) with hT
  have hmem : ∀ B : edgeFormSpace L n k 0, (B : Edge L n k 0 → ComplexMatrix2) ∈
      boundedSubmodule (complexEdgeForms L n k 0) := fun B => by
    have h := B.2
    refine ⟨⟨fun b hb => (h.1 b hb).2, h.2⟩, ?_⟩
    obtain ⟨C, hC⟩ := (Set.finite_range fun b =>
      ComplexMatrix2.operatorNorm ((B : Edge L n k 0 → ComplexMatrix2) b)).bddAbove
    exact ⟨C, fun b => hC ⟨b, rfl⟩⟩
  let ι : edgeFormSpace L n k 0 → boundedSubmodule (complexEdgeForms L n k 0) :=
    fun B => ⟨B, hmem B⟩
  have hadd : ∀ B B' : edgeFormSpace L n k 0, ι (B + B') = ι B + ι B' := fun _ _ => rfl
  have hsmul : ∀ (r : ℝ) (B : edgeFormSpace L n k 0), ι (r • B) = (r : ℂ) • ι B := fun r B => by
    refine Subtype.ext ?_
    exact (ofReal_smul_pi r _).symm
  let q : IterBilinearForm L n k := LinearMap.mk₂ ℝ (fun B B' => T (ι B) (ι B'))
    (fun B B' B'' => by rw [hadd, map_add, LinearMap.add_apply])
    (fun r B B' => by rw [hsmul, map_smul, LinearMap.smul_apply, ofReal_smul_pi])
    (fun B B' B'' => by rw [hadd, map_add])
    (fun r B B' => by rw [hsmul, map_smul, ofReal_smul_pi])
  have hqv : ∀ B B' : edgeFormSpace L n k 0, q B B' = T (ι B) (ι B') := fun _ _ => rfl
  have hq : IsIterQuadraticExpansion U q := by
    refine ⟨fun B B' => hspec.1 _ _, fun c => ?_⟩
    obtain ⟨K, δ, hδ, hK⟩ := hspec.2 c
    refine ⟨|K|, ?_⟩
    filter_upwards [h₁.2.2.1, eventually_supNorm_lt hfin hδ] with B hB hn
    have hv : Tower.iterLogRatio U c (B : Edge L n k 0 → ComplexMatrix2) =
        topLogRatio L n k U c (B : Edge L n k 0 → ComplexMatrix2) := by
      simp only [Tower.iterLogRatio, topLogRatio, iterLogRatio, iterRatio,
        iterMean_of_small s.meanStable s.iterated hB.1 le_rfl,
        iterMean_of_small s.meanStable s.iterated hU le_rfl]
    have e₁ : (1 / 2 : ℝ) • q B B c = (1 / 2 : ℂ) • T (ι B) (ι B) c := by
      rw [hqv, ← ofReal_smul_matrix]
      norm_num
    rw [hv, e₁]
    have hb := hK (ι B) hn
    refine hb.trans ?_
    have hn₀ : 0 ≤ supNorm (B : Edge L n k 0 → ComplexMatrix2) := supNorm_nonneg _
    have hle := supNorm_le_edgeFormNorm hp hfin s.orientation B.2
    exact (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hn₀ 3)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn₀ hle 3) (abs_nonneg K))
  have heq : q = iterQuadraticTerm U := h₃.1.unique hq h₃.2.1
  have hval : complexQuadraticTerm L n k U B B' = T (ι B) (ι B') := by
    simp only [complexQuadraticTerm, quadraticTermAt]
    rw [dif_pos ⟨hmem B, hmem B'⟩]
  rw [hval, ← heq]
  rfl
theorem sideRelations_holds (cal : AnalyticInputs) (hp : OneLoop.PauliMatrixRelations)
    (s : SideInputs L n k)
    (hQ : Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
      Tower.IterLogRatioAnalytic U ∧
        Tower.IterDerivIsLinearTaylorTerm U ∧
        Tower.IterHasUniqueQuadraticExpansion U) :
    SideRequirements L n k := by
  refine ⟨fun j hj V hV U hU => stepProperties_holds cal s hj hV hU,
    fun U hU => hasUniqueQuadraticTerm_top cal s hU, ?_⟩
  filter_upwards [hQ] with U hU
  exact ⟨hU.1.1, fun B B' => complexQuadraticTerm_eq cal hp s hU.1 hU.2.2 B B'⟩
end FiniteSide
end YangMills.Construction.Tower.AsDifferentials
namespace YangMills.Construction.Tower.FullSpace.AsDifferentials
open YangMills.Construction.Tower.AsDifferentials
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean IsDefinedAt)
section Bonds
variable {a : ℝ}
theorem opposite_pos (ha : 0 < a) {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpaceChainRule.opposite_isPositivelyOriented_of_not <;> assumption
theorem not_opposite_pos (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
theorem expTwist_mem (hEL : ComplexMatrix2.ExpLogEstimates) (ha : 0 < a)
    {U C : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (hC : C ∈ complexEdgeForms a) : IsFieldIn PeriodicLattice.complexGaugeGroup (expTwist C U) := by
  classical
  have hval : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => expChart_mem_unitDeterminant hEL (hC.1 b hb) (hU.1 b)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb]
      exact hval b hb
    · simp only [expTwist, if_neg hb]
      exact inv_mem_unitDeterminant (hval _ (opposite_pos ha hb))
  · by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb, if_neg (not_opposite_pos ha hb), opposite_opposite]
    · have hr := opposite_pos ha hb
      simp only [expTwist, if_neg hb, if_pos hr]
      exact (inv_inv_of_mem_unitDeterminant (hval _ hr)).symm
theorem extendOddly_of_not_positive (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : ¬ c.IsPositivelyOriented) :
    extendOddly f c = -extendOddly f c.opposite := by
  classical
  simp [extendOddly, if_neg hc, if_pos (opposite_pos ha hc)]
theorem form_mem_traceless {C : InfiniteLattice.Link a → ComplexMatrix2} (hC : C ∈ complexEdgeForms a)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : C b ∈ ComplexMatrix2.traceless :=
  hC.1 b hb
end Bonds
section Tower
variable {L k : ℕ}
def meanFamily (U : Edge L k 0 → ComplexMatrix2) : ∀ i : ℕ, Edge L k i → ComplexMatrix2 :=
  fun i => complexIter L k i U
theorem isMeanSequenceFrom_of_small (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    MeanStableFields.Infinite.IsMeanSequenceFrom k U (meanFamily U) := by
  refine ⟨⟨fun i hi => ?_, fun i hi b => (hU.2 i hi).2 b, fun i hi c hc => rfl⟩, rfl⟩
  cases i with
  | zero => exact hU.1
  | succ i => exact hO.meanStep_mem i (by omega) _ (hU.2 i (by omega))
theorem small_of_meanStable (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {W : Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ MeanStableFields.Infinite.meanStableFields L k k) :
    W ∈ smallIterateFields L k := by
  obtain ⟨V, hV, rfl⟩ := hW
  have key : ∀ i ≤ k, V i = meanFamily (V 0) i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hwr : V i ∈ MeanStableFields.Infinite.fieldsNearOne L k i :=
        ⟨hV.mem_fields i (by omega), hV.norm_sub_one_lt i (by omega)⟩
      have := (hO.meanStep_unique i (by omega) (V i) hwr (V (i + 1))
        (hV.mem_fields _ hi)).1 (hV.eq_mean i (by omega))
      rw [this, ih (by omega)]
      rfl
  refine ⟨hV.mem_fields 0 (Nat.zero_le _), fun j hj => ?_⟩
  have := key j hj.le
  show meanFamily (V 0) j ∈ _
  rw [← this]
  exact ⟨hV.mem_fields j hj.le, hV.norm_sub_one_lt j hj⟩
theorem levelwiseMean_of_small (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k)
    (c : Edge L k i) : levelwiseMean U i c = some (complexIter L k i U c) :=
  hP.eq_levelwiseMean k le_rfl U _ (isMeanSequenceFrom_of_small hO hU) i hi c
theorem iterMean_of_small (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k)
    (c : Edge L k i) : iterMean U i c = complexIter L k i U c := by
  simp [iterMean, valuesOrOne, levelwiseMean_of_small hP hO hU hi c]
structure SideInputs (L k : ℕ) : Prop where
  levelwise : LevelwiseMeans.Unbounded.UnboundedConditions L k
  meanStable : MeanStableFields.Infinite.MeanStableConditions L k
  iterated : IteratedMeans.Unbounded.SpaceConditions L k
  mesh_pos : ∀ i, 0 < meshAt L k i
  doubleBlock : ∀ j < k, ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    DoubleBlockPolydisc.Infinite.PolydiscPropertiesAt L k j (polydiscRadius L) c
  smoothing_congr : ∀ j < k, ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ V V' : Edge L k j → ComplexMatrix2,
    V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c →
    V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c →
    (∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) →
    complexSmoothing L V c = complexSmoothing L V' c
  contour_congr : ∀ j < k, ∀ y : Vertex L k (j + 1),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))) →
    ∀ V' : Edge L k j → ComplexMatrix2, V' ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      ComplexMatrix2.operatorNorm (V' b - 1) < polydiscRadius L) →
    ∀ W : Edge L k j → ComplexMatrix2,
    (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W b = V' b) →
    complexContourMean L W y x = complexContourMean L V' y x
  cube_finite : ∀ j < k, ∀ y : Vertex L k (j + 1),
    (cubeVertices L (meshAt L k j) y).Finite
  presentations_agree : ∀ j ≤ k, UniqueValue.PresentationsAgreeAlongPerturbations L k j ℂ
    PeriodicLattice.complexGaugeGroup UniqueValue.IsComplexTangent ComplexMatrix2
theorem iter_localForm (cal : AnalyticInputs) (s : SideInputs L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k) (c : Edge L k i) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k 0))
        (fun C => IsDefinedAt (expTwist C U) i c)
        (iterRatio U i c) (iterLogRatio U i c) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k 0))
        (iterLogRatio U i c) F O h D Q := by
  have hf : IsDefinedAt U i c := by
    simp [IsDefinedAt, levelwiseMean_of_small s.meanStable s.iterated hU hi c]
  obtain ⟨F, O, f, hw⟩ := s.levelwise.exists_representation i hi c U hU.1 hf
  have hfU : iterMean U i c = f (restrictToEdges F U) := by
    have := hw.eq_some U hU.1 hw.mem
    simp [iterMean, valuesOrOne, this]
  suffices hr : IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented)
        (complexEdgeForms (meshAt L k 0))
        (fun C => IsDefinedAt (expTwist C U) i c)
        (iterRatio U i c) (iterLogRatio U i c) ∧
      ∃ O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k 0))
        (iterLogRatio U i c) F O h D Q from
    ⟨hr.1, F, hr.2⟩
  refine exists_finsetLocalForm cal.traceless cal.analytic cal.unimodular (Equiv.refl _) (𝔇 := O)
    (Φ := f) (u := restrictToEdges F U) hw.mem
    (b₀ := OneLoop.pauliBasis) ?_ hw.finite_edges.1 hw.finite_edges.2
    (fun C hC b hb => form_mem_traceless hC hb) ?_ (fun C => rfl)
  · rw [← asGroupFactors_image]
    exact hw.holomorphic _
  · intro C hC hCO
    have e : expChartFamily (Equiv.refl _) (restrictToEdges F U) (restrictFinset F C) =
        restrictToEdges F (expTwist C U) := by
      funext b
      simp [expChartFamily, restrictToEdges, restrictFinset, expTwist,
        if_pos (hw.finite_edges.2 b b.2)]
    rw [e] at hCO ⊢
    have hv := hw.eq_some _ (expTwist_mem cal.expLog (s.mesh_pos 0) hU.1 hC) hCO
    refine ⟨by simp [IsDefinedAt, hv], ?_⟩
    simp only [iterRatio, hfU]
    simp [iterMean, valuesOrOne, hv]
theorem eqOn_of_positive {a : ℝ} (ha : 0 < a) {P : Set (InfiniteLattice.Link a)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {W W' : InfiniteLattice.Link a → ComplexMatrix2}
    (hW : IsFieldOn PeriodicLattice.complexGaugeGroup P W)
    (hW' : IsFieldOn PeriodicLattice.complexGaugeGroup P W')
    (hag : ∀ b ∈ P, b.IsPositivelyOriented → W b = W' b) : ∀ b ∈ P, W b = W' b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · exact hag b hb hp
  · have hr := opposite_pos ha hp
    have h₁ := hW.2 _ (hrev b hb)
    have h₂ := hW'.2 _ (hrev b hb)
    rw [opposite_opposite] at h₁ h₂
    rw [h₁, h₂, hag _ (hrev b hb) hr]
theorem extendFromPositive_eq {a : ℝ} (ha : 0 < a) {P : Set (InfiniteLattice.Link a)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {W : InfiniteLattice.Link a → ComplexMatrix2}
    (hW : IsFieldOn PeriodicLattice.complexGaugeGroup P W) :
    ∀ b ∈ P, extendFromPositive P (fun b : PositiveEdgeOf P => W b.1) b = W b := by
  classical
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp [extendFromPositive, hb, hp]
  · have hr := opposite_pos ha hp
    have h₁ := hW.2 _ (hrev b hb)
    rw [opposite_opposite] at h₁
    simp [extendFromPositive, hb, hp, hrev b hb, hr, h₁]
theorem isFieldOn_doubleBlock {j : ℕ} {c : Edge L k (j + 1)} {W : Edge L k j → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    IsFieldOn PeriodicLattice.complexGaugeGroup
      (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) W :=
  ⟨fun b _ => hW.1 b, fun b _ => hW.2 b⟩
theorem mem_polydisc_of_eqOn {j : ℕ} {c : Edge L k (j + 1)} {ρ : ℝ}
    (hrev : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
    {W W' : Edge L k j → ComplexMatrix2} (hW : W ∈ nearIdentityPolydisc L k j ρ c)
    (hag : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W' b = W b) :
    W' ∈ nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [hag b hb]
    exact hW.1.1 b hb
  · rw [hag b hb, hag _ (hrev b hb)]
    exact hW.1.2 b hb
  · rw [hag b hb]
    exact hW.2 b hb
theorem mem_polydisc_of_positive_values (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {W : Edge L k j → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (h : (fun b : DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c => W b.1) ∈
      DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c) :
    W ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := by
  have hfo := (s.doubleBlock j hj c hc).finite_open
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, h⟩ := h
  have hag := eqOn_of_positive (s.mesh_pos j) hfo.opposite_mem hW₀.1
    (isFieldOn_doubleBlock hW) fun b hb hp => congrFun h ⟨b, hb, hp⟩
  exact mem_polydisc_of_eqOn hfo.opposite_mem hW₀ fun b hb => (hag b hb).symm
theorem polydisc_localForm (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j)
    {G : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    (hG : ∃ _ : Fintype (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c),
      DoubleBlockPolydisc.IsHolomorphicWithEntries
        (DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c)
        fun v => G (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v))
    (hloc : ∀ W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc L k j (polydiscRadius L) c →
      ∀ W' : Edge L k j → ComplexMatrix2,
        (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W' b = W b) →
        G W' = G W)
    {Defined : (Edge L k j → ComplexMatrix2) → Prop}
    (hDefined : ∀ W ∈ nearIdentityPolydisc L k j (polydiscRadius L) c, Defined W)
    {a v : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    (ha : ∀ C, a C = G (expTwist C V) * (G V)⁻¹)
    (hv : ∀ C, v C = Complex.I⁻¹ • ComplexMatrix2.logSeries (a C)) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k j))
        (fun C => Defined (expTwist C V)) a v ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j)) v F O h D Q := by
  classical
  obtain ⟨inst, hhol⟩ := hG
  have hd := s.doubleBlock j hj c hc
  have hfo := hd.finite_open
  let ρ := polydiscRadius L
  let P := DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c
  let F : Finset (Edge L k j) := hfo.positive_finite.toFinset
  have hFmem : ∀ b, b ∈ F ↔ b ∈ DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c :=
    fun b => by
    simp [F]
  let ε : F ≃ DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c :=
    Equiv.subtypeEquivRight hFmem
  let u : DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c → ComplexMatrix2 :=
    fun b => V b.1
  have hVp : V ∈ nearIdentityPolydisc L k j ρ c := s.meanStable.mem_polydisc j hj c hc V hV
  have hu : u ∈ DoubleBlockPolydisc.Infinite.polydiscPositive L k j ρ c :=
    ⟨BondSetFields.restrictTo P V, ⟨V, hVp, rfl⟩, rfl⟩
  have hrev : ∀ b ∈ P, b.opposite ∈ P := hfo.opposite_mem
  have hGval : ∀ W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc L k j ρ c →
      G (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c fun b => W b.1) = G W :=
    fun W hW hWp => hloc W hW hWp _
      (extendFromPositive_eq (s.mesh_pos j) hrev (isFieldOn_doubleBlock hW))
  suffices hr : IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented)
        (complexEdgeForms (meshAt L k j)) (fun C => Defined (expTwist C V)) a v ∧
      ∃ O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j)) v F O h D Q from
    ⟨hr.1, F, hr.2⟩
  refine exists_finsetLocalForm cal.traceless cal.analytic cal.unimodular ε
    (𝔇 := DoubleBlockPolydisc.Infinite.polydiscPositive L k j ρ c)
    (Φ := fun v => G (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v)) (u := u) hu
    (b₀ := OneLoop.pauliBasis) (hhol.toUnimodular _) ?_ ?_
    (fun C hC b hb => form_mem_traceless hC hb) ?_ hv
  · obtain ⟨b, hb⟩ := hfo.positive_nonempty
    exact ⟨b, (hFmem b).2 hb⟩
  · exact fun b hb => ((hFmem b).1 hb).2
  · intro C hC hCO
    set W := expTwist C V with hWdef
    have hW : W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
      expTwist_mem cal.expLog (s.mesh_pos j) hV.1 hC
    have e : expChartFamily ε u (restrictFinset F C) = fun b => W b.1 := by
      funext b
      simp [expChartFamily, restrictFinset, u, ε, hWdef, expTwist, if_pos b.2.2]
    rw [e] at hCO ⊢
    have hWp : W ∈ nearIdentityPolydisc L k j ρ c := mem_polydisc_of_positive_values s hj hc hW hCO
    refine ⟨hDefined W hWp, ?_⟩
    rw [ha C, hGval W hW hWp]
    exact congrArg (fun X => G W * X⁻¹) (hGval V hV.1 hVp).symm
theorem mean_localForm (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k j))
        (fun C => expTwist C V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
        (meanRatio V c) (meanLogRatio V c) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j))
        (meanLogRatio V c) F O h D Q :=
  polydisc_localForm cal s hj hc hV (G := fun W => complexSmoothing L W c)
    (s.doubleBlock j hj c hc).holomorphic_smoothing
    (fun W _ hWp W' h => s.smoothing_congr j hj c hc W' W
      (mem_polydisc_of_eqOn (s.doubleBlock j hj c hc).finite_open.opposite_mem hWp h)
      hWp h)
    (Defined := fun W => W ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (fun W hW => hW) (fun _ => rfl) (fun _ => rfl)
theorem exists_positive_incident {j : ℕ} (y : Vertex L k j) :
    ∃ c : Edge L k j, c.IsPositivelyOriented ∧
      y ∈ ({c.initial, c.terminal} : Set (Vertex L k j)) :=
  ⟨⟨y, y + InfiniteLattice.axisStep _ 0, 0, Or.inl (by simp)⟩, ⟨0, by simp⟩, Or.inl rfl⟩
theorem contour_localForm (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k j))
        (fun C => ContourDefined y (expTwist C V))
        (contourRatio V y x) (contourLogRatio V y x) ∧
      ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j))
        (contourLogRatio V y x) F O h D Q := by
  obtain ⟨c, hc, hy⟩ := exists_positive_incident y
  exact polydisc_localForm cal s hj hc hV (G := fun W => complexContourMean L W y x)
    ((s.doubleBlock j hj c hc).holomorphic_contourMean y hy x hx)
    (fun W hW hWp W' h => s.contour_congr j hj y x hx c hc hy W hW hWp.2 W' h)
    (Defined := ContourDefined y) (fun W hW => ⟨c, hc, hy, hW⟩) (fun _ => rfl) (fun _ => rfl)
theorem valueViaPresentation_eventually (s : SideInputs L k) {j : ℕ} (hj : j ≤ k)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    (hopen : IsFinitelyOpen PeriodicLattice.complexGaugeGroup 𝔇)
    {h : (Edge L k j → ComplexMatrix2) → ComplexMatrix2} {U : Edge L k j → ComplexMatrix2}
    (hU : U ∈ 𝔇) {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {F₀ : Finset (Edge L k j)} {O₀ : Set (F₀ → ComplexMatrix2)}
    {f₀ : (F₀ → ComplexMatrix2) → ComplexMatrix2}
    (hw₀ : IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 h U F₀ O₀ f₀)
    (hhol : holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv F₀ O₀ f₀)
    {F : Finset (Edge L k j)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (hw : IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 h U F O f)
    {B : Edge L k j → ComplexMatrix2} (hB : UniqueValue.IsComplexTangent B) :
    ∀ᶠ t : ℂ in 𝓝 0, (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b) ∈ O ∧
      valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
        (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv) h U (t • B) =
        f fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b := by
  have hspec := Classical.epsilon_spec (p := fun w : LocalData L k j ComplexMatrix2 =>
    IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 h U w.support w.region w.fn ∧
      holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv
        w.support w.region w.fn)
    ⟨⟨F₀, O₀, f₀⟩, hw₀, hhol⟩
  obtain ⟨ε, hε, hone⟩ := s.presentations_agree j hj 𝔇 hopen h U hU _ _ _ F O f hspec.1 hw B 0 hB
    (fun b _ => ComplexMatrix2.traceless.zero_mem)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  obtain ⟨-, h₂, h₃⟩ := hone t 0 (by simpa using ht) (by simpa using hε)
  have e : ∀ F' : Finset (Edge L k j), UniqueValue.perturbedTuple F' B 0 U
      (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0) =
      fun b : F' => ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b := fun F' => by
    funext b
    simp [UniqueValue.perturbedTuple]
  rw [e] at h₂ h₃
  rw [e] at h₃
  exact ⟨h₂, h₃⟩
theorem meanStable_of_small (s : SideInputs L k) {W : Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ smallIterateFields L k) :
    W ∈ MeanStableFields.Infinite.meanStableFields L k k :=
  ⟨meanFamily W, isMeanSequenceFrom_of_small s.iterated hW⟩
theorem smallIterateFields_finitelyOpen (s : SideInputs L k) :
    IsFinitelyOpen PeriodicLattice.complexGaugeGroup (smallIterateFields L k) := by
  have hset : smallIterateFields L k = MeanStableFields.Infinite.meanStableFields L k k :=
    Set.ext fun W => ⟨meanStable_of_small s, small_of_meanStable s.iterated⟩
  rw [hset]
  exact s.meanStable.isFinitelyOpen
theorem complexIterDeriv_eq (s : SideInputs L k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k) {c : Edge L k i}
    (hc : c.IsPositivelyOriented) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0))
    {D : ComplexMatrix2} (hD : HasDerivAtZeroAlong (iterLogRatio U i c) B D) :
    complexIterDeriv L k i U B c = D := by
  classical
  have hS := meanStable_of_small s hU
  obtain ⟨F, O, f, hw⟩ := s.meanStable.exists_representation i hi c hc U hS
  obtain ⟨hw₁, hh⟩ := s.meanStable.representation_spec i hi c hc U hS F O f hw
  have hwr : IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallIterateFields L k)
      (fun U' => complexIter L k i U' c) U F O f :=
    ⟨hw₁.1, hw₁.2.1, hw₁.2.2.1, fun U' hU' hO => by
      have := hw₁.2.2.2 U' (meanStable_of_small s hU') hO
      rw [← this]
      exact (iterMean_of_small s.meanStable s.iterated hU' hi c).symm⟩
  have hv := valueViaPresentation_eventually s (Nat.zero_le k) (smallIterateFields_finitelyOpen s)
    hU hwr (hh OneLoop.pauliBasis) hwr (B := B) (fun b hb => form_mem_traceless hB hb)
  have hc₂ := s.levelwise.represents_along_curves i hi c U hU.1 F O f hw B
    (fun b hb => form_mem_traceless hB hb)
  simp only [complexIterDeriv, holLeftDifferential, extendOddly, if_pos hc,
    logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  refine smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (iterRatio U i c (t • B))) hD ?_
  filter_upwards [hv, hc₂] with t h₁ h₂
  have e : iterMean (expTwist (t • B) U) i c = f fun b : F =>
      ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b := by
    simp only [iterMean, valuesOrOne, h₂.2]
    rfl
  simp only [iterRatio, iterMean_of_small s.meanStable s.iterated hU hi, e, h₁.2]
theorem complexSmoothingDeriv_eq (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) {D : ComplexMatrix2}
    (hD : HasDerivAtZeroAlong (meanLogRatio V c) B D) :
    complexSmoothingDeriv V B c = D := by
  classical
  have hh := s.meanStable.holomorphic_smoothing j hj c hc OneLoop.pauliBasis
  obtain ⟨F₀, O₀, f₀, hw₀, hol⟩ := hh.2 V hV
  obtain ⟨F, hF, hwr⟩ := s.meanStable.polydisc_presentation j hj c hc
  have hv := valueViaPresentation_eventually s hj.le (s.meanStable.isFinitelyOpen_nearOne j hj) hV
    hw₀ hol (hwr V hV) (B := B) (fun b hb => form_mem_traceless hB hb)
  have hfo := (s.doubleBlock j hj c hc).finite_open
  simp only [complexSmoothingDeriv, holLeftDifferential, extendOddly, if_pos hc,
    logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  refine smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (meanRatio V c (t • B))) hD ?_
  filter_upwards [hv] with t ⟨h₁, h₂⟩
  set W := expTwist (t • B) V with hWdef
  have hW : W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    expTwist_mem cal.expLog (s.mesh_pos j) hV.1 ((complexEdgeForms _).smul_mem t hB)
  have hpoint : MeanStableFields.Infinite.pointOfFinset c F hF
      (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b) = fun b => W b.1 := by
    funext b
    simp [MeanStableFields.Infinite.pointOfFinset, hWdef, expTwist, if_pos b.2.2]
  have hWp : W ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := by
    refine mem_polydisc_of_positive_values s hj hc hW ?_
    rw [← hpoint]
    exact h₁
  have hav : MeanStableFields.Infinite.smoothingOnFinset c F hF
      (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b) =
        complexSmoothing L W c := by
    simp only [MeanStableFields.Infinite.smoothingOnFinset, hpoint]
    have hag := extendFromPositive_eq (s.mesh_pos j) hfo.opposite_mem
      (isFieldOn_doubleBlock (c := c) hW)
    exact s.smoothing_congr j hj c hc _ _ (mem_polydisc_of_eqOn hfo.opposite_mem hWp hag) hWp
      hag
  have h₂' : valueViaPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
      (holomorphicPresentations L k j OneLoop.pauliBasis Coordinates.ComplexCoordinates.matrixEquiv)
      (fun U' => smoothingMap L k j U' c) V (t • B) = complexSmoothing L W c := h₂.trans hav
  rw [h₂']
  rfl
theorem contourDeriv_eq {j : ℕ} {V B : Edge L k j → ComplexMatrix2}
    {y : Vertex L k (j + 1)} {x : Vertex L k j} {D : ComplexMatrix2}
    (hD : HasDerivAtZeroAlong (contourLogRatio V y x) B D) :
    logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
      (complexContourMean L V y x) B = D := by
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  exact smul_deriv_eq_of_hasDerivAt
    (f := fun t => ComplexMatrix2.logSeries (contourRatio V y x (t • B))) hD
    (Filter.EventuallyEq.of_eq rfl)
end Tower
section Requirements
variable {L k : ℕ}
theorem iter_deriv_local (cal : AnalyticInputs) (s : SideInputs L k)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) {i : ℕ} (hi : i ≤ k) {c : Edge L k i}
    (hc : c.IsPositivelyOriented) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k 0))
        (iterLogRatio U i c) F O h D Q ∧
      ∀ B ∈ complexEdgeForms (meshAt L k 0),
        complexIterDeriv L k i U B c = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := iter_localForm cal s hU hi c
  exact ⟨F, O, h, D, Q, e, fun B hB =>
    complexIterDeriv_eq s hU hi hc hB (e.hasDerivAtZeroAlong hB)⟩
theorem mean_deriv_local (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j))
        (meanLogRatio V c) F O h D Q ∧
      ∀ B ∈ complexEdgeForms (meshAt L k j),
        complexSmoothingDeriv V B c = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := mean_localForm cal s hj hc hV
  exact ⟨F, O, h, D, Q, e, fun B hB =>
    complexSmoothingDeriv_eq cal s hj hc hV hB (e.hasDerivAtZeroAlong hB)⟩
theorem contour_deriv_local (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    ∃ F O h D Q, FinsetLocalForm (complexEdgeForms (meshAt L k j))
        (contourLogRatio V y x) F O h D Q ∧
      ∀ B ∈ complexEdgeForms (meshAt L k j), logDirectionalDeriv ℂ
        (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B = D (restrictFinset F B) := by
  obtain ⟨-, F, O, h, D, Q, e⟩ := contour_localForm cal s hj hx hV
  exact ⟨F, O, h, D, Q, e, fun B hB => contourDeriv_eq (e.hasDerivAtZeroAlong hB)⟩
theorem stepProperties_holds (cal : AnalyticInputs) (s : SideInputs L k) {j : ℕ} (hj : j < k)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    StepConditions j V U := by
  have hi : j + 1 ≤ k := hj
  have hsp := s.mesh_pos (j + 1)
  have hcontour : ∀ y : Vertex L k (j + 1), ∀ B ∈ complexEdgeForms (meshAt L k j),
      ∀ B' ∈ complexEdgeForms (meshAt L k j), ∀ z : ℂ,
        contourLogDrift V (B + B') y = contourLogDrift V B y + contourLogDrift V B' y ∧
        contourLogDrift V (z • B) y = z • contourLogDrift V B y := fun y B hB B' hB' z => by
    have := finsum_linear_of_local (P := complexEdgeForms (meshAt L k j))
      (S := cubeVertices L (meshAt L k j) y) (s.cube_finite j hj y)
      (g := fun x B => logDirectionalDeriv ℂ
        (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B)
      (fun x hx => by
        obtain ⟨F, O, h, D, Q, -, hD⟩ := contour_deriv_local cal s hj hx hV
        exact ⟨F, D, hD⟩) hB hB' z
    simp only [contourLogDrift]
    rw [this.1, this.2, smul_add, smul_comm]
    exact ⟨rfl, rfl⟩
  refine ⟨fun c hc => (iter_localForm cal s hU hi c).1, fun c hc => (mean_localForm cal s hj hc hV).1,
    fun y x hx => (contour_localForm cal s hj hx hV).1, fun c hc B hB => ?_, fun c hc B hB => ?_,
    fun y x hx B hB => ?_, ?_, ?_,
    fun B hB B' hB' z => ⟨funext fun y => (hcontour y B hB B' hB' z).1,
      funext fun y => (hcontour y B hB B' hB' z).2⟩, fun c hc B hB => ?_, fun c hc B hB => ?_,
    fun y B hB => ?_⟩
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU hi hc
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := mean_deriv_local cal s hj hc hV
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := contour_deriv_local cal s hj hx hV
    rw [hD B hB]
    exact e.hasDerivAtZeroAlong hB
  · refine isLinearOn_of_positive (fun c : Edge L k (j + 1) => c.IsPositivelyOriented)
      (fun c => c.opposite) (fun c hc => opposite_pos hsp hc)
      (fun B c hc => by
        unfold complexIterDeriv holLeftDifferential
        exact extendOddly_of_not_positive hsp _ hc) fun c hc => ?_
    obtain ⟨F, O, h, D, Q, -, hD⟩ := iter_deriv_local cal s hU hi hc
    exact ⟨F, D, hD⟩
  · refine isLinearOn_of_positive (fun c : Edge L k (j + 1) => c.IsPositivelyOriented)
      (fun c => c.opposite) (fun c hc => opposite_pos hsp hc)
      (fun B c hc => by
        unfold complexSmoothingDeriv holLeftDifferential
        exact extendOddly_of_not_positive hsp _ hc) fun c hc => ?_
    obtain ⟨F, O, h, D, Q, -, hD⟩ := mean_deriv_local cal s hj hc hV
    exact ⟨F, D, hD⟩
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU hi hc
    rw [hD B hB]
    exact (e.mem_traceless hB).1
  · obtain ⟨F, O, h, D, Q, e, hD⟩ := mean_deriv_local cal s hj hc hV
    rw [hD B hB]
    exact (e.mem_traceless hB).1
  · refine ComplexMatrix2.traceless.smul_mem _ (finsum_mem_traceless fun x hx => ?_)
    obtain ⟨F, O, h, D, Q, e, hD⟩ := contour_deriv_local cal s hj hx hV
    rw [hD B hB]
    exact (e.mem_traceless hB).1
theorem covariantAverage_properties (cal : AnalyticInputs) (s : SideInputs L k) : Requirements L k :=
  ⟨fun j hj V hV U hU => stepProperties_holds cal s hj hV hU, fun U hU =>
    hasUniqueQuadraticTerm_of_local fun c => by
      obtain ⟨F, O, h, D, Q, e, hD⟩ := iter_deriv_local cal s hU le_rfl c.2
      exact ⟨F, O, h, D, Q, e, fun B hB => hD B hB⟩⟩
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) : 0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem complexSmoothing_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented) {V V' : Edge L k i → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k i) c, V b = V' b) :
    complexSmoothing L V c = complexSmoothing L V' c := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.complexSmoothing_congr <;> assumption
theorem cubeVertices_finite (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k) (y : Vertex L k (i + 1)) :
    (cubeVertices L (meshAt L k i) y).Finite := by
  have hb := (hZ L k (i + 1) hL (by omega) (by omega) hi).2.1 y
  have hcard : (cube L (meshAt L k i) y).ncard = L ^ 4 := hb.2.2.1
  have hpos : 0 < L := by have := hL.2; omega
  have hfin : (cube L (meshAt L k i) y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  exact Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn hfin
end Requirements
end YangMills.Construction.Tower.FullSpace.AsDifferentials
namespace YangMills.Construction.Tower.AsDifferentials
theorem covariantMeansAreDerivatives_holds
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hp : OneLoop.PauliMatrixRelations)
    (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hB : PairContourIndependence.Statement)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hQ : IterLeftChartExpansion)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQt : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hZ : BlockStructure)
    (hL2 : FullSpace.UniqueValue.PresentationsAgreeAndBallsOpen) :
    CovariantMeansAreDerivatives := by
  classical
  intro L hL k hk
  have cal : AnalyticInputs := ⟨hT, hA, hV, hEL⟩
  refine ⟨fun n hn => ?_, ?_⟩
  · refine sideRelations_holds cal hp ⟨(hH L hL k hk).1 n hn, (hW L hL k hk).1 n hn,
      (hO L hL k hk).1 n hn, orientationFacts hE hL hn hk,
      fun j hj c hc => (hP L hL k j hj).1 n hn c hc,
      fun j hj c hc V V' he => ?_, fun j hj y x hx c hc hy V' hconf hw W hr => ?_,
      fun j hj => ((hE6 L hL k j hj).1 n hn).2.1⟩ (hQ L n k hL hn hk)
    · unfold PeriodicLattice.complexBlockAverage
      simp only [if_pos hc]
      exact (hR L n k j hL.1 hL.2 hn hj c hc).average_eq _ _ he
    · exact ((hB L hL k j hj).1 n hn y x hx c c hc hc hy hy V' hconf hw hw W V' hr
        (fun _ _ => rfl)).2.2
  · refine FullSpace.AsDifferentials.covariantAverage_properties cal
      ⟨(hH L hL k hk).2, (hW L hL k hk).2, (hO L hL k hk).2,
        FullSpace.AsDifferentials.meshAt_pos hL,
        fun j hj c hc => (hP L hL k j hj).2 c hc,
        fun j hj c hc V V' h₁ h₂ he =>
          FullSpace.AsDifferentials.complexSmoothing_congr hS hQt hL hj hc h₁ h₂ he,
        fun j hj y x hx c hc hy V' hconf hw W hr =>
          ((hB L hL k j hj).2 y x hx c c hc hc hy hy V' hconf hw hw W V' hr
            (fun _ _ => rfl)).2.2,
        fun j hj y => FullSpace.AsDifferentials.cubeVertices_finite hZ hL hj y,
        fun j hj => ?_⟩
    exact (hL2 L k j hL.1 hL.2 hj).1.2.2.2
end YangMills.Construction.Tower.AsDifferentials
end
