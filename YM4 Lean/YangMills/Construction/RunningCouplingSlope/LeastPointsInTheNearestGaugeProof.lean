import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPointsProof
import YangMills.Construction.Towers.ContourDerivativeOfGaugeDirectionsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NearestGaugeMinimizerProof
open YangMills.Construction.Matrices
open YangMills.Construction.Tower
open YangMills.Construction.Tower.LeftChartFields
section SmoothnessAtOne
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_inv_of_eq_one {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀)
    (h1 : f p₀ = 1) : ContDiffAt ℝ m (fun p => (f p)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p36358 <;> assumption
private def matrixEntryCLM (a b : Fin 2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem contDiffAt_det {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => Matrix.det (f p)) p₀ := by apply _root_.YangMills.SharedProofs.p54943 <;> assumption
private theorem contDiffAt_cpow_half_of_eq_one {f : P → ℂ} (hf : ContDiffAt ℝ m f p₀)
    (h1 : f p₀ = 1) : ContDiffAt ℝ m (fun p => f p ^ (1 / 2 : ℂ)) p₀ := by apply _root_.YangMills.SharedProofs.p99689 <;> assumption
end SmoothnessAtOne
section AlongAFamily
variable {L n k j : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_pathHolonomy {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (Γ : List (Edge L n k j)) :
    ContDiffAt ℝ m (fun p => PeriodicLattice.pathHolonomy (V p) Γ) p₀ := by apply _root_.YangMills.SharedProofs.p35651 <;> assumption
private theorem contDiffAt_contourMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) :
    ContDiffAt ℝ m (fun p => contourMean (V p) c) p₀ := by apply _root_.YangMills.SharedProofs.p17315 <;> assumption
private theorem contDiffAt_meanRadius [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (hc : Matrix.det (contourMean (V p₀) c) = 1) :
    ContDiffAt ℝ m (fun p => meanRadius (V p) c) p₀ :=
  contDiffAt_cpow_half_of_eq_one (contDiffAt_det (contDiffAt_contourMean hV h1 c)) hc
private theorem contDiffAt_normalizedMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (hc : meanRadius (V p₀) c = 1)
    (hd : Matrix.det (contourMean (V p₀) c) = 1) :
    ContDiffAt ℝ m (fun p => normalizedMean (V p) c) p₀ := by apply _root_.YangMills.SharedProofs.p35211 <;> assumption
end AlongAFamily
section LevelFields
variable {L n k : ℕ}
private theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_of_not_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p3610 <;> assumption
private structure TowerFacts (L n k : ℕ) : Prop where
  finite_vertex : ∀ j, j ≤ k → Finite (Vertex L n k j)
  finite_pos : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  finite_edge : ∀ j, j ≤ k → Finite (Edge L n k j)
  finite_face : Finite (Face L n k 0)
  deriv_at_one : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j, ∀ c : Edge L n k (j + 1),
    c.IsPositivelyOriented →
    leftDifferential normalizedMean (fun _ => 1) B c = linearSmoothing L n k j B c
  smoothing_mem : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
    linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1)
  not_both : ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
    ¬ b.opposite.IsPositivelyOriented
  at_one : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      meanRadius (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  left_mem : ∀ j, j ≤ k → (finiteData L n k j).LeftExpMulMemGroup
  log_curves : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_levelField (hT : TowerFacts L n k) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) : ∀ j, j ≤ k →
      (∀ b, ContDiffAt ℝ m (fun p => levelField (X p) j b) p₀) ∧
        levelField (X p₀) j = fun _ => 1 := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hb, ?_⟩
    rw [h0]
    rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨ih1, ih2⟩ := ih hj.le
    haveI := hT.finite_vertex j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
        ContDiffAt ℝ m (fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c) p₀ ∧
        (X p₀).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X p₀) j) c = 1 := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := hT.at_one j hj c hc
      refine ⟨(hn _ _).mul (contDiffAt_normalizedMean ih1 ih2 c ?_ ?_), ?_⟩
      · rw [ih2, h2]
      · rw [ih2, h1]
        simp
      · rw [ih2, h3, h0]
        simp [unitPoint]
    have hval : levelField (X p₀) (j + 1) = fun _ => 1 := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · rw [levelField_succ_of_pos _ hj c hc]
        exact (hpos c hc).2
      · have hc' : c.opposite.IsPositivelyOriented :=
          (isPositivelyOriented_or_opposite c).resolve_left hc
        rw [levelField_succ_of_not_pos _ hj c hc hc', (hpos c.opposite hc').2]
        simp
    refine ⟨fun c => ?_, hval⟩
    by_cases hc : c.IsPositivelyOriented
    · have e : (fun p => levelField (X p) (j + 1) c) = fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c := by
        funext p
        exact levelField_succ_of_pos _ hj c hc
      rw [e]
      exact (hpos c hc).1
    · have hc' : c.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite c).resolve_left hc
      have e : (fun p => levelField (X p) (j + 1) c) = fun p =>
          ((X p).noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ *
            normalizedMean (levelField (X p) j) c.opposite)⁻¹ := by
        funext p
        exact levelField_succ_of_not_pos _ hj c hc hc'
      rw [e]
      exact contDiffAt_inv_of_eq_one (hpos c.opposite hc').1 (hpos c.opposite hc').2
private theorem contDiffAt_meanRadius_levelField (hT : TowerFacts L n k)
    {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ContDiffAt ℝ m (fun p => meanRadius (levelField (X p) i) c) p₀ := by
  obtain ⟨h1, h2⟩ := contDiffAt_levelField hT hb hn h0 i hi.le
  haveI := hT.finite_vertex i hi.le
  refine contDiffAt_meanRadius h1 h2 c ?_
  rw [h2, (hT.at_one i hi c hc).1]
  simp
private theorem matExp_I_smul_zero :
    ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero]
  exact NormedSpace.exp_zero
end LevelFields
section ExponentialCurves
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_matExp_I_smul_line (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.SharedProofs.p9756 <;> assumption
private theorem matExp_I_smul_zero_smul (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by apply _root_.YangMills.SharedProofs.p11429 <;> assumption
variable {L n k j : ℕ}
private def twistVelocity (V M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then Complex.I • M b * V b else V b * (Complex.I • M b)
private theorem opposite_opposite_edge (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem inv_opposite_of_mem_fieldsIn {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    (V b.opposite)⁻¹ = V b := by apply _root_.YangMills.SharedProofs.p4213 <;> assumption
private theorem hasDerivAt_expTwist_line {V M : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) (twistVelocity V M b) 0 := by apply _root_.YangMills.DeltaSharedProofs.p350 <;> assumption
private theorem expTwist_zero {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist (0 : Edge L n k j → ComplexMatrix2) V = V := by apply _root_.YangMills.SharedProofs.p57400 <;> assumption
end ExponentialCurves
section TangentTransport
variable {L n k : ℕ}
private theorem extendOddly_opposite (hT : TowerFacts L n k) {j : ℕ} (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hb' := hT.not_both j hj b hb
    simp only [extendOddly, if_pos hb, if_neg hb', opposite_opposite_edge]
  · have hb' : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [extendOddly, if_pos hb', if_neg hb, neg_neg]
private theorem levelField_succ_opposite (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c = (levelField X (j + 1) c.opposite)⁻¹ := by
  rw [levelField_succ_of_not_pos X hj c hc hc', levelField_succ_of_pos X hj c.opposite hc']
private def MeanRegularNear (L n k : ℕ) (ρ : ℝ) : Prop :=
  ∀ j, j < k → ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      meanRadius V c ≠ 0 ∧ ‖meanRadius V c - 1‖ < 1 / 2 ∧
      ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 ∧
      normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
      ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2,
        ∀ (g : Edge L n k j → ComplexMatrix2)
        (γ : ℝ → Edge L n k j → ComplexMatrix2), γ 0 = V →
        (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
          HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0
private theorem mem_fieldsIn_complex {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
private theorem det_eq_one_of_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
end TangentTransport
section CompactValues
private def IsQuaternionic (A : ComplexMatrix2) : Prop :=
  A 1 1 = (starRingEnd ℂ) (A 0 0) ∧ A 1 0 = -(starRingEnd ℂ) (A 0 1)
private theorem isQuaternionic_of_compact {A : ComplexMatrix2}
    (h : A ∈ PeriodicLattice.compactGaugeGroup) : IsQuaternionic A := by
  obtain ⟨h1, h2⟩ := Matrix.mem_specialUnitaryGroup_iff.mp h
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp h1
  have e : Matrix.adjugate A = star A := by
    calc Matrix.adjugate A = Matrix.adjugate A * (A * star A) := by rw [hu, mul_one]
      _ = (Matrix.adjugate A * A) * star A := by rw [mul_assoc]
      _ = star A := by rw [Matrix.adjugate_mul, h2, one_smul, one_mul]
  rw [Matrix.adjugate_fin_two] at e
  have e00 := congrFun (congrFun e 0) 0
  have e10 := congrFun (congrFun e 0) 1
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at e00 e10
  refine ⟨e00, ?_⟩
  rw [neg_eq_iff_eq_neg] at e10
  rw [e10]
  simp
private theorem isQuaternionic_add {A B : ComplexMatrix2} (hA : IsQuaternionic A)
    (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by
  refine ⟨?_, ?_⟩
  · simp [hA.1, hB.1]
  · simp [hA.2, hB.2]
    ring
private theorem isQuaternionic_zero : IsQuaternionic 0 := by
  refine ⟨?_, ?_⟩ <;> simp
private theorem isQuaternionic_real_smul (r : ℝ) {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    IsQuaternionic ((r : ℂ) • A) := by
  refine ⟨?_, ?_⟩
  · simp [hA.1]
  · simp [hA.2]
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
variable {L n k j : ℕ}
private theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p2470 <;> assumption
private theorem normalizedMean_mem_compact [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hu : Matrix.det (normalizedMean V c) = 1) :
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p11178 <;> assumption
private theorem expTwist_mem_fieldSpace (hT : TowerFacts L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) (t : ℝ) :
    PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V ∈ fieldSpace L n k j := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t • (M : Edge L n k j → ComplexMatrix2)) b)) * V b ∈
        PeriodicLattice.compactGaugeGroup := by
    intro b hb
    have h := ((hT.left_mem j hj).1 V hV (M : Edge L n k j → ComplexMatrix2) M.2 ⟨b, hb⟩).1 t
    have e : ((t : ℂ) • (M : Edge L n k j → ComplexMatrix2) b) =
        (t • (M : Edge L n k j → ComplexMatrix2)) b :=
      Complex.coe_smul _ _
    simp only [leftExpMul, LatticeData.onPositive, finiteData] at h
    rwa [e] at h
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_compact (hpos _ ((isPositivelyOriented_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := hT.not_both j hj b hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', opposite_opposite_edge]
    · have hb' : b.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [Matrix.nonsing_inv_nonsing_inv _
        (isUnit_det_of_eq_one (det_eq_one_of_compact (hpos _ hb')))]
end CompactValues
section TopDerivative
variable {L n k j : ℕ}
private theorem expTwist_line_near (hT : TowerFacts L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) {ρ : ℝ}
    (hnear : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ b, ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1) < ρ := by
  haveI := hT.finite_edge j hj
  have hc := mem_fieldsIn_complex hV
  have h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b, ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1) < ρ := by
    refine Filter.eventually_all.mpr fun b => ?_
    have h1 := (hasDerivAt_expTwist_line hc M.2.2 b).continuousAt
    have h2 : Tendsto (fun t : ℝ =>
        ‖PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1‖)
        (𝓝 0) (𝓝 ‖V b - 1‖) := by
      have h3 := ((h1.tendsto.sub_const (1 : ComplexMatrix2)).norm)
      simpa only [zero_smul, expTwist_zero hc] using h3
    exact h2.eventually_lt_const (hnear b)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun t ht => hh (by simpa [Real.dist_eq] using ht)⟩
end TopDerivative
section Limits
private theorem det_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit (Matrix.det g) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem det_isQuaternionic {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    Matrix.det A = ((Complex.normSq (A 0 0) + Complex.normSq (A 0 1) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, hA.1, hA.2]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  ring
private theorem traceDefect_nonneg_and_eq_zero {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g ∧ (traceDefect g = 0 → g = 1) := by apply _root_.YangMills.SharedProofs.p27652 <;> assumption
private theorem tendsto_matrix_inv {ι : Type*} {l : Filter ι} {f : ι → ComplexMatrix2}
    {A : ComplexMatrix2} (hf : Tendsto f l (𝓝 A)) (hA : Matrix.det A = 1) :
    Tendsto (fun m => (f m)⁻¹) l (𝓝 A⁻¹) := by apply _root_.YangMills.SharedProofs.p953 <;> assumption
variable {L n k j : ℕ}
private theorem tendsto_pathHolonomy {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2} (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b)))
    (Γ : List (Edge L n k j)) :
    Tendsto (fun m => PeriodicLattice.pathHolonomy (W m) Γ) l
      (𝓝 (PeriodicLattice.pathHolonomy V Γ)) := by apply _root_.YangMills.SharedProofs.p17103 <;> assumption
private theorem tendsto_contourMean [Finite (Vertex L n k j)] {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (c : Edge L n k (j + 1)) :
    Tendsto (fun m => contourMean (W m) c) l (𝓝 (contourMean V c)) := by apply _root_.YangMills.SharedProofs.p67763 <;> assumption
private theorem contourMean_isQuaternionic [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    IsQuaternionic (contourMean V c) := by
    simp only [contourMean]
    have e : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
        (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
      simp [PeriodicLattice.inverseFourthPowerWeight]
    rw [e]
    refine isQuaternionic_real_smul _ ?_
    refine finsum_mem_induction IsQuaternionic isQuaternionic_zero
      (fun _ _ => isQuaternionic_add) fun x _ => ?_
    have hs : ∀ s : Finset (Equiv.Perm (Fin 4)),
        IsQuaternionic (∑ π ∈ s, contourHolonomy V c x π) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simpa using isQuaternionic_zero
      | cons a s ha ih =>
        rw [Finset.sum_cons]
        refine isQuaternionic_add (isQuaternionic_of_compact ?_) ih
        refine ComplexMatrix2.specialUnitary.mul_mem
          (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem_compact hV _)
            (pathHolonomy_mem_compact hV _)) ?_
        exact inv_mem_compact (pathHolonomy_mem_compact hV _)
    exact hs _
private theorem meanRadius_re_nonneg [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    0 ≤ (meanRadius V c).re := by apply _root_.YangMills.SharedProofs.p43485 <;> assumption
private theorem continuous_traceDefect : Continuous traceDefect := by apply _root_.YangMills.SharedProofs.p10480 <;> assumption
end Limits
section FactsOfTheTower
private theorem towerFacts (hd : NormalizedMeanAtOne)
    (hCfg : LeftChartFields.Claim) (hS : FaceSums.FacesAndPairings)
    (hV : LinearMapValues.Statement) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    TowerFacts L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finS : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  have hvals := (hV L hL k).1 n hn
  refine
    { finite_vertex := finS
      finite_pos := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      finite_edge := fun j hj => ?_
      finite_face := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      deriv_at_one := fun j hj B hB c hc => (hd L hL n k j hn hj B hB c hc).2.2.2.2
      smoothing_mem := fun j hj B hB => ((hvals.1 j hj).1 B hB).2.2.1
      not_both := fun j hj b hb => ?_
      at_one := fun j hj c hc => ?_
      left_mem := fun j hj => ((hCfg.2.2 L k j hL hj).1 n hn).1.1
      log_curves := fun I hI => (hCfg.1 I hI).1 }
  · haveI := finS j hj
    have h : Function.Injective (fun b : Edge L n k j => (b.source, b.target)) := by
      intro b b' hb
      exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    exact Finite.of_injective _ h
  · obtain ⟨μ, hμ⟩ := hb
    rintro ⟨ν, hν⟩
    have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
    have hs : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n)
        1 μ := by
      have h := congrArg Subtype.val hμ
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps] using h
    have hs' : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n)
        1 ν := by
      have h := congrArg Subtype.val hν
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using h
    have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
    rcases hX with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ⟨ν, hs'⟩
    · exact h ⟨μ, hs⟩
  · obtain ⟨h1, h2, h3, -, -⟩ :=
      hd L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc
    exact ⟨h1, h2, h3⟩
end FactsOfTheTower
section GaugeFunctions
variable {L n k : ℕ}
private theorem restrictVertexFunction_zero (hL : 0 < L) (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_zero <;> assumption
private theorem restrictVertexFunction_succ (hL : 0 < L) {j : ℕ}
    (v : Vertex L n k 0 → ComplexMatrix2) (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y := by apply _root_.YangMills.SharedProofs.p11078 <;> assumption
private theorem restrictVertexFunction_mem_compact {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) (j : ℕ) (y : Vertex L n k j) :
    restrictVertexFunction j v y ∈ PeriodicLattice.compactGaugeGroup := hv _
private theorem levelField_gaugeTransformPoint (hCov : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X) j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X j) := by
  have hLpos : 0 < L := by have := hL.2; omega
  intro j
  induction j with
  | zero =>
    intro _
    rw [restrictVertexFunction_zero hLpos]
    rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hWc := mem_fieldsIn_complex (hX.2 j hj.le)
    have hcv : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        levelField (gaugeTransformPoint v X) (j + 1) c =
          restrictVertexFunction (j + 1) v c.source * levelField X (j + 1) c *
            (restrictVertexFunction (j + 1) v c.target)⁻¹ := by
      intro c hc
      obtain ⟨-, -, h3⟩ := hCov L hL n k j hn hj _ hWc (restrictVertexFunction j v)
        (fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (hv _)).2) c hc
      rw [levelField_succ_of_pos _ hj c hc, levelField_succ_of_pos _ hj c hc, ih hj.le, h3,
        restrictVertexFunction_succ hLpos, restrictVertexFunction_succ hLpos]
      have hr : (restrictVertexFunction (j + 1) v c.source)⁻¹ *
          restrictVertexFunction (j + 1) v c.source = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_det_compact (hv _))
      simp only [gaugeTransformPoint]
      set A := restrictVertexFunction (j + 1) v c.source
      set n₀ := X.noise ⟨j, hj⟩ ⟨c, hc⟩
      set u := normalizedMean (levelField X j) c
      set C := (restrictVertexFunction (j + 1) v c.target)⁻¹
      calc A * n₀ * A⁻¹ * (A * u * C) = A * n₀ * (A⁻¹ * A) * u * C := by simp only [mul_assoc]
        _ = A * (n₀ * u) * C := by rw [hr, mul_one]; simp only [mul_assoc]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hcv c hc
    · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
      rw [levelField_succ_opposite _ hj c hc hc', hcv _ hc']
      simp only [PeriodicLattice.gaugeTransform]
      rw [levelField_succ_opposite X hj c hc hc', Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _
          (isUnit_det_compact (restrictVertexFunction_mem_compact hv _ _))]
      simp only [PeriodicLattice.Bond.opposite, mul_assoc]
private theorem gaugeTransform_mem_fieldSpace {j : ℕ} {w : Vertex L n k j → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2}
    (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) (hV : V ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform w V ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8548 <;> assumption
private theorem gaugeTransformPoint_compact (hCov : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    IsCompactValued (gaugeTransformPoint v X) := by
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · exact ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hv _) (hX.1 i c)) (inv_mem_compact (hv _))
  · rw [levelField_gaugeTransformPoint hCov hL hn hX hv j hj]
    exact gaugeTransform_mem_fieldSpace (fun x => hv _) (hX.2 j hj)
private theorem traceDefect_conj {w g : ComplexMatrix2}
    (hw : w ∈ PeriodicLattice.compactGaugeGroup) :
    traceDefect (w * g * w⁻¹) = traceDefect g := by
  simp only [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_compact hw),
    one_mul]
private theorem chainAction_gaugeTransformPoint (hCov : ContourMeanGaugeCovariant)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant) (hk : 1 ≤ k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (a : ℝ) : chainAction a (gaugeTransformPoint v X) = chainAction a X := by
  have h1 : Tower.plaquetteAction L n k (gaugeTransformPoint v X).fine =
      Tower.plaquetteAction L n k X.fine :=
    ((hSG L n k hL.1 hL.2 hn hk).2 X.fine v (hX.2 0 (Nat.zero_le _)) hv).2
  have e : ∀ (i : Fin k) (c : PositiveEdge L n k ((i : ℕ) + 1)),
      (meanRadius (levelField (gaugeTransformPoint v X) i) c.1).re *
        traceDefect ((gaugeTransformPoint v X).noise i c) =
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) := by
    intro i c
    have hi := i.2
    have h2 := (hCov L hL n k i hn hi _ (mem_fieldsIn_complex (hX.2 i hi.le))
      (restrictVertexFunction i v)
      (fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (hv _)).2) c.1 c.2).2.1
    have h3 : traceDefect ((gaugeTransformPoint v X).noise i c) = traceDefect (X.noise i c) :=
      traceDefect_conj (restrictVertexFunction_mem_compact hv _ _)
    rw [levelField_gaugeTransformPoint hCov hL hn hX hv i hi.le, h2, h3]
  simp only [chainAction, e, h1]
end GaugeFunctions
section NearTheUnitPoint
variable {L n k j : ℕ}
private theorem tendsto_meanRadius [Finite (Vertex L n k j)] {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (c : Edge L n k (j + 1))
    (hr : meanRadius V c ≠ 0) :
    Tendsto (fun m => meanRadius (W m) c) l (𝓝 (meanRadius V c)) := by
  have hM := tendsto_contourMean hV h c
  have hdet : Tendsto (fun m => Matrix.det (contourMean (W m) c)) l
      (𝓝 (Matrix.det (contourMean V c))) :=
    ((Continuous.matrix_det continuous_id).tendsto _).comp hM
  have hq := det_isQuaternionic (contourMean_isQuaternionic hV c)
  have hd0 : Matrix.det (contourMean V c) ≠ 0 := by
    intro h0
    apply hr
    simp only [meanRadius]
    rw [h0, Complex.zero_cpow (by norm_num)]
  have hslit : Matrix.det (contourMean V c) ∈ Complex.slitPlane := by
    rw [hq] at hd0 ⊢
    left
    have hne : Complex.normSq (contourMean V c 0 0) + Complex.normSq (contourMean V c 0 1) ≠ 0 := by
      intro h0
      exact hd0 (by rw [h0]; simp)
    have hnn := add_nonneg (Complex.normSq_nonneg (contourMean V c 0 0))
      (Complex.normSq_nonneg (contourMean V c 0 1))
    simpa using lt_of_le_of_ne hnn (Ne.symm hne)
  exact (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hslit).tendsto.comp hdet
private theorem tendsto_normalizedMean [Finite (Vertex L n k j)] {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (c : Edge L n k (j + 1))
    (hr : meanRadius V c ≠ 0) :
    Tendsto (fun m => normalizedMean (W m) c) l (𝓝 (normalizedMean V c)) := by
  simp only [normalizedMean]
  exact ((tendsto_meanRadius hV h c hr).inv₀ hr).smul (tendsto_contourMean hV h c)
private theorem contDiffAt_chainAction (hT : TowerFacts L n k) {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {p₀ : P} {m : WithTop ℕ∞} {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) (a : ℝ) :
    ContDiffAt ℝ m (fun p => chainAction a (X p)) p₀ := by
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finite_pos _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.finite_face
  have rtC : ∀ {f : P → ComplexMatrix2}, ContDiffAt ℝ m f p₀ →
      ContDiffAt ℝ m (fun p => (ComplexMatrix2.halfTrace (f p)).re) p₀ := by
    intro f hf
    let T : ComplexMatrix2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun A => (ComplexMatrix2.halfTrace A).re
        map_add' := fun A B => by
          simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
        map_smul' := fun r A => by
          have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
          simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
            ComplexMatrix2.fullTrace]
          rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
    exact T.contDiff.contDiffAt.comp p₀ hf
  have e : (fun p => chainAction a (X p)) = fun p =>
      (∑ q : Face L n k 0, (1 - (ComplexMatrix2.halfTrace
        (PeriodicLattice.pathHolonomy (X p).fine q.boundaryBonds)).re)) +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField (X p) i) c.1).re *
          (1 - (ComplexMatrix2.halfTrace ((X p).noise i c)).re) := by
    funext p
    simp only [chainAction, Tower.plaquetteAction, PeriodicLattice.wilsonAction,
      finsum_eq_sum_of_fintype, PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
      traceDefect]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    simp [ComplexMatrix2.halfTrace, Complex.mul_re]
  rw [e]
  refine ContDiffAt.add (ContDiffAt.sum fun q _ => ?_) (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun c _ => ?_))
  · exact contDiffAt_const.sub (rtC (contDiffAt_pathHolonomy hb _))
  · exact (Complex.reCLM.contDiff.contDiffAt.comp p₀
      (contDiffAt_meanRadius_levelField hT hb hn h0 i.2 c.1 c.2)).mul
      (contDiffAt_const.sub (rtC (hn i c)))
private theorem chainAction_unitPoint (a : ℝ) : chainAction a (unitPoint L n k) = 0 := by apply _root_.YangMills.SharedProofs.p8209 <;> assumption
private abbrev ChainCoordinates (L n k : ℕ) : Type :=
  (Edge L n k 0 → ComplexMatrix2) ×
    ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2)
private theorem exists_nbhd_unitPoint (hT : TowerFacts L n k) {ρ δ : ℝ} (hρ0 : 0 < ρ)
    (hδ : 0 < δ) (a : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ X : ChainPoint L n k,
      (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) < ε₀) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε₀) →
      (∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) ∧
        chainAction a X < δ := by
  letI hFb : Fintype (Edge L n k 0) := @Fintype.ofFinite _ (hT.finite_edge 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finite_pos _ i.2)
  let toPoint : ChainCoordinates L n k → ChainPoint L n k := fun p => ⟨p.1, p.2⟩
  let p₀ : ChainCoordinates L n k := (fun _ => 1, fun _ _ => 1)
  have hb : ∀ b, ContDiffAt ℝ 0 (fun p : ChainCoordinates L n k => (toPoint p).fine b) p₀ :=
    fun b => (contDiff_zero.mpr (by simp only [toPoint]; fun_prop)).contDiffAt
  have hn : ∀ i c, ContDiffAt ℝ 0 (fun p : ChainCoordinates L n k => (toPoint p).noise i c) p₀ :=
    fun i c => (contDiff_zero.mpr (by simp only [toPoint]; fun_prop)).contDiffAt
  have h0 : toPoint p₀ = unitPoint L n k := rfl
  have hF := contDiffAt_levelField hT hb hn h0
  have hA := (contDiffAt_chainAction hT hb hn h0 a).continuousAt
  have hA0 : chainAction a (toPoint p₀) = 0 := by
    rw [h0]
    exact chainAction_unitPoint a
  have e1 : ∀ᶠ p in 𝓝 p₀, ∀ j ∈ Finset.range (k + 1), ∀ b : Edge L n k j,
      ComplexMatrix2.operatorNorm (levelField (toPoint p) j b - 1) < ρ := by
    refine (Filter.eventually_all_finset _).mpr fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    haveI := hT.finite_edge j hj'
    refine Filter.eventually_all.mpr fun b => ?_
    obtain ⟨h1, h2⟩ := hF j hj'
    have h3 : Tendsto (fun p => ‖levelField (toPoint p) j b - 1‖) (𝓝 p₀) (𝓝 0) := by
      have h4 := (((h1 b).continuousAt).tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [h2] using h4
    exact h3.eventually_lt_const hρ0
  have e2 : ∀ᶠ p in 𝓝 p₀, chainAction a (toPoint p) < δ := by
    have h3 := hA.tendsto
    rw [hA0] at h3
    exact h3.eventually_lt_const hδ
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
  refine ⟨ε₀, hε₀, fun X h1 h2 => ?_⟩
  have hd : dist ((X.fine, X.noise) : ChainCoordinates L n k) p₀ < ε₀ := by
    rw [dist_eq_norm, Prod.norm_def, max_lt_iff]
    exact ⟨(pi_norm_lt_iff hε₀).mpr fun b => h1 b,
      (pi_norm_lt_iff hε₀).mpr fun i => (pi_norm_lt_iff hε₀).mpr fun c => h2 i c⟩
  obtain ⟨r1, r2⟩ := hball hd
  exact ⟨fun j hj b => r1 j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) b, r2⟩
end NearTheUnitPoint
section TopOnlyPoint
variable {L n k : ℕ}
private theorem const_one_mem_fieldSpace {j : ℕ} :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩
private def castEdge {j j' : ℕ} (h : j = j') (b : Edge L n k j) : Edge L n k j' := by
  subst h
  exact b
private def topOnlyPoint (W : Edge L n k k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fun _ => 1, fun i c => open Classical in
    if h : (i : ℕ) + 1 = k then W (castEdge h c.1) else 1⟩
private theorem levelField_topOnlyPoint_lt (hT : TowerFacts L n k)
    (W : Edge L n k k → ComplexMatrix2) :
    ∀ j, j < k → levelField (topOnlyPoint W) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := by omega
    have hne : j + 1 ≠ k := by omega
    have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
        levelField (topOnlyPoint W) (j + 1) c = 1 := by
      intro c hc
      rw [levelField_succ_of_pos _ hj c hc, ih hj, (hT.at_one j hj c hc).2.2]
      simp [topOnlyPoint, hne]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
      rw [levelField_succ_opposite _ hj c hc hc', hpos _ hc']
      simp
private theorem levelField_topOnlyPoint_top (hT : TowerFacts L n k) (hk : 1 ≤ k)
    {W : Edge L n k k → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k k) : levelField (topOnlyPoint W) k = W := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hpos : ∀ c : Edge L n (m + 1) (m + 1), ∀ hc : c.IsPositivelyOriented,
      levelField (topOnlyPoint W) (m + 1) c = W c := by
    intro c hc
    rw [levelField_succ_of_pos _ hm c hc, levelField_topOnlyPoint_lt hT W m hm,
      (hT.at_one m hm c hc).2.2, mul_one]
    simp [topOnlyPoint, castEdge]
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
    rw [levelField_succ_opposite _ hm c hc hc', hpos _ hc', hW.2 c (Set.mem_univ _)]
    exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hW.1 c (Set.mem_univ _)))
private theorem topOnlyPoint_compact (hT : TowerFacts L n k) (hk : 1 ≤ k)
    {W : Edge L n k k → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k k) : IsCompactValued (topOnlyPoint W) := by
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · simp only [topOnlyPoint]
    split_ifs with h
    · exact hW.1 _ (Set.mem_univ _)
    · exact ComplexMatrix2.specialUnitary.one_mem
  · rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [levelField_topOnlyPoint_lt hT W j h]
      exact ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩
    · subst h
      rw [levelField_topOnlyPoint_top hT hk hW]
      exact hW
private theorem chainAction_nonneg (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hT : TowerFacts L n k) (hk : 1 ≤ k) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {a : ℝ}
    (ha : 0 < a) {X : ChainPoint L n k} (hX : IsCompactValued X) : 0 ≤ chainAction a X := by
  have h1 : 0 ≤ Tower.plaquetteAction L n k X.fine :=
    ((hSG L n k hL.1 hL.2 hn hk).2 X.fine (fun _ => 1) (hX.2 0 (Nat.zero_le _))
      (fun _ => ComplexMatrix2.specialUnitary.one_mem)).1
  refine add_nonneg h1 (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => ?_))
  haveI := hT.finite_vertex i i.2.le
  refine finsum_nonneg fun c => ?_
  exact mul_nonneg (meanRadius_re_nonneg (hX.2 i i.2.le) _)
    (traceDefect_nonneg_and_eq_zero (hX.1 i c)).1
end TopOnlyPoint
section MinimizerNearOne
variable {L n k : ℕ}
private theorem exists_minimizer_near_unit (hT : TowerFacts L n k)
    (hCov : ContourMeanGaugeCovariant)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hk : 1 ≤ k) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ρ : ℝ}
    (hρ : MeanRegularNear L n k ρ) {a : ℝ} (ha : 0 < a) {ε₁ δ₁ : ℝ}
    (hnear : ∀ X : ChainPoint L n k, (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) ≤ ε₁) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) ≤ ε₁) →
      ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (hδ : ∀ X : ChainPoint L n k, IsCompactValued X →
      (∀ b, ComplexMatrix2.operatorNorm (levelField X k b - 1) < δ₁) → chainAction a X < δ₁ →
      ∃ v : Vertex L n k 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) ∧
        (∀ b, ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).fine b - 1) < ε₁) ∧
        ∀ i c, ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).noise i c - 1) < ε₁)
    {W : Edge L n k k → ComplexMatrix2} (hW : W ∈ fieldSpace L n k k)
    (hWn : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < δ₁)
    (hF : chainAction a (topOnlyPoint W) < δ₁) :
    ∃ Y : ChainPoint L n k, IsMinimizerOver a W Y ∧
      (∀ b, ComplexMatrix2.operatorNorm (Y.fine b - 1) ≤ ε₁) ∧
      ∀ i c, ComplexMatrix2.operatorNorm (Y.noise i c - 1) ≤ ε₁ := by
  let S : Set ℝ := {r | ∃ X : ChainPoint L n k, IsCompactValued X ∧ levelField X k = W ∧
    r = chainAction a X}
  have hcr := topOnlyPoint_compact hT hk hW
  have hct := levelField_topOnlyPoint_top hT hk hW
  have hSne : S.Nonempty := ⟨_, topOnlyPoint W, hcr, hct, rfl⟩
  have hSb : BddBelow S := ⟨0, by
    rintro r ⟨X, hX, -, rfl⟩
    exact chainAction_nonneg hSG hT hk hL hn ha hX⟩
  set mn := sInf S with hmn
  have hmlt : mn < δ₁ := lt_of_le_of_lt (csInf_le hSb ⟨topOnlyPoint W, hcr, hct, rfl⟩) hF
  have hseq : ∀ i : ℕ, ∃ X : ChainPoint L n k, IsCompactValued X ∧ levelField X k = W ∧
      chainAction a X < min (mn + 1 / ((i : ℝ) + 1)) δ₁ := by
    intro i
    have hlt : mn < min (mn + 1 / ((i : ℝ) + 1)) δ₁ := lt_min (by
      have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
      linarith) hmlt
    obtain ⟨r, ⟨X, h1, h2, rfl⟩, h3⟩ := exists_lt_of_csInf_lt hSne hlt
    exact ⟨X, h1, h2, h3⟩
  choose X₀ hX₀ hX₀t hX₀F using hseq
  choose v hvr hv1 hvb hvn using fun i => hδ (X₀ i) (hX₀ i)
    (by rw [hX₀t i]; exact hWn) (lt_of_lt_of_le (hX₀F i) (min_le_right _ _))
  let X : ℕ → ChainPoint L n k := fun i => gaugeTransformPoint (v i) (X₀ i)
  have hX : ∀ i, IsCompactValued (X i) := fun i =>
    gaugeTransformPoint_compact hCov hL hn (hX₀ i) (hvr i)
  have hXF : ∀ i, chainAction a (X i) = chainAction a (X₀ i) := fun i =>
    chainAction_gaugeTransformPoint hCov hSG hk hL hn (hX₀ i) (hvr i) a
  have hXt : ∀ i, levelField (X i) k = W := by
    intro i
    rw [levelField_gaugeTransformPoint hCov hL hn (hX₀ i) (hvr i) k le_rfl, hX₀t i]
    funext b
    simp only [PeriodicLattice.gaugeTransform, hv1 i]
    simp
  have hU : ∀ m, (X m).fine ∈ fieldSpace L n k 0 := fun m => (hX m).2 0 (Nat.zero_le _)
  let x : ℕ → (Edge L n k 0 → ↥ComplexMatrix2.specialUnitary) ×
      ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ↥ComplexMatrix2.specialUnitary) :=
    fun m => (fun b => ⟨(X m).fine b, (hU m).1 b (Set.mem_univ b)⟩,
      fun i c => ⟨(X m).noise i c, (hX m).1 i c⟩)
  obtain ⟨A, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  let Y : ChainPoint L n k :=
    ⟨fun b => (A.1 b : ComplexMatrix2), fun i c => (A.2 i c : ComplexMatrix2)⟩
  have hYn : ∀ i c, Y.noise i c ∈ PeriodicLattice.compactGaugeGroup := fun i c => (A.2 i c).2
  have hb : ∀ b, Tendsto (fun m => (X (φ m)).fine b) atTop (𝓝 (Y.fine b)) := by
    intro b
    have h1 := (continuous_fst.tendsto A).comp hlim
    have h2 := tendsto_pi_nhds.mp h1 b
    exact (continuous_subtype_val.tendsto _).comp h2
  have hnz : ∀ i c, Tendsto (fun m => (X (φ m)).noise i c) atTop (𝓝 (Y.noise i c)) := by
    intro i c
    have h1 := (continuous_snd.tendsto A).comp hlim
    have h2 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h1 i) c
    exact (continuous_subtype_val.tendsto _).comp h2
  have hYc : Y.fine ∈ fieldSpace L n k 0 := by
    refine ⟨fun b _ => (A.1 b).2, fun b _ => ?_⟩
    have h1 := hb b.opposite
    have h2 := tendsto_matrix_inv (hb b) (det_compact (A.1 b).2)
    have e : (fun m => (X (φ m)).fine b.opposite) = fun m => ((X (φ m)).fine b)⁻¹ := by
      funext m
      exact (hU (φ m)).2 b (Set.mem_univ b)
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  have hYb : ∀ b, ComplexMatrix2.operatorNorm (Y.fine b - 1) ≤ ε₁ := by
    intro b
    refine le_of_tendsto' ((hb b).sub_const (1 : ComplexMatrix2)).norm fun m => ?_
    exact (hvb (φ m) b).le
  have hYnz : ∀ i c, ComplexMatrix2.operatorNorm (Y.noise i c - 1) ≤ ε₁ := by
    intro i c
    refine le_of_tendsto' ((hnz i c).sub_const (1 : ComplexMatrix2)).norm fun m => ?_
    exact (hvn (φ m) i c).le
  have hYnear := hnear Y hYb hYnz
  have hlev : ∀ j, j ≤ k → levelField Y j ∈ fieldSpace L n k j ∧
      ∀ b, Tendsto (fun m => levelField (X (φ m)) j b) atTop (𝓝 (levelField Y j b)) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hYc, hb⟩
    | succ j ih =>
      intro h
      have hj : j < k := h
      obtain ⟨h1, h2⟩ := ih hj.le
      haveI := hT.finite_vertex j hj.le
      have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
          levelField Y (j + 1) c ∈ PeriodicLattice.compactGaugeGroup ∧
          Tendsto (fun m => levelField (X (φ m)) (j + 1) c) atTop
            (𝓝 (levelField Y (j + 1) c)) := by
        intro c hc
        obtain ⟨r0, -, -, hu, -⟩ := hρ j hj _ (mem_fieldsIn_complex h1) (hYnear j hj.le) c hc
        have h3 := tendsto_normalizedMean h1 h2 c r0
        constructor
        · rw [levelField_succ_of_pos _ hj c hc]
          exact ComplexMatrix2.specialUnitary.mul_mem (hYn _ _)
            (normalizedMean_mem_compact h1 c hu)
        · have e : (fun m => levelField (X (φ m)) (j + 1) c) = fun m =>
              (X (φ m)).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X (φ m)) j) c := by
            funext m
            exact levelField_succ_of_pos _ hj c hc
          rw [e, levelField_succ_of_pos _ hj c hc]
          exact (hnz _ _).mul h3
      have hreal : ∀ c : Edge L n k (j + 1),
          levelField Y (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
        intro c
        by_cases hc : c.IsPositivelyOriented
        · exact (hpos c hc).1
        · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
          rw [levelField_succ_opposite _ hj c hc hc']
          exact inv_mem_compact (hpos _ hc').1
      refine ⟨⟨fun b _ => hreal b, fun b _ => ?_⟩, fun b => ?_⟩
      · by_cases hb' : b.IsPositivelyOriented
        · have hb'' := hT.not_both (j + 1) hj b hb'
          have hbr := (isPositivelyOriented_or_opposite b.opposite).resolve_left hb''
          rw [levelField_succ_opposite _ hj _ hb'' hbr, opposite_opposite_edge]
        · have hbr := (isPositivelyOriented_or_opposite b).resolve_left hb'
          rw [levelField_succ_opposite _ hj b hb' hbr,
            Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hreal _))]
      · by_cases hb' : b.IsPositivelyOriented
        · exact (hpos b hb').2
        · have hbr := (isPositivelyOriented_or_opposite b).resolve_left hb'
          have e : (fun m => levelField (X (φ m)) (j + 1) b) = fun m =>
              (levelField (X (φ m)) (j + 1) b.opposite)⁻¹ := by
            funext m
            exact levelField_succ_opposite _ hj b hb' hbr
          rw [e, levelField_succ_opposite _ hj b hb' hbr]
          exact tendsto_matrix_inv (hpos _ hbr).2 (det_compact (hpos _ hbr).1)
  have hYreal : IsCompactValued Y := ⟨hYn, fun j hj => (hlev j hj).1⟩
  have hYtop : levelField Y k = W := by
    funext b
    have h1 := (hlev k le_rfl).2 b
    simp only [hXt] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hFlim : Tendsto (fun m => chainAction a (X (φ m))) atTop (𝓝 (chainAction a Y)) := by
    letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
      @Fintype.ofFinite _ (hT.finite_pos _ i.2)
    letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.finite_face
    have e : ∀ Z : ChainPoint L n k, chainAction a Z =
        (∑ q : Face L n k 0,
          traceDefect (PeriodicLattice.pathHolonomy Z.fine q.boundaryBonds)) +
        a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
          (meanRadius (levelField Z i) c.1).re * traceDefect (Z.noise i c) := by
      intro Z
      simp only [chainAction, Tower.plaquetteAction, PeriodicLattice.wilsonAction,
        finsum_eq_sum_of_fintype, PeriodicLattice.plaquetteCost,
        PeriodicLattice.plaquetteHolonomy, traceDefect]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      simp [ComplexMatrix2.halfTrace, Complex.mul_re]
    simp only [e]
    refine Tendsto.add (tendsto_finset_sum _ fun q _ => ?_) (Tendsto.const_mul a
      (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun c _ => ?_))
    · exact (continuous_traceDefect.tendsto _).comp (tendsto_pathHolonomy hb _)
    · haveI := hT.finite_vertex i i.2.le
      obtain ⟨h1, h2⟩ := hlev i i.2.le
      obtain ⟨r0, -⟩ := hρ i i.2 _ (mem_fieldsIn_complex h1) (hYnear i i.2.le) c.1 c.2
      exact ((Complex.continuous_re.tendsto _).comp (tendsto_meanRadius h1 h2 c.1 r0)).mul
        ((continuous_traceDefect.tendsto _).comp (hnz i c))
  have hYm : chainAction a Y ≤ mn := by
    have hup : Tendsto (fun m => mn + 1 / (((φ m : ℕ) : ℝ) + 1)) atTop (𝓝 (mn + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    rw [add_zero] at hup
    refine le_of_tendsto_of_tendsto' hFlim hup fun m => ?_
    rw [hXF]
    exact ((hX₀F (φ m)).trans_le (min_le_left _ _)).le
  refine ⟨Y, ⟨hYreal, hYtop, fun X' h1 h2 => ?_⟩, hYb, hYnz⟩
  exact hYm.trans (csInf_le hSb ⟨X', h1, h2, rfl⟩)
end MinimizerNearOne
section NearestGauge
variable {L n k : ℕ}
private theorem operatorNorm_sub_one_sq {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    ComplexMatrix2.operatorNorm (g - 1) ^ 2 = 2 * traceDefect g := by apply _root_.YangMills.DeltaSharedProofs.p501476 <;> assumption
private theorem traceDefect_inv {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    traceDefect g⁻¹ = traceDefect g := by apply _root_.YangMills.SharedProofs.p3992 <;> assumption
private theorem matExp_I_smul_mem_compact (hEL : ComplexMatrix2.ExpLogEstimates)
    {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.matExp_I_smul_mem_compact <;> assumption
private def halfTraceReCLM : ComplexMatrix2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (ComplexMatrix2.halfTrace A).re
      map_add' := fun A B => by
        simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
      map_smul' := fun r A => by
        have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
        simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
          ComplexMatrix2.fullTrace]
        rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
private theorem exists_nearest_gauge (hT : TowerFacts L n k)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    ∃ w : Vertex L n k 0 → ComplexMatrix2, (∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ y : Vertex L n k k, restrictVertexFunction k w y = 1) ∧
      (∑ᶠ b : PositiveEdge L n k 0,
          traceDefect (w b.1.source * U b.1 * (w b.1.target)⁻¹) ≤
        ∑ᶠ b : PositiveEdge L n k 0, traceDefect (U b.1)) ∧
      ∀ κ ∈ topVanishingGauges L n k,
        distanceGaugeVariation (PeriodicLattice.gaugeTransform w U)
        (κ : Vertex L n k 0 → ComplexMatrix2) = 0 := by
  letI hFb : Fintype (PositiveEdge L n k 0) :=
    @Fintype.ofFinite _ (hT.finite_pos 0 (Nat.zero_le _))
  let D : (Vertex L n k 0 → ↥ComplexMatrix2.specialUnitary) → ℝ := fun v =>
    ∑ b : PositiveEdge L n k 0,
      traceDefect ((v b.1.source : ComplexMatrix2) * U b.1 * ((v b.1.target : ComplexMatrix2))⁻¹)
  let K : Set (Vertex L n k 0 → ↥ComplexMatrix2.specialUnitary) :=
    {v | ∀ y : Vertex L n k k,
      (v (y.toSublattice (PeriodicLattice.levelDepth k 0)) : ComplexMatrix2) = 1}
  have hinvC : Continuous (fun g : ↥ComplexMatrix2.specialUnitary => (g : ComplexMatrix2)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro g
    exact tendsto_matrix_inv (continuous_subtype_val.tendsto g) (det_compact g.2)
  have hDc : Continuous D := by
    refine continuous_finset_sum _ fun b _ => continuous_traceDefect.comp ?_
    exact ((continuous_subtype_val.comp (continuous_apply _)).mul continuous_const).mul
      (hinvC.comp (continuous_apply _))
  have hKc : IsClosed K := by
    have : K = ⋂ y : Vertex L n k k,
        {v | (v (y.toSublattice (PeriodicLattice.levelDepth k 0)) : ComplexMatrix2) = 1} := by
      ext v
      simp [K]
    rw [this]
    exact isClosed_iInter fun y =>
      isClosed_eq (continuous_subtype_val.comp (continuous_apply _)) continuous_const
  have hK1 : (fun _ => 1 : Vertex L n k 0 → ↥ComplexMatrix2.specialUnitary) ∈ K := fun y => rfl
  obtain ⟨v, hvK, hvmin⟩ := hKc.isCompact.exists_isMinOn ⟨_, hK1⟩ hDc.continuousOn
  refine ⟨fun x => (v x : ComplexMatrix2), fun x => (v x).2, fun y => hvK y, ?_, fun κ hκ => ?_⟩
  · have h1 := hvmin hK1
    simp only [Set.mem_setOf_eq, D] at h1
    simp only [finsum_eq_sum_of_fintype]
    simpa using h1
  set V : Edge L n k 0 → ComplexMatrix2 :=
    PeriodicLattice.gaugeTransform (fun x => (v x : ComplexMatrix2)) U with hV
  have hκs : ∀ x, (κ : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
    fun x => κ.2 x trivial
  let et : ℝ → Vertex L n k 0 → ↥ComplexMatrix2.specialUnitary := fun t x =>
    ⟨ComplexMatrix2.matExp (Complex.I • (t • (κ : Vertex L n k 0 → ComplexMatrix2) x)),
      matExp_I_smul_mem_compact hEL (ComplexMatrix2.hermitianTraceless.smul_mem t (hκs x))⟩
  let vt : ℝ → Vertex L n k 0 → ↥ComplexMatrix2.specialUnitary := fun t x => et t x * v x
  have hvt : ∀ t, vt t ∈ K := by
    intro t y
    have h0 : (κ : Vertex L n k 0 → ComplexMatrix2)
        (y.toSublattice (PeriodicLattice.levelDepth k 0)) = 0 := hκ y
    show (ComplexMatrix2.matExp (Complex.I • (t • (κ : Vertex L n k 0 → ComplexMatrix2)
      (y.toSublattice (PeriodicLattice.levelDepth k 0))))) * (v _ : ComplexMatrix2) = 1
    rw [h0, smul_zero, matExp_I_smul_zero, one_mul]
    exact hvK y
  have hDt : ∀ t, D (vt t) = ∑ b : PositiveEdge L n k 0,
      traceDefect (ComplexMatrix2.matExp
          (Complex.I • (t • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.source)) * V b.1 *
        ComplexMatrix2.matExp
          (Complex.I • (t • (-(κ : Vertex L n k 0 → ComplexMatrix2) b.1.target)))) := by
    intro t
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    show ComplexMatrix2.matExp
        (Complex.I • (t • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.source)) *
        (v b.1.source : ComplexMatrix2) * U b.1 *
      (ComplexMatrix2.matExp
        (Complex.I • (t • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.target)) *
        (v b.1.target : ComplexMatrix2))⁻¹ = _
    rw [Matrix.mul_inv_rev, matExp_inv]
    simp only [hV, PeriodicLattice.gaugeTransform, smul_neg, mul_assoc]
  have hder : HasDerivAt (fun t => D (vt t))
      (-∑ b : PositiveEdge L n k 0, halfTraceReCLM
        (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.source * V b.1 -
        V b.1 * Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.target)) 0 := by
    simp only [hDt]
    rw [← Finset.sum_neg_distrib]
    refine HasDerivAt.fun_sum fun b _ => ?_
    have h1 := ((hasDerivAt_matExp_I_smul_line
      ((κ : Vertex L n k 0 → ComplexMatrix2) b.1.source)).mul_const (V b.1)).mul
      (hasDerivAt_matExp_I_smul_line (-(κ : Vertex L n k 0 → ComplexMatrix2) b.1.target))
    have h2 := (halfTraceReCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).const_sub 1
    refine h2.congr_deriv ?_
    rw [matExp_I_smul_zero_smul, matExp_I_smul_zero_smul]
    simp only [one_mul, mul_one, smul_neg, mul_neg, sub_eq_add_neg]
  have hmin : IsLocalMin (fun t => D (vt t)) 0 := by
    have e0 : vt 0 = v := by
      funext x
      apply Subtype.ext
      show ComplexMatrix2.matExp
        (Complex.I • ((0 : ℝ) • (κ : Vertex L n k 0 → ComplexMatrix2) x)) *
        (v x : ComplexMatrix2) = _
      rw [matExp_I_smul_zero_smul, one_mul]
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [e0]
    exact hvmin (hvt t)
  have hz := hmin.hasDerivAt_eq_zero hder
  have : ∑ b : PositiveEdge L n k 0, halfTraceReCLM
      (Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.source * V b.1 -
      V b.1 * Complex.I • (κ : Vertex L n k 0 → ComplexMatrix2) b.1.target) = 0 := by linarith
  simp only [distanceGaugeVariation, finsum_eq_sum_of_fintype]
  exact this
private theorem exists_hermitianTraceless_log (hEL : ComplexMatrix2.ExpLogEstimates)
    {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (h1 : ComplexMatrix2.operatorNorm (g - 1) < 1) :
    ∃ H ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.matExp (Complex.I • H) = g ∧
      ComplexMatrix2.operatorNorm H ≤ 2 * ComplexMatrix2.operatorNorm (g - 1) := by apply _root_.YangMills.SharedProofs.p26564 <;> assumption
private theorem exists_levelForms_chart (hT : TowerFacts L n k)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {τ : ℝ} (hτ : τ ≤ 1 / 2)
    (hb : ∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) ≤ τ)
    (hn : ∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) ≤ τ) :
    ∃ ξ : LevelForms L n k, expMove ξ (unitPoint L n k) = X ∧
      (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) ≤ 2 * τ) ∧
      ∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm
          ((ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b) ≤ 2 * τ := by
  have hU : X.fine ∈ fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have hlie : ∀ g : ComplexMatrix2, ∃ H : ComplexMatrix2,
      g ∈ PeriodicLattice.compactGaugeGroup → ComplexMatrix2.operatorNorm (g - 1) ≤ τ →
      H ∈ ComplexMatrix2.hermitianTraceless ∧ ComplexMatrix2.matExp (Complex.I • H) = g ∧
        ComplexMatrix2.operatorNorm H ≤ 2 * τ := by
    intro g
    by_cases h : g ∈ PeriodicLattice.compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (g - 1) ≤ τ
    · obtain ⟨H, h1, h2, h3⟩ := exists_hermitianTraceless_log hEL h.1 (by linarith [h.2])
      exact ⟨H, fun _ _ => ⟨h1, h2, h3.trans (by linarith [h.2])⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Hf hHf using hlie
  have hτ0 : 0 ≤ τ := by
    have := hb (PeriodicLattice.Bond.forwardFrom 0 0)
    exact (norm_nonneg _).trans this
  have hsu : ∀ {j : ℕ} (hj : j ≤ k) (f : Edge L n k j → ComplexMatrix2),
      (∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) →
      extendOddly f ∈ edgeFormSpace L n k j := by
    intro j hj f hf
    refine ⟨fun b hb' => ?_, fun b => extendOddly_opposite hT hj f b⟩
    simp only [extendOddly, if_pos hb']
    exact hf b hb'
  let A : edgeFormSpace L n k 0 := ⟨extendOddly fun b => Hf (X.fine b),
    hsu (Nat.zero_le _) _ fun b _ => (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).1⟩
  let fN : (i : Fin k) → Edge L n k ((i : ℕ) + 1) → ComplexMatrix2 := fun i c =>
    open Classical in if hc : c.IsPositivelyOriented then Hf (X.noise i ⟨c, hc⟩) else 0
  let N : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1) := fun i =>
    ⟨extendOddly (fN i), hsu i.2 _ fun c hc => by
      simp only [fN, dif_pos hc]
      exact (hHf _ (hX.1 i _) (hn i _)).1⟩
  refine ⟨(A, N), ?_, fun b => ?_, fun i b => ?_⟩
  · have e1 : (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).fine = X.fine := by
      funext b
      by_cases hbp : b.IsPositivelyOriented
      · simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_pos hbp, mul_one, A,
          extendOddly]
        exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.1
      · have hbr := (isPositivelyOriented_or_opposite b).resolve_left hbp
        simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_neg hbp, if_pos hbr,
          mul_one, A, extendOddly]
        rw [(hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.1]
        exact inv_opposite_of_mem_fieldsIn (mem_fieldsIn_complex hU) b
    have e2 : (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).noise = X.noise := by
      funext i c
      simp only [expMove, unitPoint, mul_one, N, extendOddly, if_pos c.2, fN, dif_pos c.2]
      exact (hHf _ (hX.1 i _) (hn i _)).2.1
    calc expMove ((A, N) : LevelForms L n k) (unitPoint L n k) =
        ⟨(expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).fine,
          (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).noise⟩ := rfl
      _ = ⟨X.fine, X.noise⟩ := by rw [e1, e2]
      _ = X := rfl
  · show ComplexMatrix2.operatorNorm ((extendOddly fun b => Hf (X.fine b)) b) ≤ _
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.2
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact (hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.2
  · show ComplexMatrix2.operatorNorm (extendOddly (fN i) b) ≤ _
    have hbd : ∀ c : Edge L n k ((i : ℕ) + 1), ComplexMatrix2.operatorNorm (fN i c) ≤ 2 * τ := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · simp only [fN, dif_pos hc]
        exact (hHf _ (hX.1 i _) (hn i _)).2.2
      · simp only [fN, dif_neg hc]
        simp only [ComplexMatrix2.operatorNorm, norm_zero]
        linarith
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact hbd b
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact hbd _
end NearestGauge
private theorem le_card_mul_of_sum_le {ι : Type*} [Fintype ι] {f g : ι → ℝ} {c : ℝ}
    (hf : ∀ i, 0 ≤ f i)
    (hs : ∑ i, f i ≤ ∑ i, g i) (hg : ∀ i, g i ≤ c) (i : ι) :
    f i ≤ (Fintype.card ι : ℝ) * c := by
  have h1 : f i ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => hf i) (Finset.mem_univ i)
  have h2 : ∑ i, g i ≤ (Fintype.card ι : ℝ) * c := by
    have := Finset.sum_le_card_nsmul Finset.univ g c (fun i _ => hg i)
    simpa using this
  linarith
set_option maxHeartbeats 1000000 in
theorem nearestGaugeMinimizerExists (hPA : NormalizedMeanNearOne)
    (hDer : NormalizedMeanAtOne)
    (hCov : ContourMeanGaugeCovariant)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hO : SmallActionNearGaugeOrbit)
    (hCfg : LeftChartFields.Claim) (hS : FaceSums.FacesAndPairings)
    (hV : LinearMapValues.Statement) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hEL : ComplexMatrix2.ExpLogEstimates) : NearestGaugeMinimizerExists := by
  intro a ha L hL k n hk hn B ε hε
  have hT : TowerFacts L n k := towerFacts hDer hCfg hS hV hA hL hn
  obtain ⟨ρ, hρ0, hρ'⟩ := hPA L hL
  have hρ : MeanRegularNear L n k ρ := fun j hj V hV hN c hc => hρ' n k j hn hj V hV hN c hc
  letI hFb : Fintype (PositiveEdge L n k 0) :=
    @Fintype.ofFinite _ (hT.finite_pos 0 (Nat.zero_le _))
  set Nn : ℝ := (Fintype.card (PositiveEdge L n k 0) : ℝ) + 1 with hNn
  have hNn1 : 1 ≤ Nn := by
    have : (0 : ℝ) ≤ (Fintype.card (PositiveEdge L n k 0) : ℝ) := Nat.cast_nonneg _
    linarith
  set τ : ℝ := min (1 / 2) (ε / 4) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by linarith)
  obtain ⟨ε₀, hε₀, hfl⟩ := exists_nbhd_unitPoint hT hρ0 one_pos a
  set ε₁ : ℝ := min (ε₀ / 2) (τ / Nn) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by linarith) (by positivity)
  have hnear : ∀ X : ChainPoint L n k, (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) ≤ ε₁) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) ≤ ε₁) →
      ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ := by
    intro X h1 h2
    have hlt : ε₁ < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact (hfl X (fun b => (h1 b).trans_lt hlt) (fun i c => (h2 i c).trans_lt hlt)).1
  obtain ⟨δ₁, hδ₁, hδ⟩ := hO a ha L hL k n hk hn ε₁ hε₁0
  obtain ⟨ε₃, hε₃, hfl3⟩ := exists_nbhd_unitPoint hT one_pos hδ₁ a
  have h1c := const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := k)
  obtain ⟨δ, hδ0, hcur⟩ := expTwist_line_near hT le_rfl h1c B (ρ := min δ₁ ε₃)
    (fun b => by simpa [ComplexMatrix2.operatorNorm] using lt_min hδ₁ hε₃)
  refine ⟨δ, hδ0, fun s hs => ?_⟩
  set W : Edge L n k k → ComplexMatrix2 :=
    PeriodicLattice.expTwist (s • (B : Edge L n k k → ComplexMatrix2)) fun _ => 1 with hWd
  have hW : W ∈ fieldSpace L n k k := expTwist_mem_fieldSpace hT le_rfl h1c B s
  have hWn := hcur s hs
  have hFc : chainAction a (topOnlyPoint W) < δ₁ := by
    refine (hfl3 (topOnlyPoint W) (fun b => ?_) (fun i c => ?_)).2
    · simpa [topOnlyPoint, ComplexMatrix2.operatorNorm] using hε₃
    · simp only [topOnlyPoint]
      split_ifs with h
      · exact lt_of_lt_of_le (hWn _) (min_le_right _ _)
      · simpa [ComplexMatrix2.operatorNorm] using hε₃
  obtain ⟨Y, hY, hYb, hYn⟩ := exists_minimizer_near_unit hT hCov hSG hk hL hn hρ ha hnear hδ hW
    (fun b => lt_of_lt_of_le (hWn b) (min_le_left _ _)) hFc
  have hYU : Y.fine ∈ fieldSpace L n k 0 := hY.compact.2 0 (Nat.zero_le _)
  obtain ⟨w, hwr, hw1, hD, hvar⟩ := exists_nearest_gauge hT hEL hYU
  have hX₂r : IsCompactValued (gaugeTransformPoint w Y) :=
    gaugeTransformPoint_compact hCov hL hn hY.compact hwr
  have hX₂F : chainAction a (gaugeTransformPoint w Y) = chainAction a Y :=
    chainAction_gaugeTransformPoint hCov hSG hk hL hn hY.compact hwr a
  have hX₂t : levelField (gaugeTransformPoint w Y) k = W := by
    rw [levelField_gaugeTransformPoint hCov hL hn hY.compact hwr k le_rfl, hY.top_eq]
    funext b
    simp only [PeriodicLattice.gaugeTransform, hw1]
    simp
  have hD' : ∑ b : PositiveEdge L n k 0, traceDefect ((gaugeTransformPoint w Y).fine b.1) ≤
      ∑ b : PositiveEdge L n k 0, traceDefect (Y.fine b.1) := by
    simp only [finsum_eq_sum_of_fintype] at hD
    exact hD
  have hvar' : ∀ κ ∈ topVanishingGauges L n k,
      distanceGaugeVariation (gaugeTransformPoint w Y).fine
      (κ : Vertex L n k 0 → ComplexMatrix2) = 0 := hvar
  have hen : ∀ i c, traceDefect ((gaugeTransformPoint w Y).noise i c) = traceDefect (Y.noise i c) :=
    fun i c => traceDefect_conj (hwr _)
  generalize gaugeTransformPoint w Y = X₂ at hX₂r hX₂F hX₂t hD' hvar' hen
  have hτ1 : ε₁ * Nn ≤ τ := by
    have h := min_le_right (ε₀ / 2) (τ / Nn)
    calc ε₁ * Nn ≤ τ / Nn * Nn := by gcongr
      _ = τ := by field_simp
  have hε₁τ : ε₁ ≤ τ := by nlinarith
  have hUb : ∀ b, X₂.fine b ∈ PeriodicLattice.compactGaugeGroup := fun b =>
    (hX₂r.2 0 (Nat.zero_le _)).1 b (Set.mem_univ b)
  have hDe : ∀ b : PositiveEdge L n k 0, traceDefect (Y.fine b.1) ≤ ε₁ ^ 2 / 2 := by
    intro b
    have h1 := operatorNorm_sub_one_sq (hYU.1 b.1 (Set.mem_univ _))
    have h2 := hYb b.1
    have h3 : ComplexMatrix2.operatorNorm (Y.fine b.1 - 1) ^ 2 ≤ ε₁ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  have hpos : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (X₂.fine b - 1) ≤ τ := by
    intro b hb
    have h1 := operatorNorm_sub_one_sq (hUb b)
    have h2 : traceDefect (X₂.fine b) ≤
        (Fintype.card (PositiveEdge L n k 0) : ℝ) * (ε₁ ^ 2 / 2) :=
      le_card_mul_of_sum_le (f := fun b : PositiveEdge L n k 0 => traceDefect (X₂.fine b.1))
        (g := fun b : PositiveEdge L n k 0 => traceDefect (Y.fine b.1))
        (fun b => (traceDefect_nonneg_and_eq_zero (hUb b.1)).1) hD' hDe ⟨b, hb⟩
    have h4 : ComplexMatrix2.operatorNorm (X₂.fine b - 1) ^ 2 ≤ τ ^ 2 := by
      have h5 : (Fintype.card (PositiveEdge L n k 0) : ℝ) ≤ Nn ^ 2 := by nlinarith
      have h6 : (ε₁ * Nn) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by positivity) hτ1 2
      have h7 : 0 ≤ ε₁ ^ 2 := by positivity
      nlinarith
    exact abs_le_of_sq_le_sq' h4 hτ0.le |>.2
  have hbase : ∀ b, ComplexMatrix2.operatorNorm (X₂.fine b - 1) ≤ τ := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hbr := (isPositivelyOriented_or_opposite b).resolve_left hb
      have h1 := operatorNorm_sub_one_sq (hUb b)
      have h2 := operatorNorm_sub_one_sq (hUb b.opposite)
      have e1 : X₂.fine b.opposite = (X₂.fine b)⁻¹ :=
        (hX₂r.2 0 (Nat.zero_le _)).2 b (Set.mem_univ _)
      have e2 : traceDefect (X₂.fine b.opposite) = traceDefect (X₂.fine b) := by
        rw [e1]
        exact traceDefect_inv (hUb b)
      have h3 := hpos _ hbr
      have h4 : ComplexMatrix2.operatorNorm (X₂.fine b - 1) ^ 2 ≤ τ ^ 2 := by
        rw [h1, ← e2, ← h2]
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      exact abs_le_of_sq_le_sq' h4 hτ0.le |>.2
  have hnoise : ∀ i c, ComplexMatrix2.operatorNorm (X₂.noise i c - 1) ≤ τ := by
    intro i c
    have h1 := operatorNorm_sub_one_sq (hX₂r.1 i c)
    have h2 := operatorNorm_sub_one_sq (hY.compact.1 i c)
    have e1 := hen i c
    have h3 : ComplexMatrix2.operatorNorm (Y.noise i c - 1) ≤ τ := (hYn i c).trans hε₁τ
    have h4 : ComplexMatrix2.operatorNorm (X₂.noise i c - 1) ^ 2 ≤ τ ^ 2 := by
      rw [h1, e1, ← h2]
      exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    exact abs_le_of_sq_le_sq' h4 hτ0.le |>.2
  obtain ⟨ξ, hξ, hξ1, hξ2⟩ := exists_levelForms_chart hT hEL hX₂r (min_le_left _ _) hbase hnoise
  have h2τ : 2 * τ < ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / 4)
    linarith
  refine ⟨ξ, fun b => (hξ1 b).trans_lt h2τ, fun i b => (hξ2 i b).trans_lt h2τ, ?_,
    fun κ hκ => ?_⟩
  · rw [hξ]
    refine ⟨hX₂r, hX₂t, fun X' h1 h2 => ?_⟩
    rw [hX₂F]
    exact hY.le X' h1 h2
  · rw [hξ]
    exact hvar' κ hκ
end YangMills.Construction.RunningCouplingSlope.NearestGaugeMinimizerProof
end
