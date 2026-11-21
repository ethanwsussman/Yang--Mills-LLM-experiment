import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPointsProof
import YangMills.Construction.RunningCouplingSlope.FirstOrderSystemOfABranch
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FirstVariationProof
open YangMills.Construction.Matrices
open YangMills.Construction.Tower
open YangMills.Construction.Tower.LeftChartFields
section Smooth
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
private theorem contDiffAt_sqrt_of_eq_one {f : P → ℂ} (hf : ContDiffAt ℝ m f p₀) (h1 : f p₀ = 1) :
    ContDiffAt ℝ m (fun p => f p ^ (1 / 2 : ℂ)) p₀ := by apply _root_.YangMills.SharedProofs.p99689 <;> assumption
end Smooth
section Family
variable {L n k j : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem pathHolonomy_const_one (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.pathHolonomy_one <;> assumption
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
  contDiffAt_sqrt_of_eq_one (contDiffAt_det (contDiffAt_contourMean hV h1 c)) hc
private theorem contDiffAt_normalizedMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (hc : meanRadius (V p₀) c = 1)
    (hd : Matrix.det (contourMean (V p₀) c) = 1) :
    ContDiffAt ℝ m (fun p => normalizedMean (V p) c) p₀ := by apply _root_.YangMills.SharedProofs.p35211 <;> assumption
end Family
section Fields
variable {L n k : ℕ}
private theorem positive_or_opposite_positive {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem levelField_succ_of_positive (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_of_not_positive (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p3610 <;> assumption
private structure ProofInputs (L n k : ℕ) : Prop where
  vertexFinite : ∀ j, j ≤ k → Finite (Vertex L n k j)
  positiveEdgeFinite : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  edgeFinite : ∀ j, j ≤ k → Finite (Edge L n k j)
  faceFinite : Finite (Face L n k 0)
  differentialAtOne : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j, ∀ c : Edge L n k (j + 1),
    c.IsPositivelyOriented →
    leftDifferential normalizedMean (fun _ => 1) B c = linearSmoothing L n k j B c
  smoothingMem : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
    linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1)
  notBothPositive : ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
    ¬ b.opposite.IsPositivelyOriented
  atOne : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      meanRadius (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  leftMem : ∀ j, j ≤ k → (finiteData L n k j).LeftExpMulMemGroup
  curveLogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_levelFields (hT : ProofInputs L n k) {X : P → ChainPoint L n k}
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
    haveI := hT.vertexFinite j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
        ContDiffAt ℝ m (fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c) p₀ ∧
        (X p₀).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X p₀) j) c = 1 := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := hT.atOne j hj c hc
      refine ⟨(hn _ _).mul (contDiffAt_normalizedMean ih1 ih2 c ?_ ?_), ?_⟩
      · rw [ih2, h2]
      · rw [ih2, h1]
        simp
      · rw [ih2, h3, h0]
        simp [unitPoint]
    have hval : levelField (X p₀) (j + 1) = fun _ => 1 := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · rw [levelField_succ_of_positive _ hj c hc]
        exact (hpos c hc).2
      · have hc' : c.opposite.IsPositivelyOriented :=
          (positive_or_opposite_positive c).resolve_left hc
        rw [levelField_succ_of_not_positive _ hj c hc hc', (hpos c.opposite hc').2]
        simp
    refine ⟨fun c => ?_, hval⟩
    by_cases hc : c.IsPositivelyOriented
    · have e : (fun p => levelField (X p) (j + 1) c) = fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c := by
        funext p
        exact levelField_succ_of_positive _ hj c hc
      rw [e]
      exact (hpos c hc).1
    · have hc' : c.opposite.IsPositivelyOriented :=
        (positive_or_opposite_positive c).resolve_left hc
      have e : (fun p => levelField (X p) (j + 1) c) = fun p =>
          ((X p).noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ *
            normalizedMean (levelField (X p) j) c.opposite)⁻¹ := by
        funext p
        exact levelField_succ_of_not_positive _ hj c hc hc'
      rw [e]
      exact contDiffAt_inv_of_eq_one (hpos c.opposite hc').1 (hpos c.opposite hc').2
private theorem contDiffAt_meanRadius_levelField (hT : ProofInputs L n k)
    {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ContDiffAt ℝ m (fun p => meanRadius (levelField (X p) i) c) p₀ := by
  obtain ⟨h1, h2⟩ := contDiffAt_levelFields hT hb hn h0 i hi.le
  haveI := hT.vertexFinite i hi.le
  refine contDiffAt_meanRadius h1 h2 c ?_
  rw [h2, (hT.atOne i hi c hc).1]
  simp
private theorem contDiffAt_matExp_I_smul {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => ComplexMatrix2.matExp (Complex.I • f p)) p₀ := by apply _root_.YangMills.SharedProofs.p25406 <;> assumption
private theorem contDiffAt_expTwist {j : ℕ} {A U : P → Edge L n k j → ComplexMatrix2}
    (hA : ∀ b, ContDiffAt ℝ m (fun p => A p b) p₀)
    (hU : ∀ b, ContDiffAt ℝ m (fun p => U p b) p₀)
    (hA0 : A p₀ = 0) (hU0 : U p₀ = fun _ => 1) (b : Edge L n k j) :
    ContDiffAt ℝ m (fun p => PeriodicLattice.expTwist (A p) (U p) b) p₀ := by apply _root_.YangMills.SharedProofs.p28082 <;> assumption
end Fields
private theorem exists_continuous_partialDeriv_snd {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E × ℝ → F}
    (hf : ContDiffAt ℝ 2 f ((0 : E), (0 : ℝ))) :
    ∃ G : E → F, ContinuousAt G 0 ∧
      ∀ᶠ w in 𝓝 (0 : E), HasDerivAt (fun t => f (w, t)) (G w) 0 := by apply _root_.YangMills.SharedProofs.p85562 <;> assumption
section Curves
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_matExp_line (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.SharedProofs.p9756 <;> assumption
private theorem matExp_line_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by apply _root_.YangMills.SharedProofs.p11429 <;> assumption
variable {L n k j : ℕ}
private def curveVelocity (V M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then Complex.I • M b * V b else V b * (Complex.I • M b)
private theorem opposite_opposite_edge (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem det_eq_one_of_mem_fieldsIn {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    Matrix.det (V b) = 1 := hV.1 b (Set.mem_univ b)
private theorem inv_opposite_of_mem_fieldsIn {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    (V b.opposite)⁻¹ = V b := by apply _root_.YangMills.SharedProofs.p4213 <;> assumption
private theorem hasDerivAt_expTwist_line {V M : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) (curveVelocity V M b) 0 := by apply _root_.YangMills.DeltaSharedProofs.p350 <;> assumption
private theorem expTwist_zero {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist (0 : Edge L n k j → ComplexMatrix2) V = V := by apply _root_.YangMills.SharedProofs.p57400 <;> assumption
private theorem hasDerivAt_inv_of_det_eq_one
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {W : ℝ → ComplexMatrix2} {W' : ComplexMatrix2} (hW : HasDerivAt W W' 0)
    (h0 : Matrix.det (W 0) = 1) :
    HasDerivAt (fun t => (W t)⁻¹) (-((W 0)⁻¹ * W' * (W 0)⁻¹)) 0 := by apply _root_.YangMills.SharedProofs.p36414 <;> assumption
end Curves
section Movement
variable {L n k : ℕ}
private theorem extendOddly_opposite (hT : ProofInputs L n k) {j : ℕ} (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hb' := hT.notBothPositive j hj b hb
    simp only [extendOddly, if_pos hb, if_neg hb', opposite_opposite_edge]
  · have hb' : b.opposite.IsPositivelyOriented :=
      (positive_or_opposite_positive b).resolve_left hb
    simp only [extendOddly, if_pos hb', if_neg hb, neg_neg]
private theorem tangentTransport_succ_positive (X : ChainPoint L n k) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, hj⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by apply _root_.YangMills.SharedProofs.p457 <;> assumption
private theorem tangentTransport_opposite (hT : ProofInputs L n k) (X : ChainPoint L n k)
    (ξ : LevelForms L n k) : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      tangentTransport X ξ j b.opposite = -tangentTransport X ξ j b := by
  intro j hj b
  cases j with
  | zero => exact ξ.1.2.2 b
  | succ j =>
    have hj' : j < k := hj
    rw [tangentTransport, dif_pos hj']
    exact extendOddly_opposite hT hj _ b
private theorem levelField_eq_inv_opposite (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c = (levelField X (j + 1) c.opposite)⁻¹ := by
  rw [levelField_succ_of_not_positive X hj c hc hc', levelField_succ_of_positive X hj c.opposite hc']
private def MeanBehavesNearOne (L n k : ℕ) (ρ : ℝ) : Prop :=
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
private theorem mem_fieldsIn_complex_of_mem_fieldSpace {j : ℕ}
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
private theorem det_eq_one_of_mem_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
private theorem expMove_zero_smul {X : ChainPoint L n k}
    (hX : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (η : LevelForms L n k) :
    expMove ((0 : ℝ) • η) X = X := by apply _root_.YangMills.SharedProofs.p18865 <;> assumption
private theorem conjugate_step_identity (n u D ν : ComplexMatrix2) (hn : n⁻¹ * n = 1)
    (hu : u⁻¹ * u = 1) :
    Complex.I • (ComplexMatrix2.conjugateBy n (Complex.I⁻¹ • (D * u⁻¹)) + ν) * (n * u) =
      (Complex.I • ν * n) * u + n * D := by apply _root_.YangMills.SharedProofs.p26677 <;> assumption
private theorem leftDifferential_eq_of_hasDerivAt
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {j : ℕ} {V M : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {D : ComplexMatrix2}
    (h2 : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist (t • M) V) c) D 0)
    (h0 : normalizedMean (PeriodicLattice.expTwist ((0 : ℝ) • M) V) c = normalizedMean V c)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    leftDifferential normalizedMean V M c = Complex.I⁻¹ • (D * (normalizedMean V c)⁻¹) := by apply _root_.YangMills.SharedProofs.p13783 <;> assumption
private theorem hasDerivAt_levelField_expMove
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ : MeanBehavesNearOne L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (η : LevelForms L n k) : ∀ j, j ≤ k → ∀ b,
      HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) j b)
        (curveVelocity (levelField X j) (tangentTransport X η j) b) 0 := by
  have hX0 : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
    mem_fieldsIn_complex_of_mem_fieldSpace (hX.2 0 (Nat.zero_le _))
  have hY0 := expMove_zero_smul hX0 η
  intro j
  induction j with
  | zero =>
    intro _ b
    exact hasDerivAt_expTwist_line hX0 η.1.2.2 b
  | succ j ih =>
    intro h
    have hj : j < k := h
    have ih' := ih hj.le
    have hWc := mem_fieldsIn_complex_of_mem_fieldSpace (hX.2 j hj.le)
    have hMa := tangentTransport_opposite hT X η j hj.le
    have hW1 : ∀ c : Edge L n k (j + 1), Matrix.det (levelField X (j + 1) c) = 1 :=
      det_eq_one_of_mem_fieldsIn (mem_fieldsIn_complex_of_mem_fieldSpace (hX.2 (j + 1) hj))
    have pos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c)
          (Complex.I • tangentTransport X η (j + 1) c * levelField X (j + 1) c) 0 := by
      intro c hc
      obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc (hnear j hj.le) c hc
      have h1 := hD _ (fun t => levelField (expMove (t • η) X) j) (by simp only [hY0]) ih'
      have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X η j) (levelField X j) =
          levelField X j := by
        rw [zero_smul]
        exact expTwist_zero hWc
      have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X η j)
        (levelField X j)) h0 (fun b => hasDerivAt_expTwist_line hWc hMa b)
      have hmd := leftDifferential_eq_of_hasDerivAt hd hc h2 (by rw [h0]) hu
      have hn : HasDerivAt (fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩)
          (Complex.I • (η.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c *
            X.noise ⟨j, hj⟩ ⟨c, hc⟩) 0 :=
        (hasDerivAt_matExp_line _).mul_const _
      have hp := hn.mul h1
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c) =
          fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩ *
            normalizedMean (levelField (expMove (t • η) X) j) c := by
        funext t
        exact levelField_succ_of_positive _ hj c hc
      rw [e]
      refine hp.congr_deriv ?_
      simp only [hY0]
      rw [tangentTransport_succ_positive X η hj c hc, levelField_succ_of_positive X hj c hc, hmd]
      exact (conjugate_step_identity _ _ _ _
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one (det_eq_one_of_mem_compact (hX.1 _ _))))
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one hu))).symm
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [curveVelocity, if_pos hb]
      exact pos b hb
    · have hb' : b.opposite.IsPositivelyOriented :=
        (positive_or_opposite_positive b).resolve_left hb
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b) =
          fun t : ℝ => (levelField (expMove (t • η) X) (j + 1) b.opposite)⁻¹ := by
        funext t
        exact levelField_eq_inv_opposite _ hj b hb hb'
      rw [e]
      have hdet : Matrix.det
          ((fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b.opposite) 0) = 1 := by
        simp only [hY0]
        exact hW1 _
      refine (hasDerivAt_inv_of_det_eq_one hd (pos b.opposite hb') hdet).congr_deriv ?_
      simp only [hY0, curveVelocity, if_neg hb]
      rw [levelField_eq_inv_opposite X hj b hb hb', tangentTransport_opposite hT X η (j + 1) hj b]
      have hA : levelField X (j + 1) b.opposite * (levelField X (j + 1) b.opposite)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ (isUnit_det_of_eq_one (hW1 _))
      simp only [smul_neg, mul_neg, neg_mul, neg_neg]
      rw [mul_assoc ((levelField X (j + 1) b.opposite)⁻¹), mul_assoc (Complex.I • _), hA, mul_one]
end Movement
section Compact
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
variable {L n k j : ℕ}
private theorem normalizedMean_mem_compact [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hu : Matrix.det (normalizedMean V c) = 1) :
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p11178 <;> assumption
private theorem expTwist_mem_fieldSpace (hT : ProofInputs L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) (t : ℝ) :
    PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V ∈ fieldSpace L n k j := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t • (M : Edge L n k j → ComplexMatrix2)) b)) * V b ∈
        PeriodicLattice.compactGaugeGroup := by
    intro b hb
    have h := ((hT.leftMem j hj).1 V hV (M : Edge L n k j → ComplexMatrix2) M.2 ⟨b, hb⟩).1 t
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
      exact inv_mem_compact (hpos _ ((positive_or_opposite_positive b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := hT.notBothPositive j hj b hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', opposite_opposite_edge]
    · have hb' : b.opposite.IsPositivelyOriented :=
        (positive_or_opposite_positive b).resolve_left hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [Matrix.nonsing_inv_nonsing_inv _
        (isUnit_det_of_eq_one (det_eq_one_of_mem_compact (hpos _ hb')))]
end Compact
section Top
variable {L n k j : ℕ}
private theorem expTwist_line_eventually_near (hT : ProofInputs L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) {ρ : ℝ}
    (hnear : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ b, ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1) < ρ := by
  haveI := hT.edgeFinite j hj
  have hc := mem_fieldsIn_complex_of_mem_fieldSpace hV
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
private theorem leftDifferential_mem_hermitianTraceless
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ : MeanBehavesNearOne L n k ρ) (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (hnear : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) (M : edgeFormSpace L n k j)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    leftDifferential normalizedMean V (M : Edge L n k j → ComplexMatrix2) c ∈
      ComplexMatrix2.hermitianTraceless := by
  obtain ⟨δ, hδ, hh⟩ := expTwist_line_eventually_near hT hj.le hV M hnear
  have hWc := mem_fieldsIn_complex_of_mem_fieldSpace hV
  obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc hnear c hc
  have h0 : PeriodicLattice.expTwist ((0 : ℝ) • (M : Edge L n k j → ComplexMatrix2)) V = V := by
    rw [zero_smul]
    exact expTwist_zero hWc
  have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V)
    h0 (fun b => hasDerivAt_expTwist_line hWc M.2.2 b)
  rw [leftDifferential_eq_of_hasDerivAt hd hc h2 (by rw [h0]) hu]
  haveI := hT.vertexFinite j hj.le
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) δ) := by
    refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hδ⟩
    rw [Real.ball_eq_Ioo]
    exact Set.ordConnected_Ioo
  have hmaps : MapsTo (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
      (t • (M : Edge L n k j → ComplexMatrix2)) V) c) (Metric.ball (0 : ℝ) δ)
      PeriodicLattice.compactGaugeGroup := by
    intro t ht
    have ht' : |t| < δ := by simpa [Real.dist_eq] using ht
    have hr := expTwist_mem_fieldSpace hT hj.le hV M t
    exact normalizedMean_mem_compact hr c
      (hρ j hj _ (mem_fieldsIn_complex_of_mem_fieldSpace hr) (hh t ht') c hc).2.2.2.1
  have hl := (hT.curveLogs _ hI _ hmaps h2.differentiableAt).2.2.2
  rw [h2.deriv] at hl
  simp only [h0] at hl
  exact hl
private theorem conjugateBy_mem_hermitianTraceless {g A : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
private theorem curveVelocity_add (V M M' : Edge L n k j → ComplexMatrix2) :
    curveVelocity V (M + M') = curveVelocity V M + curveVelocity V M' := by apply _root_.YangMills.DeltaSharedProofs.p501277 <;> assumption
private theorem curveVelocity_smul (V M : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    curveVelocity V (r • M) = r • curveVelocity V M := by apply _root_.YangMills.DeltaSharedProofs.p500676 <;> assumption
private theorem exists_linear_tangentTransport
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ : MeanBehavesNearOne L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) :
    ∀ j, j ≤ k → ∃ T : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k j,
      ∀ ξ, (T ξ : Edge L n k j → ComplexMatrix2) = tangentTransport X ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨LinearMap.fst ℝ _ _, fun _ => rfl⟩
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨T, hTv⟩ := ih hj.le
    have hWr := hX.2 j hj.le
    have hWc := mem_fieldsIn_complex_of_mem_fieldSpace hWr
    have hmem : ∀ ξ : LevelForms L n k,
        tangentTransport X ξ (j + 1) ∈ edgeFormSpace L n k (j + 1) := by
      intro ξ
      refine ⟨fun b hb => ?_, tangentTransport_opposite hT X ξ (j + 1) hj⟩
      rw [tangentTransport_succ_positive X ξ hj b hb, ← hTv ξ]
      exact ComplexMatrix2.hermitianTraceless.add_mem (conjugateBy_mem_hermitianTraceless (hX.1 _ _)
        (leftDifferential_mem_hermitianTraceless hd hT hρ hj hWr (hnear j hj.le) (T ξ) b hb))
        ((ξ.2 ⟨j, hj⟩).2.1 b hb)
    have hform : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ∃ Λ : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2, ∀ ξ : LevelForms L n k,
          tangentTransport X ξ (j + 1) c =
            Λ (curveVelocity (levelField X j) (tangentTransport X ξ j)) +
            (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by
      intro c hc
      obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc (hnear j hj.le) c hc
      let Λ : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2 :=
        { toFun := fun Y => ComplexMatrix2.conjugateBy (X.noise ⟨j, hj⟩ ⟨c, hc⟩)
            (Complex.I⁻¹ • (D Y * (normalizedMean (levelField X j) c)⁻¹))
          map_add' := fun Y Y' => by
            simp only [ComplexMatrix2.conjugateBy, map_add, add_mul, mul_add, smul_add]
          map_smul' := fun r Y => by
            simp only [ComplexMatrix2.conjugateBy, map_smul, smul_mul_assoc, mul_smul_comm,
              RingHom.id_apply]
            rw [smul_comm] }
      refine ⟨Λ, fun ξ => ?_⟩
      have hMa := tangentTransport_opposite hT X ξ j hj.le
      have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X ξ j) (levelField X j) =
          levelField X j := by
        rw [zero_smul]
        exact expTwist_zero hWc
      have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X ξ j)
        (levelField X j)) h0 (fun b => hasDerivAt_expTwist_line hWc hMa b)
      rw [tangentTransport_succ_positive X ξ hj c hc,
        leftDifferential_eq_of_hasDerivAt hd hc h2 (by rw [h0]) hu]
      rfl
    have hadd : ∀ ξ ξ' : LevelForms L n k,
        tangentTransport X (ξ + ξ') (j + 1) =
          tangentTransport X ξ (j + 1) + tangentTransport X ξ' (j + 1) := by
      intro ξ ξ'
      have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
          tangentTransport X (ξ + ξ') (j + 1) c =
            tangentTransport X ξ (j + 1) c + tangentTransport X ξ' (j + 1) c := by
        intro c hc
        obtain ⟨Λ, hΛ⟩ := hform c hc
        rw [hΛ, hΛ, hΛ, ← hTv, ← hTv, ← hTv, map_add, Submodule.coe_add, curveVelocity_add,
          map_add]
        simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add]
        abel
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hp c hc
      · have hc' := (positive_or_opposite_positive c).resolve_left hc
        have e := fun ξ'' : LevelForms L n k =>
          tangentTransport_opposite hT X ξ'' (j + 1) hj c.opposite
        rw [opposite_opposite_edge] at e
        rw [Pi.add_apply, e, e, e, hp _ hc']
        abel
    have hsmul : ∀ (r : ℝ) (ξ : LevelForms L n k),
        tangentTransport X (r • ξ) (j + 1) = r • tangentTransport X ξ (j + 1) := by
      intro r ξ
      have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
          tangentTransport X (r • ξ) (j + 1) c = r • tangentTransport X ξ (j + 1) c := by
        intro c hc
        obtain ⟨Λ, hΛ⟩ := hform c hc
        rw [hΛ, hΛ, ← hTv, ← hTv, map_smul, Submodule.coe_smul, curveVelocity_smul, map_smul,
          smul_add]
        simp only [Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul]
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hp c hc
      · have hc' := (positive_or_opposite_positive c).resolve_left hc
        have e := fun ξ'' : LevelForms L n k =>
          tangentTransport_opposite hT X ξ'' (j + 1) hj c.opposite
        rw [opposite_opposite_edge] at e
        rw [Pi.smul_apply, e, e, hp _ hc', smul_neg]
    exact ⟨{ toFun := fun ξ => ⟨tangentTransport X ξ (j + 1), hmem ξ⟩
             map_add' := fun ξ ξ' => Subtype.ext (hadd ξ ξ')
             map_smul' := fun r ξ => Subtype.ext (hsmul r ξ) }, fun _ => rfl⟩
private theorem topDeriv_eq_tangentTransport
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ : MeanBehavesNearOne L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (ξ : LevelForms L n k) :
    (topDeriv X ξ : Edge L n k k → ComplexMatrix2) = tangentTransport X ξ k := by
  obtain ⟨T, hTv⟩ := exists_linear_tangentTransport hd hT hρ hX hnear k le_rfl
  exact Classical.epsilon_spec (p := IsTopDeriv X) ⟨T, hTv⟩ ξ
end Top
section Unit
variable {L n k : ℕ}
private theorem levelField_unitPoint (hT : ProofInputs L n k) : ∀ j, j ≤ k →
    levelField (unitPoint L n k) j = fun _ => 1 := fun j hj =>
  (contDiffAt_levelFields (P := ℝ) (p₀ := 0) (m := 0) hT (X := fun _ => unitPoint L n k)
    (fun _ => contDiffAt_const) (fun _ _ => contDiffAt_const) rfl j hj).2
private theorem const_one_mem_fieldSpace {j : ℕ} :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩
private theorem unitPoint_isCompactValued (hT : ProofInputs L n k) :
    IsCompactValued (unitPoint L n k) := by
  refine ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun j hj => ?_⟩
  rw [levelField_unitPoint hT j hj]
  exact const_one_mem_fieldSpace
private theorem linearTransport_succ (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearTransport ξ (j + 1) = linearSmoothing L n k j (linearTransport ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearTransport, dif_pos hj]
private theorem linearTransport_mem (hT : ProofInputs L n k) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → linearTransport ξ j ∈ edgeFormSpace L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => ξ.1.2
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearTransport_succ ξ hj]
    exact (edgeFormSpace L n k (j + 1)).add_mem (hT.smoothingMem j hj _ (ih hj.le))
      (ξ.2 ⟨j, hj⟩).2
private theorem conjugateBy_one (A : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 A = A := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
private theorem tangentTransport_unitPoint (hT : ProofInputs L n k) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → tangentTransport (unitPoint L n k) ξ j = linearTransport ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        tangentTransport (unitPoint L n k) ξ (j + 1) c = linearTransport ξ (j + 1) c := by
      intro c hc
      rw [tangentTransport_succ_positive _ ξ hj c hc, ih hj.le, levelField_unitPoint hT j hj.le,
        linearTransport_succ ξ hj]
      simp only [unitPoint, conjugateBy_one, Pi.add_apply]
      rw [hT.differentialAtOne j hj _ (linearTransport_mem hT ξ j hj.le) c hc]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hp c hc
    · have hc' := (positive_or_opposite_positive c).resolve_left hc
      have e := tangentTransport_opposite hT (unitPoint L n k) ξ (j + 1) hj c.opposite
      rw [opposite_opposite_edge] at e
      have e2 := (linearTransport_mem hT ξ (j + 1) hj).2 c.opposite
      rw [opposite_opposite_edge] at e2
      rw [e, e2, hp _ hc']
end Unit
section Families
variable {L n k : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {m : WithTop ℕ∞}
private theorem contDiffAt_linear_coord {j : ℕ} {p₀ : P} (A : P →ₗ[ℝ] edgeFormSpace L n k j)
    (b : Edge L n k j) :
    ContDiffAt ℝ m (fun p => (A p : Edge L n k j → ComplexMatrix2) b) p₀ :=
  (LinearMap.toContinuousLinearMap
    ((LinearMap.proj b : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2) ∘ₗ
      (edgeFormSpace L n k j).subtype ∘ₗ A)).contDiff.contDiffAt
private def twoStepPoint (A C : P →ₗ[ℝ] LevelForms L n k) (p : P) : ChainPoint L n k :=
  expMove (A p) (expMove (C p) (unitPoint L n k))
private def baseComponent : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k 0 := LinearMap.fst ℝ _ _
private def noiseComponent (i : Fin k) :
    LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k ((i : ℕ) + 1) :=
  (LinearMap.proj i) ∘ₗ LinearMap.snd ℝ _ _
private theorem twoStepPoint_zero (hT : ProofInputs L n k) (A C : P →ₗ[ℝ] LevelForms L n k) :
    twoStepPoint A C 0 = unitPoint L n k := by
  have h1 := mem_fieldsIn_complex_of_mem_fieldSpace
    (const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := 0))
  have e := expMove_zero_smul (X := unitPoint L n k) h1 (0 : LevelForms L n k)
  simp only [smul_zero] at e
  simp only [twoStepPoint, map_zero]
  rw [e, e]
private theorem contDiffAt_twoStepPoint_fine (A C : P →ₗ[ℝ] LevelForms L n k)
    (b : Edge L n k 0) :
    ContDiffAt ℝ m (fun p => (twoStepPoint A C p).fine b) (0 : P) := by
  have hc : ∀ b', ContDiffAt ℝ m (fun p => PeriodicLattice.expTwist
      ((C p).1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) b') (0 : P) := fun b' =>
    contDiffAt_expTwist (A := fun p => ((C p).1 : Edge L n k 0 → ComplexMatrix2))
      (U := fun _ _ => 1)
      (fun b'' => contDiffAt_linear_coord (baseComponent ∘ₗ C) b'') (fun _ => contDiffAt_const)
      (by simp) rfl b'
  refine contDiffAt_expTwist (A := fun p => ((A p).1 : Edge L n k 0 → ComplexMatrix2))
    (U := fun p => PeriodicLattice.expTwist ((C p).1 : Edge L n k 0 → ComplexMatrix2)
      (fun _ => 1))
    (fun b'' => contDiffAt_linear_coord (baseComponent ∘ₗ A) b'') hc (by simp) ?_ b
  have h1 := mem_fieldsIn_complex_of_mem_fieldSpace
    (const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := 0))
  simp only [map_zero, Prod.fst_zero, ZeroMemClass.coe_zero]
  exact expTwist_zero h1
private theorem contDiffAt_twoStepPoint_noise (A C : P →ₗ[ℝ] LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k ((i : ℕ) + 1)) :
    ContDiffAt ℝ m (fun p => (twoStepPoint A C p).noise i c) (0 : P) := by
  simp only [twoStepPoint, expMove, unitPoint]
  exact (contDiffAt_matExp_I_smul (contDiffAt_linear_coord (noiseComponent i ∘ₗ A) c.1)).mul
    ((contDiffAt_matExp_I_smul (contDiffAt_linear_coord (noiseComponent i ∘ₗ C) c.1)).mul
      contDiffAt_const)
end Families
section Branch
variable {L n k N : ℕ}
private def coordPoint (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    ChainPoint L n k :=
  expMove (e w).1 (unitPoint L n k)
private def coordTangent (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k :=
  LinearMap.fst ℝ _ _ ∘ₗ e.toLinearMap
private theorem coordPoint_fine_mem (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    (coordPoint e w).fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := by
  have h := expTwist_mem_fieldSpace hT (Nat.zero_le k)
    (const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := 0)) (e w).1.1 1
  rw [one_smul] at h
  exact mem_fieldsIn_complex_of_mem_fieldSpace h
private theorem twoStepPoint_zero_left (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    twoStepPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (coordTangent e) w = coordPoint e w := by
  have h := expMove_zero_smul (coordPoint_fine_mem hT e w) (0 : LevelForms L n k)
  simp only [smul_zero] at h
  simp only [twoStepPoint, LinearMap.zero_apply]
  exact h
private theorem contDiffAt_coordPoint_levelField (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {m : WithTop ℕ∞} : ∀ j, j ≤ k →
      (∀ b, ContDiffAt ℝ m (fun w => levelField (coordPoint e w) j b) (0 : Fin N → ℝ)) ∧
        levelField (coordPoint e 0) j = fun _ => 1 := by
  intro j hj
  have h := contDiffAt_levelFields (p₀ := (0 : Fin N → ℝ)) (m := m) hT
    (X := twoStepPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (coordTangent e))
    (contDiffAt_twoStepPoint_fine _ _) (contDiffAt_twoStepPoint_noise _ _)
    (twoStepPoint_zero hT _ _) j hj
  simpa only [twoStepPoint_zero_left hT e] using h
private theorem eventually_coordPoint_near (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    {ρ : ℝ} (hρ0 : 0 < ρ) : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (coordPoint e w) j b - 1) < ρ := by
  have h : ∀ j ∈ Finset.range (k + 1), ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ∀ b,
      ComplexMatrix2.operatorNorm (levelField (coordPoint e w) j b - 1) < ρ := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    haveI := hT.edgeFinite j hj'
    refine Filter.eventually_all.mpr fun b => ?_
    obtain ⟨h1, h2⟩ := contDiffAt_coordPoint_levelField (m := 0) hT e j hj'
    have h3 : Tendsto (fun w => ‖levelField (coordPoint e w) j b - 1‖)
        (𝓝 (0 : Fin N → ℝ)) (𝓝 0) := by
      have h4 := (((h1 b).continuousAt).tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [h2] using h4
    exact h3.eventually_lt_const hρ0
  have h' := (Filter.eventually_all_finset _).mpr h
  filter_upwards [h'] with w hw j hj
  exact hw j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
private theorem curveVelocity_one {j : ℕ} (M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    curveVelocity (fun _ => 1) M b = Complex.I • M b := by
  by_cases hb : b.IsPositivelyOriented <;> simp [curveVelocity, hb]
private theorem hasDerivAt_levelField_along_coords
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : MeanBehavesNearOne L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) (j : ℕ) (hj : j ≤ k)
    (b : Edge L n k j) :
    HasDerivAt (fun s => levelField (coordPoint e (c s)) j b)
      (Complex.I • linearTransport t.1 j b) 0 := by
  obtain ⟨h1, h2⟩ := contDiffAt_coordPoint_levelField (m := 2) hT e j hj
  have hdiff : HasFDerivAt (fun w => levelField (coordPoint e w) j b)
      (fderiv ℝ (fun w => levelField (coordPoint e w) j b) 0) 0 :=
    ((h1 b).differentiableAt (by norm_num)).hasFDerivAt
  have hF : HasFDerivAt (fun w => levelField (coordPoint e w) j b)
      (fderiv ℝ (fun w => levelField (coordPoint e w) j b) 0) (c 0) := by
    rw [hc0]
    exact hdiff
  have hcurve : HasDerivAt (fun s => levelField (coordPoint e (c s)) j b)
      (fderiv ℝ (fun w => levelField (coordPoint e w) j b) 0 (e.symm t)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hcd
  have hline : HasDerivAt (fun τ : ℝ => levelField (coordPoint e (τ • e.symm t)) j b)
      (fderiv ℝ (fun w => levelField (coordPoint e w) j b) 0 (e.symm t)) 0 := by
    have hl : HasDerivAt (fun τ : ℝ => τ • e.symm t) (e.symm t) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (e.symm t)
    have hF' : HasFDerivAt (fun w => levelField (coordPoint e w) j b)
        (fderiv ℝ (fun w => levelField (coordPoint e w) j b) 0) ((0 : ℝ) • e.symm t) := by
      rw [zero_smul]
      exact hdiff
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF' hl
  have hunit : ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (unitPoint L n k) j b - 1) < ρ := by
    intro j hj b
    rw [levelField_unitPoint hT j hj]
    simpa using hρ0
  have hmv := hasDerivAt_levelField_expMove hd hT hρ (unitPoint_isCompactValued hT) hunit t.1 j hj b
  have e1 : (fun τ : ℝ => levelField (coordPoint e (τ • e.symm t)) j b) =
      fun τ : ℝ => levelField (expMove (τ • t.1) (unitPoint L n k)) j b := by
    funext τ
    simp only [coordPoint, map_smul, LinearEquiv.apply_symm_apply, Prod.smul_fst]
  rw [e1] at hline
  have e2 := hline.unique hmv
  rw [e2, levelField_unitPoint hT j hj, tangentTransport_unitPoint hT t.1 j hj,
    curveVelocity_one] at hcurve
  exact hcurve
private theorem linearTransport_top_eq
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : MeanBehavesNearOne L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) (B : edgeFormSpace L n k k)
    (hev : ∀ᶠ s in 𝓝 (0 : ℝ), levelField (coordPoint e (c s)) k =
      PeriodicLattice.expTwist (s • (B : Edge L n k k → ComplexMatrix2)) fun _ => 1) :
    linearTransport t.1 k = B := by
  have hone := mem_fieldsIn_complex_of_mem_fieldSpace
    (const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := k))
  have hpos : ∀ b : Edge L n k k,
      linearTransport t.1 k b = (B : Edge L n k k → ComplexMatrix2) b := by
    intro b
    have h1 := hasDerivAt_levelField_along_coords hd hT hρ0 hρ e hc0 hcd k le_rfl b
    have h2 := hasDerivAt_expTwist_line hone B.2.2 b
    have h3 : HasDerivAt (fun s => levelField (coordPoint e (c s)) k b)
        (curveVelocity (fun _ => 1) B b) 0 := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hev] with s hs
      rw [hs]
    have h4 := h1.unique h3
    rw [curveVelocity_one] at h4
    exact smul_right_injective ComplexMatrix2 Complex.I_ne_zero h4
  funext b
  exact hpos b
end Branch
section Products
private theorem hasDerivAt_mul_of_left_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {f g : ℝ → 𝔸} {f' g₀ : 𝔸} (hf0 : f 0 = 0) (hf : HasDerivAt f f' 0)
    (hg : Tendsto g (𝓝 0) (𝓝 g₀)) : HasDerivAt (fun s => f s * g s) (f' * g₀) 0 := by apply _root_.YangMills.SharedProofs.p10857 <;> assumption
private def halfTraceRe : ComplexMatrix2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (ComplexMatrix2.halfTrace A).re
      map_add' := fun A B => by
        simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
      map_smul' := fun r A => by
        have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
        simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
          ComplexMatrix2.fullTrace]
        rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
private theorem halfTraceRe_apply (A : ComplexMatrix2) :
    halfTraceRe A = (ComplexMatrix2.halfTrace A).re := rfl
variable {L n k j : ℕ}
private theorem edgeFormPairing_re_eq_sum [Fintype (PositiveEdge L n k j)]
    (X Y : Edge L n k j → ComplexMatrix2) :
    (edgeFormPairing X Y).re = ∑ c : PositiveEdge L n k j, halfTraceRe (X c * Y c) := by
  simp only [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges]
  rw [finsum_eq_sum_of_fintype, Complex.re_sum]
  rfl
private theorem hasDerivAt_edgeFormPairing_re_of_zero [Finite (PositiveEdge L n k j)]
    {Y g : ℝ → Edge L n k j → ComplexMatrix2} {Y' g₀ : Edge L n k j → ComplexMatrix2}
    (hY0 : ∀ b, b.IsPositivelyOriented → Y 0 b = 0)
    (hY : ∀ b, b.IsPositivelyOriented → HasDerivAt (fun s => Y s b) (Y' b) 0)
    (hg : ∀ b, b.IsPositivelyOriented → Tendsto (fun s => g s b) (𝓝 0) (𝓝 (g₀ b))) :
    HasDerivAt (fun s => (edgeFormPairing (Y s) (g s)).re) ((edgeFormPairing Y' g₀).re) 0 := by
  haveI := Fintype.ofFinite (PositiveEdge L n k j)
  simp only [edgeFormPairing_re_eq_sum]
  refine HasDerivAt.fun_sum fun c _ => ?_
  exact halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mul_of_left_zero (hY0 c.1 c.2) (hY c.1 c.2) (hg c.1 c.2))
private theorem hasDerivAt_edgeFormPairing_re_left [Finite (PositiveEdge L n k j)]
    {Y : ℝ → Edge L n k j → ComplexMatrix2} {Y' Z : Edge L n k j → ComplexMatrix2}
    (hY : ∀ b, b.IsPositivelyOriented → HasDerivAt (fun s => Y s b) (Y' b) 0) :
    HasDerivAt (fun s => (edgeFormPairing (Y s) Z).re) ((edgeFormPairing Y' Z).re) 0 := by
  haveI := Fintype.ofFinite (PositiveEdge L n k j)
  simp only [edgeFormPairing_re_eq_sum]
  refine HasDerivAt.fun_sum fun c _ => ?_
  exact halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hY c.1 c.2).mul_const _)
end Products
section Partials
variable {L n k N : ℕ}
private def lineMap (η : LevelForms L n k) : ((Fin N → ℝ) × ℝ) →ₗ[ℝ] LevelForms L n k :=
  (LinearMap.toSpanSingleton ℝ _ η) ∘ₗ LinearMap.snd ℝ _ _
private def coordTangentFst (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    ((Fin N → ℝ) × ℝ) →ₗ[ℝ] LevelForms L n k :=
  coordTangent e ∘ₗ LinearMap.fst ℝ _ _
private theorem exists_partial_levelField (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    (η : LevelForms L n k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    ∃ G : (Fin N → ℝ) → ComplexMatrix2, ContinuousAt G 0 ∧ ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      HasDerivAt (fun τ : ℝ => levelField (expMove (τ • η) (coordPoint e w)) j b) (G w) 0 := by
  have h := (contDiffAt_levelFields
    (p₀ := (((0 : Fin N → ℝ), (0 : ℝ)) : (Fin N → ℝ) × ℝ)) (m := 2) hT
    (X := twoStepPoint (lineMap η) (coordTangentFst e)) (contDiffAt_twoStepPoint_fine _ _)
    (contDiffAt_twoStepPoint_noise _ _) (twoStepPoint_zero hT _ _) j hj).1 b
  exact exists_continuous_partialDeriv_snd h
private theorem exists_partial_meanRadius (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    (η : LevelForms L n k) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ∃ G : (Fin N → ℝ) → ℝ, ContinuousAt G 0 ∧ ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      HasDerivAt (fun τ : ℝ =>
        (meanRadius (levelField (expMove (τ • η) (coordPoint e w)) i) c).re) (G w) 0 := by
  have h := contDiffAt_meanRadius_levelField
    (p₀ := (((0 : Fin N → ℝ), (0 : ℝ)) : (Fin N → ℝ) × ℝ)) (m := 2) hT
    (X := twoStepPoint (lineMap η) (coordTangentFst e)) (contDiffAt_twoStepPoint_fine _ _)
    (contDiffAt_twoStepPoint_noise _ _) (twoStepPoint_zero hT _ _) hi c hc
  exact exists_continuous_partialDeriv_snd (Complex.reCLM.contDiff.contDiffAt.comp _ h)
private theorem hasDerivAt_coord_component (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    {c : ℝ → Fin N → ℝ} {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) {j : ℕ}
    (ℓ : LevelTriple L n k →ₗ[ℝ] edgeFormSpace L n k j) (b : Edge L n k j) :
    HasDerivAt (fun s => (ℓ (e (c s)) : Edge L n k j → ComplexMatrix2) b)
      ((ℓ t : Edge L n k j → ComplexMatrix2) b) 0 := by apply _root_.YangMills.SharedProofs.p21944 <;> assumption
end Partials
section Multiplier
variable {L n k N : ℕ}
private theorem hasDerivAt_levelPairing_current (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    {c : ℝ → Fin N → ℝ} {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0)
    (η : LevelForms L n k) :
    HasDerivAt (fun s => levelPairing (formValues (e (c s)).2.1) (formValues η))
      (levelPairing (formValues t.2.1) (formValues η)) 0 := by
  simp only [levelPairing, formValues]
  haveI := hT.positiveEdgeFinite 0 (Nat.zero_le _)
  refine HasDerivAt.add ?_ (HasDerivAt.fun_sum fun i _ => ?_)
  · exact hasDerivAt_edgeFormPairing_re_left fun b _ => hasDerivAt_coord_component e hcd
      (baseComponent ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _) b
  · haveI := hT.positiveEdgeFinite _ i.2
    exact hasDerivAt_edgeFormPairing_re_left fun b _ => hasDerivAt_coord_component e hcd
      (noiseComponent i ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _) b
private theorem coordPoint_zero (hT : ProofInputs L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    coordPoint e 0 = unitPoint L n k := by
  have h1 := mem_fieldsIn_complex_of_mem_fieldSpace
    (const_one_mem_fieldSpace (L := L) (n := n) (k := k) (j := 0))
  have h := expMove_zero_smul (X := unitPoint L n k) h1 (0 : LevelForms L n k)
  simp only [smul_zero] at h
  simp only [coordPoint, map_zero, Prod.fst_zero]
  exact h
private theorem unitPoint_near (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField (unitPoint L n k) j b - 1) < ρ := by
  intro j hj b
  rw [levelField_unitPoint hT j hj]
  simpa using hρ0
private theorem tendsto_tangentTransport
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : MeanBehavesNearOne L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    (hcc : Tendsto c (𝓝 0) (𝓝 0))
    (hreal : ∀ᶠ s in 𝓝 (0 : ℝ), IsCompactValued (coordPoint e (c s)))
    (η : LevelForms L n k) (b : Edge L n k k) (hb : b.IsPositivelyOriented) :
    Tendsto (fun s => tangentTransport (coordPoint e (c s)) η k b) (𝓝 0)
      (𝓝 (linearTransport η k b)) := by
  obtain ⟨G, hG, hGe⟩ := exists_partial_levelField hT e η le_rfl b
  have hnear := hcc.eventually (eventually_coordPoint_near hT e hρ0)
  have hG0 : G 0 = Complex.I • linearTransport η k b := by
    have h1 := hGe.self_of_nhds
    rw [coordPoint_zero hT e] at h1
    have h2 := hasDerivAt_levelField_expMove hd hT hρ (unitPoint_isCompactValued hT)
      (unitPoint_near hT hρ0) η k le_rfl b
    rw [h1.unique h2, levelField_unitPoint hT k le_rfl, tangentTransport_unitPoint hT η k le_rfl,
      curveVelocity_one]
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), tangentTransport (coordPoint e (c s)) η k b =
      Complex.I⁻¹ • (G (c s) * (levelField (coordPoint e (c s)) k b)⁻¹) := by
    filter_upwards [hreal, hnear, hcc.eventually hGe] with s h1 h2 h3
    have hv := hasDerivAt_levelField_expMove hd hT hρ h1 h2 η k le_rfl b
    rw [h3.unique hv]
    simp only [curveVelocity, if_pos hb]
    have hdet := det_eq_one_of_mem_fieldsIn
      (mem_fieldsIn_complex_of_mem_fieldSpace (h1.2 k le_rfl)) b
    rw [mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_of_eq_one hdet), mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  obtain ⟨h1, h2⟩ := contDiffAt_coordPoint_levelField (m := 0) hT e k le_rfl
  have hinv : ContinuousAt (fun w => (levelField (coordPoint e w) k b)⁻¹) (0 : Fin N → ℝ) :=
    (contDiffAt_inv_of_eq_one (h1 b) (by rw [h2])).continuousAt
  have hl1 : Tendsto (fun s => G (c s)) (𝓝 0) (𝓝 (G 0)) := hG.tendsto.comp hcc
  have hl2 : Tendsto (fun s => (levelField (coordPoint e (c s)) k b)⁻¹) (𝓝 0) (𝓝 1) := by
    have h3 : (levelField (coordPoint e 0) k b)⁻¹ = (1 : ComplexMatrix2) := by
      simp [h2]
    have h4 := hinv.tendsto
    rw [h3] at h4
    exact h4.comp hcc
  have hl3 := (hl1.mul hl2).const_smul (Complex.I⁻¹)
  rw [mul_one, hG0, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at hl3
  exact hl3.congr' (hev.mono fun s hs => hs.symm)
private theorem adjoint_pairing_of_branch
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : MeanBehavesNearOne L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0)
    (hev : ∀ᶠ s in 𝓝 (0 : ℝ), IsCompactValued (coordPoint e (c s)) ∧
      IsTopMultiplier (coordPoint e (c s)) (e (c s)).2.1 (e (c s)).2.2)
    (η : LevelForms L n k) :
    levelPairing (formValues t.2.1) (formValues η) =
      (edgeFormPairing (t.2.2 : Edge L n k k → ComplexMatrix2) (linearTransport η k)).re := by
  have hcc : Tendsto c (𝓝 0) (𝓝 0) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hreal := hev.mono fun s hs => hs.1
  haveI := hT.positiveEdgeFinite k le_rfl
  have hnear := hcc.eventually (eventually_coordPoint_near hT e hρ0)
  have h1 : HasDerivAt (fun s => (edgeFormPairing ((e (c s)).2.2 : Edge L n k k → ComplexMatrix2)
      (tangentTransport (coordPoint e (c s)) η k)).re)
      ((edgeFormPairing (t.2.2 : Edge L n k k → ComplexMatrix2) (linearTransport η k)).re) 0 := by
    refine hasDerivAt_edgeFormPairing_re_of_zero (fun b _ => ?_) (fun b _ => ?_)
      (fun b hb => ?_)
    · simp [hc0]
    · exact hasDerivAt_coord_component e hcd (LinearMap.snd ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _) b
    · exact tendsto_tangentTransport hd hT hρ0 hρ e hc0 hcc hreal η b hb
  have h2 := hasDerivAt_levelPairing_current hT e hcd η
  refine h2.unique (h1.congr_of_eventuallyEq ?_)
  filter_upwards [hev, hnear] with s hs hn
  rw [hs.2 η, topDeriv_eq_tangentTransport hd hT hρ hs.1 hn η]
end Multiplier
section Action
variable {L n k j : ℕ}
private def holonomyVariation (U M : Edge L n k j → ComplexMatrix2) :
    List (Edge L n k j) → ComplexMatrix2
  | [] => 0
  | b :: Γ => curveVelocity U M b * PeriodicLattice.pathHolonomy U Γ +
      U b * holonomyVariation U M Γ
private theorem pathHolonomy_cons (U : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy U (b :: Γ) = U b * PeriodicLattice.pathHolonomy U Γ := by
  simp [PeriodicLattice.pathHolonomy]
private theorem bondFormSumAlong_cons (A : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong A (b :: Γ) = A b + PeriodicLattice.bondFormSumAlong A Γ := by
  simp [PeriodicLattice.bondFormSumAlong]
private theorem hasDerivAt_pathHolonomy_twist {U M : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (Γ : List (Edge L n k j)) :
    HasDerivAt (fun τ : ℝ =>
        PeriodicLattice.pathHolonomy (PeriodicLattice.expTwist (τ • M) U) Γ)
      (holonomyVariation U M Γ) 0 := by
  induction Γ with
  | nil => exact hasDerivAt_const _ _
  | cons b Γ ih =>
    simp only [pathHolonomy_cons]
    refine ((hasDerivAt_expTwist_line hU hM b).mul ih).congr_deriv ?_
    simp only [zero_smul, expTwist_zero hU, holonomyVariation]
private theorem hasDerivAt_pathHolonomy_of_curve {U : ℝ → Edge L n k j → ComplexMatrix2}
    {Ξ : Edge L n k j → ComplexMatrix2}
    (h0 : U 0 = fun _ => 1) (hU : ∀ b, HasDerivAt (fun s => U s b) (Complex.I • Ξ b) 0)
    (Γ : List (Edge L n k j)) :
    HasDerivAt (fun s => PeriodicLattice.pathHolonomy (U s) Γ)
      (Complex.I • PeriodicLattice.bondFormSumAlong Ξ Γ) 0 := by apply _root_.YangMills.SharedProofs.p5333 <;> assumption
private theorem holonomyVariation_one (M : Edge L n k j → ComplexMatrix2)
    (Γ : List (Edge L n k j)) :
    holonomyVariation (fun _ => 1) M Γ = Complex.I • PeriodicLattice.bondFormSumAlong M Γ := by
  induction Γ with
  | nil => simp [holonomyVariation, PeriodicLattice.bondFormSumAlong]
  | cons b Γ ih =>
    simp only [holonomyVariation, ih, curveVelocity_one, pathHolonomy_const_one,
      bondFormSumAlong_cons, smul_add]
    simp
private theorem exists_hasDerivAt_holonomyVariation {U : ℝ → Edge L n k j → ComplexMatrix2}
    {M Ξ : Edge L n k j → ComplexMatrix2}
    (h0 : U 0 = fun _ => 1) (hU : ∀ b, HasDerivAt (fun s => U s b) (Complex.I • Ξ b) 0)
    (Γ : List (Edge L n k j)) :
    ∃ R, HasDerivAt (fun s => holonomyVariation (U s) M Γ) R 0 ∧ ComplexMatrix2.fullTrace R =
      ComplexMatrix2.fullTrace (-(PeriodicLattice.bondFormSumAlong M Γ *
        PeriodicLattice.bondFormSumAlong Ξ Γ)) := by
  induction Γ with
  | nil =>
    refine ⟨0, hasDerivAt_const _ _, ?_⟩
    simp [PeriodicLattice.bondFormSumAlong, ComplexMatrix2.fullTrace]
  | cons b Γ ih =>
    obtain ⟨R, hR, htr⟩ := ih
    have hv : ∃ Rv, HasDerivAt (fun s => curveVelocity (U s) M b) Rv 0 ∧
        ComplexMatrix2.fullTrace Rv = ComplexMatrix2.fullTrace (-(M b * Ξ b)) := by
      by_cases hb : b.IsPositivelyOriented
      · refine ⟨(Complex.I • M b) * (Complex.I • Ξ b), ?_, ?_⟩
        · simp only [curveVelocity, if_pos hb]
          exact (hU b).const_mul _
        · simp only [ComplexMatrix2.fullTrace, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            Complex.I_mul_I, neg_smul, one_smul]
      · refine ⟨(Complex.I • Ξ b) * (Complex.I • M b), ?_, ?_⟩
        · simp only [curveVelocity, if_neg hb]
          exact (hU b).mul_const _
        · simp only [ComplexMatrix2.fullTrace, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            Complex.I_mul_I, neg_smul, one_smul]
          rw [Matrix.trace_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
    obtain ⟨Rv, hRv, hvtr⟩ := hv
    have hQ := (hRv.mul (hasDerivAt_pathHolonomy_of_curve h0 hU Γ)).add ((hU b).mul hR)
    refine ⟨_, hQ, ?_⟩
    simp only [h0, pathHolonomy_const_one, holonomyVariation_one, curveVelocity_one, mul_one,
      one_mul, bondFormSumAlong_cons]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul, add_mul, mul_add,
      Matrix.trace_neg, neg_add_rev] at hvtr htr ⊢
    rw [hvtr, htr, Matrix.trace_mul_comm (PeriodicLattice.bondFormSumAlong Ξ Γ |> fun _ => Ξ b)
      (PeriodicLattice.bondFormSumAlong M Γ)]
    ring
end Action
section Gradient
variable {L n k N : ℕ}
private theorem halfTraceRe_eq (X : ComplexMatrix2) :
    halfTraceRe X = 1 / 2 * (ComplexMatrix2.fullTrace X).re := by
  rw [halfTraceRe_apply, ComplexMatrix2.halfTrace, Complex.mul_re]
  simp
private theorem halfTraceRe_mul_comm (A B : ComplexMatrix2) :
    halfTraceRe (A * B) = halfTraceRe (B * A) := by
  rw [halfTraceRe_eq, halfTraceRe_eq, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_mul_comm]
private theorem halfTraceRe_I_smul_eq_zero {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.hermitianTraceless) : halfTraceRe (Complex.I • Z) = 0 := by
  rw [halfTraceRe_eq]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul]
  have h := hZ.2
  simp only [ComplexMatrix2.fullTrace] at h
  rw [h]
  simp
private theorem neg_halfTraceRe_I_I (A B : ComplexMatrix2) :
    -halfTraceRe (Complex.I • A * Complex.I • B) = halfTraceRe (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg,
    neg_neg]
private theorem traceDefect_eq (g : ComplexMatrix2) : traceDefect g = 1 - halfTraceRe g := rfl
private theorem hasDerivAt_traceDefect_line (ν Y : ComplexMatrix2) :
    HasDerivAt (fun τ : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (τ • ν)) * Y))
      (-halfTraceRe (Complex.I • ν * Y)) 0 := by
  simp only [traceDefect_eq]
  have h := halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_matExp_line ν).mul_const Y)
  exact h.const_sub 1
private theorem bondFormSumAlong_boundary {A : Edge L n k 0 → ComplexMatrix2}
    (hA : ∀ b, A b.opposite = -A b) (p : Face L n k 0) :
    PeriodicLattice.bondFormSumAlong A p.boundaryBonds = edgeCoboundary A p := by
  simp only [PeriodicLattice.bondFormSumAlong, PeriodicLattice.Plaquette.boundaryBonds,
    edgeCoboundary, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hA, add_zero]
  abel
private theorem hasDerivAt_plaquetteAction_twist [Fintype (Face L n k 0)]
    {U M : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) :
    HasDerivAt (fun τ : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist (τ • M) U))
      (∑ p : Face L n k 0, -halfTraceRe (holonomyVariation U M p.boundaryBonds)) 0 := by
  have e : (fun τ : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist (τ • M) U)) =
      fun τ : ℝ => ∑ p : Face L n k 0,
        (1 - halfTraceRe (PeriodicLattice.pathHolonomy
          (PeriodicLattice.expTwist (τ • M) U) p.boundaryBonds)) := by
    funext τ
    simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
      PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy, halfTraceRe_eq]
  rw [e]
  refine HasDerivAt.fun_sum fun p _ => ?_
  exact (halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_pathHolonomy_twist hU hM p.boundaryBonds)).const_sub 1
private theorem hasDerivAt_noise_term
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ}
    (hc0 : c 0 = 0) (hcc : Tendsto c (𝓝 0) (𝓝 0)) {t : LevelTriple L n k}
    (hcd : HasDerivAt c (e.symm t) 0) (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1))
    {G : (Fin N → ℝ) → ℝ} (hG : ContinuousAt G 0) {ν : ComplexMatrix2}
    (hν : ν ∈ ComplexMatrix2.hermitianTraceless) :
    HasDerivAt (fun s => G (c s) * traceDefect ((coordPoint e (c s)).noise i q) +
        (meanRadius (levelField (coordPoint e (c s)) i) q.1).re *
          -halfTraceRe (Complex.I • ν * (coordPoint e (c s)).noise i q))
      (halfTraceRe (ν * (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1)) 0 := by
  have hZ := hasDerivAt_coord_component e hcd (noiseComponent i ∘ₗ LinearMap.fst ℝ _ _) q.1
  simp only [LinearMap.comp_apply] at hZ
  set Z : ℝ → ComplexMatrix2 := fun s => (noiseComponent i (LinearMap.fst ℝ _ _ (e (c s))) :
    Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1 with hZdef
  set Z' : ComplexMatrix2 := (noiseComponent i (LinearMap.fst ℝ _ _ t) :
    Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1 with hZ'def
  have hZ'mem : Z' ∈ ComplexMatrix2.hermitianTraceless := (t.1.2 i).2.1 q.1 q.2
  have hZ0 : Z 0 = 0 := by
    simp [hZdef, hc0, noiseComponent]
  have hY : HasDerivAt (fun s => Complex.I • Z s) (Complex.I • Z') 0 := hZ.const_smul Complex.I
  have hE : HasDerivAt (fun s => ComplexMatrix2.matExp (Complex.I • Z s)) (Complex.I • Z') 0 :=
    (hd.1 univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.2 (by simp [hZ0])
  have hN : HasDerivAt (fun s => (coordPoint e (c s)).noise i q) (Complex.I • Z') 0 := by
    have h := hE.mul_const (1 : ComplexMatrix2)
    rw [mul_one] at h
    exact h
  have hN0 : (coordPoint e (c 0)).noise i q = 1 := by
    rw [hc0, coordPoint_zero hT e]
    rfl
  have h1 : HasDerivAt (fun s => traceDefect ((coordPoint e (c s)).noise i q)) 0 0 := by
    simp only [traceDefect_eq]
    have h := (halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hN).const_sub 1
    rw [halfTraceRe_I_smul_eq_zero hZ'mem, neg_zero] at h
    exact h
  have h10 : traceDefect ((coordPoint e (c 0)).noise i q) = 0 := by
    rw [hN0, traceDefect_eq, halfTraceRe_eq]
    simp [ComplexMatrix2.fullTrace]
  have h2 : HasDerivAt (fun s => -halfTraceRe (Complex.I • ν * (coordPoint e (c s)).noise i q))
      (halfTraceRe (ν * Z')) 0 := by
    have h := (halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hN.const_mul (Complex.I • ν))).neg
    rw [← neg_halfTraceRe_I_I]
    exact h
  have h20 : -halfTraceRe (Complex.I • ν * (coordPoint e (c 0)).noise i q) = 0 := by
    rw [hN0, mul_one, halfTraceRe_I_smul_eq_zero hν, neg_zero]
  have hρ : Tendsto (fun s => (meanRadius (levelField (coordPoint e (c s)) i) q.1).re)
      (𝓝 0) (𝓝 1) := by
    have h := contDiffAt_meanRadius_levelField (p₀ := (0 : Fin N → ℝ)) (m := 0) hT
      (X := twoStepPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (coordTangent e))
      (contDiffAt_twoStepPoint_fine _ _) (contDiffAt_twoStepPoint_noise _ _)
      (twoStepPoint_zero hT _ _) i.2 q.1 q.2
    simp only [twoStepPoint_zero_left hT e] at h
    have h3 := Complex.continuous_re.continuousAt.tendsto.comp h.continuousAt.tendsto
    have h4 : (meanRadius (levelField (coordPoint e 0) i) q.1).re = 1 := by
      rw [(contDiffAt_coordPoint_levelField (m := 0) hT e i i.2.le).2, (hT.atOne i i.2 q.1 q.2).2.1]
      simp
    simp only [Function.comp_def, h4] at h3
    exact h3.comp hcc
  have hg : Tendsto (fun s => G (c s)) (𝓝 0) (𝓝 (G 0)) := hG.tendsto.comp hcc
  have t1 := hasDerivAt_mul_of_left_zero h10 h1 hg
  have t2 := hasDerivAt_mul_of_left_zero h20 h2 hρ
  have t3 := t1.add t2
  have e1 : (fun s => G (c s) * traceDefect ((coordPoint e (c s)).noise i q) +
      (meanRadius (levelField (coordPoint e (c s)) i) q.1).re *
        -halfTraceRe (Complex.I • ν * (coordPoint e (c s)).noise i q)) =
      fun s => traceDefect ((coordPoint e (c s)).noise i q) * G (c s) +
        -halfTraceRe (Complex.I • ν * (coordPoint e (c s)).noise i q) *
          (meanRadius (levelField (coordPoint e (c s)) i) q.1).re := by
    funext s
    ring
  rw [e1]
  refine t3.congr_deriv ?_
  simp only [zero_mul, zero_add, mul_one]
  rfl
private theorem hessian_pairing_of_branch
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : ProofInputs L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : MeanBehavesNearOne L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) {a : ℝ}
    (hev : ∀ᶠ s in 𝓝 (0 : ℝ),
      IsLevelGradient (chainAction a) (coordPoint e (c s)) (e (c s)).2.1)
    (η : LevelForms L n k) :
    levelPairing (formValues t.2.1) (formValues η) = hessianAtIdentity a t.1 η := by
  have hcc : Tendsto c (𝓝 0) (𝓝 0) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.positiveEdgeFinite _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.faceFinite
  choose G hGc hGe using fun (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1)) =>
    exists_partial_meanRadius hT e η i.2 q.1 q.2
  let U : ℝ → Edge L n k 0 → ComplexMatrix2 := fun s => (coordPoint e (c s)).fine
  let ν : (i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2 := fun i q =>
    (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1
  let hf : ℝ → ℝ := fun s =>
    (∑ p : Face L n k 0, -halfTraceRe (holonomyVariation (U s) η.1 p.boundaryBonds)) +
    a * ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
      (G i q (c s) * traceDefect ((coordPoint e (c s)).noise i q) +
        (meanRadius (levelField (coordPoint e (c s)) i) q.1).re *
          -halfTraceRe (Complex.I • ν i q * (coordPoint e (c s)).noise i q))
  have claim1 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun τ : ℝ => chainAction a (expMove (τ • η) (coordPoint e (c s)))) (hf s) 0 := by
    have hall : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1)),
        HasDerivAt (fun τ : ℝ =>
          (meanRadius (levelField (expMove (τ • η) (coordPoint e (c s))) i) q.1).re)
          (G i q (c s)) 0 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun q =>
        hcc.eventually (hGe i q)
    filter_upwards [hall] with s hs
    have hb := coordPoint_fine_mem hT e (c s)
    have hzero := expMove_zero_smul hb η
    have e1 : (fun τ : ℝ => chainAction a (expMove (τ • η) (coordPoint e (c s)))) = fun τ : ℝ =>
        plaquetteAction L n k
          (PeriodicLattice.expTwist (τ • (η.1 : Edge L n k 0 → ComplexMatrix2)) (U s)) +
          a * ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
            (meanRadius (levelField (expMove (τ • η) (coordPoint e (c s))) i) q.1).re *
              traceDefect (ComplexMatrix2.matExp (Complex.I • (τ • ν i q)) *
                (coordPoint e (c s)).noise i q) := by
      funext τ
      simp only [chainAction, finsum_eq_sum_of_fintype]
      rfl
    rw [e1]
    refine (hasDerivAt_plaquetteAction_twist hb η.1.2.2).add (HasDerivAt.const_mul a
      (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun q _ => ?_))
    refine ((hs i q).mul
      (hasDerivAt_traceDefect_line (ν i q) ((coordPoint e (c s)).noise i q))).congr_deriv ?_
    simp only [hzero, matExp_line_zero, one_mul]
  have claim2 : HasDerivAt hf (hessianAtIdentity a t.1 η) 0 := by
    have hU0 : U 0 = fun _ => 1 := by
      show (coordPoint e (c 0)).fine = _
      rw [hc0, coordPoint_zero hT e]
      rfl
    have hUd : ∀ b, HasDerivAt (fun s => U s b)
        (Complex.I • (t.1.1 : Edge L n k 0 → ComplexMatrix2) b) 0 :=
      fun b => hasDerivAt_levelField_along_coords hd hT hρ0 hρ e hc0 hcd 0 (Nat.zero_le _) b
    choose R hR htr using fun p : Face L n k 0 =>
      exists_hasDerivAt_holonomyVariation (M := (η.1 : Edge L n k 0 → ComplexMatrix2))
        hU0 hUd p.boundaryBonds
    have hA : HasDerivAt (fun s => ∑ p : Face L n k 0,
        -halfTraceRe (holonomyVariation (U s) η.1 p.boundaryBonds))
        (∑ p : Face L n k 0, -halfTraceRe (R p)) 0 :=
      HasDerivAt.fun_sum fun p _ =>
        (halfTraceRe.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hR p)).neg
    have hB : HasDerivAt (fun s => ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
        (G i q (c s) * traceDefect ((coordPoint e (c s)).noise i q) +
          (meanRadius (levelField (coordPoint e (c s)) i) q.1).re *
            -halfTraceRe (Complex.I • ν i q * (coordPoint e (c s)).noise i q)))
        (∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
          halfTraceRe (ν i q * (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1)) 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun q _ =>
        hasDerivAt_noise_term hd hT e hc0 hcc hcd i q (hGc i q) ((η.2 i).2.1 q.1 q.2)
    refine (hA.add (hB.const_mul a)).congr_deriv ?_
    simp only [hessianAtIdentity]
    congr 1
    · have e2 : ∀ p : Face L n k 0, -halfTraceRe (R p) =
          (ComplexMatrix2.halfTrace (edgeCoboundary (t.1.1 : Edge L n k 0 → ComplexMatrix2) p *
            edgeCoboundary (η.1 : Edge L n k 0 → ComplexMatrix2) p)).re := by
        intro p
        rw [halfTraceRe_eq, htr p, bondFormSumAlong_boundary η.1.2.2,
          bondFormSumAlong_boundary t.1.1.2.2, ← halfTraceRe_apply, halfTraceRe_mul_comm,
          halfTraceRe_eq]
        simp only [ComplexMatrix2.fullTrace, Matrix.trace_neg, Complex.neg_re]
        ring
      simp only [e2]
      rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [edgeFormPairing_re_eq_sum]
      exact Finset.sum_congr rfl fun q _ => halfTraceRe_mul_comm _ _
  have h2 := hasDerivAt_levelPairing_current hT e hcd η
  refine h2.unique (claim2.congr_of_eventuallyEq ?_)
  filter_upwards [hev, claim1] with s hs1 hs2
  rw [hs1 η, leftDeriv, hs2.deriv]
end Gradient
private theorem proofInputs (hd : NormalizedMeanAtOne)
    (hCfg : Tower.LeftChartFields.Claim) (hS : Tower.FaceSums.FacesAndPairings)
    (hV : Tower.LinearMapValues.Statement) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ProofInputs L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have vertexFinite : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  have hvals := (hV L hL k).1 n hn
  refine
    { vertexFinite := vertexFinite
      positiveEdgeFinite := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      edgeFinite := fun j hj => ?_
      faceFinite := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      differentialAtOne := fun j hj B hB c hc => (hd L hL n k j hn hj B hB c hc).2.2.2.2
      smoothingMem := fun j hj B hB => ((hvals.1 j hj).1 B hB).2.2.1
      notBothPositive := fun j hj b hb => ?_
      atOne := fun j hj c hc => ?_
      leftMem := fun j hj => ((hCfg.2.2 L k j hL hj).1 n hn).1.1
      curveLogs := fun I hI => (hCfg.1 I hI).1 }
  · haveI := vertexFinite j hj
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
      simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps] using h
    have hs' : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n)
        1 ν := by
      have h := congrArg Subtype.val hν
      simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps,
        PeriodicLattice.Bond.opposite] using h
    have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
    rcases hX with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ⟨ν, hs'⟩
    · exact h ⟨μ, hs⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := hd L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc
    exact ⟨h1, h2, h3⟩
end FirstVariationProof
open FirstVariationProof in
theorem firstVariationSolvesSystem_holds
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hPA : NormalizedMeanNearOne) (hDer : NormalizedMeanAtOne)
    (hCfg : Tower.LeftChartFields.Claim) (hS : Tower.FaceSums.FacesAndPairings)
    (hV : Tower.LinearMapValues.Statement)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    FirstVariationSolvesSystem := by
  intro a _ L hL k n _ hn B t ht
  obtain ⟨N, e, c, hc0, hcd, hev⟩ := ht
  have hT : ProofInputs L n k := proofInputs hDer hCfg hS hV hA hL hn
  obtain ⟨ρ, hρ0, hρ'⟩ := hPA L hL
  have hρ : MeanBehavesNearOne L n k ρ := fun j hj V hV hN c hc => hρ' n k j hn hj V hV hN c hc
  refine ⟨?_, fun η => ?_, fun η => ?_⟩
  · refine linearTransport_top_eq hd hT hρ0 hρ e hc0 hcd B ?_
    filter_upwards [hev] with s hs
    exact hs.1.top_eq
  · refine hessian_pairing_of_branch hd hT hρ0 hρ e hc0 hcd ?_ η
    filter_upwards [hev] with s hs
    exact hs.2.1
  · refine adjoint_pairing_of_branch hd hT hρ0 hρ e hc0 hcd ?_ η
    filter_upwards [hev] with s hs
    exact ⟨hs.1.compact, hs.2.2⟩
end YangMills.Construction.RunningCouplingSlope
end
