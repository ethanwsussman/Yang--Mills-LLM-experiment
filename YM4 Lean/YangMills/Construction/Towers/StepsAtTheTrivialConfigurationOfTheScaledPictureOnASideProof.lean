import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheFreeStepProof
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneOnTheSidesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.RescaledTrivialStepsProof
open YangMills.Construction.Matrices
variable {L n k j : ℕ}
theorem edge_reverse_isPositivelyOriented {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem trivialField_mem_fieldSpace : trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem trivialField_mem_fieldsIn :
    trivialField L n k j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p502112 <;> assumption
theorem trivialField_mem_smallComplexFields (h0 : 0 < polydiscRadius L) :
    trivialField L n k j ∈ smallComplexFields L n k j :=
  ⟨trivialField_mem_fieldsIn, fun _ => by simpa using h0⟩
def hermitianComponent (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def imaginaryComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-Complex.I / 2) • (X - X.conjTranspose)
theorem I_smul_imaginaryComponent_add_hermitianComponent (X : ComplexMatrix2) :
    Complex.I • imaginaryComponent X + hermitianComponent X = X := by
  unfold imaginaryComponent hermitianComponent
  rw [smul_smul]
  have e : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
    norm_num
  rw [e, ← smul_add]
  have : X - X.conjTranspose + (X + X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]
    abel
  rw [this, smul_smul]
  norm_num
theorem fullTrace_conjTranspose_of_traceless {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.trace_conjTranspose_eq_zero <;> assumption
theorem hermitianComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermitianComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · unfold hermitianComponent
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    simp
  · have e : ComplexMatrix2.traceless.carrier (hermitianComponent X) := by
      exact ComplexMatrix2.traceless.smul_mem _
        (ComplexMatrix2.traceless.add_mem h (fullTrace_conjTranspose_of_traceless h))
    exact e
theorem imaginaryComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    imaginaryComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · unfold imaginaryComponent
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have e : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [e, neg_smul, ← smul_neg, neg_sub]
  · have e : ComplexMatrix2.traceless.carrier (imaginaryComponent X) := by
      exact ComplexMatrix2.traceless.smul_mem _
        (ComplexMatrix2.traceless.sub_mem h (fullTrace_conjTranspose_of_traceless h))
    exact e
theorem complexEdgeForms_of_edgeFormSpace {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem exists_decomposition_edgeFormSpace {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    ∃ B₁ ∈ edgeFormSpace L n k j, ∃ B₂ ∈ edgeFormSpace L n k j, B = Complex.I • B₂ + B₁ := by
  refine ⟨fun b => hermitianComponent (B b),
    ⟨fun b hb => hermitianComponent_mem (hB.1 b hb), fun b => ?_⟩,
    fun b => imaginaryComponent (B b), ⟨fun b hb => imaginaryComponent_mem (hB.1 b hb), fun b => ?_⟩, ?_⟩
  · simp only [hB.2 b, hermitianComponent, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
  · simp only [hB.2 b, imaginaryComponent, Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg]
    congr 1
    abel
  · funext b
    exact (I_smul_imaginaryComponent_add_hermitianComponent (B b)).symm
theorem smul_finsum_mem_affine {α : Type} {S : Set α} (hS : S.Finite) (w c : ℂ)
    {f g h : α → ComplexMatrix2} (e : ∀ x ∈ S, f x = c • g x + h x) :
    w • ∑ᶠ x ∈ S, f x = c • (w • ∑ᶠ x ∈ S, g x) + w • ∑ᶠ x ∈ S, h x := by apply _root_.YangMills.Construction.Tower.StepMapsComplexLinear.smul_finsum_smul_add <;> assumption
theorem bondFormSumAlong_smul_add {m : ℕ} {i : ℤ} (c : ℂ)
    (B B' : PeriodicLattice.Bond L m i → ComplexMatrix2) (Γ : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.bondFormSumAlong (c • B + B') Γ =
      c • PeriodicLattice.bondFormSumAlong B Γ + PeriodicLattice.bondFormSumAlong B' Γ := by
  unfold PeriodicLattice.bondFormSumAlong
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.sum_cons, ih, Pi.add_apply, Pi.smul_apply, smul_add]
    abel
theorem contourFormAverage_smul_add {m : ℕ} {i i' : ℤ} (c : ℂ)
    (B B' : PeriodicLattice.Bond L m i' → ComplexMatrix2)
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m i') :
    PeriodicLattice.contourFormAverage (c • B + B') y x =
      c • PeriodicLattice.contourFormAverage B y x + PeriodicLattice.contourFormAverage B' y x := by
  unfold PeriodicLattice.contourFormAverage
  simp only [bondFormSumAlong_smul_add, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [smul_comm]
theorem cubeContourAverage_smul_add {i : ℕ} (hfin : Finite (Vertex L n k i)) (c : ℂ)
    (B B' : Edge L n k i → ComplexMatrix2) :
    cubeContourAverage L n k i (c • B + B') =
      c • cubeContourAverage L n k i B + cubeContourAverage L n k i B' := by
  funext y
  exact smul_finsum_mem_affine (Set.toFinite _) _ c fun x _ => contourFormAverage_smul_add c B B' y x
theorem linearSmoothing_smul_add {i : ℕ} (hfin : Finite (Vertex L n k i)) (c : ℂ)
    (B B' : Edge L n k i → ComplexMatrix2) :
    linearSmoothing L n k i (c • B + B') =
      c • linearSmoothing L n k i B + linearSmoothing L n k i B' := by
  funext e
  refine smul_finsum_mem_affine (Set.toFinite _) _ c fun x _ => ?_
  simp only [contourFormAverage_smul_add, bondFormSumAlong_smul_add, smul_add, smul_sub]
  abel
section Step
variable {i : ℕ}
theorem complexBlockAverage_trivialField_of_pos (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage (trivialField L n k i) c = 1 := by apply _root_.YangMills.Construction.Tower.TrivialFieldSmoothingStep.complexBlockAverageStep_trivial <;> assumption
theorem complexBlockAverageStep_trivialField (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k) :
    PeriodicLattice.complexBlockAverageStep i (trivialField L n k i) =
      trivialField L n k (i + 1) := by
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact complexBlockAverage_trivialField_of_pos hH hT hBlk hL hn hi hc
  · have hr := edge_reverse_isPositivelyOriented hc
    have h := complexBlockAverage_trivialField_of_pos hH hT hBlk hL hn hi hr
    unfold PeriodicLattice.complexBlockAverage at h
    rw [if_pos hr] at h
    show PeriodicLattice.complexBlockAverage _ c = 1
    unfold PeriodicLattice.complexBlockAverage
    rw [if_neg hc, h, inv_one]
theorem complexMeanContourHolonomy_trivialField (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (trivialField L n k i) y x = 1 := by apply _root_.YangMills.Construction.Tower.TrivialFieldSmoothingStep.complexMeanContourHolonomy_trivial <;> assumption
theorem covDiff_trivialField (l : Vertex L n k j → ComplexMatrix2) :
    covDiff (trivialField L n k j) l = vertexCoboundary l := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.covDiff_trivialField <;> assumption
theorem trivialStep (hT : TrivialFieldAtStep)
    (hStep : TrivialFieldSmoothingStep.Statement)
    (hLin : StepMapsComplexLinear.Claim)
    (hH : LevelwiseMeans.LevelwiseMeansHold) (hBlk : BlockStructure)
    (hS : SmoothingNearIdentity)
    (hF : BondSetFields.ProductStructureHolds)
    (hM : TwoLevelMaps.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k) :
    RescaledConditions.TrivialStep L n k i := by
  have hT' := hT L n k i hL hn hi
  have hS' := hStep L hL n k i hn hi
  have hone := complexBlockAverageStep_trivialField hH hT hBlk hL hn hi
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hlin := hLin L hL n k i hn hi _ (trivialField_mem_smallComplexFields h0)
  have hrel := ((hM L hL k (by omega)).1 n hn).1 i hi
  have hbonds : Finite (Edge L n k i) :=
    Set.finite_univ_iff.1 ((hF L hL k i hi.le).1 n hn).2.1
  have hsites : Finite (Vertex L n k i) :=
    Finite.of_injective
      (fun x : Vertex L n k i => (PeriodicLattice.Bond.forwardFrom x 0 : Edge L n k i))
      fun x x' h => congrArg PeriodicLattice.Bond.source h
  have hQ : ∀ B ∈ complexEdgeForms L n k i,
      complexSmoothingDeriv (trivialField L n k i) B = linearSmoothing L n k i B := by
    intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_decomposition_edgeFormSpace hB
    rw [(hlin.2.1 B₂ (complexEdgeForms_of_edgeFormSpace h₂) B₁
        (complexEdgeForms_of_edgeFormSpace h₁) Complex.I).1,
      (hS'.1 B₂ h₂).1, (hS'.1 B₁ h₁).1, linearSmoothing_smul_add hsites]
  have hN : ∀ B ∈ complexEdgeForms L n k i,
      contourLogDrift (trivialField L n k i) B = cubeContourAverage L n k i B := by
    intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_decomposition_edgeFormSpace hB
    rw [(hlin.2.1 B₂ (complexEdgeForms_of_edgeFormSpace h₂) B₁
        (complexEdgeForms_of_edgeFormSpace h₁) Complex.I).2,
      (hS'.1 B₂ h₂).2.1, (hS'.1 B₁ h₁).2.1, cubeContourAverage_smul_add hsites]
  refine ⟨hone, fun y x hx => complexMeanContourHolonomy_trivialField hH hT hL hn hi y hx,
    hT'.2.1, hT'.1, fun B hB => ⟨hQ B hB, hN B hB, ?_⟩, fun l _ => ?_⟩
  · unfold covariantSmoothingDeriv
    rw [hQ B hB, hN B hB, hone, covDiff_trivialField, hrel.linearSmoothing_eq B hB,
      sub_add_cancel]
  · funext y
    unfold adjointCubeAverage vertexSmoothing
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [complexMeanContourHolonomy_trivialField hH hT hL hn hi y hx]
    simp [ComplexMatrix2.conjugateBy]
end Step
theorem rescaledTrivialSteps (hT : TrivialFieldAtStep)
    (hStep : TrivialFieldSmoothingStep.Statement)
    (hLin : StepMapsComplexLinear.Claim)
    (hH : LevelwiseMeans.LevelwiseMeansHold) (hBlk : BlockStructure)
    (hS : SmoothingNearIdentity)
    (hF : BondSetFields.ProductStructureHolds)
    (hM : TwoLevelMaps.Statement) : RescaledTrivialSteps := by
  intro L hL k hk n hn
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hfield : ∀ j, j ≤ k →
      PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) = trivialField L n k j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      show PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.complexBlockFieldAtLevel j _) = _
      rw [ih (by omega)]
      exact complexBlockAverageStep_trivialField hH hT hBlk hL hn (by omega)
  refine ⟨⟨trivialField_mem_fieldsIn, fun j hj => ?_⟩, fun i hi =>
    trivialStep hT hStep hLin hH hBlk hS hF hM hL hn hi⟩
  rw [hfield j hj.le]
  exact trivialField_mem_smallComplexFields h0
end YangMills.Construction.Tower.RescaledTrivialStepsProof
end
