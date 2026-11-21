import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.TrivialFieldSteps
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.FullSpace.RescaledConditions
section TrivialField
variable {L k j : ℕ} {a a' : ℝ}
theorem conjugateBy_one (X : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 X = X := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
theorem complexContourMean_const_one (hM : Averaging.IdentityFamilyMeanIsOne)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    complexContourMean L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) y x = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.complexContourMean_one <;> assumption
theorem complexSmoothingPositive_const_one (hM : Averaging.IdentityFamilyMeanIsOne)
    (c : InfiniteLattice.Link a) :
    complexSmoothingPositive L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) c = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.complexSmoothingPositive_one <;> assumption
theorem smoothingMap_const_one (hM : Averaging.IdentityFamilyMeanIsOne) :
    smoothingMap L k j (fun _ => 1) = fun _ => 1 := by
  funext c
  unfold smoothingMap complexSmoothing
  split_ifs
  · exact complexSmoothingPositive_const_one hM c
  · rw [complexSmoothingPositive_const_one hM]
    simp
theorem complexIter_const_one (hM : Averaging.IdentityFamilyMeanIsOne) (j : ℕ) :
    complexIter L k j (fun _ => 1) = fun _ => 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show smoothingMap L k j (complexIter L k j _) = _
    rw [ih]
    exact smoothingMap_const_one hM
theorem const_one_mem_fieldsValuedIn : (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈
    fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.one_mem_fieldsValuedIn <;> assumption
theorem const_one_mem_smallComplexFields (h0 : 0 < polydiscRadius L) :
    (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈ smallComplexFields L k j :=
  ⟨const_one_mem_fieldsValuedIn, fun _ => by simpa [ComplexMatrix2.operatorNorm] using h0⟩
theorem covDiff_const_one (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    covDiff (fun _ : InfiniteLattice.Link a => (1 : ComplexMatrix2)) l = vertexCoboundary l := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.covDiff_one <;> assumption
end TrivialField
section RealParts
def selfAdjointHalf (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def skewAdjointHalf (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-Complex.I / 2) • (X - X.conjTranspose)
theorem I_smul_skewAdjointHalf_add (X : ComplexMatrix2) :
    Complex.I • skewAdjointHalf X + selfAdjointHalf X = X := by
  unfold skewAdjointHalf selfAdjointHalf
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
theorem fullTrace_conjTranspose {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RescaledTrivialStepsProof.fullTrace_conjTranspose_of_traceless <;> assumption
theorem selfAdjointHalf_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    selfAdjointHalf X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · unfold selfAdjointHalf
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    simp
  · have e : ComplexMatrix2.traceless.carrier (selfAdjointHalf X) := by
      exact ComplexMatrix2.traceless.smul_mem _
        (ComplexMatrix2.traceless.add_mem h (fullTrace_conjTranspose h))
    exact e
theorem skewAdjointHalf_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    skewAdjointHalf X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · unfold skewAdjointHalf
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have e : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [e, neg_smul, ← smul_neg, neg_sub]
  · have e : ComplexMatrix2.traceless.carrier (skewAdjointHalf X) := by
      exact ComplexMatrix2.traceless.smul_mem _
        (ComplexMatrix2.traceless.sub_mem h (fullTrace_conjTranspose h))
    exact e
variable {a : ℝ}
theorem mem_complexEdgeForms_of_mem_edgeFormSpace
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ edgeFormSpace a) :
    B ∈ complexEdgeForms a :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem exists_decomp_edgeFormSpace {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) :
    ∃ B₁ ∈ edgeFormSpace a, ∃ B₂ ∈ edgeFormSpace a, B = Complex.I • B₂ + B₁ := by
  refine ⟨fun b => selfAdjointHalf (B b),
    ⟨fun b hb => selfAdjointHalf_mem (hB.1 b hb), fun b => ?_⟩,
    fun b => skewAdjointHalf (B b), ⟨fun b hb => skewAdjointHalf_mem (hB.1 b hb), fun b => ?_⟩, ?_⟩
  · simp only [hB.2 b, selfAdjointHalf, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
  · simp only [hB.2 b, skewAdjointHalf, Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg]
    congr 1
    abel
  · funext b
    exact (I_smul_skewAdjointHalf_add (B b)).symm
end RealParts
section ComplexLinear
variable {a a' : ℝ}
theorem smul_finsum_mem_linear {α : Type} {S : Set α} (hS : S.Finite) (w c : ℂ)
    {f g h : α → ComplexMatrix2} (e : ∀ x ∈ S, f x = c • g x + h x) :
    w • ∑ᶠ x ∈ S, f x = c • (w • ∑ᶠ x ∈ S, g x) + w • ∑ᶠ x ∈ S, h x := by apply _root_.YangMills.Construction.Tower.StepMapsComplexLinear.smul_finsum_smul_add <;> assumption
theorem sumAlong_smul_add (c : ℂ) (A C : InfiniteLattice.Link a → ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong (c • A + C) Γ = c • sumAlong A Γ + sumAlong C Γ := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    simp only [sumAlong, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply] at ih ⊢
    rw [ih, smul_add]
    abel
theorem contourAverage_smul_add (L : ℕ) (c : ℂ) (A C : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    _root_.YangMills.Construction.Tower.FullSpace.contourAverage L (c • A + C) y x = c • _root_.YangMills.Construction.Tower.FullSpace.contourAverage L A y x + _root_.YangMills.Construction.Tower.FullSpace.contourAverage L C y x := by
  unfold _root_.YangMills.Construction.Tower.FullSpace.contourAverage
  simp only [sumAlong_smul_add, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [smul_comm]
theorem cubeContourAverage_smul_add (L : ℕ)
    (hfin : ∀ y : InfiniteLattice.LatticePoint a, (cubeVertices L a' y).Finite) (c : ℂ)
    (A C : InfiniteLattice.Link a' → ComplexMatrix2) :
    cubeContourAverage (a := a) L (c • A + C) =
      c • cubeContourAverage L A + cubeContourAverage L C := by
  funext y
  exact smul_finsum_mem_linear (hfin y) _ c fun x _ => contourAverage_smul_add L c A C y x
theorem linearSmoothing_smul_add (L : ℕ)
    (hfin : ∀ y : InfiniteLattice.LatticePoint a, (cubeVertices L a' y).Finite) (c : ℂ)
    (A C : InfiniteLattice.Link a' → ComplexMatrix2) :
    linearSmoothing (a := a) L (c • A + C) = c • linearSmoothing L A + linearSmoothing L C := by
  funext e
  refine smul_finsum_mem_linear (hfin e.initial) _ c fun x _ => ?_
  simp only [contourAverage_smul_add, sumAlong_smul_add, smul_add, smul_sub]
  abel
theorem crossingSmoothing_smul_add (L : ℕ)
    (hfin : ∀ y : InfiniteLattice.LatticePoint a, (cubeVertices L a' y).Finite) (c : ℂ)
    (A C : InfiniteLattice.Link a' → ComplexMatrix2) :
    crossingSmoothing (a := a) L (c • A + C) =
      c • crossingSmoothing L A + crossingSmoothing L C := by
  funext e
  exact smul_finsum_mem_linear (hfin e.initial) _ c fun x _ => sumAlong_smul_add c A C _
theorem vertexCoboundary_smul_add (c : ℂ) (l l' : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    vertexCoboundary (c • l + l') = c • vertexCoboundary l + vertexCoboundary l' := by
  funext b
  simp only [vertexCoboundary, Pi.add_apply, Pi.smul_apply, smul_sub]
  abel
theorem cubeVertices_finite {L k i : ℕ} (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i < k) (y : Vertex L k (i + 1)) :
    (cubeVertices L (meshAt L k i) y).Finite := by
  have hb : BlockEqOffsetImage L k (i + 1) y :=
    (hZ L k (i + 1) hL (by omega) (by omega) hi).2.1 y
  have hcard : (cube L (meshAt L k i) y).ncard = L ^ 4 := hb.2.2.1
  have hpos : 0 < L := by have := hL.2; omega
  have hfin : (cube L (meshAt L k i) y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  exact Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn hfin
end ComplexLinear
theorem trivialStep_holds {L k i : ℕ} (hM : Averaging.IdentityFamilyMeanIsOne)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hStep : SmoothingStepAtOne)
    (hLin : CovariantStepComplexLinear)
    (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i < k) :
    TrivialStep L k i := by
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hlin := (hLin L hL k i hi _ (const_one_mem_smallComplexFields h0)).2.1
  have hreal := (hStep L hL k i hi).1
  have hfin := cubeVertices_finite (L := L) (k := k) (i := i) hZ hL hi
  have hAv : smoothingMap L k i (fun _ => 1) = fun _ => 1 := smoothingMap_const_one hM
  refine ⟨hAv, fun y x _ => complexContourMean_const_one hM y x, fun B hB => ?_, fun l _ => ?_⟩
  · obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_decomp_edgeFormSpace (a := meshAt L k i) hB
    have hl := hlin B₂ (mem_complexEdgeForms_of_mem_edgeFormSpace h₂) B₁
      (mem_complexEdgeForms_of_mem_edgeFormSpace h₁) Complex.I
    have hQ : complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1)
        (Complex.I • B₂ + B₁) = linearSmoothing (a := meshAt L k (i + 1)) L
          (Complex.I • B₂ + B₁) := by
      rw [hl.1, (hreal B₂ h₂).1, (hreal B₁ h₁).1, linearSmoothing_smul_add L hfin]
    have hN : contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) (Complex.I • B₂ + B₁) =
        cubeContourAverage (a := meshAt L k (i + 1)) L (Complex.I • B₂ + B₁) := by
      rw [hl.2, (hreal B₂ h₂).2.1, (hreal B₁ h₁).2.1, cubeContourAverage_smul_add L hfin]
    refine ⟨hQ, hN, ?_⟩
    have hC : ∀ B : Edge L k i → ComplexMatrix2, covariantSmoothingDeriv (L := L) (k := k)
        (j := i) (fun _ => 1) B = complexSmoothingDeriv (L := L) (k := k) (j := i)
          (fun _ => 1) B + vertexCoboundary
            (contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) B) := fun B => by
      unfold covariantSmoothingDeriv
      rw [hAv, covDiff_const_one]
    rw [crossingSmoothing_smul_add L hfin, ← (hreal B₂ h₂).2.2, ← (hreal B₁ h₁).2.2, hC, hC, hC,
      hl.1, hl.2, vertexCoboundary_smul_add]
    simp only [smul_add]
    abel
  · funext y
    show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x _ => by rw [complexContourMean_const_one hM, conjugateBy_one]
theorem rescaledTrivialSteps_holds (hM : Averaging.IdentityFamilyMeanIsOne)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hStep : SmoothingStepAtOne)
    (hLin : CovariantStepComplexLinear)
    (hZ : BlockStructure) : RescaledTrivialSteps := by
  intro L hL k _
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨⟨const_one_mem_fieldsValuedIn, fun j _ => ?_⟩,
    fun i hi => trivialStep_holds hM hS hStep hLin hZ hL hi⟩
  rw [complexIter_const_one hM j]
  exact const_one_mem_smallComplexFields h0
end YangMills.Construction.Tower.FullSpace.TrivialFieldSteps
end
