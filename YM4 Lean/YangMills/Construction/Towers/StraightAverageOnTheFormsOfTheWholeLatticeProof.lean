import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.StraightAverageOnTheFormsOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StraightSmoothing
section Levels
variable {L k : ℕ}
theorem smoothingMap_const_one (hmean : Averaging.IdentityFamilyMeanIsOne) (j : ℕ) :
    smoothingMap L k j (fun _ => (1 : Matrices.ComplexMatrix2)) = fun _ => 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantIteratesAtIdentityProof.smoothingMap_const_one <;> assumption
theorem complexIter_const_one (hmean : Averaging.IdentityFamilyMeanIsOne) :
    ∀ j, complexIter L k j (fun _ => (1 : Matrices.ComplexMatrix2)) = fun _ => 1
  | 0 => rfl
  | j + 1 => by
    simp only [complexIter]
    rw [complexIter_const_one hmean j]
    exact smoothingMap_const_one hmean j
theorem const_one_mem_fieldsValuedIn (j : ℕ) :
    (fun _ => (1 : Matrices.ComplexMatrix2)) ∈
      fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.one_mem_fieldsValuedIn <;> assumption
end Levels
section RealParts
variable {a : ℝ}
theorem mem_complexEdgeForms_of_mem {A : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hA : A ∈ edgeFormSpace a) : A ∈ complexEdgeForms a :=
  ⟨fun e he => (hA.1 e he).2, hA.2⟩
theorem hermitianPart_mem_hermitianTraceless {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    (1 / 2 : ℂ) • (X + X.conjTranspose) ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
  have ht : Matrices.ComplexMatrix2.fullTrace X = 0 := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    simp
  · simp only [Matrices.ComplexMatrix2.fullTrace] at ht ⊢
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, ht]
    simp
theorem exists_real_imaginary_parts {B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) :
    ∃ A ∈ edgeFormSpace a, ∃ D ∈ edgeFormSpace a, B = Complex.I • D + A := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldSteps.exists_decomp_edgeFormSpace <;> assumption
end RealParts
section Linearity
variable {a a' : ℝ}
theorem crossingSmoothing_smul_add (L : ℕ)
    (hfin : ∀ y : InfiniteLattice.LatticePoint a, (cubeVertices L a' y).Finite) (c : ℂ)
    (A C : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    crossingSmoothing (a := a) L (c • A + C) =
      c • crossingSmoothing L A + crossingSmoothing L C := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldSteps.crossingSmoothing_smul_add <;> assumption
theorem covDiff_const_one_smul_add (c : ℂ)
    (u v : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    covDiff (fun _ => (1 : Matrices.ComplexMatrix2)) (c • u + v) =
      c • covDiff (fun _ => (1 : Matrices.ComplexMatrix2)) u +
        covDiff (fun _ => (1 : Matrices.ComplexMatrix2)) v := by
  have hconj : ∀ X : Matrices.ComplexMatrix2, Matrices.ComplexMatrix2.conjugateBy 1 X = X :=
    fun X => by simp [Matrices.ComplexMatrix2.conjugateBy]
  funext e
  simp only [covDiff, extendOddly, Pi.add_apply, Pi.smul_apply, hconj]
  split_ifs <;> module
theorem cubeVertices_finite {L k i : ℕ} (hcube : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i < k) (y : Vertex L k (i + 1)) :
    (cubeVertices L (meshAt L k i) y).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldSteps.cubeVertices_finite <;> assumption
end Linearity
section Iteration
variable {L k : ℕ}
theorem crossingSmoothing_mem_edgeFormSpace {i : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {X : Edge L k i → Matrices.ComplexMatrix2} (hX : X ∈ edgeFormSpace (meshAt L k i))
    (h₁ : linearSmoothing (a := meshAt L k (i + 1)) L X =
      crossingSmoothing (a := meshAt L k (i + 1)) L X -
        vertexCoboundary (cubeContourAverage (a := meshAt L k (i + 1)) L X))
    (h₂ : complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) X =
      linearSmoothing (a := meshAt L k (i + 1)) L X) :
    crossingSmoothing (a := meshAt L k (i + 1)) L X ∈ edgeFormSpace (meshAt L k (i + 1)) := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantIteratesAtIdentityProof.crossingSmoothing_mem <;> assumption
variable (hS : SmoothingStepAtOne) (hW : CovariantStepComplexLinear)
  (hR : TrivialLinearization.OneStepIdentitiesHold) (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
  (hZ : BlockStructure) (hM : Averaging.IdentityFamilyMeanIsOne)
include hS hR in
theorem crossingSmoothing_step_mem_edgeFormSpace (hL : Conventions.IsAdmissibleBlockingFactor L)
    {i : ℕ} (hi : i < k) {X : Edge L k i → Matrices.ComplexMatrix2}
    (hX : X ∈ edgeFormSpace (meshAt L k i)) :
    crossingSmoothing (a := meshAt L k (i + 1)) L X ∈ edgeFormSpace (meshAt L k (i + 1)) :=
  crossingSmoothing_mem_edgeFormSpace hL hX ((hR L hL k i hi).1 _ hX) ((hS L hL k i hi).1 _ hX).1
include hS hR hZ in
theorem crossingSmoothing_step_mem_complexEdgeForms
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {X : Edge L k i → Matrices.ComplexMatrix2} (hX : X ∈ complexEdgeForms (meshAt L k i)) :
    crossingSmoothing (a := meshAt L k (i + 1)) L X ∈ complexEdgeForms (meshAt L k (i + 1)) := by
  obtain ⟨A, hA', D, hD, rfl⟩ := exists_real_imaginary_parts hX
  rw [crossingSmoothing_smul_add L fun y => cubeVertices_finite hZ hL hi y]
  exact (complexEdgeForms _).add_mem
    ((complexEdgeForms _).smul_mem _
      (mem_complexEdgeForms_of_mem (crossingSmoothing_step_mem_edgeFormSpace hS hR hL hi hD)))
    (mem_complexEdgeForms_of_mem (crossingSmoothing_step_mem_edgeFormSpace hS hR hL hi hA'))
include hS hW hA hZ hM in
theorem covariantSmoothingDeriv_const_one_eq (hL : Conventions.IsAdmissibleBlockingFactor L)
    {i : ℕ} (hi : i < k) {X : Edge L k i → Matrices.ComplexMatrix2}
    (hX : X ∈ complexEdgeForms (meshAt L k i)) :
    covariantSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) X =
      crossingSmoothing (a := meshAt L k (i + 1)) L X := by
  obtain ⟨A, hA', D, hD, rfl⟩ := exists_real_imaginary_parts hX
  have hρ : 0 < polydiscRadius L := (hA.1 L hL).2.2.pos
  have hone : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ smallComplexFields L k i :=
    ⟨const_one_mem_fieldsValuedIn i,
     fun _ => by simpa [Matrices.ComplexMatrix2.operatorNorm] using hρ⟩
  obtain ⟨-, hlin, -, -⟩ := hW L hL k i hi _ hone
  obtain ⟨h₁, h₂⟩ := hlin D (mem_complexEdgeForms_of_mem hD) A (mem_complexEdgeForms_of_mem hA')
    Complex.I
  have hsplit : ∀ Y : Edge L k i → Matrices.ComplexMatrix2,
      covariantSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) Y =
        complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) Y +
          covDiff (fun _ => (1 : Matrices.ComplexMatrix2))
            (contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) Y) := fun Y => by
    rw [covariantSmoothingDeriv, smoothingMap_const_one hM i]
  have hD' := ((hS L hL k i hi).1 D hD).2.2
  have hA'' := ((hS L hL k i hi).1 A hA').2.2
  rw [crossingSmoothing_smul_add L fun y => cubeVertices_finite hZ hL hi y, ← hD', ← hA'',
    hsplit, hsplit, hsplit, h₁, h₂, covDiff_const_one_smul_add, smul_add]
  abel
include hZ in
theorem crossingSmoothingIter_smul_add (hL : Conventions.IsAdmissibleBlockingFactor L) (c : ℂ)
    (B B' : Edge L k 0 → Matrices.ComplexMatrix2) :
    ∀ m, m ≤ k → crossingSmoothingIter L k m (c • B + B') =
      c • crossingSmoothingIter L k m B + crossingSmoothingIter L k m B' := by
  intro m
  induction m with
  | zero => exact fun _ => rfl
  | succ m ih =>
    intro hm
    change crossingSmoothing (a := meshAt L k (m + 1)) L
        (crossingSmoothingIter L k m (c • B + B')) =
      c • crossingSmoothing (a := meshAt L k (m + 1)) L (crossingSmoothingIter L k m B) +
        crossingSmoothing (a := meshAt L k (m + 1)) L (crossingSmoothingIter L k m B')
    rw [ih (by omega), crossingSmoothing_smul_add L fun y => cubeVertices_finite hZ hL (by omega) y]
include hS hR in
theorem crossingSmoothingIter_mem_edgeFormSpace (hL : Conventions.IsAdmissibleBlockingFactor L)
    {B : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k 0)) :
    ∀ m, m ≤ k → crossingSmoothingIter L k m B ∈ edgeFormSpace (meshAt L k m) := by
  intro m
  induction m with
  | zero => exact fun _ => hB
  | succ m ih =>
    exact fun hm => crossingSmoothing_step_mem_edgeFormSpace hS hR hL (by omega) (ih (by omega))
include hS hR hZ in
theorem crossingSmoothingIter_mem_complexEdgeForms
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {B : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ m, m ≤ k → crossingSmoothingIter L k m B ∈ complexEdgeForms (meshAt L k m) := by
  intro m
  induction m with
  | zero => exact fun _ => hB
  | succ m ih =>
    exact fun hm =>
      crossingSmoothing_step_mem_complexEdgeForms hS hR hZ hL (by omega) (ih (by omega))
include hS hW hR hA hZ hM in
theorem iterCovariantDeriv_const_one_eq (hL : Conventions.IsAdmissibleBlockingFactor L)
    {B : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ m, m ≤ k → iterCovariantDeriv L k (fun _ => 1) m B = crossingSmoothingIter L k m B := by
  intro m
  induction m with
  | zero => exact fun _ => rfl
  | succ m ih =>
    intro hm
    change covariantSmoothingDeriv (complexIter L k m fun _ => 1)
      (iterCovariantDeriv L k (fun _ => 1) m B) = _
    rw [complexIter_const_one hM m, ih (by omega)]
    exact covariantSmoothingDeriv_const_one_eq hS hW hA hZ hM hL (by omega)
      (crossingSmoothingIter_mem_complexEdgeForms hS hR hZ hL hB m (by omega))
end Iteration
theorem straightSmoothingOnForms_holds (hS : SmoothingStepAtOne)
    (hW : CovariantStepComplexLinear) (hR : TrivialLinearization.OneStepIdentitiesHold)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity) (hZ : BlockStructure)
    (hM : Averaging.IdentityFamilyMeanIsOne) :
    StraightSmoothingOnForms := by
  intro L hL k m _ hm
  exact ⟨fun B hB => crossingSmoothingIter_mem_complexEdgeForms hS hR hZ hL hB m hm,
    fun B hB => crossingSmoothingIter_mem_edgeFormSpace hS hR hL hB m hm,
    fun B _ B' _ c => crossingSmoothingIter_smul_add hZ hL c B B' m hm,
    fun B hB => iterCovariantDeriv_const_one_eq hS hW hR hA hZ hM hL hB m hm⟩
end YangMills.Construction.Tower.FullSpace.StraightSmoothing
end
