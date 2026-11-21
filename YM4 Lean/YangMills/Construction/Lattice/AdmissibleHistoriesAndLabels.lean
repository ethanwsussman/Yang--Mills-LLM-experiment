import YangMills.Construction.Lattice.ListOfTheOperationsOfALevel
import YangMills.Construction.Lattice.MovesThatCutOutTheSmallFieldDomain
import YangMills.Construction.Lattice.NewLabelBackgroundAndCouplingOfALargeFieldOperation
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
open OperationList CentralBlock
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ)
inductive LevelDecomposition (t : ℕ) : Type
  | leaveAt (e : Lattice.LargeFieldDecomposition) (he : e ≠ .testAtTheLastShell)
      (hp : Slot.split e ∈ operationSlots (delayAt c x t))
  | shellUnion (P : Set (FourTorus c.L m)) (hP : P.Nonempty)
abbrev DecomposedHistory (k : ℕ) : Type := LabelHistory c m K x (LevelDecomposition c m x) k
abbrev DecomposedTerm (k : ℕ) : Type := TermOfStep c m K x (LevelDecomposition c m x) k
abbrev DecomposedOperation (k : ℕ) : Type :=
  OperationTrace c m K x (LevelDecomposition c m x (k + 1)) (k + 1)
variable {c m K x}
namespace StepTrace
def HasStepSets : ∀ {k : ℕ}, LabelAtLevel c m K x k → StepTrace c m K x k → Prop
  | 0, _, s =>
    s.densityRegion ∈ initialDensityOutcomes c K x ∧
      s.plaquetteRegion ∈
        unionsOfTestCubes c K x 0 (initialPlaquetteRegionOf c K x s.densityRegion) ∧
      s.fluctuationRegion ∈ unionsOfTestCubes c K x 0 (fluctuationTestRegion c K x 0
        (initialGaugeRegionOf c K x s.densityRegion s.plaquetteRegion)) ∧
      s.domain = smallFieldRegion c K x 0
        (initialGaugeRegionOf c K x s.densityRegion s.plaquetteRegion) s.fluctuationRegion
  | k + 1, S, s =>
    s.plaquetteRegion ∈
        unionsOfTestCubes c K x (k + 1) (plaquetteTestRegion c K x (k + 1) (incomingRegion c K x S)) ∧
      s.fluctuationRegion ∈ unionsOfTestCubes c K x (k + 1) (fluctuationTestRegion c K x (k + 1)
        (stepGaugeFixedRegion c K x (k + 1) s.plaquetteRegion (incomingRegion c K x S))) ∧
      s.domain = smallFieldRegion c K x (k + 1)
        (stepGaugeFixedRegion c K x (k + 1) s.plaquetteRegion (incomingRegion c K x S))
        s.fluctuationRegion
structure IsStepOf {k : ℕ} (S : LabelAtLevel c m K x k) (s : StepTrace c m K x k) : Prop where
  sets : s.HasStepSets S
  admissible : IsAdmissible c x (s.stepData S) s.outcome
  succLabel : IsSuccLabel c x (s.stepData S) S s.label s.outcome
end StepTrace
namespace OperationTrace
variable {k : ℕ} (o : DecomposedOperation c m K x k)
def survivorsAtOuterShell : Set (Set (FourTorus c.L m)) :=
  {X | X ∈ o.actedOn ∧ ∀ (e : Lattice.LargeFieldDecomposition) he hp, e ≠ .testOfTheDenominator →
    X ∉ o.outcome.complementCarriers (.leaveAt e he hp)}
def survivors : Set (Set (FourTorus c.L m)) := o.actedOn \ o.outcome.dropped
def outerShellUnions (S : LabelAtLevel c m K x (k + 1)) (Q : Set (Set (FourTorus c.L m)))
    (X : Set (FourTorus c.L m)) : Set (Set (FourTorus c.L m)) :=
  {P | ∃ C ⊆ partitionCubesIn (outerShellIndex c K x (k + 1))
    (CentralBlock.outerShell c S Q X), P = ⋃₀ C}
structure IsOperationOn (σ : DecomposedTerm c m K x k) (𝒬 : Set (Set (FourTorus c.L m))) : Prop where
  acted_eq : o.actedOn = 𝒬
  disjoint_carriers : Pairwise (Function.onFun Disjoint o.outcome.complementCarriers)
  classes_union_eq : o.outcome.classOne ∪ o.outcome.classTwo = o.survivors
  outerShell_mem : ∀ P hP, ∀ X ∈ o.outcome.complementCarriers (.shellUnion P hP),
    P ∈ outerShellUnions σ.resultLabel o.survivorsAtOuterShell X
  label_of_empty : o.actedOn = ∅ → o.label = σ.resultLabel
  label_of_nonempty : o.actedOn.Nonempty →
    ScaleLabel.IsOutputLabelOf c.r x σ.resultLabel o.label o.survivors o.outcome.classTwo
end OperationTrace
namespace LabelHistory
def IsGeneratedWith (𝒬 : ∀ k, DecomposedTerm c m K x k → Set (Set (FourTorus c.L m))) :
    ∀ {k : ℕ}, DecomposedHistory c m K x k → Prop
  | _, .initial => True
  | k + 1, .extend h s o =>
    h.IsGeneratedWith 𝒬 ∧ s.IsStepOf h.finalLabel ∧
      OperationTrace.IsOperationOn o ⟨h, s⟩ (𝒬 k ⟨h, s⟩)
end LabelHistory
end YangMills.Construction.PeriodicLattice.CubesOfStep
