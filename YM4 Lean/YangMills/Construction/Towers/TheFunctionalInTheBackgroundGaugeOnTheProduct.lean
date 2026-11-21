import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L m k : ℕ}
abbrev SourceEdge (L m k : ℕ) : Type := PositiveEdge L m k 0 ⊕ PositiveEdge L m k k
abbrev ProductPoint (L m k : ℕ) : Type :=
  PositiveEdge L m k 0 ⊕ SourceEdge L m k → Matrices.ComplexMatrix2
def fieldOfProductPoint (x : ProductPoint L m k) : Edge L m k 0 → Matrices.ComplexMatrix2 :=
  fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent x)
def sourceOfProductPoint (x : ProductPoint L m k) : Edge L m k 0 → Matrices.ComplexMatrix2 :=
  edgeFormOfPositiveValues fun e => Matrices.GroupLieProduct.Subspaces.algebraComponent x (.inl e)
def multiplierOfProductPoint (x : ProductPoint L m k) : Edge L m k k → Matrices.ComplexMatrix2 :=
  edgeFormOfPositiveValues fun e => Matrices.GroupLieProduct.Subspaces.algebraComponent x (.inr e)
def identityProductPoint (L m k : ℕ) : ProductPoint L m k :=
  Matrices.GroupLieProduct.Subspaces.ofParts (fun _ => 1) 0
def BackgroundFunctionalDefinedAt (x : ProductPoint L m k) : Prop :=
  ∃ (A : edgeFormSpace L m k 0) (ν : edgeFormSpace L m k k),
    (A : Edge L m k 0 → Matrices.ComplexMatrix2) = sourceOfProductPoint x ∧
      (ν : Edge L m k k → Matrices.ComplexMatrix2) = multiplierOfProductPoint x ∧
      BackgroundFunctionalWellDefined (fieldOfProductPoint x) A ν
def backgroundFunctionalAt (x : ProductPoint L m k) : ℝ :=
  open Classical in
  if hx : sourceOfProductPoint x ∈ edgeFormSpace L m k 0 ∧
      multiplierOfProductPoint x ∈ edgeFormSpace L m k k then
    backgroundFunctional (fieldOfProductPoint x) ⟨_, hx.1⟩ ⟨_, hx.2⟩
  else 0
def BackgroundFunctionalAnalyticNearIdentity (L m k : ℕ) : Prop :=
  ∃ (_ : Fintype (PositiveEdge L m k 0)) (_ : Fintype (PositiveEdge L m k k))
    (N : Set (ProductPoint L m k)),
    identityProductPoint L m k ∈ N ∧ (∀ x ∈ N, BackgroundFunctionalDefinedAt x) ∧
      Matrices.GroupLieProduct.Subspaces.IsSubspaceAnalyticToCoords (R := PositiveEdge L m k 0)
        (S := SourceEdge L m k) (l := 1)
        (Matrices.GroupLieProduct.hermitianTracelessFunctions (SourceEdge L m k)) N
        fun x _ => (backgroundFunctionalAt x : ℂ)
def BackgroundFunctionalGaugeInvariant (g : Vertex L m k 0 → Matrices.ComplexMatrix2)
    (U : Edge L m k 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ (A : edgeFormSpace L m k 0) (ν : edgeFormSpace L m k k), BackgroundFunctionalWellDefined U A ν →
    ∃ (A' : edgeFormSpace L m k 0) (ν' : edgeFormSpace L m k k),
      (A' : Edge L m k 0 → Matrices.ComplexMatrix2) = adjointForm g A ∧
        (ν' : Edge L m k k → Matrices.ComplexMatrix2) = adjointForm (restrictVertexFunction k g) ν ∧
        BackgroundFunctionalWellDefined (PeriodicLattice.gaugeTransform g U) A' ν' ∧
        backgroundFunctional (PeriodicLattice.gaugeTransform g U) A' ν' =
          backgroundFunctional U A ν
def HasBackgroundFunctionalFormula (L m k : ℕ) (W : Edge L m k k → Matrices.ComplexMatrix2) : Prop :=
  LogTotalNormaliserWellDefined W ∧
    ∃ (A : edgeFormSpace L m k 0) (ν : edgeFormSpace L m k k),
      (A : Edge L m k 0 → Matrices.ComplexMatrix2) =
          leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
            (chosenProlongComp L m k k W) ∧
        (ν : Edge L m k k → Matrices.ComplexMatrix2) = (chosenCriticalBranch L m k).energyGradient k W ∧
        BackgroundFunctionalWellDefined (chosenProlongComp L m k k W) A ν ∧
        logTotalNormaliserRatio L m k W =
          backgroundFunctional (chosenProlongComp L m k k W) A ν -
            backgroundFunctional (trivialField L m k 0) 0 0
end YangMills.Construction.Tower
end
