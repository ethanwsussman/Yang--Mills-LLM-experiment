import YangMills.Construction.LargeFieldOperation.BlindFunctionsAndCompositesOfTheOperation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LargeFieldCourse
variable {L m K k : ℕ}
structure StateTerm (L m K k : ℕ) where
  Aux : Type
  [measurableAux : MeasurableSpace Aux]
  measure : ComplexStateMeasure L m K k Aux
attribute [instance] StateTerm.measurableAux
def StateTerm.blockMeasure (σ : StateTerm L m K k) : ComplexMeasure (BlockFields L m K k) :=
  pushToBlockFields σ.measure
def IsDensityMeasure {Y : Type} [MeasurableSpace Y] (f : LevelStateSpace L m K k Y → ℝ)
    (ν ν' : ComplexStateMeasure L m K k Y) : Prop :=
  ∀ F : LevelStateSpace L m K k Y → ℂ, Measurable F → (∃ C : ℝ, ∀ p, ‖F p‖ ≤ C) →
    ν'.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      ν.integral (fun p => (f p : ℂ) * F p) (ContinuousLinearMap.mul ℝ ℂ)
structure PartitionOfUnity (σ : StateTerm L m K k) where
  χ : LevelStateSpace L m K k σ.Aux → ℝ
  measurable_χ : Measurable χ
  bounded_χ : ∃ C : ℝ, ∀ p, |χ p| ≤ C
  onχ : ComplexStateMeasure L m K k σ.Aux
  onCompl : ComplexStateMeasure L m K k σ.Aux
  isDensity_onχ : IsDensityMeasure χ σ.measure onχ
  isDensity_onCompl : IsDensityMeasure (fun p => 1 - χ p) σ.measure onCompl
def PartitionOfUnity.termχ {σ : StateTerm L m K k} (d : PartitionOfUnity σ) : StateTerm L m K k :=
  ⟨σ.Aux, d.onχ⟩
def PartitionOfUnity.termCompl {σ : StateTerm L m K k} (d : PartitionOfUnity σ) :
    StateTerm L m K k :=
  ⟨σ.Aux, d.onCompl⟩
inductive IdentityKind where
  | faddeevPopov
  | frameAverage
  | explicitIntegral
  | changeOfVariables
  | resummation
  | indicatorToOne
structure TermIdentity (σ : StateTerm L m K k) where
  kind : IdentityKind
  result : StateTerm L m K k
  blockMeasure_eq : result.blockMeasure = σ.blockMeasure
structure TermEquivalence (σ : StateTerm L m K k) (X : Set (FourTorus L m)) where
  result : StateTerm L m K k
  agreesOff : MeasuresAgreeOffRegion X σ.blockMeasure result.blockMeasure
inductive TermOperation (σ : StateTerm L m K k) (X : Set (FourTorus L m)) where
  | partition (d : PartitionOfUnity σ)
  | identity (i : TermIdentity σ)
  | equivalence (e : TermEquivalence σ X)
structure LevelOperation (L m K k : ℕ) (B : Type) where
  source : StateTerm L m K k
  region : Set (FourTorus L m)
  op : TermOperation source region
  produced : List B
structure DroppedRegion (L m K k : ℕ) (B : Type) where
  region : Set (FourTorus L m)
  kept : List (LevelOperation L m K k B)
structure OperationState (L m K k : ℕ) (B : Type) where
  term : StateTerm L m K k
  remaining : Set (Set (FourTorus L m))
  performed : List (LevelOperation L m K k B)
  dropped : List (DroppedRegion L m K k B)
  boundary : List B
namespace OperationState
variable {B : Type}
def start (σ : StateTerm L m K k) (Q : Set (Set (FourTorus L m))) : OperationState L m K k B :=
  ⟨σ, Q, [], [], []⟩
def performedAt (s : OperationState L m K k B) (X : Set (FourTorus L m)) :
    List (LevelOperation L m K k B) :=
  open Classical in s.performed.filter fun o => decide (o.region = X)
def step (s : OperationState L m K k B) (X : Set (FourTorus L m))
    (op : TermOperation s.term X) (b : List B) (t : StateTerm L m K k) : OperationState L m K k B :=
  { s with term := t, performed := s.performed ++ [⟨s.term, X, op, b⟩] }
def dropAt (s : OperationState L m K k B) (X : Set (FourTorus L m)) : OperationState L m K k B :=
  { s with
    remaining := s.remaining \ {X}
    dropped := s.dropped ++ [⟨X, s.performedAt X⟩]
    boundary := s.boundary ++ (s.performedAt X).flatMap fun o => o.produced }
def droppedRegions (s : OperationState L m K k B) : Set (Set (FourTorus L m)) :=
  {X | ∃ d ∈ s.dropped, d.region = X}
end OperationState
structure OperationSchedule (L m K k : ℕ) (B : Type) where
  isNext : ∀ s : OperationState L m K k B, ∀ X : Set (FourTorus L m), TermOperation s.term X →
    List B → Prop
  isClassPartition : ∀ s : OperationState L m K k B, Set (FourTorus L m) →
    PartitionOfUnity s.term → Prop
  isFinished : OperationState L m K k B → Prop
end YangMills.Construction.PeriodicLattice.LargeFieldCourse
