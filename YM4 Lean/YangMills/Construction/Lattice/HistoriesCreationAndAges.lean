import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.ClassesAndDropOuts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice
namespace ScaleLabel
variable {L m K m' : ℕ} {c : ℕ → ℕ}
def initial : ScaleLabel L m K m' c 0 where
  atScale := fun _ => ⟨∅, ∅, ∅⟩
  level_le := Nat.zero_le K
  domain_isUnion := fun j => absurd j.2.1 (by have := j.2.2; omega)
  smallFieldRegion_isUnion := fun j => absurd j.2.1 (by have := j.2.2; omega)
  smallFieldRegion_subset_domain := fun j => absurd j.2.1 (by have := j.2.2; omega)
  succ_domain_subset := fun j => absurd j.2.1 (by have := j.2.2; omega)
  markedSet_subset := fun j => absurd j.2.1 (by have := j.2.2; omega)
  markedSet_empty_or_union := fun j => absurd j.2.1 (by have := j.2.2; omega)
end ScaleLabel
namespace CubesOfStep
variable (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ)
def lastScale (k : ℕ) : ScaleIndex (k + 1) := ⟨k + 1, by simp⟩
structure StepTrace (k : ℕ) where
  densityRegion : Set (FourTorus c.L m)
  plaquetteRegion : Set (FourTorus c.L m)
  fluctuationRegion : Set (FourTorus c.L m)
  outcome : ExpansionOutcome c.L m K k
  label : LabelAtLevel c m K x (k + 1)
  densityRegion_eq_empty : k ≠ 0 → densityRegion = ∅
structure OperationTrace (D : Type) (k : ℕ) where
  actedOn : Set (Set (FourTorus c.L m))
  outcome : LargeFieldOutcome D actedOn
  label : LabelAtLevel c m K x k
inductive LabelHistory (D : ℕ → Type) : ℕ → Type
  | initial : LabelHistory D 0
  | extend {k : ℕ} (h : LabelHistory D k) (s : StepTrace c m K x k)
      (o : OperationTrace c m K x (D (k + 1)) (k + 1)) : LabelHistory D (k + 1)
variable {c m K x} {D : ℕ → Type}
def LabelHistory.finalLabel : ∀ {k : ℕ}, LabelHistory c m K x D k → LabelAtLevel c m K x k
  | _, .initial => ScaleLabel.initial
  | _, .extend _ _ o => o.label
def StepTrace.hullP : ∀ {k : ℕ}, StepTrace c m K x k → Set (FourTorus c.L m)
  | 0, s => coarseCubeHull c K x 0 s.densityRegion ∪ coarseCubeHull c K x 0 s.plaquetteRegion
  | k + 1, s => coarseCubeHull c K x (k + 1) s.plaquetteRegion
def StepTrace.hullQ {k : ℕ} (s : StepTrace c m K x k) : Set (FourTorus c.L m) :=
  coarseCubeHull c K x k s.fluctuationRegion
def StepTrace.domain {k : ℕ} (s : StepTrace c m K x k) : Set (FourTorus c.L m) :=
  (s.label.atScale (lastScale k)).domain
def StepTrace.stepData {k : ℕ} (S : LabelAtLevel c m K x k) (s : StepTrace c m K x k) :
    StepData c.L m K k :=
  ⟨S.domainSeq, s.domain, fun _ _ => 1, fun _ => 1, fun _ => 1⟩
def StepTrace.creationCubes {k : ℕ} (S : LabelAtLevel c m K x k) (s : StepTrace c m K x k) :
    Set (FourTorus c.L m) :=
  CubesOfStep.creationRegion c x (s.stepData S) s.hullP s.hullQ s.outcome
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
end
