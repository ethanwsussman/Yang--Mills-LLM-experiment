import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def unitStepSet (L m : ℕ) (j : ℤ) : Set (Site L m j) :=
  {s | ∃ μ : Fin 4, s = unitStep L m j μ ∨ s = -unitStep L m j μ}
abbrev UnitStepVec (L m : ℕ) (j : ℤ) : Type := ↥(unitStepSet L m j)
abbrev StepWord (L m : ℕ) (j : ℤ) : Type := List (UnitStepVec L m j)
def bondOfStep (z : Site L m j) (s : UnitStepVec L m j) : Bond L m j where
  source := z
  target := z + s
  isNeighbour := by
    obtain ⟨μ, h⟩ := s.2
    exact ⟨μ, by simpa using h⟩
def pathOfWord (z : Site L m j) : StepWord L m j → List (Bond L m j)
  | [] => []
  | s :: w => bondOfStep z s :: pathOfWord (z + s) w
abbrev wordHolonomy (U : Bond L m j → ComplexMatrix2) (z : Site L m j) (w : StepWord L m j) :
    ComplexMatrix2 :=
  pathHolonomy U (pathOfWord z w)
def IsPermutationOf (w' w : StepWord L m j) : Prop :=
  ∃ π : Equiv.Perm (Fin w.length), w' = List.ofFn fun i => w.get (π i)
def partialSumSites (z : Site L m j) (w : StepWord L m j) : Set (Site L m j) :=
  {x | ∃ I : Finset (Fin w.length), x = z + ∑ i ∈ I, (w.get i : Site L m j)}
end YangMills.Construction.PeriodicLattice
