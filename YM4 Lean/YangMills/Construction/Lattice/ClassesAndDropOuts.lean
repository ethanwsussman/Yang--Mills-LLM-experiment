import YangMills.Construction.Lattice.CubesOfAStep
import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def collarStepLevel (L r : ℕ) (x : ℕ → ℝ) (k n : ℕ) : ℕ :=
  (lowerLevel L r x k + n).toNat
end ScaleLabel
section ClassIndicators
variable (a : YangMills.Construction.ParameterChoice.ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ)
  (x : ℕ → ℝ) (m' k : ℕ)
def shrunkenCore (X : Set (FourTorus a.L m)) : Set (FourTorus a.L m) :=
  layerEnlargement (nestedCubeIndex a.L a.r x K m' k) X (-6)
def firstKindIndicator (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (X : Set (FourTorus a.L m)) : ℝ :=
  CubesOfStep.densityIndicator a K x k V (shrunkenCore a K x m' k X)
def secondKindIndicator (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (X : Set (FourTorus a.L m)) : ℝ :=
  CubesOfStep.densityIndicatorCompl a K x k V (shrunkenCore a K x m' k X)
end ClassIndicators
structure LargeFieldOutcome {L m : ℕ} (D : Type) (Q : Set (Set (FourTorus L m))) where
  complementCarriers : D → Set (Set (FourTorus L m))
  classOne : Set (Set (FourTorus L m))
  classTwo : Set (Set (FourTorus L m))
  complementCarriers_subset : ∀ d, complementCarriers d ⊆ Q
  classOne_subset : classOne ⊆ Q
  classTwo_subset : classTwo ⊆ Q
  disjoint_classOne_classTwo : Disjoint classOne classTwo
  sdiff_subset_classOne_union : Q \ ⋃ d, complementCarriers d ⊆ classOne ∪ classTwo
namespace LargeFieldOutcome
variable {L m : ℕ} {D : Type} {Q : Set (Set (FourTorus L m))}
def dropped (O : LargeFieldOutcome D Q) : Set (Set (FourTorus L m)) :=
  ⋃ d, O.complementCarriers d
def largeFieldSet (O : LargeFieldOutcome D Q) : Set (Set (FourTorus L m)) :=
  O.dropped ∪ O.classTwo
def repaired (O : LargeFieldOutcome D Q) : Set (Set (FourTorus L m)) :=
  O.classOne \ O.dropped
end LargeFieldOutcome
end YangMills.Construction.PeriodicLattice
