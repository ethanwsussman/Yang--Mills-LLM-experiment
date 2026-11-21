import YangMills.Construction.Continuum.SaturatedDenseFamilyOfTheRationalBoxes
import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Continuum.SeparatedFourTuples AmbientPoints
namespace CanonicalDecomposition
def separatingTuples (s : Conventions.StandingParameters) : Set (SepTuple s) :=
  {nilSepTuple s} ∪
    {A | 1 ≤ tupleLength A ∧ ∀ i, tupleComponents A i ∈ ⋃ Q, Continuum.RationalBoxes.chosenSaturatedFamily s Q}
def HasSupportApprox (s : Conventions.StandingParameters) (M : ℝ) (T : Set (SepTuple s)) : Prop :=
  ∀ A : SepTuple s, 1 ≤ tupleLength A →
    ∀ U : Fin (tupleLength A) → Set (EuclideanFour s), (∀ i, IsOpen (U i)) →
      (∀ i, tsupport (tupleComponents A i) ⊆ U i) →
      ∃ B : ℕ → SepTupleLen s (tupleLength A), (∀ n, ofFixedLength (B n) ∈ T) ∧
        (∀ n i, tsupport ((B n).1 i) ⊆ U i) ∧
        ∀ i, Tendsto (fun n => TestFunctions.sharpNormR4 M ((B n).1 i - tupleComponents A i)) atTop (𝓝 0)
end CanonicalDecomposition
end YangMills.Construction
