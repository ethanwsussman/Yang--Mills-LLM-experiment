import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open TestFunctions SeparatedTuples
namespace Rotations
open InfiniteLattice (AmbientSpace)
def SeparatedBound (M : ℝ) (σ : TupleFunctional) (k : ℕ) (d R B : ℝ) : Prop :=
  ∀ X : SepTuple, X.size = k → (∀ f ∈ X.1, ∃ x : AmbientSpace, tsupport f ⊆ closedBallR4 x R) →
    X.1.Pairwise (fun f h => ENNReal.ofReal d ≤ setDistR4 (tsupport f) (tsupport h)) →
    |σ X| ≤ B * (X.1.map (sharpNormR4 M)).prod
end Rotations
end
end YangMills.Construction
