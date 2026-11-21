import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OffDiagonalTensors
def Statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      tensorProdComplex X.1 ∈
        (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ))) ∧
    ∀ φ ∈ (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)), ∀ p : ℕ,
      derivSupNorm p φ < ⊤
end YangMills.Construction.TestSpaces.OffDiagonalTensors
end
