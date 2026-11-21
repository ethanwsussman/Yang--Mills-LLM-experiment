import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FlatHessian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages
def quaternionI : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
def HessianAtTrivialFieldStatement : Prop :=
  ∀ (P : StepParameters), P.Admissible → ∀ (C : ℝ) (ρ : LocalDensity), IsCurvatureFamily P C ρ →
    ∀ (n : ℕ) [NeZero n], P.n₀ ≤ n → ∀ (y : TorusSite n) (b b' : TorusBond n),
      (∀ X X' : imaginaryQuaternions, mixedDeriv (ρ n y) (trivialField n) ![b, b'] ![X, X'] =
        inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) *
          mixedDeriv (ρ n y) (trivialField n) ![b, b'] ![quaternionI, quaternionI]) ∧
      mixedDeriv (ρ n y) (trivialField n) ![b, b'] ![quaternionI, quaternionI] =
        mixedDeriv (ρ n y) (trivialField n) ![b', b] ![quaternionI, quaternionI]
end YangMills.Construction.FlatHessian
end
