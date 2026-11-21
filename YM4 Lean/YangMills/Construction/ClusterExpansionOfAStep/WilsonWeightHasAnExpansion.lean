import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def wilsonWeight (β : ℝ) : TorusFunctional := fun n W =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    Real.exp (-β * wilsonAction Finset.univ W)
def WilsonWeightHasExpansion : Prop :=
  ∃ C₀ : ℝ, ∀ ℓ : StepParameters, ℓ.Admissible → C₀ ≤ ℓ.derivBound → ∀ β : ℝ, ℓ.y₁ ≤ β →
    HasExpansion ℓ 0 β (wilsonWeight β)
end YangMills.Construction.TorusLumps
end
