import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import YangMills.Construction.ResponseInTheExpansion.TorusBoundOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses
def separationLevelScaleStatement : Prop :=
  ∀ ℓ : StepParameters, AdmissibleStep ℓ → ∀ g : ℝ, 0 < g → ℓ.y₁ ≤ (g ^ 2)⁻¹ → ∀ k : ℕ, 2 ≤ k →
    ∀ R d : ℝ, 0 < d →
    ∃ C : ℝ, ∀ P : LevelData k, P.Admissible ℓ.side R d → ∀ β : ℝ, couplingWindowTop ℓ g ≤ β →
      IsFirstPassage ℓ (couplingWindowTop ℓ g) β P.windowLevel →
      (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - (P.separationLevel ℓ β : ℤ)) ≤
          C * (clusterRange (couplingFlow ℓ β P.scaleLevel).1 : ℝ) ∧
      |(couplingFlow ℓ β (P.separationLevel ℓ β)).1 - (couplingFlow ℓ β P.scaleLevel).1| ≤
          C * Real.log (couplingFlow ℓ β P.scaleLevel).1
end YangMills.Construction.LevelTestFunctions
end
