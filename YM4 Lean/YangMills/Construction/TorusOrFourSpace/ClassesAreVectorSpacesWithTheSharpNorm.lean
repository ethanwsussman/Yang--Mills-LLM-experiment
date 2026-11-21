import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.VectorClasses
open Kind
variable (D : Params) (E : Kind)
def IsLinearSubspaceSet (V : Set (E.Pt D → ℝ)) : Prop :=
  ∃ W : Submodule ℝ (E.Pt D → ℝ), (W : Set (E.Pt D → ℝ)) = V
def SupportOfCombinationSubset (V : Set (E.Pt D → ℝ)) : Prop :=
  ∀ h ∈ V, ∀ h' ∈ V, ∀ α α' : ℝ,
    supportQ D E (α • h + α' • h') ⊆ supportQ D E h ∪ supportQ D E h'
structure IsNormOn (V : Set (E.Pt D → ℝ)) (ν : (E.Pt D → ℝ) → ℝ≥0∞) : Prop where
  lt_top : ∀ h ∈ V, ν h < ∞
  eq_zero_iff : ∀ h ∈ V, ν h = 0 ↔ h = 0
  smul : ∀ h ∈ V, ∀ α : ℝ, ν (α • h) = ENNReal.ofReal |α| * ν h
  add_le : ∀ h ∈ V, ∀ h' ∈ V, ν (h + h') ≤ ν h + ν h'
def InClosedBall (A : Set (E.Pt D)) : Prop :=
  ∃ (S : Set (E.Pt D)) (R : ℝ), IsClosedBallWithRadius D E S R ∧ A ⊆ S
def ClassesLinear (A : Set (E.Pt D)) : Prop :=
  IsLinearSubspaceSet D E (lipschitzSupportedIn D E A) ∧
  IsLinearSubspaceSet D E (c1SupportedIn D E A) ∧
  SupportOfCombinationSubset D E (lipschitzSupportedIn D E A) ∧
  SupportOfCombinationSubset D E (c1SupportedIn D E A)
def BoundedAndSharpNorm : Prop :=
  (∀ h ∈ lipschitzSupportedIn D E Set.univ, TestFunctions.IsBoundedFun h) ∧
  IsNormOn D E (lipschitzSupportedIn D E Set.univ) (sharpNormQ D E)
def CompactFreeInBall (A : Set (E.Pt D)) : Prop :=
  (∀ S : Set (E.Pt D), IsClosedQ D E S → S ⊆ A → IsCompactQ D E S) ∧
  lipschitzSupportedIn D E A = {h | IsLipschitzQ D E h ∧ supportQ D E h ⊆ A} ∧
  c1SupportedIn D E A = {h | h ∈ c1Set D E ∧ supportQ D E h ⊆ A}
def Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ A : Set (E.Pt D), ClassesLinear D E A) ∧
    BoundedAndSharpNorm D E ∧
    ∀ A : Set (E.Pt D), InClosedBall D E A → CompactFreeInBall D E A
end YangMills.Construction.PeriodicSpace.VectorClasses
end
