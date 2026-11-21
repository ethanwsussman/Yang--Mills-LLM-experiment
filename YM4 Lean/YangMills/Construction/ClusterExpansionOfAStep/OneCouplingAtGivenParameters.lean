import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingUniqueness
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
def HasColdForm (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity) : Prop :=
  ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
    Real.log (D n W) - Real.log (D n (trivialField n)) =
      -x * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W + ∑ y, centered f n y W
def HasNoLimitFormTerm (f : LocalDensity) : Prop :=
  ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
    HasSum (limitFormTerm f A A') 0
def CouplingIsUnique : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y →
    ∀ (t : ℕ) (x' x'' C C' : ℝ) (D : TorusFunctional) (f' f'' : LocalDensity),
      IsCurvatureFamily (T.stepParameters y) C f' → IsCurvatureFamily (T.stepParameters y) C' f'' →
      HasNoLimitFormTerm f' → HasNoLimitFormTerm f'' →
      HasColdForm (T.stepParameters y) (t + 1) x' D f' → HasColdForm (T.stepParameters y) (t + 1) x'' D f'' →
      x' = x''
end YangMills.Construction.CouplingUniqueness
end
