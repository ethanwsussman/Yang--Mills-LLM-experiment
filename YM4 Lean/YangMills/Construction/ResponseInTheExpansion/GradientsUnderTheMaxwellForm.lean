import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RenormalizationStepParameters TorusFields TorusLumps WeightedResponses
namespace ResponseInTheExpansion
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
variable {m : ℕ}
def latticeGradient {m : ℕ} (φ : TorusSite m → ℝ) : TorusBond m → ℝ :=
  fun b => φ (b.1 + unitStep m b.2) - φ b.1
def GradientMaxwellPropertiesAt : Prop :=
  ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n →
    (∀ φ : TorusSite n → ℝ, responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u (latticeGradient φ) =
      latticeGradient fun x => φ (parentBlock (Tb.stepParameters y).side x)) ∧
    (∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ),
      maxwellForm Tb.coupling (Tb.stepParameters y).side u (latticeGradient φ) A = 0) ∧
    ∀ A : TorusBond n → ℝ, 2 * Tb.coercivity * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤
      maxwellForm Tb.coupling (Tb.stepParameters y).side u A A
def gradientMaxwellStatement : Prop := HoldsOnParameterFamilies GradientMaxwellPropertiesAt
end ResponseInTheExpansion
end YangMills.Construction
end
