import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsStronglyContUnitaryRep UnitaryMap)
namespace ScalarMeasures
def ExistsFiniteMeasure : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ), 1 ≤ n →
    ∀ V : Space n → UnitaryMap H H, IsStronglyContUnitaryRep V →
      ∀ ψ : H, ∃ μ : Measure (Space n), IsFiniteMeasure μ ∧
        ∀ v, ⟪ψ, V v ψ⟫_ℂ = ∫ y, expChar v y ∂μ
end ScalarMeasures
end YangMills.Construction.EuclideanBorel
