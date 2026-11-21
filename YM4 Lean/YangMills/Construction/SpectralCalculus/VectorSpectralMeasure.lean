import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal
namespace YangMills.Construction.SpectralCalculus
def VectorSpectralMeasureExists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H),
    IsCommutingSemigroupGroup T U → ∀ v : H,
      ∃ μ : Measure SpectralPlane, IsFiniteMeasure μ ∧ μ.real univ = ‖v‖ ^ 2 ∧
        ∀ (t : ℝ≥0) (s : ℝ), inner ℂ v (T t (U s v)) = ∫ p, spectralCharacter t s p ∂μ
end YangMills.Construction.SpectralCalculus
