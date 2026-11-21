import YangMills.Construction.ComplexAnalysis.SeparatelyHolomorphicOnStrips
import Mathlib
namespace YangMills.Construction.Strips
def EqOnHalfPiStripOfEqOnReal : Prop :=
  ∀ f g : ℂ → ℂ, DifferentiableOn ℂ f halfPiStrip → DifferentiableOn ℂ g halfPiStrip →
    (∀ t : ℝ, f (t : ℂ) = g (t : ℂ)) → Set.EqOn f g halfPiStrip
end YangMills.Construction.Strips
