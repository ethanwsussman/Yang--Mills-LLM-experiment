import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetNumberBounds
open JetQuad
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ → ∀ I : PeriodicData, IsPeriodic I →
    ∀ C : JetQuad I I,
      (IsJet δ p C → ENNReal.ofReal ‖traceNumber C‖ ≤
        (Module.finrank ℂ (I.UnitQuot → ℂ) : ℝ≥0∞) * jetNorm δ p C) ∧
      (IsInvertibleJet δ p C → ENNReal.ofReal ‖logNumber p C‖ ≤
        (Module.finrank ℂ (I.UnitQuot → ℂ) : ℝ≥0∞) *
          ((⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (C.f00 κ))) * jetNorm δ p C +
            (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (C.f00 κ))) ^ 2 *
              jetNorm δ p C ^ 2))
end YangMills.Construction.PeriodicOperators.JetNumberBounds
end
