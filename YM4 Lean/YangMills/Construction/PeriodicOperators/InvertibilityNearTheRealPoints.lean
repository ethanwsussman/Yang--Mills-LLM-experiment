import YangMills.Construction.Towers.CoercivityOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.InvertibilityNearReal
open StripSymbols (openStripInterior)
def InvertibleNearRealAxis : Prop :=
  ∀ P : PeriodicData, IsPeriodic P →
    ∀ (υ B σ δ : ℝ) (F : (Fin 4 → ℂ) → QuotHom P P),
      0 < υ → 0 ≤ B → 0 < σ → 0 < δ → δ ≤ υ / 2 → 8 * B * δ / υ ≤ σ / 2 →
      QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior υ) F →
      (∀ ξ ∈ openStripInterior υ, quotHomNorm (F ξ) ≤ ENNReal.ofReal B) →
      (∀ ξ ∈ realDualPoints, LoewnerLE (scalarQuotHom P σ) (F ξ)) →
      ∀ ξ ∈ imStrip δ, IsInvertibleQuotHom (F ξ) ∧
        quotHomNorm (quotHomInverse (F ξ)) ≤ ENNReal.ofReal (2 / σ)
end YangMills.Construction.PeriodicOperators.InvertibilityNearReal
end
