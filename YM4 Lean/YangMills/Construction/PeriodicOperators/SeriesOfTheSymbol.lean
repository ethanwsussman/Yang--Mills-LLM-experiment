import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
structure SymbolSeriesFacts (P Q : PeriodicData) (K : Q.Carrier → P.Carrier → ℂ) (δ : ℝ) : Prop where
  summableOn_strip : SymbolSummableOn P Q K (strictImStrip δ)
  locallyUniform : ∀ j i,
    SummableLocallyUniformlyOn (fun k κ => symbolSummand P Q K κ j i k) (strictImStrip δ)
  locallyUniform_norm : ∀ j i,
    SummableLocallyUniformlyOn (fun k κ => ‖symbolSummand P Q K κ j i k‖) (strictImStrip δ)
  holomorphic : ∀ j i, Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1)
    (strictImStrip δ) fun κ _ => fourierSymbol P Q K κ j i
def SymbolSeriesClaim : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ (K : Q.Carrier → P.Carrier → ℂ) (δ : ℝ), IsDecayRate P Q K δ → SymbolSeriesFacts P Q K δ
end PeriodicOperators
end YangMills.Construction
end
