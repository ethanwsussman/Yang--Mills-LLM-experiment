import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolImShift
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
def Claim : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ (K : Q.Carrier → P.Carrier → ℂ) (δ : ℝ), IsPeriodicKernel P Q K → IsDecayRate P Q K δ →
      ∀ θ : AmbientSpace, euclidNormVec θ < δ → ∀ κ ∈ strictImStrip (δ - euclidNormVec θ),
        IsPeriodicKernel P Q (expConj P Q θ K) ∧
          SymbolSummableAt P Q (expConj P Q θ K) κ ∧
          fourierSymbol P Q (expConj P Q θ K) κ = fourierSymbol P Q K (addIVec κ θ)
end YangMills.Construction.PeriodicOperators.SymbolImShift
end
