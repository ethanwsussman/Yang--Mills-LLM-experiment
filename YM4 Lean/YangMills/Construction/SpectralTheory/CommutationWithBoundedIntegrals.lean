import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelCalculus
def CommutesWithBoundedIntegralsHolds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H), CommutesWithIntegralOps E
end YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals
