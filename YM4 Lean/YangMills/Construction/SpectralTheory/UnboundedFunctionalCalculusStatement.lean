import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BorelCalculus
def UnboundedFunctionalCalculusHolds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : YangMills.Construction.BorelSpectral.SpectralMeasure Y H),
    UnboundedFunctionalCalculus E
end YangMills.Construction.BorelCalculus
