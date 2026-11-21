import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BorelCalculus
open BorelSpectral
def SpectralPushforwardTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H), PushforwardProperties E
end YangMills.Construction.BorelCalculus
