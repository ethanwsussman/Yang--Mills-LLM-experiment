import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BorelCalculus
def MarginalsHold : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (E : YangMills.Construction.BorelSpectral.SpectralMeasure (Set.univ : Set (Fin n → ℝ)) H),
    MarginalProperties E
end YangMills.Construction.BorelCalculus
