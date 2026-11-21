import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpectralTheory.BoundedBorelCalculus
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelCalculus
def BoundedBorelCalculusHolds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H), BoundedFunctionalCalculus E
end YangMills.Construction.SpectralTheory.BoundedBorelCalculus
