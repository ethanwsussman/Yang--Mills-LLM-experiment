import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BorelCalculus
open BorelSpectral
def BorelCalculusTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ),
    (∀ (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H),
      BoundedFunctionalCalculus E ∧ StrongConvergence E ∧ CommutesWithIntegralOps E ∧
        UnboundedFunctionalCalculus E ∧ KernelAndPositivity E ∧ PushforwardProperties E ∧
        EssSupportProperties E) ∧
    ∀ E : SpectralMeasure (Set.univ : Set (Fin n → ℝ)) H, MarginalProperties E
end YangMills.Construction.BorelCalculus
