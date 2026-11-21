import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
def SlabDecompositionOfWilsonWeight.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D) (m : SlabCount) (Ψ : ZMod (m : ℕ) → T.SlabConfig → ℂ),
    ∫ U, (∏ k : ZMod (m : ℕ), Ψ k (T.slabRestriction m k U)) *
        Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ)) ∂(T.torusPeriods m).haarMeasure =
      T.slabProductIntegral m fun k => T.slabBoltzmann m (fun _ => 0) k * Ψ k
end YangMills.Construction.ChessboardTori
end
