import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Transpose
structure Facts (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop where
  periodic : IsPeriodicKernel I' I (kernelTranspose I I' T)
  decay : IsDecayRate I' I (kernelTranspose I I' T) δ
  symbol_eq : ∀ κ ∈ strictImStrip δ, SymbolSummableAt I' I (kernelTranspose I I' T) κ ∧
    quotSymbol I' I (kernelTranspose I I' T) κ =
      quotTranspose I I' (quotSymbol I I' T (-κ))
  adjoint_of_real : (∀ x' x, (T x' x).im = 0) → ∀ (κ : InfiniteLattice.AmbientSpace)
    (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ),
      wInner (I.quotWeight 1)
          (applyKernel (quotTranspose I I' (quotSymbol I I' T (-toComplexVec κ))) g) f =
        wInner (I'.quotWeight 1) g
          (applyKernel (quotSymbol I I' T (toComplexVec κ)) f)
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (T : I'.Carrier → I.Carrier → ℂ) (δ : ℝ),
      IsPeriodicKernel I I' T → IsDecayRate I I' T δ → Facts I I' T δ
end YangMills.Construction.PeriodicOperators.Transpose
end
