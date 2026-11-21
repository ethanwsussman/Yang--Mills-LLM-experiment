import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusTraceDet
open RiemannSums (DualClasses)
structure Properties (I : PeriodicData) (T : I.Carrier → I.Carrier → ℂ) : Prop where
  trace_eq : ∀ s, 0 < s → ∀ [Fintype I.UnitQuot] [Fintype (I.QuotMod s)]
    [Fintype (DualClasses s)] r, IsDualSection s r →
      Matrix.trace (Matrix.of (periodicMatrix I I T s)) =
        ∑ q, Matrix.trace (Matrix.of (quotSymbol I I T (toComplexVec (r q))))
  det_eq : ∀ s, 0 < s → ∀ [Fintype I.UnitQuot] [DecidableEq I.UnitQuot]
    [Fintype (I.QuotMod s)] [DecidableEq (I.QuotMod s)] [Fintype (DualClasses s)] r,
      IsDualSection s r →
        Matrix.det (Matrix.of (periodicMatrix I I T s)) =
          ∏ q, Matrix.det (Matrix.of (quotSymbol I I T (toComplexVec (r q))))
def Claim : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ (T : I.Carrier → I.Carrier → ℂ) (δ : ℝ),
    IsPeriodicKernel I I T → IsDecayRate I I T δ → Properties I T
end YangMills.Construction.PeriodicOperators.TorusTraceDet
end
