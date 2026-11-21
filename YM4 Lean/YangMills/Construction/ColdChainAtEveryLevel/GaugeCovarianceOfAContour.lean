import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def gaugeCovarianceStatement : Prop :=
  ∀ (F : BlockFrame) (j : ℕ), j < F.top → 0 < F.blockSide →
    Function.Injective (refineSite (F := F) (j := j)) ∧
    (∀ (g : F.Site j → UnitQuaternion) (A : F.GaugeField j) (e : F.Site (j + 1) × Fin 4),
      contourAverage (gaugeTransform g A) e = (g (refineSite e.1) : ℍ[ℝ]) * contourAverage A e *
        (((g (refineSite (e.1 + unitStep (j + 1) e.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ])) ∧
    (∀ (g : F.Site j → UnitQuaternion) (A : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4),
      plaquetteHolonomy (gaugeTransform g A) p = g p.1 * plaquetteHolonomy A p * (g p.1)⁻¹) ∧
    ∀ (g : F.Site j → UnitQuaternion) (g' : F.Site (j + 1) → UnitQuaternion) (A : F.GaugeField j)
      (A' : F.GaugeField (j + 1)) (e : F.Site (j + 1) × Fin 4), g (refineSite e.1) = g' e.1 →
      g (refineSite (e.1 + unitStep (j + 1) e.2)) = g' (e.1 + unitStep (j + 1) e.2) →
      blockFit (gaugeTransform g A) (gaugeTransform g' A') e = blockFit A A' e
end BlockAverages
end YangMills.Construction
end
