import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
def ReflectionPositivityGivesReflectionInvariance.Statement : Prop :=
  ∀ (a : Spacing) (H : NormalHyperplane) (hH : H.IsLatticeMirror (a : ℝ)),
    ((a : ℝ) • H.normal ∈ InfiniteLattice.latticeSubgroup (a : ℝ) ∧ (a : ℝ) • H.normal ≠ 0 ∧
      H.reflectionLinear ((a : ℝ) • H.normal) = -((a : ℝ) • H.normal)) ∧
    ∀ (μ : Measure (InfiniteLattice.GaugeField (a : ℝ))) [IsProbabilityMeasure μ],
      InfiniteLattice.IsShiftInvariant μ →
      NormalHyperplane.IsReflectionPositiveAcrossMirror hH μ →
        InfiniteLattice.IsSymmetricUnder μ (NormalHyperplane.reflectSymmetry hH) ∧
        NormalHyperplane.IsReflectionPositiveOnLowerSide hH μ ∧
        NormalHyperplane.ReflectedPairingBound hH μ
end LatticeConventions
end YangMills.Construction
end
