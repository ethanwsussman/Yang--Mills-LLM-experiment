import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FieldHaar
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def HaarInvariantUnderSymmetries : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ g : TorusSite n → UnitQuaternion, MeasurePreserving (gaugeTransform g) (fieldHaar n) (fieldHaar n)) ∧
    ∀ g : TorusIsometry, ∃ Ψ : TorusField n → TorusField n,
      MeasurePreserving Ψ (fieldHaar n) (fieldHaar n) ∧ ∀ W, g.Transports W (Ψ W)
end FieldHaar
end YangMills.Construction
end
