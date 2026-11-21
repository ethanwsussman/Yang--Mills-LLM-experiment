import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.InfiniteLattice
def RegionObservableReadsInteriorLinks : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (S : Set AmbientSpace) (F : GaugeField a → ℂ),
    F ∈ boundedRegionObservables a S →
    ∀ U U' : GaugeField a, (∀ b : Link a, b.LiesIn S → U b = U' b) → F U = F U'
end YangMills.Construction.InfiniteLattice
