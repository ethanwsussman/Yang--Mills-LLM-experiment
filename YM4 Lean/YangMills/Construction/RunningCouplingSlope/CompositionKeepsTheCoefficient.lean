import YangMills.Construction.RunningCouplingSlope.BlockMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace SlopeCoefficient
def PullbackKeepsSlopeCoefficient : Prop :=
  ∀ (L : ℕ) (H : GaugeTotal) (p : BlockFieldMap L) (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ)
    (Pl : LatticeBond → LatticeBond → ℝ) (b : ℝ), 0 < L → IsBlockMap L p P Pl →
    HasSlopeCoefficient Filter.atTop H b →
    (∀ᶠ n in Filter.atTop, IsGaugeTotalAt (pullbackTotal H p) n) →
    HasSlopeCoefficient Filter.atTop (pullbackTotal H p) b
end SlopeCoefficient
end YangMills.Construction
end
