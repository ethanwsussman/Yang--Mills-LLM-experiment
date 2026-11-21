import YangMills.Construction.SeparatedSequences.SupDistanceInLevelUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def BareSitesNearApexInRegionZero : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ (y : C.Apex Ω) (x : C.BareSite),
      (1 ≤ y.level → C.supDist x y.point ≤ 2 * y.mesh → (x : C.Point) ∈ Ω 0) ∧
        (C.supDist x y.point < y.mesh → (x : C.Point) ∈ Ω 0)
end YangMills.Construction.SeparatedClasses
end
