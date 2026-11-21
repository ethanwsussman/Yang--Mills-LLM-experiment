import YangMills.Construction.SeparatedSequences.SupDistanceInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def AdjacentSitesInMeetingBlocks : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    (∀ x x' : C.BareSite, (x : C.Point) ∈ Ω 0 → (x' : C.Point) ∈ Ω 0 →
      C.supDist x x' ≤ C.finestMesh →
      ∃ z z' : C.Apex Ω, (x : C.Point) ∈ z.block ∧ (x' : C.Point) ∈ z'.block ∧
        (z.block = z'.block ∨ (z.block ∩ z'.block).Nonempty)) ∧
    ∀ (y : C.Apex Ω) (b : C.BareBond), b.1 ∈ ClassData.bondsWithin y.block →
      (ClassData.anchorSite Ω b : C.Point) ∈ y.block ∨
        ∃ z : C.Apex Ω, (ClassData.anchorSite Ω b : C.Point) ∈ z.block ∧
          (z.block ∩ y.block).Nonempty
end YangMills.Construction.SeparatedClasses
end
