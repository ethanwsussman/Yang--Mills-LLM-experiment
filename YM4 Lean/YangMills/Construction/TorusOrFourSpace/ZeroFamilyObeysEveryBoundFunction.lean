import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.ZeroFamily
def ZeroHierarchyExists : Prop :=
  ∀ (P : Params) (Y : Kind) (B : BoundFamily),
    ∃ Φ ∈ boundedHierarchies P Y B,
      ∀ (n : ℕ) (hn : 2 ≤ n) (u : sepC1Tuples P Y n), Φ.func n hn u = 0
end YangMills.Construction.PeriodicSpace.Kind.ZeroFamily
end
