import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N : ℕ} {κ : LatticeShape d}
def IsAdjointPair {M M' : ℕ} {I J : Type} (T : LatticeField M κ I → LatticeField M' κ J)
    (S : LatticeField M' κ J → LatticeField M κ I) : Prop :=
  ∀ F G, FieldSquareSummable F → FieldSquareSummable G → fieldInner (T F) G = fieldInner F (S G)
end YangMills.Construction.LatticeFields
