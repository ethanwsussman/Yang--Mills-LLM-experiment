import YangMills.Construction.Geometry.UnitLatticeBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.UnitSpacingLattice
variable (𝕃 : UnitSpacingLattice)
def cubeUnion (Λ' : Set 𝕃.Point) : Set 𝕃.Point := ⋃ y ∈ Λ', 𝕃.cube y
def edgesMeeting (Λ : Set 𝕃.Point) : Set 𝕃.Edge := {b | b.src ∈ Λ ∨ b.tgt ∈ Λ}
def SupportedOffTrees (Λ' : Set 𝕃.Point) (B : 𝕃.Edge → ℝ) : Prop :=
  (∀ b, b ∉ 𝕃.edgesMeeting (𝕃.cubeUnion Λ') → B b = 0) ∧
    ∀ y ∈ Λ', ∀ b ∈ 𝕃.axialTree y, B b = 0
end YangMills.Construction.UnitSpacingLattice
