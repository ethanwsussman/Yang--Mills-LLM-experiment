import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembers
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ConvexRestriction
def extendByZero {ι ι' : Type} [Fintype ι] [DecidableEq ι'] (j : ι → ι') (ζ : BondField ι) : BondField ι' :=
  fun b => ∑ i, if j i = b then ζ i else 0
def IsConvexClassMemberCompInjective : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (ρ m κ : ℝ) (d : ι → ι → ℝ)
    (d' : ι' → ι' → ℝ) (j : ι → ι') (P : BondField ι' → ℝ), 0 < ρ → 0 ≤ κ → Function.Injective j →
    (∀ i i', d i i' = d' (j i) (j i')) → (∀ b b', 0 ≤ d' b b') → IsConvexClassMember ρ m κ d' P →
    IsConvexClassMember ρ m κ d fun ζ => P (extendByZero j ζ)
end YangMills.Construction.ConvexRestriction
end
