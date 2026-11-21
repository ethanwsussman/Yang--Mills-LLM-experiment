import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SequenceTriples
structure IsLinearOnSets {V E : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup E]
    [Module ℂ E] (𝒱 : Set V) (𝒲 : Set E) (T : V → E) : Prop where
  map_mem : ∀ f ∈ 𝒱, T f ∈ 𝒲
  map_combination : ∀ f ∈ 𝒱, ∀ f' ∈ 𝒱, ∀ z z' : ℂ, T (z • f + z' • f') = z • T f + z' • T f'
end YangMills.Construction.SequenceTriples
end
