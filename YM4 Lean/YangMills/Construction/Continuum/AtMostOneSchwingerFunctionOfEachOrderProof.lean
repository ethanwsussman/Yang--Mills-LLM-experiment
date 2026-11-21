import YangMills.Construction.Continuum.AtMostOneSchwingerFunctionOfEachOrder
import YangMills.Construction.Continuum.TransferPrinciple
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.TestSpaces
theorem schwingerUniqueAtEachOrder_of_densityTransfer (hT : DensityTransfer.Statement) :
    SchwingerUniqueAtEachOrder := by
  intro σ _ n S₁ S₂ hS₁ hS₂
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · funext φ
    rw [hS₁.2 rfl φ (fun i => i.elim0), hS₂.2 rfl φ (fun i => i.elim0)]
  · obtain ⟨l₁, ⟨k₁, c₁, hk₁, hc₁, b₁⟩, e₁⟩ := hS₁.1 hpos
    obtain ⟨l₂, ⟨k₂, c₂, hk₂, hc₂, b₂⟩, e₂⟩ := hS₂.1 hpos
    obtain ⟨m₁, m₂⟩ := hT.2 n k₁ k₂ hpos hk₁ hk₂ S₁ S₂ c₁ c₂ l₁ l₂ hc₁ hc₂ b₁ b₂
    refine hT.1 n (max k₁ k₂) hpos (lt_max_of_lt_left hk₁) S₁ S₂ l₁ l₂
      ⟨c₁, c₂, hc₁, hc₂, m₁, m₂⟩ ?_
    intro X hX h
    rw [e₁ X hX h, e₂ X hX h]
end YangMills.Construction.TestSpaces
