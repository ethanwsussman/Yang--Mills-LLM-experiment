import YangMills.Construction.Towers.AveragingPolydiscRadiusExists
import YangMills.Construction.Towers.PolydiscInsideTheDomainServes
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinity
import YangMills.Construction.Towers.SmallPolydiscLiesInTheComplexDomain
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem admissiblePolydiscRadiusExists_of
    (h₁ : PolydiscInComplexDomain)
    (h₂ : PolydiscInDomainAdmissible)
    (h₃ : PolydiscIsAdmissibleAtInfiniteSide) :
    AdmissiblePolydiscRadiusExists := fun L hL => by
  obtain ⟨ρ, h0, h1, hb⟩ := h₁ L hL
  have sides : ∀ n k j : ℕ, 0 < n → j < k → ∀ e : Edge L n k (j + 1), e.IsPositivelyOriented →
      PolydiscIsAdmissible ρ e := fun n k j hn hj e he =>
    let ⟨a, b, d⟩ := hb n k j hn hj e he
    h₂ L hL ρ h0 n k j hn hj e he a b d
  exact ⟨ρ, h0, h1, sides, h₃ L hL ρ h0 fun k j hj e he => sides 1 k j one_pos hj e he⟩
end YangMills.Construction.Tower
