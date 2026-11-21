import YangMills.Construction.TorusOrFourSpace.FactsOnTheEffectiveConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace EffectiveConstantFacts
theorem claim_holds (hRadius : RadiusThetaFacts.Claim)
    (hCover : TorusBallCoversAndPartitionsOfUnity) :
    EffectiveConstantFacts.Claim := by
  obtain ⟨hTheta, ⟨hFinite, -, hFour⟩, hDepend, -, -⟩ := hRadius
  refine ⟨hTheta, ?_, hFinite, hFour, hDepend⟩
  intro D θ P a
  exact ((hCover D 1 one_pos).2.2 (P.bump a)
    (P.subordinate.mem_unitInterval a).1).2.2.1
end EffectiveConstantFacts
end YangMills.Construction.PeriodicSpace
