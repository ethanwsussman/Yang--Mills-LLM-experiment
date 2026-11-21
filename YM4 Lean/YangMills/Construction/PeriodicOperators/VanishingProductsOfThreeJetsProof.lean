import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.VanishingProductsOfThreeJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TripleJets
open JetQuad
theorem vanishOnStrip_of_jetArguments (hArg : JetArgumentsAndEqualJets) : VanishOnStrip := by
  intro δ p hδ hp I₁ I₂ I₃ I₄ _ _ _ _ T S R _ _ _ hT hS hR
  have hSym : JetDomainSymmetries δ p := (hArg.1 δ p hδ hp).1
  have zT : ∀ κ ∈ imStrip (2 * δ), T.f00 κ = 0 := fun κ h => hT h
  have zS : ∀ κ ∈ imStrip (2 * δ), S.f00 κ = 0 := fun κ h => hS h
  have zR : ∀ κ ∈ imStrip (2 * δ), R.f00 κ = 0 := fun κ h => hR h
  refine ⟨fun κ h => ?_, fun κ h => ?_, fun κ h => ?_, fun κ h => ?_⟩
  · simp [JetQuad.mul, zeroJet, zR κ h]
  · obtain ⟨h₁, h₂, -⟩ := hSym.mem_addShift κ h
    simp [JetQuad.mul, zeroJet, zR κ h₁, zT _ h₂]
  · obtain ⟨h₁, h₂, -⟩ := hSym.mem_subShift κ h
    simp [JetQuad.mul, zeroJet, zR κ h₁, zT _ h₂]
  · obtain ⟨⟨⟨h₀, -⟩, -⟩, hm, hq⟩ := hSym.mem_real κ h
    obtain ⟨h₁, h₂, -⟩ := hSym.mem_addShift _ hm
    obtain ⟨h₃, h₄, -⟩ := hSym.mem_subShift _ hq
    simp [JetQuad.mul, zeroJet, zR κ h₀, zT κ h₀, zS _ h₁, zS _ h₃]
end YangMills.Construction.PeriodicOperators.TripleJets
end
