import YangMills.Construction.Towers.BoundOfTheBondAverageJet
import YangMills.Construction.Towers.BoundOfTheSiteAverageJet
import YangMills.Construction.Towers.BoundsOfTheDefectJets
import YangMills.Construction.Towers.ConstantComponentsOfTheBasicJets
import YangMills.Construction.Towers.TheBasicJetsAreBounded
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.BoundedBasicJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
theorem basicJetsBounded (hconst : YangMills.Construction.Tower.FullSpace.ConstantJetComponents)
    (hdef : YangMills.Construction.Tower.FullSpace.DefectJetBounds)
    (hedge : YangMills.Construction.Tower.FullSpace.EdgeSmoothingJetBound)
    (hvert : YangMills.Construction.Tower.FullSpace.VertexSmoothingJetBound) : BasicJetsBounded := by
  intro L hL
  obtain ⟨C₁, hC₁, b₁⟩ := hdef L hL
  obtain ⟨C₂, -, b₂⟩ := hedge L hL
  obtain ⟨C₃, -, b₃⟩ := hvert L hL
  have m₁ : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have m₂ : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  have m₃ : ENNReal.ofReal C₃ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨⟨max C₁ (max C₂ C₃), hC₁.trans (le_max_left _ _), ?_⟩, ?_⟩
  · intro k hk μp μm z hz
    obtain ⟨e, E, w, f⟩ := b₁ k hk μp μm z hz
    exact ⟨e.trans m₁, E.trans m₁, w.trans m₁, f.trans m₁,
      (b₂ k hk μp μm z hz).trans m₂, (b₃ k hk μp μm z hz).trans m₃⟩
  · intro k hk μp μm z hz
    refine ⟨fun κ hκ => (hconst L hL k hk μp μm z hz κ hκ).1,
      fun κ hκ => (hconst L hL k hk μp μm z hz κ hκ).2.1, fun κ hκ => ?_,
      fun κ hκ => (hconst L hL k hk μp μm z hz κ hκ).2.2.2⟩
    have hw := (hconst L hL k hk μp μm z hz κ hκ).2.2.1
    show (halfFaceTraceJet L k z μp μm).f00 κ +
        ((-1 : ℂ) • (JetQuad.one (colourFaces L k 0)).f00) κ = 0
    rw [hw]
    ext
    simp [JetQuad.one]
end YangMills.Construction.Tower.BoundedBasicJets
end
