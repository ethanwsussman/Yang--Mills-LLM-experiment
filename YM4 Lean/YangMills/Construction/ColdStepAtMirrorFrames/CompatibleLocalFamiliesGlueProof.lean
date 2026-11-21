import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem eventuallyInParametersCombines : EventuallyInParametersCombines := by
  constructor
  · intro P Q hP hQ a ha
    obtain ⟨L₁, hP⟩ := hP a ha
    obtain ⟨L₂, hQ⟩ := hQ a ha
    refine ⟨max L₁ L₂, fun L hL hLe c hc => ?_⟩
    obtain ⟨C₁, hP⟩ := hP L hL (le_trans (le_max_left _ _) hLe) c hc
    obtain ⟨C₂, hQ⟩ := hQ L hL (le_trans (le_max_right _ _) hLe) c hc
    refine ⟨max C₁ C₂, fun Ct hCt => ?_⟩
    obtain ⟨k₁, hk₁, hP⟩ := hP Ct (le_trans (le_max_left _ _) hCt)
    obtain ⟨k₂, hk₂, hQ⟩ := hQ Ct (le_trans (le_max_right _ _) hCt)
    refine ⟨min k₁ k₂, lt_min hk₁ hk₂, fun κ hκ hκ' => ?_⟩
    obtain ⟨e₁, he₁, hP⟩ := hP κ hκ (le_trans hκ' (min_le_left _ _))
    obtain ⟨e₂, he₂, hQ⟩ := hQ κ hκ (le_trans hκ' (min_le_right _ _))
    refine ⟨min e₁ e₂, lt_min he₁ he₂, fun η₃ hη h1 hη' => ?_⟩
    obtain ⟨N₁, hP⟩ := hP η₃ hη h1 (le_trans hη' (min_le_left _ _))
    obtain ⟨N₂, hQ⟩ := hQ η₃ hη h1 (le_trans hη' (min_le_right _ _))
    refine ⟨max N₁ N₂, fun m hm => ?_⟩
    obtain ⟨s₁, hs₁, hP⟩ := hP m (le_trans (le_max_left _ _) hm)
    obtain ⟨s₂, hs₂, hQ⟩ := hQ m (le_trans (le_max_right _ _) hm)
    refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun σ hσ hσ' p hp => ?_⟩
    obtain ⟨D₁, hP⟩ := hP σ hσ (le_trans hσ' (min_le_left _ _)) p hp
    obtain ⟨D₂, hQ⟩ := hQ σ hσ (le_trans hσ' (min_le_right _ _)) p hp
    refine ⟨max D₁ D₂, fun Cs hCs E hE => ?_⟩
    obtain ⟨m₁, hP⟩ := hP Cs (le_trans (le_max_left _ _) hCs) E hE
    obtain ⟨m₂, hQ⟩ := hQ Cs (le_trans (le_max_right _ _) hCs) E hE
    refine ⟨max m₁ m₂, fun n₀ hn₀ => ?_⟩
    obtain ⟨G₁, hP⟩ := hP n₀ (le_trans (le_max_left _ _) hn₀)
    obtain ⟨G₂, hQ⟩ := hQ n₀ (le_trans (le_max_right _ _) hn₀)
    refine ⟨max G₁ G₂, fun CE hCE => ?_⟩
    obtain ⟨y₁', hP⟩ := hP CE (le_trans (le_max_left _ _) hCE)
    obtain ⟨y₂', hQ⟩ := hQ CE (le_trans (le_max_right _ _) hCE)
    exact ⟨max y₁' y₂', fun y hy =>
      ⟨hP y (le_trans (le_max_left _ _) hy), hQ y (le_trans (le_max_right _ _) hy)⟩⟩
  · intro P Q hPQ hP a ha
    obtain ⟨L₀, hP⟩ := hP a ha
    refine ⟨L₀, fun L hL hLe c hc => ?_⟩
    obtain ⟨C₀, hP⟩ := hP L hL hLe c hc
    refine ⟨C₀, fun Ct hCt => ?_⟩
    obtain ⟨k₀, hk₀, hP⟩ := hP Ct hCt
    refine ⟨k₀, hk₀, fun κ hκ hκ' => ?_⟩
    obtain ⟨e₀, he₀, hP⟩ := hP κ hκ hκ'
    refine ⟨e₀, he₀, fun η₃ hη h1 hη' => ?_⟩
    obtain ⟨N₀, hP⟩ := hP η₃ hη h1 hη'
    refine ⟨N₀, fun m hm => ?_⟩
    obtain ⟨s₀, hs₀, hP⟩ := hP m hm
    refine ⟨s₀, hs₀, fun σ hσ hσ' p hp => ?_⟩
    obtain ⟨D₀, hP⟩ := hP σ hσ hσ' p hp
    refine ⟨D₀, fun Cs hCs E hE => ?_⟩
    obtain ⟨m₀, hP⟩ := hP Cs hCs E hE
    refine ⟨m₀, fun n₀ hn₀ => ?_⟩
    obtain ⟨G₀, hP⟩ := hP n₀ hn₀
    refine ⟨G₀, fun CE hCE => ?_⟩
    obtain ⟨y₀, hP⟩ := hP CE hCE
    exact ⟨y₀, fun y hy => hPQ _ ⟨ha, hL, hc, hκ, hη, h1, hσ, hp, hE⟩ (hP y hy)⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
