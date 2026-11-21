import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamily
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
namespace LevelShares
private theorem stepWeight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem isCurvatureFamily_mono {ℓ : TorusLumps.StepParameters} {C C' : ℝ} {f : TorusLumps.LocalDensity}
    (hf : TorusLumps.IsCurvatureFamily ℓ C f) (hCC : C ≤ C') :
    TorusLumps.IsCurvatureFamily ℓ C' f where
  smooth := hf.smooth
  gauge := hf.gauge
  translation := hf.translation
  decay := fun n _ hn y W hW k c X h1 h3 hX =>
    (hf.decay n hn y W hW k c X h1 h3 hX).trans (div_le_div_of_nonneg_right hCC (stepWeight_pos ℓ _).le)
  local_density := fun n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX =>
    (hf.local_density n n' hn hn' y y' W W' m h1 h2 hW hW' ha k b X hk hb hX).trans
      (div_le_div_of_nonneg_right hCC (stepWeight_pos ℓ _).le)
private theorem levelShare_trivialField_zero {n : ℕ} [NeZero n] (a : ℝ) (L : ℕ) (z : TorusFields.TorusSite n) :
    StepCosts.levelShare a L 0 Finset.univ z (TorusFields.trivialField n) = 0 := by
  simp [StepCosts.levelShare, TorusFields.plaquetteEnergy, TorusFields.holonomy_trivialField, Quaternion.re_one]
private theorem levelShare_trivialField_succ (hF : BlockAverages.flatTopVanishingStatement) {a : ℝ} {L : ℕ}
    (ha : 0 ≤ a) (hL : Odd L) (t : ℕ) {n : ℕ} [NeZero n] (z : TorusFields.TorusSite n) :
    StepCosts.levelShare a L (t + 1) Finset.univ z (TorusFields.trivialField n) = 0 :=
  (hF (TorusFields.torusFrame L t n) a
    (TorusFields.cellsOfSites (TorusFields.torusFrame L t n) (Finset.univ : Finset (TorusFields.TorusSite n))) ha hL).2.2 _
end LevelShares
open LevelShares in
theorem levelSharesUniform (hW : ShareFamilies.WilsonSharesFormCurvatureFamily)
    (hS : ShareFamilies.LevelSharesFormCurvatureFamily)
    (hF : BlockAverages.flatTopVanishingStatement) : levelSharesUniformStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL _ T hTa hTL hD _ _ _ _
  refine ⟨T.floorMin, fun y hy _ _ => ?_⟩
  obtain ⟨C₀, hC₀, hW₀, _⟩ := hW (T.stepParameters y) (hD.fits y hy)
  have hK := hS T hD y hy
  have ha₀ : 0 ≤ (T.stepParameters y).coupling := by
    show 0 ≤ T.coupling
    rw [hTa]
    linarith
  have hL₀ : Odd (T.stepParameters y).side := by
    show Odd T.side
    rw [hTL]
    exact hL
  refine ⟨max C₀ (TorusLumps.weightGrowthSup T.rt T.n₁ * TorusLumps.maxOfFirstFour T.N), le_max_of_le_left hC₀,
    fun t => ⟨?_, ?_⟩⟩
  · cases t with
    | zero => exact isCurvatureFamily_mono hW₀ (le_max_left _ _)
    | succ s => exact isCurvatureFamily_mono (hK s).1 (le_max_right _ _)
  · intro n _ _ z
    cases t with
    | zero => exact levelShare_trivialField_zero _ _ z
    | succ s => exact levelShare_trivialField_succ hF ha₀ hL₀ s z
end YangMills.Construction.ResponseInTheExpansion
end
