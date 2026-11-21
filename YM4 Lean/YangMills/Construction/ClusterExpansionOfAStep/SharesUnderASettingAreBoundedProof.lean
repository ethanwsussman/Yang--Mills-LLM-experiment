import YangMills.Construction.ClusterExpansionOfAStep.SharesUnderASettingAreBounded
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TopLevelSites TorusFields TorusFrame StepSettings StepCosts RenormalizationStepParameters TorusLumps
theorem levelShareBounded_of_complementRegular (hc : ComplementOfThickenedLumpsRegular) :
    LevelShareBounded := by
  intro T hT
  obtain ⟨-, -, -, -, -, -, -, hN, hchain⟩ := hT.chain
  refine ⟨T.N 0 * (2 * T.threshold) ^ 2 + 1, ?_, ?_⟩
  · have := hN 0
    have := hT.σ_pos
    positivity
  intro y R hy hR n _ hn s hs Y
  have hfit : R.params.Admissible := hR ▸ hT.fits y hy
  have hσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hLe : R.params.side = T.side := by rw [hR]; rfl
  have hae : R.params.coupling = T.coupling := by rw [hR]; rfl
  have hn' : T.n₀ = R.params.n₀ := by rw [hR]; rfl
  have hside : ∀ i, (torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  have hamb : IsAdmissibleAmbient (torusFrame R.params.side R.depth n) := isAdmissibleAmbient_torusFrame (by
    have := hT.n₀_ge
    omega)
  obtain ⟨s₀, hs₀, hs₁, hreg, hcold⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 2 * T.threshold ∧
      IsOrthantRegular (cellsOfSites (torusFrame R.params.side R.depth n) s.region) 2047 ∧
      IsCold (cellsOfSites (torusFrame R.params.side R.depth n) s.region) (torusFrame R.params.side R.depth n).top s₀
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse) := by
    have hσ₀ := hT.σ_pos
    rcases hs.region_spec with ⟨htop, hcoldV⟩ | ⟨hLn, htop, -⟩
    · refine ⟨9 / 8 * T.threshold, by positivity, by linarith, ?_, ?_⟩
      · rw [htop, cellsOfSites_univ hside]
        exact isOrthantRegular_finiteCells (fun i => by
          have := hT.n₀_ge
          show 0 < n
          omega) _
      · rw [htop, cellsOfSites_univ hside, ← hσ]
        exact isCold_readAtLevel hside hcoldV
    · refine ⟨T.threshold, hσ₀, by linarith, ?_, ?_⟩
      · rw [htop]
        exact isOrthantRegular_cellsOfSites_compl_thickening hc hfit hLn.1 hside s.coarse
      · rw [htop, ← hσ]
        exact isCold_cellsOfSites_compl_thickening hfit hLn.1 hside s.coarse
  have hle : s₀ ≤ T.σA := by
    have := hT.σ_le
    linarith
  have hall := hchain (torusFrame R.params.side R.depth n) 2047 _ hLe hamb (by norm_num) hreg s₀ _ hs₀ hle hcold
  have hsh := hall.2.2.1
  have hb := hsh.2.2.2.2.2.2.2.1
  have hY := hb (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)
  rw [hae]
  have hN0 := hN 0
  have hsq : s₀ ^ 2 ≤ (2 * T.threshold) ^ 2 := by
    have := hT.σ_pos
    gcongr
  refine ⟨hY.1, hY.2.trans ?_⟩
  have : T.N 0 * s₀ ^ 2 ≤ T.N 0 * (2 * T.threshold) ^ 2 := mul_le_mul_of_nonneg_left hsq hN0.le
  linarith
end YangMills.Construction.ClusterExpansionOfAStep
end
