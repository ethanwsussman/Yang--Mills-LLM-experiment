import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettingsProof
import YangMills.Construction.ResponseInTheExpansion.ScoresOfTwoSettings
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction
open scoped Quaternion
namespace ChartAgreement
open TorusFields hiding unitStep
open TorusLumps StepSettings StepCosts BlockOffsets BlockAverages LumpContours
  ColdStepAtMirrorFrames WeightedResponses
section Settings
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
omit [NeZero n] [NeZero n'] in
theorem offsetInBox_mono {k m : ℕ} (hk : k ≤ m) {h : Fin 4 → ℤ} (hh : OffsetInBox k h) : OffsetInBox m h :=
  fun l => (hh l).trans (by exact_mod_cast hk)
end Settings
section Means
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem contourMean_eq (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n) (h16' : 16 ≤ n')
    {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox 1 h)
    (hh' : OffsetInBox 1 (h + Pi.single i 1)) :
    contourMean R.params.baseDepth (stepHotLumps R.params (s.field η)) s.bases
        (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h), i) =
      contourMean R.params.baseDepth (stepHotLumps R.params (s'.field η')) s'.bases
        (readAtLevel (stepBlockFrame R.params.side n') 0 (s'.field η'))
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.contourMean_eq <;> assumption
theorem meanNorm_eq (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n) (h16' : 16 ≤ n')
    {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox 1 h)
    (hh' : OffsetInBox 1 (h + Pi.single i 1)) :
    meanNorm R.params (s.field η) s.bases (Y + siteOfInt h, i) =
      meanNorm R.params (s'.field η') s'.bases (Y' + siteOfInt h, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.meanNorm_eq <;> assumption
end Means
end ChartAgreement
namespace WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts BlockOffsets BlockAverages LumpContours
  ColdStepAtMirrorFrames ChartAgreement
theorem bondScoresAgreeNearBlocks_holds (hloc : BondKernelLocality) (hsb : BondScoreProperties) :
    BondScoresAgreeNearBlocks := by
  intro R n n' _ _ s s' Y Y' m k η η' h i hfit hJ h16 h16' hf hag hk4 hk hnear hh hh'
  have hM := contourMean_eq hloc hfit hJ h16 h16' hf hag hk4 hk hnear h i hh hh'
  have hS := meanNorm_eq hloc hfit hJ h16 h16' hf hag hk4 hk hnear h i hh hh'
  have h1m : 1 ≤ m := by omega
  have hV : s.coarse (Y + siteOfInt h) i = s'.coarse (Y' + siteOfInt h) i :=
    hag.coarse_agree (h, i) ⟨offsetInBox_mono h1m hh, offsetInBox_mono h1m hh'⟩
  have e1 := (hsb R.params hfit R.coupling n s.bases (Y + siteOfInt h, i)).2.1 (s.field η) s.coarse
  have e2 := (hsb R.params hfit R.coupling n' s'.bases (Y' + siteOfInt h, i)).2.1 (s'.field η') s'.coarse
  have hm : bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η)) s.bases
        (Y + siteOfInt h, i) =
      bondMean R.params (readAtLevel (stepBlockFrame R.params.side n') 0 (s'.field η')) s'.bases
        (Y' + siteOfInt h, i) := hM
  rw [e1, e2, hS, hm, hV]
end WeightedResponses
end YangMills.Construction
end
