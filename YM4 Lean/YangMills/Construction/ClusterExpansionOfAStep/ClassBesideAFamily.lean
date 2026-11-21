import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfAGround
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfADensity
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings StepGas TorusFields TorusLumps StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def _root_.YangMills.Construction.StepGas.GasGround.familyCore (G : GasGround R n) (γ : GasFamily R n) :
    SettingCore R n :=
  ⟨G.cut, G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst⟩
def ComponentBesideFamily : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (G : GasGround R n) (γ : GasFamily R n),
    2 ^ 8 * R.params.side ≤ R.range → 0 < R.ballRadius →
    Odd R.params.side → 2 ≤ R.params.side → G.IsAdmissibleGround → G.IsGasFamily γ →
    (G.settingOf γ).IsCoreOf (G.familyCore γ) ∧
    ((G.settingOf γ).IsAdmissible → (G.settingOf γ).IsMarked (G.familyCore γ)) ∧
    (∀ θ : GasSupport R n, γ.Occupies θ →
      (∃ 𝒦 ⊆ (G.settingOf γ).storedComponents (G.familyCore γ), 𝒦.biUnion id = θ.sites) ∧
      (G.settingOf γ).IsPiece (G.familyCore γ) θ.sites ∧
      (∀ z ∈ (G.settingOf γ).support \ θ.2,
        ∀ y ∈ sitesInBlocks R.params.side (blocksNear R.params.side R.range θ.sites),
        (R.range : ℝ) / 4 ≤ supDist y z) ∧
      (∀ b ∈ (G.familyCore γ).badBonds, b.1 ∈ θ.sites → b ∈ θ.1) ∧
      θ.1.image (fun b => parentBlock R.params.side b.1) ⊆
        badBlocksOff R.params.side (G.familyCore γ).badBonds (G.familyCore γ).core θ.sites ∧
      ((G.settingOf γ).IsAdmissible →
        ∀ l ∈ torusHotLumps R.params ((G.settingOf γ).field 0), l ⊆ θ.sites → l ⊆ θ.2)) ∧
    ∀ (θ : GasSupport R n) (s : SupportState θ), G.IsGasSupport θ → (∀ θ', γ.Occupies θ' → θ.FarApart θ') →
      (G.settingOf γ).IsAdmissible →
      (∀ Y ∈ blocksNear R.params.side R.range θ.sites, (G.settingOf γ).AwayFromCore (G.familyCore γ) Y) ∧
      G.IsGasFamily (γ.insertClass θ s) ∧
      (∀ (Y : TorusSite n) (m : ℕ), (∀ y ∈ θ.core, m + 2 ≤ supDist y Y) → 2 * m + 2 < n →
        SettingsAgreeNear (G.settingOf (γ.insertClass θ s)) (G.settingOf γ) Y Y m) ∧
      ∀ b ∈ θ.coreBonds, chartCoord R.params G.coarse (G.settingOf (γ.insertClass θ s)).fine b =
        chartCoord R.params G.coarse (G.frameField (GasFamily.single θ s)) b
end ClusterExpansionOfAStep
end YangMills.Construction
end
