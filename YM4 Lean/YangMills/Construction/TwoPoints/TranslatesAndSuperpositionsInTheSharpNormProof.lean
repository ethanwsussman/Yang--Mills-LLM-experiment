import YangMills.Construction.TwoPoints.ConvolutionIsOfClassC1
import YangMills.Construction.TwoPoints.FormAtMollifiedFunctions
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSum
import YangMills.Construction.TwoPoints.FormIsTheLimitAtRiemannSums
import YangMills.Construction.TwoPoints.PairingOfTranslatesIsContinuous
import YangMills.Construction.TwoPoints.RiemannSumsInTheSharpNorm
import YangMills.Construction.TwoPoints.TermsOfARiemannSum
import YangMills.Construction.TwoPoints.TranslatesAndSuperpositionsInTheSharpNorm
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.SharpNormTranslates
theorem proof
    (hMod : TranslationModulusProperties.Statement)
    (hC1 : ConvolveC1.Statement)
    (hTerm : RiemannSumTermProperties.Statement)
    (hEst : ConvolutionRiemannSumSharpEstimates.Statement)
    (hPair : ShiftPairingContinuity.Statement)
    (hGrid : PairedGridSumLimit.Statement)
    (hOnSums : FormOnGridSumsIsPairedSum.Statement)
    (hLim : FormIsGridSumLimit.Statement)
    (hMoll : MollifiedFormLimit.Statement) :
    SharpNormTranslates := by
  intro sc
  refine ⟨fun f hf => (hMod sc f hf).1, ?_, ?_, hMoll sc⟩
  · intro k hk φ hφ δ hδ
    obtain ⟨c₁, c₂⟩ := hC1 k hk φ hφ
    obtain ⟨-, -, -, hfin, -, -⟩ := hTerm k hk φ hφ δ hδ
    obtain ⟨b₁, b₂, b₃, b₄⟩ := hEst sc k hk φ hφ δ hδ
    exact ⟨c₁, c₂, hfin, b₁, b₂, b₃, b₄⟩
  · intro S hS hP ε hε φ₁ h₁ φ₂ h₂
    obtain ⟨hdef, hcont⟩ := hPair sc S hS hP ε hε φ₁ h₁ φ₂ h₂
    refine ⟨hdef, hcont, ?_⟩
    intro k₁ hk₁ k₂ hk₂ hfar
    obtain ⟨hdisj, htends⟩ := hLim sc S hS hP ε hε φ₁ h₁ φ₂ h₂ k₁ hk₁ k₂ hk₂ hfar
    obtain ⟨δ₀, hδ₀, hsum⟩ := hOnSums sc S hS hP ε hε φ₁ h₁ φ₂ h₂ k₁ hk₁ k₂ hk₂ hfar
    refine ⟨hdisj, ?_⟩
    have hnear : (fun δ : ℝ => complexifyForm S (cubeRiemannSum δ k₁ φ₁) (cubeRiemannSum δ k₂ φ₂))
        =ᶠ[𝓝[>] 0] fun δ : ℝ => pairedGridSum δ k₁ k₂ (shiftPairing S φ₁ φ₂) := by
      filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
      exact hsum δ hδ.1 hδ.2
    exact tendsto_nhds_unique (htends.congr' hnear)
      (hGrid ε hε (shiftPairing S φ₁ φ₂) hcont k₁ hk₁ k₂ hk₂ hfar)
end YangMills.Construction.TwoPoints.SharpNormTranslates
end
