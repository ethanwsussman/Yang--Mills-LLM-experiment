import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ClusterExpansionOfAStep.GaugeCarriesTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsGaugeInvariant
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOne
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksHaveAGrid
import YangMills.Construction.QuaternionicWilsonModel.TheKernelAndTheArraysOfTheTop
import YangMills.Construction.QuaternionicWilsonModel.TheSeamsOfTheModelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.TopAux
open TorusLumps TorusFields BlockAverages WeightedResponses TotalDensitySystem TotalDensityFlow
namespace KernelAndFunctionals
def withAdmissibleDefaults (ℓ : TorusLumps.StepParameters) : TorusLumps.StepParameters :=
  { ℓ with κ := 1 / 8, κ₁ := 1, rt := 1, n₁ := 1, E := 1, E₃ := 1, derivBound := 1, n₀ := 4096, y₁ := 2 ^ 1600, B := 1 }
theorem clusterRange_two_pow_ge : 2 ^ 16 ≤ TorusLumps.clusterRange (2 ^ 1600) := by apply _root_.YangMills.Construction.ModelSeamsProof.le_clusterRange_two_pow <;> assumption
theorem withAdmissibleDefaults_admissible {ℓ : TorusLumps.StepParameters}
    (hd : TotalDensitySystem.IsUnitMeshStepParameters ℓ) : (withAdmissibleDefaults ℓ).Admissible where
  a_ge := by
    show 1 ≤ ℓ.coupling
    rw [hd.coupling_eq_one]
  L_odd := hd.side_odd
  L_ge := by
    have h := hd.side_ge
    show 2 ^ 16 ≤ ℓ.side
    omega
  σ_pos := hd.threshold_mem.1
  κ_pos := by norm_num [withAdmissibleDefaults]
  κ_le := by norm_num [withAdmissibleDefaults]
  κ₁_pos := by norm_num [withAdmissibleDefaults]
  rt_pos := by norm_num [withAdmissibleDefaults]
  n₁_pos := by norm_num [withAdmissibleDefaults]
  E_pos := by norm_num [withAdmissibleDefaults]
  E_ge := by norm_num [withAdmissibleDefaults]
  depth_lt := hd.side_gt
  E₃_pos := by norm_num [withAdmissibleDefaults]
  B_pos := by norm_num [withAdmissibleDefaults]
  Cder_ge := by norm_num [withAdmissibleDefaults]
  n₀_ge := by norm_num [withAdmissibleDefaults]
  y₁_ge := by
    show (1 : ℝ) ≤ 2 ^ 1600
    exact one_le_pow₀ (by norm_num)
  range_ge := clusterRange_two_pow_ge
theorem chainFunctional_withAdmissibleDefaults (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) (s : ℕ) :
    WeightedResponses.chainFunctional (withAdmissibleDefaults ℓ) β x s = WeightedResponses.chainFunctional ℓ β x s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show TorusLumps.kernelImage (withAdmissibleDefaults ℓ) (x s)
        (WeightedResponses.chainFunctional (withAdmissibleDefaults ℓ) β x s) =
      TorusLumps.kernelImage ℓ (x s) (WeightedResponses.chainFunctional ℓ β x s)
    rw [ih]
    rfl
theorem flowData_snd_eq_chainFunctional (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) :
    (TotalDensityFlow.flowData ℓ β t).2 =
      WeightedResponses.chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t := by apply _root_.YangMills.SharedProofs.p64958 <;> assumption
theorem averagedKernel_pos (hB : TorusLumps.BaseChoicesNonempty) (hK : TorusLumps.BondKernelProperties)
    {ℓ : TorusLumps.StepParameters} (hd : TotalDensitySystem.IsUnitMeshStepParameters ℓ) (x : ℝ) (n : ℕ) [NeZero n]
    (W : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 0) (V : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 1) :
    0 < TorusLumps.averagedKernel ℓ x W V := by
  have hne : (TorusLumps.baseChoices ℓ W).Nonempty :=
    hB (withAdmissibleDefaults ℓ) (withAdmissibleDefaults_admissible hd) hd.side_gt n W
  have hc : (0 : ℝ) < ((TorusLumps.baseChoices ℓ W).card : ℝ) := by exact_mod_cast hne.card_pos
  unfold TorusLumps.averagedKernel
  refine mul_pos (one_div_pos.2 hc) (Finset.sum_pos (fun b _ => Finset.prod_pos fun c _ => ?_) hne)
  exact (hK.2 ℓ x n W V b c).1
theorem chainFunctional_gaugeTransform (hI : TorusLumps.KernelImageGaugeInvariant) {ℓ : TorusLumps.StepParameters}
    (hd : TotalDensitySystem.IsUnitMeshStepParameters ℓ) (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    ∀ (n : ℕ) [NeZero n] (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n),
      WeightedResponses.chainFunctional ℓ β x t n (TorusFields.gaugeTransform g V) =
        WeightedResponses.chainFunctional ℓ β x t n V := by
  induction t with
  | zero =>
    intro n hn g V
    have h0 : n ≠ 0 := NeZero.ne n
    simp only [WeightedResponses.chainFunctional, TorusLumps.wilsonWeight, dif_neg h0,
      TorusFields.wilsonAction_gaugeTransform]
  | succ t ih =>
    intro n _ g V
    exact hI (withAdmissibleDefaults ℓ) (withAdmissibleDefaults_admissible hd) (x t)
      (WeightedResponses.chainFunctional ℓ β x t) n (fun γ W => ih (n * ℓ.side) γ W) g V
end KernelAndFunctionals
theorem kernelAndFunctionalsStatement_holds (hB : TorusLumps.BaseChoicesNonempty)
    (hK : TorusLumps.BondKernelProperties) (hM : TorusLumps.AveragedKernelIntegralOne)
    (hG : TorusLumps.KernelGaugeInvariance) (hI : TorusLumps.KernelImageGaugeInvariant)
    (hC : WeightedResponses.ChainIsProbabilityLaw) (hA : ColdStepAtMirrorFrames.LumpGridExists) :
    TopAux.kernelAndFunctionalsStatement := by
  refine ⟨fun L J σ hodd hL hJ hLJ hσ => ?_, fun ℓ hd => ?_⟩
  · have hL16 : 2 ^ 16 ≤ L := by
      have h2 : (2 : ℕ) ^ 16 ≤ 2 ^ 40 := by norm_num
      omega
    have hne : L ≠ 0 := by
      omega
    obtain ⟨g⟩ := hA L hL16
    exact ⟨{ coupling := 1, side := L, side_ne := ⟨hne⟩, grid := g, baseDepth := J, threshold := σ, κ := 1, κ₁ := 1,
             rt := 1, n₁ := 1, E := 1, E₃ := 1, derivBound := 1, n₀ := 1, y₁ := 1, B := 1 }, rfl, rfl, rfl,
           ⟨rfl, hodd, hL, hJ, hLJ, hσ⟩⟩
  · have hf := KernelAndFunctionals.withAdmissibleDefaults_admissible hd
    refine ⟨fun n _ W => hB (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf hd.side_gt n W,
      fun x n _ W V => KernelAndFunctionals.averagedKernel_pos hB hK hd x n W V,
      fun x n _ W => hM (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf hd.side_gt x n W,
      fun x n _ g W V => ((hG (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf n g W V).2.2 x).2,
      fun x D n _ hD g V => hI (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf x D n hD g V,
      KernelAndFunctionals.flowData_snd_eq_chainFunctional ℓ, fun β x t n _ V => ?_,
      fun β x t n _ g V => KernelAndFunctionals.chainFunctional_gaugeTransform hI hd β x t n g V,
      fun β x t n _ => ?_, fun β t n _ => ?_⟩
    · obtain ⟨-, -, -, h2, -⟩ := hC (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf hd.side_gt β x t n
      rw [KernelAndFunctionals.chainFunctional_withAdmissibleDefaults] at h2
      exact h2 V
    · obtain ⟨-, -, -, -, -, -, h3, -⟩ := hC (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf hd.side_gt β x t n
      rw [KernelAndFunctionals.chainFunctional_withAdmissibleDefaults] at h3
      exact h3
    · obtain ⟨-, h1, -⟩ := hC (KernelAndFunctionals.withAdmissibleDefaults ℓ) hf hd.side_gt β (fun _ => 0) t n
      exact h1
end YangMills.Construction.TopAux
end
