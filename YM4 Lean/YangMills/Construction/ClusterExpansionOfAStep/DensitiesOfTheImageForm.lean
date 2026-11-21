import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.CoupledDensitiesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.PartsOfAHullExpansion
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open StepSettings StepGas StepCosts TorusLumps TorusFields RenormalizationStepParameters ClusterExpansionOfAStep
variable {R : StepSetup} {n : ℕ} [NeZero n]
def StepGas.GasGround.totalDensity (G : GasGround R n) (lam : ℝ) (Y : TorusSite n) : ℝ :=
  G.groundSetting.blockActivity lam Y + G.blockDensity Y
variable (R)
def ImageDensities.groundDensity (G : GasGround R n) (lam : ℝ) (Y : TorusSite n) : ℝ :=
  G.totalDensity lam Y +
      R.nextCoupling * levelShare R.params.coupling R.params.side (R.depth + 1) G.region Y G.coarse -
    (coldCaseGround R (trivialField n)).totalDensity lam Y
def StepSettings.StepSetup.stateDensity (lam : ℝ) (m : ℕ) (Y : TorusSite m) (V : TorusField m)
    (Y' : Finset (TorusSite m)) (ω : Y' → CoarseLabel R.labels.Ω R.params.side) : ℝ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    ImageDensities.groundDensity R (hotCaseGround R V ⟨Y', ω⟩) lam Y
def ImageDensities.ImageHasHullExpansion : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds →
    T.rt ≤ rt₀ T.toChainParameters → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
        ∀ h : CoarseLabelFacts R,
          HullExpansionDisplay R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
            (R.renormalizedDensity T.lam) (coarseLabelSpace R h) (coarseWeightExpansion R) (coarseFactorExpansion R)
            (R.stateDensity T.lam)
end YangMills.Construction
end
