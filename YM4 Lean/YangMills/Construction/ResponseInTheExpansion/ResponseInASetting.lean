import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
def chartDensity (s : StepSettings.ChartSetting R n) (η : StepSettings.FreeCoords s.free) : ℝ :=
  s.cutoffProduct η * Real.exp (-s.potential η)
def chartResponse (A : ResponseSetup R) (s : StepSettings.ChartSetting R n) (y : TorusFields.TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) : ℝ :=
  StepSettings.weightedMean (chartDensity s) fun η =>
    centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling h
def chartBondScore (s : StepSettings.ChartSetting R n) (c : TorusFields.TorusBond n) : ℝ :=
  StepSettings.weightedMean (chartDensity s) fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases c
def chartSiteScore (A : ResponseSetup R) (s : StepSettings.ChartSetting R n) (y : TorusFields.TorusSite (n * R.params.side)) :
    ℝ :=
  siteScore A.score s.support s.labelling y
def recordedSiteScore (A : ResponseSetup R) (G : StepGas.GasGround R n) (y : TorusFields.TorusSite (n * R.params.side)) : ℝ :=
  siteScore A.score G.recordedSites G.recordedLabel y
def spinScore (A : ResponseSetup R) {G : StepGas.GasGround R n} (i : G.GasSpin) : G.SpinValue i → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => ∑ z : i.1.2, A.score (v.1.2.1 z)
def configSetting (G : StepGas.GasGround R n) (σ : G.Config) : StepSettings.ChartSetting R n := G.settingOf (G.familyOf σ)
def gasResponseShift (A : ResponseSetup R) (G : StepGas.GasGround R n) (y : TorusFields.TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) : ℝ :=
  G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) y h) - chartResponse A G.groundSetting y h
def gasBondScoreShift (G : StepGas.GasGround R n) (c : TorusFields.TorusBond n) : ℝ :=
  G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) c) - chartBondScore G.groundSetting c
omit [NeZero n] in
def IsBondAtOrigin (c : (Fin 4 → ℤ) × Fin 4) : Prop := c.1 = 0 ∨ c.1 = -Pi.single c.2 1
structure OnStepParameters (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) {R : StepSettings.StepSetup} (A : ResponseSetup R) :
    Prop where
  onFamily : R.OnParameters T y
  abs_sub_le : |R.nextCoupling - R.coupling| ≤ 2 * T.B
  admissible : A.IsAdmissible
  N₀_eq : A.responseParams.N₀ = T.N 0
def HoldsAtEveryStep (P : RenormalizationStepParameters.ParameterAssignment → ∀ R : StepSettings.StepSetup, ResponseSetup R → Prop) : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ (R : StepSettings.StepSetup) (A : ResponseSetup R),
      A.responseParams = K → OnStepParameters T y A → P T R A
end WeightedResponses
end YangMills.Construction
end
