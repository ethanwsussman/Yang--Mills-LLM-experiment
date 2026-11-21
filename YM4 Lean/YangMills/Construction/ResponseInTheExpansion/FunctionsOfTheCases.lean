import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open BlockAverages StepCosts StepGas StepSettings TorusFields TorusLumps
variable {R : StepSetup} {n : ℕ} [NeZero n]
def IsGaugeInvariantCase (F : CaseFunction R n) : Prop :=
  ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ω : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (u : TorusSite (n * R.params.side) → UnitQuaternion),
    IsLiveState R.params R.coupling R.labelWeight W Yt ω →
    (∀ c, u (toTorusSite (n * R.params.side) (b c)) = 1) →
    (∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) →
    F (gaugeTransform u W) Yt (R.labels.act Yt u ω) bad b = F W Yt ω bad b
def gasExpectationOfCase (G : GasGround R n) (F : CaseFunction R n) : ℝ :=
  G.expectation ∅ fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
    F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
      (G.badBondsOf σ) (configSetting G σ).bases
end WeightedResponses
end YangMills.Construction
end
