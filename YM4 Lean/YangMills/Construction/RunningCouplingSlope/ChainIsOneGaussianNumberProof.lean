import YangMills.Construction.RunningCouplingSlope.ChainIsOneGaussianNumber
import YangMills.Construction.RunningCouplingSlope.ChainNumberIsTheStepsOfTheChain
import YangMills.Construction.RunningCouplingSlope.ChainNumberReadsNoPoint
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeast
import YangMills.Construction.RunningCouplingSlope.LeastFieldOverTheFlatField
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
namespace GaussianChain
private theorem chainLogarithm_eq_sub (hf : RunningCouplingSlope.MinimizerOverTrivialFieldIsTrivial) (a : ℝ) (ha : 0 < a) (L : ℕ)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    ∀ (k m : ℕ), 0 < m → ∀ (N : ℕ), N = 2 * L ^ m → ∀ V : TorusFields.TorusField N,
      SlopeCoefficient.chainLogarithm a ρ L k N V =
        RunningCouplingSlope.chainStepLogSum a ρ L k N V -
          RunningCouplingSlope.chainStepLogSum a ρ L k N (TorusFields.trivialField N) := by
  intro k
  induction k with
  | zero => intro m _ N _ V; simp [SlopeCoefficient.chainLogarithm, RunningCouplingSlope.chainStepLogSum]
  | succ t ih =>
    intro m hm N hN V
    subst hN
    have hN' : 2 * L ^ m * L = 2 * L ^ (m + 1) := by rw [pow_succ]; ring
    have hp := hf a ha L hL t m ρ hm h0 h1
    have e := ih (m + 1) (Nat.succ_pos m) (2 * L ^ m * L) hN'
      (SlopeCoefficient.minimizerOnFinerTorus a ρ L t (2 * L ^ m) V)
    simp only [SlopeCoefficient.chainLogarithm, RunningCouplingSlope.chainStepLogSum,
      SlopeCoefficient.stepGaugeTotal, e, hp]
    ring
end GaussianChain
theorem chainLogIsGaussianNumber_holds (hf : RunningCouplingSlope.MinimizerOverTrivialFieldIsTrivial)
    (hl : RunningCouplingSlope.UnitPointIsMinimizer) (hr : RunningCouplingSlope.MinimizerRepresentsChainNearTrivial)
    (hi : RunningCouplingSlope.ChainLogWeightIndependent) (hs : RunningCouplingSlope.ChainLogWeightEqStepLogSum) :
    RunningCouplingSlope.ChainLogIsGaussianNumber := by
  intro a ha L hL k n hk hn0 ρ h0 h1
  obtain ⟨c, hc⟩ := hs a ha L hL k n hk hn0 ρ h0 h1
  have hall := (hc.and ((hr a ha L hL k n hk hn0 ρ h0 h1).and (hi a ha L hL k n hk hn0)))
  have hflat := hall.self_of_nhds
  filter_upwards [hall] with V hV W hW
  obtain ⟨hcV, hrV, hnV⟩ := hV
  obtain ⟨hcF, hrF, hnF⟩ := hflat
  obtain ⟨X₀, hX₀, hX₀r⟩ := hrV W hW
  refine ⟨⟨X₀, hX₀⟩, ?_⟩
  intro X hX Y Y₀ _ _ _ _ _ _ l l₀ hsl hsl₀
  obtain ⟨hW₁, hflatLeast⟩ := hl a ha L hL k n hk hn0
  obtain ⟨X₁, hX₁, hX₁r⟩ := hrF _ hW₁
  obtain ⟨Z, _, _, _, m, hm, hvalue⟩ := hcV W hW X₀ hX₀ hX₀r
  obtain ⟨Z₁, _, _, _, m₁, hm₁, hvalue₁⟩ := hcF _ hW₁ X₁ hX₁ hX₁r
  have e₁ : RunningCouplingSlope.chainLogWeight a X l = RunningCouplingSlope.chainLogWeight a X₀ m :=
    hnV W hW X X₀ hX hX₀ Y Z l m hsl hm
  have e₂ : RunningCouplingSlope.chainLogWeight a (RunningCouplingSlope.unitPoint L n k) l₀ =
      RunningCouplingSlope.chainLogWeight a X₁ m₁ :=
    hnF _ hW₁ _ X₁ hflatLeast hX₁ Y₀ Z₁ l₀ m₁ hsl₀ hm₁
  rw [GaussianChain.chainLogarithm_eq_sub hf a ha L hL ρ h0 h1 k n hn0 (2 * L ^ n) rfl V, e₁, e₂,
    hvalue, hvalue₁]
  ring
end YangMills.Construction.RunningCouplingSlope
end
