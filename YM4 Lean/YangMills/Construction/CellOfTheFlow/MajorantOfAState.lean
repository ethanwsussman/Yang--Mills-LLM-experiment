import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters StepReturn WeightedResponses TorusFields
variable {ℓ : StepParameters}
def HoldsAtAdmissibleParametersWithConstants (P : ℝ → ℝ → ParameterAssignment → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound → ∀ C s₁ : ℝ, 0 ≤ C → 0 ≤ s₁ →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionReturnsAt (T.stepParameters y) →
        (∀ β : ℝ, y ≤ β → HasExpansion (T.stepParameters y) 0 β (wilsonWeight β)) → P C s₁ T y
def labelMajorant (T : StageTower ℓ) (s₀ s₁ : ℝ) : (t : ℕ) → (T.stage t).labels.Ω → ℝ
  | 0 => fun _ => s₀
  | t + 1 => coarseLabelScore (L := ℓ.side) s₁ (labelMajorant T s₀ s₁ t)
def siteMajorant (T : StageTower ℓ) (s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n)
    (y : TorusSite n) : ℝ :=
  siteScore (labelMajorant T s₀ s₁ t) (stageState T t n u).2.1 (stageState T t n u).2.2 y
def hullMajorantSum (T : StageTower ℓ) (s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n) : ℝ :=
  ∑ y ∈ stageHull T t n u, siteMajorant T s₀ s₁ t n u y
open Classical in
def componentsNearBox (T : StageTower ℓ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n) (y₀ : TorusSite n)
    (R : ℝ) : Finset (Finset (TorusSite n)) :=
  (chainComponents (stageRange T t) (stageHull T t n u)).filter fun X =>
    ∃ z ∈ X, ∃ w, (supDist w y₀ : ℝ) ≤ R ∧ supDist z w ≤ 1
def majorantNearBox (T : StageTower ℓ) (s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n)
    (y₀ : TorusSite n) (R : ℝ) : ℝ :=
  ∑ X ∈ componentsNearBox T t n u y₀ R, ∑ y ∈ X, siteMajorant T s₀ s₁ t n u y
def maxDiameterNearBox (T : StageTower ℓ) (t n : ℕ) [NeZero n] (u : MarkedSample ℓ t n) (y₀ : TorusSite n)
    (R : ℝ) : ℕ :=
  (componentsNearBox T t n u y₀ R).sup siteDiameter
def PaysMajorant (Tb : ParameterAssignment) (y : ℝ) (T : StageTower (Tb.stepParameters y)) (s₀ s₁ : ℝ) (k : ℕ) :
    Prop :=
  ∀ t ≤ k, PriceBoundsScore (Tb.stepParameters y) (T.stage t).coupling (T.stage t).labels
    (T.stage t).clusterFactor (T.stage t).siteDensity (labelMajorant T s₀ s₁ t)
end YangMills.Construction.CellWindows
end
