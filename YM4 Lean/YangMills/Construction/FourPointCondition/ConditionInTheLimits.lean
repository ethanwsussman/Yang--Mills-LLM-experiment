import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.WindowOfTheParameters.LimitsInWindows
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def IsInLimitInterval {Y : Type*} (vt d : ℝ) (f : Fin 4 → Y → ℝ) (r : ℝ) : Prop :=
  fourPointLowerConst vt * gaugeGroupDim * (2 / 3 * oneLoopCoeff) ^ 4 * Real.log (1 / d) ^ (-4 : ℤ) *
      ∏ i, TestFunctions.uniformNorm (f i) ≤ r ∧
    r ≤ fourPointUpperConst * gaugeGroupDim * (4 / 3 * oneLoopCoeff) ^ 4 * Real.log (1 / d) ^ (-4 : ℤ) *
      ∏ i, TestFunctions.uniformNorm (f i)
def LimitBoundStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∀ (R : CouplingEvaluation) (lam Ca d₀ : ℝ) (n₀ : ℕ), EvaluationLaws R (Tb.stepParameters y).side vt lam Ca d₀ n₀ →
      ∃ d₄ ∈ Ioc (0 : ℝ) d₀, ∀ d ∈ Ioc (0 : ℝ) d₄,
        (∀ (Ks : ℕ → ℕ+) (βs : ℕ → ℝ), (∀ j, R.IsFirstPassage (Ks j) (βs j)) →
          Tendsto (fun j => (Ks j : ℕ)) atTop atTop →
          ∀ s : Conventions.StandingParameters, s.L = (Tb.stepParameters y).side →
            PeriodicLattice.torusSide s.L s.m ∈ R.sides →
            ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d vt, ∀ S : ℂ,
              Tendsto (fun j => PeriodicLattice.torusUrsellFunction s.L s.m (Ks j) (βs j) f)
                atTop (nhds S) →
              ∃ r : ℝ, S = r ∧ IsInLimitInterval vt d f r) ∧
        (∀ (Ks : ℕ → ℕ+) (βs : ℕ → ℝ) (ms : ℕ → ℕ+), (∀ j, R.IsFirstPassage (Ks j) (βs j)) →
          (∀ j, PeriodicLattice.torusSide (Tb.stepParameters y).side (ms j) ∈ R.sides) →
          Tendsto (fun j => (Ks j : ℕ)) atTop atTop → Tendsto (fun j => (ms j : ℕ)) atTop atTop →
          ∀ f ∈ QuadrupleClasses.collinearQuadsR4 d vt, InfiniteLattice.IsSeparatedC1cTuple f → ∀ S : ℂ,
            Tendsto (fun j => PeriodicLattice.torusUrsellFunction (Tb.stepParameters y).side (ms j) (Ks j) (βs j)
              fun i => TestFunctions.periodize (PeriodicLattice.torusSide (Tb.stepParameters y).side (ms j)) (f i))
              atTop (nhds S) →
            ∃ r : ℝ, S = r ∧ IsInLimitInterval vt d f r) ∧
        ∀ S : (n : ℕ) → (Fin n → InfiniteLattice.AmbientSpace → ℝ) → ℂ,
          InfiniteLattice.IsWindowedVolumeLimit (Tb.stepParameters y).side
            (fun K => {β | R.IsFirstPassage K β}) S →
          ∀ f ∈ QuadrupleClasses.collinearQuadsR4 d vt, InfiniteLattice.IsSeparatedC1cTuple f →
            ∃ r : ℝ, S 4 f = r ∧ IsInLimitInterval vt d f r
end YangMills.Construction.FourPointCondition
end
