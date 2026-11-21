import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def HasLimitSecondDeriv (h : LocalDensity) : Prop :=
  ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions), ∃ v : ℝ, Filter.Tendsto
    (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X']) Filter.atTop (𝓝 v)
def limitFormTerm (h : LocalDensity) (A A' : Fin 4 → Fin 4 → imaginaryQuaternions)
    (cc : LatticeBond × LatticeBond) : ℝ :=
  secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)
def curvatureCoefficient (h : LocalDensity) : ℝ :=
  ∑' cc, limitFormTerm h unitPlaneCurvature unitPlaneCurvature cc
def HasCurvatureForm (h : LocalDensity) (b : ℝ) : Prop :=
  HasLimitSecondDeriv h ∧ ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions,
    (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
    HasSum (limitFormTerm h A A') (b * curvaturePairing A A')
structure IsAdmissibleDensity (p : StepParameters) (h : LocalDensity) : Prop where
  smooth : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n),
    IsCold p.threshold W → ContDiffThreeAt (h n y) W
  gauge : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n),
    IsCold p.threshold W → h n y (gaugeTransform g W) = h n y W
  translation : ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y u : TorusSite n) (W : TorusField n),
    IsCold p.threshold W → h n y (TorusFields.translate u W) = h n (y + u) W
def DerivDecay (p : StepParameters) (h : LocalDensity) (e : ℕ → ℕ → ℝ) : Prop :=
  ∀ n [NeZero n], p.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold p.threshold W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (h n y) W c X| ≤ e k (supportDiam y c)
def LocalComparison (p : StepParameters) (h : LocalDensity) (e : ℕ → ℝ) : Prop :=
  ∀ n n' [NeZero n] [NeZero n'], p.n₀ ≤ n → p.n₀ ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (W : TorusField n) (W' : TorusField n') (m : ℕ),
      2 * m + 2 < n → 2 * m + 2 < n' →
      IsCold p.threshold W → IsCold p.threshold W' → FieldsAgreeNear W W' y y' m →
      ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        (∀ l, BondOffsetInBox m (b l)) → AreUnitVectors X →
        |mixedDeriv (h n y) W (fun l => bondFrom y (b l)) X
          - mixedDeriv (h n' y') W' (fun l => bondFrom y' (b l)) X| ≤ e m
def centeredFamily (h : LocalDensity) : LocalDensity := fun n y W => centered h n y W
def sumOfFour (u s τ g : LocalDensity) : LocalDensity := fun n y W => u n y W + s n y W + τ n y W + g n y W
structure ExpansionDensityBounds (p : StepParameters) (Cs CE ε e x : ℝ) (u s τ g : LocalDensity) : Prop where
  admissible_u : IsAdmissibleDensity p u
  admissible_s : IsAdmissibleDensity p s
  admissible_τ : IsAdmissibleDensity p τ
  admissible_g : IsAdmissibleDensity p g
  decay_u : DerivDecay p u fun _ m => Cs * Real.exp (-(p.rt / 2 ^ 6 * m))
  local_u : LocalComparison p u fun m => Cs * Real.exp (-(p.rt / 2 ^ 9 * m))
  decay_s : DerivDecay p s fun k m => 2⁻¹ ^ 6 * (if k = 3 then p.E₃ else p.E) / p.weight m +
    CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(p.rt / 2 ^ 6 * m))
  local_s : LocalComparison p (centeredFamily s) fun m => 2⁻¹ ^ 4 * p.E / p.weight m
  flat_s : ∀ (X : imaginaryQuaternions) (μ ν : Fin 4), ‖X‖ = 1 → μ < ν → ∃ v : ℝ,
    HasSum (limitFormTerm s (planeCurvature X μ ν) (planeCurvature X μ ν)) v ∧ |v| ≤ CE * x ^ (-(1 / 2 : ℝ))
  decay_τ : DerivDecay p τ fun _ m => ε / p.weight m
  local_τ : LocalComparison p τ fun m => ε / p.weight m
  decay_g : DerivDecay p g fun _ m => e / p.weight m
  local_g : LocalComparison p (centeredFamily g) fun m => e / p.weight m
end YangMills.Construction.TorusLumps
end
