import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
structure RatioConditions (ℓ : TorusLumps.StepParameters) (R : CouplingEvaluation) (φ ψ : (Fin 4 → ℝ) → ℝ)
    (βv nv δv : ℝ) (K : ℕ+) (β d : ℝ) : Prop where
  coupling_ge : βv ≤ β
  sites_ge : nv ≤ d / levelMesh ℓ.side K 0
  twoPoint_small : ∀ d' ∈ Icc ((ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0) d,
    twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d' ≤ ((δv : ℝ) : EReal)
  twoPoint_le : twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d ≤
    ((8 / 3 * TwoPointFunction.amplitudeConstant * TestFunctions.inverseEighthKernel φ ψ *
      R.coupling K β d ^ 4 : ℝ) : EReal)
  le_twoPoint : ((2 / 9 * TwoPointFunction.amplitudeConstant * TestFunctions.inverseEighthKernel φ ψ *
      R.coupling K β d ^ 4 : ℝ) : EReal) ≤ twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d
  torus_large : ∀ σ : ℝ, twoPointLimsupAtScale ℓ.side K β R.sides φ ψ d = ((σ : ℝ) : EReal) → ∀ m : ℕ,
    Real.exp (Real.log (1 / σ) ^ 3) ≤ PeriodicLattice.torusSide ℓ.side m / d
def ratioConditionsEventually : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (vt lam Ca d₀ : ℝ) (n₀ : ℕ) (R : CouplingEvaluation)
    (φ ψ : (Fin 4 → ℝ) → ℝ) (βv nv δv : ℝ),
    ℓ.Admissible → 0 < vt → vt ≤ 1 → EvaluationLaws R ℓ.side vt lam Ca d₀ n₀ →
    (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt →
    TestFunctions.uniformNorm φ = 1 → TestFunctions.uniformNorm ψ = 1 → 0 < δv →
    0 < TestFunctions.inverseEighthKernel φ ψ ∧ ∃ d₄ ∈ Ioc (0 : ℝ) d₀, ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β →
      ∀ d ∈ Ioc (0 : ℝ) d₄, R.IsDeepEnough ℓ.side K n₀ d → RatioConditions ℓ R φ ψ βv nv δv K β d
end YangMills.Construction.FourPointCondition
end
