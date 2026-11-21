import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def cumulantRatioAt (ℓ : TorusLumps.StepParameters) : Prop :=
  ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ βv nv δv : ℝ, 1 ≤ nv ∧ 0 < δv ∧
    ∀ (K : ℕ+) (β d : ℝ) (sides : Set ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ),
      (∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ PeriodicLattice.torusSide ℓ.side m ∈ sides) →
      (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt → TestFunctions.uniformNorm φ = 1 →
      TestFunctions.uniformNorm ψ = 1 →
      βv ≤ β → nv ≤ d / levelMesh ℓ.side K 0 →
      (∀ d' ∈ Icc ((ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0) d,
        twoPointLimsupAtScale ℓ.side K β sides φ ψ d' ≤ ((δv : ℝ) : EReal)) →
      ∃ σ : ℝ, 0 < σ ∧ twoPointLimsupAtScale ℓ.side K β sides φ ψ d = ((σ : ℝ) : EReal) ∧
        ∀ s : Conventions.StandingParameters, s.L = ℓ.side → s.K = K →
          Real.exp (Real.log (1 / σ) ^ 3) ≤ PeriodicLattice.torusSide s.L s.m / d →
          ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d vt, ∃ r : ℝ,
            PeriodicLattice.torusUrsellFunction s.L s.m s.K β f = r ∧
            8 / 25 * ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ≤
              r * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) ^ 2 / σ ^ 2 ∧
            r * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) ^ 2 / σ ^ 2 ≤
              8 / 3 * ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f
def cumulantRatioStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => cumulantRatioAt (Tb.stepParameters y)
end YangMills.Construction.FourPointCondition
end
