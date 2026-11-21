import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def InvariantFamilyCurvatureForm : Prop :=
  ∀ (p : StepParameters), p.Admissible → ∀ (C : ℝ) (h : LocalDensity), IsCurvatureFamily p C h →
    SumInvariantUnderIsometries p h →
    (∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
        Filter.atTop (nhds (secondDerivLimit h c c' X X'))) ∧
    ∃ b : ℝ, ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions,
      (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2))
        (b * curvaturePairing A A')
end YangMills.Construction.TorusLumps
end
