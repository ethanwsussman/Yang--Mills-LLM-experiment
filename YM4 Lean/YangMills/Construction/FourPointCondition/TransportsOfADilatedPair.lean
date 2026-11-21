import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
def dilatedPairPeriodizationStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (vt d : ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ), ℓ.Admissible → 0 < d → 0 < vt → vt ≤ 1 →
    (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt →
    TestFunctions.uniformNorm φ = 1 → TestFunctions.uniformNorm ψ = 1 → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => φ (d⁻¹ • x)),
        TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => ψ (d⁻¹ • x))) ∈
        TestFunctions.separatedPairsFourTorus ℓ.side m d vt ∧
      ResponseInTheExpansion.IsSeparatedTestTuple ℓ m d vt (p := 2)
        ![TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => φ (d⁻¹ • x)),
          TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => ψ (d⁻¹ • x))] ∧
      TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide ℓ.side m)
        (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => φ (d⁻¹ • x)))
        (TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side m) (fun x => ψ (d⁻¹ • x))) =
        TestFunctions.inverseEighthKernel φ ψ
end YangMills.Construction.FourPointCondition
end
