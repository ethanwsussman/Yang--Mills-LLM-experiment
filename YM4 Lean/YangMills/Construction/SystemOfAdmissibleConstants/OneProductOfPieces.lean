import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open MeasureTheory TestFunctions ChessboardTori ReflectedCopies
open InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergy)
def CenteredProductBound : Prop :=
  ∀ (D : ChessboardSetup) (A b l ε : ℝ) (n k : ℕ), 0 ≤ A → 0 ≤ b → k ≤ n → 1 ≤ n → CopyInequality D A b →
    (∃ j : ℤ, l = (D.L : ℝ) ^ j) → max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) ≤ l / D.mesh →
    ε = l / (2 ^ 7 * (n : ℝ)) → ∀ (p : Fin k → AmbientSpace → ℝ) (α : Fin k → AmbientSpace),
      (∀ i, IsLipschitzFor euclidDistR4 (p i)) → (∀ i x, p i x ≠ 0 → ∀ μ, |x μ - α i μ| ≤ ε) →
      (∀ i i', i ≠ i' → ∀ x z, p i x ≠ 0 → p i' z ≠ 0 → 8 * l ≤ euclidDistR4 x z) →
      (∀ ν ∈ periodicGibbsSet D.L D.K D.β,
        |∫ U, ∏ i, (smearedEnergy (p i) U - ∫ V, smearedEnergy (p i) V ∂ν) ∂ν| ≤
          ∏ i, 2 * copyBound A b l (2 * ε) (p i)) ∧
      ∀ m : ℕ+, 2 * l ≤ PeriodicLattice.torusSide D.L m →
        (∀ i i', i ≠ i' → ∀ x z, p i x ≠ 0 → p i' z ≠ 0 →
          8 * l ≤ euclidDistTorus (TorusMetric.torusProj (PeriodicLattice.torusSide D.L m) x)
            (TorusMetric.torusProj (PeriodicLattice.torusSide D.L m) z)) →
        |∫ U, ∏ i, (PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m) (p i)) U -
            ∫ V, PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m) (p i)) V
              ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β)
          ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β| ≤ ∏ i, 2 * copyBound A b l (2 * ε) (p i)
end YangMills.Construction.AdmissibleConstants
end
