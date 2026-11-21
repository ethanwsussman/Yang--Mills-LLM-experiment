import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StepScalingOfFourierModes
open PeriodicOperators.Tempered PeriodicOperators.Tempered.OneStep
def Claim : Prop :=
  ∀ L : ℕ, ∀ hL : 0 < L, Conventions.IsAdmissibleBlockingFactor L → ∀ n i : ℕ, 0 < n →
    (∀ c : Tower.Edge L n (i + 1) i,
      stepEdgeEquiv hL n i (PeriodicLattice.Bond.opposite c) =
        PeriodicLattice.Bond.opposite (stepEdgeEquiv hL n i c)) ∧
    (∀ (q : InfiniteLattice.AmbientSpace) (σ : Fin 4) (a : Fin 3) (e : UnitEdge L (n + 1)),
      fourierModeForm L (n + 1) a q σ (PeriodicLattice.Bond.opposite e) =
        -fourierModeForm L (n + 1) a q σ e) ∧
    (∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ m : Fin 4 → ℤ,
      (fun ν => p ν + 2 * Real.pi * (m ν : ℝ)) ∈ PeriodicOperators.dualLattice (2 * L ^ n)) ∧
    (∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ (m' : Fin 4 → ℤ)
        (y : Tower.Vertex L n (i + 1) i) (ρ σ : Fin 4) (a : Fin 3),
      fourierModeForm L (n + 1) a (rescaledMomentum L p m') σ
          (stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)) =
        if σ = ρ then
          phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (m' ν : ℝ))
            (y : PeriodicLattice.FourTorus L n) • Matrices.ComplexMatrix2.pauliFamily a
        else 0) ∧
    ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ (m m' : Fin 4 → ℤ)
        (y : Tower.Vertex L n (i + 1) i),
      (∀ ν, (L : ℤ) ∣ m ν - m' ν) →
        phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (m ν : ℝ))
            (y : PeriodicLattice.FourTorus L n) =
          phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (m' ν : ℝ))
            (y : PeriodicLattice.FourTorus L n)
end YangMills.Construction.Tower.StepScalingOfFourierModes
end
