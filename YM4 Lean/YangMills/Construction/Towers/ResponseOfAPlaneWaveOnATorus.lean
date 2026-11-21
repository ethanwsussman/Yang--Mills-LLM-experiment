import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PeriodicResponseOfFourierMode
open PeriodicOperators (toComplexVec dualLattice)
open PeriodicOperators.Tempered PeriodicOperators.Tempered.OneStep
def complexPeriodicResponse (L n i : ℕ) (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2 :=
  (Tower.CriticalBranchResponse.periodicResponse L n (i + 1)
      (topLevelForm L n (i + 1) (realComponent B)) :
      Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) +
    Complex.I •
      (Tower.CriticalBranchResponse.periodicResponse L n (i + 1)
          (topLevelForm L n (i + 1) (imagComponent B)) :
        Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ i : ℕ, EventuallyForSides L fun n =>
    ∀ p ∈ dualLattice (2 * L ^ n), ∀ (a : Fin 3) (μ ρ : Fin 4) (x : Tower.Vertex L n (i + 1) 0),
      complexPeriodicResponse L n i (fourierModeForm L n a p μ)
          (PeriodicLattice.Bond.forwardFrom x ρ) =
        ∑ m ∈ Tower.PlaneWaves.freqBox L (i + 1),
          (phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (m ν : ℝ))
              (x : PeriodicLattice.FourTorus L n) *
            responseCoeff L (i + 1) (toComplexVec p) ρ μ m) •
              Matrices.ComplexMatrix2.pauliFamily a
end YangMills.Construction.Tower.PeriodicResponseOfFourierMode
end
