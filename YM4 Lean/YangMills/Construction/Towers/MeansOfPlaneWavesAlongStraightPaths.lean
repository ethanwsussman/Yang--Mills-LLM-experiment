import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StraightPathMeans
def pathAverage (L n i : ℕ) (B : Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
    (y : Tower.Vertex L n (i + 1) i) (ρ : Fin 4) : Matrices.ComplexMatrix2 :=
  Tower.TrivialLinearization.setAverage
    (Tower.TrivialLinearization.baseVerticesOfCube L n (i + 1) i y) fun x =>
      Tower.edgeFormPathSum B
        (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom y ρ) x)
def PlaneWaveMeans : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n i : ℕ, 0 < n →
    ∀ (y : Tower.Vertex L n (i + 1) i) (ρ : Fin 4) (S : Finset (Fin 4 → ℤ))
      (q : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace) (v : (Fin 4 → ℤ) → Matrices.ComplexMatrix2)
      (B B' : Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2),
      (∀ j ∈ S, q j ∈ PeriodicOperators.dualLattice (2 * L ^ n)) →
      (∀ x : Tower.Vertex L n (i + 1) 0,
        B (PeriodicLattice.Bond.forwardFrom x ρ) + Complex.I • B' (PeriodicLattice.Bond.forwardFrom x ρ) =
          ∑ j ∈ S, PeriodicOperators.Tempered.phase (L := L) (n := n) (q j)
            (x : PeriodicLattice.FourTorus L n) • v j) →
      pathAverage L n i B y ρ + Complex.I • pathAverage L n i B' y ρ =
        ∑ j ∈ S, ((L : ℂ) ^ i *
          PeriodicOperators.Tempered.OneStep.stepMean L i ρ (PeriodicOperators.toComplexVec (q j)) *
          PeriodicOperators.Tempered.phase (L := L) (n := n) (q j)
            (y : PeriodicLattice.FourTorus L n)) • v j
end YangMills.Construction.Tower.StraightPathMeans
end
