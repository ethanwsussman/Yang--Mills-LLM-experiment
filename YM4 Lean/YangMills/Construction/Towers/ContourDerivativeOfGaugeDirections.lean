import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def GaugeDirectionContourDerivative : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k k) fun W =>
      ∀ (κ : vertexFunctionsVanishingAtTop L m k) (D : edgeFormSpace L m k 0),
        (D : Edge L m k 0 → Matrices.ComplexMatrix2) = covDiff (chainBottom W) κ →
        ∀ (i : Fin k) (y : Vertex L m k ((i : ℕ) + 1)) (x : FineOnlyVertex L m k i),
          x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
          (x.1 : PeriodicLattice.FourTorus L m) ≠ y →
          contourFamily W D i x =
            restrictVertexFunction (i : ℕ) (κ : Vertex L m k 0 → Matrices.ComplexMatrix2) x.1 -
              restrictVertexFunction ((i : ℕ) + 1) (κ : Vertex L m k 0 → Matrices.ComplexMatrix2) y
end YangMills.Construction.Tower
end
