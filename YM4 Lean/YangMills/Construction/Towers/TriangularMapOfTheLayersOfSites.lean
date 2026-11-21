import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LayerDifferenceTriangular : Prop :=
  ∀ L n k : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∃ T : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] vertexFunctionsVanishingAtTop L n k,
      (∀ (κ : vertexFunctionsVanishingAtTop L n k) (i : Fin k) (y : Vertex L n k ((i : ℕ) + 1))
          (x : FineOnlyVertex L n k i),
        x.1 ∈ YangMills.Construction.PeriodicLattice.sitesInBlock
          (YangMills.Construction.PeriodicLattice.levelDepth k i) y →
        (x.1 : YangMills.Construction.PeriodicLattice.FourTorus L n) ≠ y →
        fineOnlyComponents (T κ : Vertex L n k 0 → YangMills.Construction.Matrices.ComplexMatrix2) i x =
          restrictVertexFunction (i : ℕ)
              (κ : Vertex L n k 0 → YangMills.Construction.Matrices.ComplexMatrix2) x.1 -
            restrictVertexFunction ((i : ℕ) + 1)
              (κ : Vertex L n k 0 → YangMills.Construction.Matrices.ComplexMatrix2) y) ∧
      |LinearMap.det T| = 1
end YangMills.Construction.Tower
end
