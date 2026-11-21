import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.BlockLocality
def IteratesSmall (L n k : ℕ) (ρ : ℝ) : Prop :=
  ∀ a : Edge L n k 0 → Matrices.ComplexMatrix2,
    a ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
    ∀ i < k,
      PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) ∈
          fieldsIn L n k i PeriodicLattice.complexGaugeGroup ∧
        ∀ e : Edge L n k i,
          Matrices.ComplexMatrix2.operatorNorm
              (PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) e - 1) <
            polydiscRadius L / 2
def LocalDependence : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n → 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
    IteratesSmall L n k ρ →
    (∀ e : Edge L n k k,
      ∀ a : Edge L n k 0 → Matrices.ComplexMatrix2,
        a ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      ∀ a' : Edge L n k 0 → Matrices.ComplexMatrix2,
        a' ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a' ≤ ENNReal.ofReal ρ →
      ∀ F ∈ complexEdgeForms L n k 0, ∀ F' ∈ complexEdgeForms L n k 0,
        EqOn a a' (edgesOverEdge e) → EqOn F F' (edgesOverEdge e) →
          (finestMesh L k • iterCovariantDeriv L n k (remainderGaugeField a) k F) e =
            (finestMesh L k •
              iterCovariantDeriv L n k (remainderGaugeField a') k F') e) ∧
    (∀ v : Vertex L n k k,
      ∀ a : Edge L n k 0 → Matrices.ComplexMatrix2,
        a ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      ∀ a' : Edge L n k 0 → Matrices.ComplexMatrix2,
        a' ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm a' ≤ ENNReal.ofReal ρ →
      ∀ f f' : Vertex L n k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x, f' x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k v →
          f x = f' x) →
        EqOn a a' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k v)) →
          iterAdjointCubeAverage L n k (remainderGaugeField a) k f v =
            iterAdjointCubeAverage L n k (remainderGaugeField a') k f' v)
end YangMills.Construction.Tower.BlockLocality
end
