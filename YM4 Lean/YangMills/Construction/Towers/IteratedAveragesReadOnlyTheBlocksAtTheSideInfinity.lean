import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterLocality
def SmallIterates (L k : ℕ) (ρ : ℝ) : Prop :=
  ∀ a : Edge L k 0 → Matrices.ComplexMatrix2,
    a ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
    ∀ j < k,
      complexIter L k j (remainderGaugeField a) ∈
          fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L k j,
          Matrices.ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) <
            polydiscRadius L / 2
def IterLocalityHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
    SmallIterates L k ρ →
    (∀ c : Edge L k k,
      ∀ a : Edge L k 0 → Matrices.ComplexMatrix2,
        a ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      ∀ a' : Edge L k 0 → Matrices.ComplexMatrix2,
        a' ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a' ≤ ENNReal.ofReal ρ →
      ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ B' ∈ complexEdgeForms (meshAt L k 0),
        EqOn a a' (edgesOverEdge c) → EqOn B B' (edgesOverEdge c) →
          (finestMesh L k • iterCovariantDeriv L k (remainderGaugeField a) k B) c =
            (finestMesh L k •
              iterCovariantDeriv L k (remainderGaugeField a') k B') c) ∧
    (∀ y : Vertex L k k,
      ∀ a : Edge L k 0 → Matrices.ComplexMatrix2,
        a ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a ≤ ENNReal.ofReal ρ →
      ∀ a' : Edge L k 0 → Matrices.ComplexMatrix2,
        a' ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm a' ≤ ENNReal.ofReal ρ →
      ∀ u u' : Vertex L k 0 → Matrices.ComplexMatrix2,
        (∀ x, u x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x, u' x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x : Vertex L k 0, (x : InfiniteLattice.AmbientSpace) ∈
          cubeOfOrder L (meshAt L k 0) k y → u x = u' x) →
        EqOn a a'
          {b | (b.initial : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k y ∧
            (b.terminal : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k y} →
          iterAdjointCubeAverage L k (remainderGaugeField a) k u y =
            iterAdjointCubeAverage L k (remainderGaugeField a') k u' y)
end YangMills.Construction.Tower.FullSpace.IterLocality
end
