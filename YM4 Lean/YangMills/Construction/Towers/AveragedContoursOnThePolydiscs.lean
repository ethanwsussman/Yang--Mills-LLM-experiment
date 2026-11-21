import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PolydiscContours
section Periodic
variable {L m k i : ℕ}
structure IsHolomorphicOnFieldsWithEntries (D : Set (Edge L m k i → Matrices.ComplexMatrix2))
    (h : (Edge L m k i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop where
  isHolomorphicOnFields : ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    MeanStableFields.IsHolomorphicOnFields β D h
  entries : ∃ _ : Fintype (PositiveEdge L m k i),
    ∀ (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) (r s : Fin 2),
      Matrices.GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
        (Matrices.GroupLieProduct.asGroupFactors '' (restrictToPositiveEdges '' D))
        fun p => h (fieldOfPositiveValues fun b => p (.inl b)) r s
structure ContourPropertiesAt (c : Edge L m k (i + 1)) : Prop where
  positive_finite : (DoubleBlockPolydisc.positiveDoubleBlockBonds c).Finite
  positive_nonempty : (DoubleBlockPolydisc.positiveDoubleBlockBonds c).Nonempty
  isRelativelyOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct.unimodularPi (DoubleBlockPolydisc.positiveDoubleBlockBonds c))
    (DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c)
  holomorphic_contourMean : ∀ y ∈ ({c.source, c.target} : Set (Vertex L m k (i + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      ∃ _ : Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c),
        DoubleBlockPolydisc.IsHolomorphicWithEntries
          (DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c) fun v =>
            PeriodicLattice.complexMeanContourHolonomy
              (DoubleBlockPolydisc.fieldOfValues c v) y x
  holomorphicOn_fieldsNearOne : ∀ y ∈ ({c.source, c.target} : Set (Vertex L m k (i + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      IsHolomorphicOnFieldsWithEntries
        (MeanStableFields.fieldsNearOne L m k i)
        fun V => PeriodicLattice.complexMeanContourHolonomy V y x
end Periodic
namespace Infinite
open YangMills.Construction.Tower.FullSpace
variable (L k i : ℕ)
structure ContourPropertiesAt (c : FullSpace.Edge L k (i + 1)) : Prop where
  positive_finite : (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c).Finite
  positive_nonempty : (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c).Nonempty
  isRelativelyOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct.unimodularPi (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c))
    (DoubleBlockPolydisc.Infinite.polydiscPositive L k i (polydiscRadius L) c)
  holomorphic_contourMean : ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (i + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k i) y,
      ∃ _ : Fintype (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c),
        DoubleBlockPolydisc.IsHolomorphicWithEntries
          (DoubleBlockPolydisc.Infinite.polydiscPositive L k i (polydiscRadius L) c)
          fun v => complexContourMean L
            (DoubleBlockPolydisc.Infinite.fieldOfValues L k i c v) y x
end Infinite
def ContourHolomorphyHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i < k →
    (∀ m : ℕ, 0 < m → ∀ c : Edge L m k (i + 1), c.IsPositivelyOriented → ContourPropertiesAt c) ∧
    ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented → Infinite.ContourPropertiesAt L k i c
end YangMills.Construction.Tower.PolydiscContours
end
