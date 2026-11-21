import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PairContourIndependence
def AgreesOn {β : Type} (P : Set β) (V U : β → Matrices.ComplexMatrix2) : Prop :=
  ∀ e ∈ P, U e = V e
section Periodic
variable {L n k j : ℕ}
def ContourAgreementAt (ρ : ℝ) (y : Vertex L n k (j + 1)) (x : Vertex L n k j)
    (c c' : Edge L n k (j + 1)) (V' : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ U U' : Edge L n k j → Matrices.ComplexMatrix2,
    AgreesOn (DoubleBlockPolydisc.doubleBlockBonds c) V' U →
    AgreesOn (DoubleBlockPolydisc.doubleBlockBonds c') V' U' →
      U ∈ nearIdentityPolydisc ρ c ∧ U' ∈ nearIdentityPolydisc ρ c' ∧
        PeriodicLattice.complexMeanContourHolonomy U y x =
          PeriodicLattice.complexMeanContourHolonomy U' y x
end Periodic
namespace Infinite
variable (L k j : ℕ)
def ContourAgreementAt (ρ : ℝ) (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j)
    (c c' : FullSpace.Edge L k (j + 1)) (V' : FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    Prop :=
  ∀ U U' : FullSpace.Edge L k j → Matrices.ComplexMatrix2,
    AgreesOn (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) V' U →
    AgreesOn (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c') V' U' →
      U ∈ FullSpace.nearIdentityPolydisc L k j ρ c ∧
        U' ∈ FullSpace.nearIdentityPolydisc L k j ρ c' ∧
        FullSpace.complexContourMean L U y x = FullSpace.complexContourMean L U' y x
end Infinite
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    (∀ n : ℕ, 0 < n → ∀ (y : Vertex L n k (j + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ∀ c c' : Edge L n k (j + 1), c.IsPositivelyOriented → c'.IsPositivelyOriented →
      y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) →
      y ∈ ({c'.source, c'.target} : Set (Vertex L n k (j + 1))) →
      ∀ V' : Edge L n k j → Matrices.ComplexMatrix2,
        PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V' →
        (∀ e ∈ DoubleBlockPolydisc.doubleBlockBonds c,
          Matrices.ComplexMatrix2.operatorNorm (V' e - 1) < polydiscRadius L) →
        (∀ e ∈ DoubleBlockPolydisc.doubleBlockBonds c',
          Matrices.ComplexMatrix2.operatorNorm (V' e - 1) < polydiscRadius L) →
        ContourAgreementAt (polydiscRadius L) y x c c' V') ∧
    ∀ (y : FullSpace.Vertex L k (j + 1)),
      ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
      ∀ c c' : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented → c'.IsPositivelyOriented →
      y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))) →
      y ∈ ({c'.initial, c'.terminal} : Set (FullSpace.Vertex L k (j + 1))) →
      ∀ V' : FullSpace.Edge L k j → Matrices.ComplexMatrix2,
        FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup V' →
        (∀ e ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
          Matrices.ComplexMatrix2.operatorNorm (V' e - 1) < polydiscRadius L) →
        (∀ e ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c',
          Matrices.ComplexMatrix2.operatorNorm (V' e - 1) < polydiscRadius L) →
        Infinite.ContourAgreementAt L k j (polydiscRadius L) y x c c' V'
end YangMills.Construction.Tower.PairContourIndependence
end
