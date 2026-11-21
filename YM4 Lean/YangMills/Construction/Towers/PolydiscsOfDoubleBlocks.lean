import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.DoubleBlockPolydisc
section General
variable {ι : Type}
def positiveImage (isPos : ι → Prop) (S : Set ι) (U : Set (ι → Matrices.ComplexMatrix2)) :
    Set (Tower.BondSetFields.positivePart isPos S → Matrices.ComplexMatrix2) :=
  Tower.BondSetFields.readPositive isPos S '' (Tower.BondSetFields.restrictTo S '' U)
def leftComponents {τ : Type} (p : τ ⊕ Empty → Matrices.ComplexMatrix2) :
    τ → Matrices.ComplexMatrix2 := fun t => p (.inl t)
structure IsHolomorphicWithEntries {τ : Type} [Fintype τ] (W : Set (τ → Matrices.ComplexMatrix2))
    (Φ : (τ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop where
  toUnimodular : ∀ e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular e (leftComponents ⁻¹' W)
      (Φ ∘ leftComponents)
  toMatrices : ∀ e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicToCoords e Coordinates.ComplexCoordinates.matrixEquiv
      (leftComponents ⁻¹' W) (Φ ∘ leftComponents)
  entries : ∀ (e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) (r s : Fin 2),
    Matrices.GroupLieProduct.IsHolomorphicToCoords e (Equiv.funUnique (Fin 1) ℂ).symm
      (leftComponents ⁻¹' W) fun p => Φ (leftComponents p) r s
structure FiniteOpenPolydisc (opp : ι → ι) (isPos : ι → Prop)
    (IsField : Set Matrices.ComplexMatrix2 → Set ι → (ι → Matrices.ComplexMatrix2) → Prop)
    (S : Set ι) (U : Set (ι → Matrices.ComplexMatrix2)) : Prop where
  finite : S.Finite
  opposite_mem : ∀ b ∈ S, opp b ∈ S
  positive_finite : (Tower.BondSetFields.positivePart isPos S).Finite
  positive_nonempty : (Tower.BondSetFields.positivePart isPos S).Nonempty
  bijOn_readPositive : BijOn (Tower.BondSetFields.readPositive isPos S)
    (Tower.BondSetFields.fieldsOn (IsField PeriodicLattice.complexGaugeGroup) S)
    (Matrices.GroupLieProduct.unimodularPi (Tower.BondSetFields.positivePart isPos S))
  isRelativelyOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.GroupLieProduct.unimodularPi (Tower.BondSetFields.positivePart isPos S))
    (positiveImage isPos S U)
  isRelativelyOpen_compact : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.specialUnitaryPower (Tower.BondSetFields.positivePart isPos S))
    (positiveImage isPos S {V | V ∈ U ∧ IsField PeriodicLattice.compactGaugeGroup S V})
end General
section Periodic
variable {L n k j : ℕ}
abbrev doubleBlockBonds (c : Tower.Edge L n k (j + 1)) : Set (Tower.Edge L n k j) :=
  PeriodicLattice.bondsInDoubleBlock c
abbrev positiveDoubleBlockBonds (c : Tower.Edge L n k (j + 1)) : Set (Tower.Edge L n k j) :=
  Tower.BondSetFields.positivePart PeriodicLattice.Bond.IsPositivelyOriented (doubleBlockBonds c)
abbrev polydiscPositive (ρ : ℝ) (c : Tower.Edge L n k (j + 1)) :
    Set (positiveDoubleBlockBonds c → Matrices.ComplexMatrix2) :=
  positiveImage PeriodicLattice.Bond.IsPositivelyOriented (doubleBlockBonds c)
    (Tower.nearIdentityPolydisc ρ c)
abbrev fieldOfValues (c : Tower.Edge L n k (j + 1))
    (v : positiveDoubleBlockBonds c → Matrices.ComplexMatrix2) :
    Tower.Edge L n k j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.extendFromPositive (doubleBlockBonds c) v
structure PolydiscPropertiesAt (ρ : ℝ) (c : Tower.Edge L n k (j + 1)) : Prop where
  doubleBlockBonds_eq : doubleBlockBonds c =
    {b | (b.source : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target}
  finite_open : FiniteOpenPolydisc PeriodicLattice.Bond.opposite
    PeriodicLattice.Bond.IsPositivelyOriented PeriodicLattice.IsGaugeField (doubleBlockBonds c)
    (Tower.nearIdentityPolydisc ρ c)
  holomorphic_smoothing : ∃ _ : Fintype (positiveDoubleBlockBonds c),
    IsHolomorphicWithEntries (polydiscPositive ρ c) fun v =>
      PeriodicLattice.complexBlockAverage (fieldOfValues c v) c
  holomorphic_contourMean : ∀ y ∈ ({c.source, c.target} : Set (Tower.Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ∃ _ : Fintype (positiveDoubleBlockBonds c),
        IsHolomorphicWithEntries (polydiscPositive ρ c) fun v =>
          PeriodicLattice.complexMeanContourHolonomy (fieldOfValues c v) y x
end Periodic
namespace Infinite
section Levels
variable (L k j : ℕ)
abbrev doubleBlockBonds (c : Tower.FullSpace.Edge L k (j + 1)) :
    Set (Tower.FullSpace.Edge L k j) :=
  Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c
abbrev positiveDoubleBlockBonds (c : Tower.FullSpace.Edge L k (j + 1)) :
    Set (Tower.FullSpace.Edge L k j) :=
  Tower.BondSetFields.positivePart InfiniteLattice.Link.IsPositivelyOriented
    (doubleBlockBonds L k j c)
abbrev polydiscPositive (ρ : ℝ) (c : Tower.FullSpace.Edge L k (j + 1)) :
    Set (positiveDoubleBlockBonds L k j c → Matrices.ComplexMatrix2) :=
  positiveImage InfiniteLattice.Link.IsPositivelyOriented (doubleBlockBonds L k j c)
    (Tower.FullSpace.nearIdentityPolydisc L k j ρ c)
abbrev fieldOfValues (c : Tower.FullSpace.Edge L k (j + 1))
    (v : positiveDoubleBlockBonds L k j c → Matrices.ComplexMatrix2) :
    Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2 :=
  Tower.FullSpace.extendFromPositive (doubleBlockBonds L k j c) v
structure PolydiscPropertiesAt (ρ : ℝ) (c : Tower.FullSpace.Edge L k (j + 1)) : Prop where
  doubleBlockBonds_eq : doubleBlockBonds L k j c =
    {b | (b.initial : InfiniteLattice.AmbientSpace) ∈
          Tower.FullSpace.cube L (Tower.meshAt L k j) c.initial ∪
            Tower.FullSpace.cube L (Tower.meshAt L k j) c.terminal ∧
      (b.terminal : InfiniteLattice.AmbientSpace) ∈
          Tower.FullSpace.cube L (Tower.meshAt L k j) c.initial ∪
            Tower.FullSpace.cube L (Tower.meshAt L k j) c.terminal}
  finite_open : FiniteOpenPolydisc InfiniteLattice.Link.opposite
    InfiniteLattice.Link.IsPositivelyOriented Tower.FullSpace.IsFieldOn (doubleBlockBonds L k j c)
    (Tower.FullSpace.nearIdentityPolydisc L k j ρ c)
  holomorphic_smoothing : ∃ _ : Fintype (positiveDoubleBlockBonds L k j c),
    IsHolomorphicWithEntries (polydiscPositive L k j ρ c) fun v =>
      Tower.FullSpace.complexSmoothing L (fieldOfValues L k j c v) c
  holomorphic_contourMean :
    ∀ y ∈ ({c.initial, c.terminal} : Set (Tower.FullSpace.Vertex L k (j + 1))),
      ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y,
        ∃ _ : Fintype (positiveDoubleBlockBonds L k j c),
          IsHolomorphicWithEntries (polydiscPositive L k j ρ c) fun v =>
            Tower.FullSpace.complexContourMean L (fieldOfValues L k j c v) y x
end Levels
end Infinite
def PolydiscsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    (∀ n : ℕ, 0 < n → ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      PolydiscPropertiesAt (Tower.polydiscRadius L) c) ∧
    ∀ c : Tower.FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      Infinite.PolydiscPropertiesAt L k j (Tower.polydiscRadius L) c
end YangMills.Construction.Tower.DoubleBlockPolydisc
end
