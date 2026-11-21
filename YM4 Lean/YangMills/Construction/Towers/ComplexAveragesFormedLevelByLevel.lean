import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LevelwiseMeans
open YangMills.Construction.Matrices
def valuesOrOne {β : Type} (w : β → Option ComplexMatrix2) : β → ComplexMatrix2 :=
  fun b => (w b).getD 1
section Periodic
variable {L n k : ℕ}
def edgeEntries {j : ℕ} (F : Finset (Edge L n k j)) (U : Edge L n k j → ComplexMatrix2) :
    F → ComplexMatrix2 :=
  fun b => U b
def expChartPoint {j : ℕ} (F : Finset (Edge L n k j)) (X U : Edge L n k j → ComplexMatrix2) :
    F → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • X b) * U b
def meanOfDefined {i : ℕ} (w : Edge L n k i → Option ComplexMatrix2) (c : Edge L n k (i + 1)) :
    Option ComplexMatrix2 :=
  open Classical in
  if (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)), (w b).isSome) ∧
      valuesOrOne w ∈ nearIdentityPolydisc (polydiscRadius L) c then
    some (PeriodicLattice.complexBlockAverage (valuesOrOne w) c)
  else none
def levelwiseMean (W : Edge L n k 0 → ComplexMatrix2) : (i : ℕ) → Edge L n k i → Option ComplexMatrix2
  | 0 => fun c => some (W c)
  | i + 1 => fun c =>
    open Classical in
    if c.IsPositivelyOriented then meanOfDefined (levelwiseMean W i) c
    else (meanOfDefined (levelwiseMean W i) c.opposite).map (·⁻¹)
def IsDefinedAt (W : Edge L n k 0 → ComplexMatrix2) (i : ℕ) (c : Edge L n k i) : Prop :=
  (levelwiseMean W i c).isSome
def RealAndComplexAgreeNearIdentity (j : ℕ) (c : Edge L n k (j + 1)) (y : Vertex L n k (j + 1))
    (x : Vertex L n k j) : Prop :=
  EventuallyNearIdentity (fieldSpace L n k j) fun V =>
    V ∈ nearIdentityPolydisc (polydiscRadius L) c ∧
    PeriodicLattice.complexBlockAverage V c = smoothingStep L n k j V c ∧
    PeriodicLattice.HasContourMean V y x ∧
    PeriodicLattice.complexMeanContourHolonomy V y x = PeriodicLattice.meanContourHolonomy V y x ∧
    ∀ B ∈ edgeFormSpace L n k j,
      (∀ᶠ t : ℝ in 𝓝 0, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈
        nearIdentityPolydisc (polydiscRadius L) c) ∧
      (∃ D : ComplexMatrix2,
        HasDerivAt (fun t : ℝ => smoothingStep L n k j (PeriodicLattice.expTwist ((t : ℂ) • B) V) c) D 0 ∧
        HasDerivAt (fun t : ℝ =>
          PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist ((t : ℂ) • B) V) c) D 0) ∧
      ∃ D : ComplexMatrix2,
        HasDerivAt (fun t : ℝ =>
          PeriodicLattice.meanContourHolonomy (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x) D 0 ∧
        HasDerivAt (fun t : ℝ =>
          PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist ((t : ℂ) • B) V) y x) D 0
structure IsMeanSequence (j : ℕ) (V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2) : Prop where
  mem_fields : ∀ i ≤ j, V i ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup
  norm_sub_one_lt : ∀ i < j, ∀ b, ComplexMatrix2.operatorNorm (V i b - 1) < polydiscRadius L
  eq_mean : ∀ i < j, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    V (i + 1) c = PeriodicLattice.complexBlockAverage (V i) c
structure IsHolomorphicRepresentation (j : ℕ) (c : Edge L n k j) (U : Edge L n k 0 → ComplexMatrix2)
    (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop where
  nonempty : F.Nonempty
  positive : ∀ b ∈ F, b.IsPositivelyOriented
  isOpen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct.unimodularPi F) O
  mem : edgeEntries F U ∈ O
  holomorphic : ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    GroupLieProduct.IsHolomorphicToUnimodular β (GroupLieProduct.asGroupFactors '' O)
      fun p => f fun b => p (.inl b)
  eq_some : ∀ W ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup, edgeEntries F W ∈ O →
    levelwiseMean W j c = some (f (edgeEntries F W))
def RepresentsAlongCurves (j : ℕ) (c : Edge L n k j) (U : Edge L n k 0 → ComplexMatrix2)
    (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ B : Edge L n k 0 → ComplexMatrix2,
    (∀ b : Edge L n k 0, b.IsPositivelyOriented → B b ∈ PeriodicLattice.complexLieAlgebra) →
    ∀ᶠ t : ℂ in 𝓝 0, expChartPoint F (t • B) U ∈ O ∧
      levelwiseMean (PeriodicLattice.expTwist (t • B) U) j c = some (f (expChartPoint F (t • B) U))
def IteratesDefinedNearIdentity (L n k : ℕ) : Prop :=
  EventuallyNearIdentity (fieldSpace L n k 0) fun U => ∀ i ≤ k,
    smoothingIter L n k i U ∈ fieldSpace L n k i ∧
    (∀ b, ComplexMatrix2.operatorNorm (smoothingIter L n k i U b - 1) < polydiscRadius L) ∧
    (∀ c, levelwiseMean U i c = some (smoothingIter L n k i U c)) ∧
    ∀ B ∈ edgeFormSpace L n k 0, ∀ c : Edge L n k i, c.IsPositivelyOriented →
      HasDerivAt (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k i
          (PeriodicLattice.expTwist ((t : ℂ) • B) U) c * (smoothingIter L n k i U c)⁻¹))
        (Complex.I • leftDifferential (smoothingIter L n k i) U B c) 0 ∧
      ∀ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsHolomorphicRepresentation i c U F O f →
        HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
            (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹))
          (Complex.I • leftDifferential (smoothingIter L n k i) U B c) 0
structure PeriodicConditions (L n k : ℕ) : Prop where
  agree_near_identity : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        RealAndComplexAgreeNearIdentity j c y x
  sequence_is_levelwise : ∀ j ≤ k, ∀ V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2, IsMeanSequence j V →
    ∀ i ≤ j, ∀ c : Edge L n k i, levelwiseMean (V 0) i c = some (V i c)
  exists_representation : ∀ j ≤ k, ∀ (c : Edge L n k j),
    ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup, IsDefinedAt U j c →
      ∃ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsHolomorphicRepresentation j c U F O f
  represents_along_curves : ∀ j ≤ k, ∀ (c : Edge L n k j),
    ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      ∀ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsHolomorphicRepresentation j c U F O f → RepresentsAlongCurves j c U F O f
  iterate_tendsto : ∀ i ≤ k, Tendsto (smoothingIter L n k i)
    (𝓝[fieldSpace L n k 0] fun _ => 1) (𝓝[fieldSpace L n k i] fun _ => 1)
  iterates_defined : IteratesDefinedNearIdentity L n k
end Periodic
namespace Unbounded
variable {L k : ℕ}
def expChartPoint {j : ℕ} (F : Finset (FullSpace.Edge L k j)) (X U : FullSpace.Edge L k j → ComplexMatrix2) :
    F → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • X b) * U b
def meanOfDefined {i : ℕ} (w : FullSpace.Edge L k i → Option ComplexMatrix2)
    (c : FullSpace.Edge L k (i + 1)) : Option ComplexMatrix2 :=
  open Classical in
  if (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c, (w b).isSome) ∧
      valuesOrOne w ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c then
    some (FullSpace.complexSmoothing L (valuesOrOne w) c)
  else none
def levelwiseMean (W : FullSpace.Edge L k 0 → ComplexMatrix2) :
    (i : ℕ) → FullSpace.Edge L k i → Option ComplexMatrix2
  | 0 => fun c => some (W c)
  | i + 1 => fun c =>
    open Classical in
    if c.IsPositivelyOriented then meanOfDefined (levelwiseMean W i) c
    else (meanOfDefined (levelwiseMean W i) c.opposite).map (·⁻¹)
def IsDefinedAt (W : FullSpace.Edge L k 0 → ComplexMatrix2) (i : ℕ) (c : FullSpace.Edge L k i) : Prop :=
  (levelwiseMean W i c).isSome
def RealAndComplexAgreeAt (j : ℕ) (V : FullSpace.Edge L k j → ComplexMatrix2)
    (c : FullSpace.Edge L k (j + 1)) (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j) :
    Prop :=
  V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c ∧
  V ∈ FullSpace.smoothingDomain L k j ∧
  ∀ B ∈ FullSpace.edgeFormSpace (meshAt L k j),
    (∀ᶠ t : ℝ in 𝓝 0, FullSpace.expTwist ((t : ℂ) • B) V ∈
      FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c) ∧
    (∃ D : ComplexMatrix2, HasDerivAt (fun t : ℝ =>
      FullSpace.smoothingMap L k j (FullSpace.expTwist ((t : ℂ) • B) V) c) D 0) ∧
    ∃ D : ComplexMatrix2, HasDerivAt (fun t : ℝ =>
      FullSpace.complexContourMean L (FullSpace.expTwist ((t : ℂ) • B) V) y x) D 0
structure IsMeanSequence (j : ℕ) (V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2) : Prop where
  mem_fields : ∀ i ≤ j, V i ∈ FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup
  norm_sub_one_lt : ∀ i < j, ∀ b, ComplexMatrix2.operatorNorm (V i b - 1) < polydiscRadius L
  eq_mean : ∀ i < j, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
    V (i + 1) c = FullSpace.complexSmoothing L (V i) c
structure IsHolomorphicRepresentation (j : ℕ) (c : FullSpace.Edge L k j)
    (U : FullSpace.Edge L k 0 → ComplexMatrix2) (F : Finset (FullSpace.Edge L k 0))
    (O : Set (F → ComplexMatrix2)) (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop where
  finite_edges : FullSpace.IsFinitePositiveEdgeSet F
  isOpen : ComplexMatrix2.IsRelativelyOpen
    (FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F) O
  mem : FullSpace.restrictToEdges F U ∈ O
  holomorphic : ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    GroupLieProduct.IsHolomorphicToUnimodular β (GroupLieProduct.asGroupFactors '' O)
      fun p => f fun b => p (.inl b)
  eq_some : ∀ W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
    FullSpace.restrictToEdges F W ∈ O →
    levelwiseMean W j c = some (f (FullSpace.restrictToEdges F W))
def RepresentsAlongCurves (j : ℕ) (c : FullSpace.Edge L k j) (U : FullSpace.Edge L k 0 → ComplexMatrix2)
    (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ B : FullSpace.Edge L k 0 → ComplexMatrix2,
    (∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented → B b ∈ PeriodicLattice.complexLieAlgebra) →
    ∀ᶠ t : ℂ in 𝓝 0, expChartPoint F (t • B) U ∈ O ∧
      levelwiseMean (FullSpace.expTwist (t • B) U) j c = some (f (expChartPoint F (t • B) U))
structure UnboundedConditions (L k : ℕ) : Prop where
  agree_near_identity : ∀ j < k,
    FullSpace.EventuallyNearIdentity (FullSpace.fieldSpace L k j) fun V =>
      ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))),
          ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y, RealAndComplexAgreeAt j V c y x
  sequence_is_levelwise : ∀ j ≤ k, ∀ V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2,
    IsMeanSequence j V →
    ∀ i ≤ j, ∀ c : FullSpace.Edge L k i, levelwiseMean (V 0) i c = some (V i c)
  exists_representation : ∀ j ≤ k, ∀ (c : FullSpace.Edge L k j),
    ∀ U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup, IsDefinedAt U j c →
      ∃ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsHolomorphicRepresentation j c U F O f
  represents_along_curves : ∀ j ≤ k, ∀ (c : FullSpace.Edge L k j),
    ∀ U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      ∀ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        IsHolomorphicRepresentation j c U F O f → RepresentsAlongCurves j c U F O f
end Unbounded
def LevelwiseMeansHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → PeriodicConditions L n k) ∧ Unbounded.UnboundedConditions L k
end YangMills.Construction.Tower.LevelwiseMeans
end
