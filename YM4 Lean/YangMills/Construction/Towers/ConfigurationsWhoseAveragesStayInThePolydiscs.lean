import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevel
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower.MeanStableFields
section Periodic
variable {L n k : ℕ}
def IsMeanSequenceFrom (l : ℕ) (W : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
    (V : ∀ i : ℕ, Tower.Edge L n k i → Matrices.ComplexMatrix2) : Prop :=
  Tower.LevelwiseMeans.IsMeanSequence l V ∧ V 0 = W
def meanStableFields (L n k l : ℕ) : Set (Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :=
  {W | ∃ V : ∀ i : ℕ, Tower.Edge L n k i → Matrices.ComplexMatrix2, IsMeanSequenceFrom l W V}
def levelwiseMeanAt (j : ℕ) (c : Tower.Edge L n k j)
    (W : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.levelwiseMean W j) c
def fieldsNearOne (L n k i : ℕ) : Set (Tower.Edge L n k i → Matrices.ComplexMatrix2) :=
  {V | V ∈ Tower.fieldsIn L n k i PeriodicLattice.complexGaugeGroup ∧
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < Tower.polydiscRadius L}
def IsHolomorphicOnFields {i : ℕ} (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (D : Set (Tower.Edge L n k i → Matrices.ComplexMatrix2))
    (h : (Tower.Edge L n k i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  Tower.IsOpenFieldSet PeriodicLattice.complexGaugeGroup D ∧ ∃ _ : Fintype (Tower.PositiveEdge L n k i),
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular β
      (Matrices.GroupLieProduct.asGroupFactors '' (Tower.restrictToPositiveEdges '' D))
      fun p => h (Tower.fieldOfPositiveValues fun b => p (.inl b))
structure MeanStableConditions (L n k : ℕ) : Prop where
  unique : ∀ l ≤ k, ∀ (W : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
    (V V' : ∀ i : ℕ, Tower.Edge L n k i → Matrices.ComplexMatrix2),
    IsMeanSequenceFrom l W V → IsMeanSequenceFrom l W V' → ∀ i ≤ l, V i = V' i
  eq_levelwiseMean : ∀ l ≤ k, ∀ (W : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
    (V : ∀ i : ℕ, Tower.Edge L n k i → Matrices.ComplexMatrix2),
    IsMeanSequenceFrom l W V → ∀ i ≤ l, ∀ c : Tower.Edge L n k i,
      Tower.LevelwiseMeans.levelwiseMean W i c = some (V i c)
  small_perturbation : ∀ U ∈ meanStableFields L n k k, ∀ F : Finset (Tower.Edge L n k 0),
    (∀ b ∈ F, b.IsPositivelyOriented) → ∃ ε : ℝ, 0 < ε ∧
      ∀ W ∈ Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
        (∀ b : Tower.Edge L n k 0, b.IsPositivelyOriented → b ∉ F → W b = U b) →
        (∀ b ∈ F, Matrices.ComplexMatrix2.operatorNorm (W b - U b) < ε) →
          W ∈ meanStableFields L n k k
  isOpen : Tower.IsOpenFieldSet PeriodicLattice.complexGaugeGroup (meanStableFields L n k k)
  holomorphic_mean : ∀ j ≤ k, ∀ c : Tower.Edge L n k j, c.IsPositivelyOriented →
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      IsHolomorphicOnFields β (meanStableFields L n k k) (levelwiseMeanAt j c)
  mem_polydisc : ∀ i < k, ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ fieldsNearOne L n k i, V ∈ Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c
  isOpen_nearOne : ∀ i < k,
    Tower.IsOpenFieldSet PeriodicLattice.complexGaugeGroup (fieldsNearOne L n k i)
  holomorphic_smoothing : ∀ i < k, ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      IsHolomorphicOnFields β (fieldsNearOne L n k i)
        fun V => PeriodicLattice.complexBlockAverage V c
end Periodic
namespace Infinite
variable {L k : ℕ}
def IsMeanSequenceFrom (l : ℕ) (W : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)
    (V : ∀ i : ℕ, Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2) : Prop :=
  Tower.LevelwiseMeans.Unbounded.IsMeanSequence l V ∧ V 0 = W
def meanStableFields (L k l : ℕ) : Set (Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :=
  {W | ∃ V : ∀ i : ℕ, Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2,
    IsMeanSequenceFrom l W V}
def levelwiseMeanAt (j : ℕ) (c : Tower.FullSpace.Edge L k j)
    (W : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.Unbounded.levelwiseMean W j) c
def fieldsNearOne (L k i : ℕ) : Set (Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2) :=
  {V | V ∈ Tower.FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup ∧
    ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < Tower.polydiscRadius L}
def pointOfFinset {i : ℕ} (c : Tower.FullSpace.Edge L k (i + 1))
    (F : Finset (Tower.FullSpace.Edge L k i))
    (hF : (F : Set (Tower.FullSpace.Edge L k i)) =
      Tower.DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c)
    (w : F → Matrices.ComplexMatrix2) :
    Tower.DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c →
      Matrices.ComplexMatrix2 :=
  fun b => w ⟨b.1, Finset.mem_coe.mp (hF.symm ▸ b.2)⟩
def polydiscOnFinset {i : ℕ} (c : Tower.FullSpace.Edge L k (i + 1))
    (F : Finset (Tower.FullSpace.Edge L k i))
    (hF : (F : Set (Tower.FullSpace.Edge L k i)) =
      Tower.DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c) :
    Set (F → Matrices.ComplexMatrix2) :=
  pointOfFinset c F hF ⁻¹'
    Tower.DoubleBlockPolydisc.Infinite.polydiscPositive L k i (Tower.polydiscRadius L) c
def smoothingOnFinset {i : ℕ} (c : Tower.FullSpace.Edge L k (i + 1))
    (F : Finset (Tower.FullSpace.Edge L k i))
    (hF : (F : Set (Tower.FullSpace.Edge L k i)) =
      Tower.DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c)
    (w : F → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Tower.FullSpace.complexSmoothing L
    (Tower.DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (pointOfFinset c F hF w)) c
structure MeanStableConditions (L k : ℕ) : Prop where
  unique : ∀ l ≤ k, ∀ (W : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)
    (V V' : ∀ i : ℕ, Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2),
    IsMeanSequenceFrom l W V → IsMeanSequenceFrom l W V' → ∀ i ≤ l, V i = V' i
  eq_levelwiseMean : ∀ l ≤ k, ∀ (W : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)
    (V : ∀ i : ℕ, Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2),
    IsMeanSequenceFrom l W V → ∀ i ≤ l, ∀ c : Tower.FullSpace.Edge L k i,
      Tower.LevelwiseMeans.Unbounded.levelwiseMean W i c = some (V i c)
  small_perturbation : ∀ U ∈ meanStableFields L k k, ∀ F : Finset (Tower.FullSpace.Edge L k 0),
    (∀ b ∈ F, b.IsPositivelyOriented) → ∃ ε : ℝ, 0 < ε ∧
      ∀ W ∈ Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
        (∀ b : Tower.FullSpace.Edge L k 0, b.IsPositivelyOriented → b ∉ F → W b = U b) →
        (∀ b ∈ F, Matrices.ComplexMatrix2.operatorNorm (W b - U b) < ε) →
          W ∈ meanStableFields L k k
  isFinitelyOpen :
    Tower.FullSpace.IsFinitelyOpen PeriodicLattice.complexGaugeGroup (meanStableFields L k k)
  holomorphic_mean : ∀ j ≤ k, ∀ c : Tower.FullSpace.Edge L k j, c.IsPositivelyOriented →
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Tower.FullSpace.IsFinitelyHolomorphic β Coordinates.ComplexCoordinates.matrixEquiv
        (meanStableFields L k k) (levelwiseMeanAt j c)
  exists_representation : ∀ j ≤ k, ∀ c : Tower.FullSpace.Edge L k j, c.IsPositivelyOriented →
    ∀ U ∈ meanStableFields L k k,
      ∃ (F : Finset (Tower.FullSpace.Edge L k 0)) (O : Set (F → Matrices.ComplexMatrix2))
        (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
        Tower.LevelwiseMeans.Unbounded.IsHolomorphicRepresentation j c U F O f
  representation_spec : ∀ j ≤ k, ∀ c : Tower.FullSpace.Edge L k j, c.IsPositivelyOriented →
    ∀ U ∈ meanStableFields L k k,
      ∀ (F : Finset (Tower.FullSpace.Edge L k 0)) (O : Set (F → Matrices.ComplexMatrix2))
        (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
        Tower.LevelwiseMeans.Unbounded.IsHolomorphicRepresentation j c U F O f →
        Tower.FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
            (meanStableFields L k k) (levelwiseMeanAt j c) U F O f ∧
          ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
            Matrices.GroupLieProduct.IsHolomorphicToCoords β
              Coordinates.ComplexCoordinates.matrixEquiv
              (Matrices.GroupLieProduct.asGroupFactors '' O) fun p => f fun b => p (.inl b)
  mem_polydisc : ∀ i < k, ∀ c : Tower.FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ fieldsNearOne L k i,
      V ∈ Tower.FullSpace.nearIdentityPolydisc L k i (Tower.polydiscRadius L) c
  isFinitelyOpen_nearOne : ∀ i < k,
    Tower.FullSpace.IsFinitelyOpen PeriodicLattice.complexGaugeGroup (fieldsNearOne L k i)
  holomorphic_smoothing : ∀ i < k, ∀ c : Tower.FullSpace.Edge L k (i + 1),
    c.IsPositivelyOriented →
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Tower.FullSpace.IsFinitelyHolomorphic β Coordinates.ComplexCoordinates.matrixEquiv
        (fieldsNearOne L k i) fun V => Tower.FullSpace.complexSmoothing L V c
  polydisc_presentation : ∀ i < k, ∀ c : Tower.FullSpace.Edge L k (i + 1),
    c.IsPositivelyOriented →
    ∃ (F : Finset (Tower.FullSpace.Edge L k i))
      (hF : (F : Set (Tower.FullSpace.Edge L k i)) =
        Tower.DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c),
      ∀ U ∈ fieldsNearOne L k i,
        Tower.FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup (fieldsNearOne L k i)
          (fun V => Tower.FullSpace.complexSmoothing L V c) U F (polydiscOnFinset c F hF)
          (smoothingOnFinset c F hF)
end Infinite
def MeanStableFieldsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → MeanStableConditions L n k) ∧ Infinite.MeanStableConditions L k
end Tower.MeanStableFields
end YangMills.Construction
end
