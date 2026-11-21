import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace Matrices.ComplexMatrix2
def entrywiseTopology : TopologicalSpace Matrices.ComplexMatrix2 :=
  TopologicalSpace.induced Coordinates.ComplexCoordinates.matrixEquiv inferInstance
def specialUnitaryEntrywiseTopology : TopologicalSpace Matrices.ComplexMatrix2.specialUnitary :=
  TopologicalSpace.induced
    (Subtype.val : Matrices.ComplexMatrix2.specialUnitary → Matrices.ComplexMatrix2)
    Matrices.ComplexMatrix2.entrywiseTopology
end Matrices.ComplexMatrix2
namespace PeriodicLattice.GaugeFieldSpace
def plaquetteCount (L m K : ℕ) : ℕ := Nat.card (Plaquette L m (K : ℤ))
def productTopology (L m K : ℕ) : TopologicalSpace (compactGaugeFields L m (K : ℤ)) :=
  TopologicalSpace.induced (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := 0))
    (@Pi.topologicalSpace (PositivelyOrientedBond L m (levelDepth K 0))
      (fun _ => Matrices.ComplexMatrix2.specialUnitary)
      fun _ => Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology)
def CompactMetrizableFieldSpace (L m K : ℕ) : Prop :=
  Finite (Bond L m (K : ℤ)) ∧ Finite (Plaquette L m (K : ℤ)) ∧
    Function.Bijective (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := 0)) ∧
    gaugeFieldsAtLevelTopology L m K 0 = productTopology L m K ∧
    @CompactSpace _ (productTopology L m K) ∧
    @TopologicalSpace.MetrizableSpace _ (productTopology L m K) ∧
    ∀ b : Bond L m (K : ℤ),
      @Continuous (compactGaugeFields L m (K : ℤ)) Matrices.ComplexMatrix2
        (productTopology L m K) Matrices.ComplexMatrix2.entrywiseTopology fun U => U.1 b
def BoltzmannWeightBounds (L m K : ℕ) (β : ℝ) : Prop :=
  (∀ p : Plaquette L m (K : ℤ),
    @Continuous (compactGaugeFields L m (K : ℤ)) ℝ (productTopology L m K) _
      fun U => plaquetteCost U.1 p) ∧
  @Continuous (compactGaugeFields L m (K : ℤ)) ℝ (productTopology L m K) _
    (fun U => wilsonAction U.1) ∧
  @Continuous (compactGaugeFields L m (K : ℤ)) ℝ (productTopology L m K) _
    (fun U => boltzmannWeight β U.1) ∧
  ∀ U ∈ compactGaugeFields L m (K : ℤ),
    0 ≤ wilsonAction U ∧ wilsonAction U ≤ 2 * (plaquetteCount L m K : ℝ) ∧
      Real.exp (-2 * β * (plaquetteCount L m K : ℝ)) ≤ boltzmannWeight β U ∧
      boltzmannWeight β U ≤ 1
def PartitionFunctionBounds (L m K : ℕ) (β : ℝ) : Prop :=
  Integrable (boltzmannWeight β) (productHaarMeasure L m (K : ℤ)) ∧
    Real.exp (-2 * β * (plaquetteCount L m K : ℝ)) ≤ partitionFunction L m K β ∧
    partitionFunction L m K β ≤ 1
def SpecialUnitaryTopologyUnique : Prop :=
  (∀ τ : TopologicalSpace Matrices.ComplexMatrix2.specialUnitary,
    @IsTopologicalGroup Matrices.ComplexMatrix2.specialUnitary τ _ →
      @CompactSpace Matrices.ComplexMatrix2.specialUnitary τ →
      @TopologicalSpace.MetrizableSpace Matrices.ComplexMatrix2.specialUnitary τ →
      τ = Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology) ∧
  (inferInstance : TopologicalSpace Matrices.ComplexMatrix2.specialUnitary) =
    Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology ∧
  @IsTopologicalGroup Matrices.ComplexMatrix2.specialUnitary
    Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology _ ∧
  @CompactSpace Matrices.ComplexMatrix2.specialUnitary
    Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology ∧
  @TopologicalSpace.MetrizableSpace Matrices.ComplexMatrix2.specialUnitary
    Matrices.ComplexMatrix2.specialUnitaryEntrywiseTopology
def FieldSpaceAndPartitionBounds : Prop :=
  ∀ s : Conventions.StandingParameters,
    CompactMetrizableFieldSpace s.L s.m s.K ∧
      (∀ β : ℝ, 0 < β →
        BoltzmannWeightBounds s.L s.m s.K β ∧ PartitionFunctionBounds s.L s.m s.K β) ∧
      SpecialUnitaryTopologyUnique
end PeriodicLattice.GaugeFieldSpace
end YangMills.Construction
