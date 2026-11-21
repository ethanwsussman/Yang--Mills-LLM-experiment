import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Haar
def IsNormalizedHaar {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ g : H, μ.map (fun h => g * h) = μ
def normalizedHaar (H : Type*) [Group H] [MeasurableSpace H] : Measure H :=
  Classical.epsilon IsNormalizedHaar
def NormalizedHaarUniqueInvariant : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TopologicalSpace.MetrizableSpace H] [MeasurableSpace H] [BorelSpace H],
    (∃! μ : Measure H, IsNormalizedHaar μ) ∧
      IsNormalizedHaar (normalizedHaar H) ∧
      (∀ g : H, (normalizedHaar H).map (fun h => h * g) = normalizedHaar H) ∧
      (normalizedHaar H).map (fun h => h⁻¹) = normalizedHaar H
def NormalizedHaarPositiveOnOpen : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TopologicalSpace.MetrizableSpace H] [MeasurableSpace H] [BorelSpace H] (U : Set H),
    IsOpen U → U.Nonempty → 0 < normalizedHaar H U
def NormalizedHaarFinitePower : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TopologicalSpace.MetrizableSpace H] [MeasurableSpace H] [BorelSpace H] (S : Type) [Fintype S],
    (IsTopologicalGroup (S → H) ∧ CompactSpace (S → H) ∧
        TopologicalSpace.MetrizableSpace (S → H)) ∧
      borel (S → H) = MeasurableSpace.pi ∧
      normalizedHaar (S → H) = Measure.pi fun _ : S => normalizedHaar H
def NormalizedHaarSpecialUnitary : Prop :=
  (IsTopologicalGroup YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary ∧
      CompactSpace YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary ∧
      TopologicalSpace.MetrizableSpace YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) ∧
    normalizedHaar YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary =
      YangMills.Construction.Matrices.ComplexMatrix2.haarProb
def NormalizedHaarFacts : Prop :=
  NormalizedHaarUniqueInvariant ∧ NormalizedHaarPositiveOnOpen ∧
    NormalizedHaarFinitePower ∧ NormalizedHaarSpecialUnitary
end YangMills.Construction.Haar
end
