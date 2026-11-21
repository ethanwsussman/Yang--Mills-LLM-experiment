import Mathlib
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.InvertibleContourVariables

section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Kernels
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
def IsBorelMeasurable [TopologicalSpace X] [TopologicalSpace Y] (φ : X → Y) : Prop :=
  @Measurable X Y (borel X) (borel Y) φ
end YangMills.Construction.Kernels
end
end

open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def caseSet (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) (κ : BlockAverageCase) :
    Set (BondAtLevel L m K k → Matrices.ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsAtLevel L m K k ∧ blockAverageCase ω U c = κ}
def IsBorelGaugeFieldSet (k : ℕ) (S : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) : Prop :=
  S ⊆ gaugeFieldsAtLevel L m K k ∧
    MeasurableSet[borel (gaugeFieldsAtLevel L m K k)]
      ((↑) ⁻¹' S : Set (gaugeFieldsAtLevel L m K k))
def BlockAverageAnalyticNearOne (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  (∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
      IsRegularAveragingCase ω U c) ∧
    ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
      Matrices.ComplexMatrix2.IsRealAnalyticBetween
        (fun _ : PositivelyOrientedBond L m (levelDepth K k) =>
          Matrices.ComplexMatrix2.FactorKind.group)
        (fun _ : Fin 1 => Matrices.ComplexMatrix2.FactorKind.group)
        (valuesOnPositiveBonds ''
          (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)))
        fun v _ => blockAverage ω (fieldOfPositiveValues v) c
def CaseSetsMeasurable (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ κ : BlockAverageCase, IsBorelGaugeFieldSet k (caseSet ω k c κ)
def BlockAverageContinuousOnCaseSets (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ κ : BlockAverageCase,
    ContinuousOn (fun U : BondAtLevel L m K k → Matrices.ComplexMatrix2 => blockAverage ω U c)
      (caseSet ω k c κ)
def BlockAverageBorel (L m K : ℕ) (ω : ℝ) (k : ℕ) : Prop :=
  ∃ h : MapsTo (blockAverageStep (L := L) (m := m) (K := K) ω k) (gaugeFieldsAtLevel L m K k)
      (gaugeFieldsAtLevel L m K (k + 1)),
    Kernels.IsBorelMeasurable (h.restrict _ _ _)
end YangMills.Construction.PeriodicLattice
end
