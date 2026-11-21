import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.InfiniteLattice.TorusMeasuresConnectedFunctionsAndCentredMomentsOfTheInfiniteLattice
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AtCutoff
open YangMills.Construction.ReflectionPositivity.AxisMirror
section Links
variable (D : MirrorData)
abbrev FieldSpace : Type := InfiniteLattice.GaugeField D.mesh
end Links
section Tuples
variable (D : MirrorData) (E : Ambient)
def IsPosSeparated (A B : Set (E.Point D)) : Prop := Ambient.setDist D E A B ≠ 0
def PairwisePosSeparated {n : ℕ} (A : Fin n → Set (E.Point D)) : Prop :=
  Pairwise fun i k => IsPosSeparated D E (A i) (A k)
theorem pairwisePosSeparated_iff {n : ℕ} (A : Fin n → Set (E.Point D)) :
    PairwisePosSeparated D E A ↔
      Pairwise fun i k => 0 < Ambient.setDist D E (A i) (A k) := by
  simp only [PairwisePosSeparated, IsPosSeparated, pos_iff_ne_zero]
abbrev cOneIn (A : Set (E.Point D)) : Set (E.Point D → ℝ) := Ambient.compactC1SuppIn D E A
variable {D E}
variable (D E)
end Tuples
section State
variable {a : ℝ}
def boundedBorelCompactSupport : Set (InfiniteLattice.AmbientSpace → ℝ) :=
  {f | InfiniteLattice.IsBoundedBorelCompactlySupported f}
def connectedPartitionSum (ν : MeasureTheory.Measure (InfiniteLattice.GaugeField a))
    {q : ℕ} (h : Fin q → InfiniteLattice.AmbientSpace → ℝ) : ℂ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts,
    InfiniteLattice.PeriodicTorusMeasures.measureConnectedFunction ν (Cumulants.restrictTuple h J)
end State
end YangMills.Construction.AtCutoff
end
