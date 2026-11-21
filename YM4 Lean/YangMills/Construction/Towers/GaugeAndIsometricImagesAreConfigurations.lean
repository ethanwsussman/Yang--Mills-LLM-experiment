import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
namespace Tower
namespace GaugeAndSymmetryImages
def OnPeriodicSide (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → Matrices.ComplexMatrix2) (g : Vertex L n k j → Matrices.ComplexMatrix2)
    (s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n),
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U →
    PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup g →
    IsDistancePreserving s → MapsSublatticeOnto k j s →
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ
        (PeriodicLattice.gaugeTransform g U) ∧
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ
        (pushField (k := k) (j := j) s U) ∧
      (U ∈ fieldSpace L n k j → g ∈ gaugeGroupAt L n k j →
        PeriodicLattice.gaugeTransform g U ∈ fieldSpace L n k j) ∧
      (U ∈ fieldSpace L n k j →
        pushField (k := k) (j := j) s U ∈ fieldSpace L n k j)
def OnFullSpace (L k j : ℕ) : Prop :=
  ∀ (U : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (g : FullSpace.Vertex L k j → Matrices.ComplexMatrix2)
    (s : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace),
    FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U →
    (∀ x, g x ∈ PeriodicLattice.complexGaugeGroup) →
    FullSpace.IsDistancePreserving s → FullSpace.MapsSublatticeOnto (meshAt L k j) s →
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.gaugeAct g U) ∧
      FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.pushField s U) ∧
      (U ∈ FullSpace.fieldSpace L k j → g ∈ FullSpace.gaugeGroupAt L k j →
        FullSpace.gaugeAct g U ∈ FullSpace.fieldSpace L k j) ∧
      (U ∈ FullSpace.fieldSpace L k j →
        FullSpace.pushField s U ∈ FullSpace.fieldSpace L k j)
def statement : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    (∀ n : ℕ, 0 < n → OnPeriodicSide L n k j) ∧ OnFullSpace L k j
end GaugeAndSymmetryImages
end Tower
end YangMills.Construction
