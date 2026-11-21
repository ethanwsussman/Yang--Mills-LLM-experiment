import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def Link.LiesIn (b : Link a) (S : Set AmbientSpace) : Prop :=
  (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S
theorem Link.mem_linksWithin_iff_liesIn (b : Link a) (S : Set AmbientSpace) :
    b ∈ (linksWithin S : Set (Link a)) ↔ b.LiesIn S :=
  Iff.rfl
def boundedRegionObservables (a : ℝ) (S : Set AmbientSpace) : Set (GaugeField a → ℂ) :=
  {F | IsBoundedObservable F ∧ IsRegionMeasurable S F}
def localRegionObservables (a : ℝ) (S : Set AmbientSpace) : Set (GaugeField a → ℂ) :=
  ⋃ Q ∈ {Q : Set AmbientSpace | Bornology.IsBounded Q}, boundedRegionObservables a (S ∩ Q)
end InfiniteLattice
end YangMills.Construction
