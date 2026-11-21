import YangMills.Construction.HilbertSpace.SemidefiniteFormHilbertSpace
import YangMills.Construction.InfiniteLattice.FormAtALatticeMirrorGivenWithANormal
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace NormalHyperplane
open InfiniteLattice (GaugeField localRegionObservables boundedRegionObservables regionSigma_mono)
open FormCompletion
def localObservableSubmodule (a : ℝ) (S : Set InfiniteLattice.AmbientSpace) :
    Submodule ℂ (GaugeField a → ℂ) where
  carrier := localRegionObservables a S
  add_mem' := by
    intro F G hF hG
    obtain ⟨R, hR, bF, mF⟩ := Set.mem_iUnion₂.1 hF
    obtain ⟨R', hR', bG, mG⟩ := Set.mem_iUnion₂.1 hG
    refine Set.mem_iUnion₂.2 ⟨R ∪ R', Set.mem_ofPred.2 ((Set.mem_ofPred.1 hR).union (Set.mem_ofPred.1 hR')), bF.add bG, ?_⟩
    exact Measurable.add
      (mF.mono (regionSigma_mono (Set.inter_subset_inter_right S Set.subset_union_left)) le_rfl)
      (mG.mono (regionSigma_mono (Set.inter_subset_inter_right S Set.subset_union_right)) le_rfl)
  zero_mem' := Set.mem_iUnion₂.2
    ⟨∅, Set.mem_ofPred.2 Bornology.isBounded_empty, ⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩
  smul_mem' := by
    intro c F hF
    obtain ⟨R, hR, bF, mF⟩ := Set.mem_iUnion₂.1 hF
    exact Set.mem_iUnion₂.2 ⟨R, hR, bF.const_smul c, Measurable.const_smul mF c⟩
variable {a : ℝ}
abbrev upperObservables (a : ℝ) (H : NormalHyperplane) :
    Submodule ℂ (GaugeField a → ℂ) :=
  localObservableSubmodule a H.upperHalfSpace
def upperReflectionForm {H : NormalHyperplane} (hH : H.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (F G : upperObservables a H) : ℂ :=
  reflectionForm hH ν ⟨F.1, F.2⟩ ⟨G.1, G.2⟩
abbrev MirrorHilbertSpace {H : NormalHyperplane} (hH : H.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Type :=
  FormHilbertSpace (upperReflectionForm hH ν)
def mirrorClass {H : NormalHyperplane} (hH : H.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (F : upperObservables a H) : MirrorHilbertSpace hH ν :=
  classVec (upperReflectionForm hH ν) F
end NormalHyperplane
end LatticeConventions
end YangMills.Construction
end
