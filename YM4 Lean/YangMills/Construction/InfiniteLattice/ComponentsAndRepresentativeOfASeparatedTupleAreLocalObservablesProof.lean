import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.InfiniteLattice.ComponentsAndRepresentativeOfASeparatedTupleAreLocalObservables
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CenteredRepresentatives.EntriesAreLocal
open InfiniteLattice DisjointTuples
variable {a : ℝ}
theorem isRegionMeasurable_of_subset {S T : Set AmbientSpace} (hST : S ⊆ T) {A : GaugeField a → ℂ}
    (hA : IsRegionMeasurable S A) : IsRegionMeasurable T A := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
def IsLocalBounded (A : GaugeField a → ℂ) : Prop := IsBoundedObservable A ∧ IsLocalObservable A
theorem isLocalBounded_const (z : ℂ) :
    IsLocalBounded (fun _ : GaugeField a => z) :=
  ⟨⟨measurable_const, ‖z‖, fun _ => le_rfl⟩, ∅, Bornology.isBounded_empty, measurable_const⟩
theorem IsLocalBounded.mul {A B : GaugeField a → ℂ} (hA : IsLocalBounded A)
    (hB : IsLocalBounded B) : IsLocalBounded (fun U => A U * B U) := by
  obtain ⟨⟨mA, C, hC⟩, S, bS, lA⟩ := hA
  obtain ⟨⟨mB, D, hD⟩, T, bT, lB⟩ := hB
  refine ⟨⟨mA.mul mB, C * D, fun U => ?_⟩, S ∪ T, bS.union bT, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  · have hA' : IsRegionMeasurable (S ∪ T) A := isRegionMeasurable_of_subset Set.subset_union_left lA
    have hB' : IsRegionMeasurable (S ∪ T) B := isRegionMeasurable_of_subset Set.subset_union_right lB
    exact Measurable.mul hA' hB'
theorem IsLocalBounded.sub_const {A : GaugeField a → ℂ} (hA : IsLocalBounded A) (z : ℂ) :
    IsLocalBounded (fun U => A U - z) := by
  obtain ⟨⟨mA, C, hC⟩, S, bS, lA⟩ := hA
  refine ⟨⟨mA.sub_const z, C + ‖z‖, fun U => (norm_sub_le _ _).trans ?_⟩, S, bS, ?_⟩
  · exact add_le_add (hC U) le_rfl
  · exact Measurable.sub_const lA z
theorem isLocalBounded_listProd {ι : Type*} (F : ι → GaugeField a → ℝ) (μ : ι → ℝ) (l : List ι)
    (hl : ∀ f ∈ l, IsLocalBounded fun U => ((F f U : ℝ) : ℂ)) :
    IsLocalBounded fun U => (((l.map fun f => F f U - μ f).prod : ℝ) : ℂ) := by
  induction l with
  | nil => simpa using isLocalBounded_const (a := a) 1
  | cons f l ih =>
    have hhead := (hl f List.mem_cons_self).sub_const (μ f : ℂ)
    have htail := ih fun g hg => hl g (List.mem_cons_of_mem f hg)
    simpa using hhead.mul htail
theorem integrable_of_isBoundedObservable_ofReal (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    {F : GaugeField a → ℝ} (hF : IsBoundedObservable fun U => ((F U : ℝ) : ℂ)) : Integrable F ν := by
  obtain ⟨hm, C, hC⟩ := hF
  have hFm : Measurable F := by
    have hre : (Complex.re ∘ fun U => ((F U : ℝ) : ℂ)) = F := by
      funext U
      simp
    rw [← hre]
    exact Complex.measurable_re.comp hm
  refine Integrable.of_bound hFm.aestronglyMeasurable C (Filter.Eventually.of_forall fun U => ?_)
  simpa using hC U
theorem mem_compactTestFunctions (X : DisjointTuple) {f : RealFun} (hf : f ∈ X.1) :
    f ∈ compactTestFunctions := by
  obtain ⟨hsmooth, hsupp⟩ := X.2.1 f hf
  have hcont : Continuous f := ContDiff.continuous hsmooth
  exact ⟨hcont.measurable, hcont.bounded_above_of_compact_support hsupp, hsupp⟩
theorem statement_of_smearedEnergy (hmain : SmearedEnergyAndSymmetryAction.Main) : Statement := by
  intro L K hL ν hν X
  have hpos : 0 < PeriodicLattice.meshSize L (K : ℤ) := zpow_pos (Nat.cast_pos.mpr hL) _
  have hreal := (hmain _ hpos).1.2
  have hentry : ∀ f ∈ X.1, f ∈ compactTestFunctions ∧
      {p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) | f p.center ≠ 0}.Finite ∧
      Integrable (smearedEnergy f) ν ∧
      IsBoundedObservable (fun U : GaugeFieldAtScale L K => ((smearedEnergy f U : ℝ) : ℂ)) ∧
      IsLocalObservable (fun U : GaugeFieldAtScale L K => ((smearedEnergy f U : ℝ) : ℂ)) := by
    intro f hf
    have hmem := mem_compactTestFunctions X hf
    obtain ⟨hfin, -, hobs, hloc⟩ := hreal f hmem
    exact ⟨hmem, hfin, integrable_of_isBoundedObservable_ofReal ν hobs, hobs, hloc⟩
  have hprod := isLocalBounded_listProd (a := PeriodicLattice.meshSize L (K : ℤ))
    (fun f : RealFun => smearedEnergy f)
    (fun f => ∫ V, smearedEnergy f V ∂ν) X.1
    fun f hf => ⟨(hentry f hf).2.2.2.1, (hentry f hf).2.2.2.2⟩
  exact ⟨hentry, hprod.1, hprod.2⟩
end YangMills.Construction.CenteredRepresentatives.EntriesAreLocal
