import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace YangMills.Construction
namespace GibbsAtFixedSpacing
open InfiniteLattice
namespace SymmetryActionProof
variable {a : ℝ}
theorem continuous_linkValue (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem linkSigma_le_borel (L : Set (Link a)) :
    linkSigma L ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by
  refine iSup₂_le fun b _ => ?_
  rw [← measurable_iff_comap_le]
  exact (continuous_linkValue b).measurable
theorem boundedMeasurableIn_eq (S : Set AmbientSpace) :
    boundedMeasurableIn a S = boundedRegionObservables a S := by
  ext F
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨⟨hm.mono (linkSigma_le_borel _) le_rfl, hb⟩, hm⟩
  · rintro ⟨⟨_, hb⟩, hm⟩
    exact ⟨hm, hb⟩
theorem locallyMeasurableIn_eq (S : Set AmbientSpace) :
    locallyMeasurableIn a S = localRegionObservables a S := by
  simp only [locallyMeasurableIn, localRegionObservables, boundedMeasurableIn_eq]
theorem pullbackField_pullbackField {t r : LatticeSymmetry a}
    (hrt : ∀ x, r.toFun (t.toFun x) = x) (U : GaugeField a) :
    t.pullbackField (r.pullbackField U) = U :=
  Subtype.ext (funext fun b => congrArg U.1
    (Link.ext (Subtype.ext (hrt b.initial)) (Subtype.ext (hrt b.terminal))))
theorem image_actOn_eq_of_forall_mem (C : Set (GaugeField a → ℂ))
    (hC : ∀ (s : LatticeSymmetry a) (F : GaugeField a → ℂ), F ∈ C → s.actOn F ∈ C)
    {r t : LatticeSymmetry a} (hinv : t.IsInverse r) :
    (fun F : GaugeField a → ℂ => r.actOn F) '' C = C := by
  refine Subset.antisymm ?_ fun G hG => ⟨t.actOn G, hC t G hG, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact hC r F hF
  · exact funext fun U => congrArg G (pullbackField_pullbackField hinv.2 U)
theorem isLocalObservable_of_mem_localRegionObservables {S : Set AmbientSpace}
    {F : GaugeField a → ℂ} (hF : F ∈ localRegionObservables a S) :
    IsBoundedObservable F ∧ IsLocalObservable F := by
  simp only [localRegionObservables, mem_iUnion] at hF
  obtain ⟨Q, hQ, hF, hm⟩ := hF
  exact ⟨hF, S ∩ Q, Bornology.IsBounded.subset hQ inter_subset_right, hm⟩
theorem mem_localRegionObservables_univ {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hl : IsLocalObservable F) : F ∈ localRegionObservables a univ := by
  obtain ⟨S, hS, hm⟩ := hl
  simp only [localRegionObservables, mem_iUnion]
  exact ⟨S, hS, hF, by rwa [univ_inter]⟩
theorem pullbackProperties (hP : PullbackFieldIsHomeomorph a)
    (hI : LatticeSymmetryInverses a) (r r' : LatticeSymmetry a) :
    PullbackProperties r r' := by
  refine ⟨(hP r).1, rfl, ?_⟩
  obtain ⟨t, ht⟩ := (hI r).2.1
  exact ⟨t, ht, Homeomorph.mk ⟨r.pullbackField, t.pullbackField,
    pullbackField_pullbackField ht.2, pullbackField_pullbackField ht.1⟩
    (hP r).2.continuous (hP t).2.continuous, rfl, rfl⟩
theorem observableActionRules (hK : ActOnPreservesAlgebraAndRegions a)
    (r r' : LatticeSymmetry a) : ObservableActionRules r r' :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun S => by rw [boundedMeasurableIn_eq, boundedMeasurableIn_eq]; exact (hK r).2 S,
    fun _ _ => rfl⟩
theorem isLinearAction (hK : ActOnPreservesAlgebraAndRegions a) (r : LatticeSymmetry a) :
    IsLinearAction r :=
  ⟨fun F hF => ((hK r).1 F F hF hF).1, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
theorem preservesNormAndFunctionSpaces (hP : PullbackFieldIsHomeomorph a)
    (hL : ActOnLinearIsometric a) (hLoc : ActOnLocalRegions a)
    (hI : LatticeSymmetryInverses a) (r : LatticeSymmetry a) :
    PreservesNormAndFunctionSpaces r := by
  obtain ⟨t, ht⟩ := (hI r).2.1
  refine ⟨fun F hF => ((hL r).2 F hF).2.2.2, fun S => ?_, ?_, ?_⟩
  · rw [locallyMeasurableIn_eq, locallyMeasurableIn_eq]
    exact hLoc.1 r S
  · exact image_actOn_eq_of_forall_mem _ (fun s F hF => Continuous.comp hF (hP s).2.continuous) ht
  · refine image_actOn_eq_of_forall_mem _ (fun s F hF => ?_) ht
    obtain ⟨hc, ho, hl⟩ := hF
    have hm : s.actOn F ∈ localRegionObservables a (s.setImage univ) := by
      rw [← hLoc.1 s univ]
      exact ⟨F, mem_localRegionObservables_univ ho hl, rfl⟩
    obtain ⟨ho', hl'⟩ := isLocalObservable_of_mem_localRegionObservables hm
    exact ⟨Continuous.comp hc (hP s).2.continuous, ho', hl'⟩
theorem latticeSymmetryActionOnFields (hobs : InfiniteLattice.SymmetryActionOnObservables) :
    LatticeSymmetryActionOnFields := by
  intro a ha r r'
  obtain ⟨-, hP, hK, -, -, hL, -, -, hLoc, hI, -⟩ := hobs ⟨a, ha⟩
  exact ⟨pullbackProperties hP hI r r', observableActionRules hK r r', isLinearAction hK r,
    preservesNormAndFunctionSpaces hP hL hLoc hI r⟩
end SymmetryActionProof
end GibbsAtFixedSpacing
end YangMills.Construction
