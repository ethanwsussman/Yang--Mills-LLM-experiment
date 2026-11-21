import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.SmearedEnergyAndSymmetryAction
open ConfigurationSpace
variable {a : ℝ}
theorem finite_faces_of_hasCompactSupport
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite)
    {E : Type*} [NormedAddCommGroup E] {f : AmbientSpace → E} (hf : HasCompactSupport f) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : AmbientSpace)
  have hT := hfin (Metric.closedBall 0 (R + |a|)) Metric.isBounded_closedBall
  have hinj : Function.Injective
      (fun p : ElementaryPlaquette a => (p.corner, p.lowAxis, p.highAxis)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
  refine ((hT.prod (Set.finite_univ.prod Set.finite_univ)).preimage hinj.injOn).subset ?_
  intro p hp
  have hb : ‖p.center‖ ≤ R := by
    simpa using hR (subset_tsupport f hp)
  have hcorner : (p.corner : AmbientSpace) =
      p.center - Pi.single p.lowAxis (a / 2) - Pi.single p.highAxis (a / 2) := by
    unfold ElementaryPlaquette.center
    abel
  have hs : ∀ μ : Fin 4, ‖(Pi.single μ (a / 2) : AmbientSpace)‖ = |a| / 2 := fun μ => by
    rw [Pi.norm_single, Real.norm_eq_abs, abs_div, abs_two]
  have hn : ‖(p.corner : AmbientSpace)‖ ≤ R + |a| := by
    rw [hcorner]
    have h₁ := norm_sub_le (p.center - Pi.single p.lowAxis (a / 2))
      (Pi.single p.highAxis (a / 2) : AmbientSpace)
    have h₂ := norm_sub_le p.center (Pi.single p.lowAxis (a / 2) : AmbientSpace)
    rw [hs] at h₁ h₂
    linarith
  simp only [mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
  simpa using hn
theorem smearedEnergy_eq_finsetSum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : AmbientSpace → E}
    (h : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite) (U : GaugeField a) :
    smearedEnergy f U = ∑ p ∈ h.toFinset, faceEnergy U p • f p.center := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro p hp
  simp only [Set.Finite.coe_toFinset, mem_ofPred_eq]
  intro h0
  exact hp (by simp [h0])
theorem faceEnergy_mul_const (hsp : FaceEnergyAndBoltzmannWeight a)
    (p : ElementaryPlaquette a) (c : ℂ) :
    IsBoundedObservable (fun U : GaugeField a => (faceEnergy U p : ℂ) * c) ∧
      IsLocalObservable (fun U : GaugeField a => (faceEnergy U p : ℂ) * c) := by
  obtain ⟨hc, hr, hm⟩ := hsp.1 p
  refine ⟨⟨(Complex.measurable_ofReal.comp hc.measurable).mul_const c, 2 * ‖c‖,
    fun U => ?_⟩, Subtype.val '' p.cornerSet, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr U).1]
    exact mul_le_mul_of_nonneg_right (hr U).2 (norm_nonneg c)
  · exact (Set.Finite.image _ (by simp [ElementaryPlaquette.cornerSet])).isBounded
  · exact Measurable.mul_const
      (show Measurable[regionSigma (Subtype.val '' p.cornerSet)] _ from hm) c
theorem faceEnergy_weightedSum (hsp : FaceEnergyAndBoltzmannWeight a)
    (hf : LinkSigmaAndLocality a) (F : Finset (ElementaryPlaquette a))
    (c : ElementaryPlaquette a → ℂ) :
    IsBoundedObservable (fun U : GaugeField a => ∑ p ∈ F, (faceEnergy U p : ℂ) * c p) ∧
      IsLocalObservable (fun U : GaugeField a => ∑ p ∈ F, (faceEnergy U p : ℂ) * c p) := by
  have : DecidableEq (ElementaryPlaquette a) := Classical.decEq _
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨measurable_const, 0, fun _ => by simp⟩, ∅, Bornology.isBounded_empty,
      measurable_const⟩
  | insert p F hp ih =>
    have ht := faceEnergy_mul_const hsp p (c p)
    have e : (fun U : GaugeField a => ∑ q ∈ insert p F, (faceEnergy U q : ℂ) * c q) =
        (fun U : GaugeField a => (faceEnergy U p : ℂ) * c p) +
          fun U : GaugeField a => ∑ q ∈ F, (faceEnergy U q : ℂ) * c q := by
      funext U
      simp [Finset.sum_insert hp]
    rw [e]
    exact (hf.2.2.2 _ _ ht.1 ht.2 ih.1 ih.2).1
theorem smearedEnergyComplex_holds
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite)
    (hsp : FaceEnergyAndBoltzmannWeight a)
    (hf : LinkSigmaAndLocality a) : SmearedEnergyComplex a := by
  intro f hfb
  have h := finite_faces_of_hasCompactSupport hfin hfb.2.2
  have e : (smearedEnergy f : GaugeField a → ℂ) = fun U : GaugeField a =>
      ∑ p ∈ h.toFinset, (faceEnergy U p : ℂ) * f p.center := by
    funext U
    rw [smearedEnergy_eq_finsetSum h]
    simp only [Complex.real_smul]
  have hs := faceEnergy_weightedSum hsp hf h.toFinset fun p => f p.center
  rw [← e] at hs
  exact ⟨h, smearedEnergy_eq_finsetSum h, hs.1, hs.2⟩
theorem smearedEnergyReal_holds
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite)
    (hsp : FaceEnergyAndBoltzmannWeight a)
    (hf : LinkSigmaAndLocality a) : SmearedEnergyReal a := by
  intro f hfb
  have h := finite_faces_of_hasCompactSupport hfin hfb.2.2
  have e : (fun U : GaugeField a => ((smearedEnergy f U : ℝ) : ℂ)) =
      fun U : GaugeField a =>
        ∑ p ∈ h.toFinset, (faceEnergy U p : ℂ) * ((f p.center : ℝ) : ℂ) := by
    funext U
    rw [smearedEnergy_eq_finsetSum h]
    simp only [smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  have hs := faceEnergy_weightedSum hsp hf h.toFinset fun p => ((f p.center : ℝ) : ℂ)
  rw [← e] at hs
  exact ⟨h, smearedEnergy_eq_finsetSum h, hs.1, hs.2⟩
theorem continuous_pullbackField (s : LatticeSymmetry a) : Continuous s.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem comap_regionSigma_le (s : LatticeSymmetry a) (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)).comap s.pullbackField ≤
      regionSigma (s.setImage S) := by
  simp only [regionSigma, linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun b hb => ?_
  exact le_iSup₂_of_le (f := fun (c : Link a) (_ : c ∈ linksWithin (s.setImage S)) =>
      MeasurableSpace.comap (fun U : GaugeField a => U c) inferInstance)
    (s.linkMap b) ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩ le_rfl
theorem symmetryActionProperties_holds : SymmetryActionProperties a := by
  intro s
  refine ⟨fun U => ⟨s.pullbackField U, rfl⟩, fun _ _ => rfl, continuous_pullbackField s,
    fun S A hA hS => ⟨⟨hA.1.comp (continuous_pullbackField s).measurable, ?_⟩, ?_,
      fun hc => hc.comp (continuous_pullbackField s)⟩⟩
  · obtain ⟨C, hC⟩ := hA.2
    exact ⟨C, fun U => hC _⟩
  · have hm : @Measurable _ _ (regionSigma (s.setImage S)) (regionSigma S) s.pullbackField :=
      measurable_iff_comap_le.mpr (comap_regionSigma_le s S)
    exact Measurable.comp (show Measurable[regionSigma S] A from hS) hm
theorem linkMap_comp (s t : LatticeSymmetry a) (b : Link a) :
    (s.comp t).linkMap b = s.linkMap (t.linkMap b) :=
  rfl
theorem actOn_comp_holds : ActOn_comp a := by
  intro s t A _
  funext U
  exact congrArg A (Subtype.ext (funext fun b => congrArg U (linkMap_comp s t b)))
theorem shiftInvariantSigmaCharacterization_holds : ShiftInvariantSigmaCharacterization a := by
  refine ⟨fun I hI => ⟨fun h v => ?_, fun h => ?_⟩, MeasurableSet.univ, fun I h => h.compl,
    fun I h => MeasurableSet.iUnion h⟩
  · have h' : IsShiftInvariantSet I := h
    exact ((shift v).actOn_indicator_eq_iff I).mp (h'.2 v)
  · have h' : IsShiftInvariantSet I :=
      ⟨hI, fun v => ((shift v).actOn_indicator_eq_iff I).mpr (h v)⟩
    exact h'
theorem main_holds (h₁ : LatticeGeometry.LatticeGeometryStatement)
    (h₂ : ConfigurationSpace.Main) : Main := by
  intro a ha
  obtain ⟨-, hb, -, -⟩ := h₁ a ha
  obtain ⟨-, -, hsp, -, -, hf, -⟩ := h₂ a ha
  have hfin := fun S hS => (hb.1 S hS).1
  exact ⟨⟨smearedEnergyComplex_holds hfin hsp hf,
    smearedEnergyReal_holds hfin hsp hf⟩, symmetryActionProperties_holds, actOn_comp_holds,
    shiftInvariantSigmaCharacterization_holds⟩
end YangMills.Construction.InfiniteLattice.SmearedEnergyAndSymmetryAction
