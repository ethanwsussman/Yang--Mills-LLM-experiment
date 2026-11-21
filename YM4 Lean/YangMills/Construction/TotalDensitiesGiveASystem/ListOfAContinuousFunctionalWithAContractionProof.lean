import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimitProof
import YangMills.Construction.TotalDensitiesGiveASystem.ComplementsOfAFunctionalWithAContraction
import YangMills.Construction.TotalDensitiesGiveASystem.ListOfAContinuousFunctionalWithAContraction
import YangMills.Construction.TotalDensitiesGiveASystem.SpaceOfAContinuousFunctionalIsSeparable
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace YangMills.Construction.TotalDensitiesGiveASystem.ContractionFunctionalList
section Reconstructs
open SeparatedTuples hiding conjugation
open ReflectionPositivity.TupleForm SpectralTheory
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass timeShift timeBasisVec)
open ReflectionPositivity.PairMeasureOperators (energyMomentumPair)
open ReflectionPositivity.ReconstructionComplements
open LimitConventions (SpaceVec octahedralGroup3 timeExtension)
open HilbertSpaceBasics (IsPosSemidef)
private theorem exists_octahedral_of_stabilizer (hc : OctahedralFixesTime)
    (w : TorusSymmetries.timeVecStabilizer) :
    ∃ v ∈ octahedralGroup3, ⇑(timeExtension v) = ⇑w.1.1 := by apply _root_.YangMills.SharedProofs.p12663 <;> assumption
private def octahedralOf (hc : OctahedralFixesTime) (w : TorusSymmetries.timeVecStabilizer) :
    SpaceVec ≃ₗ[ℝ] SpaceVec :=
  (exists_octahedral_of_stabilizer hc w).choose
private theorem octahedralOf_mem (hc : OctahedralFixesTime) (w : TorusSymmetries.timeVecStabilizer) :
    octahedralOf hc w ∈ octahedralGroup3 :=
  (exists_octahedral_of_stabilizer hc w).choose_spec.1
private theorem coe_timeExtension_octahedralOf (hc : OctahedralFixesTime)
    (w : TorusSymmetries.timeVecStabilizer) :
    ⇑(timeExtension (octahedralOf hc w)) = ⇑w.1.1 :=
  (exists_octahedral_of_stabilizer hc w).choose_spec.2
private theorem isEuclidIsometry_of_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    IsEuclidIsometry ⇑w.1 := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_hyperoctahedral <;> assumption
private theorem timeExtension_mem_upper (v : SpaceVec ≃ₗ[ℝ] SpaceVec) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan ⇑(timeExtension v) G ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p61114 <;> assumption
private theorem translate_mem_upper {v : InfiniteLattice.AmbientSpace}
    (hv : 0 ≤ v TimeAxis.timeIdx) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) G ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p76588 <;> assumption
section Stabilizer
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
private theorem ext_of_posClass (hC : HilbertSpaceFacts.CompletionProperties)
    {A B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hAB : ∀ F, A (posClass σ h F) = B (posClass σ h F)) : A = B := by apply _root_.YangMills.SharedProofs.p22624 <;> assumption
private theorem spanClass_of_mem {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    spanClass σ h G = posClass σ h ⟨G, hG⟩ := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanClass_of_mem <;> assumption
variable (hc : OctahedralFixesTime)
  (hpart : ∀ w ∈ octahedralGroup3, UnitaryClaim σ h w ∧ IntertwiningClaim σ h w)
private def stabilizerOp (w : TorusSymmetries.timeVecStabilizer) :
    PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h :=
  octahedralUnitaryCLM σ h (octahedralOf hc w)
include hpart in
private theorem stabilizerOp_acts (w : TorusSymmetries.timeVecStabilizer) :
    LimitTheorem.ActsOnClasses σ h w.1.1 (stabilizerOp (σ := σ) (h := h) hc w) := by
  intro F
  have h₁ := (hpart _ (octahedralOf_mem hc w)).1.2 F
  rw [coe_timeExtension_octahedralOf hc w] at h₁
  exact h₁
include hc in
private theorem stabilizer_mem_upper (w : TorusSymmetries.timeVecStabilizer)
    {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan ⇑w.1.1 G ∈ spanIn TimeAxis.upperHalfSpace := by
  rw [← coe_timeExtension_octahedralOf hc w]
  exact timeExtension_mem_upper _ hG
include hpart in
private theorem stabilizerOp_posClass (w : TorusSymmetries.timeVecStabilizer)
    (F : PositiveSpan) :
    stabilizerOp (σ := σ) (h := h) hc w (posClass σ h F) =
      posClass σ h ⟨_, stabilizer_mem_upper hc w F.2⟩ := by
  rw [stabilizerOp_acts hc hpart w F]
  exact spanClass_of_mem _
private theorem stabilizer_comp_translate (w : TorusSymmetries.timeVecStabilizer) (t : ℝ) :
    ⇑w.1.1 ∘ SeparatedTuples.translate (t • timeBasisVec) =
      SeparatedTuples.translate (t • timeBasisVec) ∘ ⇑w.1.1 := by apply _root_.YangMills.SharedProofs.p62730 <;> assumption
include hpart in
private theorem stabilizerOp_isRep
    (hC : HilbertSpaceFacts.CompletionProperties)
    (hA : BasicFacts.PushSpanProperties)
    (hTime : ReflectionPositivity.Reconstruction.IsTimeShiftFamily σ h (timeShift σ h)) :
    LimitTheorem.IsStabilizerRep σ h (stabilizerOp (σ := σ) (h := h) hc) := by
  refine ⟨fun w => ⟨stabilizerOp_acts hc hpart w, fun U' hU' => ?_⟩,
    ⟨fun w => ⟨fun ψ => ?_, ?_⟩, fun w w' => ?_⟩,
    fun w => (hpart _ (octahedralOf_mem hc w)).2.1, fun w t => ?_⟩
  · exact ext_of_posClass hC fun F => by rw [hU' F, stabilizerOp_acts hc hpart w F]
  · exact (octahedralUnitary σ h (octahedralOf hc w)).norm_map ψ
  · exact (octahedralUnitary σ h (octahedralOf hc w)).surjective
  · refine ext_of_posClass hC fun F => ?_
    change stabilizerOp hc w (stabilizerOp hc w' (posClass σ h F)) = _
    rw [stabilizerOp_posClass hc hpart w' F, stabilizerOp_posClass hc hpart w,
      stabilizerOp_posClass hc hpart (w * w') F]
    refine congrArg _ (Subtype.ext ?_)
    exact ((hA _ _ (isEuclidIsometry_of_hyperoctahedral w.1)
      (isEuclidIsometry_of_hyperoctahedral w'.1) 0 0 F.1).1).symm
  · have ht : 0 ≤ ((t : ℝ) • timeBasisVec) TimeAxis.timeIdx := by
      have : ((t : ℝ) • timeBasisVec) TimeAxis.timeIdx = (t : ℝ) := by
        simp [ReflectionPositivity.Reconstruction.timeBasisVec, PeriodicLattice.coordVec]
      rw [this]
      exact t.2
    have hτ := isEuclidIsometry_translate ((t : ℝ) • timeBasisVec)
    refine ext_of_posClass hC fun F => ?_
    change stabilizerOp hc w (timeShift σ h t (posClass σ h F)) =
      timeShift σ h t (stabilizerOp hc w (posClass σ h F))
    rw [hTime t F, spanClass_of_mem (translate_mem_upper ht F.2),
      stabilizerOp_posClass hc hpart w, stabilizerOp_posClass hc hpart w F, hTime t,
      spanClass_of_mem (translate_mem_upper ht (stabilizer_mem_upper hc w F.2))]
    refine congrArg _ (Subtype.ext ?_)
    change pushSpan ⇑w.1.1 (pushSpan (SeparatedTuples.translate ((t : ℝ) • timeBasisVec)) F.1) =
      pushSpan (SeparatedTuples.translate ((t : ℝ) • timeBasisVec)) (pushSpan ⇑w.1.1 F.1)
    rw [← (hA _ _ (isEuclidIsometry_of_hyperoctahedral w.1) hτ 0 0 F.1).1,
      ← (hA _ _ hτ (isEuclidIsometry_of_hyperoctahedral w.1) 0 0 F.1).1, stabilizer_comp_translate]
end Stabilizer
private theorem stronglyCommute_energyMomentumPair {σ : TupleFunctional}
    {h : IsPosSemidef (reflectionForm σ)}
    (hfour : StronglyCommute (energyMomentumOps σ h)) (i : Fin 3) :
    StronglyCommute (energyMomentumPair σ h i) := by apply _root_.YangMills.SharedProofs.p86973 <;> assumption
private theorem jointSpectrumSubset_nonneg {σ : TupleFunctional}
    {h : IsPosSemidef (reflectionForm σ)}
    (supp : SpectralSupport.ConcentratedOnSupportTheorem)
    (hO : OperatorClaim σ h) (hCar : SupportClaim σ h) :
    LimitTheorem.JointSpectrumSubset σ h {y | 0 ≤ y 0} := by apply _root_.YangMills.SharedProofs.p1597 <;> assumption
private theorem exists_motion_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    ∃ r : Motions.RigidMotion, LimitTheorem.IsHyperoctahedralMotion r ∧ r.toFun = w.1 := by apply _root_.YangMills.SharedProofs.p35926 <;> assumption
open ReflectionPositivity.ContractionFunctionals (IsAdmissible)
theorem contractionFunctionalReconstructs_holds
    (hA : TotalDensitiesGiveASystem.ContractionFunctionalComplements)
    (hB : TotalDensitiesGiveASystem.PhysicalSpaceSeparable)
    (hSup : SpectralSupport.ConcentratedOnSupportTheorem)
    (hHF : HilbertSpaceFacts.Facts) (hFacts : SeparatedTuples.BasicFacts.MainFacts)
    (hCub : Continuum.AxisPreservingSymmetries.Classification) :
    TotalDensities.ContractionFunctionalReconstructs := by
  intro σ hc hH hinvM
  obtain ⟨-, -, -, -, -, hC, -⟩ := hHF
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  obtain ⟨D₀, hD₀⟩ := hH.contraction
  have hI : ∀ v ∈ octahedralGroup3, σ.IsInvariant (timeExtension v) := fun v hv => by
    have hmem := (LimitConventions.mem_hyperoctahedralLinearGroup_iff_toEquiv _).1 (hCub.1 v hv).1
    obtain ⟨r, hr, e⟩ := exists_motion_hyperoctahedral ⟨_, hmem⟩
    have h := hinvM r hr
    unfold LimitTheorem.IsMotionInvariant at h
    rw [e] at h
    exact h
  obtain ⟨h, hV, hSH, hTM, hMt, -, hOps, hCar, hUnit⟩ := hA σ hH hI
  have hcub : ReflectionPositivity.ReconstructionComplements.OctahedralFixesTime :=
    hCub.2.2.2.2.2.2.2.1
  exact ⟨hH.permInvariant, hD₀.translateInvariant, h, ⟨hV, hSH, hTM, hMt⟩, hB σ h hc,
    stronglyCommute_energyMomentumPair hOps.2.2.1, jointSpectrumSubset_nonneg hSup hOps hCar, _,
    stabilizerOp_isRep hcub hUnit hC hAct hSH.2.1⟩
end Reconstructs
end YangMills.Construction.TotalDensitiesGiveASystem.ContractionFunctionalList
end
