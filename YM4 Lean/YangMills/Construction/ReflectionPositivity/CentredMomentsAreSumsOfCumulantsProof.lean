import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.PassageToTheLimit.LatticeFunctionalsAreBoundedFormsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion
theorem mixedCumulant_congr_ae {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} {n : ℕ}
    {X Y : Fin n → Ω → ℝ} (hXY : ∀ i, X i =ᵐ[ν] Y i) :
    Cumulants.mixedCumulant ν X = Cumulants.mixedCumulant ν Y := by
  have hgen : Cumulants.momentGeneratingFunction ν X = Cumulants.momentGeneratingFunction ν Y := by
    funext t
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.mpr hXY] with ω hω
    simp only [hω]
  simp only [Cumulants.mixedCumulant, hgen]
theorem singletonFree_eq_partitionsNoSingletons (q : ℕ) :
    SetPartition.singletonFree q =
      SourcesAndGluing.partitionsNoSingletons q := by
  rw [SetPartition.singletonFree_eq_nonSingletonPartitions]
  ext π
  simp [SetPartition.nonSingletonPartitions, SourcesAndGluing.partitionsNoSingletons]
theorem centredMoment_eq_sum_prod_cumulants
    (hRel : Cumulants.MomentCumulantRelations.Holds)
    (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (q : ℕ) (hq : 1 ≤ q)
    (x : Fin q → Ω → ℝ) (hx : Probability.AllBoundedRealRV x) :
    (((∫ ω, ∏ l, (x l ω - ∫ ω', x l ω' ∂ν) ∂ν : ℝ)) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
        Probability.subfamilyCumulant ν x J := by
  rw [singletonFree_eq_partitionsNoSingletons]
  exact ((hRel Ω ν).2.2.2 q x hq hx).2
variable (D : MirrorData)
theorem opensMeasurableSpace_bondField (hE : Finite D.Edge) :
    OpensMeasurableSpace D.BondField := by
  have := hE
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  infer_instance
theorem measurableSet_compactGaugeFields (hP : D.FieldSpaceIsProduct) :
    MeasurableSet (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) := by apply _root_.YangMills.Construction.LimitSpaces.BoundedForms.measurableSet_compactGaugeFields <;> assumption
theorem ae_mem_compactGaugeFields (hP : D.FieldSpaceIsProduct)
    (hB : D.EnergiesBoundedAndMeasureProbability) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by apply _root_.YangMills.Construction.LimitSpaces.BoundedForms.ae_mem_compactGaugeFields <;> assumption
theorem exists_boundedRV_ae_eq (hP : D.FieldSpaceIsProduct)
    (hB : D.EnergiesBoundedAndMeasureProbability) (f : D.Torus → ℝ) :
    ∃ X : D.BondField → ℝ, Probability.IsBoundedRealRV X ∧
      X =ᵐ[PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling]
        PeriodicLattice.smearedObservable f := by
  have hS := measurableSet_compactGaugeFields D hP
  have hae := ae_mem_compactGaugeFields D hP hB
  obtain ⟨hcont, C, hb⟩ := hB.2.1 f
  have htop := hP.2.2.2.2.2.2.1
  have hc : Continuous fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1 := by
    have hf := hcont
    rw [MirrorData.ContinuousForProduct, htop] at hf
    exact hf
  have : OpensMeasurableSpace D.BondField := opensMeasurableSpace_bondField D hP.2.1
  have hm : Measurable fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1 :=
    hc.measurable
  have hval : ∀ U : D.FieldSpace,
      Function.extend (Subtype.val : D.FieldSpace → D.BondField)
        (fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) 0 U.1 =
        PeriodicLattice.smearedObservable f U.1 := fun U =>
    Subtype.val_injective.extend_apply _ _ U
  refine ⟨Function.extend (Subtype.val : D.FieldSpace → D.BondField)
    (fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) 0,
    ⟨(MeasurableEmbedding.subtype_coe hS).measurable_extend hm measurable_const, |C|, fun U => ?_⟩,
    ?_⟩
  · by_cases hU : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
    · have hv := hval ⟨U, hU⟩
      simp only at hv
      rw [hv]
      exact (hb ⟨U, hU⟩).trans (le_abs_self C)
    · rw [Function.extend_apply' _ _ _ fun ⟨V, hV⟩ => hU (hV ▸ V.2)]
      simp
  · filter_upwards [hae] with U hU
    exact hval ⟨U, hU⟩
theorem gibbsExpectation_eq_truncatedFunctional
    (hRel : Cumulants.MomentCumulantRelations.Holds)
    (hP : D.FieldSpaceIsProduct) (hB : D.EnergiesBoundedAndMeasureProbability)
    (q : ℕ) (g : Fin q → D.Torus → ℝ) :
    ((PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (fun U => ∏ l, D.centredObservable (g l) U) : ℝ) : ℂ) = D.truncatedFunctional g := by
  have : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) :=
    hB.2.2.2.2.2.2.2.2.2.2.1
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hnil : g = List.get ([] : D.FunTuple ℝ) := funext fun i => i.elim0
    have hone : D.truncatedFunctional g = 1 := by
      rw [hnil]
      exact D.truncatedFunctionalList_nil
    simp [PeriodicLattice.gibbsExpectation, hone]
  · choose X hX hae using fun l => exists_boundedRV_ae_eq D hP hB (g l)
    have hmean : ∀ l, ∫ U, X l U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling =
        PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (PeriodicLattice.smearedObservable (g l)) :=
      fun l => integral_congr_ae (hae l)
    have hexp : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (fun U => ∏ l, D.centredObservable (g l) U) =
        ∫ U, ∏ l, (X l U - ∫ U', X l U' ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling)
          ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling := by
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.mpr hae] with U hU
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [hU l, hmean l]
      rfl
    rw [hexp, centredMoment_eq_sum_prod_cumulants hRel _ _ q hq X hX,
      MirrorData.truncatedFunctional]
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
    exact mixedCumulant_congr_ae fun k => hae _
theorem holds (hRel : Cumulants.MomentCumulantRelations.Holds)
    (hField : FieldSpaceAndFaceEnergies.Statement) : CentredMomentCumulantExpansion := by
  refine ⟨fun Ω _ ν _ q hq x hx => centredMoment_eq_sum_prod_cumulants hRel Ω ν q hq x hx,
    fun D q g _ => ?_⟩
  obtain ⟨hP, -, hB⟩ := hField D
  exact ⟨rfl, gibbsExpectation_eq_truncatedFunctional D hRel hP hB q g⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion
end
