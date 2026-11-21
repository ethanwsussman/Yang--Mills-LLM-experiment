import YangMills.Construction.InfiniteLattice.EquationOfABondSetUnderTheTorusMeasureProof
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.InfiniteLattice.TorusMeasureIsAnInvariantProbabilityMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace FixedSpacing
namespace TranslationInvariance
section Translates
open PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def bondAdd (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    PeriodicLattice.Bond L m j where
  source := b.source + w
  target := b.target + w
  isNeighbour := by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by rwa [add_sub_add_right_eq_sub]⟩
theorem bondAdd_forwardFrom (w x : PeriodicLattice.Site L m j) (μ : Fin 4) :
    bondAdd w (PeriodicLattice.Bond.forwardFrom x μ) = PeriodicLattice.Bond.forwardFrom (x + w) μ :=
  PeriodicLattice.Bond.ext rfl (add_right_comm _ _ _)
theorem bondAdd_opposite (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    bondAdd w b.opposite = (bondAdd w b).opposite := rfl
theorem isPositivelyOriented_bondAdd (w : PeriodicLattice.Site L m j)
    {b : PeriodicLattice.Bond L m j} (h : b.IsPositivelyOriented) :
    (bondAdd w b).IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ, ?_⟩
  change b.target + w - (b.source + w) = _
  rwa [add_sub_add_right_eq_sub]
def positiveBondAddEquiv (w : PeriodicLattice.Site L m j) :
    PositivelyOrientedBond L m j ≃ PositivelyOrientedBond L m j where
  toFun b := ⟨bondAdd w b.1, isPositivelyOriented_bondAdd w b.2⟩
  invFun b := ⟨bondAdd (-w) b.1, isPositivelyOriented_bondAdd (-w) b.2⟩
  left_inv _ := Subtype.ext
    (PeriodicLattice.Bond.ext (add_neg_cancel_right _ _) (add_neg_cancel_right _ _))
  right_inv _ := Subtype.ext
    (PeriodicLattice.Bond.ext (neg_add_cancel_right _ _) (neg_add_cancel_right _ _))
def plaquetteAddEquiv (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.Plaquette L m j ≃ PeriodicLattice.Plaquette L m j where
  toFun p := ⟨p.origin + w, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  invFun p := ⟨p.origin + -w, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  left_inv _ := PeriodicLattice.Plaquette.ext (add_neg_cancel_right _ _) rfl rfl
  right_inv _ := PeriodicLattice.Plaquette.ext (neg_add_cancel_right _ _) rfl rfl
def fieldTranslate (w : PeriodicLattice.Site L m j) (U : CompactGaugeField L m j) :
    CompactGaugeField L m j :=
  ⟨fun b => U.1 (bondAdd w b), fun _ _ => U.2.1 _ (mem_univ _),
    fun b _ => U.2.2 (bondAdd w b) (mem_univ _)⟩
theorem continuous_linkValue (b : PeriodicLattice.Bond L m j) :
    Continuous fun U : CompactGaugeField L m j => U.linkValue b := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.continuous_linkValue <;> assumption
theorem continuous_fieldTranslate (w : PeriodicLattice.Site L m j) :
    Continuous (fieldTranslate w) := by
  refine continuous_iff_le_induced.2 ?_
  change _ ≤ TopologicalSpace.induced (fieldTranslate w) (⨅ b : PeriodicLattice.Bond L m j,
    TopologicalSpace.induced (fun U : CompactGaugeField L m j => U.linkValue b) inferInstance)
  rw [induced_iInf]
  refine le_iInf fun b => ?_
  rw [induced_compose]
  exact continuous_iff_le_induced.1 (continuous_linkValue (bondAdd w b))
theorem gaugeFieldMeasure_map_fieldTranslate (hP : GaugeFieldProduct.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : 0 ≤ j)
    (w : PeriodicLattice.Site L m j) :
    (gaugeFieldMeasure L m j).map (fieldTranslate w) = gaugeFieldMeasure L m j := by
  obtain ⟨hfirst, hren⟩ := hP
  obtain ⟨-, ⟨-, ⟨hfin, -⟩, -⟩, ⟨-, -, -, -, huniq, hhaar, -⟩, -⟩ := hfirst L m j hL hm hj
  have := hfin
  have hvals : Measurable (restrictToPositiveBonds : CompactGaugeField L m j → _) :=
    measurable_pi_iff.2 fun b => (continuous_linkValue b.1).measurable
  have hT := (continuous_fieldTranslate w).measurable
  have hR : Measurable (reindexFactors (positiveBondAddEquiv w).symm) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  refine huniq.unique ?_ hhaar
  unfold IsProductHaarImage at hhaar ⊢
  have e : restrictToPositiveBonds ∘ fieldTranslate w =
      reindexFactors (positiveBondAddEquiv w).symm ∘
        (restrictToPositiveBonds : CompactGaugeField L m j → _) := rfl
  rw [Measure.map_map hvals hT, e, ← Measure.map_map hR hvals, hhaar]
  exact (hren _ _ (positiveBondAddEquiv w).symm).2
theorem plaquetteEnergy_fieldTranslate (w : PeriodicLattice.Site L m j)
    (U : CompactGaugeField L m j) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteCost (fieldTranslate w U).1 p =
      PeriodicLattice.plaquetteCost U.1 (plaquetteAddEquiv w p) := by
  have e : p.boundaryBonds.map (bondAdd w) = (plaquetteAddEquiv w p).boundaryBonds := by
    change _ = [PeriodicLattice.Bond.forwardFrom (p.origin + w) p.firstAxis,
      PeriodicLattice.Bond.forwardFrom (p.origin + w + PeriodicLattice.unitStep L m j p.firstAxis)
        p.secondAxis,
      (PeriodicLattice.Bond.forwardFrom (p.origin + w + PeriodicLattice.unitStep L m j p.secondAxis)
        p.firstAxis).opposite,
      (PeriodicLattice.Bond.forwardFrom (p.origin + w) p.secondAxis).opposite]
    rw [add_right_comm p.origin w, add_right_comm p.origin w]
    simp only [PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil,
      bondAdd_opposite, bondAdd_forwardFrom]
  have h : PeriodicLattice.plaquetteHolonomy (fieldTranslate w U).1 p =
      PeriodicLattice.plaquetteHolonomy U.1 (plaquetteAddEquiv w p) := by
    unfold PeriodicLattice.plaquetteHolonomy PeriodicLattice.pathHolonomy
    rw [← e, List.map_map]
    rfl
  unfold PeriodicLattice.plaquetteCost
  rw [h]
theorem wilsonAction_fieldTranslate (w : PeriodicLattice.Site L m j)
    (U : CompactGaugeField L m j) :
    PeriodicLattice.wilsonAction (fieldTranslate w U).1 = PeriodicLattice.wilsonAction U.1 := by
  unfold PeriodicLattice.wilsonAction
  simp only [plaquetteEnergy_fieldTranslate]
  exact finsum_comp_equiv (plaquetteAddEquiv w)
theorem projectLink_shift (v : InfiniteLattice.LatticePoint (meshSize L j))
    (b : InfiniteLattice.Link (meshSize L j)) :
    projectLink L m j ((shift v).linkMap b) =
      bondAdd (projectPoint L m j v) (projectLink L m j b) := by
  have h : ∀ x : InfiniteLattice.LatticePoint (meshSize L j),
      projectPoint L m j ((shift v).pointMap x) = projectPoint L m j x + projectPoint L m j v :=
    fun x => Subtype.ext (funext fun μ => by
      simp [projectPoint, TorusMetric.torusProj, shift, LatticeSymmetry.pointMap])
  exact PeriodicLattice.Bond.ext (h _) (h _)
theorem pullbackField_liftCompactField (v : InfiniteLattice.LatticePoint (meshSize L j))
    (U : CompactGaugeField L m j) :
    (shift v).pullbackField (liftCompactField U) =
      liftCompactField (fieldTranslate (projectPoint L m j v) U) := by
  refine Subtype.ext (funext fun b => ?_)
  change liftCompactField U ((shift v).linkMap b) = _
  rw [liftCompactField_apply, liftCompactField_apply, projectLink_shift]
  rfl
end Translates
theorem continuous_pullbackField {a : ℝ} (s : LatticeSymmetry a) :
    Continuous s.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
section OfTheSetup
variable (D : Setup)
theorem continuous_wilsonEnergy (hP : GaugeFieldProduct.Statement) :
    Continuous D.wilsonEnergy := by apply _root_.YangMills.Construction.FixedSpacing.KernelPreservesTorusExpectation.continuous_wilsonEnergy <;> assumption
theorem continuous_boltzmannWeight (hP : GaugeFieldProduct.Statement) :
    Continuous fun U => Real.exp (-D.β * D.wilsonEnergy U) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonEnergy D hP))
theorem compactSpace_torusFields (hP : GaugeFieldProduct.Statement) :
    CompactSpace D.TorusFields := by
  obtain ⟨-, -, ⟨-, -, h, -⟩, -⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  exact h
theorem isProbabilityMeasure_haarMeasure (hP : GaugeFieldProduct.Statement) :
    IsProbabilityMeasure D.haarMeasure := by
  obtain ⟨-, -, ⟨-, -, -, -, -, -, h⟩, -⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  exact h
theorem integrable_boltzmannWeight (hP : GaugeFieldProduct.Statement) :
    Integrable (fun U => Real.exp (-D.β * D.wilsonEnergy U)) D.haarMeasure := by
  have := compactSpace_torusFields D hP
  have := isProbabilityMeasure_haarMeasure D hP
  exact (continuous_boltzmannWeight D hP).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
theorem partitionFunction_pos (hP : GaugeFieldProduct.Statement) :
    0 < D.partitionFunction := by
  have := isProbabilityMeasure_haarMeasure D hP
  exact integral_exp_pos (integrable_boltzmannWeight D hP)
theorem isProbabilityMeasure_gibbs (hP : GaugeFieldProduct.Statement) :
    IsProbabilityMeasure D.gibbs := by
  refine ⟨?_⟩
  have hZ := partitionFunction_pos D hP
  have hl : ∫⁻ U, ENNReal.ofReal (Real.exp (-D.β * D.wilsonEnergy U)) ∂D.haarMeasure =
      ENNReal.ofReal D.partitionFunction :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_boltzmannWeight D hP)
      (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  rw [Setup.gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hl, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
theorem gibbs_map_fieldTranslate (hP : GaugeFieldProduct.Statement)
    (w : PeriodicLattice.Site D.L D.m (D.level : ℤ)) :
    D.gibbs.map (fieldTranslate w) = D.gibbs := by
  have hT := (continuous_fieldTranslate w).measurable
  have hf : Measurable fun U : D.TorusFields =>
      ENNReal.ofReal (Real.exp (-D.β * D.wilsonEnergy U)) :=
    (continuous_boltzmannWeight D hP).measurable.ennreal_ofReal
  have hH : D.haarMeasure.map (fieldTranslate w) = D.haarMeasure :=
    gaugeFieldMeasure_map_fieldTranslate hP D.admissible D.m.pos (Int.natCast_nonneg _) w
  have hA : ∀ U : D.TorusFields, D.wilsonEnergy (fieldTranslate w U) = D.wilsonEnergy U :=
    wilsonAction_fieldTranslate w
  unfold Setup.gibbs
  rw [Measure.map_smul]
  congr 1
  ext E hE
  rw [Measure.map_apply hT hE, withDensity_apply _ (hT hE), withDensity_apply _ hE,
    ← lintegral_indicator (hT hE), ← lintegral_indicator hE]
  conv_rhs => rw [← hH, lintegral_map (hf.indicator hE) hT]
  refine lintegral_congr fun U => ?_
  by_cases hU : fieldTranslate w U ∈ E
  · have hU' : U ∈ fieldTranslate w ⁻¹' E := hU
    rw [indicator_of_mem hU', indicator_of_mem hU, hA]
  · have hU' : U ∉ fieldTranslate w ⁻¹' E := hU
    rw [indicator_of_notMem hU', indicator_of_notMem hU]
end OfTheSetup
end TranslationInvariance
theorem LiftedGibbsIsInvariantProbability.holds
    (hP : GaugeFieldProduct.Statement) :
    LiftedGibbsIsInvariantProbability := by
  intro D
  have hext : Continuous D.lift := continuous_liftCompactField
  have := TranslationInvariance.isProbabilityMeasure_gibbs D hP
  refine ⟨Measure.isProbabilityMeasure_map hext.measurable.aemeasurable, fun v A hA => ?_⟩
  have hτ := (TranslationInvariance.continuous_pullbackField (shift v)).measurable
  have hAm : Measurable A := hA.1
  let w := projectPoint D.L D.m (D.level : ℤ) v
  have hT := (TranslationInvariance.continuous_fieldTranslate w).measurable
  have hG : Measurable (A ∘ D.lift) := hAm.comp hext.measurable
  unfold Setup.liftedGibbs
  have hO : Measurable ((shift v).actOn A) := hAm.comp hτ
  rw [integral_map hext.measurable.aemeasurable hO.aestronglyMeasurable,
    integral_map hext.measurable.aemeasurable hAm.aestronglyMeasurable]
  calc ∫ U, (shift v).actOn A (D.lift U) ∂D.gibbs
      = ∫ U, (A ∘ D.lift) (TranslationInvariance.fieldTranslate w U) ∂D.gibbs := by
        refine integral_congr_ae (ae_of_all _ fun U => ?_)
        exact congrArg A (TranslationInvariance.pullbackField_liftCompactField v U)
    _ = ∫ U, (A ∘ D.lift) U ∂(D.gibbs.map (TranslationInvariance.fieldTranslate w)) :=
        (integral_map hT.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ U, A (D.lift U) ∂D.gibbs := by
        rw [TranslationInvariance.gibbs_map_fieldTranslate D hP w]; rfl
end FixedSpacing
end YangMills.Construction
