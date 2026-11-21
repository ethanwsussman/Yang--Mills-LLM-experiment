import YangMills.Construction.ChessboardTori.PeriodicGibbsStatesAreInvariantAndReflectionPositive
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.LawInAState.LawsAreInvariantUnderTranslations
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.StateLaws
section Shift
variable {L m : ℕ} {j : ℤ}
private def shiftBond (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    PeriodicLattice.Bond L m j :=
  ⟨b.source + w, b.target + w, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
private theorem shiftBond_neg_shiftBond (w : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.Bond L m j) : shiftBond (-w) (shiftBond w b) = b :=
  PeriodicLattice.Bond.ext (by simp [shiftBond]) (by simp [shiftBond])
private theorem shiftBond_shiftBond_neg (w : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.Bond L m j) : shiftBond w (shiftBond (-w) b) = b :=
  PeriodicLattice.Bond.ext (by simp [shiftBond]) (by simp [shiftBond])
private def shiftBondEquiv (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.Bond L m j ≃ PeriodicLattice.Bond L m j :=
  ⟨shiftBond w, shiftBond (-w), shiftBond_neg_shiftBond w, shiftBond_shiftBond_neg w⟩
private theorem shiftBond_opposite (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    shiftBond w b.opposite = (shiftBond w b).opposite := rfl
private theorem shiftBond_forwardFrom (w x : PeriodicLattice.Site L m j) (μ : Fin 4) :
    shiftBond w (PeriodicLattice.Bond.forwardFrom x μ) = PeriodicLattice.Bond.forwardFrom (x + w) μ :=
  PeriodicLattice.Bond.ext rfl (add_right_comm _ _ _)
private theorem isPositivelyOriented_shiftBond (w : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.Bond L m j) :
    (shiftBond w b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  simp only [PeriodicLattice.Bond.IsPositivelyOriented, shiftBond, add_sub_add_right_eq_sub]
private def shiftPositive (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.PositivelyOrientedBond L m j ≃ PeriodicLattice.PositivelyOrientedBond L m j :=
  (shiftBondEquiv w).subtypeEquiv fun b => (isPositivelyOriented_shiftBond w b).symm
private theorem gaugeFieldOfPositive_shift (w : PeriodicLattice.Site L m j)
    (v : PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L m j) :
    PeriodicLattice.gaugeFieldOfPositive (v ∘ shiftPositive w) b =
      PeriodicLattice.gaugeFieldOfPositive v (shiftBond w b) := by
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h, dif_pos ((isPositivelyOriented_shiftBond w b).2 h)]
    rfl
  · rw [dif_neg h, dif_neg (mt (isPositivelyOriented_shiftBond w b).1 h)]
    by_cases h' : b.opposite.IsPositivelyOriented
    · have h'' : (shiftBond w b).opposite.IsPositivelyOriented := by
        rw [← shiftBond_opposite]
        exact (isPositivelyOriented_shiftBond w _).2 h'
      rw [dif_pos h', dif_pos h'']
      rfl
    · have h'' : ¬(shiftBond w b).opposite.IsPositivelyOriented := by
        rw [← shiftBond_opposite]
        exact mt (isPositivelyOriented_shiftBond w _).1 h'
      rw [dif_neg h', dif_neg h'']
private theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
private theorem map_haarPi_comp {ι : Type} [Countable ι] (e : ι ≃ ι) :
    (Matrices.ComplexMatrix2.haarPi ι).map (fun v => v ∘ e) = Matrices.ComplexMatrix2.haarPi ι := by
  have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ι => Matrices.ComplexMatrix2.haarProb) e.symm
  have e' : (MeasurableEquiv.piCongrLeft (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) e.symm :
      (ι → Matrices.ComplexMatrix2.specialUnitary) → ι → Matrices.ComplexMatrix2.specialUnitary) =
        fun v => v ∘ e := by
    funext v i
    obtain ⟨a, rfl⟩ := e.symm.surjective i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [e'] at h
  exact h
private def shiftField (w : PeriodicLattice.Site L m j) :
    (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) ≃ᵐ
      (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) where
  toFun U := U ∘ shiftBond w
  invFun U := U ∘ shiftBond (-w)
  left_inv U := by
    funext b
    simp [shiftBond_shiftBond_neg]
  right_inv U := by
    funext b
    simp [shiftBond_neg_shiftBond]
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
private theorem measurePreserving_productHaarMeasure (w : PeriodicLattice.Site L m j) :
    MeasurePreserving (shiftField w) (PeriodicLattice.productHaarMeasure L m j)
      (PeriodicLattice.productHaarMeasure L m j) := by
  refine ⟨(shiftField w).measurable, ?_⟩
  have hc : Measurable fun v : PeriodicLattice.PositivelyOrientedBond L m j →
      Matrices.ComplexMatrix2.specialUnitary =>
      v ∘ shiftPositive w := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have e : (shiftField w) ∘ PeriodicLattice.gaugeFieldOfPositive =
      PeriodicLattice.gaugeFieldOfPositive ∘ fun v => v ∘ shiftPositive w := by
    funext v b
    exact (gaugeFieldOfPositive_shift w v b).symm
  unfold PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
  rw [Measure.map_map (shiftField w).measurable measurable_gaugeFieldOfPositive, e,
    ← Measure.map_map measurable_gaugeFieldOfPositive hc, map_haarPi_comp]
private def shiftPlaquette (w : PeriodicLattice.Site L m j) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.Plaquette L m j :=
  ⟨p.origin + w, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
private def shiftPlaquetteEquiv (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.Plaquette L m j ≃ PeriodicLattice.Plaquette L m j :=
  ⟨shiftPlaquette w, shiftPlaquette (-w),
    fun p => PeriodicLattice.Plaquette.ext (by simp [shiftPlaquette]) rfl rfl,
    fun p => PeriodicLattice.Plaquette.ext (by simp [shiftPlaquette]) rfl rfl⟩
private theorem boundaryBonds_shiftPlaquette (w : PeriodicLattice.Site L m j)
    (p : PeriodicLattice.Plaquette L m j) :
    (shiftPlaquette w p).boundaryBonds = p.boundaryBonds.map (shiftBond w) := by
  have e : ∀ μ, p.origin + w + PeriodicLattice.unitStep L m j μ =
      p.origin + PeriodicLattice.unitStep L m j μ + w := fun μ => add_right_comm _ _ _
  simp only [PeriodicLattice.Plaquette.boundaryBonds, shiftPlaquette, List.map_cons, List.map_nil,
    shiftBond_opposite, shiftBond_forwardFrom, e]
private theorem plaquetteCost_shift (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteCost (U ∘ shiftBond w) p =
      PeriodicLattice.plaquetteCost U (shiftPlaquette w p) := by
  simp only [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
    PeriodicLattice.pathHolonomy, boundaryBonds_shiftPlaquette, List.map_map]
private theorem wilsonAction_shift (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.wilsonAction (U ∘ shiftBond w) = PeriodicLattice.wilsonAction U := by
  unfold PeriodicLattice.wilsonAction
  simp only [plaquetteCost_shift]
  exact finsum_comp_equiv (shiftPlaquetteEquiv w)
private theorem measurePreserving_wilsonGibbsMeasure (K : ℕ) (β : ℝ)
    (w : PeriodicLattice.Site L m (K : ℤ)) :
    MeasurePreserving (shiftField w) (PeriodicLattice.wilsonGibbsMeasure L m K β)
      (PeriodicLattice.wilsonGibbsMeasure L m K β) := by
  refine ⟨(shiftField w).measurable, ?_⟩
  have hS := (shiftField w).measurable
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [Measure.map_smul]
  congr 1
  ext A hA
  rw [Measure.map_apply hS hA, withDensity_apply _ (hS hA), withDensity_apply _ hA,
    ← lintegral_indicator (hS hA), ← lintegral_indicator hA]
  conv_rhs => rw [← (measurePreserving_productHaarMeasure w).lintegral_comp_emb
    (shiftField w).measurableEmbedding]
  refine lintegral_congr fun U => ?_
  have hρ : PeriodicLattice.boltzmannWeight β (shiftField w U) =
      PeriodicLattice.boltzmannWeight β U := by
    unfold PeriodicLattice.boltzmannWeight
    rw [show PeriodicLattice.wilsonAction (shiftField w U) = PeriodicLattice.wilsonAction U from
      wilsonAction_shift w U]
  by_cases hU : shiftField w U ∈ A
  · simp [indicator, hU, hρ]
  · simp [indicator, hU]
private theorem shiftField_mem_compactGaugeFields (w : PeriodicLattice.Site L m j)
    {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) :
    shiftField w U ∈ PeriodicLattice.compactGaugeFields L m j :=
  ⟨fun _ _ => hU.1 _ (mem_univ _), fun b _ => hU.2 (shiftBond w b) (mem_univ _)⟩
private theorem projectLink_linkMap (v : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (b : InfiniteLattice.Link (PeriodicLattice.meshSize L j)) :
    InfiniteLattice.projectLink L m j ((InfiniteLattice.shift v).linkMap b) =
      shiftBond (InfiniteLattice.projectPoint L m j v) (InfiniteLattice.projectLink L m j b) := by
  have e : ∀ x : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j),
      InfiniteLattice.projectPoint L m j ((InfiniteLattice.shift v).pointMap x) =
        InfiniteLattice.projectPoint L m j x + InfiniteLattice.projectPoint L m j v := fun x =>
    Subtype.ext (funext fun μ => by
      simp [InfiniteLattice.projectPoint, TorusMetric.torusProj,
        InfiniteLattice.LatticeSymmetry.pointMap, InfiniteLattice.shift])
  exact PeriodicLattice.Bond.ext (e _) (e _)
private theorem liftField_shiftField (v : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L j))
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    InfiniteLattice.liftField L m j (shiftField (InfiniteLattice.projectPoint L m j v) U) =
      (InfiniteLattice.shift v).pullbackField (InfiniteLattice.liftField L m j U) := by
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields L m j
  · refine Subtype.ext (funext fun b => Subtype.ext ?_)
    change (InfiniteLattice.liftField L m j _ b : Matrices.ComplexMatrix2) =
      (InfiniteLattice.liftField L m j U ((InfiniteLattice.shift v).linkMap b) :
        Matrices.ComplexMatrix2)
    rw [InfiniteLattice.liftField_apply_of_mem (shiftField_mem_compactGaugeFields _ hU),
      InfiniteLattice.liftField_apply_of_mem hU, projectLink_linkMap]
    rfl
  · have hU' : shiftField (InfiniteLattice.projectPoint L m j v) U ∉
        PeriodicLattice.compactGaugeFields L m j := fun h => hU (by
      have h' := shiftField_mem_compactGaugeFields (-InfiniteLattice.projectPoint L m j v) h
      have e : shiftField (-InfiniteLattice.projectPoint L m j v)
          (shiftField (InfiniteLattice.projectPoint L m j v) U) = U := by
        funext b
        change U (shiftBond _ (shiftBond _ b)) = U b
        rw [shiftBond_shiftBond_neg]
      rwa [e] at h')
    rw [InfiniteLattice.liftField_of_notMem hU', InfiniteLattice.liftField_of_notMem hU]
    rfl
private theorem measurable_pullbackField {a : ℝ} (s : InfiniteLattice.LatticeSymmetry a) :
    Measurable s.pullbackField := by
  have hv : ∀ b, Continuous fun U : InfiniteLattice.GaugeField a => U b := fun b =>
    (continuous_apply b).comp
      (continuous_subtype_val : Continuous (Subtype.val :
        {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary //
          ∀ b, U b.opposite = (U b)⁻¹} → _))
  have h' : Continuous fun U : InfiniteLattice.GaugeField a =>
      (⟨fun b => U (s.linkMap b), fun b => U.2 (s.linkMap b)⟩ : InfiniteLattice.GaugeField a) :=
    Continuous.subtype_mk (continuous_pi fun b => hv (s.linkMap b)) _
  have h : Continuous s.pullbackField := h'
  exact h.measurable
abbrev _root_.YangMills.SharedProofs.p50069 := @measurable_pullbackField
private theorem liftedWilsonMeasure_isSymmetricUnder_shift (L m K : ℕ) (β : ℝ)
    (v : InfiniteLattice.LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
    InfiniteLattice.IsSymmetricUnder (InfiniteLattice.liftedWilsonMeasure L m K β)
      (InfiniteLattice.shift v) := by
  intro A hA
  have hpe := InfiniteLattice.measurable_liftField L m (K : ℤ)
  have hτ := measurable_pullbackField (InfiniteLattice.shift v)
  unfold InfiniteLattice.liftedWilsonMeasure
  change ∫ U, (A ∘ (InfiniteLattice.shift v).pullbackField) U ∂_ = _
  rw [integral_map hpe.aemeasurable (hA.1.comp hτ).aestronglyMeasurable,
    integral_map hpe.aemeasurable hA.1.aestronglyMeasurable,
    ← (measurePreserving_wilsonGibbsMeasure K β
      (InfiniteLattice.projectPoint L m (K : ℤ) v)).integral_comp
      (shiftField _).measurableEmbedding
      (fun U => A (InfiniteLattice.liftField L m (K : ℤ) U))]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  change A ((InfiniteLattice.shift v).pullbackField _) = A _
  rw [← liftField_shiftField]
end Shift
theorem translationInvariance_of_periodicStateSymmetries
    (h : ChessboardTori.PeriodicStateSymmetries.Statement) :
    translationInvarianceStatement := by
  intro D μ hμ v
  rcases hμ with hμ | ⟨e, rfl⟩
  · exact (h D μ hμ).1 v
  · exact liftedWilsonMeasure_isSymmetricUnder_shift D.L e D.K D.β v
end YangMills.Construction.StateLaws
end
