import YangMills.Construction.FourPointCondition.CutoffNamesTheUnitOfLength
import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TestFunctions PeriodicLattice Matrices
namespace FourPointBounds
section Measures
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
private theorem map_map_measurableEquiv_comp (e : β ≃ᵐ γ) (c : α → β) (μ : Measure α) :
    (μ.map c).map e = μ.map (e ∘ c) := by
  by_cases h : AEMeasurable c μ
  · exact AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable h
  · have h' : ¬ AEMeasurable (e ∘ c) μ := fun h2 => h (by
      have h3 := e.symm.measurable.comp_aemeasurable h2
      have h4 : (e.symm ∘ e ∘ c) = c := by
        funext a
        simp
      rwa [h4] at h3)
    rw [Measure.map_of_not_aemeasurable h, Measure.map_of_not_aemeasurable h', Measure.map_zero]
private theorem map_measurableEquiv_map_comp (e : α ≃ᵐ β) (c : β → γ) (μ : Measure α) :
    (μ.map e).map c = μ.map (c ∘ e) := by
  by_cases h : AEMeasurable c (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable h e.measurable.aemeasurable
  · have h' : ¬ AEMeasurable (c ∘ e) μ :=
      fun h2 => h (e.measurableEmbedding.aemeasurable_map_iff.2 h2)
    rw [Measure.map_of_not_aemeasurable h, Measure.map_of_not_aemeasurable h']
private theorem withDensity_map_measurableEquiv (e : α ≃ᵐ β) (μ : Measure α) (g : β → ℝ≥0∞) :
    (μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e := by
  ext s hs
  rw [withDensity_apply _ hs, e.map_apply, withDensity_apply _ (e.measurable hs),
    e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
  rfl
end Measures
section Dilation
variable {L : ℕ}
private theorem torusSide_ne_zero (hL : 0 < L) (m : ℕ) : torusSide L m ≠ 0 := by apply _root_.YangMills.Construction.Tower.torusSide_ne_zero <;> assumption
private def sideDilation (hL : 0 < L) (M m : ℕ) : FourTorus L M ≃+ FourTorus L m :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle (torusSide L M) (torusSide L m) (torusSide_ne_zero hL M)
      (torusSide_ne_zero hL m)
private theorem sideDilation_apply_mk (hL : 0 < L) {M m : ℕ} (μ : Fin 4) (y : FourTorus L M)
    (t : ℝ) (h : y μ = (t : AddCircle (torusSide L M))) :
    sideDilation hL M m y μ =
      ((t * ((torusSide L M)⁻¹ * torusSide L m) : ℝ) : AddCircle (torusSide L m)) := by
  have h0 : sideDilation hL M m y μ = AddCircle.equivAddCircle (torusSide L M) (torusSide L m)
      (torusSide_ne_zero hL M) (torusSide_ne_zero hL m) (y μ) := rfl
  rw [h0, h, AddCircle.equivAddCircle_apply_mk]
private theorem sideDilation_pointOnAxis (hL : 0 < L) {M m : ℕ} (μ : Fin 4) (t : ℝ) :
    sideDilation hL M m (pointOnAxis L M μ t) =
      pointOnAxis L m μ (t * ((torusSide L M)⁻¹ * torusSide L m)) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [sideDilation_apply_mk hL ν _ t (by simp [pointOnAxis])]
    simp [pointOnAxis]
  · have h0 : pointOnAxis L M μ t ν = ((0 : ℝ) : AddCircle (torusSide L M)) := by
      simp [pointOnAxis, Pi.single_eq_of_ne h]
    rw [sideDilation_apply_mk hL ν _ 0 h0]
    simp [pointOnAxis, Pi.single_eq_of_ne h]
private theorem mem_sublattice_iff {m : ℕ} {j : ℤ} (x : FourTorus L m) :
    x ∈ sublattice L m j ↔
      ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) :=
  Iff.rfl
variable {M m : ℕ} {j j' : ℤ} (hL : 0 < L)
  (hs : meshSize L j * ((torusSide L M)⁻¹ * torusSide L m) = meshSize L j')
include hs in
private theorem mem_sublattice_iff_sideDilation (x : FourTorus L M) :
    x ∈ sublattice L M j ↔ sideDilation hL M m x ∈ sublattice L m j' := by
  rw [mem_sublattice_iff, mem_sublattice_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun μ => ?_⟩
    rw [sideDilation_apply_mk hL μ x _ (hn μ), mul_assoc, hs]
  · rintro ⟨n, hn⟩
    refine ⟨n, fun μ => ?_⟩
    have h : sideDilation hL M m x = sideDilation hL M m
        (fun ν => (((n ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L M))) := by
      funext ν
      rw [hn ν, sideDilation_apply_mk hL ν _ _ rfl, mul_assoc, hs]
    exact congrFun ((sideDilation hL M m).injective h) μ
private def siteDilation : Site L M j ≃+ Site L m j' where
  toFun x := ⟨sideDilation hL M m x, (mem_sublattice_iff_sideDilation hL hs _).1 x.2⟩
  invFun y := ⟨(sideDilation hL M m).symm y, (mem_sublattice_iff_sideDilation hL hs _).2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (map_add (sideDilation hL M m) _ _)
private theorem siteDilation_unitStep (μ : Fin 4) :
    siteDilation hL hs (unitStep L M j μ) = unitStep L m j' μ := by
  apply Subtype.ext
  change sideDilation hL M m (pointOnAxis L M μ (meshSize L j)) = pointOnAxis L m μ (meshSize L j')
  rw [sideDilation_pointOnAxis, hs]
private theorem siteDilation_sub_eq_unitStep_iff (h t : Site L M j) (μ : Fin 4) :
    siteDilation hL hs h - siteDilation hL hs t = unitStep L m j' μ ↔ h - t = unitStep L M j μ := by
  rw [← map_sub, ← siteDilation_unitStep hL hs, (siteDilation hL hs).injective.eq_iff]
private theorem siteDilation_sub_eq_neg_unitStep_iff (h t : Site L M j) (μ : Fin 4) :
    siteDilation hL hs h - siteDilation hL hs t = -unitStep L m j' μ ↔
      h - t = -unitStep L M j μ := by
  rw [← map_sub, ← siteDilation_unitStep hL hs, ← map_neg, (siteDilation hL hs).injective.eq_iff]
private def bondDilation : Bond L M j ≃ Bond L m j' where
  toFun b := ⟨siteDilation hL hs b.source, siteDilation hL hs b.target, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by rwa [siteDilation_sub_eq_unitStep_iff, siteDilation_sub_eq_neg_unitStep_iff]⟩⟩
  invFun b := ⟨(siteDilation hL hs).symm b.source, (siteDilation hL hs).symm b.target, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    refine ⟨μ, ?_⟩
    rw [← siteDilation_sub_eq_unitStep_iff hL hs, ← siteDilation_sub_eq_neg_unitStep_iff hL hs]
    simpa using h⟩
  left_inv b := Bond.ext (by simp) (by simp)
  right_inv b := Bond.ext (by simp) (by simp)
private theorem isPositivelyOriented_bondDilation (b : Bond L M j) :
    (bondDilation hL hs b).IsPositivelyOriented ↔ b.IsPositivelyOriented :=
  exists_congr fun μ => siteDilation_sub_eq_unitStep_iff hL hs b.target b.source μ
private theorem bondDilation_opposite (b : Bond L M j) :
    bondDilation hL hs b.opposite = (bondDilation hL hs b).opposite := rfl
private theorem bondDilation_forwardFrom (x : Site L M j) (μ : Fin 4) :
    bondDilation hL hs (Bond.forwardFrom x μ) = Bond.forwardFrom (siteDilation hL hs x) μ := by
  apply Bond.ext
  · rfl
  · change siteDilation hL hs (x + unitStep L M j μ) = siteDilation hL hs x + unitStep L m j' μ
    rw [map_add, siteDilation_unitStep]
private def plaquetteDilation : Plaquette L M j ≃ Plaquette L m j' where
  toFun p := ⟨siteDilation hL hs p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  invFun p := ⟨(siteDilation hL hs).symm p.origin, p.firstAxis, p.secondAxis,
    p.firstAxis_lt_secondAxis⟩
  left_inv p := Plaquette.ext (by simp) rfl rfl
  right_inv p := Plaquette.ext (by simp) rfl rfl
private theorem boundaryBonds_plaquetteDilation (p : Plaquette L M j) :
    (plaquetteDilation hL hs p).boundaryBonds = p.boundaryBonds.map (bondDilation hL hs) := by
  have h1 : siteDilation hL hs (p.origin + unitStep L M j p.firstAxis) =
      siteDilation hL hs p.origin + unitStep L m j' p.firstAxis := by
    rw [map_add, siteDilation_unitStep]
  have h2 : siteDilation hL hs (p.origin + unitStep L M j p.secondAxis) =
      siteDilation hL hs p.origin + unitStep L m j' p.secondAxis := by
    rw [map_add, siteDilation_unitStep]
  simp only [Plaquette.boundaryBonds, List.map_cons, List.map_nil, bondDilation_opposite,
    bondDilation_forwardFrom, h1, h2]
  rfl
private theorem sideDilation_barycenter (p : Plaquette L M j) :
    sideDilation hL M m p.barycenter = (plaquetteDilation hL hs p).barycenter := by
  have h : meshSize L j / 2 * ((torusSide L M)⁻¹ * torusSide L m) = meshSize L j' / 2 := by
    rw [← hs]
    ring
  simp only [Plaquette.barycenter, map_add, sideDilation_pointOnAxis, h]
  rfl
end Dilation
section Configurations
variable {L M m : ℕ} {j j' : ℤ} (hL : 0 < L)
  (hs : meshSize L j * ((torusSide L M)⁻¹ * torusSide L m) = meshSize L j')
private def pullback : (Bond L m j' → ComplexMatrix2) ≃ᵐ (Bond L M j → ComplexMatrix2) where
  toFun U := U ∘ bondDilation hL hs
  invFun V := V ∘ (bondDilation hL hs).symm
  left_inv U := by
    funext b
    simp
  right_inv V := by
    funext b
    simp
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
private theorem pullback_apply (U : Bond L m j' → ComplexMatrix2) (b : Bond L M j) :
    pullback hL hs U b = U (bondDilation hL hs b) := rfl
private theorem plaquetteHolonomy_pullback (U : Bond L m j' → ComplexMatrix2) (p : Plaquette L M j) :
    plaquetteHolonomy (pullback hL hs U) p = plaquetteHolonomy U (plaquetteDilation hL hs p) := by
  unfold plaquetteHolonomy pathHolonomy
  rw [boundaryBonds_plaquetteDilation, List.map_map]
  rfl
private theorem plaquetteCost_pullback (U : Bond L m j' → ComplexMatrix2) (p : Plaquette L M j) :
    plaquetteCost (pullback hL hs U) p = plaquetteCost U (plaquetteDilation hL hs p) := by
  unfold plaquetteCost
  rw [plaquetteHolonomy_pullback]
private theorem wilsonAction_pullback (U : Bond L m j' → ComplexMatrix2) :
    wilsonAction (pullback hL hs U) = wilsonAction U := by
  unfold wilsonAction
  simp only [plaquetteCost_pullback]
  exact finsum_comp_equiv (plaquetteDilation hL hs)
private theorem boltzmannWeight_pullback (β : ℝ) (U : Bond L m j' → ComplexMatrix2) :
    boltzmannWeight β (pullback hL hs U) = boltzmannWeight β U := by
  unfold boltzmannWeight
  rw [wilsonAction_pullback]
private theorem dilateToSide_apply (f : FourTorus L m → ℝ) (y : FourTorus L M) :
    dilateToSide L m M f y = f (sideDilation hL M m y) := by
  unfold dilateToSide
  congr 1
  funext μ
  rw [sideDilation_apply_mk hL μ y (liftPoint y μ) (congrFun (torusProj_liftPoint y) μ).symm]
  change ((torusSide L m / torusSide L M * liftPoint y μ : ℝ) : AddCircle (torusSide L m)) = _
  congr 1
  rw [div_eq_mul_inv]
  ring
private theorem smearedObservable_pullback (f : FourTorus L m → ℝ)
    (U : Bond L m j' → ComplexMatrix2) :
    smearedObservable (dilateToSide L m M f) (pullback hL hs U) = smearedObservable f U := by
  unfold smearedObservable
  simp only [dilateToSide_apply hL, plaquetteCost_pullback, sideDilation_barycenter hL hs]
  exact finsum_comp_equiv (plaquetteDilation hL hs)
    (f := fun p => plaquetteCost U p • f p.barycenter)
private def positiveBondDilation : PositivelyOrientedBond L M j ≃ PositivelyOrientedBond L m j' :=
  (bondDilation hL hs).subtypeEquiv fun b => (isPositivelyOriented_bondDilation hL hs b).symm
private def positivePullback :
    (PositivelyOrientedBond L m j' → ComplexMatrix2.specialUnitary) ≃ᵐ
      (PositivelyOrientedBond L M j → ComplexMatrix2.specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.specialUnitary)
    (positiveBondDilation hL hs).symm
private theorem positivePullback_apply (v : PositivelyOrientedBond L m j' → ComplexMatrix2.specialUnitary)
    (c : PositivelyOrientedBond L M j) :
    positivePullback hL hs v c = v (positiveBondDilation hL hs c) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ComplexMatrix2.specialUnitary)
    (positiveBondDilation hL hs).symm v (positiveBondDilation hL hs c)
  simpa [positivePullback] using h
private theorem map_gaugeFieldHaar :
    (gaugeFieldHaar L m j').map (positivePullback hL hs) = gaugeFieldHaar L M j :=
  Measure.infinitePi_map_piCongrLeft
    (fun _ : PositivelyOrientedBond L M j => ComplexMatrix2.haarProb)
    (positiveBondDilation hL hs).symm
private theorem pullback_gaugeFieldOfPositive
    (v : PositivelyOrientedBond L m j' → ComplexMatrix2.specialUnitary) :
    pullback hL hs (gaugeFieldOfPositive v) =
      gaugeFieldOfPositive (positivePullback hL hs v) := by
  funext b
  rw [pullback_apply]
  unfold gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · have h1 := (isPositivelyOriented_bondDilation hL hs b).2 h
    rw [dif_pos h, dif_pos h1, positivePullback_apply]
    rfl
  · have h1 : ¬ (bondDilation hL hs b).IsPositivelyOriented := fun h2 =>
      h ((isPositivelyOriented_bondDilation hL hs b).1 h2)
    rw [dif_neg h, dif_neg h1]
    by_cases h' : b.opposite.IsPositivelyOriented
    · have h2 : (bondDilation hL hs b).opposite.IsPositivelyOriented := by
        rw [← bondDilation_opposite]
        exact (isPositivelyOriented_bondDilation hL hs _).2 h'
      rw [dif_pos h', dif_pos h2, positivePullback_apply]
      rfl
    · have h2 : ¬ (bondDilation hL hs b).opposite.IsPositivelyOriented := fun h3 => h' (by
        rw [← bondDilation_opposite] at h3
        exact (isPositivelyOriented_bondDilation hL hs _).1 h3)
      rw [dif_neg h', dif_neg h2]
private theorem map_productHaarMeasure :
    (productHaarMeasure L m j').map (pullback hL hs) = productHaarMeasure L M j := by
  unfold productHaarMeasure
  rw [map_map_measurableEquiv_comp, ← map_gaugeFieldHaar hL hs, map_measurableEquiv_map_comp]
  congr 1
  funext v
  exact pullback_gaugeFieldOfPositive hL hs v
end Configurations
section Wilson
variable {L M m K k : ℕ} (hL : 0 < L)
  (hs : meshSize L (k : ℤ) * ((torusSide L M)⁻¹ * torusSide L m) = meshSize L (K : ℤ))
include hL hs in
private theorem partitionFunction_eq_of_meshSize (β : ℝ) :
    partitionFunction L M k β = partitionFunction L m K β := by
  unfold partitionFunction
  rw [← map_productHaarMeasure hL hs, integral_map_equiv]
  simp only [boltzmannWeight_pullback]
private theorem map_wilsonGibbsMeasure (β : ℝ) :
    (wilsonGibbsMeasure L m K β).map (pullback hL hs) = wilsonGibbsMeasure L M k β := by
  unfold wilsonGibbsMeasure
  rw [partitionFunction_eq_of_meshSize hL hs, ← map_productHaarMeasure hL hs,
    withDensity_map_measurableEquiv, Measure.map_smul]
  congr 3
  funext U
  simp only [Function.comp_apply, boltzmannWeight_pullback]
end Wilson
private theorem meshSize_mul_sideRatio {L m K M k : ℕ} (hL : 0 < L) (h : M + k = m + K) :
    meshSize L (k : ℤ) * ((torusSide L M)⁻¹ * torusSide L m) = meshSize L (K : ℤ) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hp : (L : ℝ) ^ M * (L : ℝ) ^ k = (L : ℝ) ^ m * (L : ℝ) ^ K := by
    rw [← pow_add, ← pow_add, h]
  unfold meshSize torusSide
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have h1 : (L : ℝ) ^ k ≠ 0 := pow_ne_zero _ hL'
  have h2 : (L : ℝ) ^ K ≠ 0 := pow_ne_zero _ hL'
  have h3 : (L : ℝ) ^ M ≠ 0 := pow_ne_zero _ hL'
  field_simp
  linarith
theorem cutoffRescalingInvariance_holds : CutoffRescalingInvariance := by
  intro L m K M k p β hL3 h f
  have hL : 0 < L := by omega
  have hs := meshSize_mul_sideRatio (L := L) (m := m) (K := K) (M := M) (k := k) hL h
  have hG : Cumulants.momentGeneratingFunction (wilsonGibbsMeasure L m K β)
        (fun i U => smearedObservable (f i) U) =
      Cumulants.momentGeneratingFunction (wilsonGibbsMeasure L M k β)
        (fun i U => smearedObservable (dilateToSide L m M (f i)) U) := by
    funext t
    unfold Cumulants.momentGeneratingFunction
    rw [← map_wilsonGibbsMeasure hL hs, integral_map_equiv]
    simp only [smearedObservable_pullback]
  unfold torusUrsellFunction gibbsCumulant Cumulants.mixedCumulant
  rw [hG]
end FourPointBounds
end YangMills.Construction
end
