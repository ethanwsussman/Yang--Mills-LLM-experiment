import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitionsProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionIsFormedProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicStates
variable {L m : ℕ} {j : ℤ}
def translateBond (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    PeriodicLattice.Bond L m j where
  source := b.source + w
  target := b.target + w
  isNeighbour := by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩
theorem translateBond_translateBond (w w' : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.Bond L m j) :
    translateBond w' (translateBond w b) = translateBond (w + w') b :=
  PeriodicLattice.Bond.ext (add_assoc _ _ _) (add_assoc _ _ _)
theorem translateBond_zero (b : PeriodicLattice.Bond L m j) : translateBond 0 b = b :=
  PeriodicLattice.Bond.ext (add_zero _) (add_zero _)
def translateBondEquiv (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.Bond L m j ≃ PeriodicLattice.Bond L m j where
  toFun := translateBond w
  invFun := translateBond (-w)
  left_inv b := by rw [translateBond_translateBond, add_neg_cancel, translateBond_zero]
  right_inv b := by rw [translateBond_translateBond, neg_add_cancel, translateBond_zero]
theorem translateBond_opposite (w : PeriodicLattice.Site L m j) (b : PeriodicLattice.Bond L m j) :
    translateBond w b.opposite = (translateBond w b).opposite := rfl
theorem isPositivelyOriented_translateBond (w : PeriodicLattice.Site L m j)
    (b : PeriodicLattice.Bond L m j) :
    (translateBond w b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  simp only [PeriodicLattice.Bond.IsPositivelyOriented, translateBond, add_sub_add_right_eq_sub]
theorem translateBond_forwardFrom (w x : PeriodicLattice.Site L m j) (μ : Fin 4) :
    translateBond w (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (x + w) μ :=
  PeriodicLattice.Bond.ext rfl (add_right_comm _ _ _)
def translatePlaquette (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.Plaquette L m j ≃ PeriodicLattice.Plaquette L m j where
  toFun p := ⟨p.origin + w, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  invFun p := ⟨p.origin - w, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  left_inv _ := PeriodicLattice.Plaquette.ext (add_sub_cancel_right _ _) rfl rfl
  right_inv _ := PeriodicLattice.Plaquette.ext (sub_add_cancel _ _) rfl rfl
theorem boundaryBonds_translatePlaquette (w : PeriodicLattice.Site L m j)
    (p : PeriodicLattice.Plaquette L m j) :
    (translatePlaquette w p).boundaryBonds = p.boundaryBonds.map (translateBond w) := by
  simp only [PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    translateBond_opposite, translateBond_forwardFrom]
  change [_, PeriodicLattice.Bond.forwardFrom (p.origin + w + _) _,
    (PeriodicLattice.Bond.forwardFrom (p.origin + w + _) _).opposite, _] = _
  rw [add_right_comm p.origin w, add_right_comm p.origin w]
  rfl
def translateField (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 :=
  fun b => U (translateBond w b)
theorem translateField_translateField (w w' : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    translateField w (translateField w' U) = translateField (w + w') U :=
  funext fun b => congrArg U (translateBond_translateBond w w' b)
theorem translateField_zero (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    translateField 0 U = U :=
  funext fun b => congrArg U (translateBond_zero b)
theorem measurable_translateField (w : PeriodicLattice.Site L m j) :
    Measurable (translateField w : (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) → _) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
def translateFieldMeasurableEquiv (w : PeriodicLattice.Site L m j) :
    (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) ≃ᵐ
      (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) where
  toFun := translateField w
  invFun := translateField (-w)
  left_inv U := by
    rw [translateField_translateField, neg_add_cancel, translateField_zero]
  right_inv U := by
    rw [translateField_translateField, add_neg_cancel, translateField_zero]
  measurable_toFun := measurable_translateField w
  measurable_invFun := measurable_translateField (-w)
theorem translateField_mem (w : PeriodicLattice.Site L m j)
    {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) :
    translateField w U ∈ PeriodicLattice.compactGaugeFields L m j :=
  ⟨fun _ _ => hU.1 _ (mem_univ _), fun b _ => hU.2 (translateBond w b) (mem_univ _)⟩
theorem translateField_mem_iff (w : PeriodicLattice.Site L m j)
    {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2} :
    translateField w U ∈ PeriodicLattice.compactGaugeFields L m j ↔
      U ∈ PeriodicLattice.compactGaugeFields L m j := by
  refine ⟨fun h => ?_, translateField_mem w⟩
  have h' := translateField_mem (-w) h
  rwa [translateField_translateField, neg_add_cancel, translateField_zero] at h'
theorem plaquetteHolonomy_translateField (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2)
    (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteHolonomy (translateField w U) p =
      PeriodicLattice.plaquetteHolonomy U (translatePlaquette w p) := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    boundaryBonds_translatePlaquette, List.map_map]
  rfl
theorem wilsonAction_translateField (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.wilsonAction (translateField w U) = PeriodicLattice.wilsonAction U := by
  have h : ∀ p, PeriodicLattice.plaquetteCost (translateField w U) p =
      PeriodicLattice.plaquetteCost U (translatePlaquette w p) := fun p => by
    simp only [PeriodicLattice.plaquetteCost, plaquetteHolonomy_translateField]
  simp only [PeriodicLattice.wilsonAction, h]
  exact finsum_comp_equiv (translatePlaquette w)
theorem boltzmannWeight_translateField (β : ℝ) (w : PeriodicLattice.Site L m j)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.boltzmannWeight β (translateField w U) = PeriodicLattice.boltzmannWeight β U := by
  simp only [PeriodicLattice.boltzmannWeight, wilsonAction_translateField]
def translatePositive (w : PeriodicLattice.Site L m j) :
    PeriodicLattice.PositivelyOrientedBond L m j ≃ PeriodicLattice.PositivelyOrientedBond L m j :=
  (translateBondEquiv w).subtypeEquiv fun b => (isPositivelyOriented_translateBond w b).symm
theorem translateField_gaugeFieldOfPositive (w : PeriodicLattice.Site L m j)
    (v : PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    translateField w (PeriodicLattice.gaugeFieldOfPositive v) =
      PeriodicLattice.gaugeFieldOfPositive (v ∘ translatePositive w) := by
  funext b
  simp only [translateField, PeriodicLattice.gaugeFieldOfPositive]
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos ((isPositivelyOriented_translateBond w b).2 h), dif_pos h]
    rfl
  · rw [dif_neg (mt (isPositivelyOriented_translateBond w b).1 h), dif_neg h]
    by_cases h' : b.opposite.IsPositivelyOriented
    · have h'' : (translateBond w b).opposite.IsPositivelyOriented := by
        rw [← translateBond_opposite]
        exact (isPositivelyOriented_translateBond w _).2 h'
      rw [dif_pos h'', dif_pos h']
      rfl
    · have h'' : ¬(translateBond w b).opposite.IsPositivelyOriented := by
        rw [← translateBond_opposite]
        exact mt (isPositivelyOriented_translateBond w _).1 h'
      rw [dif_neg h'', dif_neg h']
theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem map_gaugeFieldHaar (e : PeriodicLattice.PositivelyOrientedBond L m j ≃
    PeriodicLattice.PositivelyOrientedBond L m j) :
    (PeriodicLattice.gaugeFieldHaar L m j).map (fun v => v ∘ e) =
      PeriodicLattice.gaugeFieldHaar L m j := by
  have h := Measure.infinitePi_map_piCongrLeft
    (X := fun _ : PeriodicLattice.PositivelyOrientedBond L m j =>
      Matrices.ComplexMatrix2.specialUnitary)
    (μ := fun _ => Matrices.ComplexMatrix2.haarProb) e.symm
  have hc : (MeasurableEquiv.piCongrLeft
      (fun _ : PeriodicLattice.PositivelyOrientedBond L m j =>
        Matrices.ComplexMatrix2.specialUnitary) e.symm : _ → _) = fun v => v ∘ e := by
    funext v b
    have := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : PeriodicLattice.PositivelyOrientedBond L m j =>
        Matrices.ComplexMatrix2.specialUnitary) e.symm v (e b)
    simpa using this
  rw [hc] at h
  exact h
theorem map_productHaarMeasure (w : PeriodicLattice.Site L m j) :
    (PeriodicLattice.productHaarMeasure L m j).map (translateField w) =
      PeriodicLattice.productHaarMeasure L m j := by
  have hr : Measurable fun v : PeriodicLattice.PositivelyOrientedBond L m j →
      Matrices.ComplexMatrix2.specialUnitary => v ∘ translatePositive w :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  unfold PeriodicLattice.productHaarMeasure
  rw [Measure.map_map (measurable_translateField w) measurable_gaugeFieldOfPositive]
  have h : translateField w ∘ PeriodicLattice.gaugeFieldOfPositive =
      PeriodicLattice.gaugeFieldOfPositive ∘ fun v => v ∘ translatePositive w :=
    funext fun v => translateField_gaugeFieldOfPositive w v
  rw [h, ← Measure.map_map measurable_gaugeFieldOfPositive hr, map_gaugeFieldHaar]
theorem map_wilsonGibbsMeasure (K : ℕ) (β : ℝ) (w : PeriodicLattice.Site L m (K : ℤ)) :
    (PeriodicLattice.wilsonGibbsMeasure L m K β).map (translateField w) =
      PeriodicLattice.wilsonGibbsMeasure L m K β := by
  have mp : MeasurePreserving (translateField w) (PeriodicLattice.productHaarMeasure L m (K : ℤ))
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)) :=
    ⟨measurable_translateField w, map_productHaarMeasure w⟩
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [Measure.map_smul]
  congr 1
  ext E hE
  rw [Measure.map_apply (measurable_translateField w) hE,
    withDensity_apply _ (measurable_translateField w hE), withDensity_apply _ hE,
    ← mp.setLIntegral_comp_preimage_emb
      (translateFieldMeasurableEquiv w).measurableEmbedding _ E]
  simp only [boltzmannWeight_translateField]
theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectLink_linkMap (v : LatticePoint (PeriodicLattice.meshSize L j))
    (b : Link (PeriodicLattice.meshSize L j)) :
    projectLink L m j ((shift v).linkMap b) =
      translateBond (projectPoint L m j v) (projectLink L m j b) :=
  PeriodicLattice.Bond.ext (projectPoint_add _ _) (projectPoint_add _ _)
theorem pullbackField_liftField (v : LatticePoint (PeriodicLattice.meshSize L j))
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    (shift v).pullbackField (liftField L m j U) =
      liftField L m j (translateField (projectPoint L m j v) U) := by
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields L m j
  · have hU' := translateField_mem (projectPoint L m j v) hU
    refine Subtype.ext (funext fun b => Subtype.ext ?_)
    change ((liftField L m j U ((shift v).linkMap b) : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) =
      (liftField L m j (translateField (projectPoint L m j v) U) b :
        Matrices.ComplexMatrix2.specialUnitary)
    rw [liftField_apply_of_mem hU, liftField_apply_of_mem hU', projectLink_linkMap]
    rfl
  · rw [liftField_of_notMem hU,
      liftField_of_notMem (mt (translateField_mem_iff _).1 hU)]
    rfl
theorem continuous_pullbackField {a : ℝ} (s : LatticeSymmetry a) :
    Continuous s.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem map_liftedWilsonMeasure (K : ℕ) (β : ℝ)
    (v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) :
    (liftedWilsonMeasure L m K β).map (shift v).pullbackField =
      liftedWilsonMeasure L m K β := by
  have hτ := (continuous_pullbackField (shift v)).measurable
  have hp := measurable_liftField L m (K : ℤ)
  unfold liftedWilsonMeasure
  rw [Measure.map_map hτ hp]
  have h : (shift v).pullbackField ∘ liftField L m (K : ℤ) =
      liftField L m (K : ℤ) ∘ translateField (projectPoint L m (K : ℤ) v) :=
    funext fun U => pullbackField_liftField v U
  rw [h, ← Measure.map_map hp (measurable_translateField _), map_wilsonGibbsMeasure]
theorem isSymmetricUnder_of_map_eq {a : ℝ} {ν : Measure (GaugeField a)}
    {s : LatticeSymmetry a} (h : ν.map s.pullbackField = ν) : IsSymmetricUnder ν s := by
  intro A hA
  have e := integral_map (μ := ν) (continuous_pullbackField s).measurable.aemeasurable
    (f := A) hA.1.aestronglyMeasurable
  rw [h] at e
  exact e.symm
theorem wilsonGibbsMeasure_univ (K : ℕ) (β : ℝ)
    (hi : Integrable (PeriodicLattice.boltzmannWeight β)
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)))
    (hZ : 0 < PeriodicLattice.partitionFunction L m K β) :
    PeriodicLattice.wilsonGibbsMeasure L m K β univ = 1 := by apply _root_.YangMills.Construction.LiftFormation.wilsonGibbsMeasure_univ <;> assumption
theorem abs_terminal_sub_initial_le {a : ℝ} (ha : 0 ≤ a) (b : Link a) (ν : Fin 4) :
    |(b.terminal : AmbientSpace) ν - (b.initial : AmbientSpace) ν| ≤ a := by
  have hs : ∀ μ : Fin 4, |(Pi.single μ a : AmbientSpace) ν| ≤ a := fun μ => by
    by_cases h : ν = μ
    · subst h
      simp [abs_of_nonneg ha]
    · simp [Pi.single_eq_of_ne h, ha]
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · have e : (b.terminal : AmbientSpace) ν - (b.initial : AmbientSpace) ν =
        (Pi.single μ a : AmbientSpace) ν :=
      congrFun (congrArg Subtype.val h) ν
    rw [e]
    exact hs μ
  · have e : (b.terminal : AmbientSpace) ν - (b.initial : AmbientSpace) ν =
        -(Pi.single μ a : AmbientSpace) ν :=
      congrFun (congrArg Subtype.val h) ν
    rw [e, abs_neg]
    exact hs μ
theorem exists_shift_of_projectLink_eq (ha : 0 ≤ PeriodicLattice.meshSize L j)
    (hℓ : 2 * PeriodicLattice.meshSize L j < PeriodicLattice.torusSide L m)
    {b b' : Link (PeriodicLattice.meshSize L j)} (h : projectLink L m j b = projectLink L m j b') :
    ∃ v : LatticePoint (PeriodicLattice.meshSize L j),
      (∃ n : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = (n μ : ℝ) * PeriodicLattice.torusSide L m) ∧
        (shift v).linkMap b = b' := by
  have ht : TorusMetric.torusProj (PeriodicLattice.torusSide L m) (b'.initial : AmbientSpace) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (b.initial : AmbientSpace) :=
    (congrArg Subtype.val (congrArg PeriodicLattice.Bond.source h)).symm
  have hh : TorusMetric.torusProj (PeriodicLattice.torusSide L m) (b'.terminal : AmbientSpace) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (b.terminal : AmbientSpace) :=
    (congrArg Subtype.val (congrArg PeriodicLattice.Bond.target h)).symm
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq ht
  obtain ⟨k', hk'⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hh
  have hℓ0 : 0 < PeriodicLattice.torusSide L m := by linarith
  have hkk : k' = k := funext fun ν => by
    have e₁ := abs_terminal_sub_initial_le ha b ν
    have e₂ := abs_terminal_sub_initial_le ha b' ν
    have t := congrFun hk ν
    have t' := congrFun hk' ν
    simp only [Pi.add_apply, TestFunctions.latticeTranslate] at t t'
    rw [abs_le] at e₁ e₂
    have hd : PeriodicLattice.torusSide L m * ((k' ν : ℝ) - (k ν : ℝ)) <
        PeriodicLattice.torusSide L m * 1 := by
      linarith [e₁.1, e₁.2, e₂.1, e₂.2]
    have hd' : PeriodicLattice.torusSide L m * (-1) <
        PeriodicLattice.torusSide L m * ((k' ν : ℝ) - (k ν : ℝ)) := by
      linarith [e₁.1, e₁.2, e₂.1, e₂.2]
    have h₁ : ((k' ν : ℝ) - (k ν : ℝ)) < 1 := lt_of_mul_lt_mul_left hd hℓ0.le
    have h₂ : -1 < ((k' ν : ℝ) - (k ν : ℝ)) := lt_of_mul_lt_mul_left hd' hℓ0.le
    have h₁' : k' ν - k ν < 1 := by exact_mod_cast h₁
    have h₂' : -1 < k' ν - k ν := by exact_mod_cast h₂
    omega
  subst hkk
  refine ⟨b'.initial - b.initial, ⟨k', fun μ => ?_⟩, Link.ext ?_ ?_⟩
  · have t := congrFun hk μ
    simp only [Pi.add_apply, TestFunctions.latticeTranslate] at t
    change (b'.initial : AmbientSpace) μ - (b.initial : AmbientSpace) μ = _
    rw [t]
    ring
  · exact Subtype.ext (by
      change (b.initial : AmbientSpace) +
        ((b'.initial : AmbientSpace) - (b.initial : AmbientSpace)) = b'.initial
      abel)
  · exact Subtype.ext (by
      change (b.terminal : AmbientSpace) +
        ((b'.initial : AmbientSpace) - (b.initial : AmbientSpace)) = b'.terminal
      rw [hk, hk']
      abel)
theorem exists_projectLink_eq (c : PeriodicLattice.Bond L m j) :
    ∃ b : Link (PeriodicLattice.meshSize L j), projectLink L m j b = c := by apply _root_.YangMills.Construction.InfiniteLattice.FixedSpacing.exists_projectLink_eq <;> assumption
theorem projectPoint_eq_zero {v : LatticePoint (PeriodicLattice.meshSize L j)}
    (hv : ∃ n : Fin 4 → ℤ, ∀ μ,
      (v : AmbientSpace) μ = (n μ : ℝ) * PeriodicLattice.torusSide L m) :
    projectPoint L m j v = 0 := by
  obtain ⟨n, hn⟩ := hv
  refine Subtype.ext (funext fun μ => ?_)
  change (((v : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = 0
  rw [hn μ, AddCircle.coe_eq_zero_iff]
  exact ⟨n μ, by simp⟩
theorem apply_eq_of_projectLink_eq (ha : 0 ≤ PeriodicLattice.meshSize L j)
    (hℓ : 2 * PeriodicLattice.meshSize L j < PeriodicLattice.torusSide L m)
    {U : GaugeField (PeriodicLattice.meshSize L j)} (hU : U ∈ periodicFields L m j)
    {b b' : Link (PeriodicLattice.meshSize L j)} (h : projectLink L m j b = projectLink L m j b') :
    U b = U b' := by
  obtain ⟨v, hv, rfl⟩ := exists_shift_of_projectLink_eq ha hℓ h
  have e := congrArg (fun V : GaugeField (PeriodicLattice.meshSize L j) => V b) (hU v hv)
  exact e.symm
theorem bijOn_liftCompactField (ha : 0 ≤ PeriodicLattice.meshSize L j)
    (hℓ : 2 * PeriodicLattice.meshSize L j < PeriodicLattice.torusSide L m) :
    BijOn (liftCompactField : PeriodicLattice.CompactGaugeField L m j → _) univ
      (periodicFields L m j) := by
  refine ⟨fun W _ v hv => ?_, fun W _ W' _ h => ?_, fun U hU => ?_⟩
  · change (shift v).pullbackField (liftField L m j W.1) = liftField L m j W.1
    rw [pullbackField_liftField, projectPoint_eq_zero hv, translateField_zero]
  · refine Subtype.ext (funext fun c => ?_)
    obtain ⟨b, rfl⟩ := exists_projectLink_eq c
    have e := congrArg (fun V : GaugeField (PeriodicLattice.meshSize L j) => V b) h
    simp only [liftCompactField_apply] at e
    exact congrArg Subtype.val e
  · choose lift hlift using exists_projectLink_eq (L := L) (m := m) (j := j)
    have hf : ∀ c, U (lift c.opposite) = (U (lift c))⁻¹ := fun c => by
      rw [← U.2 (lift c)]
      refine apply_eq_of_projectLink_eq ha hℓ hU ?_
      rw [hlift, projectLink_opposite, hlift]
    refine ⟨PeriodicLattice.CompactGaugeField.ofLinkValues (fun c => U (lift c)) hf,
      mem_univ _, ?_⟩
    refine Subtype.ext (funext fun b => ?_)
    change liftCompactField _ b = U b
    rw [liftCompactField_apply, PeriodicLattice.CompactGaugeField.linkValue_ofLinkValues]
    exact apply_eq_of_projectLink_eq ha hℓ hU (hlift _)
theorem map_eq_of_integral_comp_eq {a : ℝ}
    (hm : TopologicalSpace.MetrizableSpace (GaugeField a))
    {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν] (φ : GaugeField a → GaugeField a)
    (hφ : Continuous φ)
    (h : ∀ F : GaugeField a → ℂ, Continuous F → ∫ U, F (φ U) ∂ν = ∫ U, F U ∂ν) :
    ν.map φ = ν := by
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  have : IsFiniteMeasure (ν.map φ) := Measure.isFiniteMeasure_map ν φ
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have e := h (fun U => ((f U : ℝ) : ℂ)) (Complex.continuous_ofReal.comp f.continuous)
  rw [integral_complex_ofReal, integral_complex_ofReal] at e
  rw [integral_map hφ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact_mod_cast e
theorem limitsAlongSides_shiftInvariant (L K : ℕ) (β : ℝ)
    (hm : TopologicalSpace.MetrizableSpace
      (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :
    LimitsAlongSidesAreShiftInvariant L K β := by
  rintro ν ⟨hp, n, -, -, hF⟩
  refine ⟨hp, fun v => isSymmetricUnder_of_map_eq ?_⟩
  have hφ := continuous_pullbackField (shift v)
  refine map_eq_of_integral_comp_eq hm _ hφ fun F hFc => ?_
  have hobs : ∀ i, ∫ U, F ((shift v).pullbackField U)
      ∂liftedWilsonMeasure L (n i) K β = ∫ U, F U ∂liftedWilsonMeasure L (n i) K β :=
    fun i => by
      have e := integral_map (μ := liftedWilsonMeasure L (n i) K β) hφ.measurable.aemeasurable
        (f := F) hFc.aestronglyMeasurable
      rw [map_liftedWilsonMeasure] at e
      exact e.symm
  have h₁ := hF (fun U => F ((shift v).pullbackField U)) (hFc.comp hφ)
  have h₂ := hF F hFc
  simp only [hobs] at h₁
  exact tendsto_nhds_unique h₁ h₂
end YangMills.Construction.InfiniteLattice.PeriodicStates
namespace YangMills.Construction.InfiniteLattice
open PeriodicStates in
theorem torusStatesAsPeriodic_holds
    (hDensity : PeriodicLattice.GaugeFieldSpace.FieldSpaceAndPartitionBounds)
    (hSpace : ConfigurationSpace.Main) :
    TorusStatesAsPeriodic.Statement := by
  intro s β hβ
  have hL : 13 ≤ s.L := s.isAdmissible.2
  have hL1 : (1 : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast (by omega : 1 ≤ s.L)
  have hL13 : (13 : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast hL
  have hapos : 0 < PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) := by
    unfold PeriodicLattice.meshSize
    exact zpow_pos (by linarith) _
  have hale : PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) ≤ 1 := by
    unfold PeriodicLattice.meshSize
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hside : (13 : ℝ) ≤ (s.L : ℝ) ^ (s.m : ℕ) :=
    hL13.trans (le_self_pow₀ hL1 s.m.pos.ne')
  have hℓ : 2 * PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) <
      PeriodicLattice.torusSide s.L s.m := by
    unfold PeriodicLattice.torusSide
    linarith
  obtain ⟨-, hb, -⟩ := hDensity s
  obtain ⟨hi, hlow, -⟩ := (hb β hβ).2
  have hZ : 0 < PeriodicLattice.partitionFunction s.L s.m s.K β :=
    (Real.exp_pos _).trans_le hlow
  have hsp := (hSpace _ hapos).1
  refine ⟨⟨fun W b => liftCompactField_apply W b, bijOn_liftCompactField hapos.le hℓ⟩,
    ⟨⟨?_⟩, fun v => isSymmetricUnder_of_map_eq (map_liftedWilsonMeasure _ _ v)⟩,
    limitsAlongSides_shiftInvariant _ _ _ hsp.2.2.2⟩
  rw [liftedWilsonMeasure, Measure.map_apply (measurable_liftField _ _ _)
    MeasurableSet.univ, preimage_univ]
  exact wilsonGibbsMeasure_univ _ _ hi hZ
end YangMills.Construction.InfiniteLattice
