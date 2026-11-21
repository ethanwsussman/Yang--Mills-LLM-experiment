import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.CellGridProperties
import YangMills.Construction.LawInAState.GridDataAtEveryExponent
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.EqualSideGridsAtEveryExponent
open PeriodicLattice (torusSide meshSize pointOnAxis)
open CellGrid EqualSideGrids
variable {L m : ℕ} {κ : ℤ} {d : CellGrid L κ}
theorem coe_inv_specialUnitary (g : Conventions.StandingParameters.gaugeGroup) :
    ((g⁻¹ : Conventions.StandingParameters.gaugeGroup) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem isForward_iff_edgeEquivBond (h : d.HasEqualSides m) (b : d.DirectedEdge) :
    b.IsForward ↔ (edgeEquivBond h b).IsPositivelyOriented := by
  refine exists_congr fun ν => ?_
  rw [isNeighbourStep_iff h _ _ ν (Or.inl rfl), one_mul]
  show _ ↔ gridPointEquivSite h b.target - gridPointEquivSite h b.source =
    PeriodicLattice.unitStep L m κ ν
  rw [sub_eq_iff_eq_add', Subtype.ext_iff]
  rfl
theorem edgeEquivBond_flip_eq_opposite (h : d.HasEqualSides m) (b : d.DirectedEdge) :
    edgeEquivBond h b.flip = (edgeEquivBond h b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
def forwardEdgeEquivBond (h : d.HasEqualSides m) :
    d.ForwardEdge ≃ PeriodicLattice.PositivelyOrientedBond L m κ :=
  (edgeEquivBond h).subtypeEquiv (isForward_iff_edgeEquivBond h)
def restrictToForwardBonds (h : d.HasEqualSides m) :
    d.GaugeConfig ≃ᵐ
      (PeriodicLattice.PositivelyOrientedBond L m κ → Matrices.ComplexMatrix2.specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (forwardEdgeEquivBond h)
theorem restrictToForwardBonds_apply (h : d.HasEqualSides m) (U : d.GaugeConfig)
    (c : d.ForwardEdge) :
    restrictToForwardBonds h U (forwardEdgeEquivBond h c) = U c :=
  Equiv.piCongrLeft_apply_apply (fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (forwardEdgeEquivBond h) U c
theorem map_restrictToForwardBonds (h : d.HasEqualSides m) :
    (BoxTorus.haarConfigMeasure L κ d.sideLengths).map (restrictToForwardBonds h) =
      PeriodicLattice.gaugeFieldHaar L m κ :=
  Measure.infinitePi_map_piCongrLeft (μ := fun _ => Matrices.ComplexMatrix2.haarProb)
    (forwardEdgeEquivBond h)
theorem toBondField_apply_edgeEquivBond (h : d.HasEqualSides m) (U : d.GaugeConfig)
    (b : d.DirectedEdge) :
    toBondField h U (edgeEquivBond h b) =
      (BoxTorus.edgeVariable U b : Matrices.ComplexMatrix2) := by
  show ((BoxTorus.edgeVariable U ((edgeEquivBond h).symm (edgeEquivBond h b)) : _) :
    Matrices.ComplexMatrix2) = _
  rw [Equiv.symm_apply_apply]
theorem gaugeFieldOfPositive_restrict (h : d.HasEqualSides m) (U : d.GaugeConfig) :
    PeriodicLattice.gaugeFieldOfPositive (restrictToForwardBonds h U) = toBondField h U := by
  funext b
  obtain ⟨b, rfl⟩ := (edgeEquivBond h).surjective b
  rw [toBondField_apply_edgeEquivBond]
  unfold PeriodicLattice.gaugeFieldOfPositive BoxTorus.edgeVariable
  by_cases hb : b.IsForward
  · rw [dif_pos ((isForward_iff_edgeEquivBond h b).mp hb), dif_pos hb]
    exact congrArg (fun x : Matrices.ComplexMatrix2.specialUnitary => (x : Matrices.ComplexMatrix2))
      (restrictToForwardBonds_apply h U ⟨b, hb⟩)
  · have hn : ¬ (edgeEquivBond h b).IsPositivelyOriented :=
      fun e => hb ((isForward_iff_edgeEquivBond h b).mpr e)
    have hr : b.flip.IsForward := BoxTorus.DirectedEdge.flip_isForward hb
    have hr' : (edgeEquivBond h b).opposite.IsPositivelyOriented := by
      rw [← edgeEquivBond_flip_eq_opposite]
      exact (isForward_iff_edgeEquivBond h _).mp hr
    have e : (⟨(edgeEquivBond h b).opposite, hr'⟩ :
        PeriodicLattice.PositivelyOrientedBond L m κ) =
        forwardEdgeEquivBond h ⟨b.flip, hr⟩ :=
      Subtype.ext (edgeEquivBond_flip_eq_opposite h b).symm
    rw [dif_neg hn, dif_pos hr', dif_neg hb, coe_inv_specialUnitary, e,
      restrictToForwardBonds_apply]
theorem measurable_gaugeFieldOfPositive_fun :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m κ → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m κ → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem toBondField_eq_gaugeFieldOfPositive_comp (h : d.HasEqualSides m) :
    toBondField h = PeriodicLattice.gaugeFieldOfPositive ∘ restrictToForwardBonds h :=
  funext fun U => (gaugeFieldOfPositive_restrict h U).symm
theorem toBondField_measurable (h : d.HasEqualSides m) : Measurable (toBondField h) := by
  rw [toBondField_eq_gaugeFieldOfPositive_comp]
  exact measurable_gaugeFieldOfPositive_fun.comp (restrictToForwardBonds h).measurable
theorem toBondField_apply_opposite (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) (U : d.GaugeConfig) (b : PeriodicLattice.Bond L m κ) :
    toBondField h U b.opposite = (toBondField h U b)⁻¹ := by
  obtain ⟨b, rfl⟩ := (edgeEquivBond h).surjective b
  rw [← edgeEquivBond_flip_eq_opposite, toBondField_apply_edgeEquivBond,
    toBondField_apply_edgeEquivBond, hl.1 U b, coe_inv_specialUnitary]
theorem gaugeFields_correspond (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) : SameGaugeFields h := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro U _
    exact ⟨fun b _ => (BoxTorus.edgeVariable U _).2,
      fun b _ => toBondField_apply_opposite hl h U b⟩
  · intro U _ U' _ e
    funext c
    apply Subtype.ext
    have hc := congrFun e (edgeEquivBond h c.1)
    rw [toBondField_apply_edgeEquivBond, toBondField_apply_edgeEquivBond] at hc
    have hU : ∀ W : d.GaugeConfig, BoxTorus.edgeVariable W c.1 = W c :=
      fun W => dif_pos c.2
    rwa [hU, hU] at hc
  · intro V hV
    let u : d.DirectedEdge → Conventions.StandingParameters.gaugeGroup :=
      fun b => ⟨V (edgeEquivBond h b), hV.1 _ (Set.mem_univ _)⟩
    have hu : ∀ b, u b.flip = (u b)⁻¹ := by
      intro b
      apply Subtype.ext
      rw [coe_inv_specialUnitary]
      show V (edgeEquivBond h b.flip) = (V (edgeEquivBond h b))⁻¹
      rw [edgeEquivBond_flip_eq_opposite]
      exact hV.2 _ (Set.mem_univ _)
    obtain ⟨U, hU, -⟩ := hl.2 u hu
    refine ⟨U, Set.mem_univ _, funext fun b => ?_⟩
    obtain ⟨b, rfl⟩ := (edgeEquivBond h).surjective b
    rw [toBondField_apply_edgeEquivBond, hU]
  · rw [toBondField_eq_gaugeFieldOfPositive_comp,
      ← Measure.map_map measurable_gaugeFieldOfPositive_fun (restrictToForwardBonds h).measurable,
      map_restrictToForwardBonds]
    rfl
theorem gridPointEquivSite_map_add (h : d.HasEqualSides m) (x y : d.GridPoint) :
    gridPointEquivSite h (x + y) = gridPointEquivSite h x + gridPointEquivSite h y :=
  Subtype.ext (map_add (spaceEquivTorus h) _ _)
theorem gridPointEquivSite_apply_gridStep (h : d.HasEqualSides m) (ν : Fin 4) :
    gridPointEquivSite h (BoxTorus.gridStep L κ d.sideLengths ν) =
      PeriodicLattice.unitStep L m κ ν :=
  Subtype.ext (spaceEquivTorus_smul_basisVector h ν _)
theorem edgeEquivBond_apply_edgeFrom (h : d.HasEqualSides m) (x : d.GridPoint) (ν : Fin 4) :
    edgeEquivBond h (BoxTorus.edgeFrom x ν) =
      PeriodicLattice.Bond.forwardFrom (gridPointEquivSite h x) ν :=
  PeriodicLattice.Bond.ext rfl (by
    show gridPointEquivSite h (x + BoxTorus.gridStep L κ d.sideLengths ν) = _
    rw [gridPointEquivSite_map_add, gridPointEquivSite_apply_gridStep]
    rfl)
def faceEquivPlaq (h : d.HasEqualSides m) : d.Face ≃ PeriodicLattice.Plaquette L m κ where
  toFun := plaquetteOfFace h
  invFun p := ⟨(gridPointEquivSite h).symm p.origin, p.firstAxis, p.secondAxis,
    p.firstAxis_lt_secondAxis⟩
  left_inv _ := BoxTorus.Face.ext ((gridPointEquivSite h).symm_apply_apply _) rfl rfl
  right_inv _ := PeriodicLattice.Plaquette.ext ((gridPointEquivSite h).apply_symm_apply _) rfl rfl
theorem faceHolonomy_eq_plaquetteHolonomy (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) (U : d.GaugeConfig) (p : d.Face) :
    (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy (toBondField h U) (plaquetteOfFace h p) := by
  have f : ∀ (x : d.GridPoint) (ν : Fin 4),
      toBondField h U (PeriodicLattice.Bond.forwardFrom (gridPointEquivSite h x) ν) =
        (BoxTorus.edgeVariable U (BoxTorus.edgeFrom x ν) : Matrices.ComplexMatrix2) :=
    fun x ν => by rw [← edgeEquivBond_apply_edgeFrom, toBondField_apply_edgeEquivBond]
  have r : ∀ (x : d.GridPoint) (ν : Fin 4),
      toBondField h U (PeriodicLattice.Bond.forwardFrom (gridPointEquivSite h x) ν).opposite =
        (BoxTorus.edgeVariable U (BoxTorus.edgeFrom x ν) : Matrices.ComplexMatrix2)⁻¹ :=
    fun x ν => by rw [toBondField_apply_opposite hl, f]
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, plaquetteOfFace, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [← gridPointEquivSite_apply_gridStep h p.dir₁, ← gridPointEquivSite_apply_gridStep h p.dir₂,
    ← gridPointEquivSite_map_add, ← gridPointEquivSite_map_add, f, f, r, r]
  simp only [BoxTorus.faceHolonomy, Submonoid.coe_mul, coe_inv_specialUnitary, mul_assoc]
theorem faceEnergy_eq_plaquetteCost (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) (U : d.GaugeConfig) (p : d.Face) :
    BoxTorus.faceEnergy U p =
      PeriodicLattice.plaquetteCost (toBondField h U) (plaquetteOfFace h p) := by
  rw [BoxTorus.faceEnergy, PeriodicLattice.plaquetteCost,
    faceHolonomy_eq_plaquetteHolonomy hl h]
theorem wilsonAction_eq_toBondField (hl : GridLattice.GaugeConfigsAsEdgeMaps d)
    (h : d.HasEqualSides m) (U : d.GaugeConfig) :
    d.wilsonAction U = PeriodicLattice.wilsonAction (toBondField h U) := by
  rw [CellGrid.wilsonAction, BoxTorus.wilsonAction, PeriodicLattice.wilsonAction,
    ← finsum_comp_equiv (faceEquivPlaq h)]
  exact finsum_congr fun p => faceEnergy_eq_plaquetteCost hl h U p
theorem continuous_plaquetteCost (p : PeriodicLattice.Plaquette L m κ) :
    Continuous fun U : PeriodicLattice.Bond L m κ → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by
  have hb : ∀ b : PeriodicLattice.Bond L m κ,
      Continuous fun U : PeriodicLattice.Bond L m κ → Matrices.ComplexMatrix2 => U b :=
    fun b => continuous_apply b
  have hv : Continuous fun U : PeriodicLattice.Bond L m κ → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteHolonomy U p := by
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    exact (hb _).matrix_mul ((hb _).matrix_mul ((hb _).matrix_mul (hb _)))
  unfold PeriodicLattice.plaquetteCost
  exact continuous_const.sub
    (continuous_const.mul (Complex.continuous_re.comp hv.matrix_trace))
theorem boltzmannWeight_measurable [Finite (PeriodicLattice.Plaquette L m κ)] (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight (L := L) (m := m) (j := κ) β) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hA : Continuous (PeriodicLattice.wilsonAction (L := L) (m := m) (j := κ)) := by
    cases nonempty_fintype (PeriodicLattice.Plaquette L m κ)
    have e : (PeriodicLattice.wilsonAction (L := L) (m := m) (j := κ)) =
        fun U => ∑ p, PeriodicLattice.plaquetteCost U p :=
      funext fun U => finsum_eq_sum_of_fintype _
    rw [e]
    exact continuous_finsetSum _ fun p _ => continuous_plaquetteCost p
  exact (Real.continuous_exp.comp (continuous_const.mul hA)).measurable
theorem map_withDensity_precomp {α β' : Type*} [MeasurableSpace α] [MeasurableSpace β']
    (μ : Measure α) {φ : α → β'} (hφ : Measurable φ) {g : β' → ENNReal} (hg : Measurable g) :
    (μ.withDensity (g ∘ φ)).map φ = (μ.map φ).withDensity g := by apply _root_.YangMills.SharedProofs.p22819 <;> assumption
theorem actionAndGibbsMeasure_correspond {K : ℕ} {d : CellGrid L (K : ℤ)}
    (hl : GridLattice.GaugeConfigsAsEdgeMaps d) (h : d.HasEqualSides m) (β : ℝ) :
    SameActionAndGibbsMeasure h β := by
  have hfin : Finite (PeriodicLattice.Plaquette L m (K : ℤ)) :=
    Finite.of_equiv _ (faceEquivPlaq h)
  have hm := toBondField_measurable h
  have hmap := (gaugeFields_correspond hl h).2
  have hρ := boltzmannWeight_measurable (L := L) (m := m) (κ := (K : ℤ)) β
  have hw : ∀ U, d.boltzmannFactor β U =
      PeriodicLattice.boltzmannWeight β (toBondField h U) := fun U => by
    rw [CellGrid.boltzmannFactor, wilsonAction_eq_toBondField hl h,
      PeriodicLattice.boltzmannWeight]
  have hZ : d.normalizingIntegral β = PeriodicLattice.partitionFunction L m K β := by
    rw [PeriodicLattice.partitionFunction, ← hmap, integral_map hm.aemeasurable
      hρ.aestronglyMeasurable, CellGrid.normalizingIntegral]
    exact integral_congr_ae (Filter.Eventually.of_forall hw)
  have hμ : (d.gibbsMeasure β).map (toBondField h) =
      PeriodicLattice.wilsonGibbsMeasure L m K β := by
    have hd : (fun U => ENNReal.ofReal (d.boltzmannFactor β U)) =
        (fun V => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β V)) ∘ toBondField h :=
      funext fun U => by simp only [Function.comp, hw]
    rw [CellGrid.gibbsMeasure, PeriodicLattice.wilsonGibbsMeasure, hZ, Measure.map_smul, hd,
      map_withDensity_precomp _ hm hρ.ennreal_ofReal, hmap]
  refine ⟨fun U p => ⟨faceHolonomy_eq_plaquetteHolonomy hl h U p,
      faceEnergy_eq_plaquetteCost hl h U p⟩,
    wilsonAction_eq_toBondField hl h, hZ, hμ, fun F hF _ => ?_⟩
  rw [PeriodicLattice.gibbsExpectation, ← hμ,
    integral_map hm.aemeasurable hF.aestronglyMeasurable, CellGrid.gibbsMean]
theorem atEveryExponent (hl : GridLattice.Properties) : EqualSideGrids.AtEveryExponent := by
  intro L m K d h β
  have hc : GridLattice.GaugeConfigsAsEdgeMaps d := (hl _ _ d).2.2.1
  exact ⟨gaugeFields_correspond hc h, actionAndGibbsMeasure_correspond hc h β⟩
end YangMills.Construction.EqualSideGridsAtEveryExponent
end
