import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroup
import YangMills.Construction.Lattice.CellGridGibbsMeasure
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction
open BoxTorus
open PeriodicLattice (meshSize)
namespace CubicGridFields
open BlockAverages WeightedResponses TorusFields ClusterExpansionOfAStep
def cubicCellGrid (c M : ℕ) (u : Fin 4 → ℤ) (hc : Odd c) (hM : Even M) (hM0 : 0 < M) (h4 : 4 ≤ c * M) : CellGrid 13 0 where
  admissible := ⟨by decide, le_rfl⟩
  cellLength := c
  cellLength_pos := by exact_mod_cast hc.pos
  cellLength_div_meshSize := ⟨c, by simp [meshSize]⟩
  counts := fun _ => M
  counts_pos := fun _ => hM0
  counts_even := fun _ => hM
  four_meshSize_le := fun _ => by
    have h : ((4 : ℕ) : ℝ) ≤ ((c * M : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h
    simp only [meshSize, neg_zero, zpow_zero, mul_one]
    linarith
  centre := fun μ => (u μ : ℝ) - (c : ℝ) / 2
  centre_mem := fun μ => by
    obtain ⟨r, hr⟩ := hc
    refine ⟨u μ - r - 1, ?_⟩
    simp only [meshSize, neg_zero, zpow_zero, one_mul, hr]
    push_cast
    ring
theorem meshSize_zero_eq_one : meshSize 13 0 = 1 := by simp [meshSize]
section Sites
variable {d : CellGrid 13 0} {m : ℕ}
def pointOfCoords (d : CellGrid 13 0) (z : Fin 4 → ℤ) : d.GridPoint :=
  ⟨projection d.sideLengths fun μ => (z μ : ℝ) * meshSize 13 0, ⟨z, rfl⟩⟩
theorem pointOfCoords_eq_iff (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (a b : Fin 4 → ℤ) :
    pointOfCoords d a = pointOfCoords d b ↔ ∀ μ, (a μ : ZMod m) = (b μ : ZMod m) := by
  have key : ∀ μ, (((a μ : ℝ) * meshSize 13 0 : ℝ) : AddCircle (d.sideLengths μ)) =
      (((b μ : ℝ) * meshSize 13 0 : ℝ) : AddCircle (d.sideLengths μ)) ↔ (a μ : ZMod m) = (b μ : ZMod m) := by
    intro μ
    rw [meshSize_zero_eq_one, mul_one, mul_one, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff,
      ← sub_eq_zero (a := (a μ : ZMod m)), ← Int.cast_sub (R := ZMod m), CharP.intCast_eq_zero_iff (ZMod m) m]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, hd μ] at hk
      have : ((a μ - b μ : ℤ) : ℝ) = ((m * k : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, hd μ]
      have : ((a μ : ℝ) - b μ) = (m : ℝ) * k := by exact_mod_cast hk
      rw [this]
      ring
  constructor
  · intro h μ
    have h1 : (fun ν : Fin 4 => ((((a ν : ℝ) * meshSize 13 0 : ℝ)) : AddCircle (d.sideLengths ν))) =
        fun ν => ((((b ν : ℝ) * meshSize 13 0 : ℝ)) : AddCircle (d.sideLengths ν)) := congrArg Subtype.val h
    exact (key μ).mp (congrFun h1 μ)
  · intro h
    refine Subtype.ext ?_
    show (fun ν : Fin 4 => ((((a ν : ℝ) * meshSize 13 0 : ℝ)) : AddCircle (d.sideLengths ν))) =
        fun ν => ((((b ν : ℝ) * meshSize 13 0 : ℝ)) : AddCircle (d.sideLengths ν))
    exact funext fun μ => (key μ).mpr (h μ)
theorem pointOfCoords_add (a b : Fin 4 → ℤ) : pointOfCoords d (a + b) = pointOfCoords d a + pointOfCoords d b := by
  refine Subtype.ext ?_
  show projection d.sideLengths _ = projection d.sideLengths _ + projection d.sideLengths _
  rw [← map_add]
  congr 1
  funext μ
  simp [add_mul]
theorem gridStep_eq_pointOfCoords (ν : Fin 4) : gridStep 13 0 d.sideLengths ν = pointOfCoords d (Pi.single ν 1) := by
  refine Subtype.ext ?_
  show projection d.sideLengths _ = projection d.sideLengths _
  congr 1
  funext μ
  by_cases h : μ = ν
  · subst h
    simp [basisVector]
  · simp [basisVector, Pi.single_eq_of_ne h]
def ofTorusSite (d : CellGrid 13 0) (x : TorusSite m) : d.GridPoint := pointOfCoords d fun μ => ((x μ).cast : ℤ)
def toTorusSite (m : ℕ) (s : d.GridPoint) : TorusSite m := fun μ => ((s.2.choose μ : ℤ) : ZMod m)
theorem pointOfCoords_choose (s : d.GridPoint) : pointOfCoords d s.2.choose = s :=
  Subtype.ext s.2.choose_spec.symm
variable [NeZero m]
theorem toTorusSite_ofTorusSite (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (x : TorusSite m) :
    toTorusSite m (ofTorusSite d x) = x := by
  funext μ
  have h := (pointOfCoords_eq_iff hd _ _).mp (pointOfCoords_choose (ofTorusSite d x)) μ
  rw [show ((ofTorusSite d x).2.choose) = ((ofTorusSite d x).2.choose) from rfl] at h
  refine h.trans ?_
  simp
theorem ofTorusSite_toTorusSite (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (s : d.GridPoint) :
    ofTorusSite d (toTorusSite m s) = s := by
  conv_rhs => rw [← pointOfCoords_choose s]
  refine (pointOfCoords_eq_iff hd _ _).mpr fun μ => ?_
  simp [toTorusSite]
theorem ofTorusSite_siteOfInt (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (z : Fin 4 → ℤ) :
    ofTorusSite d (siteOfInt z : TorusSite m) = pointOfCoords d z :=
  (pointOfCoords_eq_iff hd _ _).mpr fun μ => by simp [siteOfInt]
theorem ofTorusSite_injective (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) :
    Function.Injective (ofTorusSite d : TorusSite m → d.GridPoint) :=
  Function.LeftInverse.injective (toTorusSite_ofTorusSite hd)
theorem ofTorusSite_add_unitStep (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (x : TorusSite m) (ν : Fin 4) :
    ofTorusSite d (x + TorusFields.unitStep m ν) = ofTorusSite d x + gridStep 13 0 d.sideLengths ν := by
  rw [gridStep_eq_pointOfCoords, ofTorusSite, ofTorusSite, ← pointOfCoords_add, pointOfCoords_eq_iff hd]
  intro μ
  simp only [ZMod.intCast_zmod_cast, Pi.add_apply, Int.cast_add, TorusFields.unitStep, Pi.single_apply]
  split_ifs <;> simp
end Sites
section Links
variable {d : CellGrid 13 0} {m : ℕ} [NeZero m]
theorem edgeFrom_isForward (s : d.GridPoint) (ν : Fin 4) : (edgeFrom s ν).IsForward :=
  ⟨ν, Or.inl rfl, by simp [edgeFrom, BoxTorus.translate, gridStep]⟩
def forwardEdgeOf (d : CellGrid 13 0) (p : TorusSite m × Fin 4) : d.ForwardEdge :=
  ⟨edgeFrom (ofTorusSite d p.1) p.2, edgeFrom_isForward _ _⟩
theorem target_eq_of_isNeighbourStep {b : d.DirectedEdge} {ν : Fin 4} (h : IsNeighbourStep b.source b.target ν 1) :
    b.target = b.source + gridStep 13 0 d.sideLengths ν := by
  refine Subtype.ext ?_
  have h2 := h.2
  simp only [BoxTorus.translate, one_mul] at h2
  exact h2
theorem gridStep_injective (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) {ν ν' : Fin 4}
    (h : gridStep 13 0 d.sideLengths ν = gridStep 13 0 d.sideLengths ν') : ν = ν' := by
  haveI : Fact (1 < m) := ⟨by omega⟩
  by_contra e
  rw [gridStep_eq_pointOfCoords, gridStep_eq_pointOfCoords, pointOfCoords_eq_iff hd] at h
  have h3 := h ν
  simp [Pi.single_eq_of_ne e] at h3
theorem forwardEdgeOf_bijective (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) :
    Function.Bijective (forwardEdgeOf d : TorusSite m × Fin 4 → d.ForwardEdge) := by
  constructor
  · rintro ⟨x, ν⟩ ⟨x', ν'⟩ h
    have h1 : edgeFrom (ofTorusSite d x) ν = edgeFrom (ofTorusSite d x') ν' := congrArg Subtype.val h
    have ht : ofTorusSite d x = ofTorusSite d x' := congrArg BoxTorus.DirectedEdge.source h1
    have hh : ofTorusSite d x + gridStep 13 0 d.sideLengths ν = ofTorusSite d x' + gridStep 13 0 d.sideLengths ν' :=
      congrArg BoxTorus.DirectedEdge.target h1
    rw [ht] at hh
    have hν := gridStep_injective hd h2 (add_left_cancel hh)
    rw [ofTorusSite_injective hd ht, hν]
  · rintro ⟨b, ν, h⟩
    refine ⟨(toTorusSite m b.source, ν), Subtype.ext (BoxTorus.DirectedEdge.ext ?_ ?_)⟩
    · exact ofTorusSite_toTorusSite hd _
    · show ofTorusSite d (toTorusSite m b.source) + gridStep 13 0 d.sideLengths ν = b.target
      rw [ofTorusSite_toTorusSite hd, target_eq_of_isNeighbourStep h]
def forwardEdgeEquiv (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) : TorusSite m × Fin 4 ≃ d.ForwardEdge :=
  Equiv.ofBijective _ (forwardEdgeOf_bijective hd h2)
def configOfField (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (W : TorusField m) : d.GaugeConfig :=
  fun b => unitQuaternionEquivSpecialUnitary
    (W ((forwardEdgeEquiv hd h2).symm b).1 ((forwardEdgeEquiv hd h2).symm b).2)
def fieldOfConfig (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (U : d.GaugeConfig) : TorusField m :=
  fun x ν => unitQuaternionEquivSpecialUnitary.symm (U (forwardEdgeEquiv hd h2 (x, ν)))
theorem configOfField_forwardEdgeOf (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (W : TorusField m)
    (x : TorusSite m) (ν : Fin 4) :
    configOfField hd h2 W (forwardEdgeOf d (x, ν)) = unitQuaternionEquivSpecialUnitary (W x ν) := by
  have e : (forwardEdgeEquiv hd h2).symm (forwardEdgeOf d (x, ν)) = (x, ν) :=
    (forwardEdgeEquiv hd h2).symm_apply_apply (x, ν)
  simp only [configOfField, e]
theorem fieldOfConfig_configOfField (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (W : TorusField m) :
    fieldOfConfig hd h2 (configOfField hd h2 W) = W := by
  funext x ν
  simp only [fieldOfConfig]
  have : forwardEdgeEquiv hd h2 (x, ν) = forwardEdgeOf d (x, ν) := rfl
  rw [this, configOfField_forwardEdgeOf]
  simp
theorem configOfField_fieldOfConfig (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (U : d.GaugeConfig) :
    configOfField hd h2 (fieldOfConfig hd h2 U) = U := by
  funext b
  obtain ⟨p, rfl⟩ := (forwardEdgeEquiv hd h2).surjective b
  have : forwardEdgeEquiv hd h2 p = forwardEdgeOf d p := rfl
  rw [this]
  obtain ⟨x, ν⟩ := p
  rw [configOfField_forwardEdgeOf]
  simp [fieldOfConfig]
  rfl
theorem edgeVariable_edgeFrom (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (W : TorusField m)
    (x : TorusSite m) (ν : Fin 4) :
    edgeVariable (configOfField hd h2 W) (edgeFrom (ofTorusSite d x) ν) = unitQuaternionEquivSpecialUnitary (W x ν) := by
  rw [edgeVariable, dif_pos (edgeFrom_isForward _ _)]
  exact configOfField_forwardEdgeOf hd h2 W x ν
theorem measurable_configOfField (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) :
    Measurable (configOfField (d := d) hd h2) := by
  refine measurable_pi_iff.mpr fun b => ?_
  exact unitQuaternionEquivSpecialUnitary.continuous.measurable.comp
    ((measurable_pi_apply _).comp (measurable_pi_apply _))
theorem measurable_fieldOfConfig (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) :
    Measurable (fieldOfConfig (d := d) hd h2) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun ν => ?_
  exact unitQuaternionEquivSpecialUnitary.symm.continuous.measurable.comp (measurable_pi_apply _)
theorem map_fieldHaar (h1 : haarUnit.map unitQuaternionEquivSpecialUnitary = Matrices.ComplexMatrix2.haarProb)
    (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) :
    (fieldHaar m).map (configOfField (d := d) hd h2) = haarConfigMeasure 13 0 d.sideLengths := by
  haveI : Finite d.ForwardEdge := Finite.of_equiv _ (forwardEdgeEquiv hd h2)
  letI : Fintype d.ForwardEdge := Fintype.ofFinite _
  have hm : Measurable unitQuaternionEquivSpecialUnitary := unitQuaternionEquivSpecialUnitary.continuous.measurable
  have hh : ∀ A : Set Matrices.ComplexMatrix2.specialUnitary, MeasurableSet A →
      haarUnit (unitQuaternionEquivSpecialUnitary ⁻¹' A) = Matrices.ComplexMatrix2.haarProb A :=
    fun A hA => by rw [← h1, Measure.map_apply hm hA]
  rw [haarConfigMeasure, Matrices.ComplexMatrix2.haarPi, Measure.infinitePi_eq_pi]
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply (measurable_configOfField hd h2) (MeasurableSet.univ_pi ht)]
  have hset : configOfField (d := d) hd h2 ⁻¹' Set.pi Set.univ t =
      Set.pi Set.univ fun x => Set.pi Set.univ fun ν =>
        unitQuaternionEquivSpecialUnitary ⁻¹' t (forwardEdgeEquiv hd h2 (x, ν)) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h x ν
      have := h (forwardEdgeEquiv hd h2 (x, ν))
      have e : forwardEdgeEquiv hd h2 (x, ν) = forwardEdgeOf d (x, ν) := rfl
      rw [e] at this ⊢
      rwa [configOfField_forwardEdgeOf hd h2] at this
    · intro h b
      obtain ⟨⟨x, ν⟩, rfl⟩ := (forwardEdgeEquiv hd h2).surjective b
      have e : forwardEdgeEquiv hd h2 (x, ν) = forwardEdgeOf d (x, ν) := rfl
      have := h x ν
      rw [e] at this ⊢
      rw [configOfField_forwardEdgeOf hd h2]
      exact this
  rw [hset, fieldHaar, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hh _ (ht _)]
  rw [← Fintype.prod_prod_type
    (f := fun p : TorusSite m × Fin 4 => Matrices.ComplexMatrix2.haarProb (t (forwardEdgeEquiv hd h2 p)))]
  exact Fintype.prod_equiv (forwardEdgeEquiv hd h2) _ _ fun _ => rfl
def faceEquiv (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) : {p : TorusPlaquette m // p.2.1 < p.2.2} ≃ d.Face where
  toFun p := ⟨ofTorusSite d p.1.1, p.1.2.1, p.1.2.2, p.2⟩
  invFun p := ⟨(toTorusSite m p.corner, p.dir₁, p.dir₂), p.dir₁_lt_dir₂⟩
  left_inv p := Subtype.ext (Prod.ext (toTorusSite_ofTorusSite hd _) rfl)
  right_inv p := BoxTorus.Face.ext (ofTorusSite_toTorusSite hd _) rfl rfl
theorem faceHolonomy_configOfField (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m) (W : TorusField m)
    (x : TorusSite m) (μ ν : Fin 4) (h : μ < ν) :
    faceHolonomy (configOfField hd h2 W) ⟨ofTorusSite d x, μ, ν, h⟩ =
      unitQuaternionEquivSpecialUnitary (holonomy W x μ ν) := by
  simp only [faceHolonomy]
  rw [← ofTorusSite_add_unitStep hd, ← ofTorusSite_add_unitStep hd, edgeVariable_edgeFrom, edgeVariable_edgeFrom,
    edgeVariable_edgeFrom, edgeVariable_edgeFrom]
  simp only [holonomy, map_mul, map_inv]
theorem wilsonAction_configOfField (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (hd : ∀ μ, d.sideLengths μ = (m : ℝ))
    (h2 : 2 < m) (W : TorusField m) :
    d.wilsonAction (configOfField hd h2 W) = TorusFields.wilsonAction Finset.univ W := by
  classical
  haveI : Finite d.Face := inferInstance
  show BoxTorus.wilsonAction _ = _
  rw [BoxTorus.wilsonAction, ← finsum_comp_equiv (faceEquiv hd), finsum_eq_sum_of_fintype]
  unfold TorusFields.wilsonAction
  have hmem : ∀ p : TorusPlaquette m, p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) ↔ p.2.1 < p.2.2 := by
    intro p
    simp [plaquettesIn]
  rw [Finset.sum_subtype _ hmem]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨⟨x, μ, ν⟩, h⟩ := p
  show BoxTorus.faceEnergy _ ⟨ofTorusSite d x, μ, ν, h⟩ = plaquetteEnergy W x μ ν
  unfold BoxTorus.faceEnergy plaquetteEnergy
  rw [faceHolonomy_configOfField hd h2 W x μ ν h, (hq.2.1 _).1]
theorem normalizingIntegral_eq (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (hd : ∀ μ, d.sideLengths μ = (m : ℝ))
    (h2 : 2 < m) (β : ℝ) :
    d.normalizingIntegral β = ∫ W, Real.exp (-β * TorusFields.wilsonAction Finset.univ W) ∂(fieldHaar m) := by
  have hc : Measurable fun U : d.GaugeConfig =>
      Real.exp (-β * TorusFields.wilsonAction Finset.univ (fieldOfConfig hd h2 U)) :=
    (Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))).measurable.comp
      (measurable_fieldOfConfig hd h2)
  have hb : (fun U : d.GaugeConfig => d.boltzmannFactor β U) =
      fun U => Real.exp (-β * TorusFields.wilsonAction Finset.univ (fieldOfConfig hd h2 U)) := by
    funext U
    unfold CellGrid.boltzmannFactor
    rw [← wilsonAction_configOfField hq hd h2, configOfField_fieldOfConfig]
  unfold CellGrid.normalizingIntegral
  rw [hb, ← map_fieldHaar hq.1 hd h2, integral_map (measurable_configOfField hd h2).aemeasurable
    hc.aestronglyMeasurable]
  simp only [fieldOfConfig_configOfField]
theorem map_wilsonLaw (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m)
    (β : ℝ) : (wilsonLaw β m).map (configOfField (d := d) hd h2) = d.gibbsMeasure β := by
  have hcf := measurable_configOfField (d := d) hd h2
  set Z : ℝ := ∫ W, Real.exp (-β * TorusFields.wilsonAction Finset.univ W) ∂(fieldHaar m) with hZ
  have hcont : Continuous fun W : TorusField m => Real.exp (-β * TorusFields.wilsonAction Finset.univ W) :=
    Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))
  have hZ0 : 0 < Z := integral_exp_pos (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hexp : Measurable fun W : TorusField m => ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ W)) :=
    (Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))).measurable.ennreal_ofReal
  have hb : Measurable fun U : d.GaugeConfig => ENNReal.ofReal (d.boltzmannFactor β U) := by
    have e : (fun U : d.GaugeConfig => ENNReal.ofReal (d.boltzmannFactor β U)) =
        fun U => ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ (fieldOfConfig hd h2 U))) := by
      funext U
      unfold CellGrid.boltzmannFactor
      rw [← wilsonAction_configOfField hq hd h2, configOfField_fieldOfConfig]
    rw [e]
    exact hexp.comp (measurable_fieldOfConfig hd h2)
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hcf hA, CellGrid.gibbsMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA, normalizingIntegral_eq hq hd h2, ← map_fieldHaar hq.1 hd h2,
    setLIntegral_map hA hb hcf, wilsonLaw, withDensity_apply _ (hcf hA)]
  have e1 : ∀ W : TorusField m, ENNReal.ofReal (d.boltzmannFactor β (configOfField hd h2 W)) =
      ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ W)) := fun W => by
    unfold CellGrid.boltzmannFactor
    rw [wilsonAction_configOfField hq hd h2]
  have e2 : ∀ W : TorusField m, ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ W) / Z) =
      (ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ W)) := fun W => by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hZ0.le), ENNReal.ofReal_inv_of_pos hZ0]
  simp only [← hZ, e1, e2]
  rw [lintegral_const_mul _ hexp]
theorem gibbsMean_eq (hq : ClusterExpansionOfAStep.UnitQuaternionHaarTraceNorm) (hd : ∀ μ, d.sideLengths μ = (m : ℝ)) (h2 : 2 < m)
    (β : ℝ) {F : d.GaugeConfig → ℂ} (hF : Measurable F) :
    d.gibbsMean β F = ∫ W, F (configOfField hd h2 W) ∂(wilsonLaw β m) := by
  unfold CellGrid.gibbsMean
  rw [← map_wilsonLaw hq hd h2, integral_map (measurable_configOfField hd h2).aemeasurable
    hF.aestronglyMeasurable]
end Links
end CubicGridFields
end YangMills.Construction
end
