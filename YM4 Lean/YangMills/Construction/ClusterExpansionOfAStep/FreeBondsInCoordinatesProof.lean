import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixingOfTheStepProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory Measure
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings StepCosts ColdStepAtMirrorFrames
namespace FreeChart
open BlockTrees
abbrev ImCoords : Type := EuclideanSpace ℝ (Fin 3)
section Haar
theorem continuous_toImaginary : Continuous (fun v : ImCoords => (toImaginary v : ℍ[ℝ])) := by
  have e : (fun v : ImCoords => (toImaginary v : ℍ[ℝ])) = fun v : ImCoords =>
      (v 0) • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) + (v 1) • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) + (v 2) • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
    funext v
    ext <;> simp [toImaginary]
  rw [e]
  have c : ∀ i, Continuous fun v : ImCoords => v i :=
    fun i => (EuclideanSpace.proj i : ImCoords →L[ℝ] ℝ).continuous
  exact (((c 0).smul continuous_const).add ((c 1).smul continuous_const)).add
    ((c 2).smul continuous_const)
def expCoords (v : ImCoords) : UnitQuaternion := expUnit (toImaginary v)
theorem continuous_expCoords : Continuous expCoords := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.continuous_expLog <;> assumption
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem haarLogDensity_nonneg (v : ImCoords) : 0 ≤ haarLogDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.haarLogDensity_nonneg <;> assumption
def haarOnCoords : Measure ImCoords := volume.withDensity fun v => ENNReal.ofReal (haarLogDensity v)
theorem integrable_haarLogDensity (hH : HaarIntegralInLogCoords) :
    Integrable haarLogDensity ∧ ∫ v, haarLogDensity v = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixing.integrable_haarLogDensity <;> assumption
theorem isFiniteMeasure_haarOnCoords (hH : HaarIntegralInLogCoords) : IsFiniteMeasure haarOnCoords := by
  constructor
  unfold haarOnCoords
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_haarLogDensity hH).1
    (Filter.Eventually.of_forall haarLogDensity_nonneg), (integrable_haarLogDensity hH).2]
  simp
theorem map_expCoords_haarOnCoords (hH : HaarIntegralInLogCoords) :
    Measure.map expCoords haarOnCoords = haarUnit := by
  have := isFiniteMeasure_haarOnCoords hH
  have hm : Measurable fun v : ImCoords => ENNReal.ofReal (haarLogDensity v) :=
    ENNReal.measurable_ofReal.comp measurable_haarLogDensity
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map continuous_expCoords.aemeasurable f.continuous.aestronglyMeasurable, haarOnCoords,
    integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    hH f f.continuous]
  apply integral_congr_ae
  filter_upwards with v
  rw [ENNReal.toReal_ofReal (haarLogDensity_nonneg v)]
  rfl
def piBall : Set ImCoords := Metric.ball 0 Real.pi
theorem measurableSet_piBall : MeasurableSet piBall := measurableSet_ball
def haarOnBall : Measure piBall := haarOnCoords.comap Subtype.val
theorem measurePreserving_coe_piBall :
    MeasurePreserving (Subtype.val : piBall → ImCoords) haarOnBall haarOnCoords := by
  refine ⟨measurable_subtype_coe, ?_⟩
  unfold haarOnBall
  rw [map_comap_subtype_coe measurableSet_piBall]
  apply Measure.restrict_eq_self_of_ae_mem
  have hm : Measurable fun v : ImCoords => ENNReal.ofReal (haarLogDensity v) :=
    ENNReal.measurable_ofReal.comp measurable_haarLogDensity
  unfold haarOnCoords
  rw [ae_withDensity_iff hm]
  filter_upwards with v hv
  by_contra hb
  apply hv
  have : ¬ ‖v‖ < Real.pi := by simpa [piBall] using hb
  simp [haarLogDensity, this]
theorem isFiniteMeasure_haarOnBall (hH : HaarIntegralInLogCoords) : IsFiniteMeasure haarOnBall := by
  have := isFiniteMeasure_haarOnCoords hH
  constructor
  have h1 := measurePreserving_coe_piBall.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  rw [Set.preimage_univ] at h1
  rw [h1]
  exact measure_lt_top _ _
theorem pi_haarOnCoords {ι : Type} [Fintype ι] (hH : HaarIntegralInLogCoords) :
    Measure.pi (fun _ : ι => haarOnCoords) =
      (volume : Measure (ι → ImCoords)).withDensity fun v => ∏ b, ENNReal.ofReal (haarLogDensity (v b)) := by
  classical
  have := isFiniteMeasure_haarOnCoords hH
  have hm : Measurable fun v : ImCoords => ENNReal.ofReal (haarLogDensity v) :=
    ENNReal.measurable_ofReal.comp measurable_haarLogDensity
  have hI := (integrable_haarLogDensity hH).1
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  set f : ι → ImCoords → ℝ := fun b => (s b).indicator haarLogDensity with hf
  have hfn : ∀ b v, 0 ≤ f b v := fun b v => Set.indicator_nonneg (fun x _ => haarLogDensity_nonneg x) v
  have hfi : ∀ b, Integrable (f b) := fun b => hI.indicator (hs b)
  have h1 : ∀ v : ι → ImCoords, (Set.univ.pi s).indicator
      (fun v : ι → ImCoords => ∏ b, ENNReal.ofReal (haarLogDensity (v b))) v =
        ENNReal.ofReal (∏ b, f b (v b)) := by
    intro v
    rw [ENNReal.ofReal_prod_of_nonneg fun b _ => hfn b _]
    by_cases hv : v ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hv]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hf]
      simp only
      rw [Set.indicator_of_mem (hv b (Set.mem_univ b))]
    · rw [Set.indicator_of_notMem hv]
      obtain ⟨b, hb⟩ : ∃ b, v b ∉ s b := by
        by_contra hcon
        push Not at hcon
        exact hv fun b _ => hcon b
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      rw [hf]
      simp only
      rw [Set.indicator_of_notMem hb]
      simp
  simp only [h1]
  have hint : Integrable (fun v : ι → ImCoords => ∏ b, f b (v b)) (volume : Measure (ι → ImCoords)) :=
    Integrable.fintype_prod hfi
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun v => Finset.prod_nonneg fun b _ => hfn b _),
    integral_fintype_prod_volume_eq_prod f,
    ENNReal.ofReal_prod_of_nonneg fun b _ => integral_nonneg (hfn b)]
  refine Finset.prod_congr rfl fun b _ => ?_
  unfold haarOnCoords
  rw [withDensity_apply _ (hs b), ← lintegral_indicator (hs b),
    ofReal_integral_eq_lintegral_ofReal (hfi b) (Filter.Eventually.of_forall (hfn b))]
  apply lintegral_congr
  intro v
  by_cases hv : v ∈ s b
  · simp [hf, Set.indicator_of_mem hv]
  · simp [hf, Set.indicator_of_notMem hv]
end Haar
section Invariance
theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
instance : IsMulRightInvariant haarUnit := by
  constructor
  intro g
  have : IsMulLeftInvariant (map (· * g) haarUnit) := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
theorem measurePreserving_mul_mul (g h : UnitQuaternion) :
    MeasurePreserving (fun u : UnitQuaternion => g * u * h) haarUnit haarUnit :=
  (measurePreserving_mul_right haarUnit h).comp (measurePreserving_mul_left haarUnit g)
variable {m : ℕ} [NeZero m]
def bondHaar (m : ℕ) [NeZero m] : Measure (TorusBond m → UnitQuaternion) :=
  Measure.pi fun _ : TorusBond m => haarUnit
theorem measurePreserving_curry_symm :
    MeasurePreserving (MeasurableEquiv.curry (TorusSite m) (Fin 4) UnitQuaternion).symm
      (fieldHaar m) (bondHaar m) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurePreserving_uncurry_fieldHaar <;> assumption
theorem measurePreserving_skew_exp {I J B : Type} [Fintype I] [Fintype J] [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (e : B → UnitQuaternion) (he : MeasurePreserving e ν haarUnit)
    (val : (J → UnitQuaternion) → I → UnitQuaternion → UnitQuaternion)
    (hm : ∀ b, Measurable fun p : (J → UnitQuaternion) × UnitQuaternion => val p.1 b p.2)
    (hv : ∀ t b, MeasurePreserving (val t b) haarUnit haarUnit) :
    MeasurePreserving
      (fun p : (J → UnitQuaternion) × (I → B) => (p.1, fun b => val p.1 b (e (p.2 b))))
      ((Measure.pi fun _ : J => haarUnit).prod (Measure.pi fun _ : I => ν))
      ((Measure.pi fun _ : J => haarUnit).prod (Measure.pi fun _ : I => haarUnit)) := by
  have h1 : MeasurePreserving (fun (v : I → B) b => e (v b))
      (Measure.pi fun _ : I => ν) (Measure.pi fun _ : I => haarUnit) :=
    measurePreserving_pi _ _ fun _ => he
  have h2 : MeasurePreserving
      (fun p : (J → UnitQuaternion) × (I → UnitQuaternion) => (p.1, fun b => val p.1 b (p.2 b)))
      ((Measure.pi fun _ : J => haarUnit).prod (Measure.pi fun _ : I => haarUnit))
      ((Measure.pi fun _ : J => haarUnit).prod (Measure.pi fun _ : I => haarUnit)) := by
    have hu : Measurable (Function.uncurry
        fun (t : J → UnitQuaternion) (u : I → UnitQuaternion) (b : I) => val t b (u b)) := by
      refine measurable_pi_lambda _ fun b => ?_
      have h5 : Measurable fun p : (J → UnitQuaternion) × (I → UnitQuaternion) => (p.1, p.2 b) :=
        measurable_fst.prodMk ((measurable_pi_apply b).comp measurable_snd)
      exact (hm b).comp h5
    have hk : ∀ t : J → UnitQuaternion, Measure.map (fun (u : I → UnitQuaternion) (b : I) => val t b (u b))
        (Measure.pi fun _ : I => haarUnit) = Measure.pi fun _ : I => haarUnit := fun t =>
      (measurePreserving_pi (fun _ : I => haarUnit) (fun _ : I => haarUnit) fun b => hv t b).map_eq
    exact (MeasurePreserving.id (Measure.pi fun _ : J => haarUnit)).skew_product
      (g := fun (t : J → UnitQuaternion) (u : I → UnitQuaternion) (b : I) => val t b (u b)) hu
      (Filter.Eventually.of_forall hk)
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : J => haarUnit)).prod h1
  exact h2.comp h3
end Invariance
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n) (A : Finset (TorusSite n))
abbrev FixedBond : Type := {b : TorusBond (n * R.params.side) // ¬ b ∈ s.free}
open Classical in
def glueField (t : FixedBond s → UnitQuaternion) (g : s.free → UnitQuaternion) :
    TorusField (n * R.params.side) :=
  fun x i => if h : (x, i) ∈ s.free then g ⟨(x, i), h⟩ else t ⟨(x, i), h⟩
def treeGauge (t : FixedBond s → UnitQuaternion) (x : TorusSite (n * R.params.side)) : UnitQuaternion :=
  blockGauge R.params.side (s.glueOver A (glueField s t 1)) x
open Classical in
def freeValue (t : FixedBond s → UnitQuaternion) (b : s.free) (u : UnitQuaternion) : UnitQuaternion :=
  (treeGauge s A t b.1.1)⁻¹ *
    (if IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
      then u * s.coarse (parentBlock R.params.side b.1.1) b.1.2 else u) *
    treeGauge s A t (b.1.1 + TorusFields.unitStep (n * R.params.side) b.1.2)
def chartField (t : FixedBond s → UnitQuaternion) (v : s.free → piBall) : TorusField (n * R.params.side) :=
  glueField s t fun b => freeValue s A t b (expCoords (v b))
def chartOffset (v : s.free → piBall) : FreeCoords s.free :=
  fun b => (v b : ImCoords) - toCoords (s.frame b.1)
variable {s A}
theorem not_mem_free_of_isAxialTreeBond (hs : s.IsChartCover A) {z : TorusSite (n * R.params.side)}
    {i : Fin 4}
    (ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z, i)) :
    (z, i) ∉ s.free := fun h => by
  classical
  have := hs.subset_chart h
  unfold chartBonds at this
  exact (Finset.mem_filter.mp this).2 ht
theorem blockGauge_glueOver_glueField (hs : s.IsChartCover A) (hL : Odd R.params.side) (hn : 2 ≤ n)
    (t : FixedBond s → UnitQuaternion) (g : s.free → UnitQuaternion) (x : TorusSite (n * R.params.side)) :
    blockGauge R.params.side (s.glueOver A (glueField s t g)) x = treeGauge s A t x := by
  classical
  apply blockGauge_congr hL hn
  intro z i _ ht
  have hnf := not_mem_free_of_isAxialTreeBond hs ht
  unfold ChartSetting.glueOver glueField
  simp [hnf]
theorem parentBlock_add_unitStep {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (ht : ¬ IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)) :
    parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) =
      parentBlock R.params.side x := by
  have h1 : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x +
      BlockAverages.unitStep (F := stepBlockFrame R.params.side n) 0 i) =
      enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x) := not_not.mp ht
  rw [← torusSiteInFrame_unitStep, ← torusSiteInFrame_add] at h1
  exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
    ((enclosingCell_torusSiteInFrame _).symm.trans (h1.trans (enclosingCell_torusSiteInFrame x)))
theorem exists_gauge_glueOver_chartField (hs : s.IsChartCover A) (hL : Odd R.params.side) (hn : 2 ≤ n)
    (t : FixedBond s → UnitQuaternion) (v : s.free → piBall) :
    ∃ g, IsBlockGauge R.params.side A g ∧
      _root_.YangMills.Construction.TorusFields.gaugeTransform g (s.glueOver A (chartField s A t v)) = s.field (chartOffset s v) := by
  classical
  set Wo := s.glueOver A (chartField s A t v) with hWo
  have htau : ∀ x, blockGauge R.params.side Wo x = treeGauge s A t x :=
    fun x => blockGauge_glueOver_glueField hs hL hn t _ x
  have hoff : ∀ y, parentBlock R.params.side y ∉ A →
      blockGauge R.params.side Wo y = blockGauge R.params.side s.fine y := by
    intro y hy
    apply blockGauge_congr hL hn
    intro z i hb ht
    have hnf := not_mem_free_of_isAxialTreeBond hs ht
    have hT : (z, i) ∉ axialTreeBonds R.params.side A := fun h => by
      have := (Finset.mem_filter.mp h).2.1
      rw [show parentBlock R.params.side (z, i).1 = parentBlock R.params.side y from hb] at this
      exact hy this
    rw [hWo]
    unfold ChartSetting.glueOver
    simp [hnf, hT]
  have hon : ∀ y, parentBlock R.params.side y ∈ A → blockGauge R.params.side s.fine y = 1 := by
    intro y hy
    have h1 : blockGauge R.params.side s.fine y =
        blockGauge R.params.side (trivialField (n * R.params.side)) y := by
      apply blockGauge_congr hL hn
      intro z i hb ht
      have hT : (z, i) ∈ axialTreeBonds R.params.side A := by
        unfold axialTreeBonds
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ht⟩
        show parentBlock R.params.side z ∈ A
        rw [hb]
        exact hy
      exact hs.fine_eq_one _ hT
    rw [h1]
    exact blockGauge_of_forall_eq_one _ (fun _ _ => rfl) _
  refine ⟨fun x => (blockGauge R.params.side s.fine x)⁻¹ * blockGauge R.params.side Wo x,
    ⟨fun x hx => ?_, fun x h0 => ?_⟩, ?_⟩
  · simp [hoff x hx]
  · simp [blockGauge_of_cellOffset_eq_zero _ x h0]
  · funext x i
    unfold TorusFields.gaugeTransform ChartSetting.field
    show ((blockGauge R.params.side s.fine x)⁻¹ * blockGauge R.params.side Wo x) * Wo x i *
      ((blockGauge R.params.side s.fine (x + TorusFields.unitStep (n * R.params.side) i))⁻¹ *
        blockGauge R.params.side Wo (x + TorusFields.unitStep (n * R.params.side) i))⁻¹ = _
    by_cases hf : (x, i) ∈ s.free
    · rw [dif_pos hf]
      have e1 : Wo x i = freeValue s A t ⟨(x, i), hf⟩ (expCoords (v ⟨(x, i), hf⟩)) := by
        rw [hWo]
        unfold ChartSetting.glueOver chartField glueField
        simp [hf]
      have e2 : s.frame (x, i) + toImaginary (chartOffset s v ⟨(x, i), hf⟩) =
          toImaginary (v ⟨(x, i), hf⟩ : ImCoords) := by
        apply Subtype.ext
        unfold chartOffset
        show (s.frame (x, i) : ℍ[ℝ]) + (toImaginary _ : ℍ[ℝ]) = _
        rw [toImaginary_sub, toImaginary_toCoords]
        simp
      rw [e1, e2, htau, htau]
      unfold chartLink freeValue expCoords
      simp only
      show _ = (blockGauge R.params.side s.fine x)⁻¹ * _ *
        blockGauge R.params.side s.fine (x + TorusFields.unitStep (n * R.params.side) i)
      split_ifs <;> group
    · rw [dif_neg hf]
      by_cases hT : (x, i) ∈ axialTreeBonds R.params.side A
      · have hm := Finset.mem_filter.mp hT
        have ht := hm.2.2
        have hA : parentBlock R.params.side x ∈ A := hm.2.1
        have hA' : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ A := by
          rw [parentBlock_add_unitStep ht.1]
          exact hA
        rw [hon x hA, hon _ hA', blockGauge_add_unitStep hL hn Wo x i ht, hs.fine_eq_one _ hT]
        group
      · have hv : Wo x i = s.fine x i := by
          rw [hWo]
          unfold ChartSetting.glueOver
          simp [hf, hT]
        have hno : parentBlock R.params.side x ∉ A ∧
            parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∉ A := by
          by_cases ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
              (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
          · have h1 : parentBlock R.params.side x ∉ A :=
              fun h => hT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, ht⟩)
            refine ⟨h1, ?_⟩
            rw [parentBlock_add_unitStep ht.1]
            exact h1
          · have hb : (x, i) ∈ chartBonds R.params.side n :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
            exact ⟨fun h => hf (hs.mem_of_touching _ hb (Or.inl h)),
              fun h => hf (hs.mem_of_touching _ hb (Or.inr h))⟩
        rw [hv, hoff x hno.1, hoff _ hno.2]
        simp
theorem glueOver_chartField_free (t : FixedBond s → UnitQuaternion) (v : s.free → piBall) (b : s.free) :
    s.glueOver A (chartField s A t v) b.1.1 b.1.2 = freeValue s A t b (expCoords (v b)) := by
  classical
  have h : (b.1.1, b.1.2) ∈ s.free := b.2
  unfold ChartSetting.glueOver chartField glueField
  simp [h]
theorem bondCutoff_glueOver_chartField (hs : s.IsChartCover A) (hL : Odd R.params.side) (hn : 2 ≤ n)
    (t : FixedBond s → UnitQuaternion) (v : s.free → piBall) (b : s.free) :
    s.bondCutoff (s.glueOver A (chartField s A t v)) b.1 =
      cutoffFactor R.ballRadius R.barrierFn (coordNorm (chartOffset s v b)) := by
  classical
  have hv : ‖(toImaginary (v b : ImCoords) : ℍ[ℝ])‖ < Real.pi := by
    rw [norm_toImaginary]
    simpa [piBall] using (v b).2
  have hc : chartCoord R.params s.coarse (s.glueOver A (chartField s A t v)) b.1 =
      toImaginary (v b : ImCoords) := by
    rw [chartCoord_eq_minimalLog R.params s.coarse _ b.1 (expCoords (v b)) ?_]
    · exact minimalLog_expUnit hv
    · have e1 : ∀ x, blockGauge R.params.side (s.glueOver A (chartField s A t v)) x = treeGauge s A t x :=
        fun x => blockGauge_glueOver_glueField hs hL hn t _ x
      rw [glueOver_chartField_free, e1, e1]
      rfl
  unfold ChartSetting.bondCutoff coordNorm chartOffset
  rw [hc, toImaginary_sub, toImaginary_toCoords]
theorem measurePreserving_freeValue (t : FixedBond s → UnitQuaternion) (b : s.free) :
    MeasurePreserving (freeValue s A t b) haarUnit haarUnit := by
  classical
  by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
  · have : freeValue s A t b = fun u => (treeGauge s A t b.1.1)⁻¹ * u *
        (s.coarse (parentBlock R.params.side b.1.1) b.1.2 *
          treeGauge s A t (b.1.1 + TorusFields.unitStep (n * R.params.side) b.1.2)) := by
      funext u
      unfold freeValue
      rw [if_pos hc]
      group
    rw [this]
    exact measurePreserving_mul_mul _ _
  · have : freeValue s A t b = fun u => (treeGauge s A t b.1.1)⁻¹ * u *
        treeGauge s A t (b.1.1 + TorusFields.unitStep (n * R.params.side) b.1.2) := by
      funext u
      unfold freeValue
      rw [if_neg hc]
    rw [this]
    exact measurePreserving_mul_mul _ _
theorem measurable_glueOver_glueField :
    Measurable fun t : FixedBond s → UnitQuaternion => s.glueOver A (glueField s t 1) := by
  classical
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
  unfold ChartSetting.glueOver glueField
  by_cases h1 : (x, i) ∈ s.free
  · simp [h1]
  · by_cases h2 : (x, i) ∈ axialTreeBonds R.params.side A
    · simp only [h1, h2, or_true, if_true, dif_neg, not_false_eq_true]
      exact measurable_pi_apply _
    · simp [h1, h2]
theorem measurable_treeGauge (x : TorusSite (n * R.params.side)) :
    Measurable fun t : FixedBond s → UnitQuaternion => treeGauge s A t x :=
  (measurable_blockGauge x).comp measurable_glueOver_glueField
theorem measurable_freeValue (b : s.free) :
    Measurable fun p : (FixedBond s → UnitQuaternion) × UnitQuaternion => freeValue s A p.1 b p.2 := by
  classical
  have h1 : Measurable fun p : (FixedBond s → UnitQuaternion) × UnitQuaternion => treeGauge s A p.1 b.1.1 :=
    (measurable_treeGauge _).comp measurable_fst
  have h2 : Measurable fun p : (FixedBond s → UnitQuaternion) × UnitQuaternion =>
      treeGauge s A p.1 (b.1.1 + TorusFields.unitStep (n * R.params.side) b.1.2) :=
    (measurable_treeGauge _).comp measurable_fst
  unfold freeValue
  by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
  · simp only [if_pos hc]
    exact (h1.inv.mul (measurable_snd.mul_const _)).mul h2
  · simp only [if_neg hc]
    exact (h1.inv.mul measurable_snd).mul h2
theorem measurePreserving_glueField :
    MeasurePreserving (fun p : (FixedBond s → UnitQuaternion) × (s.free → UnitQuaternion) => glueField s p.1 p.2)
      ((Measure.pi fun _ : FixedBond s => haarUnit).prod (Measure.pi fun _ : s.free => haarUnit))
      (fieldHaar (n * R.params.side)) := by
  classical
  have h1 := measurePreserving_piEquivPiSubtypeProd
    (fun _ : TorusBond (n * R.params.side) => haarUnit) (· ∈ s.free)
  have h2 := h1.symm (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : TorusBond (n * R.params.side) => UnitQuaternion) (· ∈ s.free))
  have h3 : MeasurePreserving (MeasurableEquiv.curry (TorusSite (n * R.params.side)) (Fin 4) UnitQuaternion)
      (bondHaar (n * R.params.side)) (fieldHaar (n * R.params.side)) :=
    (measurePreserving_curry_symm (m := n * R.params.side)).symm
      (MeasurableEquiv.curry (TorusSite (n * R.params.side)) (Fin 4) UnitQuaternion).symm
  have h2' : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : TorusBond (n * R.params.side) => UnitQuaternion) (· ∈ s.free)).symm
      ((Measure.pi fun _ : s.free => haarUnit).prod (Measure.pi fun _ : FixedBond s => haarUnit))
      (Measure.pi fun _ : TorusBond (n * R.params.side) => haarUnit) := by
    convert h2 using 3
  have h4 := h3.comp (h2'.comp (Measure.measurePreserving_swap
    (μ := Measure.pi fun _ : FixedBond s => haarUnit) (ν := Measure.pi fun _ : s.free => haarUnit)))
  convert h4 using 1
  funext p x i
  unfold glueField
  rfl
theorem measurePreserving_chartField (hH : HaarIntegralInLogCoords) :
    MeasurePreserving (fun p : (FixedBond s → UnitQuaternion) × (s.free → piBall) => chartField s A p.1 p.2)
      ((Measure.pi fun _ : FixedBond s => haarUnit).prod (Measure.pi fun _ : s.free => haarOnBall))
      (fieldHaar (n * R.params.side)) := by
  have := isFiniteMeasure_haarOnBall hH
  have he : MeasurePreserving (fun v : piBall => expCoords v) haarOnBall haarUnit :=
    (MeasurePreserving.mk continuous_expCoords.measurable (map_expCoords_haarOnCoords hH)).comp
      measurePreserving_coe_piBall
  have h := measurePreserving_skew_exp haarOnBall (fun v : piBall => expCoords v) he (freeValue s A)
    (measurable_freeValue (A := A)) (measurePreserving_freeValue (A := A))
  exact (measurePreserving_glueField (s := s)).comp h
theorem chartField_injective :
    Function.Injective fun p : (FixedBond s → UnitQuaternion) × (s.free → piBall) => chartField s A p.1 p.2 := by
  classical
  rintro ⟨t, v⟩ ⟨t', v'⟩ h
  simp only at h
  have ht : t = t' := by
    funext b
    have := congrFun (congrFun h b.1.1) b.1.2
    have hb : (b.1.1, b.1.2) ∉ s.free := b.2
    unfold chartField glueField at this
    simpa [hb] using this
  subst ht
  have hv : v = v' := by
    funext b
    have := congrFun (congrFun h b.1.1) b.1.2
    have hb : (b.1.1, b.1.2) ∈ s.free := b.2
    unfold chartField glueField at this
    simp only [hb, dif_pos] at this
    have e : expCoords (v b) = expCoords (v' b) := by
      unfold freeValue at this
      by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
      · simpa [hc] using this
      · simpa [hc] using this
    have n1 : ‖(toImaginary (v b : ImCoords) : ℍ[ℝ])‖ < Real.pi := by
      rw [norm_toImaginary]
      simpa [piBall] using (v b).2
    have n2 : ‖(toImaginary (v' b : ImCoords) : ℍ[ℝ])‖ < Real.pi := by
      rw [norm_toImaginary]
      simpa [piBall] using (v' b).2
    exact Subtype.ext (toImaginary_injective (eq_of_expUnit_eq e n1 (norm_le_of_expUnit_eq e.symm n2)))
  rw [hv]
theorem measurable_cutoffFactor_coordNorm (ρ : ℝ) (p : ℝ → ℝ) (hc : IsCutoff ρ p) :
    Measurable fun v : ImCoords => cutoffFactor ρ p (coordNorm v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurable_cutoffFactor_coordNorm <;> assumption
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
omit [NeZero n] in
theorem measurable_chartSetting_field (s : ChartSetting R n) :
    Measurable fun η : FreeCoords s.free => s.field η := by
  classical
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
  unfold ChartSetting.field
  by_cases hf : (x, i) ∈ s.free
  · simp only [dif_pos hf]
    have h1 : Continuous fun v : ImCoords => expUnit (s.frame (x, i) + toImaginary v) := by
      have e : (fun v : ImCoords => expUnit (s.frame (x, i) + toImaginary v)) =
          fun v : ImCoords => expCoords (toCoords (s.frame (x, i)) + v) := by
        funext v
        unfold expCoords
        congr 1
        apply Subtype.ext
        have : toImaginary (toCoords (s.frame (x, i)) + v) =
            toImaginary (toCoords (s.frame (x, i)) + v - v) + toImaginary v := by
          apply Subtype.ext
          have := toImaginary_sub (toCoords (s.frame (x, i)) + v) v
          show (toImaginary _ : ℍ[ℝ]) = (toImaginary _ : ℍ[ℝ]) + (toImaginary _ : ℍ[ℝ])
          rw [this]
          simp
        rw [this]
        simp [toImaginary_toCoords]
      rw [e]
      exact continuous_expCoords.comp (continuous_const.add continuous_id)
    have h2 : Measurable fun η : FreeCoords s.free =>
        expUnit (s.frame (x, i) + toImaginary (η ⟨(x, i), hf⟩)) :=
      h1.measurable.comp (measurable_pi_apply _)
    unfold chartLink
    by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
    · simp only [if_pos hc]
      exact (h2.mul_const _).const_mul _ |>.mul_const _
    · simp only [if_neg hc]
      exact (h2.const_mul _).mul_const _
  · simp only [dif_neg hf]
    exact measurable_const
end Chart
end FreeChart
open FreeChart BlockTrees in
theorem FreeChart.haarInChartCoordinates_proof (hH : HaarIntegralInLogCoords) :
    HaarInChartCoordinates := by
  classical
  intro R hodd hcut n _ hn s A hs H hHm hHg
  have hfin := isFiniteMeasure_haarOnBall hH
  have hlog := isFiniteMeasure_haarOnCoords hH
  have hp := measurePreserving_chartField (s := s) (A := A) hH
  have hP1 : PolishSpace UnitQuaternion := TorusFields.isCompact_unitary_quaternion.isClosed.polishSpace
  have hP2 : PolishSpace piBall := Metric.isOpen_ball.polishSpace
  have hemb : MeasurableEmbedding
      fun p : (FixedBond s → UnitQuaternion) × (s.free → piBall) => chartField s A p.1 p.2 :=
    hp.measurable.measurableEmbedding chartField_injective
  set fr : FreeCoords s.free := fun b => toCoords (s.frame b.1) with hfr
  set G : FreeCoords s.free → ENNReal := fun w =>
    H (s.field (w - fr)) * ENNReal.ofReal (s.cutoffProduct (w - fr)) with hG
  have hcuts : Measurable fun η : FreeCoords s.free => s.cutoffProduct η := by
    unfold ChartSetting.cutoffProduct
    exact Finset.measurable_prod _ fun b _ =>
      (measurable_cutoffFactor_coordNorm _ _ hcut).comp (measurable_pi_apply b)
  have hGm : Measurable G := by
    have hsub : Measurable fun w : FreeCoords s.free => w - fr := measurable_id.sub_const _
    exact (hHm.comp ((measurable_chartSetting_field s).comp hsub)).mul
      (ENNReal.measurable_ofReal.comp (hcuts.comp hsub))
  have hval : ∀ p : (FixedBond s → UnitQuaternion) × (s.free → piBall),
      H (s.glueOver A (chartField s A p.1 p.2)) *
        ∏ b : s.free, ENNReal.ofReal (s.bondCutoff (s.glueOver A (chartField s A p.1 p.2)) b) =
      G (fun b => (p.2 b : ImCoords)) := by
    rintro ⟨t, v⟩
    obtain ⟨g, hg, hgf⟩ := exists_gauge_glueOver_chartField hs hodd hn t v
    have h1 : H (s.glueOver A (chartField s A t v)) = H (s.field (chartOffset s v)) := by
      rw [← hgf]
      exact (hHg g hg _).symm
    have h2 : ∏ b : s.free, ENNReal.ofReal (s.bondCutoff (s.glueOver A (chartField s A t v)) b) =
        ENNReal.ofReal (s.cutoffProduct (chartOffset s v)) := by
      unfold ChartSetting.cutoffProduct
      rw [ENNReal.ofReal_prod_of_nonneg fun b _ => cutoffFactor_nonneg _ _ _]
      exact Finset.prod_congr rfl fun b _ => by rw [bondCutoff_glueOver_chartField hs hodd hn t v b]
    simp only [h1, h2]
    rfl
  have step1 := hp.lintegral_comp_emb hemb
    (fun W => H (s.glueOver A W) * ∏ b : s.free, ENNReal.ofReal (s.bondCutoff (s.glueOver A W) b))
  rw [← step1]
  simp only [hval]
  have hpi : Measurable fun v : s.free → piBall => G fun b => (v b : ImCoords) :=
    hGm.comp (measurable_pi_lambda _ fun b => measurable_subtype_coe.comp (measurable_pi_apply b))
  have hprod := lintegral_prod (μ := Measure.pi fun _ : FixedBond s => haarUnit)
    (ν := Measure.pi fun _ : s.free => haarOnBall)
    (fun a : (FixedBond s → UnitQuaternion) × (s.free → piBall) => G fun b => (a.2 b : ImCoords))
    (hpi.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]
  have hco : MeasurePreserving (fun (v : s.free → piBall) b => (v b : ImCoords))
      (Measure.pi fun _ : s.free => haarOnBall) (Measure.pi fun _ : s.free => haarOnCoords) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_coe_piBall
  rw [hco.lintegral_comp hGm, pi_haarOnCoords hH]
  have hD : Measurable fun v : s.free → ImCoords => ∏ b, ENNReal.ofReal (haarLogDensity (v b)) :=
    Finset.measurable_prod _ fun b _ =>
      (ENNReal.measurable_ofReal.comp measurable_haarLogDensity).comp (measurable_pi_apply b)
  rw [lintegral_withDensity_eq_lintegral_mul _ hD hGm]
  have hshift := lintegral_add_right_eq_self (μ := (volume : Measure (FreeCoords s.free)))
    (fun w => ((fun v : s.free → ImCoords => ∏ b, ENNReal.ofReal (haarLogDensity (v b))) * G) w) fr
  rw [← hshift]
  apply lintegral_congr
  intro η
  have hsub : η + fr - fr = η := by simp
  simp only [Pi.mul_apply, hG, hsub]
  have hcn : 0 ≤ s.cutoffProduct η := Finset.prod_nonneg fun b _ => cutoffFactor_nonneg _ _ _
  rw [ENNReal.ofReal_mul hcn]
  have hj : ∏ b, ENNReal.ofReal (haarLogDensity ((η + fr) b)) = ENNReal.ofReal (s.haarJacobian η) := by
    unfold ChartSetting.haarJacobian
    rw [ENNReal.ofReal_prod_of_nonneg fun b _ => haarLogDensity_nonneg _]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Pi.add_apply, add_comm]
  rw [hj]
  ring
end YangMills.Construction.ClusterExpansionOfAStep
end
