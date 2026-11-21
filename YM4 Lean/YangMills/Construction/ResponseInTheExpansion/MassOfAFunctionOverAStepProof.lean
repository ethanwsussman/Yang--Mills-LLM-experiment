import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOne
import YangMills.Construction.ResponseInTheExpansion.MassOfAFunctionOverAStep
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings WeightedResponses StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem baseLaw_nonneg' (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) : 0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem sum_markProduct_eq_one (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ s ∈ (markedBonds R C).powerset, ENNReal.ofReal (markProduct R C V W s) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.sum_markProduct_eq_one <;> assumption
private theorem averagedKernel_eq_sum (W : TorusField (n * R.params.side)) (V : TorusField n) :
    averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) =
      ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.averagedKernel_eq_sum <;> assumption
private theorem baseLaw_mul_kernels_eq (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c =
      stepTransitionDensity R.params R.coupling W b V := by
  classical
  unfold baseLaw stepTransitionDensity
  split_ifs <;> simp
section Main
variable (hk : BondKernelProperties)
include hk
private theorem bondKernel_prod_nonneg (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n) :
    0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
  Finset.prod_nonneg fun c _ => (hk.2 R.params R.coupling n _ _ b c).1.le
private theorem lintegral_configurationWeight_mul (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (s : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (H : (Yt → R.labels.Ω) → ℝ) :
    ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H ωt) ∂(Measure.pi fun _ => R.labels.μ) =
      (open Classical in if IsHullState R.params R.range W Yt then
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ) else 0) *
        ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
        ENNReal.ofReal (markProduct R C V W s) := by
  classical
  by_cases hh : IsHullState R.params R.range W Yt
  · simp only [configurationWeight, if_pos hh]
    have hnn : ∀ ωt, 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt := fun ωt => hR.hasExpansions.2.nonneg _ hside W Yt ωt hh
    have hκ := mul_nonneg (baseLaw_nonneg' (R := R) W b) (bondKernel_prod_nonneg hk W V b)
    have he : ∀ ωt, ENNReal.ofReal (stepWeight R C V W Yt ωt s b) * ENNReal.ofReal (H ωt) =
        ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H ωt) *
          (ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
          ENNReal.ofReal (markProduct R C V W s)) := by
      intro ωt
      have e : stepWeight R C V W Yt ωt s b = R.labelWeight (n * R.params.side) W Yt ωt *
          ((baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
          markProduct R C V W s) := by
        unfold stepWeight
        ring
      rw [e, ENNReal.ofReal_mul (hnn ωt), ENNReal.ofReal_mul (hnn ωt), ENNReal.ofReal_mul hκ]
      ring
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), mul_assoc]
  · simp only [configurationWeight, if_neg hh, zero_mul, lintegral_zero]
private theorem sum_configurations_at_field (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (H' : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ) :
    ∑ s ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H' Yt W ωt) ∂(Measure.pi fun _ => R.labels.μ) =
      (open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H' Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ)) *
        ENNReal.ofReal (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) := by
  classical
  simp_rw [fun s Yt b => lintegral_configurationWeight_mul hk hR C V W hside s Yt b (H' Yt W)]
  have hrow : ∑ Yt : Finset (TorusSite (n * R.params.side)), (if IsHullState R.params R.range W Yt then
      ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H' Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ) else 0) =
      ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H' Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ) := by
    rw [Finset.sum_filter]
    rfl
  have hbase : ∑ b : BaseChoice R.params.side n, ENNReal.ofReal (baseLaw (R := R) W b *
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) =
      ENNReal.ofReal (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) := by
    rw [averagedKernel_eq_sum, ENNReal.ofReal_sum_of_nonneg]
    exact fun b _ => mul_nonneg (baseLaw_nonneg' (R := R) W b) (bondKernel_prod_nonneg hk W V b)
  have hall : ∀ s, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      (if IsHullState R.params R.range W Yt then
        ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H' Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ) else 0) *
      ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
      ENNReal.ofReal (markProduct R C V W s) =
      (∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H' Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ)) *
        ENNReal.ofReal (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) *
        ENNReal.ofReal (markProduct R C V W s) := by
    intro s
    rw [← hrow, ← hbase, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_mul]
  simp_rw [hall]
  rw [← Finset.mul_sum, sum_markProduct_eq_one hR, mul_one]
end Main
private def hullStateIntegral (R : StepSetup) (n : ℕ) [NeZero n]
    (H : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ) (W : TorusField (n * R.params.side)) : ENNReal :=
  open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
    ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H Yt W ωt) ∂(Measure.pi fun _ : Yt => R.labels.μ)
private theorem hullStateIntegral_measurable (hR : R.IsWellPosed) (hsideL : IsBlockTorusSide R.params (n * R.params.side))
    (H : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ)
    (hHm : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H Yt p.1 p.2) :
    Measurable (hullStateIntegral R n H) := by
  classical
  have e : hullStateIntegral R n H = fun W => ∑ Yt : Finset (TorusSite (n * R.params.side)), ∫⁻ ωt,
      ENNReal.ofReal ((if IsHullState R.params (clusterRange R.coupling) W Yt then R.labelWeight (n * R.params.side) W Yt ωt else 0) * H Yt W ωt)
        ∂(Measure.pi fun _ : Yt => R.labels.μ) := by
    funext W
    unfold hullStateIntegral
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    by_cases h : IsHullState R.params (clusterRange R.coupling) W Yt
    · simp only [if_pos h]
    · simp [if_neg h]
  rw [e]
  refine Finset.measurable_sum _ fun Yt _ => ?_
  have h1 := (hR.hasExpansions.2.borel (n * R.params.side) hsideL Yt).1
  have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ENNReal.ofReal ((if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) * H Yt p.1 p.2) :=
    (h1.mul (hHm Yt)).ennreal_ofReal
  exact h2.lintegral_prod_right'
private theorem coarse_sum_eq_lintegral (hc : ConfigurationMassWithFunction) (hk : BondKernelProperties)
    (hw : ConfigurationWeightMeasurable) (hH : CoarseHullIsHullState) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params n) (hn : R.params.n₀ ≤ n) (hsideL : IsBlockTorusSide R.params (n * R.params.side))
    (H : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ)
    (hHm : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H Yt p.1 p.2)
    (V : TorusField n) (C : Finset (TorusSite n)) (hCV : C = hotCoreSites R V) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, coarseMassWith R C V (fun Yt W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ∫⁻ W, hullStateIntegral R n H W * ENNReal.ofReal
        (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hg : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ENNReal.ofReal (H Yt p.1 p.2) := fun Yt => (hHm Yt).ennreal_ofReal
  have hcm : ∀ (s : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (Y : Finset (TorusSite n)), Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      configurationMassWith R C V s Yt b (fun W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩ := by
    intro s Yt b Y
    by_cases h : Y = coarseHull R.params.side R.range R.nextRange s Yt C
    · subst h
      exact (hc R hR n hn C V s Yt b _ (hg Yt)).2.2.1
    · have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
          configurationMassWith R C V s Yt b (fun W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩) = fun _ => 0 :=
        funext fun ω => (hc R hR n hn C V s Yt b _ (hg Yt)).1 ⟨Y, ω⟩ h
      rw [this]
      exact measurable_const
  have hint : ∀ Y : Finset (TorusSite n), ∫⁻ ω, coarseMassWith R C V (fun Yt W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ s ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMassWith R C V s Yt b (fun W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Y
    unfold coarseMassWith
    rw [lintegral_finsetSum _ fun s _ => Finset.measurable_sum _ fun Yt _ => Finset.measurable_sum _ fun b _ =>
      hcm s Yt b Y]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [lintegral_finsetSum _ fun Yt _ => Finset.measurable_sum _ fun b _ => hcm s Yt b Y]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [lintegral_finsetSum _ fun b _ => hcm s Yt b Y]
  have hcase : ∀ (s : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, configurationMassWith R C V s Yt b (fun W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro s Yt b
    have hmem : coarseHull R.params.side R.range R.nextRange s Yt C ∈ Finset.univ.filter (IsHullState R.params R.nextRange V) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hCV]
      exact hH R.params hR.admissible R.range R.nextRange hR.range_le hR.nextRange_ge n hside.1 V s Yt
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · exact (hc R hR n hn C V s Yt b _ (hg Yt)).2.2.2
    · intro Y _ hY
      rw [lintegral_congr fun ω => (hc R hR n hn C V s Yt b _ (hg Yt)).1 ⟨Y, ω⟩ hY]
      simp
  have hwm : ∀ (s : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun W : TorusField (n * R.params.side) =>
      ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
        ∂(Measure.pi fun _ => R.labels.μ) := by
    intro s Yt b
    have h1 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        configurationWeight R C V s Yt b p.1 p.2 * ENNReal.ofReal (H Yt p.1 p.2) :=
      (hw R hR n hn C V s Yt b).mul (hg Yt)
    exact h1.lintegral_prod_right'
  have hmid : ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, coarseMassWith R C V (fun Yt W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ s ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    simp_rw [hint]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => hcase s Yt b
  rw [hmid]
  have h3 : ∀ (s : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))),
      ∑ b : BaseChoice R.params.side n, ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∑ b : BaseChoice R.params.side n, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) :=
    fun s Yt => (lintegral_finsetSum _ fun b _ => hwm s Yt b).symm
  simp_rw [h3]
  have h2 : ∀ s : Finset (TorusBond (n * R.params.side)), ∑ Yt : Finset (TorusSite (n * R.params.side)), ∫⁻ W, ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V s Yt b W ωt * ENNReal.ofReal (H Yt W ωt)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) :=
    fun s => (lintegral_finsetSum _ fun Yt _ => Finset.measurable_sum _ fun b _ => hwm s Yt b).symm
  simp_rw [h2]
  rw [← lintegral_finsetSum _ fun s _ =>
    Finset.measurable_sum _ fun Yt _ => Finset.measurable_sum _ fun b _ => hwm s Yt b]
  refine lintegral_congr fun W => ?_
  exact sum_configurations_at_field hk hR C V W hsideL H
private theorem lintegral_swap_of_mass_one {A B : Type} [MeasurableSpace A] [MeasurableSpace B] {μ : Measure A} {ν : Measure B}
    [SFinite μ] [SFinite ν] {K : A → ENNReal} {m : A × B → ENNReal} (hK : Measurable K) (hm : Measurable m)
    (h1 : ∀ a, ∫⁻ b, m (a, b) ∂ν = 1) : ∫⁻ b, ∫⁻ a, K a * m (a, b) ∂μ ∂ν = ∫⁻ a, K a ∂μ := by
  have hprod : Measurable (Function.uncurry fun (b : B) (a : A) => K a * m (a, b)) :=
    (hK.comp measurable_snd).mul (hm.comp measurable_swap)
  rw [lintegral_lintegral_swap hprod.aemeasurable]
  refine lintegral_congr fun a => ?_
  have hma : Measurable fun b => m (a, b) := hm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ hma, h1 a, mul_one]
theorem massOverStepStatement_holds (hc : ConfigurationMassWithFunction) (hk : BondKernelProperties)
    (hm : AveragedKernelIntegralOne) (hd : StepTransitionDensityBounds) (hw : ConfigurationWeightMeasurable)
    (hH : CoarseHullIsHullState) : massOverStepStatement := by
  classical
  intro R hR n _ hside H hHm hH0
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hside.2
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side R.params.n₀]; exact Nat.mul_le_mul_right _ hn⟩
  have hKm := hullStateIntegral_measurable hR hsideL H hHm
  have hmk : Measurable fun p : TorusField (n * R.params.side) × TorusField n => ENNReal.ofReal
      (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 p.1) (readAtLevel (stepBlockFrame R.params.side n) 1 p.2)) := by
    have e : (fun p : TorusField (n * R.params.side) × TorusField n =>
        averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 p.1) (readAtLevel (stepBlockFrame R.params.side n) 1 p.2)) =
        fun p => ∑ b : BaseChoice R.params.side n, stepTransitionDensity R.params R.coupling p.1 b p.2 := by
      funext p
      rw [averagedKernel_eq_sum (R := R)]
      exact Finset.sum_congr rfl fun b _ => baseLaw_mul_kernels_eq (R := R) p.1 p.2 b
    refine Measurable.ennreal_ofReal ?_
    rw [e]
    exact Finset.measurable_sum _ fun b _ => (hd R.params R.coupling n).1 b
  have hmass : ∀ W : TorusField (n * R.params.side), ∫⁻ V, ENNReal.ofReal
      (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) ∂(fieldHaar n) = 1 := by
    intro W
    have h1 := hm R.params hR.admissible hR.admissible.depth_lt R.coupling n (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    have hI : Integrable (fun V : TorusField n =>
        averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) (fieldHaar n) := by
      by_contra hnot
      rw [integral_undef hnot] at h1
      exact zero_ne_one h1
    have hnn : ∀ V : TorusField n, 0 ≤ averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V) := by
      intro V
      rw [averagedKernel_eq_sum (R := R)]
      exact Finset.sum_nonneg fun b _ => mul_nonneg (baseLaw_nonneg' (R := R) W b) (bondKernel_prod_nonneg hk W V b)
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hnn), h1, ENNReal.ofReal_one]
  have hV : ∀ V : TorusField n, ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, coarseMassWith R (hotCoreSites R V) V (fun Yt W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) = _ :=
    fun V => coarse_sum_eq_lintegral hc hk hw hH hR hside hn hsideL H hHm V (hotCoreSites R V) rfl
  exact ((lintegral_congr hV).trans (lintegral_swap_of_mass_one hKm hmk hmass)).symm
end YangMills.Construction.ResponseInTheExpansion
end
