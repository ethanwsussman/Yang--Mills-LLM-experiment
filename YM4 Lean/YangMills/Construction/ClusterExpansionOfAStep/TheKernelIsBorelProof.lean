import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.KernelMeasurability
open BlockAverages LumpContours TorusFields TorusLumps TorusContours
section General
variable {α β γ : Type*} [MeasurableSpace α]
theorem measurableSet_fibre_comp [Countable β] (f : α → β) (hf : ∀ b, MeasurableSet {a | f a = b})
    (g : β → γ) (c : γ) : MeasurableSet {a | g (f a) = c} := by
  have : {a | g (f a) = c} = ⋃ b ∈ {b | g b = c}, {a | f a = b} := by
    ext a
    simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun b _ => hf b
theorem measurable_of_measurableSet_fibres [Countable β] (f : α → β)
    (hf : ∀ b, MeasurableSet {a | f a = b})
    (G : β → α → ℝ) (hG : ∀ b, Measurable (G b)) : Measurable fun a => G (f a) a := by
  intro s hs
  have : (fun a => G (f a) a) ⁻¹' s = ⋃ b, {a | f a = b} ∩ (G b) ⁻¹' s := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨f a, rfl, h⟩
    · rintro ⟨b, rfl, h⟩
      exact h
  rw [this]
  exact MeasurableSet.iUnion fun b => (hf b).inter (hG b hs)
end General
section Continuity
variable {F : BlockFrame} {α : Type*} [TopologicalSpace α]
theorem continuous_pathHolonomy {j : ℕ} (X : α → F.GaugeField j)
    (hX : ∀ x i, Continuous fun a => X a x i) (x : F.Site j)
    (l : List PathStep) : Continuous fun a => pathHolonomy (X a) x l := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st r ih =>
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      exact (hX _ _).inv
    · simp only [linkValue, if_true]
      exact hX _ _
theorem continuous_plaquetteDefect {j : ℕ} (X : α → F.GaugeField j)
    (hX : ∀ x i, Continuous fun a => X a x i)
    (p : F.Site j × Fin 4 × Fin 4) : Continuous fun a => plaquetteDefect (X a) p := by
  unfold plaquetteDefect plaquetteHolonomy
  exact ((continuous_subtype_val.comp (continuous_pathHolonomy X hX _ _)).sub continuous_const).norm
theorem continuous_contourMean (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) (X : α → F.GaugeField F.depth) (hX : ∀ x i, Continuous fun a => X a x i) :
    Continuous fun a => contourMean J₀ h b (X a) c := by
  unfold contourMean
  exact (continuous_finset_sum _ fun e _ =>
    continuous_subtype_val.comp (continuous_pathHolonomy X hX _ _)).const_smul
      (1 / ((usedContours J₀ h b c).card : ℝ))
end Continuity
instance instSecondCountableTopologyUnitQuaternion : SecondCountableTopology UnitQuaternion :=
  EMetric.secondCountable_of_sigmaCompact UnitQuaternion
theorem continuous_partitionFn : Continuous partitionFn := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.continuous_partitionFn <;> assumption
theorem measurable_meanKernel_comp {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α]
    (s : ℝ) (Q : α → ℍ[ℝ]) (G : α → UnitQuaternion) (hQ : Continuous Q) (hG : Continuous G) :
    Measurable fun a => TorusContours.meanKernel s (Q a) (G a) := by
  unfold TorusContours.meanKernel
  refine Measurable.div ?_ ?_
  · refine Continuous.measurable ?_
    exact Real.continuous_exp.comp (continuous_const.mul (Quaternion.continuous_re.comp
      (hQ.mul (continuous_subtype_val.comp hG.inv))))
  · refine Continuous.measurable ?_
    exact continuous_partitionFn.comp (continuous_const.mul hQ.norm)
section Step
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem continuous_fineLevelField_apply (x : (stepBlockFrame ℓ.side n).Site 0) (i : Fin 4) :
    Continuous fun W : TorusField (n * ℓ.side) => fineLevelField ℓ n W x i :=
  (continuous_apply i).comp (continuous_apply _)
open Classical in
def hotPlaquettes (ℓ : StepParameters) (n : ℕ) [NeZero n] (W : TorusField (n * ℓ.side)) :
    Finset ((stepBlockFrame ℓ.side n).Site 0 × Fin 4 × Fin 4) :=
  (cutPlaquettes (levelSites (stepBlockFrame ℓ.side n) 0)).filter fun p =>
    ℓ.threshold ≤ plaquetteDefect (fineLevelField ℓ n W) p
theorem measurableSet_hotPlaquettes (A : Finset ((stepBlockFrame ℓ.side n).Site 0 × Fin 4 × Fin 4)) :
    MeasurableSet {W : TorusField (n * ℓ.side) | hotPlaquettes ℓ n W = A} := by
  classical
  have : {W : TorusField (n * ℓ.side) | hotPlaquettes ℓ n W = A} =
      ⋂ p : (stepBlockFrame ℓ.side n).Site 0 × Fin 4 × Fin 4, {W : TorusField (n * ℓ.side) |
        (p ∈ cutPlaquettes (levelSites (stepBlockFrame ℓ.side n) 0) ∧
          ℓ.threshold ≤ plaquetteDefect (fineLevelField ℓ n W) p) ↔ p ∈ A} := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, hotPlaquettes, Finset.mem_filter]
  rw [this]
  refine MeasurableSet.iInter fun p => ?_
  have hc := continuous_plaquetteDefect (F := stepBlockFrame ℓ.side n)
    (fun W : TorusField (n * ℓ.side) => fineLevelField ℓ n W)
    (fun x i => continuous_fineLevelField_apply x i) p
  by_cases hs : p ∈ cutPlaquettes (levelSites (stepBlockFrame ℓ.side n) 0)
  · by_cases hp : p ∈ A
    · simp only [hp, iff_true, hs, true_and]
      exact (isClosed_le continuous_const hc).measurableSet
    · simp only [hp, iff_false, not_le, hs, true_and]
      exact (isOpen_lt hc continuous_const).measurableSet
  · by_cases hp : p ∈ A
    · simp [hp, hs]
    · simp [hp, hs]
theorem measurableSet_fineHotLumps_eq (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))) :
    MeasurableSet {W : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n W) = H} := by
  classical
  exact measurableSet_fibre_comp (hotPlaquettes ℓ n) measurableSet_hotPlaquettes
    (fun A => A.biUnion fun p => (plaquetteCorners p).image (lumpOf ℓ.grid)) H
theorem measurableSet_baseChoices_eq
    (A : Finset ((stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)) :
    MeasurableSet {W : TorusField (n * ℓ.side) | baseChoices ℓ (fineLevelField ℓ n W) = A} :=
  measurableSet_fibre_comp (fun W : TorusField (n * ℓ.side) => fineHotLumps ℓ (fineLevelField ℓ n W))
    measurableSet_fineHotLumps_eq (baseChoicesOf ℓ n) A
theorem measurableSet_fineHotLumps_fst_eq (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))) :
    MeasurableSet {p : TorusField (n * ℓ.side) × TorusField n |
      fineHotLumps ℓ (fineLevelField ℓ n p.1) = H} :=
  measurable_fst (measurableSet_fineHotLumps_eq H)
def kernelAtLumps (ℓ : StepParameters) (x : ℝ) (n : ℕ)
    (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4)
    (p : TorusField (n * ℓ.side) × TorusField n) : ℝ :=
  TorusContours.meanKernel (ℓ.coupling * x) (contourMean ℓ.baseDepth H b (fineLevelField ℓ n p.1) c)
    (coarseLevelField ℓ n p.2 c.1 c.2)
theorem measurable_kernelAtLumps (x : ℝ) (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    Measurable (kernelAtLumps ℓ x n H b c) := by
  refine measurable_meanKernel_comp _ _ _ ?_ ?_
  · exact continuous_contourMean (F := stepBlockFrame ℓ.side n) ℓ.baseDepth H b c
      (fun p : TorusField (n * ℓ.side) × TorusField n => fineLevelField ℓ n p.1)
      (fun x i => (continuous_fineLevelField_apply x i).comp continuous_fst)
  · exact (continuous_apply c.2).comp ((continuous_apply _).comp continuous_snd)
theorem measurable_bondKernel (x : ℝ)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      bondKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2) b c :=
  measurable_of_measurableSet_fibres
    (fun p : TorusField (n * ℓ.side) × TorusField n => fineHotLumps ℓ (fineLevelField ℓ n p.1))
    measurableSet_fineHotLumps_fst_eq (fun H => kernelAtLumps ℓ x n H b c)
    (fun H => measurable_kernelAtLumps x H b c)
theorem measurable_averagedKernel (x : ℝ) :
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
      averagedKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2) :=
  measurable_of_measurableSet_fibres
    (fun p : TorusField (n * ℓ.side) × TorusField n => fineHotLumps ℓ (fineLevelField ℓ n p.1))
    measurableSet_fineHotLumps_fst_eq
    (fun H p => (1 / ((baseChoicesOf ℓ n H).card : ℝ)) * ∑ b ∈ baseChoicesOf ℓ n H,
      ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, kernelAtLumps ℓ x n H b c p)
    (fun H => (Finset.measurable_sum _ fun b _ =>
      Finset.measurable_prod _ fun c _ => measurable_kernelAtLumps x H b c).const_mul _)
end Step
theorem analyticAt_meanKernel_expUnit_mul (s : ℝ) (q : ℍ[ℝ]) (Vc : UnitQuaternion) {k : ℕ}
    (v : (Fin k → ℝ) → imaginaryQuaternions)
    (hv : AnalyticAt ℝ (fun σ => ((v σ : imaginaryQuaternions) : ℍ[ℝ])) 0) :
    AnalyticAt ℝ (fun σ => TorusContours.meanKernel s q (expUnit (v σ) * Vc)) 0 := by
  let T : ℍ[ℝ] →L[ℝ] ℝ := (innerSL ℝ (1 : ℍ[ℝ])).comp
    (ContinuousLinearMap.mul ℝ ℍ[ℝ] (q * ((Vc⁻¹ : UnitQuaternion) : ℍ[ℝ])))
  have hT : ∀ w, T w = (q * (((Vc⁻¹ : UnitQuaternion) : ℍ[ℝ]) * w)).re := by
    intro w
    simp [T, Quaternion.inner_def, mul_assoc]
    ring
  have hstar : ∀ w : imaginaryQuaternions, star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by
    intro w
    have hw : (w : ℍ[ℝ]).re = 0 := w.2
    ext <;> simp [hw]
  have hinv : ∀ σ, (((expUnit (v σ) * Vc)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((Vc⁻¹ : UnitQuaternion) : ℍ[ℝ]) * NormedSpace.exp (-((v σ : imaginaryQuaternions) : ℍ[ℝ])) := by
    intro σ
    rw [mul_inv_rev, ← hstar, ← NormedSpace.star_exp]
    rfl
  have h1 : AnalyticAt ℝ (fun σ => NormedSpace.exp (-((v σ : imaginaryQuaternions) : ℍ[ℝ]))) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp hv.neg
  have h3 : AnalyticAt ℝ (fun σ => T (NormedSpace.exp (-((v σ : imaginaryQuaternions) : ℍ[ℝ])))) 0 :=
    (T.analyticAt _).comp h1
  have h4 : AnalyticAt ℝ
      (fun σ => Real.exp (s * T (NormedSpace.exp (-((v σ : imaginaryQuaternions) : ℍ[ℝ]))))) 0 :=
    analyticAt_rexp.comp (analyticAt_const.mul h3)
  have h5 := h4.mul (analyticAt_const (v := (partitionFn (s * ‖q‖))⁻¹))
  refine h5.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only [TorusContours.meanKernel, div_eq_mul_inv, hinv, hT, Pi.mul_apply]
theorem bondKernelBorel_holds : BondKernelBorel := by
  intro ℓ x n _
  refine ⟨Set.toFinite _, Set.toFinite _, measurableSet_fineHotLumps_eq, measurableSet_baseChoices_eq, ?_,
    measurable_bondKernel x, measurable_averagedKernel x, ?_⟩
  · intro H b c
    have hc := continuous_contourMean (F := stepBlockFrame ℓ.side n) ℓ.baseDepth H b c
      (fun W : TorusField (n * ℓ.side) => fineLevelField ℓ n W)
      (fun x i => continuous_fineLevelField_apply x i)
    refine hc.continuousOn.congr fun W hW => ?_
    exact congrArg (fun G => contourMean ℓ.baseDepth G b (fineLevelField ℓ n W) c) hW
  · intro W b c V k e X
    have hv : AnalyticAt ℝ (fun σ : Fin k → ℝ =>
        (((∑ l, if e l = (toTorusSite n c.1, c.2) then σ l • X l else 0 : imaginaryQuaternions)) :
          ℍ[ℝ])) 0 := by
      have hfun : (fun σ : Fin k → ℝ =>
          (((∑ l, if e l = (toTorusSite n c.1, c.2) then σ l • X l else 0 : imaginaryQuaternions)) :
            ℍ[ℝ])) =
          fun σ => ∑ l, (if e l = (toTorusSite n c.1, c.2) then σ l • (X l : ℍ[ℝ]) else 0) := by
        funext σ
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp
      rw [hfun]
      refine Finset.analyticAt_fun_sum _ fun l _ => ?_
      split_ifs
      · exact ((ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l : ℍ[ℝ])).analyticAt 0
      · exact analyticAt_const
    exact analyticAt_meanKernel_expUnit_mul (ℓ.coupling * x)
      (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) (V (toTorusSite n c.1) c.2) _ hv
end YangMills.Construction.KernelMeasurability
end
