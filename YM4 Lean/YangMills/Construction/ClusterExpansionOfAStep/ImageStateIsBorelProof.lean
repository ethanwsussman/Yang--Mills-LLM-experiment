import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAStateAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.FrameIsContinuousWhereItIsRead
import YangMills.Construction.ClusterExpansionOfAStep.ImageDensityIsBorelProofForm
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.LabelsByShapes
import YangMills.Construction.ClusterExpansionOfAStep.SetsEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepCosts StepFrames StateMeasurability RenormalizationStepParameters ColdChain BlockAverages
  ColdStepAtMirrorFrames StepGas
namespace CoarseMeasurability
section
theorem measurable_comp_of_finite_range {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (f : α → β)
    (hfin : (Set.range f).Finite) (hf : ∀ b, MeasurableSet {a | f a = b}) (g : β → γ) :
    Measurable fun a => g (f a) := by
  intro s _
  have e : (fun a => g (f a)) ⁻¹' s = ⋃ b ∈ Set.range f ∩ g ⁻¹' s, {a | f a = b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      exact ⟨f a, ⟨⟨a, rfl⟩, h⟩, rfl⟩
    · rintro ⟨b, ⟨_, hb⟩, rfl⟩
      exact hb
  rw [e]
  exact MeasurableSet.biUnion (hfin.subset Set.inter_subset_left).countable fun b _ => hf b
theorem measurableSet_eq_of_standardBorel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] {f g : α → β} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a | f a = g a} := by
  let _ := upgradeStandardBorel β
  have h : MeasurableSet {p : β × β | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  exact (hf.prodMk hg) h
theorem quaternion_norm_eq_sqrt (q : ℍ[ℝ]) :
    ‖q‖ = Real.sqrt (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) := by
  rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self, Real.sqrt_mul_self (norm_nonneg _)]
theorem measurable_norm_sub_of_quaternion {Ξ : Type} [MeasurableSpace Ξ] {f g : Ξ → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) (hg : MeasurableQuaternion g) : Measurable fun ξ => ‖f ξ - g ξ‖ := by
  obtain ⟨a1, a2, a3, a4⟩ := hf
  obtain ⟨b1, b2, b3, b4⟩ := hg
  have e : (fun ξ => ‖f ξ - g ξ‖) = fun ξ => Real.sqrt (((f ξ).re - (g ξ).re) ^ 2 + ((f ξ).imI - (g ξ).imI) ^ 2 +
      ((f ξ).imJ - (g ξ).imJ) ^ 2 + ((f ξ).imK - (g ξ).imK) ^ 2) := by
    funext ξ
    rw [quaternion_norm_eq_sqrt]
    simp
  rw [e]
  exact ((((a1.sub b1).pow_const 2).add ((a2.sub b2).pow_const 2)).add ((a3.sub b3).pow_const 2)).add
    ((a4.sub b4).pow_const 2) |>.sqrt
theorem measurable_cutoffFactor {ρ : ℝ} {p : ℝ → ℝ} (hc : IsCutoff ρ p) {Ξ : Type} [MeasurableSpace Ξ]
    {u : Ξ → ℝ} (hu : Measurable u) (h0 : ∀ ξ, 0 ≤ u ξ) : Measurable fun ξ => cutoffFactor ρ p (u ξ) := by
  classical
  have hcont : ContinuousOn (fun v => Real.exp (- p v)) (Set.Ico 0 ρ) :=
    (hc.smooth.continuousOn.neg).rexp
  have hg : Measurable ((Set.Ico 0 ρ).piecewise (fun v => Real.exp (- p v)) fun _ => (0 : ℝ)) :=
    ContinuousOn.measurable_piecewise hcont continuousOn_const measurableSet_Ico
  have e : (fun ξ => cutoffFactor ρ p (u ξ)) =
      fun ξ => ((Set.Ico 0 ρ).piecewise (fun v => Real.exp (- p v)) fun _ => (0 : ℝ)) (u ξ) := by
    funext ξ
    unfold cutoffFactor
    by_cases h : u ξ < ρ
    · simp [Set.piecewise, Set.mem_Ico, h0 ξ, h]
    · simp [Set.piecewise, Set.mem_Ico, h]
  rw [e]
  exact hg.comp hu
end
section
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
theorem measurableSet_of_torusHotLumps (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (P : Finset (Finset (TorusSite n)) → Prop) :
    MeasurableSet {W : TorusField n | P (torusHotLumps ℓ W)} := by
  have e : {W : TorusField n | P (torusHotLumps ℓ W)} =
      ⋃ H ∈ {H | P H}, {W : TorusField n | torusHotLumps ℓ W = H} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨H, h, h'⟩ => h' ▸ h⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun H _ => measurableSet_torusHotLumps_eq hfit hLn H
theorem measurableSet_isHullState (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ) (Y : Finset (TorusSite n)) :
    MeasurableSet {W : TorusField n | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_setOf_isHullState <;> assumption
end
section
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def labelsWithDefault (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (ν : S → R.labels.Ω) : Yt → R.labels.Ω := fun z =>
  getOrDefault (q.labelAt z) (if h : (z : TorusSite (n * R.params.side)) ∈ S then ν ⟨z, h⟩ else d z)
theorem fillLabels_eq_labelsWithDefault (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (ν : q.unlabelled Yt → R.labels.Ω) :
    q.fillLabels Yt ν = labelsWithDefault q Yt (q.unlabelled Yt) d ν := by
  classical
  funext z
  unfold CoarseState.fillLabels labelsWithDefault
  split
  · rename_i a hz
    simp [hz, getOrDefault]
  · rename_i u hz
    have hm : (z : TorusSite (n * R.params.side)) ∈ q.unlabelled Yt := Finset.mem_filter.mpr ⟨z.2, by rw [hz]⟩
    simp [hz, getOrDefault, hm]
theorem lintegral_unlabelled_eq (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (e : q.unlabelled Yt = S) (G : (Yt → R.labels.Ω) → ℝ≥0∞) :
    ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, G (q.fillLabels Yt ν) ∂(Measure.pi fun _ => R.labels.μ) =
      ∫⁻ ν : S → R.labels.Ω, G (labelsWithDefault q Yt S d ν) ∂(Measure.pi fun _ => R.labels.μ) := by
  subst e
  refine lintegral_congr fun ν => ?_
  rw [fillLabels_eq_labelsWithDefault q Yt d ν]
variable {α : Type} [MeasurableSpace α] {Y : Finset (TorusSite n)}
theorem measurableSet_labelAt_eq_inl {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (z : TorusSite (n * R.params.side)) :
    MeasurableSet {a | CoarseState.labelAt (⟨Y, ω a⟩ : CoarseState R n) z = Sum.inl ()} := by
  have h := ((measurable_labelAt (R := R) Y z).comp hω)
    (measurableSet_range_inl (α := Unit) (β := R.labels.Ω))
  have e : {a | CoarseState.labelAt (⟨Y, ω a⟩ : CoarseState R n) z = Sum.inl ()} =
      (fun ω' : Y → CoarseLabel R.labels.Ω R.params.side =>
        CoarseState.labelAt (⟨Y, ω'⟩ : CoarseState R n) z) ∘ ω ⁻¹' Set.range Sum.inl := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.comp, Set.mem_range]
    constructor
    · intro h'
      exact ⟨(), h'.symm⟩
    · rintro ⟨u, hu⟩
      exact hu.symm
  rw [e]
  exact h
theorem measurableSet_unlabelled_eq {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (Yt S : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} := by
  classical
  have e : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} =
      ⋂ z : TorusSite (n * R.params.side),
        {a | (z ∈ Yt ∧ CoarseState.labelAt (⟨Y, ω a⟩ : CoarseState R n) z = Sum.inl ()) ↔ z ∈ S} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, CoarseState.unlabelled, Finset.mem_filter]
  rw [e]
  refine MeasurableSet.iInter fun z => ?_
  by_cases h1 : z ∈ Yt <;> by_cases h2 : z ∈ S
  · simpa [h1, h2] using measurableSet_labelAt_eq_inl hω z
  · have e' : {a | (z ∈ Yt ∧ CoarseState.labelAt (⟨Y, ω a⟩ : CoarseState R n) z = Sum.inl ()) ↔ z ∈ S} =
        {a | CoarseState.labelAt (⟨Y, ω a⟩ : CoarseState R n) z = Sum.inl ()}ᶜ := by
      ext a
      simp [h1, h2]
    rw [e']
    exact (measurableSet_labelAt_eq_inl hω z).compl
  · simp [h1, h2]
  · simp [h1, h2]
theorem measurable_labelsWithDefault {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (Yt S : Finset (TorusSite (n * R.params.side))) (d : Yt → R.labels.Ω) {β : Type} [MeasurableSpace β]
    {f : β → α} (hf : Measurable f) {g : β → S → R.labels.Ω} (hg : Measurable g) :
    Measurable fun x => labelsWithDefault (⟨Y, ω (f x)⟩ : CoarseState R n) Yt S d (g x) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  unfold labelsWithDefault
  have h1 : Measurable fun x =>
      CoarseState.labelAt (⟨Y, ω (f x)⟩ : CoarseState R n) (z : TorusSite (n * R.params.side)) :=
    (measurable_labelAt (R := R) Y _).comp (hω.comp hf)
  have h2 : Measurable fun x => if h : (z : TorusSite (n * R.params.side)) ∈ S then g x ⟨z, h⟩ else d z := by
    by_cases h : (z : TorusSite (n * R.params.side)) ∈ S
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp hg
    · simp only [dif_neg h]
      exact measurable_const
  exact measurable_getOrDefault.comp (h1.prodMk h2)
theorem measurable_blockConfigAt (C Z : Finset (TorusSite n)) {W : α → TorusField (n * R.params.side)}
    (hW : Measurable W) (Yt : Finset (TorusSite (n * R.params.side))) {lab : α → Yt → R.labels.Ω}
    (hlab : Measurable lab) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (y : TorusSite n) :
    Measurable fun a => blockConfigAt R C Z (W a) Yt (lab a) bad b y := by
  classical
  have h1 : Measurable fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).siteLabel := by
    refine measurable_pi_iff.mpr fun o => ?_
    by_cases h : blockSite y o ∈ Yt
    · have e : (fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).siteLabel o) =
          fun a => Sum.inr (lab a ⟨_, h⟩) := by
        funext a
        simp [blockConfigAt, h]
      rw [e]
      exact measurable_inr.comp ((measurable_pi_apply _).comp hlab)
    · have e : (fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).siteLabel o) = fun _ => Sum.inl () := by
        funext a
        simp [blockConfigAt, h]
      rw [e]
      exact measurable_const
  have h2 : Measurable fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).linkValue := by
    refine measurable_pi_iff.mpr fun c => ?_
    by_cases h : parentBlock R.params.side
        (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z
    · have e : (fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).linkValue c) =
          fun a => Sum.inr (W a (blockSite y c.1) c.2) := by
        funext a
        simp [blockConfigAt, h]
      rw [e]
      exact measurable_inr.comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hW))
    · have e : (fun a => (blockConfigAt R C Z (W a) Yt (lab a) bad b y).linkValue c) = fun _ => Sum.inl () := by
        funext a
        simp [blockConfigAt, h]
      rw [e]
      exact measurable_const
  have h3 : Measurable (BlockLabels.toProd ∘ fun a => blockConfigAt R C Z (W a) Yt (lab a) bad b y) := by
    have e : (BlockLabels.toProd ∘ fun a => blockConfigAt R C Z (W a) Yt (lab a) bad b y) = fun a =>
        (decide (y ∈ C), ((fun q => decide ((blockSite y q.1, q.2) ∈ bad)) : BlockBond R.params.side → Bool),
          (blockConfigAt R C Z (W a) Yt (lab a) bad b y).siteLabel, baseOffset R b y,
          (blockConfigAt R C Z (W a) Yt (lab a) bad b y).linkValue) := by
      funext a
      rfl
    rw [e]
    exact measurable_const.prodMk (measurable_const.prodMk (h1.prodMk (measurable_const.prodMk h2)))
  exact (measurable_comap_iff (g := BlockLabels.toProd)).mpr h3
theorem measurableSet_coarseStateOf_eq [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (Yt : Finset (TorusSite (n * R.params.side))) (Y : Finset (TorusSite n))
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) {lab : α → Yt → R.labels.Ω}
    (hlab : Measurable lab) :
    MeasurableSet {a | coarseStateOf R C (W a) Yt (lab a) bad b = (⟨Y, ω a⟩ : CoarseState R n)} := by
  classical
  by_cases hY : coarseHull R.params.side R.range R.nextRange bad Yt C = Y
  · subst hY
    have e : {a | coarseStateOf R C (W a) Yt (lab a) bad b =
          (⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω a⟩ : CoarseState R n)} =
        ⋂ y : coarseHull R.params.side R.range R.nextRange bad Yt C, {a |
          (if (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C then
            Sum.inr (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) (W a) Yt (lab a) bad b y)
          else Sum.inl ()) = ω a y} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, coarseStateOf, Sigma.mk.injEq, heq_eq_eq, true_and,
        funext_iff]
    rw [e]
    refine MeasurableSet.iInter fun y => ?_
    refine measurableSet_eq_of_standardBorel ?_ ((measurable_pi_apply y).comp hω)
    by_cases h : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
    · simp only [if_pos h]
      exact measurable_inr.comp (measurable_blockConfigAt _ _ hW Yt hlab bad b _)
    · simp only [if_neg h]
      exact measurable_const
  · have e : {a | coarseStateOf R C (W a) Yt (lab a) bad b = (⟨Y, ω a⟩ : CoarseState R n)} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hY (congrArg Sigma.fst h)
    rw [e]
    exact MeasurableSet.empty
theorem measurableQuaternion_comp {Ξ Ξ' : Type} [MeasurableSpace Ξ] [MeasurableSpace Ξ'] {f : Ξ → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) {g : Ξ' → Ξ} (hg : Measurable g) : MeasurableQuaternion fun x => f (g x) :=
  ⟨hf.1.comp hg, hf.2.1.comp hg, hf.2.2.1.comp hg, hf.2.2.2.comp hg⟩
theorem measurable_bondMark (hcut : IsCutoff R.ballRadius R.barrierFn) (hch : ChartCoordMeasurable)
    {v : α → TorusField n} (hv : Measurable v) {W : α → TorusField (n * R.params.side)} (hW : Measurable W)
    (b : TorusBond (n * R.params.side))
    (hf : MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => bondMark R (v a) (W a) b := by
  have h1 := measurableQuaternion_comp (hch R.params n b) (hv.prodMk hW)
  have h2 := measurable_norm_sub_of_quaternion h1 hf
  have h3 := measurable_cutoffFactor hcut h2 fun _ => norm_nonneg _
  exact h3
theorem measurable_markProduct (hcut : IsCutoff R.ballRadius R.barrierFn) (hch : ChartCoordMeasurable)
    (C : Finset (TorusSite n)) {v : α → TorusField n} (hv : Measurable v)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) (bad : Finset (TorusBond (n * R.params.side)))
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => markProduct R C (v a) (W a) bad := by
  classical
  unfold markProduct
  refine Finset.measurable_fun_prod _ fun b hb => ?_
  have hm := measurable_bondMark hcut hch hv hW b (hf b hb)
  by_cases h : b ∈ bad
  · simp only [if_pos h]
    exact measurable_const.sub hm
  · simp only [if_neg h]
    exact hm
theorem measurable_baseLaw (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by
  classical
  obtain ⟨_, h2, _, h4, _⟩ := hK R.params R.coupling n
  exact measurable_comp_of_finite_range
    (fun W : TorusField (n * R.params.side) => baseChoices R.params (fineLevelField R.params n W)) h2 h4
    (fun A => if b ∈ A then 1 / (A.card : ℝ) else 0)
open Classical in
def massIntegrand (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    (v : α → TorusField n) (ω : α → Y → CoarseLabel R.labels.Ω R.params.side)
    (p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω)) : ℝ≥0∞ :=
  if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
    ENNReal.ofReal (stepWeight R C (v p.1.1)
      (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
      (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b)
  else 0
theorem measurable_massIntegrand (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable (massIntegrand C bad Yt S b d v ω) := by
  classical
  have hA : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hWq : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2 :=
    (measurable_fieldWithStoredLinks (R := R) Y).comp ((hω.comp hA).prodMk (measurable_snd.comp measurable_fst))
  have hlab : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2 :=
    measurable_labelsWithDefault hω Yt S d hA measurable_snd
  have hv' : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1 :=
    hv.comp hA
  have hT1 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      IsHullState R.params R.range
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt} :=
    hWq (measurableSet_isHullState hfit hblock.1 R.range Yt)
  have hT2 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩} :=
    measurableSet_coarseStateOf_eq C bad b Yt Y (hω.comp hA) hWq hlab
  have hDq := ((hrow.2.borel (n * R.params.side) hblock Yt).1).comp (hWq.prodMk hlab)
  have hB := (measurable_baseLaw (R := R) hK b).comp hWq
  have hker : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
        (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c := by
    refine Finset.measurable_fun_prod _ fun c _ => ?_
    obtain ⟨_, _, _, _, _, h6, _⟩ := hK R.params R.coupling n
    have h7 := (h6 b c).comp (hWq.prodMk hv')
    exact h7
  have hf' : ∀ b' ∈ markedBonds R C, MeasurableQuaternion
      fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v p.1.1) b' : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro b' hb'
    have h := measurableQuaternion_comp (hf b' hb') hA
    exact h
  have hM : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      markProduct R C (v p.1.1)
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad := by
    exact measurable_markProduct
      (v := fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1)
      hcut hch C hv' hWq bad hf'
  have e : massIntegrand C bad Yt S b d v ω = fun p =>
      if IsHullState R.params R.range
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
        coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
      ENNReal.ofReal ((if IsHullState R.params (clusterRange R.coupling)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt then
          R.labelWeight (n * R.params.side)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) else 0) *
        baseLaw (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c) *
        markProduct R C (v p.1.1)
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad)
      else 0 := by
    funext p
    unfold massIntegrand
    by_cases h : IsHullState R.params R.range
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩
    · rw [if_pos h, if_pos h, if_pos (show IsHullState R.params (clusterRange R.coupling) _ Yt from h.1)]
      rfl
    · rw [if_neg h, if_neg h]
  rw [e]
  exact Measurable.ite (hT1.inter hT2)
    (ENNReal.measurable_ofReal.comp (((hDq.mul hB).mul hker).mul hM)) measurable_const
theorem measurable_massTerm (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => ∫⁻ W, ∫⁻ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      (open Classical in
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b = ⟨Y, ω a⟩ then
          ENNReal.ofReal (stepWeight R C (v a) (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  by_cases hne : Nonempty (Yt → R.labels.Ω)
  · obtain ⟨d⟩ := hne
    refine measurable_of_countable_cover (fun S : Finset (TorusSite (n * R.params.side)) =>
      {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S})
      (fun S => measurableSet_unlabelled_eq hω Yt S) (fun a => ⟨_, rfl⟩) fun S => ?_
    have hsub : Measurable
        (Subtype.val : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} → α) :=
      measurable_subtype_coe
    have hi := measurable_massIntegrand hK hch hrow hfit hcut hblock C bad Yt S b d
      (hv.comp hsub) (hω.comp hsub) (fun b' hb' => by
        have h := measurableQuaternion_comp (hf b' hb') hsub
        exact h)
    have h1 := (hi.lintegral_prod_right' (ν := Measure.pi fun _ : S => R.labels.μ)).lintegral_prod_right'
      (ν := fieldHaar (n * R.params.side))
    convert h1 using 2 with x
    refine lintegral_congr fun W => ?_
    exact lintegral_unlabelled_eq _ Yt S d x.2 fun l =>
      if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b =
            ⟨Y, ω x⟩ then
        ENNReal.ofReal
          (stepWeight R C (v x) (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b)
      else 0
  · have hemp : ∀ a, IsEmpty (CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω) :=
      fun a => ⟨fun ν => hne ⟨CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν⟩⟩
    have e : (fun a => ∫⁻ W, ∫⁻ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      (open Classical in
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b = ⟨Y, ω a⟩ then
          ENNReal.ofReal (stepWeight R C (v a) (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) = fun _ => 0 := by
      funext a
      have := hemp a
      simp [Measure.eq_zero_of_isEmpty
        (Measure.pi fun _ : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt => R.labels.μ)]
    rw [e]
    exact measurable_const
end
section
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurableQuaternion_of_continuousOn {s : Set (TorusField n)} {f : TorusField n → ℍ[ℝ]}
    (hf : ContinuousOn f s) {α : Type} [MeasurableSpace α] {v : α → TorusField n} (hv : Measurable v)
    (hs : ∀ a, v a ∈ s) : MeasurableQuaternion fun a => f (v a) := by
  have hι : Measurable fun a => (⟨v a, hs a⟩ : s) := hv.subtype_mk
  have hc : Continuous fun V : s => f V.1 := continuousOn_iff_continuous_domRestrict.mp hf
  have hq : ∀ g : ℍ[ℝ] → ℝ, Continuous g → Measurable fun a => g (f (v a)) := fun g hg => by
    have h1 : Continuous fun V : s => g (f V.1) := hg.comp hc
    have h2 : Measurable fun V : s => g (f V.1) := h1.measurable
    exact h2.comp hι
  exact ⟨hq _ Quaternion.continuous_re, hq _ Quaternion.continuous_imI, hq _ Quaternion.continuous_imJ,
    hq _ Quaternion.continuous_imK⟩
theorem natAbs_le_of_abs_le {e : ℤ} {m : ℕ} (h : |e| ≤ (m : ℤ)) : e.natAbs ≤ m := by apply _root_.YangMills.Construction.CongruentBoxes.natAbs_le_of_abs_le_natCast <;> assumption
theorem mem_hotCoreSites_of_le {V : TorusField n} {y z : TorusSite n} (hz : z ∈ torusHotSites R.params V)
    (h : supDist y z ≤ 2 * R.nextRange) : y ∈ hotCoreSites R V := by
  classical
  unfold hotCoreSites thickening
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, h⟩
theorem coldNearSite_of_not_mem_hotCoreSites (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hm : R.frameReach ≤ 2 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    ColdNearSite R.params.threshold R.frameReach y V := by
  intro a μ ν hlt hbox
  by_contra hc
  have hs : R.params.threshold ≤ curvature V (y + siteOfInt a) μ ν := not_lt.mp hc
  have hz := mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt hs (base_mem_plaquetteVertices _ μ ν)
  have h0 : OffsetInBox R.frameReach a := by simpa using hbox 0 (by simp [plaquetteOffsets])
  exact hy (mem_hotCoreSites_of_le hz
    ((supDist_add_siteOfInt_le y a _ fun i => natAbs_le_of_abs_le (h0 i)).trans hm))
theorem isCold_of_not_mem_hotCoreSites_of_small (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hsm : n ≤ 4 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    IsCold R.params.threshold V := by
  intro x μ ν hlt
  by_contra hc
  have hs : R.params.threshold ≤ curvature V x μ ν := not_lt.mp hc
  have hz := mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt hs (base_mem_plaquetteVertices _ μ ν)
  have h1 : supDist y x ≤ n / 2 := (supDist_le_iff y x _).mpr fun i => ZMod.natAbs_valMinAbs_le _
  exact hy (mem_hotCoreSites_of_le hz (by omega))
end
theorem coarseWeightExpansionMeasurable_holds (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hfr : continuousOn_frameCoord_of_cold) (hlb : CoarseLabelMeasureByShapes) :
    CoarseWeightExpansionMeasurable := by
  classical
  intro T hT
  refine ⟨0, fun y _ R hOn hS n _ hn Y => ?_⟩
  have hfit := hS.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) :=
    (hlb R.labels.Ω R.labels.μ R.params.side).2.1 inferInstance
  have hr40 : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hL0) hS.range_ge_side
  have hr' : 2 ^ 16 ≤ R.nextRange := hS.nextRange_ge
  have hab := hS.range_le
  have hm16 : 16 ≤ R.frameReach := by
    unfold StepSetup.frameReach
    norm_num at hr40 ⊢
    omega
  have hmr : R.frameReach ≤ R.range / 2 ^ 11 := le_refl _
  have hm : R.frameReach ≤ 2 * R.nextRange := by
    norm_num at hr' hmr
    omega
  have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn₀
  have ha : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, hOn.anchorRadius_eq]
    exact hT.chain
  have hσA : R.params.threshold ≤ T.σA := by
    rw [hσ]
    linarith [hT.σ_le, hT.σ_pos]
  have hcont : ∀ (C : Finset (TorusSite n)), ∀ b ∈ markedBonds R C,
      ContinuousOn
        (fun V : TorusField n =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        {V | hotCoreSites R V = C} := by
    intro C b hb
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨h1, h2⟩ := hfr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hchain hσA R.depth
      R.frameReach n hm16 n64 b hb'.1
    by_cases hs : 4 * R.frameReach + 5 < n
    · refine (h1 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      exact coldNearSite_of_not_mem_hotCoreSites hfit hn.1 hm (by rw [hV']; exact hb'.2)
    · refine (h2 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      have hsm : n ≤ 4 * R.nextRange := by
        norm_num at hr' hmr
        omega
      exact isCold_of_not_mem_hotCoreSites_of_small hfit hn.1 hsm (y := parentBlock R.params.side b.1)
        (by rw [hV']; exact hb'.2)
  refine measurable_of_countable_cover (fun C : Finset (TorusSite n) =>
    {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C})
    (fun C => measurable_fst
      (measurableSet_of_torusHotLumps hfit hn.1 fun H => thickening (2 * R.nextRange) (H.biUnion id) = C))
    (fun p => ⟨_, rfl⟩) fun C => ?_
  have hv : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} => a.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hω : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} => a.1.2 :=
    measurable_snd.comp measurable_subtype_coe
  have hfq : ∀ b ∈ markedBonds R C, MeasurableQuaternion
      fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach a.1.1 b : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro b hb
    exact measurableQuaternion_of_continuousOn (hcont C b hb) hv fun a => a.2
  have hmass : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} =>
      coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) := by
    unfold coarseStateMass
    refine Finset.measurable_fun_sum _ fun bad _ => Finset.measurable_fun_sum _ fun Yt _ =>
      Finset.measurable_fun_sum _ fun b _ => ?_
    exact measurable_massTerm hK hch hS.hasExpansions hfit hS.isCutoff hblock C bad Yt b hv hω hfq
  have e : (fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} =>
      if IsHullState R.params R.nextRange a.1.1 Y then coarseWeightExpansion R n a.1.1 Y a.1.2 else 0) =
      fun a => if IsHullState R.params R.nextRange a.1.1 Y then
        (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal else 0 := by
    funext a
    have hC : hotCoreSites R a.1.1 = C := a.2
    have h2 : coarseWeightExpansion R n a.1.1 Y a.1.2 =
        (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal := by
      unfold coarseWeightExpansion
      rw [dif_neg (NeZero.ne n)]
      show coarseStateWeight R (hotCoreSites R a.1.1) a.1.1 ⟨Y, a.1.2⟩ = _
      rw [hC]
      rfl
    rw [h2]
  exact e ▸ Measurable.ite (hv (measurableSet_isHullState hfit hn.1 R.nextRange Y))
    (ENNReal.measurable_toReal.comp hmass) measurable_const
end CoarseMeasurability
end YangMills.Construction
end
