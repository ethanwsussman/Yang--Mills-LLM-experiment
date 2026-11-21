import YangMills.Construction.ClusterExpansionOfAStep.ActionOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.LabelsByShapes
import YangMills.Construction.ClusterExpansionOfAStep.PlacesOfABlock
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings BlockPlaces
open BlockAverages hiding unitStep
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem blockConfig_ext {Ω : Type} {L : ℕ} {s s' : BlockLabels Ω L} (h1 : s.isCore = s'.isCore)
    (h2 : s.badBond = s'.badBond) (h3 : s.siteLabel = s'.siteLabel) (h4 : s.basePoint = s'.basePoint)
    (h5 : s.linkValue = s'.linkValue) : s = s' := by
  cases s
  cases s'
  simp_all
theorem markAt_of_inr {q : CoarseState R n} {y : TorusSite n} (hy : y ∈ q.1)
    {s : BlockLabels R.labels.Ω R.params.side} (h : q.2 ⟨y, hy⟩ = Sum.inr s) : q.markAt y = some s := by
  simp [CoarseState.markAt, hy, h]
theorem markAt_of_inl {q : CoarseState R n} {y : TorusSite n} (hy : y ∈ q.1)
    (h : q.2 ⟨y, hy⟩ = Sum.inl ()) : q.markAt y = none := by
  simp [CoarseState.markAt, hy, h]
theorem markAt_of_not_mem {q : CoarseState R n} {y : TorusSite n} (hy : y ∉ q.1) : q.markAt y = none := by
  simp [CoarseState.markAt, hy]
theorem labelAt_blockSite {q : CoarseState R n} {y : TorusSite n} {s : BlockLabels R.labels.Ω R.params.side}
    (h : q.markAt y = some s) (o : BlockOffset R.params.side) :
    q.labelAt (blockSite y o) = s.siteLabel o := by
  simp only [CoarseState.labelAt]
  rw [parentBlock_blockSite, h, siteOffset_blockSite]
theorem labelAt_of_decorationAt {q : CoarseState R n} {z : TorusSite (n * R.params.side)}
    {s : BlockLabels R.labels.Ω R.params.side}
    (h : q.markAt (parentBlock R.params.side z) = some s) : q.labelAt z = s.siteLabel (siteOffset z) := by
  simp only [CoarseState.labelAt]
  rw [h]
theorem labelAt_of_decorationAt_none {q : CoarseState R n} {z : TorusSite (n * R.params.side)}
    (h : q.markAt (parentBlock R.params.side z) = none) : q.labelAt z = Sum.inl () := by
  simp only [CoarseState.labelAt]
  rw [h]
theorem mem_labelSet {q : CoarseState R n} {z : TorusSite (n * R.params.side)} :
    z ∈ q.labelSet ↔ q.labelAt z ≠ Sum.inl () := by
  simp [CoarseState.labelSet]
theorem labelAt_eq_inr_labeling (q : CoarseState R n) (z : q.labelSet) :
    q.labelAt z = Sum.inr (q.labeling z) := by
  unfold CoarseState.labeling
  split
  · rename_i a h
    exact h
  · rename_i u h
    exact absurd h (mem_labelSet.mp z.2)
theorem labelSpace_act_congr (Λ : LabelSpace) {m : ℕ} [NeZero m] {S S' : Finset (TorusSite m)} (h : S = S')
    (g : TorusSite m → UnitQuaternion) (a : S → Λ.Ω) (a' : S' → Λ.Ω)
    (ha : ∀ z hz hz', a ⟨z, hz⟩ = a' ⟨z, hz'⟩)
    (z : TorusSite m) (hz : z ∈ S) (hz' : z ∈ S') : Λ.act S g a ⟨z, hz⟩ = Λ.act S' g a' ⟨z, hz'⟩ := by
  subst h
  have : a = a' := funext fun x => ha x.1 x.2 x.2
  rw [this]
def _root_.YangMills.Construction.StepSettings.CoarseState.gaugeTransform (q : CoarseState R n)
    (g : TorusSite n → UnitQuaternion) : CoarseState R n :=
  ⟨q.1, coarseGaugeAct (R := R) q.1 g q.2⟩
theorem markAt_gaugeTransform (q : CoarseState R n) (g : TorusSite n → UnitQuaternion) (y : TorusSite n) :
    (q.gaugeTransform g).markAt y = (q.markAt y).map (gaugeOnCoarseState q g y) := by
  by_cases hy : y ∈ q.1
  · rcases h : q.2 ⟨y, hy⟩ with ⟨⟩ | s
    · rw [markAt_of_inl hy h]
      refine markAt_of_inl (q := q.gaugeTransform g) hy ?_
      simp only [CoarseState.gaugeTransform, coarseGaugeAct, h]
    · rw [markAt_of_inr hy h]
      refine markAt_of_inr (q := q.gaugeTransform g) hy ?_
      simp only [CoarseState.gaugeTransform, coarseGaugeAct, h]
  · rw [markAt_of_not_mem hy]
    exact markAt_of_not_mem (q := q.gaugeTransform g) hy
theorem labelAt_gaugeTransform_of_mem (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ q.labelSet) :
    (q.gaugeTransform g).labelAt z =
      Sum.inr (R.labels.act q.labelSet (blockConstantGauge R.params.side g) q.labeling ⟨z, hz⟩) := by
  have hz' := mem_labelSet.mp hz
  rcases h : q.markAt (parentBlock R.params.side z) with ⟨⟩ | s
  · exact absurd (labelAt_of_decorationAt_none h) hz'
  · have h2 := markAt_gaugeTransform q g (parentBlock R.params.side z)
    rw [h] at h2
    rw [labelAt_of_decorationAt (s := gaugeOnCoarseState q g (parentBlock R.params.side z) s) (by rw [h2]; rfl)]
    simp only [gaugeOnCoarseState, blockSite_parentBlock_siteOffset, dif_pos hz]
theorem labelAt_gaugeTransform_of_not_mem (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    {z : TorusSite (n * R.params.side)} (hz : z ∉ q.labelSet) :
    (q.gaugeTransform g).labelAt z = Sum.inl () := by
  have hz' : q.labelAt z = Sum.inl () := by
    by_contra h
    exact hz (mem_labelSet.mpr h)
  rcases h : q.markAt (parentBlock R.params.side z) with ⟨⟩ | s
  · have h2 := markAt_gaugeTransform q g (parentBlock R.params.side z)
    rw [h] at h2
    exact labelAt_of_decorationAt_none h2
  · have h2 := markAt_gaugeTransform q g (parentBlock R.params.side z)
    rw [h] at h2
    rw [labelAt_of_decorationAt (s := gaugeOnCoarseState q g (parentBlock R.params.side z) s) (by rw [h2]; rfl)]
    simp only [gaugeOnCoarseState, blockSite_parentBlock_siteOffset, dif_neg hz]
    rw [← labelAt_of_decorationAt h]
    exact hz'
theorem labelSet_gaugeTransform (q : CoarseState R n) (g : TorusSite n → UnitQuaternion) :
    (q.gaugeTransform g).labelSet = q.labelSet := by
  ext z
  by_cases hz : z ∈ q.labelSet
  · simp only [hz, iff_true]
    refine mem_labelSet.mpr ?_
    rw [labelAt_gaugeTransform_of_mem q g hz]
    simp
  · simp only [hz, iff_false]
    intro h
    exact mem_labelSet.mp h (labelAt_gaugeTransform_of_not_mem q g hz)
theorem labeling_gaugeTransform (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (z : TorusSite (n * R.params.side)) (hz : z ∈ q.labelSet) (hz' : z ∈ (q.gaugeTransform g).labelSet) :
    (q.gaugeTransform g).labeling ⟨z, hz'⟩ =
      R.labels.act q.labelSet (blockConstantGauge R.params.side g) q.labeling ⟨z, hz⟩ := by
  have h1 := labelAt_eq_inr_labeling (q.gaugeTransform g) ⟨z, hz'⟩
  rw [labelAt_gaugeTransform_of_mem q g hz] at h1
  exact (Sum.inr_injective h1).symm
theorem coarseGaugeAct_of_inr {Y : Finset (TorusSite n)} {g : TorusSite n → UnitQuaternion}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side} {y : Y}
    {s : BlockLabels R.labels.Ω R.params.side} (h : ω y = Sum.inr s) :
    coarseGaugeAct (R := R) Y g ω y = Sum.inr (gaugeOnCoarseState (R := R) ⟨Y, ω⟩ g y s) := by
  simp only [coarseGaugeAct, h]
theorem coarseGaugeAct_of_inl {Y : Finset (TorusSite n)} {g : TorusSite n → UnitQuaternion}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side} {y : Y}
    (h : ω y = Sum.inl ()) : coarseGaugeAct (R := R) Y g ω y = Sum.inl () := by
  simp only [coarseGaugeAct, h]
theorem gaugeOnCoarseState_one (q : CoarseState R n) {y : TorusSite n} {s : BlockLabels R.labels.Ω R.params.side}
    (h : q.markAt y = some s) : gaugeOnCoarseState q (fun _ => 1) y s = s := by
  refine blockConfig_ext rfl rfl ?_ rfl ?_
  · funext o
    simp only [gaugeOnCoarseState]
    split_ifs with hz
    · have h1 := labelAt_eq_inr_labeling q ⟨_, hz⟩
      have h2 : blockConstantGauge R.params.side (fun _ : TorusSite n => (1 : UnitQuaternion)) = fun _ => 1 := rfl
      rw [h2, R.labels.act_one, ← h1]
      exact labelAt_blockSite h o
    · rfl
  · funext c
    simp only [gaugeOnCoarseState]
    rcases s.linkValue c with ⟨⟩ | w
    · rfl
    · simp [blockConstantGauge]
theorem coarseGaugeAct_one (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseGaugeAct (R := R) Y (fun _ => 1) ω = ω := by
  funext y
  rcases h : ω y with ⟨⟩ | s
  · exact coarseGaugeAct_of_inl h
  · rw [coarseGaugeAct_of_inr h, gaugeOnCoarseState_one (R := R) ⟨Y, ω⟩ (markAt_of_inr (q := ⟨Y, ω⟩) y.2 h)]
theorem coarseGaugeAct_mul (Y : Finset (TorusSite n)) (g g' : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseGaugeAct (R := R) Y (g * g') ω = coarseGaugeAct (R := R) Y g (coarseGaugeAct (R := R) Y g' ω) := by
  funext y
  rcases h : ω y with ⟨⟩ | s
  · rw [coarseGaugeAct_of_inl h, coarseGaugeAct_of_inl (coarseGaugeAct_of_inl h)]
  · rw [coarseGaugeAct_of_inr h, coarseGaugeAct_of_inr (coarseGaugeAct_of_inr h)]
    congr 1
    set q : CoarseState R n := ⟨Y, ω⟩ with hq
    have hq' : (⟨Y, coarseGaugeAct (R := R) Y g' ω⟩ : CoarseState R n) = q.gaugeTransform g' := rfl
    rw [hq']
    refine blockConfig_ext rfl rfl ?_ rfl ?_
    · funext o
      simp only [gaugeOnCoarseState]
      have hS := labelSet_gaugeTransform q g'
      by_cases hz : blockSite (y : TorusSite n) o ∈ q.labelSet
      · have hz' : blockSite (y : TorusSite n) o ∈ (q.gaugeTransform g').labelSet := hS ▸ hz
        rw [dif_pos hz, dif_pos hz']
        congr 1
        have hmul : blockConstantGauge R.params.side (g * g') =
            blockConstantGauge R.params.side g * blockConstantGauge R.params.side g' := rfl
        rw [hmul, R.labels.act_mul]
        refine labelSpace_act_congr R.labels hS.symm _ _ _ (fun z hz1 hz2 => ?_) _ _ _
        exact (labeling_gaugeTransform q g' z hz1 hz2).symm
      · have hz' : blockSite (y : TorusSite n) o ∉ (q.gaugeTransform g').labelSet := hS ▸ hz
        rw [dif_neg hz, dif_neg hz', dif_neg hz]
    · funext c
      simp only [gaugeOnCoarseState]
      rcases s.linkValue c with ⟨⟩ | w
      · rfl
      · simp only [blockConstantGauge, Pi.mul_apply, mul_inv_rev]
        group
theorem gaugeOnCoarseState_of_trivial_near (hL : 2 ≤ R.params.side) (q : CoarseState R n)
    {g : TorusSite n → UnitQuaternion} {y : TorusSite n}
    {s : BlockLabels R.labels.Ω R.params.side} (hs : q.markAt y = some s)
    (hg : ∀ z, supDist z y ≤ 1 → g z = 1) :
    gaugeOnCoarseState q g y s = s := by
  have hnear : ∀ (x u : TorusSite (n * R.params.side)), parentBlock R.params.side x = y → supDist u x ≤ 1 →
      blockConstantGauge R.params.side g u = 1 := by
    intro x u hx hu
    refine hg _ ?_
    have := supDist_parentBlock_le_one hL u x hu
    rwa [hx] at this
  refine blockConfig_ext rfl rfl ?_ rfl ?_
  · funext o
    simp only [gaugeOnCoarseState]
    split_ifs with hz
    · have hf := R.labels.act_free q.labelSet (blockConstantGauge R.params.side g) q.labeling ⟨_, hz⟩
        (fun u hu => hnear _ u (parentBlock_blockSite y o) hu)
      rw [hf, ← labelAt_eq_inr_labeling]
      exact labelAt_blockSite hs o
    · rfl
  · funext c
    simp only [gaugeOnCoarseState]
    rcases s.linkValue c with ⟨⟩ | w
    · rfl
    · have h1 := hnear (blockSite y c.1) (blockSite y c.1) (parentBlock_blockSite y c.1)
        (by rw [supDist_self]; omega)
      have h2 := hnear (blockSite y c.1) (blockSite y c.1 + unitStep (n * R.params.side) c.2)
        (parentBlock_blockSite y c.1) (by rw [supDist_comm]; exact supDist_add_unitStep_le _ _)
      simp only [h1, h2, one_mul, inv_one, mul_one]
theorem coarseGaugeAct_of_trivial_near (hL : 2 ≤ R.params.side) (Y : Finset (TorusSite n))
    (g : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (y : Y) (hg : ∀ z, supDist z (y : TorusSite n) ≤ 1 → g z = 1) :
    coarseGaugeAct (R := R) Y g ω y = ω y := by
  rcases h : ω y with ⟨⟩ | s
  · exact coarseGaugeAct_of_inl h
  · rw [coarseGaugeAct_of_inr h,
      gaugeOnCoarseState_of_trivial_near hL (R := R) ⟨Y, ω⟩ (markAt_of_inr (q := ⟨Y, ω⟩) y.2 h) hg]
theorem coarseGaugeAct_local (hL : 2 ≤ R.params.side) (Y Y' : Finset (TorusSite n))
    (g g' : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (ω' : Y' → CoarseLabel R.labels.Ω R.params.side)
    (y : TorusSite n) (hy : y ∈ Y) (hy' : y ∈ Y')
    (hg : ∀ z, supDist z y ≤ 1 → g z = g' z) (hY : ∀ z, supDist z y ≤ 1 → (z ∈ Y ↔ z ∈ Y'))
    (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), supDist z y ≤ 1 → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) :
    coarseGaugeAct (R := R) Y g ω ⟨y, hy⟩ = coarseGaugeAct (R := R) Y' g' ω' ⟨y, hy'⟩ := by
  have h0 : ω ⟨y, hy⟩ = ω' ⟨y, hy'⟩ := hω y hy hy' (by rw [supDist_self]; omega)
  rcases h : ω ⟨y, hy⟩ with ⟨⟩ | s
  · rw [coarseGaugeAct_of_inl h, coarseGaugeAct_of_inl (h0 ▸ h)]
  · have h' : ω' ⟨y, hy'⟩ = Sum.inr s := h0 ▸ h
    rw [coarseGaugeAct_of_inr h, coarseGaugeAct_of_inr h']
    congr 1
    set q : CoarseState R n := ⟨Y, ω⟩ with hq
    set q' : CoarseState R n := ⟨Y', ω'⟩ with hq'
    have hst : ∀ u, supDist u y ≤ 1 → q.markAt u = q'.markAt u := by
      intro u hu
      by_cases hm : u ∈ Y
      · have hm' := (hY u hu).mp hm
        have he := hω u hm hm' hu
        rcases h2 : ω ⟨u, hm⟩ with ⟨⟩ | t
        · rw [markAt_of_inl (q := q) hm h2, markAt_of_inl (q := q') hm' (he.symm.trans h2)]
        · rw [markAt_of_inr (q := q) hm h2, markAt_of_inr (q := q') hm' (he.symm.trans h2)]
      · have hm' : u ∉ Y' := fun h3 => hm ((hY u hu).mpr h3)
        rw [markAt_of_not_mem (q := q) hm, markAt_of_not_mem (q := q') hm']
    have hlab : ∀ z, supDist (parentBlock R.params.side z) y ≤ 1 → q.labelAt z = q'.labelAt z := by
      intro z hz
      simp only [CoarseState.labelAt]
      rw [hst _ hz]
    have hnear : ∀ (x u : TorusSite (n * R.params.side)), parentBlock R.params.side x = y → supDist u x ≤ 1 →
        supDist (parentBlock R.params.side u) y ≤ 1 := by
      intro x u hx hu
      have := supDist_parentBlock_le_one hL u x hu
      rwa [hx] at this
    refine blockConfig_ext rfl rfl ?_ rfl ?_
    · funext o
      simp only [gaugeOnCoarseState]
      have hb : parentBlock R.params.side (blockSite y o : TorusSite (n * R.params.side)) = y :=
        parentBlock_blockSite y o
      have hmem : ∀ u, supDist u (blockSite y o) ≤ 1 → (u ∈ q.labelSet ↔ u ∈ q'.labelSet) := by
        intro u hu
        rw [mem_labelSet, mem_labelSet, hlab u (hnear _ u hb hu)]
      by_cases hz : blockSite y o ∈ q.labelSet
      · have hz' := (hmem _ (by rw [supDist_self]; omega)).mp hz
        rw [dif_pos hz, dif_pos hz']
        congr 1
        refine R.labels.act_local q.labelSet q'.labelSet _ _ _ _ _ hz hz' (fun u hu => ?_) hmem
          (fun u h1 h2 hu => ?_)
        · exact hg _ (hnear _ u hb hu)
        · have e1 := labelAt_eq_inr_labeling q ⟨u, h1⟩
          have e2 := labelAt_eq_inr_labeling q' ⟨u, h2⟩
          have e3 := hlab u (hnear _ u hb hu)
          simp only at e1 e2
          rw [e1, e2] at e3
          exact Sum.inr_injective e3
      · have hz' : blockSite y o ∉ q'.labelSet := fun h3 =>
          hz ((hmem _ (by rw [supDist_self]; omega)).mpr h3)
        rw [dif_neg hz, dif_neg hz']
    · funext c
      simp only [gaugeOnCoarseState]
      rcases s.linkValue c with ⟨⟩ | w
      · rfl
      · have hb : parentBlock R.params.side (blockSite y c.1 : TorusSite (n * R.params.side)) = y :=
          parentBlock_blockSite y c.1
        have h1 : blockConstantGauge R.params.side g (blockSite y c.1) =
            blockConstantGauge R.params.side g' (blockSite y c.1) :=
          hg _ (hnear _ _ hb (by rw [supDist_self]; omega))
        have h2 : blockConstantGauge R.params.side g (blockSite y c.1 + unitStep (n * R.params.side) c.2) =
            blockConstantGauge R.params.side g' (blockSite y c.1 + unitStep (n * R.params.side) c.2) :=
          hg _ (hnear _ _ hb (by rw [supDist_comm]; exact supDist_add_unitStep_le _ _))
        rw [h1, h2]
section Shapes
instance instSecondCountableTopologyUnitQuaternion : SecondCountableTopology UnitQuaternion :=
  TopologicalSpace.Subtype.secondCountableTopology _
theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [Measure.IsMulLeftInvariant μ] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
instance instIsMulRightInvariantHaarUnit : Measure.IsMulRightInvariant haarUnit := by
  constructor
  intro g
  have : Measure.IsMulLeftInvariant (Measure.map (· * g) haarUnit) := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (Measure.map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
theorem measurePreserving_mul_mul_inv (g h : UnitQuaternion) :
    MeasurePreserving (fun u : UnitQuaternion => g * u * h⁻¹) haarUnit haarUnit :=
  (measurePreserving_mul_right haarUnit h⁻¹).comp (measurePreserving_mul_left haarUnit g)
theorem measurePreserving_comp_equiv {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (e : ι ≃ κ) :
    MeasurePreserving (fun (a : κ → X) i => a (e i)) (Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι => μ) := by
  have hm : Measurable (fun (a : κ → X) i => a (e i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq (μ := fun _ : ι => μ) fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (a : κ → X) i => a (e i)) ⁻¹' Set.pi univ s = Set.pi univ fun k => s (e.symm k) := by
    ext a
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h k
      have := h (e.symm k)
      simpa using this
    · intro h i
      have := h (e i)
      simpa using this
  rw [hpre, Measure.pi_pi]
  exact Equiv.prod_comp e.symm fun i => μ (s i)
variable (Y : Finset (TorusSite n)) (σ : Y → Option (BlockShape R.params.side))
theorem labelOfShape_cases {L : ℕ} {Ω : Type} (sh : Option (BlockShape L))
    (pr : (storedOffsets sh → Ω) × (storedBonds sh → UnitQuaternion)) :
    (sh = none ∧ labelOfShape sh pr = Sum.inl ()) ∨ ∃ s : BlockLabels Ω L, labelOfShape sh pr = Sum.inr s ∧
      ∀ o, s.siteLabel o = open Classical in
        if h : o ∈ storedOffsets sh then Sum.inr (pr.1 ⟨o, h⟩) else Sum.inl () := by
  classical
  rcases sh with ⟨⟩ | sh
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨markOfShape sh pr.1 pr.2, rfl, fun o => ?_⟩
    by_cases h : o ∈ storedOffsets (some sh)
    · rw [dif_pos h]
      exact dif_pos (show o ∈ sh.2.2.1 from h)
    · rw [dif_neg h]
      exact dif_neg (show o ∉ sh.2.2.1 from h)
abbrev shapeState (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) : CoarseState R n :=
  ⟨Y, labelsOfShapes σ p⟩
theorem labelAt_shapeState (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (y : Y)
    (o : BlockOffset R.params.side) :
    (shapeState Y σ p).labelAt (blockSite (y : TorusSite n) o) =
      open Classical in if h : o ∈ storedOffsets (σ y) then Sum.inr (p.1 ⟨y, ⟨o, h⟩⟩) else Sum.inl () := by
  rcases labelOfShape_cases (σ y) (fun o => p.1 ⟨y, o⟩, fun c => p.2 ⟨y, c⟩) with ⟨h1, h2⟩ | ⟨s, h1, h2⟩
  · have hn : o ∉ storedOffsets (σ y) := by
      rw [h1]
      simp [storedOffsets]
    rw [dif_neg hn]
    refine labelAt_of_decorationAt_none ?_
    rw [parentBlock_blockSite]
    exact markAt_of_inl (q := ⟨Y, labelsOfShapes σ p⟩) y.2 h2
  · rw [labelAt_blockSite (s := s) (markAt_of_inr (q := ⟨Y, labelsOfShapes σ p⟩) y.2 h1), h2 o]
open Classical in
def shapeLabelSites : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ.filter fun z => ∃ y : Y, parentBlock R.params.side z = y ∧ siteOffset z ∈ storedOffsets (σ y)
theorem labelSet_shapeState (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) :
    (shapeState Y σ p).labelSet = shapeLabelSites Y σ := by
  classical
  ext z
  rw [mem_labelSet]
  simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_cases hy : parentBlock R.params.side z ∈ Y
    · refine ⟨⟨_, hy⟩, rfl, ?_⟩
      by_contra hn
      have h1 := labelAt_shapeState Y σ p ⟨_, hy⟩ (siteOffset z)
      simp only [blockSite_parentBlock_siteOffset] at h1
      rw [dif_neg hn] at h1
      exact h h1
    · exact absurd (labelAt_of_decorationAt_none (markAt_of_not_mem (q := ⟨Y, labelsOfShapes σ p⟩) hy)) h
  · rintro ⟨y, hy, hm⟩
    have h1 := labelAt_shapeState Y σ p y (siteOffset z)
    rw [← hy, blockSite_parentBlock_siteOffset, dif_pos hm] at h1
    rw [h1]
    simp
def shapeLabelSite (x : Σ y : Y, storedOffsets (σ y)) : shapeLabelSites Y σ :=
  ⟨blockSite (x.1 : TorusSite n) x.2.1, by
      classical
      simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x.1, parentBlock_blockSite _ _, by rw [siteOffset_blockSite]; exact x.2.2⟩⟩
noncomputable def shapeLabelEquiv : (Σ y : Y, storedOffsets (σ y)) ≃ shapeLabelSites Y σ :=
  Equiv.ofBijective (shapeLabelSite Y σ)
    (by
     refine ⟨?_, ?_⟩
     ·
      rintro ⟨y, o⟩ ⟨y', o'⟩ h
      have h1 : blockSite (y : TorusSite n) o.1 = blockSite (y' : TorusSite n) o'.1 := congrArg Subtype.val h
      have hy : y = y' := Subtype.ext (by
        have := congrArg (parentBlock R.params.side) h1
        rwa [parentBlock_blockSite, parentBlock_blockSite] at this)
      subst hy
      have ho : o = o' := Subtype.ext (by
        have := congrArg siteOffset h1
        rwa [siteOffset_blockSite, siteOffset_blockSite] at this)
      subst ho
      rfl
     · classical
       rintro ⟨z, hz⟩
       have hz' := hz
       simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
       obtain ⟨y, hy, hm⟩ := hz'
       refine ⟨⟨y, ⟨siteOffset z, hm⟩⟩, Subtype.ext ?_⟩
       show blockSite (y : TorusSite n) (siteOffset z) = z
       rw [← hy, blockSite_parentBlock_siteOffset])
theorem labeling_shapeState (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) (x : Σ y : Y, storedOffsets (σ y))
    (h : blockSite (x.1 : TorusSite n) x.2.1 ∈ (shapeState Y σ p).labelSet) :
    (shapeState Y σ p).labeling ⟨_, h⟩ = p.1 x := by
  have h1 := labelAt_eq_inr_labeling (⟨Y, labelsOfShapes σ p⟩ : CoarseState R n) ⟨_, h⟩
  have h2 := labelAt_shapeState Y σ p x.1 x.2.1
  simp only at h1
  rw [dif_pos x.2.2] at h2
  rw [h1] at h2
  exact Sum.inr_injective h2
def storedBondSite (c : Σ y : Y, storedBonds (σ y)) : TorusSite (n * R.params.side) :=
  blockSite (c.1 : TorusSite n) c.2.1.1
def shapeGaugeAct (g : TorusSite n → UnitQuaternion) (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) :
    ShapeLabelData R.labels.Ω σ × ShapeLinkData σ :=
  (fun x => R.labels.act (shapeLabelSites Y σ) (blockConstantGauge R.params.side g)
      (fun z => p.1 ((shapeLabelEquiv Y σ).symm z)) (shapeLabelEquiv Y σ x),
    fun c => blockConstantGauge R.params.side g (storedBondSite Y σ c) * p.2 c *
      (blockConstantGauge R.params.side g (storedBondSite Y σ c + unitStep (n * R.params.side) c.2.1.2))⁻¹)
theorem gaugeOnCoarseState_labelOfShape (q : CoarseState R n) (g : TorusSite n → UnitQuaternion) (y : TorusSite n)
    (sh : Option (BlockShape R.params.side))
    (pr : (storedOffsets sh → R.labels.Ω) × (storedBonds sh → UnitQuaternion)) (a' : storedOffsets sh → R.labels.Ω)
    (h1 : ∀ o (ho : o ∈ storedOffsets sh), ∃ hz : blockSite y o ∈ q.labelSet,
      R.labels.act q.labelSet (blockConstantGauge R.params.side g) q.labeling ⟨_, hz⟩ = a' ⟨o, ho⟩)
    (h2 : ∀ o, o ∉ storedOffsets sh → blockSite y o ∉ q.labelSet) :
    (match labelOfShape sh pr with
      | Sum.inr s => (Sum.inr (gaugeOnCoarseState q g y s) : CoarseLabel R.labels.Ω R.params.side)
      | Sum.inl u => Sum.inl u) =
      labelOfShape sh (a', fun c => blockConstantGauge R.params.side g (blockSite y c.1.1) * pr.2 c *
        (blockConstantGauge R.params.side g (blockSite y c.1.1 + unitStep (n * R.params.side) c.1.2))⁻¹) := by
  classical
  rcases sh with ⟨⟩ | sh
  · rfl
  · show Sum.inr (gaugeOnCoarseState q g y (markOfShape sh pr.1 pr.2)) = Sum.inr (markOfShape sh a' _)
    congr 1
    refine blockConfig_ext rfl rfl ?_ rfl ?_
    · funext o
      simp only [gaugeOnCoarseState, markOfShape]
      by_cases ho : o ∈ sh.2.2.1
      · obtain ⟨hz, e⟩ := h1 o ho
        rw [dif_pos hz, dif_pos ho, e]
        rfl
      · have hz := h2 o ho
        rw [dif_neg hz, dif_neg ho, dif_neg ho]
    · funext c
      simp only [gaugeOnCoarseState, markOfShape]
      by_cases hc : c ∈ sh.2.2.2.2
      · simp only [dif_pos hc]
      · simp only [dif_neg hc]
theorem coarseGaugeAct_labelsOfShapes (g : TorusSite n → UnitQuaternion)
    (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) :
    coarseGaugeAct (R := R) Y g (labelsOfShapes σ p) = labelsOfShapes σ (shapeGaugeAct Y σ g p) := by
  classical
  funext y
  set q : CoarseState R n := shapeState Y σ p with hq
  have hS := labelSet_shapeState Y σ p
  refine gaugeOnCoarseState_labelOfShape q g y (σ y) (fun o => p.1 ⟨y, o⟩, fun c => p.2 ⟨y, c⟩)
    (fun o => (shapeGaugeAct Y σ g p).1 ⟨y, o⟩) ?_ ?_
  · intro o ho
    have hz : blockSite (y : TorusSite n) o ∈ q.labelSet := by
      rw [hS]
      exact (shapeLabelEquiv Y σ ⟨y, ⟨o, ho⟩⟩).2
    refine ⟨hz, ?_⟩
    refine labelSpace_act_congr R.labels hS _ _ _ (fun z h1 h2 => ?_) _ _ _
    have hx : (shapeLabelEquiv Y σ ((shapeLabelEquiv Y σ).symm ⟨z, h2⟩) : TorusSite (n * R.params.side)) = z := by
      rw [Equiv.apply_symm_apply]
    obtain ⟨x, hx'⟩ := (shapeLabelEquiv Y σ).surjective ⟨z, h2⟩
    have hz2 : z = blockSite (x.1 : TorusSite n) x.2.1 := (congrArg Subtype.val hx').symm
    subst hz2
    rw [labeling_shapeState Y σ p x h1]
    exact congrArg p.1 ((shapeLabelEquiv Y σ).symm_apply_eq.mpr hx'.symm).symm
  · intro o ho hz
    rw [hS] at hz
    simp only [shapeLabelSites, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨y', hy', hm⟩ := hz
    rw [parentBlock_blockSite] at hy'
    have : y = y' := Subtype.ext hy'
    subst this
    rw [siteOffset_blockSite] at hm
    exact ho hm
theorem measurePreserving_shapeGaugeAct (g : TorusSite n → UnitQuaternion) :
    MeasurePreserving (shapeGaugeAct Y σ g)
      ((Measure.pi fun _ : Σ y : Y, storedOffsets (σ y) => R.labels.μ).prod
        (Measure.pi fun _ : Σ y : Y, storedBonds (σ y) => haarUnit))
      ((Measure.pi fun _ : Σ y : Y, storedOffsets (σ y) => R.labels.μ).prod
        (Measure.pi fun _ : Σ y : Y, storedBonds (σ y) => haarUnit)) := by
  have h1 := measurePreserving_comp_equiv R.labels.μ (shapeLabelEquiv Y σ).symm
  have h2 := R.labels.act_keeps (shapeLabelSites Y σ) (blockConstantGauge R.params.side g)
  have h3 := measurePreserving_comp_equiv R.labels.μ (shapeLabelEquiv Y σ)
  have h4 := measurePreserving_pi (fun _ : Σ y : Y, storedBonds (σ y) => (haarUnit : Measure UnitQuaternion))
    (fun _ => (haarUnit : Measure UnitQuaternion)) (fun c => measurePreserving_mul_mul_inv
      (blockConstantGauge R.params.side g (storedBondSite Y σ c))
      (blockConstantGauge R.params.side g (storedBondSite Y σ c + unitStep (n * R.params.side) c.2.1.2)))
  exact (h3.comp (h2.comp h1)).prod h4
theorem measurable_shapeGaugeAct :
    Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
      shapeGaugeAct Y σ r.1 r.2 := by
  have hg : Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
      blockConstantGauge R.params.side r.1 :=
    measurable_pi_lambda _ fun z => (measurable_pi_apply _).comp measurable_fst
  have ha : Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
      fun z => r.2.1 ((shapeLabelEquiv Y σ).symm z) :=
    measurable_pi_lambda _ fun z => (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_lambda _ fun x => ?_
    exact (measurable_pi_apply _).comp ((R.labels.act_borel (shapeLabelSites Y σ)).comp (hg.prodMk ha))
  · refine measurable_pi_lambda _ fun c => ?_
    have h1 : Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
        blockConstantGauge R.params.side r.1 (storedBondSite Y σ c) :=
      (measurable_pi_apply (parentBlock R.params.side (storedBondSite Y σ c))).comp measurable_fst
    have h2 : Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
        blockConstantGauge R.params.side r.1 (storedBondSite Y σ c + unitStep (n * R.params.side) c.2.1.2) :=
      (measurable_pi_apply
        (parentBlock R.params.side (storedBondSite Y σ c + unitStep (n * R.params.side) c.2.1.2))).comp
        measurable_fst
    have h3 : Measurable fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
        r.2.2 c :=
      (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    exact (h1.mul h3).mul h2.inv
end Shapes
section Merge
theorem measurePreserving_overwrite {ι X : Type} [Fintype ι] [MeasurableSpace X] (S : Finset ι)
    [DecidablePred (· ∈ S)] (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (p : (S → X) × (ι → X)) i => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 i)
      ((Measure.pi fun _ : S => μ).prod (Measure.pi fun _ : ι => μ)) (Measure.pi fun _ : ι => μ) := by
  classical
  have hm : Measurable (fun (p : (S → X) × (ι → X)) i => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 i) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ S
    · simp only [h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  refine ⟨hm, (Measure.pi_eq (μ := fun _ : ι => μ) fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (p : (S → X) × (ι → X)) i => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 i) ⁻¹' Set.pi univ s =
      (Set.pi univ fun i : S => s i) ×ˢ (Set.pi univ fun i => if i ∈ S then univ else s i) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h i
        simpa [i.2] using this
      · by_cases hi : i ∈ S
        · simp [hi]
        · have := h i
          simpa [hi] using this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · simpa [hi] using h1 ⟨i, hi⟩
      · have := h2 i
        simpa [hi] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Finset.prod_coe_sort S fun i => μ (s i)]
  rw [← Finset.prod_sdiff (Finset.subset_univ S),
    ← Finset.prod_sdiff (Finset.subset_univ S) (f := fun i => μ (s i))]
  have h1 : ∏ i ∈ S, μ (if i ∈ S then univ else s i) = 1 :=
    Finset.prod_eq_one fun i hi => by simp [hi]
  have h2 : ∏ i ∈ Finset.univ \ S, μ (if i ∈ S then univ else s i) = ∏ i ∈ Finset.univ \ S, μ (s i) :=
    Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]
  rw [h1, h2, mul_one, mul_comm]
theorem measurePreserving_union {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (U A : Finset ι) (hA : A ⊆ U)
    [DecidablePred (· ∈ A)] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (fun (p : (A → X) × ((U \ A : Finset ι) → X)) (z : U) =>
        if h : (z : ι) ∈ A then p.1 ⟨z, h⟩ else p.2 ⟨z, Finset.mem_sdiff.mpr ⟨z.2, h⟩⟩)
      ((Measure.pi fun _ : A => μ).prod (Measure.pi fun _ : (U \ A : Finset ι) => μ))
      (Measure.pi fun _ : U => μ) := by
  have hm : Measurable (fun (p : (A → X) × ((U \ A : Finset ι) → X)) (z : U) =>
      if h : (z : ι) ∈ A then p.1 ⟨z, h⟩ else p.2 ⟨z, Finset.mem_sdiff.mpr ⟨z.2, h⟩⟩) := by
    refine measurable_pi_lambda _ fun z => ?_
    by_cases h : (z : ι) ∈ A
    · simp only [h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  refine ⟨hm, (Measure.pi_eq (μ := fun _ : U => μ) fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (p : (A → X) × ((U \ A : Finset ι) → X)) (z : U) =>
      if h : (z : ι) ∈ A then p.1 ⟨z, h⟩ else p.2 ⟨z, Finset.mem_sdiff.mpr ⟨z.2, h⟩⟩) ⁻¹' Set.pi univ s =
      (Set.pi univ fun i : A => s ⟨i, hA i.2⟩) ×ˢ
        (Set.pi univ fun i : (U \ A : Finset ι) => s ⟨i, (Finset.mem_sdiff.mp i.2).1⟩) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h ⟨i, hA i.2⟩
        simpa [i.2] using this
      · have := h ⟨i, (Finset.mem_sdiff.mp i.2).1⟩
        simpa [(Finset.mem_sdiff.mp i.2).2] using this
    · rintro ⟨h1, h2⟩ z
      by_cases hi : (z : ι) ∈ A
      · simpa [hi] using h1 ⟨z, hi⟩
      · simpa [hi] using h2 ⟨z, Finset.mem_sdiff.mpr ⟨z.2, hi⟩⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  let f : ι → ENNReal := fun i => if h : i ∈ U then μ (s ⟨i, h⟩) else 1
  have e1 : ∏ i : A, μ (s ⟨i, hA i.2⟩) = ∏ i ∈ A, f i := by
    rw [← Finset.prod_coe_sort A f]
    exact Finset.prod_congr rfl fun i _ => by simp [f, hA i.2]
  have e2 : ∏ i : (U \ A : Finset ι), μ (s ⟨i, (Finset.mem_sdiff.mp i.2).1⟩) = ∏ i ∈ U \ A, f i := by
    rw [← Finset.prod_coe_sort (U \ A) f]
    exact Finset.prod_congr rfl fun i _ => by simp [f, (Finset.mem_sdiff.mp i.2).1]
  have e3 : ∏ z : U, μ (s z) = ∏ i ∈ U, f i := by
    rw [← Finset.prod_coe_sort U f]
    exact Finset.prod_congr rfl fun z _ => by simp [f, z.2]
  rw [e1, e2, e3, ← Finset.prod_sdiff hA, mul_comm]
def bondHaar (n : ℕ) [NeZero n] : Measure (TorusBond n → UnitQuaternion) :=
  Measure.pi fun _ : TorusBond n => haarUnit
theorem map_uncurry_fieldHaar :
    (fieldHaar n).map (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).symm = bondHaar n := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.measurable _)
    (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun x : TorusSite n => Set.univ.pi fun i : Fin 4 => s (x, i) := by
    ext W
    simp [Set.mem_pi, Prod.forall, MeasurableEquiv.coe_curry_symm]
  rw [e]
  unfold fieldHaar
  rw [Measure.pi_pi _ _]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]
theorem measurePreserving_uncurry_fieldHaar :
    MeasurePreserving (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).symm (fieldHaar n)
      (bondHaar n) :=
  ⟨MeasurableEquiv.measurable _, map_uncurry_fieldHaar⟩
open Classical in
theorem measurePreserving_field_overwrite (S : Finset (TorusBond n)) :
    MeasurePreserving (fun (p : (S → UnitQuaternion) × TorusField n) x i =>
        if h : (x, i) ∈ S then p.1 ⟨(x, i), h⟩ else p.2 x i)
      ((Measure.pi fun _ : S => haarUnit).prod (fieldHaar n)) (fieldHaar n) := by
  have h1 := measurePreserving_uncurry_fieldHaar (n := n)
  have h2 := measurePreserving_overwrite S (haarUnit : Measure UnitQuaternion)
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : S => (haarUnit : Measure UnitQuaternion))).prod h1
  exact (h1.symm.comp (h2.comp h3))
open Classical in
def overwriteBonds {m : ℕ} (S : Finset (TorusBond m)) (p : (S → UnitQuaternion) × TorusField m) :
    TorusField m :=
  fun x i => if h : (x, i) ∈ S then p.1 ⟨(x, i), h⟩ else p.2 x i
theorem measurePreserving_overwriteBonds {m : ℕ} [NeZero m] (S : Finset (TorusBond m)) :
    MeasurePreserving (overwriteBonds S) ((Measure.pi fun _ : S => haarUnit).prod (fieldHaar m))
      (fieldHaar m) :=
  measurePreserving_field_overwrite S
def joinOnSubset {ι X : Type} [DecidableEq ι] (U A : Finset ι) (p : (A → X) × ((U \ A : Finset ι) → X)) :
    U → X :=
  fun z => if h : (z : ι) ∈ A then p.1 ⟨z, h⟩ else p.2 ⟨z, Finset.mem_sdiff.mpr ⟨z.2, h⟩⟩
theorem measurePreserving_joinOnSubset {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (U A : Finset ι)
    (hA : A ⊆ U) (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (joinOnSubset U A) ((Measure.pi fun _ : A => μ).prod
      (Measure.pi fun _ : (U \ A : Finset ι) => μ)) (Measure.pi fun _ : U => μ) :=
  measurePreserving_union U A hA μ
theorem measurable_lintegral_joint {X₁ X₂ Wd Bd Ud : Type} [MeasurableSpace X₁] [MeasurableSpace X₂]
    [MeasurableSpace Wd] [MeasurableSpace Bd] [MeasurableSpace Ud] (mW : Measure Wd) (mB : Measure Bd)
    [SFinite mW] [SFinite mB]
    {fm : X₂ × Wd → Wd} {um : X₁ × Bd → Ud} (hf : Measurable fm) (hu : Measurable um) {G : Wd → Ud → ENNReal}
    (hG : Measurable fun p : Wd × Ud => G p.1 p.2) :
    Measurable fun r : X₁ × X₂ => ∫⁻ W, ∫⁻ ν, G (fm (r.2, W)) (um (r.1, ν)) ∂mB ∂mW := by
  have hM : Measurable fun x : ((X₁ × X₂) × Wd) × Bd => G (fm (x.1.1.2, x.1.2)) (um (x.1.1.1, x.2)) :=
    hG.comp ((hf.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst))).prodMk
      (hu.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))
  exact hM.lintegral_prod_right'.lintegral_prod_right'
theorem lintegral_joint {X₁ X₂ Wd Bd Ud : Type} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Wd]
    [MeasurableSpace Bd] [MeasurableSpace Ud] {m₁ : Measure X₁} {m₂ : Measure X₂} {mW : Measure Wd}
    {mB : Measure Bd} {mU : Measure Ud} [SFinite m₁] [SFinite m₂] [SFinite mW] [SFinite mB] [SFinite mU]
    {fm : X₂ × Wd → Wd} {um : X₁ × Bd → Ud} (hf : MeasurePreserving fm (m₂.prod mW) mW)
    (hu : MeasurePreserving um (m₁.prod mB) mU) {G : Wd → Ud → ENNReal}
    (hG : Measurable fun p : Wd × Ud => G p.1 p.2) :
    ∫⁻ r : X₁ × X₂, ∫⁻ W, ∫⁻ ν, G (fm (r.2, W)) (um (r.1, ν)) ∂mB ∂mW ∂(m₁.prod m₂) =
      ∫⁻ W, ∫⁻ u, G W u ∂mU ∂mW := by
  have hK : Measurable fun x : (X₁ × Wd) × Bd => G x.1.2 (um (x.1.1, x.2)) :=
    hG.comp ((measurable_snd.comp measurable_fst).prodMk
      (hu.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hL : Measurable fun x : X₁ × Wd => ∫⁻ ν, G x.2 (um (x.1, ν)) ∂mB := hK.lintegral_prod_right'
  have e1 : ∀ W, ∫⁻ u, G W u ∂mU = ∫⁻ a, ∫⁻ ν, G W (um (a, ν)) ∂mB ∂m₁ := by
    intro W
    have hGW : Measurable (G W) := hG.comp (measurable_const.prodMk measurable_id)
    rw [← hu.lintegral_comp hGW]
    exact lintegral_prod _ (hGW.comp hu.measurable).aemeasurable
  simp_rw [e1]
  rw [lintegral_lintegral_swap (f := fun W a => ∫⁻ ν, G W (um (a, ν)) ∂mB) (μ := mW) (ν := m₁)
    (by exact (hL.comp measurable_swap).aemeasurable)]
  have e2 : ∀ a, ∫⁻ W, ∫⁻ ν, G W (um (a, ν)) ∂mB ∂mW =
      ∫⁻ g, ∫⁻ W, ∫⁻ ν, G (fm (g, W)) (um (a, ν)) ∂mB ∂mW ∂m₂ := by
    intro a
    have hLa : Measurable fun W => ∫⁻ ν, G W (um (a, ν)) ∂mB :=
      hL.comp (measurable_const.prodMk measurable_id)
    rw [← hf.lintegral_comp hLa]
    exact lintegral_prod _ (hLa.comp hf.measurable).aemeasurable
  simp_rw [e2]
  rw [lintegral_prod]
  have hM : Measurable fun x : ((X₁ × X₂) × Wd) × Bd => G (fm (x.1.1.2, x.1.2)) (um (x.1.1.1, x.2)) :=
    hG.comp ((hf.measurable.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst))).prodMk
      (hu.measurable.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))
  exact hM.lintegral_prod_right'.lintegral_prod_right'.aemeasurable
end Merge
section Fields
variable (Y : Finset (TorusSite n)) (σ : Y → Option (BlockShape R.params.side))
theorem linkValue_of_labelOfShape {L : ℕ} {Ω : Type} (sh : Option (BlockShape L))
    (pr : (storedOffsets sh → Ω) × (storedBonds sh → UnitQuaternion))
    (s : BlockLabels Ω L) (h : labelOfShape sh pr = Sum.inr s) (c : BlockBond L) :
    s.linkValue c = open Classical in
      if h : c ∈ storedBonds sh then Sum.inr (pr.2 ⟨c, h⟩) else Sum.inl () := by
  classical
  rcases sh with ⟨⟩ | sh
  · cases h
  · have h1 : markOfShape sh pr.1 pr.2 = s := Sum.inr_injective h
    subst h1
    by_cases hc : c ∈ storedBonds (some sh)
    · rw [dif_pos hc]
      exact dif_pos (show c ∈ sh.2.2.2.2 from hc)
    · rw [dif_neg hc]
      exact dif_neg (show c ∉ sh.2.2.2.2 from hc)
open Classical in
def shapeLinkBonds : Finset (TorusBond (n * R.params.side)) :=
  Finset.univ.filter fun b =>
    ∃ y : Y, parentBlock R.params.side b.1 = y ∧ (siteOffset b.1, b.2) ∈ storedBonds (σ y)
def shapeLinkBond (x : Σ y : Y, storedBonds (σ y)) : shapeLinkBonds Y σ :=
  ⟨(blockSite (x.1 : TorusSite n) x.2.1.1, x.2.1.2), by
      classical
      simp only [shapeLinkBonds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x.1, parentBlock_blockSite _ _, by rw [siteOffset_blockSite]; exact x.2.2⟩⟩
noncomputable def shapeLinkEquiv : (Σ y : Y, storedBonds (σ y)) ≃ shapeLinkBonds Y σ :=
  Equiv.ofBijective (shapeLinkBond Y σ)
    (by
     refine ⟨?_, ?_⟩
     · rintro ⟨y, o⟩ ⟨y', o'⟩ h
       have h0 := congrArg Subtype.val h
       have h1 : blockSite (y : TorusSite n) o.1.1 = blockSite (y' : TorusSite n) o'.1.1 := congrArg Prod.fst h0
       have h2 : o.1.2 = o'.1.2 := congrArg (fun b : TorusBond (n * R.params.side) => b.2) h0
       have hy : y = y' := Subtype.ext (by
         have := congrArg (parentBlock R.params.side) h1
         rwa [parentBlock_blockSite, parentBlock_blockSite] at this)
       subst hy
       have ho : o = o' := Subtype.ext (Prod.ext (by
         have := congrArg siteOffset h1
         rwa [siteOffset_blockSite, siteOffset_blockSite] at this) h2)
       subst ho
       rfl
     · classical
       rintro ⟨z, hz⟩
       have hz' := hz
       simp only [shapeLinkBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
       obtain ⟨y, hy, hm⟩ := hz'
       refine ⟨⟨y, ⟨(siteOffset z.1, z.2), hm⟩⟩, Subtype.ext ?_⟩
       show (blockSite (y : TorusSite n) (siteOffset z.1), z.2) = z
       rw [← hy, blockSite_parentBlock_siteOffset])
open Classical in
theorem fieldWithStoredLinks_shapeState (p : ShapeLabelData R.labels.Ω σ × ShapeLinkData σ)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    (shapeState Y σ p).fieldWithStoredLinks W x i =
      if h : (x, i) ∈ shapeLinkBonds Y σ then p.2 ((shapeLinkEquiv Y σ).symm ⟨(x, i), h⟩) else W x i := by
  have hno : ∀ y : Y, parentBlock R.params.side x = y → (siteOffset x, i) ∉ storedBonds (σ y) →
      (x, i) ∉ shapeLinkBonds Y σ := by
    intro y hy hm hb
    simp only [shapeLinkBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨y', hy', hm'⟩ := hb
    have : y = y' := Subtype.ext (hy.symm.trans hy')
    subst this
    exact hm hm'
  by_cases hy : parentBlock R.params.side x ∈ Y
  · rcases labelOfShape_cases (σ ⟨_, hy⟩) (fun o => p.1 ⟨⟨_, hy⟩, o⟩, fun c => p.2 ⟨⟨_, hy⟩, c⟩) with
      ⟨h1, h2⟩ | ⟨s, h1, h2⟩
    · have hs := markAt_of_inl (q := shapeState Y σ p) hy h2
      have hn := hno ⟨_, hy⟩ rfl (by rw [h1]; simp [storedBonds])
      rw [dif_neg hn]
      simp only [CoarseState.fieldWithStoredLinks, hs]
    · have hs := markAt_of_inr (q := shapeState Y σ p) hy h1
      have hf := linkValue_of_labelOfShape _ _ s h1 (siteOffset x, i)
      simp only [CoarseState.fieldWithStoredLinks, hs]
      by_cases hc : (siteOffset x, i) ∈ storedBonds (σ ⟨_, hy⟩)
      · rw [dif_pos hc] at hf
        have hb : (x, i) ∈ shapeLinkBonds Y σ := by
          simp only [shapeLinkBonds, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨_, hy⟩, rfl, hc⟩
        rw [dif_pos hb, hf]
        have he : (shapeLinkEquiv Y σ).symm ⟨(x, i), hb⟩ = ⟨⟨_, hy⟩, ⟨(siteOffset x, i), hc⟩⟩ := by
          rw [Equiv.symm_apply_eq]
          refine Subtype.ext ?_
          show (x, i) = (blockSite (parentBlock R.params.side x) (siteOffset x), i)
          rw [blockSite_parentBlock_siteOffset]
        rw [he]
      · rw [dif_neg hc] at hf
        rw [dif_neg (hno ⟨_, hy⟩ rfl hc), hf]
  · have hs := markAt_of_not_mem (q := shapeState Y σ p) hy
    have hn : (x, i) ∉ shapeLinkBonds Y σ := by
      intro hb
      simp only [shapeLinkBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨y', hy', hm'⟩ := hb
      exact hy (hy' ▸ y'.2)
    rw [dif_neg hn]
    simp only [CoarseState.fieldWithStoredLinks, hs]
theorem unlabelled_eq_sdiff (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    q.unlabelled Yt = Yt \ q.labelSet := by
  classical
  ext z
  simp only [CoarseState.unlabelled, Finset.mem_filter, Finset.mem_sdiff, mem_labelSet, not_not]
theorem fillLabels_of_mem (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (ν : q.unlabelled Yt → R.labels.Ω)
    (z : TorusSite (n * R.params.side)) (hz : z ∈ Yt) (h : z ∈ q.labelSet) :
    q.fillLabels Yt ν ⟨z, hz⟩ = q.labeling ⟨z, h⟩ := by
  have h1 := labelAt_eq_inr_labeling q ⟨z, h⟩
  unfold CoarseState.fillLabels
  split
  · rename_i a ha
    simp only at h1
    simp only at ha
    rw [ha] at h1
    exact Sum.inr_injective h1
  · rename_i u hu
    exact absurd hu (mem_labelSet.mp h)
theorem fillLabels_of_mem_unlabelled (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (ν : q.unlabelled Yt → R.labels.Ω)
    (z : TorusSite (n * R.params.side)) (hz : z ∈ Yt) (h : z ∈ q.unlabelled Yt) :
    q.fillLabels Yt ν ⟨z, hz⟩ = ν ⟨z, h⟩ := by
  classical
  have h1 : q.labelAt z = Sum.inl () := (Finset.mem_filter.mp h).2
  unfold CoarseState.fillLabels
  split
  · rename_i a ha
    simp only at ha
    rw [h1] at ha
    cases ha
  · rfl
theorem lintegral_pi_congr_finset {ι α : Type} [MeasurableSpace α] (μ : Measure α) {S S' : Finset ι}
    (h : S = S') (f : (S → α) → ENNReal) (f' : (S' → α) → ENNReal)
    (hf : ∀ ν ν', (∀ z hz hz', ν ⟨z, hz⟩ = ν' ⟨z, hz'⟩) → f ν = f' ν') :
    ∫⁻ ν, f ν ∂(Measure.pi fun _ : S => μ) = ∫⁻ ν, f' ν ∂(Measure.pi fun _ : S' => μ) := by
  subst h
  exact lintegral_congr fun ν => hf ν ν fun _ _ _ => rfl
end Fields
end ClusterExpansionOfAStep
end YangMills.Construction
end
