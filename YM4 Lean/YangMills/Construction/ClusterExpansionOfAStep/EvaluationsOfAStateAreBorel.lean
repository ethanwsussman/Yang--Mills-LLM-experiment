import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace StateMeasurability
open BlockAverages LumpContours TorusFields TorusLumps StepSettings
theorem measurable_of_countable_cover {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i)) (hcover : ∀ a, ∃ i, a ∈ S i) {f : α → β}
    (hf : ∀ i, Measurable fun x : S i => f x) : Measurable f := by
  intro t ht
  have e : f ⁻¹' t = ⋃ i, Subtype.val '' ((fun x : S i => f x) ⁻¹' t) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi⟩ := hcover a
      exact Set.mem_iUnion.mpr ⟨i, ⟨a, hi⟩, ha, rfl⟩
    · intro ha
      obtain ⟨i, ⟨b, hb⟩, hb', rfl⟩ := Set.mem_iUnion.mp ha
      exact hb'
  rw [e]
  exact MeasurableSet.iUnion fun i => (hS i).subtype_image (hf i ht)
section StateObservables
variable {Ω : Type} [MeasurableSpace Ω] {L : ℕ}
theorem measurable_blockConfig_toProd : Measurable (BlockLabels.toProd : BlockLabels Ω L → _) :=
  comap_measurable _
theorem measurable_isCore : Measurable fun s : BlockLabels Ω L => s.isCore :=
  measurable_fst.comp measurable_blockConfig_toProd
theorem measurable_badBond (b : BlockBond L) : Measurable fun s : BlockLabels Ω L => s.badBond b :=
  (measurable_pi_apply b).comp (measurable_fst.comp (measurable_snd.comp measurable_blockConfig_toProd))
theorem measurable_siteLabel (o : BlockOffset L) : Measurable fun s : BlockLabels Ω L => s.siteLabel o :=
  (measurable_pi_apply o).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_blockConfig_toProd)))
theorem measurable_basePoint : Measurable fun s : BlockLabels Ω L => s.basePoint :=
  measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_blockConfig_toProd)))
theorem measurable_linkValue (b : BlockBond L) : Measurable fun s : BlockLabels Ω L => s.linkValue b :=
  (measurable_pi_apply b).comp
    (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_blockConfig_toProd))))
def getOrDefault {α : Type} (m : WithNone α) (d : α) : α := Sum.elim (fun _ => d) id m
theorem measurable_getOrDefault {α : Type} [MeasurableSpace α] :
    Measurable fun p : WithNone α × α => getOrDefault p.1 p.2 := by
  intro t ht
  have e : (fun p : WithNone α × α => getOrDefault p.1 p.2) ⁻¹' t =
      (Set.range (Sum.inl : Unit → WithNone α) ×ˢ t) ∪ ((Sum.inr '' t) ×ˢ Set.univ) := by
    ext ⟨m, d⟩
    rcases m with u | a
    · simp [getOrDefault]
    · simp [getOrDefault]
  rw [e]
  exact (measurableSet_range_inl.prod ht).union (ht.inr_image.prod MeasurableSet.univ)
theorem measurable_withNone_isRight {α : Type} [MeasurableSpace α] :
    Measurable fun m : WithNone α => m.isRight := by
  have e : (fun m : WithNone α => m.isRight) = Sum.elim (fun _ => false) (fun _ => true) := by
    funext m
    rcases m with u | a <;> rfl
  rw [e]
  exact measurable_const.sumElim measurable_const
def storedLink (ℓ : CoarseLabel Ω L) (b : BlockBond L) : WithNone UnitQuaternion :=
  Sum.elim (fun _ => Sum.inl ()) (fun s => s.linkValue b) ℓ
def storedSiteLabel (ℓ : CoarseLabel Ω L) (o : BlockOffset L) : WithNone Ω :=
  Sum.elim (fun _ => Sum.inl ()) (fun s => s.siteLabel o) ℓ
theorem measurable_storedLink (b : BlockBond L) :
    Measurable fun ℓ : CoarseLabel Ω L => storedLink ℓ b :=
  measurable_const.sumElim (measurable_linkValue b)
theorem measurable_storedSiteLabel (o : BlockOffset L) :
    Measurable fun ℓ : CoarseLabel Ω L => storedSiteLabel ℓ o :=
  measurable_const.sumElim (measurable_siteLabel o)
abbrev CoarseStateShape (L : ℕ) : Type :=
  Unit ⊕ (Bool × (BlockBond L → Bool) × (BlockOffset L → Bool) × BlockOffset L × (BlockBond L → Bool))
def markShape (ℓ : CoarseLabel Ω L) : CoarseStateShape L :=
  Sum.elim (fun _ => Sum.inl ())
    (fun s => Sum.inr (s.isCore, s.badBond, (fun o => (s.siteLabel o).isRight), s.basePoint,
      fun b => (s.linkValue b).isRight)) ℓ
theorem measurableSet_configShape (v : CoarseStateShape L) :
    MeasurableSet {ℓ : CoarseLabel Ω L | markShape ℓ = v} := by
  rcases v with u | ⟨a, b, c, d, e⟩
  · have : {ℓ : CoarseLabel Ω L | markShape ℓ = Sum.inl u} = Set.range Sum.inl := by
      ext ℓ
      rcases ℓ with u' | s
      · simp [markShape]
      · simp [markShape]
    rw [this]
    exact measurableSet_range_inl
  · have : {ℓ : CoarseLabel Ω L | markShape ℓ = Sum.inr (a, b, c, d, e)} = Sum.inr ''
        ({s : BlockLabels Ω L | s.isCore = a} ∩ (⋂ k, {s : BlockLabels Ω L | s.badBond k = b k}) ∩
          (⋂ o, {s : BlockLabels Ω L | (s.siteLabel o).isRight = c o}) ∩
          {s : BlockLabels Ω L | s.basePoint = d} ∩
          ⋂ k, {s : BlockLabels Ω L | (s.linkValue k).isRight = e k}) := by
      ext ℓ
      rcases ℓ with u' | s
      · simp [markShape]
      · simp only [markShape, Sum.elim_inr, Set.mem_setOf_eq, Sum.inr.injEq, Prod.mk.injEq,
          Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, funext_iff]
        constructor
        · rintro ⟨h1, h2, h3, h4, h5⟩
          exact ⟨s, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, rfl⟩
        · rintro ⟨s', ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
          subst h6
          exact ⟨h1, h2, h3, h4, h5⟩
    rw [this]
    refine MeasurableSet.inr_image ?_
    refine ((((measurable_isCore (measurableSet_singleton a)).inter
      (MeasurableSet.iInter fun k => measurable_badBond k (measurableSet_singleton (b k)))).inter
      (MeasurableSet.iInter fun o => ?_)).inter (measurable_basePoint (measurableSet_singleton d))).inter
      (MeasurableSet.iInter fun k => ?_)
    · exact (measurable_withNone_isRight.comp (measurable_siteLabel o)) (measurableSet_singleton (c o))
    · exact (measurable_withNone_isRight.comp (measurable_linkValue k)) (measurableSet_singleton (e k))
end StateObservables
section StateEvaluations
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def coarseLabelAt (q : CoarseState R n) (y : TorusSite n) : CoarseLabel R.labels.Ω R.params.side :=
  if h : y ∈ q.1 then q.2 ⟨y, h⟩ else Sum.inl ()
theorem markAt_eq_elim (q : CoarseState R n) (y : TorusSite n) :
    q.markAt y = Sum.elim (fun _ => none) some (coarseLabelAt q y) := by
  classical
  unfold CoarseState.markAt coarseLabelAt
  by_cases h : y ∈ q.1
  · simp only [dif_pos h]
    rcases q.2 ⟨y, h⟩ with u | s <;> rfl
  · simp only [dif_neg h]
    rfl
theorem measurable_coarseLabelAt (Y : Finset (TorusSite n)) (y : TorusSite n) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      coarseLabelAt (⟨Y, ω⟩ : CoarseState R n) y := by
  classical
  unfold coarseLabelAt
  by_cases h : y ∈ Y
  · simp only [dif_pos h]
    exact measurable_pi_apply (⟨y, h⟩ : Y)
  · simp only [dif_neg h]
    exact measurable_const
theorem fieldWithStoredLinks_eq (q : CoarseState R n) (W : TorusField (n * R.params.side))
    (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    q.fieldWithStoredLinks W x i =
      getOrDefault (storedLink (coarseLabelAt q (parentBlock R.params.side x)) (siteOffset x, i)) (W x i) := by
  unfold CoarseState.fieldWithStoredLinks
  rw [markAt_eq_elim]
  rcases coarseLabelAt q (parentBlock R.params.side x) with u | s
  · rfl
  · simp only [Sum.elim_inr, storedLink]
    rcases s.linkValue (siteOffset x, i) with u | g <;> rfl
theorem labelAt_eq_storedSiteLabel (q : CoarseState R n) (z : TorusSite (n * R.params.side)) :
    q.labelAt z = storedSiteLabel (coarseLabelAt q (parentBlock R.params.side z)) (siteOffset z) := by
  unfold CoarseState.labelAt
  rw [markAt_eq_elim]
  rcases coarseLabelAt q (parentBlock R.params.side z) with u | s <;> rfl
theorem measurable_fieldWithStoredLinks (Y : Finset (TorusSite n)) :
    Measurable fun p : (Y → CoarseLabel R.labels.Ω R.params.side) × TorusField (n * R.params.side) =>
      CoarseState.fieldWithStoredLinks (⟨Y, p.1⟩ : CoarseState R n) p.2 := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => ?_
  simp only [fieldWithStoredLinks_eq]
  have h1 : Measurable fun p : (Y → CoarseLabel R.labels.Ω R.params.side) × TorusField (n * R.params.side) =>
      storedLink (coarseLabelAt (⟨Y, p.1⟩ : CoarseState R n) (parentBlock R.params.side x)) (siteOffset x, i) :=
    (measurable_storedLink _).comp ((measurable_coarseLabelAt Y _).comp measurable_fst)
  have h2 : Measurable fun p : (Y → CoarseLabel R.labels.Ω R.params.side) × TorusField (n * R.params.side) =>
      p.2 x i :=
    (measurable_pi_apply i).comp ((measurable_pi_apply x).comp measurable_snd)
  exact measurable_getOrDefault.comp (h1.prodMk h2)
theorem measurable_storedField (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      CoarseState.storedField (⟨Y, ω⟩ : CoarseState R n) :=
  (measurable_fieldWithStoredLinks Y).comp (measurable_id.prodMk measurable_const)
theorem measurable_labelAt (Y : Finset (TorusSite n)) (z : TorusSite (n * R.params.side)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      CoarseState.labelAt (⟨Y, ω⟩ : CoarseState R n) z := by
  simp only [labelAt_eq_storedSiteLabel]
  exact (measurable_storedSiteLabel _).comp (measurable_coarseLabelAt Y _)
structure ShapeEquivalent (q q' : CoarseState R n) : Prop where
  support_eq : q.1 = q'.1
  shape_eq : ∀ y, markShape (coarseLabelAt q y) = markShape (coarseLabelAt q' y)
theorem markAt_shape {q q' : CoarseState R n} (h : ShapeEquivalent q q') (y : TorusSite n) :
    (q.markAt y = none ∧ q'.markAt y = none) ∨ ∃ s s', q.markAt y = some s ∧ q'.markAt y = some s' ∧
      s.isCore = s'.isCore ∧ s.badBond = s'.badBond ∧
      (∀ o, (s.siteLabel o).isRight = (s'.siteLabel o).isRight) ∧ s.basePoint = s'.basePoint ∧
      ∀ b, (s.linkValue b).isRight = (s'.linkValue b).isRight := by
  have hs := h.shape_eq y
  rw [markAt_eq_elim, markAt_eq_elim]
  rcases hq : coarseLabelAt q y with u | s <;> rcases hq' : coarseLabelAt q' y with u' | s'
  · left
    simp
  · rw [hq, hq'] at hs
    simp [markShape] at hs
  · rw [hq, hq'] at hs
    simp [markShape] at hs
  · right
    rw [hq, hq'] at hs
    simp only [markShape, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq] at hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs
    exact ⟨s, s', rfl, rfl, h1, h2, fun o => congrFun h3 o, h4, fun b => congrFun h5 b⟩
theorem markedZone_eq {q q' : CoarseState R n} (h : ShapeEquivalent q q') : q.markedZone = q'.markedZone := by
  classical
  unfold CoarseState.markedZone
  rw [h.support_eq]
  refine Finset.filter_congr fun y _ => ?_
  rcases markAt_shape h y with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _⟩ <;> simp [h1, h2]
theorem storedBadBonds_eq {q q' : CoarseState R n} (h : ShapeEquivalent q q') :
    q.storedBadBonds = q'.storedBadBonds := by
  classical
  unfold CoarseState.storedBadBonds
  refine Finset.filter_congr fun b _ => ?_
  rcases markAt_shape h (parentBlock R.params.side b.1) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, h3, _⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]
theorem storedFieldBonds_eq {q q' : CoarseState R n} (h : ShapeEquivalent q q') :
    q.storedFieldBonds = q'.storedFieldBonds := by
  classical
  unfold CoarseState.storedFieldBonds
  refine Finset.filter_congr fun b _ => ?_
  rcases markAt_shape h (parentBlock R.params.side b.1) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, _, h3⟩
  · simp [h1, h2]
  · simp only [h1, h2, Option.some.injEq, exists_eq_left']
    have h4 := h3 (siteOffset b.1, b.2)
    rcases hf : s.linkValue (siteOffset b.1, b.2) with u | g <;>
      rcases hf' : s'.linkValue (siteOffset b.1, b.2) with u' | g'
    · simp
    · rw [hf, hf'] at h4
      simp at h4
    · rw [hf, hf'] at h4
      simp at h4
    · simp
theorem labelAt_isRight_eq {q q' : CoarseState R n} (h : ShapeEquivalent q q')
    (z : TorusSite (n * R.params.side)) :
    (q.labelAt z).isRight = (q'.labelAt z).isRight := by
  unfold CoarseState.labelAt
  rcases markAt_shape h (parentBlock R.params.side z) with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, h3, _⟩
  · simp [h1, h2]
  · simp [h1, h2, h3]
theorem labelSet_eq {q q' : CoarseState R n} (h : ShapeEquivalent q q') : q.labelSet = q'.labelSet := by
  classical
  unfold CoarseState.labelSet
  refine Finset.filter_congr fun z _ => ?_
  have h1 := labelAt_isRight_eq h z
  rcases hq : q.labelAt z with u | a <;> rcases hq' : q'.labelAt z with u' | a'
  · simp
  · rw [hq, hq'] at h1
    simp at h1
  · rw [hq, hq'] at h1
    simp at h1
  · simp
end StateEvaluations
end StateMeasurability
end YangMills.Construction
end
