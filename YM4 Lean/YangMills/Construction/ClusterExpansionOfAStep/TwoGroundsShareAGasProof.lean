import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBox
import YangMills.Construction.ClusterExpansionOfAStep.InnerSupportsWithTheirCores
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfSharedCores
import YangMills.Construction.ClusterExpansionOfAStep.TwoGroundsShareAGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps
theorem measurePreserving_subtype_of_equiv {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) {P : α → Prop} {Q : β → Prop} (hPQ : ∀ a, P a ↔ Q (f a)) :
    ∃ g : {a // P a} ≃ᵐ {b // Q b}, (∀ a, (g a : β) = f a) ∧
      MeasurePreserving g (μ.comap Subtype.val) (ν.comap Subtype.val) := by
  classical
  let g : {a // P a} ≃ᵐ {b // Q b} :=
    { toFun := fun a => ⟨f a, (hPQ a).1 a.2⟩
      invFun := fun b => ⟨f.symm b, (hPQ _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      measurable_toFun := (f.measurable.comp measurable_subtype_coe).subtype_mk
      measurable_invFun := (f.symm.measurable.comp measurable_subtype_coe).subtype_mk }
  refine ⟨g, fun _ => rfl, g.measurable, ?_⟩
  have hsymm : MeasurePreserving f.symm ν μ := hf.symm f
  have himg : ∀ t : Set {b // Q b}, (Subtype.val '' t : Set β) = f '' (Subtype.val '' (g ⁻¹' t)) := by
    intro t
    ext b
    constructor
    · rintro ⟨b', hb', rfl⟩
      refine ⟨(g.symm b' : α), ⟨g.symm b', ?_, rfl⟩, ?_⟩
      · simpa using hb'
      · exact (congrArg Subtype.val (g.apply_symm_apply b'))
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨g a, ha, rfl⟩
  have himg' : ∀ s : Set {a // P a}, (Subtype.val '' s : Set α) = f.symm '' (Subtype.val '' (g.symm ⁻¹' s)) := by
    intro s
    ext a
    constructor
    · rintro ⟨a', ha', rfl⟩
      refine ⟨(g a' : β), ⟨g a', ?_, rfl⟩, ?_⟩
      · simpa using ha'
      · exact (congrArg Subtype.val (g.symm_apply_apply a'))
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨g.symm b, hb, rfl⟩
  have hnull : ∀ s : Set α, NullMeasurableSet s μ → NullMeasurableSet (f '' s) ν := by
    intro s hs
    rw [f.image_eq_preimage_symm]
    exact hs.preimage hsymm.quasiMeasurePreserving
  have hnull' : ∀ s : Set β, NullMeasurableSet s ν → NullMeasurableSet (f.symm '' s) μ := by
    intro s hs
    rw [f.symm.image_eq_preimage_symm]
    exact hs.preimage hf.quasiMeasurePreserving
  by_cases h : Function.Injective (Subtype.val : {a // P a} → α) ∧
      ∀ s : Set {a // P a}, MeasurableSet s → NullMeasurableSet (Subtype.val '' s : Set α) μ
  · have h' : Function.Injective (Subtype.val : {b // Q b} → β) ∧
        ∀ t : Set {b // Q b}, MeasurableSet t → NullMeasurableSet (Subtype.val '' t : Set β) ν := by
      refine ⟨Subtype.val_injective, fun t ht => ?_⟩
      rw [himg t]
      exact hnull _ (h.2 _ (g.measurable ht))
    ext t ht
    rw [Measure.map_apply g.measurable ht, Measure.comap_apply₀ _ _ h.1 h.2 (g.measurable ht).nullMeasurableSet,
      Measure.comap_apply₀ _ _ h'.1 h'.2 ht.nullMeasurableSet, himg t, ← hf.measure_preimage_equiv,
      f.preimage_image]
  · have h' : ¬ (Function.Injective (Subtype.val : {b // Q b} → β) ∧
        ∀ t : Set {b // Q b}, MeasurableSet t → NullMeasurableSet (Subtype.val '' t : Set β) ν) := by
      rintro ⟨_, h2⟩
      refine h ⟨Subtype.val_injective, fun s hs => ?_⟩
      rw [himg' s]
      exact hnull' _ (h2 _ (g.symm.measurable hs))
    rw [Measure.comap, dif_neg h, Measure.comap, dif_neg h', Measure.map_zero]
theorem measurePreserving_withDensity_of_equiv {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) {a : α → ENNReal} {b : β → ENNReal} (hab : ∀ x, a x = b (g x)) :
    MeasurePreserving g (μ.withDensity a) (ν.withDensity b) := by
  refine ⟨g.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply g.measurable ht, withDensity_apply _ (g.measurable ht), withDensity_apply _ ht,
    ← hg.setLIntegral_comp_preimage_emb g.measurableEmbedding]
  exact setLIntegral_congr_fun (g.measurable ht) fun x _ => hab x
theorem measurePreserving_withNone_of_equiv {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∃ v : WithNone α ≃ᵐ WithNone β, v (Sum.inl ()) = Sum.inl () ∧ (∀ a, v (Sum.inr a) = Sum.inr (g a)) ∧
      MeasurePreserving v (withNoneMeasure μ) (withNoneMeasure ν) := by
  refine ⟨MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit) g, rfl, fun _ => rfl, ?_⟩
  refine ⟨MeasurableEquiv.measurable _, ?_⟩
  unfold withNoneMeasure
  rw [Measure.map_add _ _ (MeasurableEquiv.measurable _), Measure.map_map (MeasurableEquiv.measurable _) measurable_inl,
    Measure.map_map (MeasurableEquiv.measurable _) measurable_inr]
  have e1 : (MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit) g : WithNone α → WithNone β) ∘ Sum.inl = Sum.inl := rfl
  have e2 : (MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit) g : WithNone α → WithNone β) ∘ Sum.inr =
      Sum.inr ∘ g := rfl
  rw [e1, e2, ← Measure.map_map measurable_inr g.measurable, hg.map_eq]
theorem groundsShareInnerGas_of_correspondences (hS : InnerSupportsCorrespondWithCores)
    (hSt : SharedCoreStatesEquiv) (hA : AllowedStatesTransferInBox) : GroundsShareInnerGas := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ => ?_⟩
  obtain ⟨y₁, h₁⟩ := hS T hT
  obtain ⟨y₂, h₂⟩ := hA T hT
  refine ⟨max y₁ (max y₂ T.floorMin), fun y hy R hR hx n n' _ _ G G' Y Y' N A A' hG hG' hN hag hbl => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₂, a₃⟩ := max_le_iff.mp hy
  have hodd : Odd R.params.side := by
    have : R.params.Admissible := by
      rw [hR.params_eq]
      exact hT.fits y a₃
    exact this.L_odd
  obtain ⟨e, he⟩ := h₁ y a₁ R hR n n' G G' Y Y' N A A' hN hag hbl
  have hf := fun j : G.InnerSpin Y (N - R.frameReach - 1) A =>
    hSt R n n' j.1.1 (e j).1.1 Y Y' N hodd hag.lt_extent hag.lt_extent' (he j).1 (he j).2.1
  choose f hfm hfs using hf
  have hag' : GroundsAgreeNear G' G Y' Y N :=
    ⟨hag.lt_extent', hag.lt_extent, fun b hb => (hag.coarse_agree b hb).symm, fun a ha => (hag.cut_iff a ha).symm,
      fun a ha => (hag.marking_eq a ha).symm⟩
  have hal := fun (j : G.InnerSpin Y (N - R.frameReach - 1) A) (s : SupportState j.1.1) =>
    h₂ y a₂ R hR hx n n' G G' Y Y' N j.1 (e j).1 s (f j s) hG hG' hN hag j.2.core_near (e j).2.core_near
      (he j).1 (he j).2.1 (hfs j s)
  have hal' := fun (j : G.InnerSpin Y (N - R.frameReach - 1) A) (s : SupportState j.1.1) =>
    h₂ y a₂ R hR hx n' n G' G Y' Y N (e j).1 j.1 (f j s) s hG' hG hN hag' (e j).2.core_near j.2.core_near
      ⟨(he j).1.core_mem', (he j).1.core_mem, fun q hq => ((he j).1.bad_iff q hq).symm,
        fun a o ha ho => ((he j).1.sites_iff a o ha ho).symm⟩
      (fun a ha => ((he j).2.1 a ha).symm)
      ⟨fun q hb hb' hq => ((hfs j s).field_eq q hb' hb hq).symm,
        fun a o hz hz' ha ho => ((hfs j s).label_eq a o hz' hz ha ho).symm,
        fun a hy hy' ha => ((hfs j s).base_eq a hy' hy ha).symm⟩
  have hg := fun j : G.InnerSpin Y (N - R.frameReach - 1) A =>
    measurePreserving_subtype_of_equiv (P := G.IsAllowed j.1.1) (Q := G'.IsAllowed (e j).1.1) (f j) (hfm j)
      (fun s => ⟨fun h => (hal j s h).1, fun h => (hal' j s h).1⟩)
  choose g hgv hgm using hg
  have hd : ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
      MeasurePreserving (g j) (G.spinStateMeasure j.1) (G'.spinStateMeasure (e j).1) := by
    intro j
    refine measurePreserving_withDensity_of_equiv (g j) (hgm j) fun s => ?_
    show ENNReal.ofReal (G.activity j.1.1 s.1) = ENNReal.ofReal (G'.activity (e j).1.1 (g j s).1)
    rw [hgv j s, (hal j s.1 s.2).2]
  have hv := fun j : G.InnerSpin Y (N - R.frameReach - 1) A => measurePreserving_withNone_of_equiv (g j) (hd j)
  choose v hvl hvr hvm using hv
  exact ⟨{ spinEquiv := e
           valueEquiv := v
           sameSupport := fun j => (he j).1
           meets_iff := fun j => (he j).2.2.1
           unitCount_eq := fun j => (he j).2.2.2.1
           map_vacant := hvl
           map_occupied := fun j s => ⟨g j s, hvr j s, by rw [hgv j s]; exact hfs j s.1⟩
           farApart_iff := fun j j' h => (he j).2.2.2.2 j' h
           measurePreserving := hvm }⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
