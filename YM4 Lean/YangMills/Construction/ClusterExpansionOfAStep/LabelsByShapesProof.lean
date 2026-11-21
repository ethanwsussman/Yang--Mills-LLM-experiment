import YangMills.Construction.ClusterExpansionOfAStep.LabelsByShapes
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXiProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.TorusLumps
section PiSigma
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] {X : ∀ i, κ i → Type*}
  [∀ i j, MeasurableSpace (X i j)] (μ : ∀ i j, Measure (X i j)) [∀ i j, SigmaFinite (μ i j)]
theorem measurePreserving_piSigmaCurry :
    MeasurePreserving (fun (f : ∀ p : Σ i, κ i, X p.1 p.2) i j => f ⟨i, j⟩)
      (Measure.pi fun p : Σ i, κ i => μ p.1 p.2) (Measure.pi fun i => Measure.pi (μ i)) := by
  have hmeas : Measurable (fun (f : ∀ p : Σ i, κ i, X p.1 p.2) i j => f ⟨i, j⟩) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi univ '' Set.pi univ fun j => {s : Set (X i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hts using hs
  have hset : MeasurableSet (Set.pi univ s) := by
    refine MeasurableSet.univ_pi fun i => ?_
    rw [← hts i]
    exact MeasurableSet.univ_pi fun j => ht i j (mem_univ j)
  rw [Measure.map_apply hmeas hset]
  have hpre : (fun (f : ∀ p : Σ i, κ i, X p.1 p.2) i j => f ⟨i, j⟩) ⁻¹' Set.pi univ s =
      Set.pi univ fun p : Σ i, κ i => t p.1 p.2 := by
    ext f
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h p
      have := h p.1
      rw [← hts p.1] at this
      exact this p.2 (mem_univ _)
    · intro h i
      rw [← hts i]
      intro j _
      exact h ⟨i, j⟩
  rw [hpre, Measure.pi_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hts i, Measure.pi_pi]
end PiSigma
section PiProd
variable {ι : Type*} [Fintype ι] {A B : ι → Type*} [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
  (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
theorem measurePreserving_piProdSplit :
    MeasurePreserving (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i))
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi fun i => (μ i).prod (ν i)) := by
  have hmeas : Measurable (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) :=
    measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.image2 (· ×ˢ ·) {s : Set (A i) | MeasurableSet s} {t : Set (B i) | MeasurableSet t})
    (fun i => generateFrom_prod) (fun i => isPiSystem_prod)
    (fun i => (μ i).toFiniteSpanningSetsIn.prod (ν i).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose a ha b hb hab using hs
  have hset : MeasurableSet (Set.pi univ s) := by
    refine MeasurableSet.univ_pi fun i => ?_
    rw [← hab i]
    exact (ha i).prod (hb i)
  rw [Measure.map_apply hmeas hset]
  have hpre : (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) ⁻¹' Set.pi univ s =
      Set.pi univ a ×ˢ Set.pi univ b := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h i
        rw [← hab i] at this
        exact this.1
      · have := h i
        rw [← hab i] at this
        exact this.2
    · rintro ⟨h1, h2⟩ i
      rw [← hab i]
      exact ⟨h1 i, h2 i⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hab i, Measure.prod_prod]
end PiProd
section ExtendByConst
variable {ι : Type} [Fintype ι] {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
theorem pi_eq_map_extendByConst (A : Finset ι) [DecidablePred (· ∈ A)] (e : X → Y) (he : Measurable e) (y₀ : Y)
    (μ : Measure X) [SigmaFinite μ]
    (m : ι → Measure Y) [∀ i, SigmaFinite (m i)] (hin : ∀ i ∈ A, m i = μ.map e)
    (hout : ∀ i, i ∉ A → m i = Measure.dirac y₀) :
    Measure.pi m = (Measure.pi fun _ : A => μ).map
      fun a i => if h : i ∈ A then e (a ⟨i, h⟩) else y₀ := by
  have hmeas : Measurable (fun (a : A → X) i => if h : i ∈ A then e (a ⟨i, h⟩) else y₀) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ A
    · simp only [h, dite_true]
      exact he.comp (measurable_pi_apply _)
    · simp only [h, dite_false]
      exact measurable_const
  refine Measure.pi_eq (μ := m) fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  by_cases hall : ∀ i, i ∉ A → y₀ ∈ s i
  · have hpre : (fun (a : A → X) i => if h : i ∈ A then e (a ⟨i, h⟩) else y₀) ⁻¹' Set.pi univ s =
        Set.pi univ (fun i : A => e ⁻¹' s i) := by
      ext a
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
      constructor
      · intro h i
        have := h i
        simpa [i.2] using this
      · intro h i
        by_cases hi : i ∈ A
        · simpa [hi] using h ⟨i, hi⟩
        · simpa [hi] using hall i hi
    rw [hpre, Measure.pi_pi]
    have hfactor : ∀ i, m i (s i) = if i ∈ A then μ (e ⁻¹' s i) else 1 := by
      intro i
      by_cases hi : i ∈ A
      · simp only [hi, if_true]
        rw [hin i hi, Measure.map_apply he (hs i)]
      · simp only [hi, if_false]
        rw [hout i hi, Measure.dirac_apply' _ (hs i)]
        simp [hall i hi]
    simp_rw [hfactor]
    calc ∏ i : A, μ (e ⁻¹' s i) = ∏ i ∈ A, μ (e ⁻¹' s i) := Finset.prod_coe_sort A fun i => μ (e ⁻¹' s i)
      _ = ∏ i ∈ A, (if i ∈ A then μ (e ⁻¹' s i) else 1) :=
        Finset.prod_congr rfl fun i hi => by simp [hi]
      _ = ∏ i, (if i ∈ A then μ (e ⁻¹' s i) else 1) :=
        Finset.prod_subset (Finset.subset_univ A) fun i _ hi => by simp [hi]
  · push Not at hall
    obtain ⟨i₀, hi₀, hy⟩ := hall
    have hpre : (fun (a : A → X) i => if h : i ∈ A then e (a ⟨i, h⟩) else y₀) ⁻¹' Set.pi univ s = ∅ := by
      ext a
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_empty_iff_false, iff_false]
      intro h
      have := h i₀
      simp [hi₀] at this
      exact hy this
    rw [hpre, measure_empty]
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [hout i₀ hi₀, Measure.dirac_apply' _ (hs i₀)]
    simp [hy]
end ExtendByConst
section WithNone
variable {α : Type} [MeasurableSpace α] (μ : Measure α)
theorem measurableEmbedding_sumInr {β : Type} [MeasurableSpace β] : MeasurableEmbedding (Sum.inr : α → β ⊕ α) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.mpr hs⟩
instance sigmaFinite_withNoneMeasure [SigmaFinite μ] : SigmaFinite (withNoneMeasure μ) := by
  unfold withNoneMeasure
  have : SigmaFinite (Measure.map (Sum.inr : α → Unit ⊕ α) μ) :=
    measurableEmbedding_sumInr.sigmaFinite_map
  have : IsFiniteMeasure (Measure.map (Sum.inl : Unit → Unit ⊕ α) (Measure.dirac ())) :=
    Measure.isFiniteMeasure_map _ _
  infer_instance
theorem withNoneMeasure_restrict_range_inr : (withNoneMeasure μ).restrict (range Sum.inr) = μ.map Sum.inr := by
  unfold withNoneMeasure
  have hset : MeasurableSet (range (Sum.inr : α → Unit ⊕ α)) := measurableSet_range_inr
  rw [Measure.restrict_add]
  have h1 : (Measure.map (Sum.inl : Unit → Unit ⊕ α) (Measure.dirac ())).restrict (range Sum.inr) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    rw [Measure.map_apply measurable_inl hset]
    have : (Sum.inl : Unit → Unit ⊕ α) ⁻¹' range Sum.inr = ∅ := by
      ext u
      simp
    rw [this, measure_empty]
  have h2 : (Measure.map (Sum.inr : α → Unit ⊕ α) μ).restrict (range Sum.inr) = μ.map Sum.inr := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_map_iff measurable_inr.aemeasurable (by exact hset)]
    exact Filter.Eventually.of_forall fun x => mem_range_self x
  rw [h1, h2, zero_add]
theorem withNoneMeasure_restrict_inl :
    (withNoneMeasure μ).restrict {Sum.inl ()} = Measure.dirac (Sum.inl () : WithNone α) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.withNoneMeasure_restrict_vacant <;> assumption
end WithNone
section LevelOperations
variable {Ω : Type} [MeasurableSpace Ω] {L : ℕ}
set_option linter.unusedSectionVars false
def blockConfigEquivProd : BlockLabels Ω L ≃ᵐ
    Bool × (BlockBond L → Bool) × (BlockOffset L → WithNone Ω) × BlockOffset L ×
      (BlockBond L → WithNone BlockAverages.UnitQuaternion) where
  toFun := BlockLabels.toProd
  invFun := BlockLabels.ofProd
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have : BlockLabels.ofProd ⁻¹' (BlockLabels.toProd ⁻¹' t) = t := by
      ext p
      rfl
    change MeasurableSet (BlockLabels.ofProd ⁻¹' (BlockLabels.toProd ⁻¹' t))
    rw [this]
    exact ht
open Classical in
def supportPattern {ι α : Type} (A : Finset ι) : Set (ι → WithNone α) :=
  Set.pi univ fun o => if o ∈ A then range Sum.inr else {Sum.inl ()}
open Classical in
theorem mem_supportPattern {ι α : Type} [Fintype ι] (A : Finset ι) (l : ι → WithNone α) :
    l ∈ supportPattern A ↔ Finset.univ.filter (fun o => l o ≠ Sum.inl ()) = A := by
  unfold supportPattern
  simp only [Set.mem_pi, mem_univ, forall_true_left]
  constructor
  · intro h
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ho := h o
    by_cases hA : o ∈ A
    · simp only [hA, if_true] at ho ⊢
      obtain ⟨a, ha⟩ := ho
      simp [← ha]
    · simp only [hA, if_false, mem_singleton_iff] at ho ⊢
      simp [ho]
  · rintro rfl o
    by_cases hl : l o = Sum.inl ()
    · simp [hl]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, ne_eq, not_false_eq_true, if_true]
      rcases h : l o with ⟨⟩ | a
      · exact absurd h hl
      · exact ⟨a, rfl⟩
theorem count_restrict_singleton {β : Type} [MeasurableSpace β] [MeasurableSingletonClass β] (b : β) :
    (Measure.count : Measure β).restrict {b} = Measure.dirac b := by
  rw [Measure.restrict_singleton, Measure.count_singleton, one_smul]
open Classical in
theorem pi_withNoneMeasure_restrict_supportPattern {ι α : Type} [Fintype ι] [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (A : Finset ι) [DecidablePred (· ∈ A)] :
    (Measure.pi fun _ : ι => withNoneMeasure μ).restrict (supportPattern A) =
      (Measure.pi fun _ : A => μ).map
        fun a i => if h : i ∈ A then Sum.inr (a ⟨i, h⟩) else Sum.inl () := by
  unfold supportPattern
  rw [Measure.restrict_pi_pi]
  refine pi_eq_map_extendByConst A Sum.inr measurable_inr (Sum.inl ()) μ _ (fun i hi => ?_) (fun i hi => ?_)
  · simp only [hi, if_true]
    exact withNoneMeasure_restrict_range_inr μ
  · simp only [hi, if_false]
    exact withNoneMeasure_restrict_inl μ
theorem measurable_extendByNone {ι α : Type} [MeasurableSpace α] (A : Finset ι) [DecidablePred (· ∈ A)] :
    Measurable (fun (a : A → α) i => if h : i ∈ A then (Sum.inr (a ⟨i, h⟩) : WithNone α) else Sum.inl ()) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ A
  · simp only [h, dite_true]
    exact measurable_inr.comp (measurable_pi_apply _)
  · simp only [h, dite_false]
    exact measurable_const
open Classical in
theorem ofProd_preimage_shape_eq (sh : BlockShape L) :
    BlockLabels.ofProd ⁻¹' {s : BlockLabels Ω L | s.shape = sh} =
      ({sh.1} : Set Bool) ×ˢ ({sh.2.1} : Set (BlockBond L → Bool)) ×ˢ (supportPattern sh.2.2.1) ×ˢ
        ({sh.2.2.2.1} : Set (BlockOffset L)) ×ˢ (supportPattern sh.2.2.2.2) := by
  ext p
  obtain ⟨c, β, l, o, f⟩ := p
  obtain ⟨c', β', A, o', B⟩ := sh
  simp only [mem_preimage, Set.mem_ofPred_eq, BlockLabels.shape, BlockLabels.ofProd, Set.mem_prod, mem_singleton_iff,
    mem_supportPattern, Prod.mk.injEq]
  constructor <;> rintro ⟨h1, h2, h3, h4, h5⟩ <;> refine ⟨h1, h2, h3, h4, ?_⟩ <;> convert h5
open Classical in
theorem blockConfigMeasure_restrict_shape (μ : Measure Ω) [SigmaFinite μ] (sh : BlockShape L) :
    (blockConfigMeasure μ L).restrict {s : BlockLabels Ω L | s.shape = sh} =
      ((Measure.pi fun _ : sh.2.2.1 => μ).prod
        (Measure.pi fun _ : sh.2.2.2.2 => TorusFields.haarUnit)).map
        fun p => markOfShape sh p.1 p.2 := by
  unfold blockConfigMeasure
  have he : MeasurableEmbedding (BlockLabels.ofProd (Ω := Ω) (L := L)) :=
    (blockConfigEquivProd (Ω := Ω) (L := L)).symm.measurableEmbedding
  rw [he.restrict_map, ofProd_preimage_shape_eq, ← Measure.prod_restrict, ← Measure.prod_restrict,
    ← Measure.prod_restrict, ← Measure.prod_restrict, count_restrict_singleton, count_restrict_singleton,
    count_restrict_singleton, pi_withNoneMeasure_restrict_supportPattern, pi_withNoneMeasure_restrict_supportPattern]
  have hL := measurable_extendByNone (α := Ω) sh.2.2.1
  have hF := measurable_extendByNone (α := BlockAverages.UnitQuaternion) sh.2.2.2.2
  have hof : Measurable (BlockLabels.ofProd (Ω := Ω) (L := L)) := he.measurable
  have hg1 := (measurable_prodMk_left (m := MeasurableSpace.pi) (x := sh.2.2.2.1)).comp hF
  rw [Measure.dirac_prod sh.2.2.2.1, Measure.map_map measurable_prodMk_left hF, Measure.map_prod_map _ _ hL hg1,
    Measure.dirac_prod, Measure.dirac_prod, Measure.map_map hof measurable_prodMk_left,
    Measure.map_map (hof.comp measurable_prodMk_left) measurable_prodMk_left,
    Measure.map_map ((hof.comp measurable_prodMk_left).comp measurable_prodMk_left) (hL.prodMap hg1)]
  rfl
theorem measurable_configOfShape (sh : BlockShape L) :
    Measurable (fun p : (sh.2.2.1 → Ω) × (sh.2.2.2.2 → BlockAverages.UnitQuaternion) =>
      markOfShape sh p.1 p.2) := by
  have hL := measurable_extendByNone (α := Ω) sh.2.2.1
  have hF := measurable_extendByNone (α := BlockAverages.UnitQuaternion) sh.2.2.2.2
  have hof : Measurable (BlockLabels.ofProd (Ω := Ω) (L := L)) :=
    (blockConfigEquivProd (Ω := Ω) (L := L)).symm.measurable
  have : (fun p : (sh.2.2.1 → Ω) × (sh.2.2.2.2 → BlockAverages.UnitQuaternion) => markOfShape sh p.1 p.2) =
      fun p => BlockLabels.ofProd (sh.1, sh.2.1,
        (fun i => if h : i ∈ sh.2.2.1 then Sum.inr (p.1 ⟨i, h⟩) else Sum.inl ()),
        sh.2.2.2.1, fun i => if h : i ∈ sh.2.2.2.2 then Sum.inr (p.2 ⟨i, h⟩) else Sum.inl ()) := rfl
  rw [this]
  refine hof.comp ?_
  exact measurable_const.prodMk (measurable_const.prodMk ((hL.comp measurable_fst).prodMk
    (measurable_const.prodMk (hF.comp measurable_snd))))
instance sigmaFinite_blockLabelMeasure (μ : Measure Ω) [SigmaFinite μ] :
    SigmaFinite (blockConfigMeasure μ L) := by
  unfold blockConfigMeasure
  exact (blockConfigEquivProd (Ω := Ω) (L := L)).symm.sigmaFinite_map
instance sigmaFinite_coarseLabelMeasure (μ : Measure Ω) [SigmaFinite μ] :
    SigmaFinite (coarseLabelMeasure μ L) := by
  unfold coarseLabelMeasure
  infer_instance
open Classical in
theorem labelShape_preimage_none :
    labelShape ⁻¹' {(none : Option (BlockShape L))} = ({Sum.inl ()} : Set (CoarseLabel Ω L)) := by
  ext l
  rcases l with ⟨⟩ | s
  · simp [labelShape]
  · simp [labelShape]
open Classical in
theorem labelShape_preimage_some (sh : BlockShape L) :
    labelShape ⁻¹' {some sh} = (Sum.inr '' {s : BlockLabels Ω L | s.shape = sh} : Set (CoarseLabel Ω L)) := by
  ext l
  rcases l with ⟨⟩ | s
  · simp [labelShape]
  · simp [labelShape]
theorem coarseLabelMeasure_restrict_shape (μ : Measure Ω) [SigmaFinite μ] (sh : Option (BlockShape L)) :
    (coarseLabelMeasure μ L).restrict (labelShape ⁻¹' {sh}) =
      ((Measure.pi fun _ : storedOffsets sh => μ).prod
        (Measure.pi fun _ : storedBonds sh => TorusFields.haarUnit)).map (labelOfShape sh) := by
  unfold coarseLabelMeasure
  rcases sh with ⟨⟩ | sh
  · rw [labelShape_preimage_none, withNoneMeasure_restrict_inl]
    have : labelOfShape (none : Option (BlockShape L)) =
        fun _ : (storedOffsets (none : Option (BlockShape L)) → Ω) ×
            (storedBonds (none : Option (BlockShape L)) → BlockAverages.UnitQuaternion) =>
          (Sum.inl () : CoarseLabel Ω L) := by
      funext p
      rfl
    rw [this, Measure.map_const]
    have h1 : IsEmpty (storedOffsets (none : Option (BlockShape L))) :=
      ⟨fun x => by simpa [storedOffsets] using x.2⟩
    have h2 : IsEmpty (storedBonds (none : Option (BlockShape L))) :=
      ⟨fun x => by simpa [storedBonds] using x.2⟩
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.pi_univ, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_empty, one_mul, one_smul]
  · rw [labelShape_preimage_some]
    have hsub : (Sum.inr '' {s : BlockLabels Ω L | s.shape = sh} : Set (CoarseLabel Ω L)) ⊆ range Sum.inr := by
      rintro _ ⟨s, _, rfl⟩
      exact mem_range_self s
    have h1 : (withNoneMeasure (blockConfigMeasure μ L)).restrict
          (Sum.inr '' {s : BlockLabels Ω L | s.shape = sh}) =
        ((withNoneMeasure (blockConfigMeasure μ L)).restrict (range Sum.inr)).restrict
          (Sum.inr '' {s : BlockLabels Ω L | s.shape = sh}) := by
      rw [Measure.restrict_restrict' measurableSet_range_inr, inter_eq_left.mpr hsub]
    rw [h1, withNoneMeasure_restrict_range_inr, measurableEmbedding_sumInr.restrict_map,
      Sum.inr_injective.preimage_image, blockConfigMeasure_restrict_shape,
      Measure.map_map measurable_inr (measurable_configOfShape sh)]
    rfl
end LevelOperations
section Configurations
variable {Ω : Type} [MeasurableSpace Ω] {L : ℕ} {Y : Type} [Fintype Y]
theorem measurable_labelOfShape (sh : Option (BlockShape L)) : Measurable (labelOfShape (Ω := Ω) sh) := by
  rcases sh with ⟨⟩ | sh
  · exact measurable_const
  · exact measurable_inr.comp (measurable_configOfShape sh)
theorem pi_coarseLabelMeasure_restrict_shapes (μ : Measure Ω) [SigmaFinite μ] (σ : Y → Option (BlockShape L)) :
    (Measure.pi fun _ : Y => coarseLabelMeasure μ L).restrict {ω | ∀ y, labelShape (ω y) = σ y} =
      ((Measure.pi fun _ : Σ y, storedOffsets (σ y) => μ).prod
        (Measure.pi fun _ : Σ y, storedBonds (σ y) => TorusFields.haarUnit)).map
        (labelsOfShapes σ) := by
  have hset : {ω : Y → CoarseLabel Ω L | ∀ y, labelShape (ω y) = σ y} =
      Set.pi univ fun y => labelShape ⁻¹' {σ y} := by
    ext ω
    simp
  rw [hset, Measure.restrict_pi_pi]
  simp_rw [coarseLabelMeasure_restrict_shape]
  have hsf : ∀ y, SigmaFinite (((Measure.pi fun _ : storedOffsets (σ y) => μ).prod
      (Measure.pi fun _ : storedBonds (σ y) => TorusFields.haarUnit)).map (labelOfShape (σ y))) := by
    intro y
    rw [← coarseLabelMeasure_restrict_shape]
    infer_instance
  rw [← Measure.pi_map_pi fun y => (measurable_labelOfShape (σ y)).aemeasurable]
  have hc1 := measurePreserving_piSigmaCurry (fun (y : Y) (_ : storedOffsets (σ y)) => μ)
  have hc2 := measurePreserving_piSigmaCurry (fun (y : Y) (_ : storedBonds (σ y)) =>
    (TorusFields.haarUnit : Measure BlockAverages.UnitQuaternion))
  have hsplit := measurePreserving_piProdSplit (fun y : Y => Measure.pi fun _ : storedOffsets (σ y) => μ)
    (fun y : Y => Measure.pi fun _ : storedBonds (σ y) =>
      (TorusFields.haarUnit : Measure BlockAverages.UnitQuaternion))
  have hall := hsplit.comp (hc1.prod hc2)
  have hfm : Measurable (fun (x : ∀ y, (storedOffsets (σ y) → Ω) ×
      (storedBonds (σ y) → BlockAverages.UnitQuaternion)) i => labelOfShape (σ i) (x i)) :=
    measurable_pi_lambda _ fun y => (measurable_labelOfShape (σ y)).comp (measurable_pi_apply y)
  rw [← hall.map_eq, Measure.map_map hfm hall.measurable]
  rfl
end Configurations
section StandardBorel
theorem standardBorelSpace_of_measurableEquiv {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (e : A ≃ᵐ B)
    [StandardBorelSpace B] : StandardBorelSpace A := by
  let _ := upgradeStandardBorel B
  let τ : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  have hp : PolishSpace A := e.toEquiv.polishSpace_induced
  have hb : BorelSpace A := by
    refine ⟨?_⟩
    have h1 : @borel A τ = (borel B).comap e := borel_comap
    rw [h1, ← BorelSpace.measurable_eq (α := B)]
    exact e.measurableEmbedding.comap_eq.symm
  exact ⟨⟨τ, hb, hp⟩⟩
theorem standardBorelSpace_sum_unit {α : Type} [MeasurableSpace α] [StandardBorelSpace α] :
    StandardBorelSpace (Unit ⊕ α) := by
  rcases isEmpty_or_nonempty α with he | ⟨⟨a₀⟩⟩
  · have e : (Unit ⊕ α) ≃ᵐ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => Sum.inl ()
        left_inv := by
          rintro (⟨⟩ | a)
          · rfl
          · exact he.elim a
        right_inv := fun _ => rfl
        measurable_toFun := measurable_const
        measurable_invFun := measurable_const }
    exact standardBorelSpace_of_measurableEquiv e
  · let f : Unit ⊕ α → Bool × α := fun l => match l with
      | Sum.inl _ => (false, a₀)
      | Sum.inr a => (true, a)
    have hf : Measurable f := by
      refine measurable_fun_sum ?_ ?_
      · exact measurable_const
      · exact measurable_const.prodMk measurable_id
    let S : Set (Bool × α) := {(false, a₀)} ∪ ({true} ×ˢ univ)
    have hS : MeasurableSet S :=
      (measurableSet_singleton _).union ((measurableSet_singleton _).prod MeasurableSet.univ)
    have := hS.standardBorel
    have hmem : ∀ l, f l ∈ S := by
      rintro (⟨⟩ | a)
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, mem_univ _⟩
    let e : (Unit ⊕ α) ≃ᵐ S :=
      { toFun := fun l => ⟨f l, hmem l⟩
        invFun := fun p => if p.1.1 then Sum.inr p.1.2 else Sum.inl ()
        left_inv := by
          rintro (⟨⟩ | a)
          · rfl
          · rfl
        right_inv := by
          rintro ⟨⟨b, a⟩, h⟩
          rcases h with h | ⟨h, -⟩
          · simp only [mem_singleton_iff, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
          · simp only [mem_singleton_iff] at h
            subst h
            rfl
        measurable_toFun := Measurable.subtype_mk (h := hmem) hf
        measurable_invFun := by
          have h1 : MeasurableSet {p : S | p.1.1 = true} :=
            (measurable_fst.comp measurable_subtype_coe) (measurableSet_singleton true)
          refine Measurable.ite h1 ?_ measurable_const
          exact measurable_inr.comp (measurable_snd.comp measurable_subtype_coe) }
    exact standardBorelSpace_of_measurableEquiv e
instance standardBorelSpace_unitQuaternion : StandardBorelSpace BlockAverages.UnitQuaternion := inferInstance
theorem standardBorelSpace_coarseLabel {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {L : ℕ} :
    StandardBorelSpace (CoarseLabel Ω L) := by
  have h1 : StandardBorelSpace (WithNone Ω) := standardBorelSpace_sum_unit
  have h2 : StandardBorelSpace (WithNone BlockAverages.UnitQuaternion) := standardBorelSpace_sum_unit
  have h3 : StandardBorelSpace (BlockLabels Ω L) := standardBorelSpace_of_measurableEquiv blockConfigEquivProd
  exact standardBorelSpace_sum_unit
end StandardBorel
section Shapes
variable {Ω : Type} {L : ℕ}
theorem measurableSet_labelShape_preimage [MeasurableSpace Ω] (sh : Option (BlockShape L)) :
    MeasurableSet (labelShape (Ω := Ω) ⁻¹' {sh}) := by
  rcases sh with ⟨⟩ | sh
  · rw [labelShape_preimage_none]
    have : ({Sum.inl ()} : Set (CoarseLabel Ω L)) = range Sum.inl := by
      ext u
      constructor
      · rintro rfl
        exact ⟨(), rfl⟩
      · rintro ⟨⟨⟩, rfl⟩
        rfl
    rw [this]
    exact measurableSet_range_inl
  · rw [labelShape_preimage_some]
    refine measurableSet_inr_image.mpr ?_
    have hp : ∀ {ι α : Type} [MeasurableSpace α] [Fintype ι] (A : Finset ι),
        MeasurableSet (supportPattern (α := α) A) := by
      intro ι α _ _ A
      refine MeasurableSet.univ_pi fun o => ?_
      split_ifs
      · exact measurableSet_range_inr
      · have : ({Sum.inl ()} : Set (WithNone α)) = range Sum.inl := by
          ext u
          constructor
          · rintro rfl
            exact ⟨(), rfl⟩
          · rintro ⟨⟨⟩, rfl⟩
            rfl
        rw [this]
        exact measurableSet_range_inl
    have hR := (measurableSet_singleton sh.1).prod ((measurableSet_singleton sh.2.1).prod
      ((hp (α := Ω) sh.2.2.1).prod ((measurableSet_singleton sh.2.2.2.1).prod
        (hp (α := BlockAverages.UnitQuaternion) sh.2.2.2.2))))
    rw [← ofProd_preimage_shape_eq (Ω := Ω) sh] at hR
    have : {s : BlockLabels Ω L | s.shape = sh} =
        BlockLabels.toProd ⁻¹' (BlockLabels.ofProd ⁻¹' {s : BlockLabels Ω L | s.shape = sh}) := by
      ext s
      rfl
    rw [this]
    exact (blockConfigEquivProd (Ω := Ω) (L := L)).measurable hR
theorem labelShape_labelOfShape (sh : Option (BlockShape L))
    (p : (storedOffsets sh → Ω) × (storedBonds sh → BlockAverages.UnitQuaternion)) :
    labelShape (labelOfShape sh p) = sh := by
  classical
  rcases sh with ⟨⟩ | ⟨c, β, A, o, B⟩
  · rfl
  · simp only [labelOfShape, labelShape, BlockLabels.shape, markOfShape, Option.some.injEq, Prod.mk.injEq,
      true_and]
    refine ⟨?_, ?_⟩
    · ext x
      by_cases h : x ∈ A <;> simp [h]
    · ext x
      by_cases h : x ∈ B <;> simp [h]
theorem exists_labelOfShape_eq (sh : Option (BlockShape L)) (l : CoarseLabel Ω L) (h : labelShape l = sh) :
    ∃ p, labelOfShape sh p = l := by
  classical
  subst h
  rcases l with ⟨⟩ | s
  · exact ⟨(fun x => (Finset.notMem_empty _ x.2).elim, fun x => (Finset.notMem_empty _ x.2).elim), rfl⟩
  have hlab : ∀ o : s.shape.2.2.1, ∃ v, s.siteLabel o.1 = Sum.inr v := by
    intro o
    have h1 := (Finset.mem_filter.mp o.2).2
    rcases h : s.siteLabel o.1 with ⟨⟩ | v
    · exact absurd h h1
    · exact ⟨v, rfl⟩
  have hlink : ∀ o : s.shape.2.2.2.2, ∃ v, s.linkValue o.1 = Sum.inr v := by
    intro o
    have h1 := (Finset.mem_filter.mp o.2).2
    rcases h : s.linkValue o.1 with ⟨⟩ | v
    · exact absurd h h1
    · exact ⟨v, rfl⟩
  choose a ha using hlab
  choose g hg using hlink
  refine ⟨(a, g), ?_⟩
  change Sum.inr (markOfShape s.shape a g) = Sum.inr s
  congr 1
  have hl : (markOfShape s.shape a g).siteLabel = s.siteLabel := by
    funext o
    by_cases h : o ∈ s.shape.2.2.1
    · simp only [markOfShape, dif_pos h]
      exact (ha ⟨o, h⟩).symm
    · simp only [markOfShape, dif_neg h]
      have h2 : ¬ s.siteLabel o ≠ Sum.inl () := fun h3 =>
        h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
      exact (not_not.mp h2).symm
  have hf : (markOfShape s.shape a g).linkValue = s.linkValue := by
    funext o
    by_cases h : o ∈ s.shape.2.2.2.2
    · simp only [markOfShape, dif_pos h]
      exact (hg ⟨o, h⟩).symm
    · simp only [markOfShape, dif_neg h]
      have h2 : ¬ s.linkValue o ≠ Sum.inl () := fun h3 =>
        h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
      exact (not_not.mp h2).symm
  have h1 : (markOfShape s.shape a g).isCore = s.isCore := rfl
  have h2 : (markOfShape s.shape a g).badBond = s.badBond := rfl
  have h3 : (markOfShape s.shape a g).basePoint = s.basePoint := rfl
  revert hl hf h1 h2 h3
  generalize markOfShape s.shape a g = s'
  cases s
  cases s'
  simp only [BlockLabels.mk.injEq]
  tauto
theorem labelOfShape_injective (sh : Option (BlockShape L)) :
    Function.Injective (labelOfShape (Ω := Ω) sh) := by
  classical
  rcases sh with ⟨⟩ | sh
  · intro p p' _
    refine Prod.ext (funext fun x => (Finset.notMem_empty _ x.2).elim)
      (funext fun x => (Finset.notMem_empty _ x.2).elim)
  · intro p p' h
    have h1 : markOfShape sh p.1 p.2 = markOfShape sh p'.1 p'.2 := Sum.inr_injective h
    refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
    · have h2 := congrFun (congrArg BlockLabels.siteLabel h1) x.1
      have hx : (x : BlockOffset L) ∈ sh.2.2.1 := x.2
      simp only [markOfShape] at h2
      rw [dif_pos hx, dif_pos hx] at h2
      exact Sum.inr_injective h2
    · have h2 := congrFun (congrArg BlockLabels.linkValue h1) x.1
      have hx : (x : BlockBond L) ∈ sh.2.2.2.2 := x.2
      simp only [markOfShape] at h2
      rw [dif_pos hx, dif_pos hx] at h2
      exact Sum.inr_injective h2
theorem labelsOfShapes_injective {Y : Type} (σ : Y → Option (BlockShape L)) :
    Function.Injective (labelsOfShapes (Ω := Ω) σ) := by
  intro p p' h
  refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
  · have h1 := labelOfShape_injective _ (congrFun h x.1)
    exact congrFun (congrArg Prod.fst h1) x.2
  · have h1 := labelOfShape_injective _ (congrFun h x.1)
    exact congrFun (congrArg Prod.snd h1) x.2
theorem range_labelsOfShapes {Y : Type} (σ : Y → Option (BlockShape L)) :
    range (labelsOfShapes (Ω := Ω) σ) = {ω | ∀ y, labelShape (ω y) = σ y} := by
  ext ω
  constructor
  · rintro ⟨p, rfl⟩ y
    exact labelShape_labelOfShape _ _
  · intro h
    choose p hp using fun y => exists_labelOfShape_eq (σ y) (ω y) (h y)
    exact ⟨(fun x => (p x.1).1 x.2, fun x => (p x.1).2 x.2), funext fun y => hp y⟩
end Shapes
theorem coarseLabelMeasureByShapes_holds : CoarseLabelMeasureByShapes := by
  intro Ω _ μ _ L
  refine ⟨sigmaFinite_coarseLabelMeasure μ, fun h => standardBorelSpace_coarseLabel,
    measurableSet_labelShape_preimage, fun Y _ σ => ⟨?_, labelsOfShapes_injective σ,
    range_labelsOfShapes σ, pi_coarseLabelMeasure_restrict_shapes μ σ⟩⟩
  exact measurable_pi_lambda _ fun y => (measurable_labelOfShape (σ y)).comp
    (((measurable_pi_lambda _ fun o => (measurable_pi_apply _).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ fun c => (measurable_pi_apply _).comp measurable_snd))
end YangMills.Construction.TorusLumps
end
