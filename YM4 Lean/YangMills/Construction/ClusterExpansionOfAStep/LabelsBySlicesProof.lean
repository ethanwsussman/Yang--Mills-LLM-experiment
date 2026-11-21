import YangMills.Construction.ClusterExpansionOfAStep.LabelsBySlices
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusLumps TorusFields
namespace SlicedLabels
open scoped Classical
variable {ι α : Type} [MeasurableSpace α]
lemma measurable_fillOn (A : Finset ι) : Measurable (fillOn (α := α) A) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ A
  · simp only [fillOn, h, dite_true]
    exact measurable_inr.comp (measurable_pi_apply _)
  · simp only [fillOn, h, dite_false]
    exact measurable_const
lemma withNoneMeasure_apply (μ : Measure α) {s : Set (WithNone α)} (hs : MeasurableSet s) :
    withNoneMeasure μ s = μ (Sum.inr ⁻¹' s) + (if Sum.inl () ∈ s then 1 else 0) := by
  unfold withNoneMeasure
  rw [Measure.add_apply, Measure.map_apply measurable_inl hs, Measure.map_apply measurable_inr hs,
    add_comm]
  congr 1
  rw [Measure.dirac_apply' _ (measurable_inl hs)]
  by_cases h : Sum.inl () ∈ s <;> simp [h]
instance sigmaFinite_withNoneMeasure (μ : Measure α) [SigmaFinite μ] :
    SigmaFinite (withNoneMeasure μ) := by
  unfold withNoneMeasure
  have h1 : SigmaFinite (Measure.map (Sum.inr : α → WithNone α) μ) :=
    (show MeasurableEmbedding (Sum.inr : α → WithNone α) from ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩).sigmaFinite_map
  have h2 : SigmaFinite (Measure.map (Sum.inl : Unit → WithNone α) (Measure.dirac ())) :=
    (show MeasurableEmbedding (Sum.inl : Unit → WithNone α) from ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩).sigmaFinite_map
  infer_instance
theorem pi_withNoneMeasure_eq_sum [Fintype ι] (μ : Measure α) [SigmaFinite μ] :
    Measure.pi (fun _ : ι => withNoneMeasure μ) =
      ∑ A : Finset ι, Measure.map (fillOn A) (Measure.pi fun _ : A => μ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.finsetSum_apply]
  have hpi : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  have key : ∀ A : Finset ι, Measure.map (fillOn A) (Measure.pi fun _ : A => μ) (Set.pi Set.univ s) =
      (∏ i ∈ A, μ (Sum.inr ⁻¹' s i)) * ∏ i ∈ Finset.univ \ A, (if Sum.inl () ∈ s i then 1 else 0) := by
    intro A
    rw [Measure.map_apply (measurable_fillOn A) hpi]
    by_cases hA : ∀ i ∉ A, Sum.inl () ∈ s i
    · have : fillOn A ⁻¹' Set.pi Set.univ s = Set.pi Set.univ fun a : A => Sum.inr ⁻¹' s a := by
        ext ν
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
        constructor
        · intro h a
          have := h a
          simpa [fillOn, a.2] using this
        · intro h i
          by_cases hi : i ∈ A
          · simpa [fillOn, hi] using h ⟨i, hi⟩
          · simpa [fillOn, hi] using hA i hi
      rw [this, Measure.pi_pi, Finset.prod_coe_sort A (fun i => μ (Sum.inr ⁻¹' s i))]
      rw [Finset.prod_eq_one (s := Finset.univ \ A), mul_one]
      intro i hi
      simp [hA i (by simpa using hi)]
    · push Not at hA
      obtain ⟨i, hi, hs'⟩ := hA
      have : fillOn A ⁻¹' Set.pi Set.univ s = ∅ := by
        ext ν
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_empty_iff_false,
          iff_false, not_forall]
        exact ⟨i, by simpa [fillOn, hi] using hs'⟩
      rw [this, measure_empty, Finset.prod_eq_zero (s := Finset.univ \ A) (i := i) (by simpa using hi) (by simp [hs']), mul_zero]
  simp_rw [key, withNoneMeasure_apply μ (hs _)]
  rw [Finset.prod_add, Finset.powerset_univ]
section Tools
open Set in
theorem pi_pi_eq_map_curry {ι κ β : Type} [Fintype ι] [Fintype κ] [MeasurableSpace β] (m : Measure β) [SigmaFinite m] :
    Measure.pi (fun _ : ι => Measure.pi fun _ : κ => m) =
      Measure.map (fun (f : ι × κ → β) (i : ι) (j : κ) => f (i, j)) (Measure.pi fun _ : ι × κ => m) := by
  have hmeas : Measurable (fun (f : ι × κ → β) (i : ι) (j : κ) => f (i, j)) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine Measure.pi_eq_generateFrom
    (C := fun _ => Set.pi univ '' Set.pi univ fun _ : κ => {s : Set β | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => m.toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hts using hs
  have ht' : ∀ i j, MeasurableSet (t i j) := fun i j => ht i j (mem_univ _)
  have hpre : (fun (f : ι × κ → β) (i : ι) (j : κ) => f (i, j)) ⁻¹' (Set.pi univ s) =
      Set.pi univ fun p : ι × κ => t p.1 p.2 := by
    ext f
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, ← hts, Prod.forall]
  have hms : MeasurableSet (Set.pi univ s) := by
    refine MeasurableSet.univ_pi fun i => ?_
    rw [← hts]
    exact MeasurableSet.univ_pi (ht' i)
  rw [Measure.map_apply hmeas hms, hpre, Measure.pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hts, Measure.pi_pi]
theorem lintegral_prod_le_iterated {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] (f : α × β → ENNReal) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [lintegral]
  refine iSup₂_le fun g hg => ?_
  rw [← SimpleFunc.lintegral_eq_lintegral, lintegral_prod _ g.measurable.aemeasurable]
  exact lintegral_mono fun x => lintegral_mono fun y => hg _
end Tools
section Slices
variable {Z β : Type} [Fintype Z]
theorem lintegral_pi_prod_le {α β' : Type} [MeasurableSpace α] [MeasurableSpace β'] (μ : Measure α)
    (ν : Measure β') [SigmaFinite μ] [SigmaFinite ν] (f : (Z → α × β') → ENNReal) :
    ∫⁻ z, f z ∂(Measure.pi fun _ : Z => μ.prod ν) ≤
      ∫⁻ x, ∫⁻ y, f (fun i => (x i, y i)) ∂(Measure.pi fun _ : Z => ν) ∂(Measure.pi fun _ : Z => μ) := by
  have h := (measurePreserving_arrowProdEquivProdArrow α β' Z (fun _ => μ) (fun _ => ν)).symm
  rw [← h.map_eq]
  refine (lintegral_map_le _ _).trans ?_
  exact lintegral_prod_le_iterated _ _ _
theorem lintegral_prod_le_iterated_swap {α β' : Type} [MeasurableSpace α] [MeasurableSpace β'] (μ : Measure α)
    (ν : Measure β') [SFinite μ] [SFinite ν] (f : α × β' → ENNReal) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← Measure.prod_swap (μ := ν) (ν := μ)]
  refine (lintegral_map_le _ _).trans ?_
  exact lintegral_prod_le_iterated _ _ _
theorem lintegral_pi_count_le [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (f : (Z → β) → ENNReal) (c : ENNReal) (h : ∀ x, f x ≤ c) :
    ∫⁻ x, f x ∂(Measure.pi fun _ : Z => (Measure.count : Measure β)) ≤
      ((Fintype.card β ^ Fintype.card Z : ℕ) : ENNReal) * c := by
  rw [lintegral_fintype]
  calc ∑ x, f x * (Measure.pi fun _ : Z => (Measure.count : Measure β)) {x}
      ≤ ∑ _x : Z → β, c := Finset.sum_le_sum fun x _ => by
        rw [Measure.pi_singleton]
        simpa using h x
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, ]
theorem lintegral_pi_pi_withNone_le {κ α : Type} [Fintype κ] [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (f : (Z → κ → WithNone α) → ENNReal) (c : ENNReal)
    (h : ∀ A : Finset (Z × κ), ∫⁻ ν : A → α, f (fun i j => fillOn A ν (i, j)) ∂(Measure.pi fun _ : A => μ) ≤ c) :
    ∫⁻ x, f x ∂(Measure.pi fun _ : Z => Measure.pi fun _ : κ => withNoneMeasure μ) ≤
      ((2 ^ (Fintype.card Z * Fintype.card κ) : ℕ) : ENNReal) * c := by
  rw [pi_pi_eq_map_curry]
  refine (lintegral_map_le _ _).trans ?_
  rw [pi_withNoneMeasure_eq_sum, lintegral_finsetSum_measure]
  calc ∑ A : Finset (Z × κ), ∫⁻ x, f (fun i j => x (i, j)) ∂Measure.map (fillOn A) (Measure.pi fun _ : A => μ)
      ≤ ∑ _A : Finset (Z × κ), c := Finset.sum_le_sum fun A _ =>
        (lintegral_map_le _ _).trans (h A)
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_prod]
end Slices
section Main
theorem lintegral_pi_prod_le_swap {Z α β' : Type} [Fintype Z] [MeasurableSpace α] [MeasurableSpace β']
    (μ : Measure α) (ν : Measure β') [SigmaFinite μ] [SigmaFinite ν] (f : (Z → α × β') → ENNReal) :
    ∫⁻ z, f z ∂(Measure.pi fun _ : Z => μ.prod ν) ≤
      ∫⁻ y, ∫⁻ x, f (fun i => (x i, y i)) ∂(Measure.pi fun _ : Z => μ) ∂(Measure.pi fun _ : Z => ν) := by
  have h := (measurePreserving_arrowProdEquivProdArrow α β' Z (fun _ => μ) (fun _ => ν)).symm
  rw [← h.map_eq]
  refine (lintegral_map_le _ _).trans ?_
  exact lintegral_prod_le_iterated_swap _ _ _
variable {ι Ω G O Q B : Type} [Fintype ι] [Fintype O] [Fintype Q] [Nonempty O]
  [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace O] [MeasurableSingletonClass O]
  [MeasurableSpace Q] [MeasurableSpace B]
def blockTupleMeasure (μ : Measure Ω) (γ : Measure G) (O Q : Type) [Fintype O] [Fintype Q] [MeasurableSpace O] :
    Measure (Bool × (Q → Bool) × (O → WithNone Ω) × O × (Q → WithNone G)) :=
  (Measure.count : Measure Bool).prod ((Measure.count : Measure (Q → Bool)).prod
    ((Measure.pi fun _ : O => withNoneMeasure μ).prod ((Measure.count : Measure O).prod
      (Measure.pi fun _ : Q => withNoneMeasure γ))))
def discreteDataCount (O Q : Type) [Fintype O] [Fintype Q] : ℕ :=
  2 * (2 ^ Fintype.card Q * (Fintype.card O * (2 ^ Fintype.card Q * 2 ^ Fintype.card O)))
theorem lintegral_blockTuple_le (μ : Measure Ω) [SigmaFinite μ] (γ : Measure G) [IsProbabilityMeasure γ]
    {Z : Type} [Fintype Z]
    (H : (Z → Bool × (Q → Bool) × (O → WithNone Ω) × O × (Q → WithNone G)) → ENNReal) (c : ENNReal)
    (h : ∀ (a : Z → Bool) (bb : Z → Q → Bool) (o : Z → O) (A : Finset (Z × O)) (Bs : Finset (Z × Q))
      (g : Bs → G), ∫⁻ ω : A → Ω,
        H (fun y => (a y, bb y, (fun k => fillOn A ω (y, k)), o y, (fun q => fillOn Bs g (y, q))))
          ∂(Measure.pi fun _ : A => μ) ≤ c) :
    ∫⁻ x, H x ∂(Measure.pi fun _ : Z => blockTupleMeasure μ γ O Q) ≤
      ((discreteDataCount O Q ^ Fintype.card Z : ℕ) : ENNReal) * c := by
  classical
  unfold blockTupleMeasure
  have s3 : ∀ (a : Z → Bool) (bb : Z → Q → Bool) (o : Z → O),
      ∫⁻ y, ∫⁻ x, H (fun i => (a i, bb i, x i, o i, y i))
        ∂(Measure.pi fun _ : Z => Measure.pi fun _ : O => withNoneMeasure μ)
        ∂(Measure.pi fun _ : Z => Measure.pi fun _ : Q => withNoneMeasure γ) ≤
      ((2 ^ (Fintype.card Z * Fintype.card Q) : ℕ) : ENNReal) *
        (((2 ^ (Fintype.card Z * Fintype.card O) : ℕ) : ENNReal) * c) := by
    intro a bb o
    refine lintegral_pi_pi_withNone_le γ _ _ fun Bs => ?_
    have : ∀ g : Bs → G, ∫⁻ x, H (fun i => (a i, bb i, x i, o i, fun j => fillOn Bs g (i, j)))
        ∂(Measure.pi fun _ : Z => Measure.pi fun _ : O => withNoneMeasure μ) ≤
        ((2 ^ (Fintype.card Z * Fintype.card O) : ℕ) : ENNReal) * c :=
      fun g => lintegral_pi_pi_withNone_le μ _ c fun A => h a bb o A Bs g
    refine (lintegral_mono this).trans ?_
    simp
  have s2 : ∀ (a : Z → Bool) (bb : Z → Q → Bool),
      ∫⁻ y, H (fun i => (a i, bb i, y i)) ∂(Measure.pi fun _ : Z =>
        (Measure.pi fun _ : O => withNoneMeasure μ).prod ((Measure.count : Measure O).prod
          (Measure.pi fun _ : Q => withNoneMeasure γ))) ≤
      ((Fintype.card O ^ Fintype.card Z : ℕ) : ENNReal) *
        (((2 ^ (Fintype.card Z * Fintype.card Q) : ℕ) : ENNReal) *
          (((2 ^ (Fintype.card Z * Fintype.card O) : ℕ) : ENNReal) * c)) := fun a bb =>
    (lintegral_pi_prod_le_swap _ _ _).trans ((lintegral_pi_prod_le _ _ _).trans
      (lintegral_pi_count_le _ _ (s3 a bb)))
  have s1 : ∀ a : Z → Bool,
      ∫⁻ y, H (fun i => (a i, y i)) ∂(Measure.pi fun _ : Z =>
        (Measure.count : Measure (Q → Bool)).prod
          ((Measure.pi fun _ : O => withNoneMeasure μ).prod ((Measure.count : Measure O).prod
            (Measure.pi fun _ : Q => withNoneMeasure γ)))) ≤
      ((Fintype.card (Q → Bool) ^ Fintype.card Z : ℕ) : ENNReal) *
        (((Fintype.card O ^ Fintype.card Z : ℕ) : ENNReal) *
        (((2 ^ (Fintype.card Z * Fintype.card Q) : ℕ) : ENNReal) *
          (((2 ^ (Fintype.card Z * Fintype.card O) : ℕ) : ENNReal) * c))) := fun a =>
    (lintegral_pi_prod_le _ _ _).trans (lintegral_pi_count_le _ _ (s2 a))
  refine (lintegral_pi_prod_le _ _ _).trans ((lintegral_pi_count_le _ _ s1).trans (le_of_eq ?_))
  simp only [discreteDataCount, Fintype.card_bool, Fintype.card_fun]
  push_cast
  rw [pow_mul' (2 : ENNReal) (Fintype.card Z) (Fintype.card Q),
    pow_mul' (2 : ENNReal) (Fintype.card Z) (Fintype.card O)]
  simp only [mul_pow]
  simp only [mul_assoc]
end Main
section Outer
variable {ι Ω G O Q B : Type} [Fintype ι] [Fintype O] [Fintype Q] [Nonempty O]
  [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace O] [MeasurableSingletonClass O]
  [MeasurableSpace Q] [MeasurableSpace B]
theorem lintegral_pi_withNone_map_le (μ : Measure Ω) [SigmaFinite μ] (γ : Measure G) [IsProbabilityMeasure γ]
    (mk : Bool × (Q → Bool) × (O → WithNone Ω) × O × (Q → WithNone G) → B) (hmk : MeasurableEmbedding mk)
    (F : (ι → WithNone B) → ENNReal) (c : ENNReal)
    (h : ∀ (Z : Finset ι) (a : Z → Bool) (bb : Z → Q → Bool) (o : Z → O) (A : Finset (Z × O))
      (Bs : Finset (Z × Q)) (g : Bs → G), ∫⁻ ω : A → Ω,
        F (fillOn Z fun y => mk (a y, bb y, (fun k => fillOn A ω (y, k)), o y,
          (fun q => fillOn Bs g (y, q)))) ∂(Measure.pi fun _ : A => μ) ≤ c) :
    ∫⁻ ν, F ν ∂(Measure.pi fun _ : ι => withNoneMeasure (Measure.map mk (blockTupleMeasure μ γ O Q))) ≤
      (((2 * discreteDataCount O Q) ^ Fintype.card ι : ℕ) : ENNReal) * c := by
  classical
  haveI hs : SigmaFinite (blockTupleMeasure μ γ O Q) := by unfold blockTupleMeasure; infer_instance
  haveI : SigmaFinite (Measure.map mk (blockTupleMeasure μ γ O Q)) := hmk.sigmaFinite_map
  rw [pi_withNoneMeasure_eq_sum, lintegral_finsetSum_measure]
  have hone : 1 ≤ discreteDataCount O Q := by
    have : 0 < Fintype.card O := Fintype.card_pos
    exact show 0 < discreteDataCount O Q from by unfold discreteDataCount; positivity
  have term : ∀ Z : Finset ι, ∫⁻ ν, F ν ∂Measure.map (fillOn Z)
      (Measure.pi fun _ : Z => Measure.map mk (blockTupleMeasure μ γ O Q)) ≤
      ((discreteDataCount O Q ^ Fintype.card ι : ℕ) : ENNReal) * c := by
    intro Z
    refine (lintegral_map_le _ _).trans ?_
    rw [← Measure.pi_map_pi (fun _ => hmk.measurable.aemeasurable)]
    refine (lintegral_map_le _ _).trans ?_
    refine (lintegral_blockTuple_le μ γ (fun x => F (fillOn Z fun y => mk (x y))) c fun a bb o A Bs g => h Z a bb o A Bs g).trans ?_
    gcongr
    simpa using Finset.card_le_univ Z
  refine (Finset.sum_le_sum fun Z _ => term Z).trans (le_of_eq ?_)
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_finset, mul_pow, mul_assoc]
end Outer
theorem measurableEmbedding_ofProd (Ω : Type) [MeasurableSpace Ω] (L : ℕ) :
    MeasurableEmbedding (BlockLabels.ofProd (Ω := Ω) (L := L)) := by
  have hinv : ∀ p, (BlockLabels.ofProd (Ω := Ω) (L := L) p).toProd = p := fun _ => rfl
  refine ⟨fun p p' h => ?_, ?_, fun s hs => ?_⟩
  · rw [← hinv p, ← hinv p', h]
  · rw [measurable_iff_comap_le]
    refine MeasurableSpace.comap_le_iff_le_map.mpr ?_
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have : BlockLabels.ofProd ⁻¹' (BlockLabels.toProd ⁻¹' t) = t := by
      ext p
      simp [hinv]
    exact this ▸ ht
  · refine ⟨s, hs, ?_⟩
    ext b
    constructor
    · intro h
      exact ⟨b.toProd, h, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [hinv] using hp
theorem sliceBound : SliceBoundStatement := by
  intro Ω _ μ _ L _ ι _ F c h
  have hfin : Nonempty (BlockOffset L) := inferInstance
  have := lintegral_pi_withNone_map_le (ι := ι) (Ω := Ω) (G := UnitQuaternion) (O := BlockOffset L) (Q := BlockBond L) μ haarUnit
    BlockLabels.ofProd (measurableEmbedding_ofProd Ω L) F c (fun Z a bb o A Bs g => h Z a bb o A Bs g)
  refine (le_of_eq ?_).trans (this.trans (le_of_eq ?_))
  · rfl
  · simp [discreteDataCount, blockDataCount]
end SlicedLabels
end YangMills.Construction
