import YangMills.Construction.Continuum.ConnectedFunctionsCentredFunctionalsOnTheSpanAndCumulantsOfAState
import YangMills.Construction.Continuum.RecentringRespectsTheOperationsOnCombinations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Continuum.CentringRespectsOperations
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.LimitConventions (cubicMotionGroup)
open YangMills.Construction.TupleLists (get_mem_disjointSupportTuples ofList)
open YangMills.Construction.TestSpaces (c1CompactSupp cumulantOne componentCumulantOne cumulantOne_eq
  singletonSepTuple centredTuple centring centring_basisVec centringCoeff sepTuple_ext)
open YangMills.Construction.SeparatedTuples
def elementsAt (P : ℕ → Bool) : ℕ → List RealValued → List RealValued
  | _, [] => []
  | n, f :: L => if P n then f :: elementsAt P (n + 1) L else elementsAt P (n + 1) L
theorem componentsAt_sublist (P : ℕ → Bool) (n : ℕ) (L : List RealValued) :
    (elementsAt P n L).Sublist L := by
  induction L generalizing n with
  | nil => exact List.Sublist.refl _
  | cons f L ih =>
    rw [elementsAt]
    split_ifs
    · exact (ih (n + 1)).cons_cons f
    · exact (ih (n + 1)).cons f
theorem componentsAt_append (P : ℕ → Bool) (n : ℕ) (L L' : List RealValued) :
    elementsAt P n (L ++ L') = elementsAt P n L ++ elementsAt P (n + L.length) L' := by
  induction L generalizing n with
  | nil => simp [elementsAt]
  | cons f L ih =>
    have h : n + (f :: L).length = n + 1 + L.length := by simp; omega
    rw [List.cons_append, elementsAt, elementsAt, h, ih]
    split_ifs <;> simp
theorem componentsAt_shift (P Q : ℕ → Bool) (n k : ℕ) (L : List RealValued)
    (h : ∀ i, n ≤ i → P (i + k) = Q i) : elementsAt P (n + k) L = elementsAt Q n L := by
  induction L generalizing n with
  | nil => rfl
  | cons f L ih =>
    have h₁ : n + k + 1 = n + 1 + k := by omega
    rw [elementsAt, elementsAt, h n le_rfl, h₁, ih (n + 1) fun i hi => h i (by omega)]
theorem componentsAt_congr (P Q : ℕ → Bool) (n : ℕ) (L : List RealValued)
    (h : ∀ i, n ≤ i → i < n + L.length → P i = Q i) :
    elementsAt P n L = elementsAt Q n L := by
  induction L generalizing n with
  | nil => rfl
  | cons f L ih =>
    rw [elementsAt, elementsAt, h n le_rfl (by simp),
      ih (n + 1) fun i hi hi' => h i (by omega) (by simp; omega)]
theorem componentsAt_of_forall (P : ℕ → Bool) (n : ℕ) (L : List RealValued)
    (h : ∀ i, n ≤ i → i < n + L.length → P i = true) : elementsAt P n L = L := by
  induction L generalizing n with
  | nil => rfl
  | cons f L ih =>
    rw [elementsAt, if_pos (h n le_rfl (by simp)),
      ih (n + 1) fun i hi hi' => h i (by omega) (by simp; omega)]
theorem componentsAt_map (P : ℕ → Bool) (n : ℕ) (φ : RealValued → RealValued)
    (L : List RealValued) :
    elementsAt P n (L.map φ) = (elementsAt P n L).map φ := by
  induction L generalizing n with
  | nil => rfl
  | cons f L ih =>
    rw [List.map_cons, elementsAt, elementsAt, ih]
    split_ifs <;> simp
theorem filter_zipIdx_map_fst (I : Finset ℕ) (n : ℕ) (L : List RealValued) :
    ((L.zipIdx n).filter fun p => decide (p.2 ∈ I)).map Prod.fst =
      elementsAt (fun i => decide (i ∈ I)) n L := by
  induction L generalizing n with
  | nil => rfl
  | cons f L ih =>
    rw [List.zipIdx_cons, elementsAt, List.filter_cons]
    by_cases h : n ∈ I <;> simp [h, ih]
theorem sublistOn_eq_elementsAt (L : List RealValued) (I : Finset ℕ) :
    SepTuple.sublistOn L I = elementsAt (fun i => decide (i ∈ I)) 1 L :=
  filter_zipIdx_map_fst I 1 L
open Classical in
def negMeanCoeff (s : TestSpaces.SepTuple → ℝ) (f : RealValued) : ℂ :=
  if hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) then
    ((-cumulantOne s f hf : ℝ) : ℂ) else 0
theorem prod_filter_eq_prod_componentsAt (m : RealValued → ℂ) (A : Finset ℕ) (n : ℕ)
    (L : List RealValued) :
    ∏ l ∈ Finset.univ.filter (fun l : Fin L.length => (l : ℕ) + n ∉ A), m (L.get l) =
      ((elementsAt (fun i => decide (i ∉ A)) n L).map m).prod := by
  induction L generalizing n with
  | nil => simp [elementsAt]
  | cons f L ih =>
    have ih' := ih (n + 1)
    rw [Finset.prod_filter] at ih'
    rw [Finset.prod_filter]
    change ∏ l : Fin (L.length + 1), (if (l : ℕ) + n ∉ A then m ((f :: L).get l) else 1) = _
    rw [Fin.prod_univ_succ, elementsAt]
    have h₁ : ∏ l : Fin L.length, (if ((l.succ : Fin (L.length + 1)) : ℕ) + n ∉ A then
        m ((f :: L).get l.succ) else 1) =
        ((elementsAt (fun i => decide (i ∉ A)) (n + 1) L).map m).prod := by
      rw [← ih']
      refine Finset.prod_congr rfl fun l _ => ?_
      have h₂ : ((l.succ : Fin (L.length + 1)) : ℕ) + n = (l : ℕ) + (n + 1) := by
        simp only [Fin.val_succ]; omega
      rw [h₂]
      rfl
    rw [h₁]
    by_cases h : n ∈ A <;> simp [h]
theorem centringCoeff_eq_prod (s : TestSpaces.SepTuple → ℝ) (X : SepTuple) (A : Finset ℕ) :
    centringCoeff s X A =
      ((elementsAt (fun i => decide (i ∉ A)) 1 X.1).map (negMeanCoeff s)).prod := by
  rw [← prod_filter_eq_prod_componentsAt]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [negMeanCoeff, dif_pos ((get_mem_disjointSupportTuples X).1 l)]
  rfl
def mergeIndices (k : ℕ) (p : Finset ℕ × Finset ℕ) : Finset ℕ := p.1 ∪ p.2.image (· + k)
def splitIndices (k : ℕ) (C : Finset ℕ) : Finset ℕ × Finset ℕ :=
  (C.filter (· ≤ k), (C.filter (k < ·)).image (· - k))
theorem mem_mergeIndices_of_le {k i k' : ℕ} {A B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 k')
    (hi : i ≤ k) : i ∈ mergeIndices k (A, B) ↔ i ∈ A := by
  simp only [mergeIndices, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact h
    · have := (Finset.mem_Icc.1 (hB hb)).1
      omega
  · exact Or.inl
theorem add_mem_mergeIndices_iff {k i : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.Icc 1 k)
    (hi : 1 ≤ i) : i + k ∈ mergeIndices k (A, B) ↔ i ∈ B := by
  simp only [mergeIndices, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, h⟩)
    · have := (Finset.mem_Icc.1 (hA h)).2
      omega
    · have : b = i := by omega
      exact this ▸ hb
  · exact fun h => Or.inr ⟨i, h, rfl⟩
theorem mergeIndices_subset {k k' : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.Icc 1 k)
    (hB : B ⊆ Finset.Icc 1 k') : mergeIndices k (A, B) ⊆ Finset.Icc 1 (k + k') := by
  intro i hi
  simp only [mergeIndices, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with h | ⟨b, hb, rfl⟩
  · have := Finset.mem_Icc.1 (hA h)
    exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
  · have := Finset.mem_Icc.1 (hB hb)
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
theorem splitIndices_fst_subset {k k' : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.Icc 1 (k + k')) :
    (splitIndices k C).1 ⊆ Finset.Icc 1 k := by
  intro i hi
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 hi
  exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 (hC h₁)).1, h₂⟩
theorem splitIndices_snd_subset {k k' : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.Icc 1 (k + k')) :
    (splitIndices k C).2 ⊆ Finset.Icc 1 k' := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 hj
  have := Finset.mem_Icc.1 (hC h₁)
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
theorem splitIndices_mergeIndices {k k' : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.Icc 1 k)
    (hB : B ⊆ Finset.Icc 1 k') : splitIndices k (mergeIndices k (A, B)) = (A, B) := by
  refine Prod.ext ?_ ?_
  · ext i
    simp only [splitIndices, Finset.mem_filter]
    constructor
    · rintro ⟨h, hi⟩
      exact (mem_mergeIndices_of_le hB hi).1 h
    · intro h
      have hi := (Finset.mem_Icc.1 (hA h)).2
      exact ⟨(mem_mergeIndices_of_le hB hi).2 h, hi⟩
  · ext i
    simp only [splitIndices, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨h, hj⟩, rfl⟩
      have h₁ : j - k + k = j := by omega
      exact (add_mem_mergeIndices_iff hA (by omega)).1 (h₁.symm ▸ h)
    · intro h
      have hi := (Finset.mem_Icc.1 (hB h)).1
      exact ⟨i + k, ⟨(add_mem_mergeIndices_iff hA hi).2 h, by omega⟩, by omega⟩
theorem mergeIndices_splitIndices (k : ℕ) (C : Finset ℕ) :
    mergeIndices k (splitIndices k C) = C := by
  ext i
  simp only [mergeIndices, splitIndices, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨_, ⟨j, ⟨h, hj⟩, rfl⟩, rfl⟩)
    · exact h
    · have h₁ : j - k + k = j := by omega
      rwa [h₁]
  · intro h
    by_cases hi : i ≤ k
    · exact Or.inl ⟨h, hi⟩
    · exact Or.inr ⟨i - k, ⟨i, ⟨h, by omega⟩, rfl⟩, by omega⟩
theorem componentsAt_mem_mergeIndices {L L' : List RealValued} {k' : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 L.length) (hB : B ⊆ Finset.Icc 1 k') :
    elementsAt (fun i => decide (i ∈ mergeIndices L.length (A, B))) 1 (L ++ L') =
      elementsAt (fun i => decide (i ∈ A)) 1 L ++ elementsAt (fun i => decide (i ∈ B)) 1 L' := by
  rw [componentsAt_append]
  congr 1
  · refine componentsAt_congr _ _ 1 L fun i _ hi => ?_
    simp only [mem_mergeIndices_of_le hB (show i ≤ L.length by omega)]
  · refine componentsAt_shift _ _ 1 L.length L' fun i hi => ?_
    simp only [add_mem_mergeIndices_iff hA hi]
theorem componentsAt_not_mem_mergeIndices {L L' : List RealValued} {k' : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 L.length) (hB : B ⊆ Finset.Icc 1 k') :
    elementsAt (fun i => decide (i ∉ mergeIndices L.length (A, B))) 1 (L ++ L') =
      elementsAt (fun i => decide (i ∉ A)) 1 L ++
        elementsAt (fun i => decide (i ∉ B)) 1 L' := by
  rw [componentsAt_append]
  congr 1
  · refine componentsAt_congr _ _ 1 L fun i _ hi => ?_
    simp only [mem_mergeIndices_of_le hB (show i ≤ L.length by omega)]
  · refine componentsAt_shift _ _ 1 L.length L' fun i hi => ?_
    simp only [add_mem_mergeIndices_iff hA hi]
theorem composable_subtuple {X Y : SepTuple} (h : SepTuple.Composable X Y) (A B : Finset ℕ) :
    SepTuple.Composable (X.subtuple A) (Y.subtuple B) := fun f hf g hg =>
  h f ((SepTuple.sublistOn_sublist X.1 A).subset hf) g
    ((SepTuple.sublistOn_sublist Y.1 B).subset hg)
theorem centredTuple_juxt (s : TestSpaces.SepTuple → ℝ) {X Y : SepTuple}
    (h : SepTuple.Composable X Y) :
    centredTuple s (SepTuple.juxt X Y) =
      formalMul (centredTuple s X) (centredTuple s Y) := by
  have hval := SepTuple.juxt_val h
  have hlen : (SepTuple.juxt X Y).size = X.size + Y.size := by
    simp [SepTuple.size, hval]
  rw [centredTuple, centredTuple, centredTuple, formalMul_sum, hlen,
    ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (mergeIndices X.size) (splitIndices X.size) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.1 hp
    exact Finset.mem_powerset.2
      (mergeIndices_subset (Finset.mem_powerset.1 hA) (Finset.mem_powerset.1 hB))
  · intro C hC
    have hC' := Finset.mem_powerset.1 hC
    exact Finset.mem_product.2 ⟨Finset.mem_powerset.2 (splitIndices_fst_subset hC'),
      Finset.mem_powerset.2 (splitIndices_snd_subset hC')⟩
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.1 hp
    exact splitIndices_mergeIndices (Finset.mem_powerset.1 hA) (Finset.mem_powerset.1 hB)
  · intro C _
    exact mergeIndices_splitIndices _ C
  · rintro ⟨A, B⟩ hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.1 hp
    have hA' : A ⊆ Finset.Icc 1 X.1.length := Finset.mem_powerset.1 hA
    have hB' : B ⊆ Finset.Icc 1 Y.size := Finset.mem_powerset.1 hB
    have hsub : (SepTuple.juxt X Y).subtuple (mergeIndices X.size (A, B)) =
        SepTuple.juxt (X.subtuple A) (Y.subtuple B) := by
      refine Subtype.ext ?_
      rw [SepTuple.juxt_val (composable_subtuple h A B)]
      change SepTuple.sublistOn (SepTuple.juxt X Y).1 _ =
        SepTuple.sublistOn X.1 A ++ SepTuple.sublistOn Y.1 B
      rw [hval, sublistOn_eq_elementsAt, sublistOn_eq_elementsAt, sublistOn_eq_elementsAt]
      exact componentsAt_mem_mergeIndices hA' hB'
    have hcoef : centringCoeff s (SepTuple.juxt X Y) (mergeIndices X.size (A, B)) =
        centringCoeff s X A * centringCoeff s Y B := by
      rw [centringCoeff_eq_prod, centringCoeff_eq_prod, centringCoeff_eq_prod, hval]
      change ((elementsAt (fun i => decide (i ∉ mergeIndices X.1.length (A, B))) 1
        (X.1 ++ Y.1)).map (negMeanCoeff s)).prod = _
      rw [componentsAt_not_mem_mergeIndices hA' hB', List.map_append, List.prod_append]
    simp only [hsub, hcoef]
theorem centring_formalMul_sum (s : TestSpaces.SepTuple → ℝ) (S T : Finset SepTuple)
    (c c' : SepTuple → ℂ) (h : ∀ X ∈ S, ∀ Y ∈ T, SepTuple.Composable X Y) :
    centring s (formalMul (∑ X ∈ S, c X • basisVec X) (∑ Y ∈ T, c' Y • basisVec Y)) =
      formalMul (centring s (∑ X ∈ S, c X • basisVec X))
        (centring s (∑ Y ∈ T, c' Y • basisVec Y)) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun Y hY => congrArg (c' Y • ·) <|
    Finset.sum_congr rfl fun X hX => congrArg (c X • ·) ?_
  rw [formalMul_basisVec, centring_basisVec, centring_basisVec, centring_basisVec,
    centredTuple_juxt s (h X hX Y hY)]
theorem sum_support_smul_basisVec (Z : FormalSpan) : ∑ X ∈ Z.support, Z X • basisVec X = Z := by
  conv_rhs => rw [← Finsupp.sum_single Z]
  refine Finset.sum_congr rfl fun X _ => ?_
  simp [basisVec]
theorem conjugation_centredTuple (s : TestSpaces.SepTuple → ℝ) (X : SepTuple) :
    conjugation (centredTuple s X) = centredTuple s X := by
  rw [centredTuple, conjugation_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  congr 1
  simp only [centringCoeff, map_prod, Complex.conj_ofReal]
theorem centring_conjugation (s : TestSpaces.SepTuple → ℝ) (Z : FormalSpan) :
    centring s (conjugation Z) = conjugation (centring s Z) := by
  rw [← sum_support_smul_basisVec Z]
  simp only [map_sum, map_smulₛₗ, conjugation_basisVec, centring_basisVec,
    conjugation_centredTuple, RingHom.id_apply]
theorem spanIn_le_comap_centring (s : TestSpaces.SepTuple → ℝ) (O : Set AmbientSpace) :
    spanIn O ≤ (spanIn O).comap (centring s) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨X, hX⟩, rfl⟩
  change centring s (basisVec X) ∈ spanIn O
  rw [centring_basisVec, centredTuple]
  refine Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨X.subtuple A, fun f hf => hX f ((SepTuple.sublistOn_sublist X.1 A).subset hf)⟩, rfl⟩
theorem centredTuple_eq_basisVec_of_vanishing (s : TestSpaces.SepTuple → ℝ)
    (h₀ : ∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
      cumulantOne s f hf = 0) (X : SepTuple) :
    centredTuple s X = basisVec X := by
  rw [centredTuple, Finset.sum_eq_single (Finset.Icc 1 X.size)]
  · have hc : centringCoeff s X (Finset.Icc 1 X.size) = 1 := by
      refine Finset.prod_eq_one fun l hl => ?_
      exact absurd (Finset.mem_Icc.2 ⟨by omega, l.2⟩) (Finset.mem_filter.1 hl).2
    have hs : X.subtuple (Finset.Icc 1 X.size) = X := by
      refine Subtype.ext ?_
      change SepTuple.sublistOn X.1 _ = X.1
      rw [sublistOn_eq_elementsAt]
      refine componentsAt_of_forall _ 1 X.1 fun i hi hi' => ?_
      exact decide_eq_true (Finset.mem_Icc.2 ⟨hi, by change i ≤ X.1.length; omega⟩)
    rw [hc, hs, one_smul]
  · intro A hA hne
    obtain ⟨i, hi, hiA⟩ := Finset.not_subset.1
      fun h => hne (Finset.Subset.antisymm (Finset.mem_powerset.1 hA) h)
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.1 hi
    have hl : i - 1 < X.1.length := by
      change i ≤ X.1.length at h₂
      omega
    have hc : centringCoeff s X A = 0 := by
      refine Finset.prod_eq_zero (i := ⟨i - 1, hl⟩) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩) ?_
      · have : i - 1 + 1 = i := by omega
        simpa [this] using hiA
      · simp [componentCumulantOne, h₀]
    rw [hc, zero_smul]
  · intro hn
    exact absurd (Finset.mem_powerset.2 subset_rfl) hn
section Motion
variable {r : Equiv.Perm AmbientSpace}
theorem contDiff_of_mem_cubicMotionGroup (hr : r ∈ cubicMotionGroup) :
    ContDiff ℝ 1 (r : AmbientSpace → AmbientSpace) := by
  obtain ⟨w, -, v, h⟩ := hr
  have hw : (r : AmbientSpace → AmbientSpace) =
      fun x => LinearMap.toContinuousLinearMap (w : AmbientSpace →ₗ[ℝ] AmbientSpace) x + v :=
    funext fun x => by simpa using h x
  rw [hw]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const
def homeomorphOfMotion (hr : r ∈ cubicMotionGroup) : AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := r
  continuous_toFun := (contDiff_of_mem_cubicMotionGroup hr).continuous
  continuous_invFun := (contDiff_of_mem_cubicMotionGroup (inv_mem hr)).continuous
theorem invMap_eq_inv (r : Equiv.Perm AmbientSpace) :
    invMap (r : AmbientSpace → AmbientSpace) = ⇑r⁻¹ := by
  funext x
  apply r.injective
  have h := Function.rightInverse_invFun r.surjective x
  change r (Function.invFun r x) = _
  rw [h]
  simp
theorem tsupport_comp_inv (hr : r ∈ cubicMotionGroup) (f : RealValued) :
    tsupport (f ∘ ⇑r⁻¹) = ⇑r⁻¹ ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (homeomorphOfMotion hr).symm
theorem isC1c_comp_inv (hr : r ∈ cubicMotionGroup) {f : RealValued}
    (hf : IsC1c f) : IsC1c (f ∘ ⇑r⁻¹) := by
  refine ⟨ContDiff.comp (show ContDiff ℝ 1 f from hf.1)
    (contDiff_of_mem_cubicMotionGroup (inv_mem hr)), ?_⟩
  unfold HasCompactSupport
  rw [tsupport_comp_inv hr]
  exact (homeomorphOfMotion hr).symm.isCompact_preimage.2 hf.2
theorem isDisjointlySupported_map_comp_inv (hr : r ∈ cubicMotionGroup) {L : List RealValued}
    (hL : IsDisjointlySupported L) : IsDisjointlySupported (L.map fun f => f ∘ ⇑r⁻¹) := by
  refine ⟨fun g hg => ?_, List.pairwise_map.2 (hL.2.imp fun {f g} h => ?_)⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    exact isC1c_comp_inv hr (hL.1 f hf)
  · rw [tsupport_comp_inv hr, tsupport_comp_inv hr]
    exact h.preimage _
theorem push_val (hr : r ∈ cubicMotionGroup) (X : SepTuple) :
    (push r X).1 = X.1.map fun f => f ∘ ⇑r⁻¹ := by
  have h : pushList r X.1 = X.1.map fun f => f ∘ ⇑r⁻¹ := by
    rw [pushList, invMap_eq_inv]
  have hs : IsDisjointlySupported (pushList r X.1) := by
    rw [h]
    exact isDisjointlySupported_map_comp_inv hr X.2
  unfold push
  rw [dif_pos hs]
  exact h
theorem ofList_eq_singleton {f : RealValued} (T : SepTuple) (hT : T.1 = [f])
    (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    ofList T = ⟨1, singletonSepTuple f hf⟩ := by
  obtain ⟨L, hL⟩ := T
  obtain rfl : L = [f] := hT
  refine sepTuple_ext _ _ rfl fun k => ?_
  rcases k with ⟨_ | k, hk⟩
  · rfl
  · simp at hk
theorem negMeanCoeff_comp_inv (s : TestSpaces.SepTuple → ℝ) (hr : r ∈ cubicMotionGroup)
    (hs : ∀ X : SepTuple, s (ofList (push r X)) = s (ofList X)) {f : RealValued}
    (hf : IsC1c f) : negMeanCoeff s (f ∘ ⇑r⁻¹) = negMeanCoeff s f := by
  have hg := isC1c_comp_inv hr hf
  have h₁ : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
    ⟨hf.1, hf.2, Set.subset_univ _⟩
  have h₂ : f ∘ ⇑r⁻¹ ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
    ⟨hg.1, hg.2, Set.subset_univ _⟩
  let T : SepTuple := ⟨[f], ⟨by simpa using hf, by simp⟩⟩
  have hT : (push r T).1 = [f ∘ ⇑r⁻¹] := by
    rw [push_val hr]
    rfl
  rw [negMeanCoeff, negMeanCoeff, dif_pos h₁, dif_pos h₂, cumulantOne_eq,
    cumulantOne_eq, ← ofList_eq_singleton _ hT h₂, ← ofList_eq_singleton T rfl h₁, hs]
theorem push_subtuple (hr : r ∈ cubicMotionGroup) (X : SepTuple) (A : Finset ℕ) :
    (push r X).subtuple A = push r (X.subtuple A) := by
  refine Subtype.ext ?_
  rw [push_val hr]
  change SepTuple.sublistOn (push r X).1 A = (SepTuple.sublistOn X.1 A).map _
  rw [push_val hr, sublistOn_eq_elementsAt, sublistOn_eq_elementsAt, componentsAt_map]
theorem centringCoeff_push (s : TestSpaces.SepTuple → ℝ) (hr : r ∈ cubicMotionGroup)
    (hs : ∀ X : SepTuple, s (ofList (push r X)) = s (ofList X)) (X : SepTuple) (A : Finset ℕ) :
    centringCoeff s (push r X) A = centringCoeff s X A := by
  rw [centringCoeff_eq_prod, centringCoeff_eq_prod, push_val hr, componentsAt_map,
    List.map_map]
  congr 1
  refine List.map_congr_left fun f hf => ?_
  exact negMeanCoeff_comp_inv s hr hs (X.2.1 f ((componentsAt_sublist _ 1 X.1).subset hf))
theorem centredTuple_push (s : TestSpaces.SepTuple → ℝ) (hr : r ∈ cubicMotionGroup)
    (hs : ∀ X : SepTuple, s (ofList (push r X)) = s (ofList X)) (X : SepTuple) :
    centredTuple s (push r X) = pushSpan r (centredTuple s X) := by
  have hlen : (push r X).size = X.size := by
    simp [SepTuple.size, push_val hr]
  rw [centredTuple, centredTuple, hlen, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_smul, pushSpan, linearExtend_basisVec, push_subtuple hr,
    centringCoeff_push s hr hs]
end Motion
theorem centringPreservesStructure_holds : CentringPreservesStructure := by
  intro s
  refine ⟨fun Z W h => ?_, centring_conjugation s, fun O Z hZ =>
    spanIn_le_comap_centring s O hZ, fun r hr hs Z => ?_, fun h₀ Z => ?_⟩
  · have := centring_formalMul_sum s Z.support W.support Z W h
    rwa [sum_support_smul_basisVec, sum_support_smul_basisVec] at this
  · rw [← sum_support_smul_basisVec Z]
    simp only [map_sum, map_smul, pushSpan, linearExtend_basisVec, centring_basisVec,
      centredTuple_push s hr hs]
  · rw [← sum_support_smul_basisVec Z]
    simp only [map_sum, map_smul, centring_basisVec, centredTuple_eq_basisVec_of_vanishing s h₀]
end YangMills.Construction.Continuum.CentringRespectsOperations
end
