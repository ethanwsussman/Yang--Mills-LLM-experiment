import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnly
import YangMills.Construction.EuclideanFunctionals.ConcatenationIsTheTensorProductAndTheFormsInComponents
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MulTensor
open TensorCompRules (splitTerm)
open TensorComponents
open ReflectionPositivity.AxisMirror
theorem splitTerm_apply (F A : FreeSep) (n : ℕ) (k : Fin (n + 1))
    (x : TestSpaces.PointTuple n) :
    splitTerm F A n k x =
      tensorComp k F (fun i => x (Fin.castLE (by omega) i)) *
        tensorComp (n - k) A
          (fun j => x (Fin.cast (by omega) (Fin.natAdd (k : ℕ) j))) := by
  obtain ⟨k, hk⟩ := k
  unfold splitTerm
  dsimp only
  split_ifs with h0 hn
  · subst h0
    show tensorCompZero F * tensorComp n A x = _
    rw [tensorComp_zero_apply]
    refine congrArg _ (congrArg (tensorComp n A) ?_)
    funext j
    exact congrArg x (Fin.ext (by simp))
  · subst hn
    have key : ∀ (m : ℕ), m = 0 → ∀ y : TestSpaces.PointTuple m,
        tensorComp m A y = tensorCompZero A := by
      rintro _ rfl y
      exact tensorComp_zero_apply A y
    rw [key _ (Nat.sub_self k)]
    show tensorCompZero A * tensorComp k F x = _
    rw [mul_comm]
    refine congrArg (· * tensorCompZero A) (congrArg (tensorComp k F) ?_)
    funext i
    exact congrArg x (Fin.ext rfl)
  · rfl
theorem splitTerm_eq_tensorFun (F A : FreeSep) (q q' : ℕ) :
    splitTerm F A (q + q') ⟨q, by omega⟩ =
      TestSpaces.tensorFun (tensorComp q F) (tensorComp q' A) := by
  funext x
  rw [splitTerm_apply, tensorFun_apply]
  have key : ∀ (m : ℕ), m = q' → ∀ e : q + m = q + q',
      tensorComp m A (fun j => x (Fin.cast e (Fin.natAdd q j))) =
        tensorComp q' A (fun j => x (Fin.natAdd q j)) := by
    rintro _ rfl e
    rfl
  exact congrArg₂ (· * ·) rfl (key _ (Nat.add_sub_cancel_left q q') _)
def gradedPart (k : ℕ) (F : FreeSep) : FreeSep := F.filter fun X => X.1.length = k
theorem tensorComp_single (X : sepAll) (z : ℂ) (j : ℕ) :
    tensorComp j (Finsupp.single X z) = z • tensorAt j X := by
  simp [tensorComp, liftLin]
theorem tensorComp_gradedPart (k j : ℕ) (F : FreeSep) :
    tensorComp j (gradedPart k F) = if j = k then tensorComp j F else 0 := by
  induction F using Finsupp.induction_linear with
  | zero =>
    rw [gradedPart, Finsupp.filter_zero]
    simp
  | add f g hf hg =>
    have : gradedPart k (f + g) = gradedPart k f + gradedPart k g := Finsupp.filter_add
    rw [this, map_add, hf, hg, map_add]
    split_ifs <;> simp
  | single X z =>
    by_cases hX : X.1.length = k
    · have : gradedPart k (Finsupp.single X z) = Finsupp.single X z :=
        Finsupp.filter_single_of_pos _ hX
      rw [this]
      split_ifs with hj
      · rfl
      · rw [tensorComp_single, tensorAt_of_length_ne X (by omega), smul_zero]
    · have : gradedPart k (Finsupp.single X z) = 0 := Finsupp.filter_single_of_neg _ hX
      rw [this, map_zero]
      split_ifs with hj
      · rw [tensorComp_single, tensorAt_of_length_ne X (by omega), smul_zero]
      · rfl
theorem combSupp_gradedPart_subset (k : ℕ) (F : FreeSep) :
    combSupp (gradedPart k F) ⊆ combSupp F := by
  intro y hy
  obtain ⟨X, hX, hy⟩ := Set.mem_iUnion₂.1 hy
  refine Set.mem_iUnion₂.2 ⟨X, ?_, hy⟩
  have hX' : X ∈ (F.filter fun X => X.1.length = k).support := hX
  rw [Finsupp.support_filter] at hX'
  exact (Finset.mem_filter.1 hX').1
theorem exists_tensorComp_eq_zero (F : FreeSep) :
    ∃ N, ∀ q, N ≤ q → tensorComp q F = 0 := by
  induction F using Finsupp.induction_linear with
  | zero => exact ⟨0, fun q _ => map_zero _⟩
  | add f g hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    refine ⟨max N N', fun q hq => ?_⟩
    rw [map_add, hN q (le_of_max_le_left hq), hN' q (le_of_max_le_right hq), add_zero]
  | single X z =>
    refine ⟨X.1.length + 1, fun q hq => ?_⟩
    rw [tensorComp_single, tensorAt_of_length_ne X (by omega), smul_zero]
theorem isCompact_combSupp (F : FreeSep) : IsCompact (combSupp F) := by
  refine F.support.isCompact_biUnion fun X _ => ?_
  refine (List.finite_toSet X.1).isCompact_biUnion fun f hf => ?_
  exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).1
    ((isSeparatedList_of_mem_sepAll X.2).1 f hf).2
theorem mem_freeSpanIn_of_subset {F : FreeSep} {O : Set R4} (h : combSupp F ⊆ O) :
    F ∈ freeSpanIn O := by
  rw [← finCombIn_eq_freeSpanIn, finCombIn, Finsupp.mem_supported]
  intro X hX
  refine ⟨X.2, fun f hf y hy => h (Set.mem_iUnion₂.2 ⟨X, Finset.mem_coe.1 hX, ?_⟩)⟩
  exact Set.mem_iUnion₂.2 ⟨f, hf, hy⟩
theorem tensorComp_freeMul (hR : TensorCompRules.MulRule)
    {F A : FreeSep} (h : MulDefined F A) :
    tensorCompZero (freeMul F A) = tensorCompZero F * tensorCompZero A ∧
      ∀ r, tensorComp r (freeMul F A) = ∑ k, splitTerm F A r k := by
  obtain ⟨U, V, hU, hV, hFU, hAV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (isCompact_combSupp F) (isCompact_combSupp A) h
  obtain ⟨h₀, h₁⟩ := hR U V hU hV hUV F (mem_freeSpanIn_of_subset hFU) A (mem_freeSpanIn_of_subset hAV)
  refine ⟨h₀, fun r => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · funext e
    rw [tensorComp_zero_apply, h₀, Fin.sum_univ_one, splitTerm_apply]
    exact congrArg₂ (· * ·) (tensorComp_zero_apply F _).symm (tensorComp_zero_apply A _).symm
  · exact h₁ r hr
theorem splitTerm_mem (hR : TensorCompRules.MulRule)
    (hL : CompsInSepSpan) {F A : FreeSep} (h : MulDefined F A) (r : ℕ)
    (k : Fin (r + 1)) : splitTerm F A r k ∈ sepTensorSpan r := by
  have hd : MulDefined (gradedPart k F) (gradedPart (r - k) A) :=
    Disjoint.mono (combSupp_gradedPart_subset _ _) (combSupp_gradedPart_subset _ _) h
  have hk : splitTerm F A r k =
      tensorComp r (freeMul (gradedPart k F) (gradedPart (r - k) A)) := by
    rw [(tensorComp_freeMul hR hd).2 r, Finset.sum_eq_single k]
    · funext x
      rw [splitTerm_apply, splitTerm_apply, tensorComp_gradedPart,
        tensorComp_gradedPart, if_pos rfl, if_pos rfl]
    · intro j _ hj
      funext x
      rw [splitTerm_apply, tensorComp_gradedPart, if_neg fun e => hj (Fin.ext e)]
      simp
    · simp
  rw [hk]
  exact hL _ r
variable {S : ConnFamily}
theorem centeredOnTensor_zero {q : ℕ} (hlin : LinearOnSepSpan S q) :
    centeredOnTensor S q 0 = 0 := by
  have := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0 0
  simpa using this
theorem centeredOnTensor_sum {q : ℕ} (hlin : LinearOnSepSpan S q) {ι : Type*} (s : Finset ι)
    (f : ι → TestSpaces.PointTuple q → ℂ) (hf : ∀ i ∈ s, f i ∈ sepTensorSpan q) :
    centeredOnTensor S q (∑ i ∈ s, f i) = ∑ i ∈ s, centeredOnTensor S q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using centeredOnTensor_zero hlin
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ← ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    have := hlin (f a) (hf a (Finset.mem_insert_self _ _)) (∑ i ∈ s, f i)
      (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)) 1 1
    simpa using this
def orderPairTerm (S : ConnFamily) (F A : FreeSep) (p : ℕ × ℕ) : ℂ :=
  centeredOnTensor S (p.1 + p.2) (splitTerm F A (p.1 + p.2) ⟨p.1, by omega⟩)
theorem centeredOnTensor_index_congr (S : ConnFamily) (F A : FreeSep) {n m : ℕ} (h : m = n)
    (k : ℕ) (h₁ : k < n + 1) (h₂ : k < m + 1) :
    centeredOnTensor S n (splitTerm F A n ⟨k, h₁⟩) =
      centeredOnTensor S m (splitTerm F A m ⟨k, h₂⟩) := by
  subst h
  rfl
theorem centeredFnFree_freeMul_eq_finsum (hR : TensorCompRules.MulRule)
    (hL : CompsInSepSpan) (hlin : ∀ q, LinearOnSepSpan S q)
    (hSum : EqFinsumOverOrders S) {F A : FreeSep} (h : MulDefined F A) :
    (Function.support (orderPairTerm S F A)).Finite ∧
      centeredFnFree S (freeMul F A) = ∑ᶠ p, orderPairTerm S F A p := by
  classical
  obtain ⟨N, hN⟩ := exists_tensorComp_eq_zero F
  obtain ⟨N', hN'⟩ := exists_tensorComp_eq_zero A
  have hvan : ∀ p : ℕ × ℕ, p ∉ Finset.range N ×ˢ Finset.range N' →
      orderPairTerm S F A p = 0 := by
    rintro ⟨q, q'⟩ hp
    have hz : TestSpaces.tensorFun (tensorComp q F) (tensorComp q' A) = 0 := by
      rw [Finset.mem_product, not_and_or] at hp
      rcases hp with hp | hp
      · rw [hN q (by simpa using hp)]
        funext x
        simp [TestSpaces.tensorFun]
      · rw [hN' q' (by simpa using hp)]
        funext x
        simp [TestSpaces.tensorFun]
    show centeredOnTensor S (q + q') (splitTerm F A (q + q') ⟨q, by omega⟩) = 0
    rw [splitTerm_eq_tensorFun, hz]
    exact centeredOnTensor_zero (hlin _)
  have hsup : Function.support (orderPairTerm S F A) ⊆ ↑(Finset.range N ×ˢ Finset.range N') :=
    fun p hp => by_contra fun h' => hp (hvan p fun h'' => h' (Finset.mem_coe.2 h''))
  refine ⟨(Finset.finite_toSet _).subset hsup, ?_⟩
  have hfib : ∀ r, centeredOnTensor S r (tensorComp r (freeMul F A)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal r, orderPairTerm S F A p := by
    intro r
    rw [(tensorComp_freeMul hR h).2 r,
      centeredOnTensor_sum (hlin r) _ _ fun k _ => splitTerm_mem hR hL h r k]
    refine Finset.sum_bij (fun k _ => ((k : ℕ), r - (k : ℕ))) ?_ ?_ ?_ ?_
    · intro k _
      have := k.2
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      simp only
      omega
    · intro k _ k' _ e
      exact Fin.ext (congrArg Prod.fst e)
    · rintro ⟨a, b⟩ hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      simp only at hp
      refine ⟨⟨a, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      omega
    · intro k _
      have := k.2
      exact centeredOnTensor_index_congr S F A (by simp only; omega) _ _ _
  have hsupr : Function.support (fun r => centeredOnTensor S r (tensorComp r (freeMul F A))) ⊆
      ↑(Finset.range (N + N')) := by
    intro r hr
    by_contra h'
    refine hr ?_
    show centeredOnTensor S r (tensorComp r (freeMul F A)) = 0
    rw [hfib r]
    refine Finset.sum_eq_zero fun p hp => hvan p fun hp' => h' ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp'
    rw [Finset.mem_coe, Finset.mem_range]
    omega
  rw [(hSum (freeMul F A)).2, finsum_eq_sum_of_support_subset _ hsupr,
    finsum_eq_sum_of_support_subset _ hsup,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.range N ×ˢ Finset.range N')
      (t := Finset.range (N + N')) (g := fun p : ℕ × ℕ => p.1 + p.2)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [hfib r]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      exact (Finset.mem_filter.1 hp).2
    · intro p hp hp'
      refine hvan p fun hs => hp' (Finset.mem_filter.2 ⟨hs, ?_⟩)
      exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range]
    omega
theorem tensorComp_complexTuple_single
    (hTuple : TupleRules.ComplexTupleRules) {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ) :
    tensorComp 1 (complexTuple fun _ : Fin 1 => h) =
        tensorOfFns (fun _ : Fin 1 => h) ∧
      tensorCompZero (complexTuple fun _ : Fin 1 => h) = 0 ∧
      ∀ m, m ≠ 1 → tensorComp m (complexTuple fun _ : Fin 1 => h) = 0 := by
  have hE : ComplexComponents fun _ : Fin 1 => h :=
    ⟨le_rfl, fun _ => hh, fun a b hab => absurd (Subsingleton.elim a b) hab⟩
  obtain ⟨-, -, h₁, h₀, hne, -⟩ :=
    hTuple Set.univ isOpen_univ timeFlip 1 (fun _ => h) hE fun _ => Set.subset_univ _
  refine ⟨h₁, h₀, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hp
  · funext e
    rw [tensorComp_zero_apply, h₀]
    rfl
  · exact hne m hp hm
theorem tensorComp_freeMul_single_succ
    (hR : TensorCompRules.MulRule)
    (hTuple : TupleRules.ComplexTupleRules) {F : FreeSep} {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ)
    (hd : MulDefined F (complexTuple fun _ : Fin 1 => h)) (q : ℕ) :
    tensorComp (q + 1) (freeMul F (complexTuple fun _ : Fin 1 => h)) =
      TestSpaces.tensorFun (tensorComp q F) (tensorOfFns fun _ : Fin 1 => h) := by
  obtain ⟨h₁, -, hne⟩ := tensorComp_complexTuple_single hTuple hh
  rw [(tensorComp_freeMul hR hd).2, Finset.sum_eq_single ⟨q, by omega⟩]
  · rw [splitTerm_eq_tensorFun F _ q 1, h₁]
  · intro k _ hk
    funext x
    have hk' : (k : ℕ) ≠ q := fun e => hk (Fin.ext e)
    have := k.2
    rw [splitTerm_apply, hne (q + 1 - k) (by omega)]
    simp
  · simp
theorem tensorComp_zero_freeMul_single
    (hR : TensorCompRules.MulRule)
    (hTuple : TupleRules.ComplexTupleRules) {F : FreeSep} {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ)
    (hd : MulDefined F (complexTuple fun _ : Fin 1 => h)) :
    tensorComp 0 (freeMul F (complexTuple fun _ : Fin 1 => h)) = 0 := by
  funext e
  rw [tensorComp_zero_apply, (tensorComp_freeMul hR hd).1,
    (tensorComp_complexTuple_single hTuple hh).2.1, mul_zero]
  rfl
theorem orderPairTerm_succ (hR : TensorCompRules.MulRule)
    (hTuple : TupleRules.ComplexTupleRules) {F A : FreeSep} {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ)
    (hd : MulDefined (flipConj F)
      (complexTuple fun _ : Fin 1 => h)) (p : ℕ × ℕ) :
    orderPairTerm S (freeMul (flipConj F) (singleComponent h)) A (p.1 + 1, p.2) =
      insertionTerm S F h A p := by
  show centeredOnTensor S (p.1 + 1 + p.2) (splitTerm _ A (p.1 + 1 + p.2) ⟨p.1 + 1, _⟩) = _
  rw [splitTerm_eq_tensorFun]
  show _ = centeredOnTensor S (p.1 + 1 + p.2) (tensorWithInsert F h A p.1 p.2)
  unfold tensorWithInsert singleComponent
  rw [tensorComp_freeMul_single_succ hR hTuple hh hd]
theorem orderPairTerm_zero (hR : TensorCompRules.MulRule)
    (hlin : ∀ q, LinearOnSepSpan S q)
    (hTuple : TupleRules.ComplexTupleRules) {F A : FreeSep} {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ)
    (hd : MulDefined F (complexTuple fun _ : Fin 1 => h)) (q' : ℕ) :
    orderPairTerm S (freeMul F (singleComponent h)) A (0, q') = 0 := by
  show centeredOnTensor S (0 + q') (splitTerm _ A (0 + q') ⟨0, _⟩) = 0
  rw [splitTerm_eq_tensorFun]
  unfold singleComponent
  rw [tensorComp_zero_freeMul_single hR hTuple hh hd]
  have : TestSpaces.tensorFun (0 : TestSpaces.PointTuple 0 → ℂ) (tensorComp q' A) = 0 := by
    funext x
    simp [TestSpaces.tensorFun]
  rw [this]
  exact centeredOnTensor_zero (hlin _)
theorem holds_of_rules (hR : TensorCompRules.Holds)
    (hC : TensorComponents.CenteredSeesTensorComps)
    (hT : TupleRules.TupleSpanActionRules) : Holds := by
  obtain ⟨-, -, hConc, -⟩ := hR
  obtain ⟨-, -, hAct, -, -, -, hAssoc, hTuple, hMirror, hRefl, -, -⟩ := hT
  intro m S σ
  obtain ⟨-, -, ⟨hq, -, -, hL, hSum⟩, -, -⟩ := hC S
  have hlin : ∀ q, LinearOnSepSpan S q := fun q => (hq q).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F A h
    obtain ⟨h₀, h₁⟩ := tensorComp_freeMul hConc h
    exact ⟨h₀, fun r _ => h₁ r, fun r k => splitTerm_mem hConc hL h r k⟩
  · intro F hF
    obtain ⟨-, -, -, c₀, c₁, r₀, r₁, -⟩ := hAct timeFlip timeFlip (freeConj F)
    obtain ⟨-, -, -, d₀, d₁, -, -, -⟩ := hAct timeFlip timeFlip F
    have hm := (hRefl.1 0 le_rfl F hF F hF).1
    rw [neg_zero] at hm
    refine ⟨hm, ?_, fun q hq' x => ?_⟩
    · exact r₀.trans d₀
    · have := r₁ q hq' x
      rw [hMirror.1] at this
      exact this.trans (congrFun (d₁ q hq') _)
  · intro F hF A hA
    have hd := (hRefl.1 0 le_rfl F hF A hA).2
    obtain ⟨hfin, hval⟩ := centeredFnFree_freeMul_eq_finsum hConc hL hlin hSum hd
    refine ⟨hfin, ?_⟩
    have hcl : ∀ (G : FreeSep) (hG : G ∈ finCombIn upperHalf),
        reconClass σ G = σ.recon.cls ⟨G, hG⟩ := fun G hG => dif_pos hG
    rw [hcl F hF, hcl A hA, σ.recon.inner_cls]
    exact hval
  · intro c hc F hF A hA h hh hs
    have h3 := hRefl.2 c hc F hF A hA h hh hs
    have hd : MulDefined
        (freeMul (flipConj F) (singleComponent h)) A := (hAssoc _ _ _ h3).1
    obtain ⟨hfin, hval⟩ := centeredFnFree_freeMul_eq_finsum (S := S) hConc hL hlin hSum hd
    have hinj : Function.Injective fun p : ℕ × ℕ => (p.1 + 1, p.2) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ e
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at e
      exact Prod.ext e.1 e.2
    have hterm : insertionTerm S F h A =
        orderPairTerm S (freeMul (flipConj F) (singleComponent h)) A ∘
          fun p : ℕ × ℕ => (p.1 + 1, p.2) :=
      funext fun p => (orderPairTerm_succ hConc hTuple hh h3.1 p).symm
    refine ⟨?_, ?_⟩
    · rw [hterm, Function.support_comp_eq_preimage]
      exact hfin.preimage hinj.injOn
    · show centeredFnFree S (freeMul (freeMul (flipConj F) (singleComponent h)) A) = _
      rw [hval, hterm]
      have hP : ∀ p : ℕ × ℕ, p ∉ Set.range (fun p : ℕ × ℕ => (p.1 + 1, p.2)) →
          orderPairTerm S (freeMul (flipConj F) (singleComponent h)) A p = 0 := by
        rintro ⟨a, b⟩ hp
        rcases a with _ | a
        · exact orderPairTerm_zero hConc hlin hTuple hh h3.1 b
        · exact absurd ⟨(a, b), rfl⟩ hp
      refine Eq.trans ?_ (finsum_mem_range
        (f := orderPairTerm S (freeMul (flipConj F) (singleComponent h)) A) hinj)
      refine finsum_congr fun p => ?_
      classical
      rw [finsum_eq_if]
      split_ifs with hp
      · rfl
      · exact hP p hp
end YangMills.Construction.EuclideanFunctionals.MulTensor
