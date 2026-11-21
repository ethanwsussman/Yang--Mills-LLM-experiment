import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgreeProof
import YangMills.Construction.EuclideanFunctionals.RaisingContractsAnInsertionMovedInTimeAndThePlateBoundAtEveryFractionProof
import YangMills.Construction.EuclideanFunctionals.TensorsWithComplexEntriesTranslationsAndTranslatedClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror
namespace EuclideanFunctionals.TensorTranslation
theorem actFree_toFree (r : EuclidMotion) (X : sepAll) :
    r.actFree (toFree X.1) = toFree (r.actList X.1) :=
  liftLin_toFree _ X
theorem centeredFnFree_toFree (S : ConnFamily) (X : sepAll) :
    centeredFnFree S (toFree X.1) = (centeredFn S X : ℂ) :=
  liftLin_toFree _ X
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
def blockProductSum (S : ConnFamily) (n : ℕ) (f : Fin n → R4 → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
    Ambient.ConnectedFamily.evalAt S J.card
      (List.ofFn fun k : Fin J.card => f (J.orderEmbOfFin rfl k))
theorem centeredFn_eq_blockProductSum (S : ConnFamily) (X : sepAll) :
    centeredFn S X = blockProductSum S X.1.length X.1.get :=
  rfl
theorem blockProductSum_congr (S : ConnFamily) {n n' : ℕ} (h : n = n') (f : Fin n → R4 → ℝ)
    (g : Fin n' → R4 → ℝ) (hfg : ∀ i, f i = g (Fin.cast h i)) :
    blockProductSum S n f = blockProductSum S n' g := by
  subst h
  have : f = g := funext hfg
  rw [this]
theorem evalAt_transl {S : ConnFamily} (hinv : ConnectedInvariant S) (z : R4) {n : ℕ}
    {Y : FnList} (hY : Y ∈ sepN n) :
    Ambient.ConnectedFamily.evalAt S n ((EuclidMotion.transl z).actList Y) =
      Ambient.ConnectedFamily.evalAt S n Y := by
  by_cases h : 2 ≤ n
  · simp only [Ambient.ConnectedFamily.evalAt, dif_pos h]
    exact (hinv n h Y hY).1 z
  · simp only [Ambient.ConnectedFamily.evalAt, dif_neg h]
theorem blockProductSum_transl {S : ConnFamily} (hinv : ConnectedInvariant S) (z : R4)
    (X : sepAll) :
    blockProductSum S X.1.length (fun i => (EuclidMotion.transl z).actFn (X.1.get i)) =
      blockProductSum S X.1.length X.1.get := by
  have hs := isSeparatedList_of_mem_sepAll X.2
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  have hJ := Ambient.subList_mem_separatedN hs J
  have h := evalAt_transl hinv z hJ
  have e : (EuclidMotion.transl z).actList (Ambient.subList X.1 J) =
      List.ofFn fun k : Fin J.card =>
        (EuclidMotion.transl z).actFn (X.1.get (J.orderEmbOfFin rfl k)) := by
    rw [EuclidMotion.actList, Ambient.subList, List.map_ofFn]
    rfl
  exact (congrArg (Ambient.ConnectedFamily.evalAt S J.card) e).symm.trans h
theorem actList_mem_sepAll (hImg : TupleRules.MotionOfListsAndCombs)
    (r : EuclidMotion) {X : FnList} (hX : X ∈ sepAll) : r.actList X ∈ sepAll := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hX
  have hin : X ∈ sepNIn n Set.univ := ⟨hn, hX, fun _ _ => Set.subset_univ _⟩
  exact Ambient.separatedN_subset_separatedAll _ _ n
    ((((hImg r Set.univ isOpen_univ).2.1 n).1.mapsTo hin).1)
theorem get_map_eq_cast {α β : Type*} (g : α → β) (X : List α) (h : (X.map g).length = X.length)
    (i : Fin (X.map g).length) : (X.map g).get i = g (X.get (Fin.cast h i)) := by
  simp
theorem centeredFn_transl {S : ConnFamily} (hinv : ConnectedInvariant S)
    (z : R4) (X : sepAll) (hY : (EuclidMotion.transl z).actList X.1 ∈ sepAll) :
    centeredFn S ⟨_, hY⟩ = centeredFn S X := by
  rw [centeredFn_eq_blockProductSum, centeredFn_eq_blockProductSum,
    ← blockProductSum_transl hinv z X]
  refine blockProductSum_congr S (by simp [EuclidMotion.actList]) _ _ fun i =>
    get_map_eq_cast _ _ _ i
theorem centeredFnFree_transl {S : ConnFamily} (hImg : TupleRules.MotionOfListsAndCombs)
    (hinv : ConnectedInvariant S) (z : R4) (F : FreeSep) :
    centeredFnFree S ((EuclidMotion.transl z).actFree F) =
      centeredFnFree S F := by
  have h : centeredFnFree S ∘ₗ (EuclidMotion.transl z).actFree =
      centeredFnFree S := freeBasis.ext fun X => by
    have hY := actList_mem_sepAll hImg (EuclidMotion.transl z) X.2
    rw [freeBasis_apply, LinearMap.comp_apply, actFree_toFree,
      centeredFnFree_toFree S ⟨_, hY⟩, centeredFnFree_toFree S X,
      centeredFn_transl hinv z X hY]
  exact LinearMap.congr_fun h F
theorem tensorComp_transl (hAct : TupleRules.MotionOnFree) (z : R4)
    (q : ℕ) (F : FreeSep) :
    tensorComp q ((EuclidMotion.transl z).actFree F) =
      translateArgs z (tensorComp q F) := by
  have h := (hAct 1 1 F).2.2.2.2.2.2.2 z
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [translateArgs_zero]
    funext e
    rw [tensorComp_zero_apply, tensorComp_zero_apply, h.1]
  · exact h.2 q hq
theorem hasSoleTensorComp_transl (hAct : TupleRules.MotionOnFree) (z : R4) {q : ℕ}
    {A : TestSpaces.PointTuple q → ℂ} {F : FreeSep} (h : HasSoleTensorComp q A F) :
    HasSoleTensorComp q (translateArgs z A) ((EuclidMotion.transl z).actFree F) := by
  refine ⟨by rw [tensorComp_transl hAct, h.1], fun q' hq' => ?_⟩
  rw [tensorComp_transl hAct, h.2 q' hq']
  rfl
theorem translateSepTensors_holds {S : ConnFamily} (hinv : ConnectedInvariant S)
    (hT : TupleRules.TupleSpanActionRules) (hC : TensorComponents.CenteredSeesTensorComps) :
    TranslateSepTensors S := by
  obtain ⟨-, hImg, hAct, -⟩ := hT
  obtain ⟨-, -, ⟨hq, hnum, -, hspan, -⟩, -⟩ := hC S
  have hval : ∀ (q : ℕ) (A : TestSpaces.PointTuple q → ℂ) (F : FreeSep),
      A ∈ sepTensorSpan q → HasSoleTensorComp q A F →
        centeredOnTensor S q A = centeredFnFree S F := fun q A F hAq hF =>
    (hq q).2.1 A hAq _ F (Classical.epsilon_spec ⟨F, hF⟩) hF
  refine ⟨fun z q A hAq => ?_, by simp [sepTensorSpan], fun z A e =>
    ⟨translateArgs_zero z A, hnum A e⟩⟩
  obtain ⟨F, hF⟩ := (hq q).1 A hAq
  have hF' := hasSoleTensorComp_transl hAct z hF
  have hmem : translateArgs z A ∈ sepTensorSpan q := by
    rw [← hF'.1]
    exact hspan _ q
  exact ⟨hmem, by rw [hval q _ _ hmem hF', hval q A F hAq hF, centeredFnFree_transl hImg hinv]⟩
theorem reImPart_mem_C1c {h : R4 → ℂ} (hP : TupleRules.ReImAndMotionOfFns)
    (c : SharpScale) (hh : h ∈ C1c ℂ) (ε : Fin 2) :
    reOrImPart ε h ∈ C1c ℝ := by
  have := hP c 1 1 h hh
  by_cases he : ε = 0
  · simpa [reOrImPart, he] using this.1
  · simpa [reOrImPart, he] using this.2.1
theorem supp_reImPart_subset {h : R4 → ℂ} (hP : TupleRules.ReImAndMotionOfFns)
    (c : SharpScale) (hh : h ∈ C1c ℂ) (ε : Fin 2) :
    supp (reOrImPart ε h) ⊆ supp h := by
  have := (hP c 1 1 h hh).2.2.1
  by_cases he : ε = 0
  · simpa [reOrImPart, he] using Set.subset_union_left.trans this
  · simpa [reOrImPart, he] using Set.subset_union_right.trans this
theorem realTensorExpansion_holds {q : ℕ} (h : Fin q → R4 → ℂ) : RealTensorExpansion h := by
  have hone : ∀ (w : ℂ), w = ∑ e : Fin 2, Complex.I ^ (e : ℕ) *
      (((if e = 0 then w.re else w.im : ℝ)) : ℂ) := fun w => by
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, if_true, one_mul, Fin.val_one, pow_one,
      one_ne_zero, if_false]
    rw [mul_comm]
    exact (Complex.re_add_im w).symm
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    tensorOfFns_apply]
  have hpart : ∀ l, h l (x l) = ∑ e : Fin 2, Complex.I ^ (e : ℕ) * complexOfPart e (h l) (x l) := by
    intro l
    conv_lhs => rw [hone (h l (x l))]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e = 0 <;> simp [complexOfPart, reOrImPart, he]
  rw [Finset.prod_congr rfl fun l _ => hpart l, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
theorem tensorsAboveHeight_holds {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
    (hT : TupleRules.TupleSpanActionRules) : TensorsAboveHeight σ := by
  obtain ⟨hP, -, -, -, -, -, -, hW, -⟩ := hT
  intro c hc q hq h hmem hdis hsup
  have hE : ComplexComponents h := ⟨hq, hmem, hdis⟩
  have hopen : IsOpen {x : R4 | c < x 3} := isOpen_lt continuous_const (continuous_apply 3)
  have hopenP : IsOpen upperHalf := isOpen_lt continuous_const (continuous_apply 3)
  have hsub : {x : R4 | c < x 3} ⊆ upperHalf := fun x hx =>
    lt_of_le_of_lt hc hx
  have hw := hW _ hopen 1 q h hE hsup
  have hwP := hW _ hopenP 1 q h hE fun l => (hsup l).trans hsub
  have hs := fun (ε : Fin 2) (l : Fin q) => supp_reImPart_subset hP m (hmem l) ε
  refine ⟨realTensorExpansion_holds h, fun ε l => hs ε l, fun ε => ⟨fun l => reImPart_mem_C1c hP m (hmem l) _,
    fun k l hkl => (hdis hkl).mono (hs _ k) (hs _ l), fun l => (hs _ l).trans (hsup l)⟩,
    hwP.1, ⟨hw.2.2.1, fun q' hq' => ?_⟩, rfl, hw.1⟩
  rcases Nat.eq_zero_or_pos q' with rfl | hpos
  · funext e
    rw [tensorComp_zero_apply, hw.2.2.2.1]
    rfl
  · exact hw.2.2.2.2.1 q' hpos hq'
theorem timeVec_three : timeVec 3 = 1 := by
  simp [PeriodicLattice.coordVec]
theorem transl_neg_mul_transl (c : ℝ) :
    EuclidMotion.transl ((-c) • timeVec) * EuclidMotion.transl (c • timeVec) = 1 :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
      EuclidMotion.one_apply]
    simp
theorem transl_image_upperHalf (c : ℝ) :
    (EuclidMotion.transl (c • timeVec)) '' upperHalf = {x | c < x 3} := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.image_transl_upperHalf <;> assumption
theorem pullDown_raise (hAct : TupleRules.MotionOnFree) (c : ℝ) (F : FreeSep) :
    pullDown c (raise c F) = F := by
  rw [pullDown, raise, (hAct _ _ F).1, transl_neg_mul_transl, actFree_one]
theorem raise_pullDown (hAct : TupleRules.MotionOnFree) (c : ℝ) (F : FreeSep) :
    raise c (pullDown c F) = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.raise_pullDown <;> assumption
theorem raiseBijIsometric_holds {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) (hT : TupleRules.TupleSpanActionRules) :
    RaiseBijIsometric σ := by
  obtain ⟨-, hImg, hAct, -⟩ := hT
  intro c _
  have hopenP : IsOpen upperHalf := isOpen_lt continuous_const (continuous_apply 3)
  have hb := (hImg (EuclidMotion.transl (c • timeVec)) upperHalf hopenP).2.2
  rw [transl_image_upperHalf] at hb
  refine ⟨hb, ⟨fun F _ => pullDown_raise hAct c F, fun F _ => raise_pullDown hAct c F⟩,
    fun F _ => ?_⟩
  rw [heightNorm, pullDown_raise hAct]
theorem transl_neg_mul_timeFlip (c : ℝ) :
    EuclidMotion.transl ((-c) • timeVec) * timeFlip = timeFlip * EuclidMotion.transl (c • timeVec) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TimeShiftAndFractions.transl_neg_mul_timeFlip <;> assumption
theorem lowerFlipConj_holds (hT : TupleRules.TupleSpanActionRules) : LowerFlipConj := by
  obtain ⟨-, -, hAct, -⟩ := hT
  intro F _ c _
  rw [flipConj, flipConj, raise, (hAct _ _ _).1, (hAct _ 1 F).2.1,
    (hAct _ _ _).1, transl_neg_mul_timeFlip]
theorem allFacts_holds (hT : TupleRules.TupleSpanActionRules)
    (hC : TensorComponents.CenteredSeesTensorComps) :
    AllFacts := fun _ _ σ =>
  ⟨tensorsAboveHeight_holds σ hT,
    translateSepTensors_holds σ.invariant hT hC,
    raiseBijIsometric_holds σ hT,
    lowerFlipConj_holds hT⟩
end EuclideanFunctionals.TensorTranslation
end YangMills.Construction
