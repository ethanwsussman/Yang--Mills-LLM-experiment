import YangMills.Construction.EuclideanFunctionals.RulesForTheTensorComponentsProof
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntriesProof
import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgree
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.TupleConcat
theorem nil_mem_sepAll : ([] : FnList) ∈ sepAll := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.nil_mem_sepAll <;> assumption
theorem tensorComp_toFree (q : ℕ) (X : sepAll) :
    tensorComp q (toFree X.1) = tensorAt q X :=
  liftLin_toFree _ X
theorem freeMul_toFree {X Y : FnList} (hX : X ∈ sepAll) (hY : Y ∈ sepAll) :
    freeMul (toFree X) (toFree Y) = toFree (listAppend X Y) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeMul_toFree <;> assumption
theorem freeMul_toFree_nil (F : FreeSep) : freeMul F (toFree []) = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.freeMul_nil_right <;> assumption
def homogeneous (k : ℕ) : Submodule ℂ FreeSep :=
  Finsupp.supported ℂ ℂ {X : sepAll | X.1.length = k}
theorem toFree_mem_homogeneous {X : FnList} {k : ℕ} (hlen : X.length = k) :
    toFree X ∈ homogeneous k := by
  by_cases hX : X ∈ sepAll
  · rw [toFree_of_mem hX]
    exact Finsupp.single_mem_supported ℂ 1 hlen
  · simp [toFree, hX]
theorem length_eq_of_mem_homogeneous {k : ℕ} {F : FreeSep} (hF : F ∈ homogeneous k) {X : sepAll}
    (hX : X ∈ F.support) : X.1.length = k :=
  (Finsupp.mem_supported ℂ F).1 hF hX
theorem complexTuple_mem_homogeneous {n : ℕ} (f : Fin n → R4 → ℂ) :
    complexTuple f ∈ homogeneous n := by
  unfold complexTuple
  split_ifs
  · exact toFree_mem_homogeneous (List.length_ofFn ..)
  · exact Submodule.sum_mem _ fun ε _ =>
      Submodule.smul_mem _ _ (toFree_mem_homogeneous (List.length_ofFn ..))
theorem freeMul_mem_homogeneous {n : ℕ} {F G : FreeSep} (hF : F ∈ homogeneous 1)
    (hG : G ∈ homogeneous n) : freeMul F G ∈ homogeneous (n + 1) := by
  rw [freeMul_apply]
  refine Submodule.sum_mem _ fun X hX => Submodule.sum_mem _ fun Y hY =>
    Submodule.smul_mem _ _ (toFree_mem_homogeneous ?_)
  change (X.1 ++ Y.1).length = n + 1
  rw [List.length_append, length_eq_of_mem_homogeneous hF hX, length_eq_of_mem_homogeneous hG hY,
    Nat.add_comm]
theorem tensorComp_apply_eq_sum (q : ℕ) (K : FreeSep) (y : TestSpaces.PointTuple q) :
    tensorComp q K y = ∑ X ∈ K.support, K X * tensorAt q X y := by
  simp [tensorComp, liftLin, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
theorem tensorComp_eq_zero_of_ne {k q : ℕ} (hq : q ≠ k) {F : FreeSep} (hF : F ∈ homogeneous k) :
    tensorComp q F = 0 := by
  funext y
  rw [tensorComp_apply_eq_sum]
  refine Finset.sum_eq_zero fun X hX => ?_
  rw [tensorAt_of_length_ne X fun e => hq (e.symm.trans (length_eq_of_mem_homogeneous hF hX))]
  simp
theorem tensorAt_append {n : ℕ} (X Y Z : sepAll) (hX : X.1.length = 1)
    (hY : Y.1.length = n) (hZ : Z.1 = listAppend X.1 Y.1) (x : TestSpaces.PointTuple (n + 1)) :
    tensorAt (n + 1) Z x =
      tensorAt 1 X (fun _ => x 0) * tensorAt n Y fun i => x i.succ := by
  obtain ⟨X, hXs⟩ := X
  obtain ⟨Z, hZs⟩ := Z
  dsimp only at hX hZ
  obtain ⟨f, rfl⟩ := List.length_eq_one_iff.1 hX
  obtain rfl := hZ
  have hZl : (listAppend [f] Y.1).length = n + 1 := by
    change (f :: Y.1).length = n + 1
    rw [List.length_cons, hY]
  rw [tensorAt_of_length _ hZl, tensorAt_of_length _ hX, tensorAt_of_length Y hY,
    tensorOfFns_apply, tensorOfFns_apply, tensorOfFns_apply, Fin.prod_univ_succ,
    Fin.prod_univ_one]
  congr 1
theorem tensorComp_freeMul {n : ℕ} {F G : FreeSep} (hF : F ∈ homogeneous 1)
    (hG : G ∈ homogeneous n)
    (hsep : ∀ X ∈ F.support, ∀ Y ∈ G.support, listAppend X.1 Y.1 ∈ sepAll)
    (x : TestSpaces.PointTuple (n + 1)) :
    tensorComp (n + 1) (freeMul F G) x =
      tensorComp 1 F (fun _ => x 0) * tensorComp n G fun i => x i.succ := by
  rw [tensorComp_apply_eq_sum 1, tensorComp_apply_eq_sum n, Finset.sum_mul_sum, freeMul_apply]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun X hX => Finset.sum_congr rfl fun Y hY => ?_
  rw [show toFree (listAppend X.1 Y.1) =
      toFree (⟨listAppend X.1 Y.1, hsep X hX Y hY⟩ : sepAll).1 from rfl,
    tensorComp_toFree,
    tensorAt_append X Y _ (length_eq_of_mem_homogeneous hF hX)
      (length_eq_of_mem_homogeneous hG hY) rfl]
  ring
theorem freeMul_mem_finCombIn {O : Set R4} {F G : FreeSep} (hF : F ∈ finCombIn O)
    (hG : G ∈ finCombIn O)
    (hsep : ∀ X ∈ F.support, ∀ Y ∈ G.support, listAppend X.1 Y.1 ∈ sepAll) :
    freeMul F G ∈ finCombIn O := by
  rw [freeMul_apply]
  refine Submodule.sum_mem _ fun X hX => Submodule.sum_mem _ fun Y hY =>
    Submodule.smul_mem _ _ ?_
  rw [toFree_of_mem (hsep X hX Y hY)]
  refine Finsupp.single_mem_supported ℂ 1 ⟨hsep X hX Y hY, fun f hf => ?_⟩
  rcases List.mem_append.1 hf with hf | hf
  · exact ((Finsupp.mem_supported ℂ F).1 hF hX).2 f hf
  · exact ((Finsupp.mem_supported ℂ G).1 hG hY).2 f hf
theorem complexTuple_facts (entries : TupleRules.ComplexTupleRules) {O : Set R4}
    (hO : IsOpen O) {n : ℕ} {hs : Fin n → R4 → ℂ} (mem : ∀ l, hs l ∈ C1c ℂ)
    (disj : Pairwise fun k l => Disjoint (supp (hs k)) (supp (hs l)))
    (sub : ∀ l, supp (hs l) ⊆ O) :
    complexTuple hs ∈ finCombIn O ∧
      combSupp (complexTuple hs) ⊆ ⋃ l, supp (hs l) ∧
      tensorComp n (complexTuple hs) = tensorOfFns hs := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [complexTuple_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [toFree_of_mem nil_mem_sepAll]
      exact Finsupp.single_mem_supported ℂ 1 ⟨nil_mem_sepAll, fun _ hf => by cases hf⟩
    · intro x hx
      simp only [combSupp, Set.mem_iUnion] at hx
      obtain ⟨X, hX, f, hf, -⟩ := hx
      rw [toFree_of_mem nil_mem_sepAll] at hX
      have hX' : X = ⟨[], nil_mem_sepAll⟩ := by simpa using Finsupp.support_single_subset hX
      subst hX'
      simp at hf
    · rw [show toFree [] = toFree (⟨[], nil_mem_sepAll⟩ : sepAll).1 from rfl,
        tensorComp_toFree, tensorAt_of_length (n := 0) (⟨[], nil_mem_sepAll⟩ : sepAll) rfl]
      funext x
      simp [tensorOfFns_apply]
  · obtain ⟨a, b, c, -⟩ := entries O hO 1 n hs ⟨hn, mem, disj⟩ sub
    exact ⟨a, b, c⟩
theorem translTuple_of_components (entries : TupleRules.ComplexTupleRules)
    (z : R4) {n : ℕ} {hs : Fin n → R4 → ℂ} (mem : ∀ l, hs l ∈ C1c ℂ)
    (disj : Pairwise fun k l => Disjoint (supp (hs k)) (supp (hs l))) :
    TranslTuple z hs := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold TranslTuple
    rw [complexTuple_zero, complexTuple_zero]
    exact liftLin_toFree _ (⟨[], nil_mem_sepAll⟩ : sepAll)
  · exact (entries Set.univ isOpen_univ _ n hs ⟨hn, mem, disj⟩
      fun _ => Set.subset_univ _).2.2.2.2.2.2.1
theorem reImPart_mem (parts : TupleRules.ReImAndMotionOfFns) (ε : Fin 2)
    {g : R4 → ℂ} (hg : g ∈ C1c ℂ) :
    reOrImPart ε g ∈ C1c ℝ ∧ supp (reOrImPart ε g) ⊆ supp g := by
  obtain ⟨hre, him, hsub, -⟩ := parts ⟨1, le_rfl⟩ 1 1 g hg
  by_cases hε : ε = 0
  · have e : reOrImPart ε g = fun x => (g x).re := by simp [reOrImPart, hε]
    rw [e]
    exact ⟨hre, Set.subset_union_left.trans hsub⟩
  · have e : reOrImPart ε g = fun x => (g x).im := by simp [reOrImPart, hε]
    rw [e]
    exact ⟨him, Set.subset_union_right.trans hsub⟩
def reImList {n : ℕ} (g : Fin n → R4 → ℂ) (ε : Fin n → Fin 2) : FnList :=
  List.ofFn fun l => reOrImPart (ε l) (g l)
theorem reImList_mem (parts : TupleRules.ReImAndMotionOfFns) {n : ℕ}
    {g : Fin n → R4 → ℂ} (mem : ∀ l, g l ∈ C1c ℂ)
    (disj : Pairwise fun k l => Disjoint (supp (g k)) (supp (g l)))
    (ε : Fin n → Fin 2) : reImList g ε ∈ sepAll := by
  refine Set.mem_iUnion.2 ⟨n, List.length_ofFn .., ?_, ?_⟩
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact (reImPart_mem parts _ (mem l)).1
  · refine List.pairwise_ofFn.2 fun k l hkl => ?_
    exact (disj hkl.ne).mono (reImPart_mem parts _ (mem k)).2 (reImPart_mem parts _ (mem l)).2
theorem reImList_cons {n : ℕ} (g : R4 → ℂ) (hs : Fin n → R4 → ℂ) (a : Fin 2)
    (ε : Fin n → Fin 2) :
    reImList (consEntries g hs) (Fin.cons a ε) =
      listAppend (reImList (fun _ : Fin 1 => g) fun _ => a) (reImList hs ε) := by
  simp [reImList, consEntries, List.ofFn_succ, listAppend,
    ReflectionPositivity.AxisMirror.Ambient.append]
  rfl
theorem complexTuple_of_real {n : ℕ} {g : Fin n → R4 → ℂ} (hr : ∀ l, IsRealValued (g l)) :
    complexTuple g = toFree (reImList g 0) := by
  rw [complexTuple, if_pos hr]
  congr 1
theorem complexTuple_of_not_real {n : ℕ} {g : Fin n → R4 → ℂ}
    (hr : ¬ ∀ l, IsRealValued (g l)) :
    complexTuple g = ∑ ε ∈ admissibleSigns g,
      (Complex.I ^ ∑ l, (ε l : ℕ)) • toFree (reImList g ε) := by
  rw [complexTuple, if_neg hr]
  rfl
theorem sum_admissibleSigns_cons {n : ℕ} {g : R4 → ℂ} (hs : Fin n → R4 → ℂ)
    (hnr : ¬ IsRealValued g) (φ : (Fin (n + 1) → Fin 2) → FreeSep) :
    ∑ ε ∈ admissibleSigns (consEntries g hs), φ ε =
      ∑ a ∈ admissibleSigns (fun _ : Fin 1 => g), ∑ ε ∈ admissibleSigns hs,
        φ (Fin.cons (a 0) ε) := by
  refine Eq.trans ?_ (Finset.sum_product' (admissibleSigns fun _ : Fin 1 => g) (admissibleSigns hs)
    fun a ε => φ (Fin.cons (a 0) ε))
  refine Finset.sum_nbij' (fun ε => ((fun _ => ε 0), Fin.tail ε))
    (fun p => Fin.cons (p.1 0) p.2) ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    simp only [admissibleSigns, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hε ⊢
    exact ⟨fun _ hr => absurd hr hnr, fun l hr => hε l.succ hr⟩
  · rintro ⟨a, ε⟩ hp
    simp only [admissibleSigns, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    intro l
    exact Fin.cases (fun hr => absurd hr hnr) (fun l hr => hp.2 l hr) l
  · intro ε _
    exact Fin.cons_self_tail ε
  · rintro ⟨a, ε⟩ _
    refine Prod.ext (funext fun l => ?_) (funext fun l => rfl)
    rw [Subsingleton.elim l 0]
    rfl
  · intro ε _
    simp [Fin.cons_self_tail]
section HeadAndTail
variable {n : ℕ} {h : R4 → ℂ} {hs : Fin n → R4 → ℂ}
theorem head_mem_C1c (H : ComplexComponents (consEntries h hs)) : h ∈ C1c ℂ :=
  H.mem 0
theorem tail_mem_C1c (H : ComplexComponents (consEntries h hs)) (l : Fin n) :
    hs l ∈ C1c ℂ :=
  H.mem l.succ
theorem tail_pairwise_disjoint (H : ComplexComponents (consEntries h hs)) :
    Pairwise fun k l => Disjoint (supp (hs k)) (supp (hs l)) :=
  fun _ _ hkl => H.disjoint fun e => hkl (Fin.succ_injective _ e)
theorem head_disjoint_tail (H : ComplexComponents (consEntries h hs)) (l : Fin n) :
    Disjoint (supp h) (supp (hs l)) :=
  H.disjoint (Fin.succ_ne_zero l).symm
theorem const_pairwise_disjoint :
    Pairwise fun k l : Fin 1 => Disjoint (supp ((fun _ => h) k)) (supp ((fun _ => h) l)) :=
  fun k l hkl => (hkl (Subsingleton.elim k l)).elim
theorem mulDefined_single_tuple (entries : TupleRules.ComplexTupleRules)
    (H : ComplexComponents (consEntries h hs)) :
    MulDefined (singleComponent h) (complexTuple hs) := by
  have s₁ := (complexTuple_facts entries isOpen_univ (hs := fun _ : Fin 1 => h)
    (fun _ => head_mem_C1c H) const_pairwise_disjoint fun _ => Set.subset_univ _).2.1
  have s₂ := (complexTuple_facts entries isOpen_univ (tail_mem_C1c H) (tail_pairwise_disjoint H)
    fun _ => Set.subset_univ _).2.1
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨_, hx⟩ := Set.mem_iUnion.1 (s₁ hx)
  obtain ⟨l, hx'⟩ := Set.mem_iUnion.1 (s₂ hx')
  exact Set.disjoint_left.1 (head_disjoint_tail H l) hx hx'
theorem sameComponents_of_rules (entries : TupleRules.ComplexTupleRules)
    (sep : TupleRules.SupportListsOfMulSeparated)
    (H : ComplexComponents (consEntries h hs)) : SameComponents h hs := by
  have hdef := mulDefined_single_tuple entries H
  have A := complexTuple_mem_homogeneous (fun _ : Fin 1 => h)
  have B := complexTuple_mem_homogeneous hs
  have hmul : singleMulTuple h hs ∈ homogeneous (n + 1) := freeMul_mem_homogeneous A B
  have hcons : consTuple h hs ∈ homogeneous (n + 1) := complexTuple_mem_homogeneous _
  have hT₁ := (complexTuple_facts entries isOpen_univ (hs := fun _ : Fin 1 => h)
    (fun _ => head_mem_C1c H) const_pairwise_disjoint fun _ => Set.subset_univ _).2.2
  have hTₙ := (complexTuple_facts entries isOpen_univ (tail_mem_C1c H) (tail_pairwise_disjoint H)
    fun _ => Set.subset_univ _).2.2
  have hTl : tensorComp (n + 1) (consTuple h hs) = tensorOfFns (consEntries h hs) :=
    (complexTuple_facts entries isOpen_univ H.mem H.disjoint fun _ => Set.subset_univ _).2.2
  have hTc : tensorComp (n + 1) (singleMulTuple h hs) = tensorOfFns (consEntries h hs) := by
    funext x
    change tensorComp (n + 1) (freeMul (complexTuple fun _ : Fin 1 => h)
      (complexTuple hs)) x = _
    rw [tensorComp_freeMul A B (sep _ _ hdef), hT₁, hTₙ, tensorOfFns_apply,
      tensorOfFns_apply, tensorOfFns_apply, Fin.prod_univ_one, Fin.prod_univ_succ]
    rfl
  refine ⟨hdef, (sameTensors_iff _ _).2 fun q => ?_,
    ⟨hTc, fun q hq => tensorComp_eq_zero_of_ne hq hmul⟩,
    ⟨hTl, fun q hq => tensorComp_eq_zero_of_ne hq hcons⟩⟩
  by_cases hq : q = n + 1
  · subst hq
    rw [hTc, hTl]
  · rw [tensorComp_eq_zero_of_ne hq hmul, tensorComp_eq_zero_of_ne hq hcons]
theorem equalCases_of_components (parts : TupleRules.ReImAndMotionOfFns)
    (H : ComplexComponents (consEntries h hs)) : EqualCases h hs := by
  rintro (rfl | hr | ⟨h₁, h₂⟩)
  · have e : consEntries h hs = fun _ => h := by
      funext l
      rw [show l = 0 from Subsingleton.elim (α := Fin 1) l 0]
      rfl
    rw [singleMulTuple, consTuple, complexTuple_zero, freeMul_toFree_nil, e]
    rfl
  · have hr₀ : IsRealValued h := hr 0
    have hrs : ∀ l, IsRealValued (hs l) := fun l => hr l.succ
    have e : (0 : Fin (n + 1) → Fin 2) = Fin.cons 0 0 := by
      funext l
      refine Fin.cases ?_ (fun _ => ?_) l <;> rfl
    have hsep₁ := reImList_mem parts (g := fun _ : Fin 1 => h) (fun _ => head_mem_C1c H)
      const_pairwise_disjoint 0
    have hsep₂ := reImList_mem parts (tail_mem_C1c H) (tail_pairwise_disjoint H) 0
    rw [singleMulTuple, consTuple, singleComponent,
      complexTuple_of_real (g := fun _ : Fin 1 => h) (fun _ => hr₀), complexTuple_of_real hrs,
      complexTuple_of_real hr, freeMul_toFree hsep₁ hsep₂, e, reImList_cons]
    rfl
  · have h₃ : ¬ ∀ l : Fin 1, IsRealValued ((fun _ => h) l) := fun r => h₁ (r 0)
    have h₄ : ¬ ∀ l, IsRealValued (consEntries h hs l) := fun r => h₁ (r 0)
    rw [singleMulTuple, consTuple, singleComponent, complexTuple_of_not_real h₃,
      complexTuple_of_not_real h₂, complexTuple_of_not_real h₄, sum_admissibleSigns_cons hs h₁,
      map_sum freeMul, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum (freeMul _)]
    refine Finset.sum_congr rfl fun ε _ => ?_
    have ha : a = fun _ => a 0 := by
      funext l
      rw [Subsingleton.elim l 0]
    have hexp : (∑ l, ((Fin.cons (a 0) ε : Fin (n + 1) → Fin 2) l : ℕ)) =
        (∑ l, (a l : ℕ)) + ∑ l, (ε l : ℕ) := by
      simp [Fin.sum_univ_succ]
    rw [map_smul freeMul, LinearMap.smul_apply, map_smul (freeMul _),
      freeMul_toFree (reImList_mem parts (fun _ => head_mem_C1c H) const_pairwise_disjoint a)
        (reImList_mem parts (tail_mem_C1c H) (tail_pairwise_disjoint H) ε),
      reImList_cons, ← ha, smul_smul, hexp, pow_add]
end HeadAndTail
theorem tupleFacts_holds (tuples : TupleRules.TupleSpanActionRules)
    (plates : TranslationRules.TranslationAndMotionFacts)
    (height : HeightTuples.HeightTuplesLemma) : TupleFacts := by
  obtain ⟨parts, -, action, sep, -, rules, -, entries, -⟩ := tuples
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const (continuous_apply 3)
  refine ⟨fun n h hs z H => ?_, fun z z' => ?_, ?_⟩
  · have hcomp := sameComponents_of_rules entries sep H
    have same := hcomp.2.1
    refine ⟨translTuple_of_components entries z (tail_mem_C1c H) (tail_pairwise_disjoint H), hcomp,
      equalCases_of_components parts H, fun m S σ => ?_, fun hsub => ?_⟩
    · exact ((height 1 one_pos).2.2 m S σ).1.1 _ _ same
    · have hone := (complexTuple_facts entries hopen (hs := fun _ : Fin 1 => h)
        (fun _ => head_mem_C1c H) const_pairwise_disjoint fun _ => hsub 0).1
      have htail := (complexTuple_facts entries hopen (tail_mem_C1c H) (tail_pairwise_disjoint H)
        fun l => hsub l.succ).1
      have hlong := (complexTuple_facts entries hopen H.mem H.disjoint hsub).1
      have hmul := freeMul_mem_finCombIn hone htail
        (sep _ _ (mulDefined_single_tuple entries H))
      exact ⟨hmul, hlong, fun m S σ =>
        (((height 1 one_pos).2.2 m S σ).1.2.1 _ hmul _ hlong same).2⟩
  · refine ⟨fun F => ?_, fun F F' hF => ?_⟩
    · have e : EuclidMotion.transl z * EuclidMotion.transl z' = EuclidMotion.transl (z + z') :=
        EuclidMotion.ext_of_apply fun x => by
          rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
            EuclidMotion.transl_apply, add_comm z z', add_assoc]
      rw [(action (EuclidMotion.transl z) (EuclidMotion.transl z') F).1, e]
    · obtain ⟨-, -, -, hd, he⟩ := rules (EuclidMotion.transl z) F F' hF
      exact ⟨hd, he⟩
  · intro α hα φ hφ
    obtain ⟨-, -, hpl, -⟩ := plates
    exact ⟨(hpl α hα φ hφ).1, fun x hx => ((hpl α hα φ hφ).2 hx).1⟩
end EuclideanFunctionals.TupleConcat
end YangMills.Construction
end
