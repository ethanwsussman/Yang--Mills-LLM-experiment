import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenationProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror TorusMetric MetricNotions
open scoped ComplexConjugate
namespace EuclideanFunctionals.TupleRules
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem supp_subset_of_ne_zero {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜'] {f : R4 → 𝕜} {g : R4 → 𝕜'}
    (hfg : ∀ x, f x ≠ 0 → g x ≠ 0) : supp f ⊆ supp g := fun x hx r hr => by
  obtain ⟨y, hy, hd⟩ := hx r hr
  exact ⟨y, hfg y hy, hd⟩
theorem re_mem_C1c {u : R4 → ℂ} (hu : u ∈ C1c ℂ) :
    (fun x => (u x).re) ∈ C1c ℝ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.re_mem_C1c <;> assumption
theorem im_mem_C1c {u : R4 → ℂ} (hu : u ∈ C1c ℂ) :
    (fun x => (u x).im) ∈ C1c ℝ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.im_mem_C1c <;> assumption
theorem conj_mem_C1c {u : R4 → ℂ} (hu : u ∈ C1c ℂ) :
    (fun x => conj (u x)) ∈ C1c ℂ := by
  rw [mem_C1c_iff] at hu ⊢
  exact ⟨Complex.conjCLE.contDiff.comp hu.1,
    hu.2.comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
theorem supp_re_subset (u : R4 → ℂ) : supp (fun x => (u x).re) ⊆ supp u := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.supp_re_subset <;> assumption
theorem supp_im_subset (u : R4 → ℂ) : supp (fun x => (u x).im) ⊆ supp u := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.supp_im_subset <;> assumption
theorem supp_conj (u : R4 → ℂ) : supp (fun x => conj (u x)) = supp u :=
  Set.Subset.antisymm (supp_subset_of_ne_zero fun x hx h0 => hx (by simp [h0]))
    (supp_subset_of_ne_zero fun x hx h0 => hx (by simpa using h0))
theorem reImPart_mem_C1c (ε : Fin 2) {u : R4 → ℂ} (hu : u ∈ C1c ℂ) :
    reOrImPart ε u ∈ C1c ℝ := by
  rw [reOrImPart]
  split_ifs
  · exact re_mem_C1c hu
  · exact im_mem_C1c hu
theorem supp_reImPart_subset (ε : Fin 2) (u : R4 → ℂ) :
    supp (reOrImPart ε u) ⊆ supp u := by
  rw [reOrImPart]
  split_ifs
  · exact supp_re_subset u
  · exact supp_im_subset u
theorem supp_actFn {𝕜 : Type*} [RCLike 𝕜] (r : EuclidMotion) (f : R4 → 𝕜) :
    supp (r.actFn f) = r '' supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.supp_actFn <;> assumption
theorem sharpNorm_actFn (c : SharpScale) (r : EuclidMotion) (u : R4 → ℂ) :
    c.sharpNorm (r.actFn u) = c.sharpNorm u := by
  have hsup : TestFunctions.uniformNorm (r.actFn u) = TestFunctions.uniformNorm u :=
    (r⁻¹).toPerm.surjective.iSup_comp (fun x => ‖u x‖)
  have hlip : TestFunctions.lipConstR4 (r.actFn u) = TestFunctions.lipConstR4 u := by
    refine congrArg sInf (Set.ext fun C => and_congr Iff.rfl ⟨fun hC x y => ?_, fun hC x y => ?_⟩)
    · have := hC (r x) (r y)
      change ‖u (r⁻¹ (r x)) - u (r⁻¹ (r y))‖ ≤ C * euclidNormVec (r x - r y) at this
      rw [EuclidMotion.inv_apply_apply, EuclidMotion.inv_apply_apply,
        EuclidMotion.euclidNormVec_sub] at this
      exact this
    · have := hC (r⁻¹ x) (r⁻¹ y)
      change ‖u (r⁻¹ x) - u (r⁻¹ y)‖ ≤ C * euclidNormVec (r⁻¹ x - r⁻¹ y) at this
      rw [EuclidMotion.euclidNormVec_sub] at this
      exact this
  simp only [SharpScale.sharpNorm, TestFunctions.sharpNormR4, hsup, hlip]
theorem reImAndMotionOfFns_holds (H : MotionRules.MotionOnFunctions) :
    ReImAndMotionOfFns := by
  intro c r r' u hu
  obtain ⟨a₁, a₂, a₃, a₄, -, a₆⟩ := H r r' u hu
  exact ⟨re_mem_C1c hu, im_mem_C1c hu, Set.union_subset (supp_re_subset u) (supp_im_subset u),
    a₁, a₂, a₃, a₄, a₆.symm, sharpNorm_actFn c r u⟩
theorem actFn_inv_actFn {α : Type*} (r : EuclidMotion) (f : R4 → α) :
    (r⁻¹).actFn (r.actFn f) = f := by apply _root_.YangMills.Construction.EuclideanFunctionals.inv_actFn_actFn <;> assumption
theorem actList_inv_actList (r : EuclidMotion) (X : FnList) : (r⁻¹).actList (r.actList X) = X := by
  simp only [EuclidMotion.actList, List.map_map]
  have hid : (r⁻¹).actFn ∘ r.actFn = (id : (R4 → ℝ) → R4 → ℝ) :=
    funext fun f => actFn_inv_actFn r f
  rw [hid, List.map_id]
theorem toFree_of_not_mem {X : FnList} (hX : X ∉ sepAll) : toFree X = 0 := by
  simp [toFree, hX]
theorem single_eq_smul_toFree (X : sepAll) (z : ℂ) : Finsupp.single X z = z • toFree X.1 := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.single_eq_smul_toFree <;> assumption
theorem actList_mem_sepAll (H : MotionRules.MotionOnLists) (r : EuclidMotion)
    {X : FnList} (hX : X ∈ sepAll) : r.actList X ∈ sepAll :=
  ((H Set.univ isOpen_univ r 1).2.1.mapsTo ⟨hX, fun _ _ => Set.subset_univ _⟩).1
theorem actList_mem_sepAll_iff (H : MotionRules.MotionOnLists)
    (r : EuclidMotion) {X : FnList} : r.actList X ∈ sepAll ↔ X ∈ sepAll :=
  ⟨fun hX => by simpa [actList_inv_actList] using actList_mem_sepAll H r⁻¹ hX,
    actList_mem_sepAll H r⟩
theorem actFree_toFree (H : MotionRules.MotionOnLists) (r : EuclidMotion)
    (T : FnList) : r.actFree (toFree T) = toFree (r.actList T) := by
  by_cases hT : T ∈ sepAll
  · exact liftLin_toFree (fun X : sepAll => toFree (r.actList X.1)) ⟨T, hT⟩
  · rw [toFree_of_not_mem hT, map_zero,
      toFree_of_not_mem (mt (actList_mem_sepAll_iff H r).1 hT)]
def sepAllMap (H : MotionRules.MotionOnLists) (r : EuclidMotion)
    (X : sepAll) : sepAll :=
  ⟨r.actList X.1, actList_mem_sepAll H r X.2⟩
theorem sepAllMap_injective (H : MotionRules.MotionOnLists)
    (r : EuclidMotion) : Function.Injective (sepAllMap H r) := fun X Y hXY => by
  have h' : r.actList X.1 = r.actList Y.1 := congrArg Subtype.val hXY
  apply Subtype.ext
  rw [← actList_inv_actList r X.1, h', actList_inv_actList]
theorem actFree_eq_mapDomain (H : MotionRules.MotionOnLists) (r : EuclidMotion)
    (F : FreeSep) : r.actFree F = Finsupp.mapDomain (sepAllMap H r) F := by
  refine Finsupp.induction_linear F ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [map_add, hf, hg, Finsupp.mapDomain_add]
  · intro X z
    rw [Finsupp.mapDomain_single, single_eq_smul_toFree, map_smul, actFree_toFree H,
      single_eq_smul_toFree (sepAllMap H r X)]
    rfl
theorem mem_combSupp_iff {F : FreeSep} {x : R4} :
    x ∈ combSupp F ↔ ∃ X ∈ F.support, ∃ f ∈ X.1, x ∈ supp f := by
  simp only [combSupp, Set.mem_iUnion, exists_prop]
theorem combSupp_actFree (H : MotionRules.MotionOnLists)
    (r : EuclidMotion) (F : FreeSep) :
    combSupp (r.actFree F) = r '' combSupp F := by
  classical
  have hs : (r.actFree F).support = F.support.image (sepAllMap H r) := by
    rw [actFree_eq_mapDomain H, Finsupp.mapDomain_support_of_injective (sepAllMap_injective H r)]
  ext x
  constructor
  · intro hx
    obtain ⟨Y, hY, g, hg, hxg⟩ := mem_combSupp_iff.1 hx
    rw [hs] at hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    rw [supp_actFn] at hxg
    obtain ⟨z, hz, rfl⟩ := hxg
    exact ⟨z, mem_combSupp_iff.2 ⟨X, hX, f, hf, hz⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨X, hX, f, hf, hzf⟩ := mem_combSupp_iff.1 hz
    refine mem_combSupp_iff.2 ⟨sepAllMap H r X, ?_, r.actFn f,
      List.mem_map.2 ⟨f, hf, rfl⟩, ?_⟩
    · rw [hs]
      exact Finset.mem_image_of_mem _ hX
    · rw [supp_actFn]
      exact ⟨z, hzf, rfl⟩
theorem motionOfListsAndCombs_holds (H : MotionRules.MotionOnLists) :
    MotionOfListsAndCombs := by
  intro r O hO
  obtain ⟨a₁, a₂, a₃, a₄, -⟩ := H O hO r 1
  refine ⟨a₁, fun n => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro X hX
    have hm := a₂.mapsTo hX.2
    exact ⟨⟨(a₃ X hX.2).trans hX.1.1, isSeparatedList_of_mem_sepAll hm.1⟩, hm⟩
  · exact fun X hX Y hY hXY => a₂.injOn hX.2 hY.2 hXY
  · intro Y hY
    obtain ⟨X, hX, rfl⟩ := a₂.surjOn hY.2
    exact ⟨X, ⟨⟨(a₃ X hX).symm.trans hY.1.1, isSeparatedList_of_mem_sepAll hX.1⟩, hX⟩, rfl⟩
  · exact fun X _ => actList_inv_actList r X
  · intro Y _
    simpa using actList_inv_actList r⁻¹ Y
  · rw [finCombIn_eq_freeSpanIn, finCombIn_eq_freeSpanIn]
    exact a₄
theorem transl_inv_apply (z x : R4) : (EuclidMotion.transl z)⁻¹ x = x - z := by
  have h' := EuclidMotion.inv_apply_apply (EuclidMotion.transl z) (x - z)
  rw [EuclidMotion.transl_apply, sub_add_cancel] at h'
  exact h'
theorem motionOnFree_holds (H : MotionRules.MotionOnLists)
    (Hc : TensorCompRules.ConjRule)
    (Hr : TensorCompRules.MotionRule) :
    MotionOnFree := by
  intro r r' F
  obtain ⟨-, -, -, -, a₅, a₆, -⟩ := H Set.univ isOpen_univ r r'
  refine ⟨(a₅ F).symm, a₆ F, combSupp_actFree H r F, (Hc F).1, (Hc F).2,
    (Hr r F).1, (Hr r F).2, fun z => ⟨(Hr _ F).1, fun q hq => ?_⟩⟩
  funext x
  rw [(Hr _ F).2 q hq x]
  exact congrArg (tensorComp q F) (funext fun l => transl_inv_apply z (x l))
theorem freeConj_apply (F : FreeSep) (X : sepAll) : freeConj F X = conj (F X) :=
  Finsupp.mapRange_apply (hf := map_zero _)
theorem freeConj_support (F : FreeSep) : (freeConj F).support = F.support := by
  ext X
  simp [Finsupp.mem_support_iff, freeConj_apply]
theorem combSupp_freeConj (F : FreeSep) :
    combSupp (freeConj F) = combSupp F := by
  rw [combSupp, freeConj_support, combSupp]
theorem freeConj_add (F G : FreeSep) : freeConj (F + G) = freeConj F + freeConj G := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.freeConj_add <;> assumption
theorem freeConj_smul (a : ℂ) (F : FreeSep) : freeConj (a • F) = conj a • freeConj F := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.freeConj_smul <;> assumption
theorem mem_finCombIn_iff {O : Set R4} {F : FreeSep} :
    F ∈ finCombIn O ↔ ∀ X ∈ F.support, X.1 ∈ sepIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.mem_finCombIn_iff <;> assumption
theorem toFree_mem_finCombIn {O : Set R4} {T : FnList} (hT : T ∈ sepIn O) :
    toFree T ∈ finCombIn O := by
  rw [finCombIn_eq_freeSpanIn]
  exact Submodule.subset_span ⟨T, hT, rfl⟩
theorem combSupp_subset {O : Set R4} {F : FreeSep} (hF : F ∈ finCombIn O) :
    combSupp F ⊆ O := fun x hx => by
  obtain ⟨X, hX, f, hf, hxf⟩ := mem_combSupp_iff.1 hx
  exact (mem_finCombIn_iff.1 hF X hX).2 f hf hxf
theorem mem_finCombIn_combSupp (F : FreeSep) :
    F ∈ finCombIn (combSupp F) :=
  mem_finCombIn_iff.2 fun X hX =>
    ⟨X.2, fun f hf _ hx => mem_combSupp_iff.2 ⟨X, hX, f, hf, hx⟩⟩
theorem freeConj_mem_finCombIn {O : Set R4} {F : FreeSep} (hF : F ∈ finCombIn O) :
    freeConj F ∈ finCombIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.freeConj_mem_finCombIn <;> assumption
theorem mem_sepAll_iff {X : FnList} :
    X ∈ sepAll ↔ Ambient.IsSeparatedList defaultMirrorData Ambient.euclidean X :=
  ⟨isSeparatedList_of_mem_sepAll, fun hX => Set.mem_iUnion.2 ⟨_, rfl, hX⟩⟩
theorem mem_sepAll_of_listAppend {T U : FnList} (hTU : listAppend T U ∈ sepAll) :
    T ∈ sepAll ∧ U ∈ sepAll := by
  have h' := isSeparatedList_of_mem_sepAll hTU
  have hp := List.pairwise_append.1 h'.2
  exact ⟨mem_sepAll_iff.2 ⟨fun f hf => h'.1 f (List.mem_append_left _ hf), hp.1⟩,
    mem_sepAll_iff.2 ⟨fun f hf => h'.1 f (List.mem_append_right _ hf), hp.2.1⟩⟩
theorem freeMul_toFree (T U : FnList) :
    freeMul (toFree T) (toFree U) = toFree (listAppend T U) := by
  by_cases hT : T ∈ sepAll
  · by_cases hU : U ∈ sepAll
    · have e : freeMul (toFree T) =
          liftLin (fun Y : sepAll => toFree (listAppend T Y.1)) :=
        liftLin_toFree
          (fun X : sepAll => liftLin fun Y : sepAll => toFree (listAppend X.1 Y.1))
          ⟨T, hT⟩
      rw [e]
      exact liftLin_toFree (fun Y : sepAll => toFree (listAppend T Y.1)) ⟨U, hU⟩
    · rw [toFree_of_not_mem hU, map_zero,
        toFree_of_not_mem fun hTU => hU (mem_sepAll_of_listAppend hTU).2]
  · rw [toFree_of_not_mem hT, map_zero, LinearMap.zero_apply,
      toFree_of_not_mem fun hTU => hT (mem_sepAll_of_listAppend hTU).1]
theorem freeMul_mem_finCombIn {S S' : Set R4} (hd : Disjoint S S') {F A : FreeSep}
    (hF : F ∈ finCombIn S) (hA : A ∈ finCombIn S') :
    freeMul F A ∈ finCombIn (S ∪ S') := by
  rw [freeMul_apply]
  simp only [Finsupp.sum]
  exact Submodule.sum_mem _ fun X hX => Submodule.sum_mem _ fun Y hY =>
    Submodule.smul_mem _ _ (toFree_mem_finCombIn (listAppend_mem_sepIn hd
      (mem_finCombIn_iff.1 hF X hX) (mem_finCombIn_iff.1 hA Y hY)))
theorem combSupp_freeMul_subset {F A : FreeSep} (hFA : MulDefined F A) :
    combSupp (freeMul F A) ⊆ combSupp F ∪ combSupp A :=
  combSupp_subset (freeMul_mem_finCombIn hFA
    (mem_finCombIn_combSupp F) (mem_finCombIn_combSupp A))
theorem supportListsOfMulSeparated_holds : SupportListsOfMulSeparated := by
  intro F A hFA X hX Y hY
  exact (listAppend_mem_sepIn hFA
    (mem_finCombIn_iff.1 (mem_finCombIn_combSupp F) X hX)
    (mem_finCombIn_iff.1 (mem_finCombIn_combSupp A) Y hY)).1
theorem mulOnDisjointOpen_holds : MulOnDisjointOpen := by
  intro O O' _ _ hd
  refine ⟨fun F hF A hA => ⟨?_, freeMul_mem_finCombIn hd hF hA⟩, ?_, ?_⟩
  · exact hd.mono (combSupp_subset hF) (combSupp_subset hA)
  · intro a b F₁ _ F₂ _ A _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · intro a b F _ A₁ _ A₂ _
    simp only [map_add, map_smul]
theorem freeConj_freeMul (F A : FreeSep) :
    freeConj (freeMul F A) = freeMul (freeConj F) (freeConj A) := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.freeConj_freeMul <;> assumption
theorem actList_listAppend (r : EuclidMotion) (X Y : FnList) :
    r.actList (listAppend X Y) = listAppend (r.actList X) (r.actList Y) :=
  List.map_append ..
theorem actFree_freeMul (H : MotionRules.MotionOnLists) (r : EuclidMotion)
    (F A : FreeSep) : r.actFree (freeMul F A) = freeMul (r.actFree F) (r.actFree A) := by
  refine Finsupp.induction_linear F ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, LinearMap.add_apply, hf, hg]
  · intro X z
    refine Finsupp.induction_linear A ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, hf, hg]
    · intro Y w
      simp only [single_eq_smul_toFree, map_smul, LinearMap.smul_apply, freeMul_toFree,
        actFree_toFree H, actList_listAppend]
theorem definedMulRules_holds (H : MotionRules.MotionOnLists) :
    DefinedMulRules := by
  intro r F A hFA
  refine ⟨combSupp_freeMul_subset hFA, ?_, freeConj_freeMul F A, ?_,
    actFree_freeMul H r F A⟩
  · change Disjoint _ _
    rw [combSupp_freeConj, combSupp_freeConj]
    exact hFA
  · change Disjoint _ _
    rw [combSupp_actFree H, combSupp_actFree H]
    exact (Set.disjoint_image_iff r.toPerm.injective).2 hFA
theorem freeMul_assoc (F A A' : FreeSep) :
    freeMul (freeMul F A) A' = freeMul F (freeMul A A') := by
  refine Finsupp.induction_linear F ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, LinearMap.add_apply, hf, hg]
  · intro X a
    refine Finsupp.induction_linear A ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, LinearMap.add_apply, hf, hg]
    · intro Y b
      refine Finsupp.induction_linear A' ?_ ?_ ?_
      · simp
      · intro f g hf hg
        simp only [map_add, hf, hg]
      · intro Z c
        simp only [single_eq_smul_toFree, map_smul, LinearMap.smul_apply, freeMul_toFree]
        have e : listAppend (listAppend X.1 Y.1) Z.1 = listAppend X.1 (listAppend Y.1 Z.1) :=
          List.append_assoc ..
        rw [e]
theorem mulAssoc_holds : MulAssoc := by
  rintro F A A' ⟨h₁, h₂, h₃⟩
  refine ⟨?_, ?_, freeMul_assoc F A A'⟩
  · exact Set.disjoint_of_subset_left (combSupp_freeMul_subset h₁)
      (Set.disjoint_union_left.2 ⟨h₂, h₃⟩)
  · exact Set.disjoint_of_subset_right (combSupp_freeMul_subset h₃)
      (Set.disjoint_union_right.2 ⟨h₁, h₂⟩)
section ComplexComponentsLemmas
variable {n : ℕ} {h : Fin n → R4 → ℂ}
theorem reImParts_mem_sepIn (A : ComplexComponents h) {S : Set R4}
    (hS : ∀ l, supp (h l) ⊆ S) (ε : Fin n → Fin 2) :
    List.ofFn (fun l => reOrImPart (ε l) (h l)) ∈ sepIn S := by
  refine ⟨Set.mem_iUnion.2 ⟨n, List.length_ofFn, ?_, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact reImPart_mem_C1c _ (A.mem l)
  · exact List.pairwise_ofFn.2 fun i j hij =>
      (A.disjoint hij.ne).mono (supp_reImPart_subset _ _) (supp_reImPart_subset _ _)
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact (supp_reImPart_subset _ _).trans (hS l)
theorem complexTuple_mem_finCombIn (A : ComplexComponents h) {S : Set R4}
    (hS : ∀ l, supp (h l) ⊆ S) : complexTuple h ∈ finCombIn S := by
  classical
  rw [complexTuple]
  split_ifs
  · have e : (fun (l : Fin n) (x : R4) => (h l x).re) =
        fun l => reOrImPart ((0 : Fin n → Fin 2) l) (h l) := by
      funext l x
      simp [reOrImPart]
    rw [e]
    exact toFree_mem_finCombIn (reImParts_mem_sepIn A hS 0)
  · exact Submodule.sum_mem _ fun ε _ =>
      Submodule.smul_mem _ _ (toFree_mem_finCombIn (reImParts_mem_sepIn A hS ε))
theorem fullyExpanded_mem_finCombIn (A : ComplexComponents h) {S : Set R4}
    (hS : ∀ l, supp (h l) ⊆ S) : fullyExpanded h ∈ finCombIn S :=
  Submodule.sum_mem _ fun ε _ =>
    Submodule.smul_mem _ _ (toFree_mem_finCombIn (reImParts_mem_sepIn A hS ε))
open Classical in
theorem sum_admissibleSigns (h : Fin n → R4 → ℂ) :
    ∑ ε ∈ admissibleSigns h,
      (Complex.I ^ ∑ l, (ε l : ℕ)) • toFree (List.ofFn fun l => reOrImPart (ε l) (h l)) =
    complexList h := by
  refine Finset.sum_nbij' (fun ε k => ε k.1)
    (fun ε l => if hl : l ∈ nonrealIdx h then ε ⟨l, hl⟩ else 0) ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ => Finset.mem_univ _
  · intro ε _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun l hl => ?_⟩
    have hl' : ∀ x, (h l x).im = 0 := hl
    have : l ∉ nonrealIdx h := by
      simpa [nonrealIdx] using hl'
    simp [this]
  · intro ε hε
    funext l
    by_cases hl : l ∈ nonrealIdx h
    · simp [hl]
    · have hr : IsRealValued (h l) := by
        simpa [nonrealIdx, IsRealValued] using hl
      simp [hl, (Finset.mem_filter.1 hε).2 l hr]
  · intro ε _
    funext k
    simp [k.2]
  · intro ε hε
    have hs : ∑ l, (ε l : ℕ) = imagCount h fun k => ε k.1 := by
      rw [imagCount, Finset.sum_coe_sort (nonrealIdx h) fun l => (ε l : ℕ)]
      refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
      have hr : IsRealValued (h l) := by
        simpa [nonrealIdx, IsRealValued] using hl
      simp [(Finset.mem_filter.1 hε).2 l hr]
    have he : (fun l => reOrImPart (ε l) (h l)) = realPartComponent h fun k => ε k.1 := by
      funext l x
      by_cases hl : l ∈ nonrealIdx h
      · by_cases h0 : ε l = 0 <;> simp [realPartComponent, reOrImPart, hl, h0]
      · have hr : IsRealValued (h l) := by
          simpa [nonrealIdx, IsRealValued] using hl
        simp [realPartComponent, reOrImPart, hl, (Finset.mem_filter.1 hε).2 l hr]
    rw [hs, he]
theorem complexTuple_eq_complexList (h : Fin n → R4 → ℂ) :
    complexTuple h = complexList h := by
  classical
  rw [complexTuple]
  split_ifs with hr
  · have e : h = fun k x => (((h k x).re : ℝ) : ℂ) := by
      funext k x
      exact Complex.ext (by simp) (by simpa using hr k x)
    conv_rhs => rw [e]
    rw [complexList_ofReal fun k x => (h k x).re]
  · exact sum_admissibleSigns h
theorem complexFamily_actFn (H : MotionRules.MotionOnFunctions)
    (A : ComplexComponents h) (r : EuclidMotion) :
    ComplexComponents fun l => r.actFn (h l) :=
  ⟨A.one_le, fun l => (H r 1 (h l) (A.mem l)).1, fun k l hkl => by
    change Disjoint (supp (r.actFn (h k))) (supp (r.actFn (h l)))
    rw [supp_actFn, supp_actFn]
    exact (Set.disjoint_image_iff r.toPerm.injective).2 (A.disjoint hkl)⟩
theorem complexFamily_conj (A : ComplexComponents h) :
    ComplexComponents fun l x => conj (h l x) :=
  ⟨A.one_le, fun l => conj_mem_C1c (A.mem l), fun k l hkl => by
    change Disjoint (supp fun x => conj (h k x)) (supp fun x => conj (h l x))
    rw [supp_conj, supp_conj]
    exact A.disjoint hkl⟩
theorem tensorComp_toFree_ofFn (g : Fin n → R4 → ℝ) (hg : List.ofFn g ∈ sepAll)
    (x : TestSpaces.PointTuple n) :
    tensorComp n (toFree (List.ofFn g)) x = ∏ l, ((g l (x l) : ℝ) : ℂ) := by
  have e : tensorComp n (toFree (List.ofFn g)) = tensorAt n ⟨List.ofFn g, hg⟩ :=
    liftLin_toFree (tensorAt n) ⟨List.ofFn g, hg⟩
  rw [e, tensorAt_of_length _ List.length_ofFn, tensorOfFns_apply]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [cplxEntries]
theorem tensorComp_fullyExpanded (A : ComplexComponents h) :
    tensorComp n (fullyExpanded h) = tensorOfFns h ∧
    tensorCompZero (fullyExpanded h) = 0 ∧
    ∀ q, 1 ≤ q → q ≠ n → tensorComp q (fullyExpanded h) = 0 := by
  have hs : ∀ ε : Fin n → Fin 2, List.ofFn (fun l => reOrImPart (ε l) (h l)) ∈ sepAll :=
    fun ε => (reImParts_mem_sepIn (S := Set.univ) A (fun _ => Set.subset_univ _) ε).1
  refine ⟨?_, ?_, fun q _ hq => ?_⟩
  · funext x
    have hl : ∀ l, h l (x l) =
        ∑ e : Fin 2, Complex.I ^ (e : ℕ) * ((reOrImPart e (h l) (x l) : ℝ) : ℂ) := by
      intro l
      simp [Fin.sum_univ_two, reOrImPart, mul_comm Complex.I]
    rw [tensorOfFns_apply, Finset.prod_congr rfl fun l _ => hl l, Finset.prod_univ_sum,
      Fintype.piFinset_univ, fullyExpanded, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [map_smul, Pi.smul_apply, tensorComp_toFree_ofFn _ (hs ε), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  · rw [fullyExpanded, map_sum]
    refine Finset.sum_eq_zero fun ε _ => ?_
    have e : tensorCompZero (toFree (List.ofFn fun l => reOrImPart (ε l) (h l))) =
        tensorAtZero ⟨_, hs ε⟩ := liftLin_toFree tensorAtZero ⟨_, hs ε⟩
    have hn : n ≠ 0 := by
      have := A.one_le
      omega
    rw [map_smul, e, tensorAtZero]
    simp [hn]
  · rw [fullyExpanded, map_sum]
    refine Finset.sum_eq_zero fun ε _ => ?_
    have e : tensorComp q (toFree (List.ofFn fun l => reOrImPart (ε l) (h l))) =
        tensorAt q ⟨_, hs ε⟩ := liftLin_toFree (tensorAt q) ⟨_, hs ε⟩
    rw [map_smul, e, tensorAt_of_length_ne _ (by simpa using hq.symm), smul_zero]
end ComplexComponentsLemmas
theorem complexTupleRules_holds (H : MotionRules.MotionOnFunctions)
    (Ht : MotionRules.MotionOnLists)
    (Hc : TensorCompRules.ConjRule)
    (Hk : TensorCompRules.ComplexListRule) :
    ComplexTupleRules := by
  intro O hO r n h A hS
  have Ar := complexFamily_actFn H A r
  have Ac := complexFamily_conj A
  have hSc : ∀ l, supp (fun x => conj (h l x)) ⊆ O := fun l => by
    rw [supp_conj]
    exact hS l
  have c₁ := Hk n A.one_le h A.mem A.disjoint
  have c₂ := Hk n A.one_le _ Ac.mem Ac.disjoint
  have e := complexTuple_eq_complexList h
  have ec := complexTuple_eq_complexList fun l x => conj (h l x)
  have x₁ := tensorComp_fullyExpanded A
  have hO' : complexTuple h ∈ finCombIn O := complexTuple_mem_finCombIn A hS
  refine ⟨hO', ?_, ?_, ?_, fun q hq hqn => ?_, Ar, ?_, Ac, freeConj_mem_finCombIn hO',
    complexTuple_mem_finCombIn Ac hSc, ⟨?_, fun q hq => ?_⟩, e,
    fullyExpanded_mem_finCombIn A hS, ⟨?_, fun q hq => ?_⟩⟩
  · exact combSupp_subset
      (complexTuple_mem_finCombIn A fun l => Set.subset_iUnion (fun l => supp (h l)) l)
  · rw [e]
    exact c₁.1
  · rw [e]
    exact c₁.2.1
  · rw [e]
    exact c₁.2.2 q hq hqn
  · rw [e, complexTuple_eq_complexList]
    exact ((Ht O hO r 1).2.2.2.2.2.2 n A.one_le h A.mem A.disjoint hS).2
  · rw [(Hc _).1, e, ec, c₁.2.1, c₂.2.1, map_zero]
  · rw [(Hc _).2 q hq, e, ec]
    by_cases hqn : q = n
    · subst hqn
      rw [c₁.1, c₂.1]
      funext x
      simp only [tensorOfFns_apply, map_prod]
    · rw [c₁.2.2 q hq hqn, c₂.2.2 q hq hqn]
      funext x
      simp
  · rw [x₁.2.1, e, c₁.2.1]
  · rw [e]
    by_cases hqn : q = n
    · subst hqn
      rw [x₁.1, c₁.1]
    · rw [x₁.2.2 q hq hqn, c₁.2.2 q hq hqn]
theorem timeFlipHalfSpaces_holds (Hl : MotionRules.FlipAndGroupLinear)
    (Hh : MotionRules.HalfSpaceImages) : TimeFlipHalfSpaces :=
  ⟨Hl.2.2, fun c => (Hh c 0).1⟩
theorem isOpen_timeAbove (c : ℝ) : IsOpen {x : R4 | c < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem flipConj_mem_finCombIn (H : MotionRules.MotionOnLists)
    (Hh : MotionRules.HalfSpaceImages) (c : ℝ) {F : FreeSep}
    (hF : F ∈ finCombIn {x | c < x 3}) :
    flipConj F ∈ finCombIn {x | x 3 < -c} := by
  have hb := (H _ (isOpen_timeAbove c) timeFlip 1).2.2.2.1
  have hc := freeConj_mem_finCombIn hF
  rw [finCombIn_eq_freeSpanIn] at hc
  have hm := hb.mapsTo (SetLike.mem_coe.2 hc)
  rw [(Hh c 0).1] at hm
  rw [finCombIn_eq_freeSpanIn]
  exact hm
theorem disjoint_timeBelow_timeAbove {c : ℝ} (hc : 0 ≤ c) :
    Disjoint {x : R4 | x 3 < -c} {x | c < x 3} :=
  Set.disjoint_left.2 fun x h₁ h₂ => by
    have h₁' : x 3 < -c := h₁
    have h₂' : c < x 3 := h₂
    linarith
theorem flipConjMulDefined_holds (H : MotionRules.MotionOnLists)
    (Hh : MotionRules.HalfSpaceImages) : FlipConjMulDefined := by
  refine ⟨fun c hc F hF A hA => ⟨flipConj_mem_finCombIn H Hh c hF, ?_⟩,
    fun c hc F hF A hA u hu hs => ?_⟩
  · exact (disjoint_timeBelow_timeAbove hc).mono
      (combSupp_subset (flipConj_mem_finCombIn H Hh c hF))
      (combSupp_subset hA)
  · have Au : ComplexComponents fun _ : Fin 1 => u :=
      ⟨le_rfl, fun _ => hu, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
    have ht : combSupp (complexTuple fun _ : Fin 1 => u) ⊆
        {x | |x 3| < c} :=
      combSupp_subset (complexTuple_mem_finCombIn Au fun _ => hs)
    have hθ := combSupp_subset (flipConj_mem_finCombIn H Hh c hF)
    have hA' := combSupp_subset hA
    refine ⟨?_, (disjoint_timeBelow_timeAbove hc.le).mono hθ hA', ?_⟩
    · refine Set.disjoint_left.2 fun x h₁ h₂ => ?_
      have h₁' : x 3 < -c := hθ h₁
      have h₂' : |x 3| < c := ht h₂
      have := (abs_lt.1 h₂').1
      linarith
    · refine Set.disjoint_left.2 fun x h₁ h₂ => ?_
      have h₁' : |x 3| < c := ht h₁
      have h₂' : c < x 3 := hA' h₂
      have := (abs_lt.1 h₁').2
      linarith
theorem timeStabilizerCommutes_holds
    (Hl : MotionRules.FlipAndGroupLinear)
    (Hs : MotionRules.TimeStabilizerRules) :
    TimeStabilizerCommutes := by
  intro w hw
  obtain ⟨-, h₂, -, h₄⟩ := Hs w hw
  refine ⟨h₄, h₂ 0, fun v α f => ?_⟩
  have hs : w.offset = 0 := Hl.2.1 w hw.1
  funext x
  rw [EuclidMotion.actFn_transl]
  change (EuclidMotion.transl v).actFn f (w⁻¹ x) = f (w⁻¹ (x - w v))
  rw [EuclidMotion.actFn_transl]
  have key : w (w⁻¹ x - v) = x - w v := by
    have h₁ := w.apply_inv_apply x
    simp only [hs, add_zero] at h₁ ⊢
    rw [map_sub, h₁]
  rw [← key, EuclidMotion.inv_apply_apply]
theorem flipConjMulSesquilinear_holds : FlipConjMulSesquilinear := by
  intro c _
  refine ⟨fun a b F₁ _ F₂ _ A _ => ?_, fun a b F _ A₁ _ A₂ _ => ?_⟩
  · simp only [flipConj, freeConj_add, freeConj_smul, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
  · simp only [map_add, map_smul]
theorem tupleSpanActionRules_holds (h₁ : MotionRules.AllRules)
    (h₂ : TensorCompRules.Holds) : TupleSpanActionRules := by
  obtain ⟨-, hF, hT, -, -, -, hL, hH, hS, -⟩ := h₁
  obtain ⟨hC, hI, -, hK⟩ := h₂
  exact ⟨reImAndMotionOfFns_holds hF, motionOfListsAndCombs_holds hT,
    motionOnFree_holds hT hC hI, supportListsOfMulSeparated_holds,
    mulOnDisjointOpen_holds, definedMulRules_holds hT, mulAssoc_holds,
    complexTupleRules_holds hF hT hC hK, timeFlipHalfSpaces_holds hL hH,
    flipConjMulDefined_holds hT hH, timeStabilizerCommutes_holds hL hS,
    flipConjMulSesquilinear_holds⟩
end EuclideanFunctionals.TupleRules
end YangMills.Construction
