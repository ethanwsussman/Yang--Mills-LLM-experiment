import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnlyProof
import YangMills.Construction.EuclideanFunctionals.ConcatenationIsTheTensorProductAndTheFormsInComponents
import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import YangMills.Construction.EuclideanFunctionals.TuplesAboveAHeightTheRestrictionsAgree
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.HeightTuples
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem isOpen_upperAt (c : ℝ) : IsOpen {x : R4 | c < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem finCombIn_mono {O O' : Set R4} (h : O ⊆ O') :
    finCombIn O ≤ finCombIn O' := by
  refine Finsupp.supported_mono ?_
  intro X hX
  exact ⟨hX.1, fun f hf => (hX.2 f hf).trans h⟩
theorem tensorComp_toFree (q : ℕ) {X : FnList} (hX : X ∈ sepAll) :
    tensorComp q (toFree X) = tensorAt q ⟨X, hX⟩ :=
  liftLin_toFree (tensorAt q) ⟨X, hX⟩
theorem tensorComp_single (q : ℕ) (X : sepAll) (a : ℂ) :
    tensorComp q (Finsupp.single X a) = a • tensorAt q X := by
  simp [tensorComp, liftLin]
theorem pairwise_disjoint_supp {X : FnList} (hX : X ∈ sepAll) :
    Pairwise fun k l : Fin X.length => Disjoint (supp (X.get k)) (supp (X.get l)) := by
  have h := List.pairwise_iff_get.1 (isSeparatedList_of_mem_sepAll hX).2
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · exact h k l hlt
  · exact (h l k hlt).symm
theorem get_mem_C1c {X : FnList} (hX : X ∈ sepAll) (k : Fin X.length) :
    X.get k ∈ C1c ℝ :=
  (isSeparatedList_of_mem_sepAll hX).1 _ (List.get_mem X k)
theorem tsupport_tensorOfFns_subset {n : ℕ} (h : Fin n → R4 → ℂ) :
    tsupport (tensorOfFns h) ⊆ Set.pi Set.univ fun l => tsupport (h l) := by
  refine closure_minimal ?_ (isClosed_set_pi fun l _ => isClosed_tsupport _)
  intro x hx l _
  apply subset_tsupport
  intro h0
  apply hx
  rw [tensorOfFns_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ l) h0
theorem hasCompactSupport_tensorOfFns {n : ℕ} (h : Fin n → R4 → ℂ)
    (hh : ∀ l, HasCompactSupport (h l)) : HasCompactSupport (tensorOfFns h) :=
  (isCompact_univ_pi hh).of_isClosed_subset (isClosed_tsupport _) (tsupport_tensorOfFns_subset h)
theorem tsupport_complexify (f : R4 → ℝ) : tsupport (fun x => ((f x : ℝ) : ℂ)) = tsupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorComponents.tsupport_ofReal_comp <;> assumption
theorem hasCompactSupport_tensorAt (q : ℕ) (X : sepAll) :
    HasCompactSupport (tensorAt q X) := by
  by_cases hX : X.1.length = q
  · rw [tensorAt_of_length X hX]
    refine hasCompactSupport_tensorOfFns _ fun l => ?_
    have h := ((mem_C1c_iff _).1 (get_mem_C1c X.2 (Fin.cast hX.symm l))).2
    change IsCompact (tsupport fun x => ((X.1.get (Fin.cast hX.symm l) x : ℝ) : ℂ))
    rw [tsupport_complexify]
    exact h
  · rw [tensorAt_of_length_ne X hX]
    exact HasCompactSupport.zero
theorem hasCompactSupport_tensorComp (q : ℕ) (F : FreeSep) :
    HasCompactSupport (tensorComp q F) := by
  induction F using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact HasCompactSupport.zero
  | add F G hF hG =>
    rw [map_add]
    exact hF.add hG
  | single X a =>
    rw [tensorComp_single]
    exact (hasCompactSupport_tensorAt q X).mono (Function.support_const_smul_subset a _)
theorem exists_tensorComp_eq_zero (F : FreeSep) : ∃ N : ℕ, ∀ q, N < q → tensorComp q F = 0 := by
  induction F using Finsupp.induction_linear with
  | zero => exact ⟨0, fun q _ => map_zero _⟩
  | add F G hF hG =>
    obtain ⟨N, hN⟩ := hF
    obtain ⟨M, hM⟩ := hG
    refine ⟨max N M, fun q hq => ?_⟩
    rw [map_add, hN q (lt_of_le_of_lt (le_max_left _ _) hq),
      hM q (lt_of_le_of_lt (le_max_right _ _) hq), add_zero]
  | single X a =>
    refine ⟨X.1.length, fun q hq => ?_⟩
    rw [tensorComp_single, tensorAt_of_length_ne X hq.ne, smul_zero]
theorem tsupport_tensorComp_subset_upper (c : ℝ) (q : ℕ) {G : FreeSep}
    (hG : G ∈ finCombIn {x | c < x 3}) :
    tsupport (tensorComp q G) ⊆ {x | ∀ l, c < x l 3} := by
  rw [finCombIn_eq_freeSpanIn] at hG
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, hX, rfl⟩ := hG
    rw [tensorComp_toFree q hX.1]
    by_cases hq : X.length = q
    · rw [tensorAt_of_length ⟨X, hX.1⟩ hq]
      intro x hx l
      have h := tsupport_tensorOfFns_subset _ hx l (Set.mem_univ l)
      change x l ∈ tsupport (fun y => ((X.get (Fin.cast hq.symm l) y : ℝ) : ℂ)) at h
      rw [tsupport_complexify, ← supp_eq_tsupport] at h
      exact hX.2 _ (List.get_mem X _) h
    · rw [tensorAt_of_length_ne ⟨X, hX.1⟩ hq]
      simp [tsupport]
  | zero =>
    rw [map_zero]
    simp [tsupport]
  | add F G _ _ hF hG =>
    rw [map_add]
    refine (closure_minimal ((Function.support_add _ _).trans
      (Set.union_subset_union (subset_tsupport _) (subset_tsupport _)))
      ((isClosed_tsupport _).union (isClosed_tsupport _))).trans (Set.union_subset hF hG)
  | smul a F _ hF =>
    rw [map_smul]
    exact (closure_mono (Function.support_const_smul_subset a _)).trans hF
def rampUp (c d t : ℝ) : ℝ := Real.smoothTransition ((t - (c + d / 2)) / (d / 2))
theorem rampUp_eq_one {c d t : ℝ} (hd : 0 < d) (h : c + d ≤ t) : rampUp c d t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))
theorem rampUp_eq_zero {c d t : ℝ} (hd : 0 < d) (h : t ≤ c + d / 2) : rampUp c d t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
theorem contDiff_rampUp (c d : ℝ) : ContDiff ℝ 1 fun x : R4 => rampUp c d (x 3) := by
  unfold rampUp
  exact Real.smoothTransition.contDiff.comp (by fun_prop)
def rampProd (c : ℝ) {q : ℕ} (d : Fin q → ℝ) (x : TestSpaces.PointTuple q) : ℂ :=
  ∏ l, ((rampUp c (d l) (x l 3) : ℝ) : ℂ)
theorem rampProd_mul_tensor_mem (c : ℝ) {q : ℕ} (X : sepAll) (hX : X.1.length = q) (d : Fin q → ℝ)
    (hd : ∀ l, 0 < d l) :
    (fun x => rampProd c d x * tensorOfFns (cplxEntries X.1 hX) x) ∈
      disjointTensorsAbove c q := by
  have hsub : ∀ l, tsupport (fun x : R4 => rampUp c (d l) (x 3) *
      X.1.get (Fin.cast hX.symm l) x) ⊆ tsupport (X.1.get (Fin.cast hX.symm l)) := fun l =>
    closure_mono fun x hx h0 => hx (by simp [h0])
  refine ⟨fun l x => rampUp c (d l) (x 3) * X.1.get (Fin.cast hX.symm l) x, fun l => ?_, ?_, ?_, ?_⟩
  · have h := (mem_C1c_iff _).1 (get_mem_C1c X.2 (Fin.cast hX.symm l))
    exact (mem_C1c_iff _).2 ⟨(contDiff_rampUp c (d l)).mul h.1, h.2.mul_left⟩
  · intro k l hkl
    have h : Disjoint (supp (X.1.get (Fin.cast hX.symm k)))
        (supp (X.1.get (Fin.cast hX.symm l))) := pairwise_disjoint_supp X.2
      (show Fin.cast hX.symm k ≠ Fin.cast hX.symm l from fun e => hkl (Fin.cast_injective _ e))
    rw [supp_eq_tsupport, supp_eq_tsupport] at h ⊢
    exact h.mono (hsub k) (hsub l)
  · intro l
    rw [supp_eq_tsupport]
    have hclosed : IsClosed {x : R4 | c + d l / 2 ≤ x 3} :=
      isClosed_le continuous_const (continuous_apply 3)
    refine (closure_minimal ?_ hclosed).trans ?_
    · intro x hx
      by_contra hlt
      refine hx ?_
      change rampUp c (d l) (x 3) * X.1.get (Fin.cast hX.symm l) x = 0
      rw [rampUp_eq_zero (hd l) (not_le.1 hlt).le, zero_mul]
    · intro x hx
      have := hd l
      have hx' : c + d l / 2 ≤ x 3 := hx
      change c < x 3
      linarith
  · funext x
    rw [tensorOfFns_apply, tensorOfFns_apply, rampProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp [cplxEntries]
theorem rampProd_mul_tensorComp_mem (c : ℝ) {q : ℕ} (d : Fin q → ℝ) (hd : ∀ l, 0 < d l) (F : FreeSep) :
    (fun x => rampProd c d x * tensorComp q F x) ∈ Submodule.span ℂ (disjointTensorsAbove c q) := by
  induction F using Finsupp.induction_linear with
  | zero =>
    have : (fun x => rampProd c d x * tensorComp q (0 : FreeSep) x) = 0 := by
      funext x
      simp
    rw [this]
    exact Submodule.zero_mem _
  | add F G hF hG =>
    have : (fun x => rampProd c d x * tensorComp q (F + G) x) =
        (fun x => rampProd c d x * tensorComp q F x) +
          fun x => rampProd c d x * tensorComp q G x := by
      funext x
      simp [mul_add]
    rw [this]
    exact Submodule.add_mem _ hF hG
  | single X a =>
    have : (fun x => rampProd c d x * tensorComp q (Finsupp.single X a) x) =
        a • fun x => rampProd c d x * tensorAt q X x := by
      funext x
      rw [tensorComp_single]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    refine Submodule.smul_mem _ _ ?_
    by_cases hX : X.1.length = q
    · rw [tensorAt_of_length X hX]
      exact Submodule.subset_span (rampProd_mul_tensor_mem c X hX d hd)
    · rw [tensorAt_of_length_ne X hX]
      have : (fun x => rampProd c d x * (0 : TestSpaces.PointTuple q → ℂ) x) = 0 := by
        funext x
        simp
      rw [this]
      exact Submodule.zero_mem _
theorem exists_gap_above (c : ℝ) {q : ℕ} {K : Set (TestSpaces.PointTuple q)} (hK : IsCompact K)
    (hc : K ⊆ {x | ∀ l, c < x l 3}) (l : Fin q) : ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K, c + d ≤ x l 3 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => hx.elim⟩
  · have hcont : Continuous fun x : TestSpaces.PointTuple q => x l 3 :=
      (continuous_apply 3).comp (continuous_apply l)
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    refine ⟨x₀ l 3 - c, sub_pos.2 (hc hx₀ l), fun x hx => ?_⟩
    have : x₀ l 3 ≤ x l 3 := hmin hx
    linarith
theorem spannedByTensorsAbove_of_supported (c : ℝ) (F : FreeSep) (h : ComponentsSupportedAbove c F) :
    SpannedByTensorsAbove c F := by
  intro q hq
  have hK : IsCompact (tsupport (tensorComp q F)) := hasCompactSupport_tensorComp q F
  choose d hd hmargin using exists_gap_above c hK (h q hq)
  have hmain : tensorComp q F = fun x => rampProd c d x * tensorComp q F x := by
    funext x
    by_cases hx : x ∈ tsupport (tensorComp q F)
    · have : rampProd c d x = 1 := by
        refine Finset.prod_eq_one fun l _ => ?_
        rw [rampUp_eq_one (hd l) (hmargin l x hx)]
        simp
      rw [this, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [hmain]
  exact rampProd_mul_tensorComp_mem c d hd F
theorem exists_lift_of_mem_span (c : ℝ) (q : ℕ) {A : TestSpaces.PointTuple q → ℂ}
    (hA : A ∈ Submodule.span ℂ (disjointTensorsAbove c q)) :
    ∃ G ∈ finCombIn {x | c < x 3}, HasSoleTensorComp q A G := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨f, hf, hdis, habove, rfl⟩ := hA
    have hlen : (List.ofFn f).length = q := List.length_ofFn
    have hL : List.ofFn f ∈ sepIn {x | c < x 3} := by
      refine ⟨Set.mem_iUnion.2 ⟨q, hlen, ?_, ?_⟩, ?_⟩
      · intro g hg
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        exact hf i
      · exact List.pairwise_ofFn.2 fun i j hij => hdis hij.ne
      · intro g hg
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        exact habove i
    refine ⟨toFree (List.ofFn f), ?_, ?_, fun q' hq' => ?_⟩
    · rw [finCombIn_eq_freeSpanIn]
      exact Submodule.subset_span ⟨_, hL, rfl⟩
    · rw [tensorComp_toFree q hL.1, tensorAt_of_length ⟨_, hL.1⟩ hlen]
      congr 1
      funext l x
      simp [cplxEntries]
    · rw [tensorComp_toFree q' hL.1, tensorAt_of_length_ne ⟨_, hL.1⟩]
      intro e
      exact hq' (e.symm.trans hlen)
  | zero =>
    exact ⟨0, Submodule.zero_mem _, map_zero _, fun _ _ => map_zero _⟩
  | add A B _ _ hA hB =>
    obtain ⟨G, hG, hG₁, hG₂⟩ := hA
    obtain ⟨G', hG', hG₁', hG₂'⟩ := hB
    refine ⟨G + G', Submodule.add_mem _ hG hG', ?_, fun q' hq' => ?_⟩
    · rw [map_add, hG₁, hG₁']
    · rw [map_add, hG₂ q' hq', hG₂' q' hq', add_zero]
  | smul a A _ hA =>
    obtain ⟨G, hG, hG₁, hG₂⟩ := hA
    refine ⟨a • G, Submodule.smul_mem _ _ hG, ?_, fun q' hq' => ?_⟩
    · rw [map_smul, hG₁]
    · rw [map_smul, hG₂ q' hq', smul_zero]
theorem nil_mem_sepIn (O : Set R4) : ([] : FnList) ∈ sepIn O :=
  ⟨Set.mem_iUnion.2 ⟨0, rfl, fun _ hf => absurd hf List.not_mem_nil, List.Pairwise.nil⟩,
    fun _ hf => absurd hf List.not_mem_nil⟩
theorem componentsMatchAbove_of_spanned (c : ℝ) (F : FreeSep) (h : SpannedByTensorsAbove c F) :
    ComponentsMatchAbove c F := by
  classical
  obtain ⟨N, hN⟩ := exists_tensorComp_eq_zero F
  have hG : ∀ q : ℕ, ∃ G, 1 ≤ q → G ∈ finCombIn {x | c < x 3} ∧
      HasSoleTensorComp q (tensorComp q F) G := by
    intro q
    by_cases hq : 1 ≤ q
    · obtain ⟨G, h₁, h₂⟩ := exists_lift_of_mem_span c q (h q hq)
      exact ⟨G, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose G hG using hG
  have hEmpty := nil_mem_sepIn {x : R4 | c < x 3}
  have hEmptyMem : toFree [] ∈ finCombIn {x : R4 | c < x 3} := by
    rw [finCombIn_eq_freeSpanIn]
    exact Submodule.subset_span ⟨_, hEmpty, rfl⟩
  have e : TestSpaces.PointTuple 0 := fun i => i.elim0
  refine ⟨tensorCompZero F • toFree [] + ∑ q ∈ Finset.Icc 1 N, G q,
    Submodule.add_mem _ (Submodule.smul_mem _ _ hEmptyMem)
      (Submodule.sum_mem _ fun q hq => (hG q (Finset.mem_Icc.1 hq).1).1), ?_, fun n hn => ?_⟩
  · have h₁ : tensorCompZero (toFree []) = 1 := by
      have := liftLin_toFree tensorAtZero ⟨[], hEmpty.1⟩
      simpa [tensorCompZero, tensorAtZero, tensorOfNil] using this
    have h₂ : ∀ q ∈ Finset.Icc 1 N, tensorCompZero (G q) = 0 := by
      intro q hq
      have hq₁ := (Finset.mem_Icc.1 hq).1
      rw [← tensorComp_zero_apply (G q) e, (hG q hq₁).2.2 0 (by omega)]
      rfl
    rw [map_add, map_smul, map_sum, Finset.sum_eq_zero h₂, h₁]
    simp
  · rw [map_add, map_smul, map_sum, tensorComp_toFree n hEmpty.1,
      tensorAt_of_length_ne ⟨[], hEmpty.1⟩ (by simp; omega), smul_zero, zero_add]
    by_cases hnN : n ≤ N
    · rw [Finset.sum_eq_single n]
      · exact (hG n hn).2.1
      · intro q hq hne
        exact (hG q (Finset.mem_Icc.1 hq).1).2.2 n hne.symm
      · intro hn'
        exact absurd (Finset.mem_Icc.2 ⟨hn, hnN⟩) hn'
    · rw [hN n (by omega)]
      refine Finset.sum_eq_zero fun q hq => (hG q (Finset.mem_Icc.1 hq).1).2.2 n ?_
      have := (Finset.mem_Icc.1 hq).2
      omega
theorem heightConditionsEquiv_holds (c : ℝ) : HeightConditionsEquiv c := by
  intro F _
  have h₁₃ : ComponentsMatchAbove c F → ComponentsSupportedAbove c F := by
    rintro ⟨G, hG, hGF⟩ q _
    rw [← hGF.2 q ‹_›]
    exact tsupport_tensorComp_subset_upper c q hG
  exact ⟨⟨fun h => spannedByTensorsAbove_of_supported c F (h₁₃ h), componentsMatchAbove_of_spanned c F⟩,
    ⟨h₁₃, fun h => componentsMatchAbove_of_spanned c F (spannedByTensorsAbove_of_supported c F h)⟩⟩
theorem sameTensors_refl (F : FreeSep) : SameTensors F F := ⟨rfl, fun _ _ => rfl⟩
theorem sameTensors_symm {F G : FreeSep} (h : SameTensors F G) : SameTensors G F :=
  ⟨h.1.symm, fun n hn => (h.2 n hn).symm⟩
theorem sameTensors_trans {F G K : FreeSep} (h : SameTensors F G)
    (h' : SameTensors G K) : SameTensors F K :=
  ⟨h.1.trans h'.1, fun n hn => (h.2 n hn).trans (h'.2 n hn)⟩
theorem sameTensors_add {F F' G G' : FreeSep} (h : SameTensors F F')
    (h' : SameTensors G G') : SameTensors (F + G) (F' + G') :=
  ⟨by rw [map_add, map_add, h.1, h'.1], fun n hn => by rw [map_add, map_add, h.2 n hn, h'.2 n hn]⟩
theorem sameTensors_smul (a : ℂ) {F F' : FreeSep} (h : SameTensors F F') :
    SameTensors (a • F) (a • F') :=
  ⟨by rw [map_smul, map_smul, h.1], fun n hn => by rw [map_smul, map_smul, h.2 n hn]⟩
theorem isNullElem_sub {F G : FreeSep} (h : SameTensors F G) : IsNullElem (F - G) :=
  ⟨by rw [map_sub, h.1, sub_self], fun q hq => by rw [map_sub, h.2 q hq, sub_self]⟩
theorem sameTensors_zero_of_isNullElem {N : FreeSep} (h : IsNullElem N) : SameTensors 0 N :=
  ⟨by rw [map_zero, h.1], fun q hq => by rw [map_zero, h.2 q hq]⟩
theorem sameTensors_flipConj (hAction : TupleRules.MotionOnFree)
    {F G : FreeSep} (h : SameTensors F G) :
    SameTensors (flipConj F) (flipConj G) := by
  obtain ⟨-, -, -, f₄, f₅, -, -, -⟩ := hAction timeFlip 1 F
  obtain ⟨-, -, -, g₄, g₅, -, -, -⟩ := hAction timeFlip 1 G
  obtain ⟨-, -, -, -, -, f₆, f₇, -⟩ := hAction timeFlip 1 (freeConj F)
  obtain ⟨-, -, -, -, -, g₆, g₇, -⟩ := hAction timeFlip 1 (freeConj G)
  refine ⟨?_, fun q hq => ?_⟩
  · change tensorCompZero (timeFlip.actFree (freeConj F)) =
      tensorCompZero (timeFlip.actFree (freeConj G))
    rw [f₆, g₆, f₄, g₄, h.1]
  · funext x
    change tensorComp q (timeFlip.actFree (freeConj F)) x =
      tensorComp q (timeFlip.actFree (freeConj G)) x
    rw [f₇ q hq, g₇ q hq, f₅ q hq, g₅ q hq, h.2 q hq]
theorem sameTensors_transl (hAction : TupleRules.MotionOnFree)
    (z : R4) {F G : FreeSep} (h : SameTensors F G) :
    SameTensors ((EuclidMotion.transl z).actFree F) ((EuclidMotion.transl z).actFree G) := by
  obtain ⟨f₀, f₁⟩ := (hAction 1 1 F).2.2.2.2.2.2.2 z
  obtain ⟨g₀, g₁⟩ := (hAction 1 1 G).2.2.2.2.2.2.2 z
  exact ⟨by rw [f₀, g₀, h.1], fun q hq => by rw [f₁ q hq, g₁ q hq, h.2 q hq]⟩
theorem isNullElem_transl_iff (hAction : TupleRules.MotionOnFree)
    (z : R4) (F : FreeSep) : IsNullElem ((EuclidMotion.transl z).actFree F) ↔ IsNullElem F := by
  obtain ⟨f₀, f₁⟩ := (hAction 1 1 F).2.2.2.2.2.2.2 z
  constructor
  · rintro ⟨h₀, h₁⟩
    refine ⟨by rw [← f₀, h₀], fun q hq => ?_⟩
    funext x
    have h := congrFun (h₁ q hq) fun l => x l + z
    rw [f₁ q hq] at h
    simpa [translateArgs] using h
  · rintro ⟨h₀, h₁⟩
    refine ⟨by rw [f₀, h₀], fun q hq => ?_⟩
    rw [f₁ q hq, h₁ q hq]
    rfl
theorem sameTensors_freeMul
    (hConcat : MulTensor.MulComponents)
    {F F' A A' : FreeSep} (hF : MulDefined F A) (hF' : MulDefined F' A')
    (h₁ : SameTensors F F') (h₂ : SameTensors A A') :
    SameTensors (freeMul F A) (freeMul F' A') := by
  have e₁ := (sameTensors_iff _ _).1 h₁
  have e₂ := (sameTensors_iff _ _).1 h₂
  obtain ⟨a₀, a₁, -⟩ := hConcat F A hF
  obtain ⟨b₀, b₁, -⟩ := hConcat F' A' hF'
  refine ⟨by rw [a₀, b₀, h₁.1, h₂.1], fun r hr => ?_⟩
  rw [a₁ r hr, b₁ r hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [TensorCompRules.splitTerm, e₁, e₂, h₁.1, h₂.1]
theorem actFree_one (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by apply _root_.YangMills.Construction.EuclideanFunctionals.one_actFree <;> assumption
theorem timeVec_three : timeVec 3 = 1 := by
  simp [PeriodicLattice.coordVec]
theorem pullDown_raise (hAction : TupleRules.MotionOnFree) (c : ℝ)
    (A : FreeSep) : pullDown c (raise c A) = A := by
  have e : EuclidMotion.transl ((-c) • timeVec) * EuclidMotion.transl (c • timeVec) = 1 :=
    EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
        EuclidMotion.one_apply]
      simp
  change (EuclidMotion.transl ((-c) • timeVec)).actFree ((EuclidMotion.transl (c • timeVec)).actFree A) = A
  rw [(hAction _ _ A).1, e, actFree_one]
theorem raise_pullDown (hAction : TupleRules.MotionOnFree) (c : ℝ)
    (A : FreeSep) : raise c (pullDown c A) = A := by
  have e : EuclidMotion.transl (c • timeVec) * EuclidMotion.transl ((-c) • timeVec) = 1 :=
    EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, EuclidMotion.transl_apply,
        EuclidMotion.one_apply]
      simp
  change (EuclidMotion.transl (c • timeVec)).actFree ((EuclidMotion.transl ((-c) • timeVec)).actFree A) = A
  rw [(hAction _ _ A).1, e, actFree_one]
theorem image_transl_upperHalf (c : ℝ) :
    (fun x => EuclidMotion.transl (c • timeVec) x) '' upperHalf = {x | c < x 3} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : 0 < y 3 := hy
    change c < (y + c • timeVec) 3
    simp only [Pi.add_apply, Pi.smul_apply, timeVec_three, smul_eq_mul, mul_one]
    linarith
  · intro hx
    have hx' : c < x 3 := hx
    refine ⟨x - c • timeVec, ?_, ?_⟩
    · change 0 < (x - c • timeVec) 3
      simp only [Pi.sub_apply, Pi.smul_apply, timeVec_three, smul_eq_mul, mul_one]
      linarith
    · change x - c • timeVec + c • timeVec = x
      simp
theorem raise_bijOn (hImages : TupleRules.MotionOfListsAndCombs) (c : ℝ) :
    Set.BijOn (raise c) (finCombIn upperHalf : Set FreeSep)
      (finCombIn {x | c < x 3} : Set FreeSep) := by
  have h := (hImages (EuclidMotion.transl (c • timeVec)) upperHalf (isOpen_upperAt 0)).2.2
  rw [image_transl_upperHalf] at h
  exact h
def liftedSubmodule (c : ℝ) : Submodule ℂ FreeSep where
  carrier := liftedSet c
  add_mem' := by
    rintro F G ⟨hF, F', hF', hFF⟩ ⟨hG, G', hG', hGG⟩
    exact ⟨Submodule.add_mem _ hF hG, F' + G', Submodule.add_mem _ hF' hG',
      sameTensors_add hFF hGG⟩
  zero_mem' := ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, sameTensors_refl 0⟩
  smul_mem' := by
    rintro a F ⟨hF, F', hF', hFF⟩
    exact ⟨Submodule.smul_mem _ _ hF, a • F', Submodule.smul_mem _ _ hF',
      sameTensors_smul a hFF⟩
theorem liftedSubspace_holds (hImages : TupleRules.MotionOfListsAndCombs)
    (hAction : TupleRules.MotionOnFree) {c : ℝ} (hc : 0 < c) :
    LiftedSubspace c := by
  have hAbove : finCombIn {x | c < x 3} ≤ finCombIn upperHalf :=
    finCombIn_mono fun x hx => lt_trans hc hx
  have hBij := raise_bijOn hImages c
  have hPull : ∀ F ∈ finCombIn {x | c < x 3},
      pullDown c F ∈ finCombIn upperHalf := by
    intro F hF
    obtain ⟨A, hA, rfl⟩ := hBij.surjOn hF
    rw [pullDown_raise hAction]
    exact hA
  have hW : finCombIn {x | c < x 3} ≤ liftedSubmodule c :=
    fun F hF => ⟨hAbove hF, F, hF, sameTensors_refl F⟩
  refine ⟨liftedSubmodule c, rfl, hW, fun N hN hNull => ⟨hN, 0, Submodule.zero_mem _,
    sameTensors_zero_of_isNullElem hNull⟩, ?_, fun A _ => (isNullElem_transl_iff hAction _ A).symm,
    fun A hA => hW (hBij.mapsTo hA), fun A _ A' _ => ?_, ?_, fun F hF => ⟨hPull F hF, fun A _ => ?_⟩⟩
  · rintro G ⟨hG, F', hF', hs⟩
    exact ⟨F', hF', G - F', Submodule.sub_mem _ hG (hAbove hF'), isNullElem_sub (sameTensors_symm hs),
      (add_sub_cancel F' G).symm⟩
  · rw [← map_sub]
    exact (isNullElem_transl_iff hAction _ _).symm
  · rintro G ⟨hG, F', hF', hs⟩
    refine ⟨pullDown c F', hPull F' hF', ?_⟩
    rw [raise_pullDown hAction]
    exact isNullElem_sub (sameTensors_symm hs)
  · have e : raise c A - F = raise c (A - pullDown c F) := by
      rw [map_sub, raise_pullDown hAction]
    rw [e]
    exact isNullElem_transl_iff hAction _ _
section Functional
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
theorem reconClass_of_mem {F : FreeSep} (h : F ∈ finCombIn upperHalf) :
    reconClass σ F = σ.recon.cls ⟨F, h⟩ := by
  simp [reconClass, readClass, h]
theorem formsClassesDependOnComponents_holds (hValues : ValueDependsOnComponents S)
    (hConcat : MulTensor.MulComponents)
    (hAction : TupleRules.MotionOnFree)
    (hRefl : TupleRules.FlipConjMulDefined) : FormsClassesDependOnComponents σ := by
  have hdef : ∀ F ∈ finCombIn upperHalf, ∀ A ∈ finCombIn upperHalf,
      MulDefined (flipConj F) A :=
    fun F hF A hA => (hRefl.1 0 le_rfl F hF A hA).2
  have hLeft : ∀ F' ∈ finCombIn upperHalf, ∀ F'' ∈ finCombIn upperHalf,
      SameTensors F' F'' → ∀ A ∈ finCombIn upperHalf,
        osForm S F' A = osForm S F'' A :=
    fun F' hF' F'' hF'' h A hA => hValues _ _ (sameTensors_freeMul hConcat (hdef F' hF' A hA)
      (hdef F'' hF'' A hA) (sameTensors_flipConj hAction h) (sameTensors_refl A))
  have hRight : ∀ F' ∈ finCombIn upperHalf, ∀ F'' ∈ finCombIn upperHalf,
      SameTensors F' F'' → ∀ A ∈ finCombIn upperHalf,
        osForm S A F' = osForm S A F'' :=
    fun F' hF' F'' hF'' h A hA => hValues _ _ (sameTensors_freeMul hConcat (hdef A hA F' hF')
      (hdef A hA F'' hF'') (sameTensors_refl _) h)
  intro F' hF' F'' hF'' h
  refine ⟨fun A hA => ⟨hLeft F' hF' F'' hF'' h A hA, hRight F' hF' F'' hF'' h A hA⟩, ?_⟩
  rw [reconClass_of_mem σ hF', reconClass_of_mem σ hF'']
  let D : finCombIn upperHalf := ⟨F' - F'', Submodule.sub_mem _ hF' hF''⟩
  have hD : σ.recon.cls ⟨F', hF'⟩ =
      σ.recon.cls D + σ.recon.cls ⟨F'', hF''⟩ := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [D]
  have hD' : σ.recon.cls D =
      σ.recon.cls ⟨F', hF'⟩ - σ.recon.cls ⟨F'', hF''⟩ :=
    eq_sub_of_add_eq hD.symm
  have hzero : σ.recon.cls D = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    nth_rewrite 2 [hD']
    rw [inner_sub_right, σ.recon.inner_cls, σ.recon.inner_cls]
    exact sub_eq_zero.2 (hRight F' hF' F'' hF'' h D.1 D.2)
  rw [hD, hzero, zero_add]
theorem agreeAtHeight_holds (hValues : ValueDependsOnComponents S) (hForms : FormsClassesDependOnComponents σ)
    (hConcat : MulTensor.MulComponents)
    (hAction : TupleRules.MotionOnFree)
    (hRefl : TupleRules.FlipConjMulDefined)
    (hAssoc : TupleRules.MulAssoc) {c : ℝ} (hc : 0 < c)
    (hPull : ∀ F ∈ finCombIn {x | c < x 3},
      pullDown c F ∈ finCombIn upperHalf)
    {F' F'' : FreeSep} (hF' : F' ∈ finCombIn {x | c < x 3})
    (hF'' : F'' ∈ finCombIn {x | c < x 3}) (h : SameTensors F' F'') :
    AgreeAtHeight σ c F' F'' := by
  have hpull : SameTensors (pullDown c F') (pullDown c F'') :=
    sameTensors_transl hAction _ h
  have hcl : reconClass σ (pullDown c F') = reconClass σ (pullDown c F'') :=
    (hForms _ (hPull F' hF') _ (hPull F'' hF'') hpull).2
  refine ⟨hcl, by simp only [heightNorm, hcl], fun A hA k hk hsupp => ⟨?_, ?_⟩⟩
  · have t₁ := hRefl.2 c hc F' hF' A hA k hk hsupp
    have t₂ := hRefl.2 c hc F'' hF'' A hA k hk hsupp
    exact hValues _ _ (sameTensors_freeMul hConcat (hAssoc _ _ _ t₁).1 (hAssoc _ _ _ t₂).1
      (sameTensors_freeMul hConcat t₁.1 t₂.1 (sameTensors_flipConj hAction h)
        (sameTensors_refl _)) (sameTensors_refl A))
  · have t₁ := hRefl.2 c hc A hA F' hF' k hk hsupp
    have t₂ := hRefl.2 c hc A hA F'' hF'' k hk hsupp
    exact hValues _ _ (sameTensors_freeMul hConcat (hAssoc _ _ _ t₁).1 (hAssoc _ _ _ t₂).1
      (sameTensors_refl _) h)
theorem pullDownClassesDense_holds (hAction : TupleRules.MotionOnFree)
    (hImages : TupleRules.MotionOfListsAndCombs) {c : ℝ}
    (hPull : ∀ F ∈ finCombIn {x | c < x 3},
      pullDown c F ∈ finCombIn upperHalf) :
    PullDownClassesDense σ c := by
  refine ⟨?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨_, hPull F hF, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨raise c A, (raise_bijOn hImages c).mapsTo hA, by rw [pullDown_raise hAction]⟩
  · refine Dense.mono ?_ σ.recon.denseRange_cls
    rintro _ ⟨A, rfl⟩
    exact ⟨A.1, A.2, (reconClass_of_mem σ A.2).symm⟩
end Functional
theorem heightTuplesLemma_holds (hComponents : MulTensor.Holds)
    (hCentered : TensorComponents.CenteredSeesTensorComps)
    (hFacts : TupleRules.TupleSpanActionRules) : HeightTuplesLemma := by
  obtain ⟨-, hImages, hAction, -, -, -, hAssoc, -, -, hRefl, -, -⟩ := hFacts
  intro c hc
  refine ⟨heightConditionsEquiv_holds c, liftedSubspace_holds hImages hAction hc, fun m S σ => ?_⟩
  have hConcat := (hComponents m S σ).1
  have hValues : ValueDependsOnComponents S := (hCentered S).2.1
  have hForms := formsClassesDependOnComponents_holds σ hValues hConcat hAction hRefl
  have hAbove : finCombIn {x | c < x 3} ≤ finCombIn upperHalf :=
    finCombIn_mono fun x hx => lt_trans hc hx
  have hPull : ∀ F ∈ finCombIn {x | c < x 3},
      pullDown c F ∈ finCombIn upperHalf := by
    intro F hF
    obtain ⟨A, hA, rfl⟩ := (raise_bijOn hImages c).surjOn hF
    rw [pullDown_raise hAction]
    exact hA
  have hHeight := fun {F' F''} => agreeAtHeight_holds σ hValues hForms hConcat hAction hRefl hAssoc
    hc hPull (F' := F') (F'' := F'')
  refine ⟨⟨hValues, hForms, fun F' hF' F'' hF'' h => hHeight hF' hF'' h, ?_⟩,
    pullDownClassesDense_holds σ hAction hImages hPull⟩
  intro F hF _ F' hF' hs
  refine ⟨(hForms F' (hAbove hF') F hF hs).2, fun F'' hF'' hs' => ?_⟩
  exact hHeight hF' hF'' (sameTensors_trans hs (sameTensors_symm hs'))
end YangMills.Construction.EuclideanFunctionals.HeightTuples
