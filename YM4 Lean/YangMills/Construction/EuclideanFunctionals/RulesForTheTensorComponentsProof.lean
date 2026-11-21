import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.RulesForTheTensorComponents
import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenation
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TensorCompRules
theorem single_eq_smul_toFree (S : sepAll) (c : ℂ) : Finsupp.single S c = c • toFree S.1 := by
  rw [toFree_of_mem S.2, Finsupp.smul_single, smul_eq_mul, mul_one]
theorem freeSep_induction_on {P : FreeSep → Prop} (hbase : ∀ S : sepAll, P (toFree S.1))
    (hzero : P 0) (hadd : ∀ u v, P u → P v → P (u + v)) (hsmul : ∀ (c : ℂ) u, P u → P (c • u))
    (w : FreeSep) : P w := by
  refine Finsupp.induction_linear w hzero (fun u v hu hv => hadd u v hu hv) fun S c => ?_
  rw [single_eq_smul_toFree]
  exact hsmul c _ (hbase S)
theorem freeSpanIn_induction_on {U : Set R4} {P : FreeSep → Prop}
    (hbase : ∀ L ∈ sepIn U, P (toFree L)) (hzero : P 0)
    (hadd : ∀ u v, P u → P v → P (u + v)) (hsmul : ∀ (c : ℂ) u, P u → P (c • u))
    {w : FreeSep} (hw : w ∈ freeSpanIn U) : P w := by
  refine Submodule.span_induction (p := fun u _ => P u) ?_ hzero (fun u v _ _ => hadd u v)
    (fun c u _ => hsmul c u) hw
  rintro _ ⟨L, hL, rfl⟩
  exact hbase L hL
theorem tensorComp_toFree (n : ℕ) (S : sepAll) :
    tensorComp n (toFree S.1) = tensorAt n S :=
  liftLin_toFree _ S
theorem tensorCompZero_toFree (S : sepAll) :
    tensorCompZero (toFree S.1) = tensorAtZero S :=
  liftLin_toFree _ S
theorem freeMul_toFree {A B : FnList} (hA : A ∈ sepAll) (hB : B ∈ sepAll) :
    freeMul (toFree A) (toFree B) = toFree (listAppend A B) := by
  have hmul : freeMul (toFree A) = liftLin fun B : sepAll => toFree (listAppend A B.1) :=
    liftLin_toFree _ ⟨A, hA⟩
  rw [hmul]
  exact liftLin_toFree _ ⟨B, hB⟩
theorem conj_tensorAt (n : ℕ) (S : sepAll) (p : TestSpaces.PointTuple n) :
    conj (tensorAt n S p) = tensorAt n S p := by
  by_cases hS : S.1.length = n
  · rw [tensorAt_of_length S hS, tensorOfFns_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ => Complex.conj_ofReal _
  · rw [tensorAt_of_length_ne S hS]
    simp
theorem conj_tensorAtZero (S : sepAll) :
    conj (tensorAtZero S) = tensorAtZero S := by
  unfold tensorAtZero tensorOfNil
  split_ifs <;> simp
theorem freeConj_single (S : sepAll) (c : ℂ) :
    freeConj (Finsupp.single S c) = conj c • toFree S.1 := by
  rw [← single_eq_smul_toFree]
  exact Finsupp.mapRange_single
theorem conjRule_holds : ConjRule := by
  intro w
  induction w using Finsupp.induction_linear with
  | zero =>
    refine ⟨by simp [freeConj], fun n _ => ?_⟩
    funext p
    simp [freeConj]
  | add u v ihu ihv =>
    obtain ⟨hu₀, hu⟩ := ihu
    obtain ⟨hv₀, hv⟩ := ihv
    have hsum : freeConj (u + v) = freeConj u + freeConj v :=
      Finsupp.mapRange_add (map_add _) u v
    refine ⟨by rw [hsum, map_add, map_add, map_add, hu₀, hv₀], fun n hn => ?_⟩
    funext p
    rw [hsum, map_add, map_add, hu n hn, hv n hn]
    simp
  | single S c =>
    rw [freeConj_single, single_eq_smul_toFree]
    refine ⟨?_, fun n _ => ?_⟩
    · rw [map_smul, map_smul, tensorCompZero_toFree, smul_eq_mul, smul_eq_mul, map_mul,
        conj_tensorAtZero]
    · funext p
      rw [map_smul, map_smul, tensorComp_toFree, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, map_mul, conj_tensorAt]
theorem actList_mem_sepAll (hrules : MotionRules.AllRules) (g : EuclidMotion)
    (S : sepAll) : g.actList S.1 ∈ sepAll :=
  ((hrules.2.2.1 Set.univ isOpen_univ g g).2.1.mapsTo ⟨S.2, fun _ _ => Set.subset_univ _⟩).1
theorem length_actList (g : EuclidMotion) (A : FnList) : (g.actList A).length = A.length :=
  List.length_map _
theorem tensorAt_actList (g : EuclidMotion) (S T : sepAll) (hT : T.1 = g.actList S.1) (n : ℕ)
    (p : TestSpaces.PointTuple n) :
    tensorAt n T p = tensorAt n S fun i => g⁻¹ (p i) := by
  obtain ⟨T, hT'⟩ := T
  obtain rfl : T = g.actList S.1 := hT
  by_cases hS : S.1.length = n
  · have hS' : (g.actList S.1).length = n := (length_actList g _).trans hS
    rw [tensorAt_of_length _ hS', tensorAt_of_length S hS, tensorOfFns_apply,
      tensorOfFns_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [cplxEntries, EuclidMotion.actList, EuclidMotion.actFn]
    rfl
  · have hS' : (g.actList S.1).length ≠ n := fun e => hS ((length_actList g _).symm.trans e)
    rw [tensorAt_of_length_ne _ hS', tensorAt_of_length_ne S hS]
    rfl
theorem motionRule_holds (hrules : MotionRules.AllRules) : MotionRule := by
  intro g w
  have hg : ∀ S : sepAll, g.actFree (toFree S.1) = toFree (g.actList S.1) :=
    fun S => liftLin_toFree _ S
  refine freeSep_induction_on
    (P := fun w => tensorCompZero (g.actFree w) = tensorCompZero w ∧
      ∀ n, 1 ≤ n → ∀ p : TestSpaces.PointTuple n,
        tensorComp n (g.actFree w) p = tensorComp n w fun i => g⁻¹ (p i))
    (fun S => ?_) ?_ (fun u v hu hv => ?_) (fun c u hu => ?_) w
  · rw [hg]
    refine ⟨?_, fun n _ p => ?_⟩
    · have hT := tensorCompZero_toFree ⟨g.actList S.1, actList_mem_sepAll hrules g S⟩
      rw [show toFree (g.actList S.1) = toFree (⟨g.actList S.1, actList_mem_sepAll hrules g S⟩ : sepAll).1
        from rfl, hT, tensorCompZero_toFree]
      simp [tensorAtZero, length_actList]
    · rw [show toFree (g.actList S.1) = toFree (⟨g.actList S.1, actList_mem_sepAll hrules g S⟩ : sepAll).1
        from rfl, tensorComp_toFree, tensorComp_toFree]
      exact tensorAt_actList g S _ rfl n p
  · simp
  · refine ⟨by rw [map_add, map_add, map_add, hu.1, hv.1], fun n hn p => ?_⟩
    rw [map_add, map_add, Pi.add_apply, hu.2 n hn, hv.2 n hn, map_add, Pi.add_apply]
  · refine ⟨by rw [map_smul, map_smul, map_smul, hu.1], fun n hn p => ?_⟩
    rw [map_smul, map_smul, Pi.smul_apply, hu.2 n hn, map_smul, Pi.smul_apply]
theorem bilinear_induction_on {U V : Set R4} {P : FreeSep → FreeSep → Prop}
    (hbase : ∀ A ∈ sepIn U, ∀ B ∈ sepIn V, P (toFree A) (toFree B))
    (hzl : ∀ v, P 0 v) (hzr : ∀ u, P u 0)
    (hal : ∀ u₁ u₂ v, P u₁ v → P u₂ v → P (u₁ + u₂) v)
    (har : ∀ u v₁ v₂, P u v₁ → P u v₂ → P u (v₁ + v₂))
    (hsl : ∀ (c : ℂ) u v, P u v → P (c • u) v)
    (hsr : ∀ (c : ℂ) u v, P u v → P u (c • v))
    {u v : FreeSep} (hu : u ∈ freeSpanIn U) (hv : v ∈ freeSpanIn V) : P u v := by
  refine freeSpanIn_induction_on (P := fun w => P u w) (fun B hB => ?_) (hzr u)
    (fun a b => har u a b) (fun c a => hsr c u a) hv
  exact freeSpanIn_induction_on (P := fun w => P w (toFree B)) (fun A hA => hbase A hA B hB)
    (hzl _) (fun a b => hal a b _) (fun c a => hsl c a _) hu
theorem splitTerm_add_left (u₁ u₂ v : FreeSep) (n : ℕ) (j : Fin (n + 1)) :
    splitTerm (u₁ + u₂) v n j = splitTerm u₁ v n j + splitTerm u₂ v n j := by
  funext p
  unfold splitTerm
  split_ifs <;>
    simp [TestSpaces.scalarTensorLeft, TestSpaces.scalarTensorRight, tensorFun_apply, add_mul,
      mul_add]
theorem splitTerm_add_right (u v₁ v₂ : FreeSep) (n : ℕ) (j : Fin (n + 1)) :
    splitTerm u (v₁ + v₂) n j = splitTerm u v₁ n j + splitTerm u v₂ n j := by
  funext p
  unfold splitTerm
  split_ifs <;>
    simp [TestSpaces.scalarTensorLeft, TestSpaces.scalarTensorRight, tensorFun_apply, add_mul,
      mul_add]
theorem splitTerm_smul_left (c : ℂ) (u v : FreeSep) (n : ℕ) (j : Fin (n + 1)) :
    splitTerm (c • u) v n j = c • splitTerm u v n j := by
  funext p
  unfold splitTerm
  split_ifs <;>
    simp [TestSpaces.scalarTensorLeft, TestSpaces.scalarTensorRight, tensorFun_apply, mul_assoc,
      mul_left_comm]
theorem splitTerm_smul_right (c : ℂ) (u v : FreeSep) (n : ℕ) (j : Fin (n + 1)) :
    splitTerm u (c • v) n j = c • splitTerm u v n j := by
  funext p
  unfold splitTerm
  split_ifs <;>
    simp [TestSpaces.scalarTensorLeft, TestSpaces.scalarTensorRight, tensorFun_apply, mul_assoc,
      mul_left_comm]
theorem tensorAt_listAppend (S T W : sepAll) (hW : W.1 = listAppend S.1 T.1) {a b n : ℕ}
    (ha : S.1.length = a) (hb : T.1.length = b) (hab : a + b = n) (p : TestSpaces.PointTuple n) :
    tensorAt n W p =
      tensorAt a S (fun i => p (Fin.cast hab (Fin.castAdd b i))) *
        tensorAt b T fun i => p (Fin.cast hab (Fin.natAdd a i)) := by
  subst ha hb hab
  obtain ⟨W, hW'⟩ := W
  obtain rfl : W = listAppend S.1 T.1 := hW
  have hlen : (listAppend S.1 T.1).length = S.1.length + T.1.length := List.length_append
  rw [tensorAt_of_length _ hlen, tensorAt_of_length S rfl, tensorAt_of_length T rfl,
    tensorOfFns_apply, tensorOfFns_apply, tensorOfFns_apply, Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have e : (S.1 ++ T.1)[(i : ℕ)]'(by simp; omega) = S.1[(i : ℕ)] := by simp
    simp only [cplxEntries, listAppend, ReflectionPositivity.AxisMirror.Ambient.append]
    exact congrArg (fun t : ℝ => (t : ℂ)) (congrFun e _)
  · refine Finset.prod_congr rfl fun i _ => ?_
    have e : (S.1 ++ T.1)[S.1.length + (i : ℕ)]'(by simp) = T.1[(i : ℕ)] := by
      simp
    simp only [cplxEntries, listAppend, ReflectionPositivity.AxisMirror.Ambient.append]
    exact congrArg (fun t : ℝ => (t : ℂ)) (congrFun e _)
theorem splitTerm_toFree_eq_zero (S T : sepAll) {n : ℕ} (j : Fin (n + 1))
    (hne : ¬(S.1.length = j ∧ T.1.length + j = n)) :
    splitTerm (toFree S.1) (toFree T.1) n j = 0 := by
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
  funext p
  unfold splitTerm
  split_ifs with h₀ hn'
  · rw [tensorCompZero_toFree, tensorComp_toFree]
    by_cases hS : S.1.length = 0
    · have hT : T.1.length ≠ n := fun hT => hne ⟨by omega, by omega⟩
      simp [TestSpaces.scalarTensorLeft, tensorAt_of_length_ne T hT]
    · simp [TestSpaces.scalarTensorLeft, tensorAtZero, hS]
  · rw [tensorCompZero_toFree, tensorComp_toFree]
    by_cases hT : T.1.length = 0
    · have hS : S.1.length ≠ n := fun hS => hne ⟨by omega, by omega⟩
      simp [TestSpaces.scalarTensorRight, tensorAt_of_length_ne S hS]
    · simp [TestSpaces.scalarTensorRight, tensorAtZero, hT]
  · beta_reduce
    rw [tensorComp_toFree, tensorComp_toFree, tensorFun_apply]
    by_cases hS : S.1.length = j
    · have hT : T.1.length ≠ n - j := fun hT => hne ⟨hS, by omega⟩
      simp [tensorAt_of_length_ne T hT]
    · simp [tensorAt_of_length_ne S hS]
theorem splitTerm_toFree_eq (S T W : sepAll) (hW : W.1 = listAppend S.1 T.1) {n : ℕ}
    (hn : 1 ≤ n) (j : Fin (n + 1)) (hS : S.1.length = j) (hT : T.1.length + j = n) :
    splitTerm (toFree S.1) (toFree T.1) n j = tensorAt n W := by
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
  funext p
  unfold splitTerm
  split_ifs with h₀ hn'
  · have hS0 : S.1 = [] := List.length_eq_zero_iff.1 (hS.trans h₀)
    have hWT : W = T := Subtype.ext (by rw [hW, hS0]; rfl)
    rw [hWT, tensorCompZero_toFree, tensorComp_toFree]
    simp [TestSpaces.scalarTensorLeft, tensorAtZero, tensorOfNil, hS0]
  · have hT0 : T.1 = [] := List.length_eq_zero_iff.1 (by omega)
    have hWS : W = S := Subtype.ext (by
      rw [hW, hT0]
      exact List.append_nil _)
    rw [hWS, tensorCompZero_toFree, tensorComp_toFree]
    simp [TestSpaces.scalarTensorRight, tensorAtZero, tensorOfNil, hT0]
  · beta_reduce
    rw [tensorComp_toFree, tensorComp_toFree, tensorFun_apply,
      tensorAt_listAppend S T W hW hS (by omega : T.1.length = n - j)
        (Nat.add_sub_of_le hjn) p]
theorem mulRule_toFree {U V : Set R4} (hUV : Disjoint U V) {A B : FnList}
    (hA : A ∈ sepIn U) (hB : B ∈ sepIn V) :
    tensorCompZero (freeMul (toFree A) (toFree B)) =
        tensorCompZero (toFree A) * tensorCompZero (toFree B) ∧
      ∀ n, 1 ≤ n → tensorComp n (freeMul (toFree A) (toFree B)) =
        ∑ j, splitTerm (toFree A) (toFree B) n j := by
  classical
  let S : sepAll := ⟨A, hA.1⟩
  let T : sepAll := ⟨B, hB.1⟩
  let W : sepAll := ⟨listAppend A B, (listAppend_mem_sepIn hUV hA hB).1⟩
  have hm : freeMul (toFree A) (toFree B) = toFree W.1 := freeMul_toFree hA.1 hB.1
  have hlen : W.1.length = A.length + B.length := List.length_append
  rw [hm]
  refine ⟨?_, fun n hn => ?_⟩
  · change tensorCompZero (toFree W.1) = tensorCompZero (toFree S.1) *
      tensorCompZero (toFree T.1)
    rw [tensorCompZero_toFree, tensorCompZero_toFree, tensorCompZero_toFree]
    simp only [tensorAtZero, tensorOfNil, hlen, S, T]
    by_cases h₁ : A.length = 0 <;> by_cases h₂ : B.length = 0 <;> simp [h₁, h₂]
  · change tensorComp n (toFree W.1) =
      ∑ j, splitTerm (toFree S.1) (toFree T.1) n j
    rw [tensorComp_toFree]
    by_cases hn' : A.length + B.length = n
    · have hj : A.length < n + 1 := by omega
      rw [Finset.sum_eq_single (⟨A.length, hj⟩ : Fin (n + 1))]
      · exact (splitTerm_toFree_eq S T W rfl hn _ rfl (by
          change B.length + A.length = n
          omega)).symm
      · intro j _ hne
        refine splitTerm_toFree_eq_zero S T j fun e => hne (Fin.ext e.1.symm)
      · simp
    · rw [tensorAt_of_length_ne W (by rw [hlen]; exact hn')]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      refine splitTerm_toFree_eq_zero S T j fun e => hn' ?_
      have e₁ : A.length = j := e.1
      have e₂ : B.length + j = n := e.2
      omega
theorem mulRule_holds : MulRule := by
  intro U V _ _ hUV u hu v hv
  refine bilinear_induction_on
    (P := fun u v => tensorCompZero (freeMul u v) =
        tensorCompZero u * tensorCompZero v ∧
      ∀ n, 1 ≤ n → tensorComp n (freeMul u v) = ∑ j, splitTerm u v n j)
    (fun A hA B hB => mulRule_toFree hUV hA hB) ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · intro w
    refine ⟨by simp, fun n _ => ?_⟩
    rw [map_zero, LinearMap.zero_apply, map_zero]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e := splitTerm_smul_left 0 0 w n j
    simpa using e
  · intro w
    refine ⟨by simp, fun n _ => ?_⟩
    rw [map_zero, map_zero]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e := splitTerm_smul_right 0 w 0 n j
    simpa using e
  · rintro u₁ u₂ w ⟨e₁, e₁'⟩ ⟨e₂, e₂'⟩
    refine ⟨by simp only [map_add, LinearMap.add_apply, e₁, e₂, add_mul], fun n hn => ?_⟩
    simp only [map_add, LinearMap.add_apply, e₁' n hn, e₂' n hn, splitTerm_add_left,
      Finset.sum_add_distrib]
  · rintro w v₁ v₂ ⟨e₁, e₁'⟩ ⟨e₂, e₂'⟩
    refine ⟨by simp only [map_add, e₁, e₂, mul_add], fun n hn => ?_⟩
    simp only [map_add, e₁' n hn, e₂' n hn, splitTerm_add_right, Finset.sum_add_distrib]
  · rintro c u w ⟨e, e'⟩
    refine ⟨by simp only [map_smul, LinearMap.smul_apply, e, smul_eq_mul, mul_assoc],
      fun n hn => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, e' n hn, splitTerm_smul_left, Finset.smul_sum]
  · rintro c u w ⟨e, e'⟩
    refine ⟨by simp only [map_smul, e, smul_eq_mul, mul_left_comm], fun n hn => ?_⟩
    simp only [map_smul, e' n hn, splitTerm_smul_right, Finset.smul_sum]
theorem metric_eq_euclidNormVec (p q : R4) :
    ReflectionPositivity.AxisMirror.Ambient.metric defaultMirrorData
        ReflectionPositivity.AxisMirror.Ambient.euclidean p q =
      TorusMetric.euclidNormVec (p - q) := rfl
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure metric_eq_euclidNormVec _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
section ComplexComponents
variable {n : ℕ} {φ : Fin n → R4 → ℂ}
theorem realPartComponent_re_or_im (σ : nonrealIdx φ → Fin 2) (i : Fin n) :
    realPartComponent φ σ i = (fun p => (φ i p).re) ∨ realPartComponent φ σ i = (fun p => (φ i p).im) := by
  unfold realPartComponent
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem ofFn_realPartComponent_mem_sepAll (hφ : ∀ i, φ i ∈ C1c ℂ)
    (hdisj : Pairwise fun i j => Disjoint (supp (φ i)) (supp (φ j)))
    (σ : nonrealIdx φ → Fin 2) : List.ofFn (realPartComponent φ σ) ∈ sepAll := by
  have hsub : ∀ i, supp (realPartComponent φ σ i) ⊆ supp (φ i) := fun i => by
    rw [supp_eq_tsupport, supp_eq_tsupport]
    refine closure_mono fun p hp h0 => hp ?_
    rcases realPartComponent_re_or_im σ i with e | e <;> rw [e] <;> simp [h0]
  have hmem : ∀ i, realPartComponent φ σ i ∈ C1c ℝ := fun i => by
    have hi := (mem_C1c_iff _).1 (hφ i)
    rw [mem_C1c_iff]
    rcases realPartComponent_re_or_im σ i with e | e <;> rw [e]
    · exact ⟨Complex.reCLM.contDiff.comp hi.1, hi.2.comp_left (g := Complex.re) Complex.zero_re⟩
    · exact ⟨Complex.imCLM.contDiff.comp hi.1, hi.2.comp_left (g := Complex.im) Complex.zero_im⟩
  refine Set.mem_iUnion.2 ⟨_, rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact hmem i
  · exact List.pairwise_ofFn.2 fun i j hij => (hdisj hij.ne).mono (hsub i) (hsub j)
end ComplexComponents
theorem sum_I_pow_imagCount_mul_prod {m : ℕ} (φ : Fin m → R4 → ℂ) (p : TestSpaces.PointTuple m) :
    ∑ σ : nonrealIdx φ → Fin 2, Complex.I ^ imagCount φ σ *
        ∏ i, ((realPartComponent φ σ i (p i) : ℝ) : ℂ) = ∏ i, φ i (p i) := by
  classical
  set J := nonrealIdx φ with hJ
  have hsplit : ∀ σ : J → Fin 2, ∏ i, ((realPartComponent φ σ i (p i) : ℝ) : ℂ) =
      (∏ i : J, ((realPartComponent φ σ i.1 (p i.1) : ℝ) : ℂ)) *
        ∏ i ∈ Jᶜ, ((realPartComponent φ σ i (p i) : ℝ) : ℂ) := fun σ => by
    rw [Finset.prod_coe_sort J fun i => ((realPartComponent φ σ i (p i) : ℝ) : ℂ),
      Finset.prod_mul_prod_compl]
  have hreal : ∀ σ : J → Fin 2, ∏ i ∈ Jᶜ, ((realPartComponent φ σ i (p i) : ℝ) : ℂ) =
      ∏ i ∈ Jᶜ, φ i (p i) := fun σ => by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ∉ J := Finset.mem_compl.1 hi
    have him : ∀ q, (φ i q).im = 0 := by
      by_contra hc
      exact hi' (by
        simp only [hJ, nonrealIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hc)
    simp only [realPartComponent, ← hJ, dif_neg hi']
    exact Complex.ext (by simp) (by simp [him])
  have hpow : ∀ σ : J → Fin 2, Complex.I ^ imagCount φ σ =
      ∏ i : J, Complex.I ^ (σ i : ℕ) := fun σ => by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  let g : J → Fin 2 → ℂ := fun i b =>
    if b = 0 then ((φ i.1 (p i.1)).re : ℂ) else Complex.I * ((φ i.1 (p i.1)).im : ℂ)
  have hfactor : ∀ (σ : J → Fin 2) (i : J), Complex.I ^ (σ i : ℕ) *
      ((realPartComponent φ σ i.1 (p i.1) : ℝ) : ℂ) = g i (σ i) := fun σ i => by
    have hi : i.1 ∈ nonrealIdx φ := i.2
    simp only [realPartComponent, dif_pos hi, g]
    by_cases h0 : σ i = 0
    · simp [h0]
    · have h1 : σ i = 1 := by omega
      simp [h1]
  have hsum : ∀ i : J, ∑ b : Fin 2, g i b = φ i.1 (p i.1) := fun i => by
    simp only [g, Fin.sum_univ_two]
    simp only [if_true, one_ne_zero, if_false]
    rw [mul_comm Complex.I]
    exact Complex.re_add_im _
  calc ∑ σ : J → Fin 2, Complex.I ^ imagCount φ σ * ∏ i, ((realPartComponent φ σ i (p i) : ℝ) : ℂ)
      = ∑ σ : J → Fin 2, (∏ i : J, g i (σ i)) * ∏ i ∈ Jᶜ, φ i (p i) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hsplit, hreal, ← mul_assoc, hpow, ← Finset.prod_mul_distrib]
        simp only [hfactor]
    _ = (∏ i : J, ∑ b : Fin 2, g i b) * ∏ i ∈ Jᶜ, φ i (p i) := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ i, φ i (p i) := by
        simp only [hsum]
        rw [Finset.prod_coe_sort J fun i => φ i (p i), Finset.prod_mul_prod_compl]
theorem complexListRule_holds : ComplexListRule := by
  intro m hm φ hφ hdisj
  let L : (nonrealIdx φ → Fin 2) → sepAll := fun σ =>
    ⟨List.ofFn (realPartComponent φ σ), ofFn_realPartComponent_mem_sepAll hφ hdisj σ⟩
  have hlen : ∀ σ, (L σ).1.length = m := fun σ => List.length_ofFn
  have hT : ∀ n, tensorComp n (complexList φ) =
      ∑ σ, Complex.I ^ imagCount φ σ • tensorAt n (L σ) := fun n => by
    simp only [complexList, map_sum, map_smul]
    exact Finset.sum_congr rfl fun σ _ => by rw [← tensorComp_toFree n (L σ)]
  refine ⟨?_, ?_, fun n _ hnm => ?_⟩
  · funext p
    rw [hT, Finset.sum_apply, tensorOfFns_apply, ← sum_I_pow_imagCount_mul_prod]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, tensorAt_of_length _ (hlen σ), tensorOfFns_apply]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [cplxEntries, L]
  · simp only [complexList, map_sum, map_smul]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [show toFree (List.ofFn (realPartComponent φ σ)) = toFree (L σ).1 from rfl,
      tensorCompZero_toFree]
    have hne : (L σ).1.length ≠ 0 := by rw [hlen]; omega
    simp [tensorAtZero, hne]
  · rw [hT]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [tensorAt_of_length_ne _ (by rw [hlen]; exact fun e => hnm e.symm), smul_zero]
theorem holds_of_allRules (hrules : MotionRules.AllRules) : Holds :=
  ⟨conjRule_holds, motionRule_holds hrules, mulRule_holds, complexListRule_holds⟩
end YangMills.Construction.EuclideanFunctionals.TensorCompRules
