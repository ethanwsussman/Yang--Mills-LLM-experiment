import YangMills.Construction.EuclideanFunctionals.CentredFunctionalSeesTensorComponentsOnly
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.RealTuples
theorem supp_ofReal (f : R4 → ℝ) : supp (fun x => (f x : ℂ)) = supp f := by
  have hset : {x | (f x : ℂ) ≠ 0} = {x | f x ≠ 0} := by
    ext x
    simp
  change MetricNotions.closureWrt _ {x | (f x : ℂ) ≠ 0} = MetricNotions.closureWrt _ {x | f x ≠ 0}
  rw [hset]
theorem ofReal_mem_C1c {f : R4 → ℝ} (hf : f ∈ C1c ℝ) :
    (fun x => (f x : ℂ)) ∈ C1c ℂ := by
  refine ⟨?_, ?_⟩
  · have hcd : ContDiff ℝ 1 f := hf.1
    exact Complex.ofRealCLM.contDiff.comp hcd
  · have hcpt := hf.2
    change MetricNotions.IsCompactWrt _ (supp f) at hcpt
    change MetricNotions.IsCompactWrt _ (supp fun x => (f x : ℂ))
    rw [supp_ofReal]
    exact hcpt
theorem cplxEntries_ofFn {n : ℕ} (u : Fin n → R4 → ℝ) (j : Fin n) :
    cplxEntries (List.ofFn u) List.length_ofFn j = fun x => (u j x : ℂ) := by
  funext x
  simp [cplxEntries]
theorem ofRealFns_eq_toFree {n : ℕ} (u : Fin n → R4 → ℝ) :
    ofRealFns u = toFree (List.ofFn u) := by
  have hreal : ∀ j, IsRealValued (cplxEntries (List.ofFn u) List.length_ofFn j) := by
    intro j x
    rw [cplxEntries_ofFn]
    simp
  rw [ofRealFns, complexTuple, if_pos hreal]
  congr 2
  funext j x
  rw [cplxEntries_ofFn]
  simp
theorem ofRealFn_eq_toFree (f : R4 → ℝ) : ofRealFn f = toFree [f] := by
  rw [ofRealFn, ofRealFns_eq_toFree]
  simp
theorem singletonsOf_eq_map {n : ℕ} (u : Fin n → R4 → ℝ) :
    singletonsOf u = (List.ofFn u).map fun f => toFree [f] := by
  rw [singletonsOf, List.map_ofFn]
  congr 1
  funext j
  exact ofRealFn_eq_toFree _
theorem mem_sepAll_of_sublist {A B : FnList} (hA : A ∈ sepAll) (hB : B.Sublist A) :
    B ∈ sepAll := by
  have hs := isSeparatedList_of_mem_sepAll hA
  exact Set.mem_iUnion.2 ⟨_, rfl, fun f hf => hs.1 f (hB.subset hf), hs.2.sublist hB⟩
theorem freeMul_toFree {A B : FnList} (hA : A ∈ sepAll) (hB : B ∈ sepAll) :
    freeMul (toFree A) (toFree B) = toFree (A ++ B) := by
  have e₁ := liftLin_toFree
    (fun A : sepAll => liftLin fun B : sepAll => toFree (listAppend A.1 B.1)) ⟨A, hA⟩
  have e₂ := liftLin_toFree (fun B : sepAll => toFree (listAppend A B.1)) ⟨B, hB⟩
  calc freeMul (toFree A) (toFree B)
      = liftLin (fun B : sepAll => toFree (listAppend A B.1)) (toFree B) :=
        congrArg (fun T : FreeSep →ₗ[ℂ] FreeSep => T (toFree B)) e₁
    _ = toFree (A ++ B) := e₂
theorem foldl_freeMul_singletons (L : FnList) : ∀ P : FnList, P ∈ sepAll → P ++ L ∈ sepAll →
    (L.map fun f => toFree [f]).foldl (fun B C => freeMul B C) (toFree P) = toFree (P ++ L) := by
  induction L with
  | nil =>
    intro P _ _
    simp
  | cons g L ih =>
    intro P hP hPL
    have hg : [g] ∈ sepAll :=
      mem_sepAll_of_sublist hPL (List.singleton_sublist.2 (by simp))
    have hPg : P ++ [g] ∈ sepAll :=
      mem_sepAll_of_sublist hPL (List.Sublist.append_left (List.singleton_sublist.2 (by simp)) P)
    simp only [List.map_cons, List.foldl_cons]
    rw [freeMul_toFree hP hg, ih _ hPg (by simpa using hPL)]
    simp
theorem mulLeft_singletons {M : FnList} (hM : M ∈ sepAll) (hne : M ≠ []) :
    Motions.mulLeft (M.map fun f => toFree [f]) = toFree M := by
  obtain ⟨a, L, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : [a] ∈ sepAll :=
    mem_sepAll_of_sublist hM (List.singleton_sublist.2 (by simp))
  simp only [Motions.mulLeft, List.map_cons]
  exact foldl_freeMul_singletons L [a] ha hM
theorem combSupp_toFree {M : FnList} (hM : M ∈ sepAll) :
    combSupp (toFree M) = ⋃ f ∈ M, supp f := by
  rw [combSupp, toFree_of_mem hM, Finsupp.support_single _ one_ne_zero]
  simp
theorem linearInComponent_of_isRealMultilinear {S : ConnFamily}
    (hS : TensorComponents.IsRealMultilinear S) :
    LinearInArgument S := by
  intro n hn i f g hf hg a a'
  obtain ⟨e₁, e₂, -⟩ := hS n (by omega) i f g hf hg a a'
  exact ⟨e₁, e₂⟩
theorem realAndZeroAtZeroComponent_of_isRealMultilinear {S : ConnFamily}
    (hS : TensorComponents.IsRealMultilinear S) :
    RealAndZeroAtZeroComponent S := by
  intro A hA
  refine ⟨?_, fun hzero => ?_⟩
  · have e := liftLin_toFree (fun A : sepAll => (centeredFn S A : ℂ)) ⟨A, hA⟩
    have hval : centeredAt S A = centeredFn S ⟨A, hA⟩ := dif_pos hA
    rw [hval]
    exact e
  · obtain ⟨i, hi⟩ := List.mem_iff_get.1 hzero
    have hlen : 1 ≤ A.length := by
      have := i.2
      omega
    have hmem : List.ofFn A.get ∈ sepN A.length := by
      rw [List.ofFn_get]
      exact ⟨rfl, isSeparatedList_of_mem_sepAll hA⟩
    have hupd : Function.update A.get i (A.get i) = A.get := Function.update_eq_self _ _
    have hcomb : (0 : ℝ) • A.get i + (0 : ℝ) • A.get i = A.get i := by
      rw [hi]
      simp
    have e := (hS A.length hlen i A.get (A.get i) hmem (by rw [hupd]; exact hmem) 0 0).2.1
    rw [hcomb, hupd, List.ofFn_get] at e
    simpa using e
theorem ofFn_mem_sepN {n : ℕ} {u : Fin n → R4 → ℝ}
    (hm : ∀ j, u j ∈ C1c ℝ)
    (hd : Pairwise fun k j => Disjoint (supp (u k)) (supp (u j))) :
    List.ofFn u ∈ sepN n := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact hm i
  · exact List.pairwise_ofFn.2 fun i j hij => hd hij.ne
theorem complexFamily_ofFn_real {n : ℕ} {u : Fin n → R4 → ℝ} (hn : 1 ≤ n)
    (hm : ∀ j, u j ∈ C1c ℝ)
    (hd : Pairwise fun k j => Disjoint (supp (u k)) (supp (u j))) :
    ComplexComponents (cplxEntries (List.ofFn u) List.length_ofFn) where
  one_le := hn
  mem j := by
    rw [cplxEntries_ofFn]
    exact ofReal_mem_C1c (hm j)
  disjoint k j hkj := by
    beta_reduce
    rw [cplxEntries_ofFn, cplxEntries_ofFn, supp_ofReal, supp_ofReal]
    exact hd hkj
theorem mulDefined_succ {n : ℕ} {u : Fin n → R4 → ℝ}
    (hA : List.ofFn u ∈ sepAll) (k : ℕ) (hk : k + 1 < n) :
    MulDefined (Motions.mulLeft ((singletonsOf u).take (k + 1)))
      (ofRealFn (u ⟨k + 1, hk⟩)) := by
  have hkl : k + 1 < (List.ofFn u).length := by simpa using hk
  have hdrop := List.drop_eq_getElem_cons hkl
  have hget : (List.ofFn u)[k + 1] = u ⟨k + 1, hk⟩ := by simp
  rw [hget] at hdrop
  have hgd : u ⟨k + 1, hk⟩ ∈ (List.ofFn u).drop (k + 1) := by
    rw [hdrop]
    simp
  have hgm : u ⟨k + 1, hk⟩ ∈ List.ofFn u := List.mem_of_mem_drop hgd
  have hM : (List.ofFn u).take (k + 1) ∈ sepAll :=
    mem_sepAll_of_sublist hA (List.take_sublist _ _)
  have hne : (List.ofFn u).take (k + 1) ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp at this
    omega
  have hg : [u ⟨k + 1, hk⟩] ∈ sepAll :=
    mem_sepAll_of_sublist hA (List.singleton_sublist.2 hgm)
  have hpw : ((List.ofFn u).take (k + 1) ++ (List.ofFn u).drop (k + 1)).Pairwise
      fun f g => Disjoint (supp f) (supp g) := by
    rw [List.take_append_drop]
    exact (isSeparatedList_of_mem_sepAll hA).2
  have hcross := (List.pairwise_append.1 hpw).2.2
  rw [singletonsOf_eq_map, ← List.map_take, mulLeft_singletons hM hne,
    ofRealFn_eq_toFree, MulDefined, combSupp_toFree hM,
    combSupp_toFree hg]
  refine Set.disjoint_iUnion₂_left.2 fun f hf => Set.disjoint_iUnion₂_right.2 fun g hg' => ?_
  rw [List.mem_singleton] at hg'
  subst hg'
  exact hcross f hf _ hgd
theorem realTupleComponents_holds {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) :
    RealTupleEvaluations d := by
  intro n hn u hm hd
  have hsep := ofFn_mem_sepN hm hd
  have hA : List.ofFn u ∈ sepAll :=
    ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ n hsep
  have heq := ofRealFns_eq_toFree u
  have hne : List.ofFn u ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp at this
    omega
  refine ⟨hsep, complexFamily_ofFn_real hn hm hd, by rw [heq], mulDefined_succ hA, ?_, ?_⟩
  · rw [singletonsOf_eq_map, mulLeft_singletons hA hne, heq]
  · intro hpos
    have hIn : toFree (List.ofFn u) ∈ finCombIn upperHalf := by
      rw [finCombIn_eq_freeSpanIn]
      refine Submodule.subset_span ⟨_, ⟨hA, fun f hf => ?_⟩, rfl⟩
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
      exact hpos i
    have hIn' : ofRealFns u ∈ finCombIn upperHalf := by
      rw [heq]
      exact hIn
    refine ⟨hIn', hIn, ?_⟩
    congr 1
    exact Subtype.ext heq
theorem realFunctionTuples_of_centeredSeesTensorComps
    (hT : TensorComponents.CenteredSeesTensorComps) : realFunctionTuples := by
  intro m S d
  exact ⟨linearInComponent_of_isRealMultilinear (hT S).1,
    realAndZeroAtZeroComponent_of_isRealMultilinear (hT S).1, realTupleComponents_holds d⟩
end YangMills.Construction.EuclideanFunctionals.RealTuples
