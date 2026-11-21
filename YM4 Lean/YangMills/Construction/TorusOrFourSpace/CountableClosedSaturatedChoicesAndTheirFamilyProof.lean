import YangMills.Construction.TorusOrFourSpace.ApproximationInTheStockAndAChoiceWithTheStabilitiesProof
import YangMills.Construction.TorusOrFourSpace.DisjointMembersOfTheStock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SaturatedChoices
open Kind SupportAdapted
variable {D : Params} {E : Kind}
private theorem adic_isQuotIsometryGroup (hG : AdicIsometryGroup.Claim) :
    IsQuotIsometryGroup D E (Kind.adicIsometriesQ D E) :=
  (hG D E).2.2.2.1.2.1
private theorem pushFn_facts (hG : AdicIsometryGroup.Claim) :
    AdicIsometryGroup.SupportPushFn D E ∧
      AdicIsometryGroup.PushFnPreservesC1CompactSupport D E ∧
      AdicIsometryGroup.SupportStockInvariant D E := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, h15⟩ := hG D E
  exact ⟨h13, h14, h15⟩
private theorem symm_mem_adic (hG : AdicIsometryGroup.Claim)
    (r : E.Pt D ≃ E.Pt D) (hr : ⇑r ∈ Kind.adicIsometriesQ D E) :
    ⇑r.symm ∈ Kind.adicIsometriesQ D E := by
  obtain ⟨r', hr', h1, -⟩ := (adic_isQuotIsometryGroup hG).2.2.2 r hr
  have h : r' = ⇑r.symm := by
    funext y
    apply r.injective
    simpa using congrFun h1 y
  exact h ▸ hr'
private theorem trans_mem_adic (hG : AdicIsometryGroup.Claim)
    (r r' : E.Pt D ≃ E.Pt D) (hr : ⇑r ∈ Kind.adicIsometriesQ D E)
    (hr' : ⇑r' ∈ Kind.adicIsometriesQ D E) : ⇑(r'.trans r) ∈ Kind.adicIsometriesQ D E :=
  (adic_isQuotIsometryGroup hG).2.2.1 r hr r' hr'
private theorem pushFn_mem_c1VanishingOutside (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim)
    (r : E.Pt D ≃ E.Pt D) (hr : ⇑r ∈ Kind.adicIsometriesQ D E)
    {Q Q' : Set (E.Pt D)} (hQ : Q ∈ supportStock D E) (hQ' : Q' = r '' Q)
    {f : E.Pt D → ℝ} (hf : f ∈ c1VanishingOutside D E Q) :
    pushFn D E r f ∈ c1VanishingOutside D E Q' := by
  have hcomp := ((hS D E Q hQ).1.2 f hf).1
  refine ⟨((pushFn_facts hG).2.1 r hr f hf.1 hcomp).1, fun y hy => ?_⟩
  exact hf.2 _ (fun h => hy (hQ' ▸ ⟨_, h, by simp⟩))
private theorem empty_mem_supportStock : (∅ : Set (E.Pt D)) ∈ supportStock D E :=
  ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
private theorem union_mem_supportStock {Q Q' : Set (E.Pt D)} (hQ : Q ∈ supportStock D E)
    (hQ' : Q' ∈ supportStock D E) : Q ∪ Q' ∈ supportStock D E := by apply _root_.YangMills.Construction.PeriodicSpace.SupportAdapted.union_mem_supportStock <;> assumption
private theorem c1VanishingOutside_mono {Q Q' : Set (E.Pt D)} (h : Q ⊆ Q') {f : E.Pt D → ℝ}
    (hf : f ∈ c1VanishingOutside D E Q) : f ∈ c1VanishingOutside D E Q' :=
  ⟨hf.1, fun y hy => hf.2 y (fun h' => hy (h h'))⟩
private theorem supportQ_subset_of_mem (hS : C1OfStock.Holds) {Q : Set (E.Pt D)}
    (hQ : Q ∈ supportStock D E) {f : E.Pt D → ℝ} (hf : f ∈ c1VanishingOutside D E Q) :
    Kind.supportQ D E f ⊆ Q :=
  ((hS D E Q hQ).1.1 f hf.1).1 hf
private theorem rat_smul_eq_real_smul (a : ℚ) (x : E.Pt D → ℝ) : a • x = (a : ℝ) • x := by
  funext y
  simp [Rat.smul_def]
private theorem exists_closed_saturated (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim)
    (hF : CountableChoiceFamilyFacts) :
    ExistsCountableClosedSaturatedChoice D E := by
  classical
  have hstock : (supportStock D E).Countable := (hF D E).1.1
  have hvs : ∀ Q ∈ supportStock D E,
      IsFunctionSpaceNorm D E (euclidC1Norm D E) (c1VanishingOutside D E Q) :=
    fun Q hQ => ((hF D E).2.1 Q hQ).2.2.1.1
  have hdense : ∀ Q : supportStock D E, ∃ A, A ⊆ c1VanishingOutside D E Q.1 ∧ A.Countable ∧
      IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q.1) A :=
    fun Q => ((hF D E).2.1 Q.1 Q.2).2.2.1.2.2
  choose A hAsub hAc hAd using hdense
  have hstockType : Countable (supportStock D E) := hstock.to_subtype
  let G : Set (E.Pt D ≃ E.Pt D) := {r | ⇑r ∈ Kind.adicIsometriesQ D E}
  have hGc : G.Countable := ((hG D E).2.2.2.1.1).preimage DFunLike.coe_injective
  let S : Set (E.Pt D → ℝ) :=
    {g | ∃ r ∈ G, ∃ Q, ∃ f ∈ A Q, g = pushFn D E r f}
  have hSc : S.Countable :=
    (hGc.biUnion fun r _ => Set.countable_iUnion fun Q =>
      (hAc Q).image (pushFn D E r)).mono (by
        rintro g ⟨r, hr, Q, f, hf, rfl⟩
        exact Set.mem_biUnion hr (Set.mem_iUnion.2 ⟨Q, ⟨f, hf, rfl⟩⟩))
  let V : Submodule ℚ (E.Pt D → ℝ) := Submodule.span ℚ S
  have hVc : (V : Set (E.Pt D → ℝ)).Countable := by
    have hST : Countable S := hSc.to_subtype
    have hr := Finsupp.range_linearCombination (R := ℚ) (v := ((↑) : S → E.Pt D → ℝ))
    rw [Subtype.range_coe] at hr
    have hV : (V : Set (E.Pt D → ℝ)) =
        Set.range (Finsupp.linearCombination ℚ ((↑) : S → E.Pt D → ℝ)) := by
      rw [← LinearMap.coe_range, hr]
    rw [hV]
    exact Set.countable_range _
  have hAV : ∀ Q, A Q ⊆ V := fun Q f hf => Submodule.subset_span
    ⟨Equiv.refl _, (adic_isQuotIsometryGroup hG).2.1, Q, f, hf, rfl⟩
  have hP : ∀ f ∈ V, ∃ Q ∈ supportStock D E, f ∈ c1VanishingOutside D E Q := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, hr, Q, f0, hf0, rfl⟩ := hg
      exact ⟨r '' Q.1, (pushFn_facts hG).2.2 r hr Q.1 Q.2,
        pushFn_mem_c1VanishingOutside hS hG r hr Q.2 rfl (hAsub Q hf0)⟩
    | zero => exact ⟨∅, empty_mem_supportStock, (hvs ∅ empty_mem_supportStock).zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨Q, hQ, hxQ⟩ := hx
      obtain ⟨Q', hQ', hyQ⟩ := hy
      have hU := union_mem_supportStock hQ hQ'
      refine ⟨Q ∪ Q', hU, ?_⟩
      have h := (hvs _ hU).lincomb_mem x (c1VanishingOutside_mono Set.subset_union_left hxQ)
        y (c1VanishingOutside_mono Set.subset_union_right hyQ) 1 1
      simpa using h
    | smul a x _ hx =>
      obtain ⟨Q, hQ, hxQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      have h := (hvs _ hQ).lincomb_mem x hxQ x hxQ (a : ℝ) 0
      rw [rat_smul_eq_real_smul]
      simpa using h
  have hact : ∀ r ∈ G, ∀ f ∈ V, pushFn D E r f ∈ V := by
    intro r hr f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r', hr', Q, f0, hf0, rfl⟩ := hg
      exact Submodule.subset_span ⟨r'.trans r, trans_mem_adic hG r r' hr hr', Q, f0, hf0, rfl⟩
    | zero =>
      have h : pushFn D E r (0 : E.Pt D → ℝ) = 0 := rfl
      rw [h]
      exact V.zero_mem
    | add x y _ _ hx hy =>
      have h : pushFn D E r (x + y) = pushFn D E r x + pushFn D E r y := rfl
      rw [h]
      exact V.add_mem hx hy
    | smul a x _ hx =>
      have h : pushFn D E r (a • x) = a • pushFn D E r x := rfl
      rw [h]
      exact V.smul_mem a hx
  let C : supportStock D E → Set (E.Pt D → ℝ) :=
    fun Q => (V : Set (E.Pt D → ℝ)) ∩ c1VanishingOutside D E Q.1
  have hent : choiceComponents D E C = (V : Set (E.Pt D → ℝ)) := by
    ext f
    constructor
    · intro hf
      obtain ⟨Q, hQ⟩ := Set.mem_iUnion.1 hf
      exact hQ.1
    · intro hf
      obtain ⟨Q, hQ, hfQ⟩ := hP f hf
      exact Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, hf, hfQ⟩
  have hchoice : IsDenseChoice D E C := fun Q => ⟨Set.inter_subset_right, fun f hf ε hε => by
    obtain ⟨g, hg, hlt⟩ := hAd Q f hf ε hε
    exact ⟨g, ⟨hAV Q hg, hAsub Q hg⟩, hlt⟩⟩
  refine ⟨C, ⟨hchoice, fun Q => hVc.mono Set.inter_subset_left⟩, ⟨?_, ?_⟩, ?_⟩
  · intro r hr f hf
    rw [hent] at hf ⊢
    exact hact r hr f hf
  · rintro p f g hf ⟨-, c, rfl⟩
    rw [hent]
    refine V.sum_mem fun i _ => ?_
    rw [← rat_smul_eq_real_smul]
    have hfi := hf i
    rw [hent] at hfi
    exact V.smul_mem _ hfi
  · intro Q
    rw [hent]
private theorem choiceTupleFamily_eq_disjointComponentTuples (hDj : DisjointStockMembers.Statement)
    (hS : C1OfStock.Holds)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hC : IsDenseChoice D E C)
    (hB : IsSaturated D E C) :
    choiceTupleFamily D E C = disjointComponentTuples D E C := by
  ext ⟨n, φ⟩
  constructor
  · rintro ⟨hn, Q, hQ, hdisj, hmem⟩
    refine ⟨hn, fun i => Set.mem_iUnion.2 ⟨⟨Q i, hQ i⟩, hmem i⟩, fun i k hik => ?_⟩
    exact Set.disjoint_iff_inter_eq_empty.1
      (Disjoint.mono (supportQ_subset_of_mem hS (hQ i) ((hC _).1 (hmem i)))
        (supportQ_subset_of_mem hS (hQ k) ((hC _).1 (hmem k))) (hdisj hik))
  · rintro ⟨hn, hent, hsup⟩
    have hcomp : ∀ i, IsCompactQ D E (Kind.supportQ D E (φ i)) := fun i => by
      obtain ⟨Q, hQ⟩ := Set.mem_iUnion.1 (hent i)
      exact ((hS D E Q.1 Q.2).1.2 _ ((hC Q).1 hQ)).1
    have hc1 : ∀ i, φ i ∈ c1Set D E := fun i => by
      obtain ⟨Q, hQ⟩ := Set.mem_iUnion.1 (hent i)
      exact ((hC Q).1 hQ).1
    obtain ⟨Q, hQ, hdisj, hsub⟩ := hDj D E n hn (fun i => Kind.supportQ D E (φ i))
      (fun _ => Set.univ) hcomp
      (fun i k hik => Set.disjoint_iff_inter_eq_empty.2 (hsup i k hik))
      (fun _ _ _ => ⟨1, one_pos, fun _ _ => trivial⟩) (fun _ => Set.subset_univ _)
    refine ⟨hn, Q, hQ, hdisj, fun i => ?_⟩
    rw [hB ⟨Q i, hQ i⟩]
    exact ⟨hent i, ((hS D E (Q i) (hQ i)).1.1 _ (hc1 i)).2 (hsub i).1⟩
private theorem disjointComponentTuples_stable (hG : AdicIsometryGroup.Claim)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hA : HasClosedValues D E C) :
    IsAdicIsometryInvariant D E (disjointComponentTuples D E C) ∧
      IsClosedUnderAppend D E (disjointComponentTuples D E C) := by
  constructor
  · rintro r hr ⟨n, φ⟩ ⟨hn, hent, hsup⟩
    refine ⟨hn, fun i => hA.1 r hr _ (hent i), fun i k hik => ?_⟩
    have hs := (pushFn_facts hG).1 r hr
    change Kind.supportQ D E (pushFn D E r (φ i)) ∩
      Kind.supportQ D E (pushFn D E r (φ k)) = ∅
    rw [hs, hs, ← Set.image_inter r.injective, hsup i k hik, Set.image_empty]
  · rintro ⟨n, φ⟩ ⟨hn, hent, hsup⟩ ⟨p, ψ⟩ ⟨hp, hent', hsup'⟩ hd
    refine ⟨?_, fun i => ?_, fun i k hik => ?_⟩
    · have hn' : 1 ≤ n := hn
      change 1 ≤ n + p
      omega
    · change appendTuples D E φ ψ i ∈ choiceComponents D E C
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [appendTuples] using hent i
      · simpa [appendTuples] using hent' i
    · change Kind.supportQ D E (appendTuples D E φ ψ i) ∩
        Kind.supportQ D E (appendTuples D E φ ψ k) = ∅
      revert hik
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> intro hik
      · have hne : i ≠ k := fun h => hik (by rw [h])
        simpa [appendTuples] using hsup i k hne
      · simpa [appendTuples] using Set.disjoint_iff_inter_eq_empty.1 (hd i k)
      · simpa [appendTuples, Set.inter_comm] using
          Set.disjoint_iff_inter_eq_empty.1 (hd k i)
      · have hne : i ≠ k := fun h => hik (by rw [h])
        simpa [appendTuples] using hsup' i k hne
private theorem choiceSets_ratSubmodules_of (hF : CountableChoiceFamilyFacts)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hC : IsDenseChoice D E C)
    (hA : HasClosedValues D E C) (hB : IsSaturated D E C) :
    ChoiceSetsAreRatSubmodules D E C := by
  intro Q
  have hv := ((hF D E).2.1 Q.1 Q.2).2.2.1.1
  have hcomb : ∀ (a b : ℚ) (f g : E.Pt D → ℝ), f ∈ C Q → g ∈ C Q →
      (a : ℝ) • f + (b : ℝ) • g ∈ C Q := by
    intro a b f g hf hg
    rw [hB Q]
    refine ⟨?_, hv.lincomb_mem f ((hC Q).1 hf) g ((hC Q).1 hg) a b⟩
    refine hA.2 2 ![f, g] _ (fun i => ?_) ⟨by norm_num, ![a, b], by simp [Fin.sum_univ_two]⟩
    fin_cases i
    · exact Set.mem_iUnion.2 ⟨Q, hf⟩
    · exact Set.mem_iUnion.2 ⟨Q, hg⟩
  obtain ⟨g, hg, -⟩ := (hC Q).2 0 hv.zero_mem 1 one_pos
  refine ⟨{ carrier := C Q, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    simpa using hcomb 1 1 x y hx hy
  · simpa using hcomb 0 0 g g hg hg
  · intro c x hx
    have h := hcomb c 0 x x hx hx
    rw [rat_smul_eq_real_smul]
    simpa using h
private theorem pushFn_mem_choiceSet (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hC : IsDenseChoice D E C)
    (hA : HasClosedValues D E C) (hB : IsSaturated D E C)
    (r : E.Pt D ≃ E.Pt D) (hr : ⇑r ∈ Kind.adicIsometriesQ D E)
    (Q Q' : supportStock D E) (h : Q'.1 = r '' Q.1) {f : E.Pt D → ℝ} (hf : f ∈ C Q) :
    pushFn D E r f ∈ C Q' := by
  rw [hB Q']
  exact ⟨hA.1 r hr f (Set.mem_iUnion.2 ⟨Q, hf⟩),
    pushFn_mem_c1VanishingOutside hS hG r hr Q.2 h ((hC Q).1 hf)⟩
private theorem choiceSetsEquivariant_of (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim)
    (C : supportStock D E → Set (E.Pt D → ℝ)) (hC : IsDenseChoice D E C)
    (hA : HasClosedValues D E C) (hB : IsSaturated D E C) :
    ChoiceSetsEquivariant D E C := by
  intro r hr Q
  have h : r '' Q.1 ∈ supportStock D E := (pushFn_facts hG).2.2 r hr Q.1 Q.2
  refine ⟨h, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact pushFn_mem_choiceSet hS hG C hC hA hB r hr Q ⟨_, h⟩ rfl hf
  · intro g hg
    have hQ : Q.1 = r.symm '' (r '' Q.1) := by
      rw [Set.image_image]
      simp
    have hm := pushFn_mem_choiceSet hS hG C hC hA hB r.symm (symm_mem_adic hG r hr) ⟨_, h⟩ Q hQ hg
    refine ⟨_, hm, ?_⟩
    funext y
    simp [pushFn]
private theorem listingsEquivariant_of (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim) : ListingsEquivariant D E := by
  intro C hC hA hB r hr n φ Q _ hlist
  obtain ⟨hQ, hdisj, hφ⟩ := hlist
  have hstock : ∀ i, r '' Q i ∈ supportStock D E :=
    fun i => (pushFn_facts hG).2.2 r hr (Q i) (hQ i)
  refine ⟨⟨hstock, fun i j hij => (Set.disjoint_image_iff r.injective).2 (hdisj hij), fun i => ?_⟩,
    fun i k _ => ?_⟩
  · exact pushFn_mem_choiceSet hS hG C hC hA hB r hr ⟨Q i, hQ i⟩ ⟨_, hstock i⟩ rfl (hφ i)
  · have hP := ((adic_isQuotIsometryGroup hG).1 r hr).2
    simp only [setInfDist, iInf_image, hP _ _]
theorem claim_holds (hDj : DisjointStockMembers.Statement) (hS : C1OfStock.Holds)
    (hG : AdicIsometryGroup.Claim)
    (hF : CountableChoiceFamilyFacts) : Claim := by
  intro D E
  refine ⟨exists_closed_saturated hS hG hF,
    fun C hC hB => choiceTupleFamily_eq_disjointComponentTuples hDj hS C hC hB, ?_,
    listingsEquivariant_of hS hG, fun C _ hA => disjointComponentTuples_stable hG C hA⟩
  intro C hC hA hB
  have hfam := choiceTupleFamily_eq_disjointComponentTuples hDj hS C hC hB
  have hst := disjointComponentTuples_stable hG C hA
  rw [← hfam] at hst
  exact ⟨choiceSets_ratSubmodules_of hF C hC hA hB, choiceSetsEquivariant_of hS hG C hC hA hB,
    hst.1, hst.2⟩
end YangMills.Construction.PeriodicSpace.SaturatedChoices
