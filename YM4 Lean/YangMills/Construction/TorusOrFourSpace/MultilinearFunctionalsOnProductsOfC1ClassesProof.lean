import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClassesProof
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsOnProductsOfC1Classes
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.DisjointProducts
open MetricNotions
open TupleFacts (DistIsMetric EvalLipschitzCompact SingleC1Agree)
section CompactSeparation
variable {X : Type*} (d : X → X → ℝ)
private theorem exists_member_of_monotone_cover {K : Set X} (hK : IsCompactWrt d K)
    (P : ℝ → Set X) (hP : ∀ r, 0 < r → IsOpenWrt d (P r))
    (hmono : ∀ r s, 0 < r → r ≤ s → P s ⊆ P r)
    (hcover : ∀ x ∈ K, ∃ r, 0 < r ∧ x ∈ P r) (hpos : ∃ r : ℝ, 0 < r) :
    ∃ r, 0 < r ∧ K ⊆ P r := by
  have hopen : ∀ U ∈ {U | ∃ r, 0 < r ∧ U = P r}, IsOpenWrt d U := by
    rintro U ⟨r, hr, rfl⟩
    exact hP r hr
  have hsub : K ⊆ ⋃₀ {U | ∃ r, 0 < r ∧ U = P r} := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := hcover x hx
    exact ⟨P r, ⟨r, hr, rfl⟩, hxr⟩
  obtain ⟨𝒱, h𝒱, hfin, hK𝒱⟩ := hK _ hopen hsub
  have hbound : ∃ r, 0 < r ∧ ∀ U ∈ 𝒱, U ⊆ P r := by
    clear hK𝒱
    induction 𝒱, hfin using Set.Finite.induction_on with
    | empty =>
      obtain ⟨r, hr⟩ := hpos
      exact ⟨r, hr, fun U hU => absurd hU (Set.notMem_empty U)⟩
    | @insert U S _ _ ih =>
      obtain ⟨r, hr, hS⟩ := ih ((Set.subset_insert _ _).trans h𝒱)
      obtain ⟨s, hs, rfl⟩ := h𝒱 (Set.mem_insert U S)
      refine ⟨min r s, lt_min hr hs, ?_⟩
      rintro V (rfl | hVS)
      · exact hmono _ _ (lt_min hr hs) (min_le_right r s)
      · exact (hS V hVS).trans (hmono _ _ (lt_min hr hs) (min_le_left r s))
  obtain ⟨r, hr, hbound⟩ := hbound
  refine ⟨r, hr, fun x hx => ?_⟩
  obtain ⟨U, hU𝒱, hxU⟩ := hK𝒱 hx
  exact hbound U hU𝒱 hxU
private theorem exists_pos_sep_of_disjoint (hnonneg : ∀ x y, 0 ≤ d x y)
    (heq : ∀ x y, d x y = 0 → x = y) (hcomm : ∀ x y, d x y = d y x)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    {K L : Set X} (hK : IsCompactWrt d K) (hL : IsCompactWrt d L) (hKL : Disjoint K L) :
    ∃ r, 0 < r ∧ ∀ x ∈ K, ∀ y ∈ L, r ≤ d x y := by
  have hpt : ∀ x ∈ K, ∃ r, 0 < r ∧ ∀ y ∈ L, r ≤ d x y := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := exists_member_of_monotone_cover d hL (fun r => {y | r < d x y})
      (fun r _ y hy => ⟨d x y - r, sub_pos.2 hy, fun y' hy' => by
        have h1 := htriangle x y y'
        show r < d x y'
        have h2 := hcomm x y
        have h3 := htriangle x y' y
        have h4 := hcomm y' y
        linarith⟩)
      (fun r s _ hrs y hy => lt_of_le_of_lt hrs hy)
      (fun y hy => by
        have hne : d x y ≠ 0 := fun h0 =>
          Set.disjoint_left.1 hKL hx (by rw [heq x y h0]; exact hy)
        have hlt : 0 < d x y := lt_of_le_of_ne (hnonneg x y) (Ne.symm hne)
        exact ⟨d x y / 2, half_pos hlt, half_lt_self hlt⟩)
      ⟨1, one_pos⟩
    exact ⟨r, hr, fun y hy => (hsub hy).le⟩
  obtain ⟨r, hr, hsub⟩ := exists_member_of_monotone_cover d hK
    (fun r => {x | ∃ s, r < s ∧ ∀ y ∈ L, s ≤ d x y})
    (fun r _ x ⟨s, hrs, hs⟩ => ⟨(s - r) / 2, half_pos (sub_pos.2 hrs), fun x' hx' =>
      ⟨(s + r) / 2, by linarith, fun y hy => by
        have h1 := hs y hy
        have h2 := htriangle x x' y
        linarith⟩⟩)
    (fun r s _ hrs x ⟨t, hst, ht⟩ => ⟨t, lt_of_le_of_lt hrs hst, ht⟩)
    (fun x hx => by
      obtain ⟨r, hr, hs⟩ := hpt x hx
      exact ⟨r / 2, half_pos hr, r, half_lt_self hr, hs⟩)
    ⟨1, one_pos⟩
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  obtain ⟨s, hrs, hs⟩ := hsub hx
  exact hrs.le.trans (hs y hy)
end CompactSeparation
variable (D : Params) (E : Kind)
private def singleton (y : E.Pt D) : E.Tuple D 1 := fun _ => y
private theorem quotDist_nonneg (y y' : E.Pt D) : 0 ≤ quotDist D E y y' := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_nonneg <;> assumption
private theorem tupleDist_singleton (y y' : E.Pt D) :
    Tuple.tupleDist D E (singleton D E y) (singleton D E y') = quotDist D E y y' := by
  have h : Tuple.tupleDist D E (singleton D E y) (singleton D E y') =
      Real.sqrt (quotDist D E y y' ^ 2) := by
    show Real.sqrt (∑ _i : Fin 1, quotDist D E y y' ^ 2) = _
    simp
  rw [h, Real.sqrt_sq (quotDist_nonneg D E y y')]
private theorem isCompactQ_of_singleSet
    (heval : EvalLipschitzCompact D E 1) {S : Set (E.Pt D)}
    (hS : Tuple.IsCompactT D E (Tuple.singleSet D E S)) :
    IsCompactQ D E S := by
  have h := (heval ⟨0, (1 : ℕ+).pos⟩).2 _ hS
  have himg : (fun y : E.Tuple D 1 => y ⟨0, (1 : ℕ+).pos⟩) ''
      Tuple.singleSet D E S = S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨singleton D E z, hz, rfl⟩
  rwa [himg] at h
private theorem mem_c1SupportedIn_of_real_test
    (heval : EvalLipschitzCompact D E 1)
    (hagree : SingleC1Agree D E) {Ω : Set (E.Pt D)} {u : E.Pt D → ℝ}
    (hu : (fun y => (u y : ℂ)) ∈ Tuple.singleTestFns D E Ω) :
    u ∈ c1SupportedIn D E Ω := by
  obtain ⟨hsmooth, hcpt, hsub⟩ := hu
  have hc1 : IsC1Fn D E u := ((hagree u).1).1 (hsmooth 1)
  have hsupp := ((hagree u).2 hc1).2
  rw [hsupp] at hcpt hsub
  refine ⟨hc1, isCompactQ_of_singleSet D E heval hcpt, fun y hy => ?_⟩
  exact hsub (show singleton D E y ∈ Tuple.singleSet D E (supportQ D E u) from hy)
private theorem productSet_subset_sep (n : ℕ) : ProductSetSubsetSepC1 D E n := by
  intro A hA f hf
  have hf' : ∀ l, f l ∈ c1SupportedIn D E (A l) := fun l => hf l (Set.mem_univ l)
  refine ⟨fun l => (hf' l).1, fun l => (hf' l).2.1, fun l l' hll' => ?_⟩
  exact (hA l l' hll').mono (hf' l).2.2 (hf' l').2.2
private theorem apply_congr {n : ℕ} {K : Set (FnTuple D E n)} (Ψ : K → ℝ) {a b : FnTuple D E n}
    (ha : a ∈ K) (hb : b ∈ K) (hab : a = b) : Ψ ⟨a, ha⟩ = Ψ ⟨b, hb⟩ := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.MultilinearProducts.eval_eq_of_eq <;> assumption
private theorem multilinear_on_products (hlin : ∀ A : Set (E.Pt D),
    VectorClasses.IsLinearSubspaceSet D E (c1SupportedIn D E A)) (n : ℕ) :
    MultilinearOnDisjointProducts D E n := by
  intro Ψ hΨ A hA
  have hprod := productSet_subset_sep D E n A hA
  refine ⟨hprod, ?_⟩
  intro g hg i u hu v hv α β hgu hgv hgw
  obtain ⟨W, hW⟩ := hlin (A i)
  have hmem : ∀ w, w ∈ W ↔ w ∈ c1SupportedIn D E (A i) := fun w => by
    rw [← hW]
    rfl
  have hsmul : ∀ (c : ℝ) (w : E.Pt D → ℝ), w ∈ c1SupportedIn D E (A i) →
      c • w ∈ c1SupportedIn D E (A i) := fun c w hw =>
    (hmem _).1 (W.smul_mem c ((hmem w).2 hw))
  have hupd : ∀ w, w ∈ c1SupportedIn D E (A i) → Function.update g i w ∈
      productSet D E (fun l => c1SupportedIn D E (A l)) := by
    intro w hw l _
    by_cases hl : l = i
    · subst hl
      simpa using hw
    · simpa [Function.update_of_ne hl] using hg l (Set.mem_univ l)
  have hs := hprod (hupd _ (hsmul α u hu))
  have ht := hprod (hupd _ (hsmul β v hv))
  have hoff : ∀ l, l ≠ i → (⟨_, hs⟩ : sepC1Tuples D E n).1 l =
      (⟨_, ht⟩ : sepC1Tuples D E n).1 l := fun l hl => by
    simp [Function.update_of_ne hl]
  have haddEq : Function.update (Function.update g i (α • u)) i
      (Function.update g i (α • u) i + Function.update g i (β • v) i) =
      Function.update g i (α • u + β • v) := by
    simp
  have haddMem : Function.update (Function.update g i (α • u)) i
      (Function.update g i (α • u) i + Function.update g i (β • v) i) ∈
      sepC1Tuples D E n := by
    rw [haddEq]
    exact hgw
  have hadd := (hΨ i ⟨_, hs⟩ ⟨_, ht⟩ hoff).1 haddMem
  have hhom : ∀ (c : ℝ) (w : E.Pt D → ℝ)
      (hw : Function.update g i w ∈ sepC1Tuples D E n)
      (hcw : Function.update g i (c • w) ∈ sepC1Tuples D E n),
      Ψ ⟨_, hcw⟩ = c * Ψ ⟨_, hw⟩ := by
    intro c w hw hcw
    have hEq : Function.update (Function.update g i w) i (c • Function.update g i w i) =
        Function.update g i (c • w) := by
      simp
    have hMem : Function.update (Function.update g i w) i (c • Function.update g i w i) ∈
        sepC1Tuples D E n := by
      rw [hEq]
      exact hcw
    have h := (hΨ i ⟨_, hw⟩ ⟨_, hw⟩ (fun _ _ => rfl)).2 c hMem
    rw [← h]
    exact apply_congr D E Ψ hcw hMem hEq.symm
  calc Ψ ⟨_, hgw⟩ = Ψ ⟨_, haddMem⟩ := apply_congr D E Ψ hgw haddMem haddEq.symm
    _ = Ψ ⟨_, hs⟩ + Ψ ⟨_, ht⟩ := hadd
    _ = α * Ψ ⟨_, hgu⟩ + β * Ψ ⟨_, hgv⟩ := by rw [hhom α u hgu hs, hhom β v hgv ht]
private theorem zero_at_zero_argument {n : ℕ} (K : Set (FnTuple D E n)) :
    MultilinearZeroAtZeroCoordinate D E K := by
  intro Ψ hΨ h i hi
  have hEq : Function.update h.1 i ((0 : ℝ) • h.1 i) = h.1 := by
    rw [zero_smul, ← hi]
    exact Function.update_eq_self i h.1
  have hMem : Function.update h.1 i ((0 : ℝ) • h.1 i) ∈ K := by
    rw [hEq]
    exact h.2
  have h0 := (hΨ i h h (fun _ _ => rfl)).2 0 hMem
  have h1 : Ψ h = Ψ ⟨_, hMem⟩ := apply_congr D E Ψ h.2 hMem hEq.symm
  rw [h1, h0, zero_mul]
abbrev _root_.YangMills.DeltaSharedProofs.p500495 := @zero_at_zero_argument
private theorem disjointCompact_infDist (hmet : DistIsMetric D E 1) :
    DisjointCompactInfDistPosFinite D E := by
  obtain ⟨-, hzero, hcomm, htriangle⟩ := hmet
  intro K L hK hL hKL ⟨z, hz⟩ ⟨z', hz'⟩
  obtain ⟨r, hr, hsep⟩ := exists_pos_sep_of_disjoint (quotDist D E) (quotDist_nonneg D E)
    (fun x y h => by
      have h1 : Tuple.tupleDist D E (singleton D E x) (singleton D E y) = 0 := by
        rw [tupleDist_singleton]
        exact h
      exact congrFun ((hzero _ _).1 h1) ⟨0, (1 : ℕ+).pos⟩)
    (fun x y => by
      rw [← tupleDist_singleton, ← tupleDist_singleton]
      exact hcomm _ _)
    (fun x y w => by
      simp only [← tupleDist_singleton]
      exact htriangle _ _ _)
    hK hL hKL
  constructor
  · refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hr) ?_
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (hsep x hx y hy)
  · refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := quotDist D E z z'))
    exact (iInf₂_le z hz).trans (iInf₂_le z' hz')
theorem claim_of_facts (hvec : VectorClasses.Claim) (htup : TupleFacts.AllFacts) : Claim := by
  intro D E n _
  obtain ⟨-, -, hmet, -, -, -, -, -, -, -, -, -, heval, -, -, -, hagree, -⟩ := htup D E 1
  have hlin : ∀ A : Set (E.Pt D),
      VectorClasses.IsLinearSubspaceSet D E (c1SupportedIn D E A) :=
    fun A => ((hvec D E).1 A).2.1
  exact ⟨⟨hlin, fun Ω _ u hu => mem_c1SupportedIn_of_real_test D E heval hagree hu⟩,
    productSet_subset_sep D E n, multilinear_on_products D E hlin n,
    zero_at_zero_argument D E _, disjointCompact_infDist D E hmet⟩
end YangMills.Construction.PeriodicSpace.Kind.DisjointProducts
