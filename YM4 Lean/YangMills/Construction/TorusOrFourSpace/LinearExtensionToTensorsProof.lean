import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.FinitePartitionsOfUnityAtAGivenScale
import YangMills.Construction.TorusOrFourSpace.LinearExtensionToTensors
import YangMills.Construction.TorusOrFourSpace.OrderedMomentsOfAFamilyAreMultilinear
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.TensorExtension
section
private theorem multilinearMap_relation {X ι : Type} [Fintype ι] (n : ℕ) :
    ∀ (M : MultilinearMap ℝ (fun _ : Fin n => X → ℝ) ℝ) (u : ι → Fin n → X → ℝ) (c : ι → ℝ),
      (∀ x : Fin n → X, ∑ j, c j * ∏ i, u j i (x i) = 0) → ∑ j, c j * M (u j) = 0 := by
  induction n with
  | zero =>
    intro M u c h
    have h0 : ∑ j, c j = 0 := by simpa using h (fun i => i.elim0)
    have hM : ∀ j, M (u j) = M 0 := fun j => congrArg M (Subsingleton.elim _ _)
    simp only [hM]
    rw [← Finset.sum_mul, h0, zero_mul]
  | succ n ih =>
    intro M u c h
    classical
    let W : Submodule ℝ (X → ℝ) := Submodule.span ℝ (Set.range fun j => u j 0)
    have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    let b := Module.finBasis ℝ W
    let w : ι → W := fun j => ⟨u j 0, Submodule.subset_span ⟨j, rfl⟩⟩
    let lam : ι → Fin (Module.finrank ℝ W) → ℝ := fun j a => b.repr (w j) a
    have hu : ∀ j, u j 0 = ∑ a, lam j a • (b a : X → ℝ) := by
      intro j
      have h1 := congrArg Subtype.val (b.sum_repr (w j))
      rw [AddSubmonoidClass.coe_finsetSum] at h1
      exact h1.symm
    have key : ∀ a, ∑ j, (c j * lam j a) *
        (M.curryLeft (b a : X → ℝ)) (fun i => u j i.succ) = 0 := by
      intro a
      refine ih _ _ _ fun x => ?_
      have hz : ∑ a', (∑ j, c j * lam j a' * ∏ i, u j i.succ (x i)) • b a' = 0 := by
        apply Subtype.ext
        funext x0
        have h1 := h (Fin.cons x0 x)
        rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
          Pi.zero_apply]
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at h1
        rw [← h1]
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hu j, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      exact (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hz a
    have hM : ∀ j, M (u j) =
        ∑ a, lam j a * (M.curryLeft (b a : X → ℝ)) (fun i => u j i.succ) := by
      intro j
      have h1 : M (u j) = (M.curryLeft (u j 0)) (fun i => u j i.succ) := by
        rw [MultilinearMap.curryLeft_apply]
        exact congrArg M (Fin.cons_self_tail (u j)).symm
      rw [h1, hu j, map_sum, sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_apply, smul_eq_mul]
    simp only [hM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← key a]
    exact Finset.sum_congr rfl fun j _ => by ring
private theorem multilinearMap_relation_of_subspaces {X ι : Type} [Fintype ι] {n : ℕ}
    (W : Fin n → Submodule ℝ (X → ℝ)) (M : MultilinearMap ℝ (fun l => W l) ℝ)
    (u : ι → Fin n → X → ℝ) (hu : ∀ j l, u j l ∈ W l) (c : ι → ℝ)
    (h : ∀ x : Fin n → X, ∑ j, c j * ∏ i, u j i (x i) = 0) :
    ∑ j, c j * M (fun l => ⟨u j l, hu j l⟩) = 0 := by
  have hp : ∀ l, ∃ p : (X → ℝ) →ₗ[ℝ] W l, p ∘ₗ (W l).subtype = LinearMap.id := fun l =>
    LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
  choose p hp using hp
  have hval : ∀ j, (M.compLinearMap p) (u j) = M (fun l => ⟨u j l, hu j l⟩) := by
    intro j
    rw [MultilinearMap.compLinearMap_apply]
    refine congrArg M (funext fun l => ?_)
    exact LinearMap.congr_fun (hp l) ⟨u j l, hu j l⟩
  have h1 := multilinearMap_relation n (M.compLinearMap p) u c h
  simpa only [hval] using h1
end
section
private theorem exists_pos_ofReal_le {T : Type} [Finite T] (s : T → ℝ≥0∞) (hs : ∀ t, 0 < s t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, ENNReal.ofReal δ ≤ s t := by
  have h1 : ∀ t, ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), ENNReal.ofReal δ ≤ s t := fun t => by
    have h2 : ∀ᶠ δ : ℝ in nhds 0, ENNReal.ofReal δ < s t :=
      (ENNReal.continuous_ofReal.tendsto 0).eventually_lt_const (by simpa using hs t)
    exact (h2.filter_mono nhdsWithin_le_nhds).mono fun δ hδ => hδ.le
  obtain ⟨δ, hδ, hpos⟩ := ((Filter.eventually_all.2 h1).and self_mem_nhdsWithin).exists
  exact ⟨δ, hpos, hδ⟩
variable {X : Type*} (d : X → X → ℝ)
private theorem isCompactWrt_iUnion {T : Type} [Finite T] (Z : T → Set X)
    (hZ : ∀ t, MetricNotions.IsCompactWrt d (Z t)) :
    MetricNotions.IsCompactWrt d (⋃ t, Z t) := by
  intro 𝒰 hU hcov
  have h1 : ∀ t, ∃ 𝒰' ⊆ 𝒰, 𝒰'.Finite ∧ Z t ⊆ ⋃₀ 𝒰' := fun t =>
    hZ t 𝒰 hU ((Set.subset_iUnion Z t).trans hcov)
  choose 𝒱 hsub hfin hcov' using h1
  refine ⟨⋃ t, 𝒱 t, Set.iUnion_subset hsub, Set.finite_iUnion hfin, Set.iUnion_subset fun t => ?_⟩
  exact (hcov' t).trans (Set.sUnion_mono (Set.subset_iUnion 𝒱 t))
end
variable {D : Params} {E : Kind}
private theorem exists_multilinearMap_of_subspaces {n : ℕ} {Ψ : sepC1Tuples D E n → ℝ}
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E n) Ψ)
    (W : Fin n → Submodule ℝ (E.Pt D → ℝ))
    (hW : ∀ g : FnTuple D E n, (∀ l, g l ∈ W l) → g ∈ sepC1Tuples D E n) :
    ∃ M : MultilinearMap ℝ (fun l => W l) ℝ, ∀ (g : FnTuple D E n) (hg : ∀ l, g l ∈ W l),
      M (fun l => ⟨g l, hg l⟩) = Ψ ⟨g, hW g hg⟩ := by
  have hupd : ∀ (m : (l : Fin n) → W l) (i : Fin n) (x : W i),
      (fun l => ((Function.update m i x l : W l) : E.Pt D → ℝ)) =
        Function.update (fun l => (m l : E.Pt D → ℝ)) i x := by
    intro m i x
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl]
  refine ⟨{ toFun := fun v => Ψ ⟨fun l => (v l : E.Pt D → ℝ), hW _ fun l => (v l).2⟩
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun g hg => rfl⟩
  · intro inst m i x y
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    have hx := hW _ fun l => (Function.update m i x l).2
    have hy := hW _ fun l => (Function.update m i y l).2
    have hagree : ∀ l, l ≠ i →
        (⟨_, hx⟩ : sepC1Tuples D E n).1 l = (⟨_, hy⟩ : sepC1Tuples D E n).1 l := by
      intro l hl
      simp [hl]
    have hs := (hΨ i ⟨_, hx⟩ ⟨_, hy⟩ hagree).1
    have he : Function.update (fun l => ((Function.update m i x l : W l) : E.Pt D → ℝ)) i
        (((Function.update m i x i : W i) : E.Pt D → ℝ) +
          ((Function.update m i y i : W i) : E.Pt D → ℝ)) =
        fun l => ((Function.update m i (x + y) l : W l) : E.Pt D → ℝ) := by
      rw [hupd m i (x + y), hupd m i x]
      simp
    have hmem := hW _ fun l => (Function.update m i (x + y) l).2
    have := hs (he ▸ hmem)
    refine Eq.trans ?_ this
    exact congrArg Ψ (Subtype.ext he.symm)
  · intro inst m i a x
    obtain rfl : inst = fun a b => instDecidableEqFin n a b := Subsingleton.elim _ _
    have hx := hW _ fun l => (Function.update m i x l).2
    have hs := (hΨ i ⟨_, hx⟩ ⟨_, hx⟩ fun _ _ => rfl).2 a
    have he : Function.update (fun l => ((Function.update m i x l : W l) : E.Pt D → ℝ)) i
        (a • ((Function.update m i x i : W i) : E.Pt D → ℝ)) =
        fun l => ((Function.update m i (a • x) l : W l) : E.Pt D → ℝ) := by
      rw [hupd m i (a • x), hupd m i x]
      simp
    have hmem := hW _ fun l => (Function.update m i (a • x) l).2
    have := hs (he ▸ hmem)
    rw [smul_eq_mul]
    refine Eq.trans ?_ this
    exact congrArg Ψ (Subtype.ext he.symm)
private theorem eq_zero_of_entry_eq_zero {n : ℕ} {Ψ : sepC1Tuples D E n → ℝ}
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E n) Ψ)
    (h : sepC1Tuples D E n) (i : Fin n) (hi : h.1 i = 0) : Ψ h = 0 := by
  have he : Function.update h.1 i ((0 : ℝ) • h.1 i) = h.1 := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hi]
    · simp [hl]
  have hmem : Function.update h.1 i ((0 : ℝ) • h.1 i) ∈ sepC1Tuples D E n := by
    rw [he]
    exact h.2
  have h1 := (hΨ i h h fun _ _ => rfl).2 0 hmem
  rw [zero_mul] at h1
  rw [← h1]
  exact congrArg Ψ (Subtype.ext he.symm)
private theorem mem_sepC1Tuples_of_disjoint {n : ℕ} (A : Fin n → Set (E.Pt D))
    (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l')) (g : FnTuple D E n)
    (hg : ∀ l, g l ∈ c1SupportedIn D E (A l)) : g ∈ sepC1Tuples D E n :=
  ⟨fun i => (hg i).1, fun i => (hg i).2.1, fun i k hik =>
    Set.disjoint_of_subset (hg i).2.2 (hg k).2.2 (hA i k hik)⟩
private theorem real_relation
    (h1 : VectorClasses.Claim)
    (h2 : C1ProductsAndThickenings.Statement)
    (h3 : QuotientCompactC1.Claim)
    (h4 : SmallScalePartitionsOfUnity)
    {n : ℕ} {Ψ : sepC1Tuples D E n → ℝ}
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E n) Ψ)
    {ι : Type} [Fintype ι] (f : ι → sepC1Tuples D E n) (c : ι → ℝ)
    (hrel : ∀ x : Fin n → E.Pt D, ∑ j, c j * ∏ i, (f j).1 i (x i) = 0) :
    ∑ j, c j * Ψ (f j) = 0 := by
  classical
  obtain ⟨hmet, -, -, hcomp, -⟩ := h3 D E
  obtain ⟨hnonneg, hzero, hsymm, htri, -, -⟩ := hmet
  obtain ⟨hLip, hProd, -, -⟩ := h2 D E
  have hex : ∀ A : Set (E.Pt D), ∃ W : Submodule ℝ (E.Pt D → ℝ),
      (W : Set (E.Pt D → ℝ)) = c1SupportedIn D E A := fun A => ((h1 D E).1 A).2.1
  choose cls hcls using hex
  have hmemcls : ∀ {A : Set (E.Pt D)} {g : E.Pt D → ℝ}, g ∈ cls A ↔ g ∈ c1SupportedIn D E A := by
    intro A g
    rw [← hcls A]
    rfl
  have hself : ∀ j l, (f j).1 l ∈ c1SupportedIn D E (supportQ D E ((f j).1 l)) := fun j l =>
    ⟨(f j).2.1 l, (f j).2.2.1 l, subset_rfl⟩
  have hinsupp : ∀ (u : E.Pt D → ℝ) (y : E.Pt D), u y ≠ 0 → y ∈ supportQ D E u :=
    fun u y hy r hr => ⟨y, hy, by rw [(hzero y y).2 rfl]; exact hr⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_ofReal_le
    (T := {t : ι × Fin n × Fin n // t.2.1 ≠ t.2.2})
    (fun t => setInfDist D E (supportQ D E ((f t.1.1).1 t.1.2.1))
      (supportQ D E ((f t.1.1).1 t.1.2.2)))
    (fun t => hcomp.1 _ _ ((f t.1.1).2.2.1 _) ((f t.1.1).2.2.1 _)
      ((f t.1.1).2.2.2 _ _ t.2))
  have hK : IsCompactQ D E (⋃ t : ι × Fin n, supportQ D E ((f t.1).1 t.2)) :=
    isCompactWrt_iUnion _ _ fun t => (f t.1).2.2.1 t.2
  obtain ⟨P, -, θ, hθs, hθc, hθd, hθ1⟩ := h4 D E _ hK (δ / 3) (by positivity)
  have hθC1 : ∀ k, IsC1Fn D E (θ k) := fun k => by
    have h5 : IsSmoothFn D E (θ k) := (hθs k).1
    exact show ContDiff ℝ 1 (θ k ∘ E.quotMap D) from ContDiff.of_le h5 (by simp)
  have hθLip : ∀ k, IsLipschitzQ D E (θ k) := fun k =>
    (hLip.1 (θ k) (hθC1 k) (hθc k)).2.1
  have hcut : ∀ (k : Fin P) (A : Set (E.Pt D)) (h : E.Pt D → ℝ), h ∈ c1SupportedIn D E A →
      θ k * h ∈ c1SupportedIn D E (A ∩ supportQ D E (θ k)) := fun k A h hh =>
    (hProd (θ k) (hθs k).2 (hθLip k) A h (hLip.2.1 A hh)).2.2 (hθC1 k) hh
  let piece : ι → (Fin n → Fin P) → FnTuple D E n := fun j k l => θ (k l) * (f j).1 l
  have hpiece : ∀ j k l, piece j k l ∈
      c1SupportedIn D E (supportQ D E ((f j).1 l) ∩ supportQ D E (θ (k l))) := fun j k l =>
    hcut (k l) _ _ (hself j l)
  have hpiece₁ : ∀ j k l, piece j k l ∈ c1SupportedIn D E (supportQ D E ((f j).1 l)) :=
    fun j k l =>
    ⟨(hpiece j k l).1, (hpiece j k l).2.1, (hpiece j k l).2.2.trans Set.inter_subset_left⟩
  have hpiece₂ : ∀ j k l, piece j k l ∈ c1SupportedIn D E (supportQ D E (θ (k l))) :=
    fun j k l =>
    ⟨(hpiece j k l).1, (hpiece j k l).2.1, (hpiece j k l).2.2.trans Set.inter_subset_right⟩
  have hpieceSep : ∀ j k, piece j k ∈ sepC1Tuples D E n := fun j k =>
    mem_sepC1Tuples_of_disjoint _ (f j).2.2.2 _ (hpiece₁ j k)
  have hsum : ∀ j l, (f j).1 l = ∑ k, θ k * (f j).1 l := by
    intro j l
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply]
    rw [← Finset.sum_mul]
    by_cases hy : (f j).1 l y = 0
    · simp [hy]
    · rw [hθ1 y (Set.mem_iUnion.2 ⟨(j, l), hinsupp _ _ hy⟩), one_mul]
  have hexpand : ∀ j, Ψ (f j) = ∑ k : Fin n → Fin P, Ψ ⟨piece j k, hpieceSep j k⟩ := by
    intro j
    obtain ⟨M, hM⟩ := exists_multilinearMap_of_subspaces hΨ
      (fun l => cls (supportQ D E ((f j).1 l)))
      (fun g hg => mem_sepC1Tuples_of_disjoint _ (f j).2.2.2 g
        fun l => hmemcls.1 (hg l))
    have hfj : ∀ l, (f j).1 l ∈ cls (supportQ D E ((f j).1 l)) := fun l =>
      hmemcls.2 (hself j l)
    have hterm : ∀ (l : Fin n) (k : Fin P), θ k * (f j).1 l ∈ cls (supportQ D E ((f j).1 l)) :=
      fun l k => hmemcls.2
        ⟨(hcut k _ _ (hself j l)).1, (hcut k _ _ (hself j l)).2.1,
          (hcut k _ _ (hself j l)).2.2.trans Set.inter_subset_left⟩
    have h5 : (fun l => (⟨(f j).1 l, hfj l⟩ : cls (supportQ D E ((f j).1 l)))) =
        fun l => ∑ k, (⟨θ k * (f j).1 l, hterm l k⟩ : cls (supportQ D E ((f j).1 l))) := by
      funext l
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact hsum j l
    have h6 := hM (f j).1 hfj
    rw [h5, MultilinearMap.map_sum] at h6
    refine Eq.trans ?_ (h6.symm.trans ?_)
    · exact congrArg Ψ (Subtype.ext rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      have h7 := hM (piece j k) fun l => hterm l (k l)
      exact h7.trans (congrArg Ψ (Subtype.ext rfl))
  have hone : ∀ k : Fin n → Fin P, ∑ j, c j * Ψ ⟨piece j k, hpieceSep j k⟩ = 0 := by
    intro k
    by_cases hd : ∀ l l', l ≠ l' → Disjoint (supportQ D E (θ (k l))) (supportQ D E (θ (k l')))
    · obtain ⟨M, hM⟩ := exists_multilinearMap_of_subspaces hΨ
        (fun l => cls (supportQ D E (θ (k l))))
        (fun g hg => mem_sepC1Tuples_of_disjoint _ hd g fun l => hmemcls.1 (hg l))
      have hu : ∀ j l, piece j k l ∈ cls (supportQ D E (θ (k l))) := fun j l =>
        hmemcls.2 (hpiece₂ j k l)
      have h5 := multilinearMap_relation_of_subspaces _ M (fun j => piece j k) hu c (fun x => by
        have h6 : ∀ j, c j * ∏ i, piece j k i (x i) =
            (∏ i, θ (k i) (x i)) * (c j * ∏ i, (f j).1 i (x i)) := by
          intro j
          simp only [piece, Pi.mul_apply, Finset.prod_mul_distrib]
          ring
        simp only [h6]
        rw [← Finset.mul_sum, hrel x, mul_zero])
      rw [← h5]
      exact Finset.sum_congr rfl fun j _ => by rw [hM (piece j k) (hu j)]
    · push Not at hd
      obtain ⟨l, l', hll, hnd⟩ := hd
      obtain ⟨z₀, hz₀, hz₀'⟩ := Set.not_disjoint_iff.1 hnd
      refine Finset.sum_eq_zero fun j _ => ?_
      have hdist : ∀ {S : Set (E.Pt D)} {z z' : E.Pt D}, z ∈ S → z' ∈ S →
          ∀ {η : ℝ}, 0 < η → setDiam D E S < ENNReal.ofReal η → quotDist D E z z' < η := by
        intro S z z' hz hz' η hη hdiam
        have h6 : ENNReal.ofReal (quotDist D E z z') ≤ setDiam D E S :=
          le_iSup₂_of_le z hz (le_iSup₂_of_le z' hz' le_rfl)
        exact (ENNReal.ofReal_lt_ofReal_iff hη).1 (h6.trans_lt hdiam)
      by_cases hl₁ : piece j k l = 0
      · rw [eq_zero_of_entry_eq_zero hΨ ⟨piece j k, hpieceSep j k⟩ l hl₁, mul_zero]
      by_cases hl₂ : piece j k l' = 0
      · rw [eq_zero_of_entry_eq_zero hΨ ⟨piece j k, hpieceSep j k⟩ l' hl₂, mul_zero]
      exfalso
      obtain ⟨z, hz⟩ := Function.ne_iff.1 hl₁
      obtain ⟨z', hz'⟩ := Function.ne_iff.1 hl₂
      have hzθ : θ (k l) z ≠ 0 := fun h0 => hz (by simp [piece, h0])
      have hzf : (f j).1 l z ≠ 0 := fun h0 => hz (by simp [piece, h0])
      have hzθ' : θ (k l') z' ≠ 0 := fun h0 => hz' (by simp [piece, h0])
      have hzf' : (f j).1 l' z' ≠ 0 := fun h0 => hz' (by simp [piece, h0])
      have hd₁ := hdist (hinsupp _ _ hzθ) hz₀ (η := δ / 3) (by positivity) (hθd (k l))
      have hd₂ := hdist hz₀' (hinsupp _ _ hzθ') (η := δ / 3) (by positivity) (hθd (k l'))
      have hfar : ENNReal.ofReal δ ≤ ENNReal.ofReal (quotDist D E z z') :=
        (hsep ⟨(j, l, l'), hll⟩).trans
          ((iInf₂_le z (hinsupp _ _ hzf)).trans (iInf₂_le z' (hinsupp _ _ hzf')))
      have hfar' := (ENNReal.ofReal_le_ofReal_iff (hnonneg z z')).1 hfar
      have := htri z z₀ z'
      linarith
  simp only [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun k _ => hone k
private theorem complex_relation
    (h1 : VectorClasses.Claim)
    (h2 : C1ProductsAndThickenings.Statement)
    (h3 : QuotientCompactC1.Claim)
    (h4 : SmallScalePartitionsOfUnity)
    {n : ℕ} {Ψ : sepC1Tuples D E n → ℝ}
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E n) Ψ)
    {ι : Type} [Fintype ι] (f : ι → sepC1Tuples D E n) (c : ι → ℂ)
    (hrel : ∑ j, c j • tensorFn D E (fun i y => (((f j).1 i y : ℝ) : ℂ)) = 0) :
    ∑ j, c j * ((Ψ (f j) : ℝ) : ℂ) = 0 := by
  have hpt : ∀ x : Fin n → E.Pt D,
      ∑ j, c j * ((∏ i, (f j).1 i (x i) : ℝ) : ℂ) = 0 := by
    intro x
    have h5 := congrFun hrel x
    rw [Finset.sum_apply] at h5
    simpa [tensorFn] using h5
  have hre := real_relation h1 h2 h3 h4 hΨ f (fun j => (c j).re) fun x => by
    have h5 := congrArg Complex.re (hpt x)
    simpa [Complex.re_sum, Complex.mul_re, -Complex.ofReal_prod] using h5
  have him := real_relation h1 h2 h3 h4 hΨ f (fun j => (c j).im) fun x => by
    have h5 := congrArg Complex.im (hpt x)
    simpa [Complex.im_sum, Complex.mul_im, -Complex.ofReal_prod] using h5
  apply Complex.ext
  · simpa [Complex.re_sum, Complex.mul_re] using hre
  · simpa [Complex.im_sum, Complex.mul_im] using him
private theorem uniqueLinearForm_of_relations {n : ℕ} (Ψ : sepC1Tuples D E n → ℝ)
    (hrel : ∀ (ι : Type) [Fintype ι] (f : ι → sepC1Tuples D E n) (c : ι → ℂ),
      ∑ j, c j • tensorFn D E (fun i y => (((f j).1 i y : ℝ) : ℂ)) = 0 →
        ∑ j, c j * ((Ψ (f j) : ℝ) : ℂ) = 0) :
    UniqueLinearFormOnTensors D E Ψ := by
  classical
  let t : sepC1Tuples D E n → (Fin n → E.Pt D) → ℂ :=
    fun f => tensorFn D E fun i y => ((f.1 i y : ℝ) : ℂ)
  let G := Finsupp.linearCombination ℂ t
  let L := Finsupp.linearCombination ℂ fun f : sepC1Tuples D E n => ((Ψ f : ℝ) : ℂ)
  have hker : LinearMap.ker G ≤ LinearMap.ker L := by
    intro g hg
    rw [LinearMap.mem_ker] at hg ⊢
    have h5 := hrel g.support (fun s => s.1) (fun s => g s.1) (by
      rw [Finset.sum_coe_sort g.support fun f => g f • t f]
      exact hg)
    rw [Finset.sum_coe_sort g.support fun f => g f * ((Ψ f : ℝ) : ℂ)] at h5
    exact h5
  have hrange : sepTensorSpan D E n = LinearMap.range G := by
    rw [Finsupp.range_linearCombination]
    refine congrArg (Submodule.span ℂ) (Set.ext fun F => ⟨?_, ?_⟩)
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  obtain ⟨T, hex⟩ : ∃ T : sepTensorSpan D E n →ₗ[ℂ] ℂ, ∀ f : sepC1Tuples D E n,
      T ⟨_, tensorFn_mem_sepTensorSpan D E f⟩ = ((Ψ f : ℝ) : ℂ) := by
    refine ⟨((LinearMap.ker G).liftQ L hker) ∘ₗ G.quotKerEquivRange.symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ hrange).toLinearMap, fun f => ?_⟩
    have h5 : G (Finsupp.single f 1) = t f := by simp [G]
    have h6 : (LinearEquiv.ofEq _ _ hrange)
        ⟨_, tensorFn_mem_sepTensorSpan D E f⟩ =
          ⟨G (Finsupp.single f 1), LinearMap.mem_range_self G _⟩ :=
      Subtype.ext h5.symm
    have h7 := LinearMap.quotKerEquivRange_symm_apply_image G (Finsupp.single f 1)
      (LinearMap.mem_range_self G _)
    change (LinearMap.ker G).liftQ L hker (G.quotKerEquivRange.symm
      ((LinearEquiv.ofEq _ _ hrange) ⟨_, tensorFn_mem_sepTensorSpan D E f⟩)) = _
    rw [h6, h7]
    exact (Submodule.liftQ_apply _ _ _).trans (by simp [L])
  refine ⟨T, hex, fun T' hT' => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, hf, rfl⟩ := hF
    exact (hT' ⟨f, hf⟩).trans (hex ⟨f, hf⟩).symm
  | zero =>
    exact (map_zero T').trans (map_zero T).symm
  | add a b ha hb iha ihb =>
    exact (map_add T' ⟨a, ha⟩ ⟨b, hb⟩).trans
      ((congrArg₂ (· + ·) iha ihb).trans (map_add T ⟨a, ha⟩ ⟨b, hb⟩).symm)
  | smul α a ha iha =>
    exact (map_smul T' α ⟨a, ha⟩).trans
      ((congrArg (α • ·) iha).trans (map_smul T α ⟨a, ha⟩).symm)
theorem claim_holds
    (h1 : VectorClasses.Claim)
    (h2 : C1ProductsAndThickenings.Statement)
    (h3 : QuotientCompactC1.Claim)
    (h4 : SmallScalePartitionsOfUnity)
    (h5 : OrderedMoments.MultilinearityStatement) : Claim := by
  intro D E
  have hext : ∀ (n : ℕ) (Ψ : sepC1Tuples D E n → ℝ),
      IsMultilinearOn D E (sepC1Tuples D E n) Ψ →
        ExtendsToTensorSpan D E Ψ := by
    intro n Ψ hΨ
    have hrel : ∀ (ι : Type) [Fintype ι] (f : ι → sepC1Tuples D E n) (c : ι → ℂ),
        ∑ j, c j • tensorFn D E (fun i y => (((f j).1 i y : ℝ) : ℂ)) = 0 →
          ∑ j, c j * ((Ψ (f j) : ℝ) : ℂ) = 0 := fun ι _ f c h =>
      complex_relation h1 h2 h3 h4 hΨ f c h
    exact ⟨fun J f c h => hrel (Fin J) f c h, uniqueLinearForm_of_relations Ψ hrel⟩
  refine ⟨fun n _ Ψ hΨ => hext n Ψ hΨ, fun Φ =>
    ⟨fun n hn => hext n _ (Φ.multilinear n hn), fun q hq => ?_⟩⟩
  obtain ⟨hfam, -, hhier⟩ := h5 D E
  have he : (fun f : sepC1Tuples D E q => Φ.partitionMoment f) =
      Φ.toMultilinearFamily.indexOrderedMoment hq := funext fun f => ((hhier Φ).2 q hq f).symm
  rw [he]
  exact hext q _ ((hfam Φ.toMultilinearFamily).1 q hq)
end YangMills.Construction.PeriodicSpace.Kind.TensorExtension
