import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClasses
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.MultilinearProducts
open Function
variable {D : Params} {E : Kind}
structure SupportClassPair {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) (P : (E.Pt D → ℝ) → Prop) : Prop where
  memV : ∀ A g, g ∈ V A ↔ P g ∧ IsCompactQ D E (supportQ D E g) ∧ supportQ D E g ⊆ A
  memK : ∀ f, f ∈ K ↔ (∀ i, P (f i)) ∧ CompactDisjointSupports D E f ∧
    ∀ i, supportQ D E (f i) ⊆ centredBall D E ρ
  comb : ∀ A, ∀ u ∈ V A, ∀ v ∈ V A, ∀ a b : ℝ, a • u + b • v ∈ V A
theorem mem_productSet_iff {n : ℕ} {W : Fin n → Set (E.Pt D → ℝ)} {g : FnTuple D E n} :
    g ∈ productSet D E W ↔ ∀ l, g l ∈ W l := by
  simp [productSet, Set.mem_pi]
theorem update_mem_productSet {n : ℕ} {W : Fin n → Set (E.Pt D → ℝ)} {g : FnTuple D E n}
    (hg : g ∈ productSet D E W) (i : Fin n) {u : E.Pt D → ℝ} (hu : u ∈ W i) :
    update g i u ∈ productSet D E W := by
  rw [mem_productSet_iff] at hg ⊢
  intro l
  by_cases hl : l = i
  · subst hl
    simpa using hu
  · simpa [update_of_ne hl] using hg l
theorem eval_eq_of_eq {n : ℕ} {K : Set (FnTuple D E n)} (Ψ : K → ℝ) {x y : FnTuple D E n}
    (hx : x ∈ K) (hy : y ∈ K) (h : x = y) : Ψ ⟨x, hx⟩ = Ψ ⟨y, hy⟩ := by
  subst h
  rfl
theorem additive_of_multilinear {n : ℕ} {K : Set (FnTuple D E n)} {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) (i : Fin n) {x y z : FnTuple D E n}
    (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) (hag : ∀ l, l ≠ i → x l = y l)
    (hzeq : z = update x i (x i + y i)) : Ψ ⟨z, hz⟩ = Ψ ⟨x, hx⟩ + Ψ ⟨y, hy⟩ := by
  subst hzeq
  exact (hΨ i ⟨x, hx⟩ ⟨y, hy⟩ hag).1 hz
theorem homogeneous_of_multilinear {n : ℕ} {K : Set (FnTuple D E n)} {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) (i : Fin n) {x z : FnTuple D E n}
    (hx : x ∈ K) (hz : z ∈ K) (a : ℝ) (hzeq : z = update x i (a • x i)) :
    Ψ ⟨z, hz⟩ = a * Ψ ⟨x, hx⟩ := by
  subst hzeq
  exact (hΨ i ⟨x, hx⟩ ⟨x, hx⟩ (fun _ _ => rfl)).2 a hz
theorem onProduct_of_multilinear {n : ℕ} {K : Set (FnTuple D E n)}
    {W : Fin n → Set (E.Pt D → ℝ)} {Ψ : K → ℝ} (hΨ : IsMultilinearOn D E K Ψ)
    (hsub : productSet D E W ⊆ K)
    (hW : ∀ i, ∀ u ∈ W i, ∀ v ∈ W i, ∀ a b : ℝ, a • u + b • v ∈ W i) :
    IsMultilinearOnProduct D E K W Ψ := by
  refine ⟨hsub, ?_⟩
  intro g hg i u hu' v hv' a b hu hv hw
  have hscale : ∀ (c : ℝ) (x : E.Pt D → ℝ), x ∈ W i → c • x ∈ W i := by
    intro c x hx
    simpa using hW i x hx x hx c 0
  have hau : update g i (a • u) ∈ K := hsub (update_mem_productSet hg i (hscale a u hu'))
  have hbv : update g i (b • v) ∈ K := hsub (update_mem_productSet hg i (hscale b v hv'))
  have e₁ := homogeneous_of_multilinear hΨ i hu hau a (by simp)
  have e₂ := homogeneous_of_multilinear hΨ i hv hbv b (by simp)
  have e₃ := additive_of_multilinear hΨ i hau hbv hw
    (fun l hl => by simp [update_of_ne hl]) (by simp)
  rw [e₃, e₁, e₂]
theorem relations_of_onProduct {n : ℕ} {K : Set (FnTuple D E n)}
    {W : Fin n → Set (E.Pt D → ℝ)} {Ψ : K → ℝ} (hN : IsMultilinearOnProduct D E K W Ψ)
    (i : Fin n) (f f' : K) (hag : ∀ l, l ≠ i → f.1 l = f'.1 l)
    (hp : f.1 ∈ productSet D E W) (hp' : f'.1 ∈ productSet D E W) :
    (∀ hSum : update f.1 i (f.1 i + f'.1 i) ∈ K, Ψ ⟨_, hSum⟩ = Ψ f + Ψ f') ∧
      ∀ (a : ℝ) (hScaled : update f.1 i (a • f.1 i) ∈ K), Ψ ⟨_, hScaled⟩ = a * Ψ f := by
  have hu' : f.1 i ∈ W i := mem_productSet_iff.1 hp i
  have hv' : f'.1 i ∈ W i := mem_productSet_iff.1 hp' i
  have eu : update f.1 i (f.1 i) = f.1 := update_eq_self i f.1
  have ev : update f.1 i (f'.1 i) = f'.1 := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [update_of_ne hl, hag l hl]
  have hu : update f.1 i (f.1 i) ∈ K := eu.symm ▸ f.2
  have hv : update f.1 i (f'.1 i) ∈ K := ev.symm ▸ f'.2
  have vu : Ψ ⟨_, hu⟩ = Ψ f := eval_eq_of_eq Ψ hu f.2 eu
  have vv : Ψ ⟨_, hv⟩ = Ψ f' := eval_eq_of_eq Ψ hv f'.2 ev
  constructor
  · intro hSum
    have hw : update f.1 i ((1 : ℝ) • f.1 i + (1 : ℝ) • f'.1 i) ∈ K := by
      simpa using hSum
    have key := hN.2 f.1 hp i (f.1 i) hu' (f'.1 i) hv' 1 1 hu hv hw
    rw [eval_eq_of_eq Ψ hSum hw (by simp), key, vu, vv]
    ring
  · intro a hScaled
    have hw : update f.1 i (a • f.1 i + (0 : ℝ) • f.1 i) ∈ K := by
      simpa using hScaled
    have key := hN.2 f.1 hp i (f.1 i) hu' (f.1 i) hu' a 0 hu hu hw
    rw [eval_eq_of_eq Ψ hScaled hw (by simp), key, vu]
    ring
theorem disjoint_of_setInfDist_pos
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    {S S' : Set (E.Pt D)} (h : 0 < setInfDist D E S S') : Disjoint S S' := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hle : setInfDist D E S S' ≤ ENNReal.ofReal (quotDist D E z z) :=
    (iInf₂_le z hz).trans (iInf₂_le z hz')
  rw [(hM.2.1 z z).2 rfl, ENNReal.ofReal_zero] at hle
  exact absurd h (not_lt.2 hle)
theorem isCompactQ_union {S S' : Set (E.Pt D)} (hS : IsCompactQ D E S)
    (hS' : IsCompactQ D E S') : IsCompactQ D E (S ∪ S') := by
  intro U hU hc
  obtain ⟨U₁, h₁, f₁, c₁⟩ := hS U hU (Set.subset_union_left.trans hc)
  obtain ⟨U₂, h₂, f₂, c₂⟩ := hS' U hU (Set.subset_union_right.trans hc)
  exact ⟨U₁ ∪ U₂, Set.union_subset h₁ h₂, f₁.union f₂,
    Set.union_subset (c₁.trans (Set.sUnion_mono Set.subset_union_left))
      (c₂.trans (Set.sUnion_mono Set.subset_union_right))⟩
section Abstract
variable {n : ℕ} {ρ : ℝ≥0∞} {K : Set (FnTuple D E n)}
  {V : Set (E.Pt D) → Set (E.Pt D → ℝ)} {P : (E.Pt D → ℝ) → Prop}
theorem productsSubset_of_pair (C : SupportClassPair ρ K V P)
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E) :
    ProductsSubset D E ρ K V := by
  intro A hA f hf
  rw [mem_productSet_iff] at hf
  have hv := fun l => (C.memV _ _).1 (hf l)
  refine (C.memK f).2 ⟨fun i => (hv i).1, ⟨fun i => (hv i).2.1, fun i k hik => ?_⟩,
    fun i => (hv i).2.2.trans (hA.1 i)⟩
  exact (disjoint_of_setInfDist_pos hM (hA.2 i k hik)).mono (hv i).2.2 (hv k).2.2
theorem pairInCommonProduct_of_pair (C : SupportClassPair ρ K V P)
    (hc : QuotientCompactC1.CompactSetsThickenings D E) :
    PairInCommonProduct D E ρ K V := by
  intro i f f' hK hK' hag
  obtain ⟨hP, ⟨hcomp, hdis⟩, hball⟩ := (C.memK f).1 hK
  obtain ⟨hP', ⟨hcomp', hdis'⟩, hball'⟩ := (C.memK f').1 hK'
  have Si : pairSupports D E f f' i i = supportQ D E (f i) ∪ supportQ D E (f' i) := by
    simp [pairSupports]
  have Sl : ∀ l, l ≠ i → pairSupports D E f f' i l = supportQ D E (f l) := by
    intro l hl
    simp [pairSupports, update_of_ne hl]
  have hcompS : ∀ l, IsCompactQ D E (pairSupports D E f f' i l) := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [Si]
      exact isCompactQ_union (hcomp l) (hcomp' l)
    · rw [Sl l hl]
      exact hcomp l
  have aux : ∀ l, l ≠ i →
      Disjoint (pairSupports D E f f' i l) (pairSupports D E f f' i i) := by
    intro l hl
    rw [Si, Sl l hl, Set.disjoint_union_right]
    refine ⟨hdis l i hl, ?_⟩
    rw [hag l hl]
    exact hdis' l i hl
  have hdisS : ∀ l l', l ≠ l' →
      Disjoint (pairSupports D E f f' i l) (pairSupports D E f f' i l') := by
    intro l l' hll
    by_cases hl : l = i
    · subst hl
      exact (aux l' (Ne.symm hll)).symm
    · by_cases hl' : l' = i
      · subst hl'
        exact aux l hl
      · rw [Sl l hl, Sl l' hl']
        exact hdis l l' hll
  have hballS : ∀ l, pairSupports D E f f' i l ⊆ centredBall D E ρ := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [Si]
      exact Set.union_subset (hball l) (hball' l)
    · rw [Sl l hl]
      exact hball l
  have hmem : f ∈ productSet D E (fun l => V (pairSupports D E f f' i l)) := by
    rw [mem_productSet_iff]
    intro l
    refine (C.memV _ _).2 ⟨hP l, hcomp l, ?_⟩
    by_cases hl : l = i
    · subst hl
      rw [Si]
      exact Set.subset_union_left
    · rw [Sl l hl]
  have hmem' : f' ∈ productSet D E (fun l => V (pairSupports D E f f' i l)) := by
    rw [mem_productSet_iff]
    intro l
    refine (C.memV _ _).2 ⟨hP' l, hcomp' l, ?_⟩
    by_cases hl : l = i
    · subst hl
      rw [Si]
      exact Set.subset_union_right
    · rw [Sl l hl, hag l hl]
  refine ⟨hcompS, hdisS, ⟨hballS, fun l l' hll => hc.1 _ _ (hcompS l) (hcompS l') (hdisS l l' hll)⟩,
    hmem, hmem', fun a a' => update_mem_productSet hmem i ?_⟩
  exact C.comb _ _ (mem_productSet_iff.1 hmem i) _ (mem_productSet_iff.1 hmem' i) a a'
theorem multilinearIffOnProducts_of_pair (C : SupportClassPair ρ K V P)
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hc : QuotientCompactC1.CompactSetsThickenings D E) :
    MultilinearIffOnProducts D E ρ K V := by
  intro Ψ
  constructor
  · intro hΨ A hA
    exact onProduct_of_multilinear hΨ (productsSubset_of_pair C hM A hA) (fun i => C.comb (A i))
  · intro hN i f f' hag
    obtain ⟨-, -, hball, hp, hp', -⟩ := pairInCommonProduct_of_pair C hc i f.1 f'.1 f.2 f'.2 hag
    exact relations_of_onProduct (hN _ hball) i f f' hag hp hp'
theorem eqUnionProducts_of_pair (C : SupportClassPair ρ K V P)
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hc : QuotientCompactC1.CompactSetsThickenings D E) :
    EqUnionProducts D E ρ K V := by
  apply Set.Subset.antisymm
  · intro f hf
    obtain ⟨hP, ⟨hcomp, hdis⟩, hball⟩ := (C.memK f).1 hf
    refine Set.mem_iUnion₂.2 ⟨fun l => supportQ D E (f l),
      ⟨hball, fun l l' hll => hc.1 _ _ (hcomp l) (hcomp l') (hdis l l' hll)⟩, ?_⟩
    rw [mem_productSet_iff]
    exact fun l => (C.memV _ _).2 ⟨hP l, hcomp l, subset_rfl⟩
  · exact Set.iUnion₂_subset fun A hA => productsSubset_of_pair C hM A hA
theorem productStructure_of_pair (C : SupportClassPair ρ K V P)
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hc : QuotientCompactC1.CompactSetsThickenings D E) :
    ProductStructure D E ρ K V := by
  refine ⟨productsSubset_of_pair C hM, pairInCommonProduct_of_pair C hc,
    multilinearIffOnProducts_of_pair C hM hc, ?_, eqUnionProducts_of_pair C hM hc⟩
  intro Ψ hΨ f i hi
  have key := homogeneous_of_multilinear hΨ i f.2 f.2 0 (by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hi]
    · simp [update_of_ne hl])
  simpa using key
end Abstract
theorem exists_uniform_lower_bound {n : ℕ} (hn : 1 ≤ n) (S : Fin n → Set (E.Pt D))
    (hpos : ∀ l l', l ≠ l' → 0 < setInfDist D E (S l) (S l')) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l l', l ≠ l' → ENNReal.ofReal δ ≤ setInfDist D E (S l) (S l') := by
  classical
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  let m : Fin n × Fin n → ℝ≥0∞ := fun p =>
    if p.1 ≠ p.2 then min 1 (setInfDist D E (S p.1) (S p.2)) else 1
  obtain ⟨p, hp⟩ := Finite.exists_min m
  have hm0 : 0 < m p := by
    by_cases h : p.1 ≠ p.2
    · simp only [m, if_pos h]
      exact lt_min one_pos (hpos _ _ h)
    · simp only [m, if_neg h]
      exact one_pos
  have hm1 : m p ≤ 1 := by
    by_cases h : p.1 ≠ p.2
    · simp only [m, if_pos h]
      exact min_le_left _ _
    · simp only [m, if_neg h]
      exact le_rfl
  have hfin : m p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hm1
  refine ⟨(m p).toReal, ENNReal.toReal_pos hm0.ne' hfin, fun l l' hl => ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  have h₁ := hp (l, l')
  have h₂ : m (l, l') = min 1 (setInfDist D E (S l) (S l')) := by
    simp only [m]
    exact if_pos hl
  rw [h₂] at h₁
  exact h₁.trans (min_le_right _ _)
theorem exists_near_of_mem_openThickening {S : Set (E.Pt D)} {hS : IsCompactQ D E S} {η : ℝ}
    {hη : 0 < η} {y : E.Pt D} (hy : y ∈ openThickening D E S hS η hη) :
    ∃ s ∈ S, quotDist D E y s < η := by
  have h : setInfDist D E {y} S < ENNReal.ofReal η := hy
  unfold setInfDist at h
  simp only [iInf_lt_iff] at h
  obtain ⟨z, hz, s, hs, hlt⟩ := h
  have hzy : z = y := hz
  subst hzy
  exact ⟨s, hs, (ENNReal.ofReal_lt_ofReal_iff hη).1 hlt⟩
theorem disjoint_closureQ_openThickening
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    {S S' : Set (E.Pt D)} (hS : IsCompactQ D E S) (hS' : IsCompactQ D E S')
    {δ : ℝ} (hδ : 0 < δ) (hη : 0 < δ / 3) (hd : ENNReal.ofReal δ ≤ setInfDist D E S S') :
    Disjoint (closureQ D E (openThickening D E S hS (δ / 3) hη))
      (closureQ D E (openThickening D E S' hS' (δ / 3) hη)) := by
  obtain ⟨hnn, -, hsymm, htri, -⟩ := hM
  rw [Set.disjoint_left]
  intro y hy hy'
  have hy₁ : ∀ r : ℝ, 0 < r →
      ∃ a ∈ openThickening D E S hS (δ / 3) hη, quotDist D E y a < r := hy
  have hy₂ : ∀ r : ℝ, 0 < r →
      ∃ b ∈ openThickening D E S' hS' (δ / 3) hη, quotDist D E y b < r := hy'
  obtain ⟨a, ha, hya⟩ := hy₁ (δ / 6) (by positivity)
  obtain ⟨b, hb, hyb⟩ := hy₂ (δ / 6) (by positivity)
  obtain ⟨s, hs, has⟩ := exists_near_of_mem_openThickening ha
  obtain ⟨s', hs', hbs⟩ := exists_near_of_mem_openThickening hb
  have hlow : ENNReal.ofReal δ ≤ ENNReal.ofReal (quotDist D E s s') :=
    hd.trans ((iInf₂_le s hs).trans (iInf₂_le s' hs'))
  have hlow' : δ ≤ quotDist D E s s' := (ENNReal.ofReal_le_ofReal_iff (hnn _ _)).1 hlow
  have t₁ := htri s a s'
  have t₂ := htri a y s'
  have t₃ := htri y b s'
  have e₁ := hsymm s a
  have e₂ := hsymm a y
  linarith
theorem c1SupportedIn_mono {A A' : Set (E.Pt D)} (h : A ⊆ A') :
    c1SupportedIn D E A ⊆ c1SupportedIn D E A' :=
  fun _ hu => ⟨hu.1, hu.2.1, hu.2.2.trans h⟩
theorem multilinearIffOnOpenProducts_of_pair {n : ℕ} (hn : 1 ≤ n)
    (C : SupportClassPair (⊤ : ℝ≥0∞) (sepC1Tuples D E n) (c1SupportedIn D E) (IsC1Fn D E))
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hc : QuotientCompactC1.CompactSetsThickenings D E) :
    MultilinearIffOnOpenProducts D E n := by
  intro Ψ
  constructor
  · intro hΨ O _ hdis
    refine onProduct_of_multilinear hΨ ?_ (fun i => C.comb (O i))
    intro f hf
    rw [mem_productSet_iff] at hf
    have hsub : ∀ l, O l ⊆ closureQ D E (O l) := by
      intro l x hx r hr
      refine ⟨x, hx, ?_⟩
      rw [(hM.2.1 x x).2 rfl]
      exact hr
    refine (C.memK f).2 ⟨fun i => (hf i).1, ⟨fun i => (hf i).2.1, fun i k hik => ?_⟩, ?_⟩
    · exact (hdis i k hik).mono ((hf i).2.2.trans (hsub i)) ((hf k).2.2.trans (hsub k))
    · intro i
      simp [centredBall]
  · intro hN i f f' hag
    obtain ⟨hcomp, -, hball, hp, hp', -⟩ := pairInCommonProduct_of_pair C hc i f.1 f'.1 f.2 f'.2 hag
    obtain ⟨δ, hδ, hbound⟩ := exists_uniform_lower_bound hn _ hball.2
    have hη : 0 < δ / 3 := by positivity
    let O : Fin n → Set (E.Pt D) := fun l =>
      openThickening D E (pairSupports D E f.1 f'.1 i l) (hcomp l) (δ / 3) hη
    have hopen : ∀ l, IsOpenQ D E (O l) := fun l => (hc.2.1 _ (hcomp l) _ hη).1
    have hin : ∀ l, pairSupports D E f.1 f'.1 i l ⊆ O l :=
      fun l => (hc.2.1 _ (hcomp l) _ hη).2
    have hdisO : ∀ l l', l ≠ l' → Disjoint (closureQ D E (O l)) (closureQ D E (O l')) :=
      fun l l' hll =>
        disjoint_closureQ_openThickening hM (hcomp l) (hcomp l') hδ hη (hbound l l' hll)
    have hmono : ∀ g : FnTuple D E n,
        g ∈ productSet D E (fun l => c1SupportedIn D E (pairSupports D E f.1 f'.1 i l)) →
        g ∈ productSet D E (fun l => c1SupportedIn D E (O l)) := by
      intro g hg
      rw [mem_productSet_iff] at hg ⊢
      exact fun l => c1SupportedIn_mono (hin l) (hg l)
    exact relations_of_onProduct (hN O hopen hdisO) i f f' hag (hmono _ hp) (hmono _ hp')
theorem lincomb_mem_of_linearSubspaceSet {V : Set (E.Pt D → ℝ)}
    (hV : VectorClasses.IsLinearSubspaceSet D E V) :
    ∀ u ∈ V, ∀ v ∈ V, ∀ a b : ℝ, a • u + b • v ∈ V := by
  obtain ⟨W, rfl⟩ := hV
  intro u hu v hv a b
  exact W.add_mem (W.smul_mem a hu) (W.smul_mem b hv)
theorem statement_holds (hClasses : VectorClasses.Claim)
    (hSpace : QuotientCompactC1.Claim) : Statement := by
  intro D E n hn
  obtain ⟨hM, -, -, hc, -⟩ := hSpace D E
  have hvs := fun A => ((hClasses D E).1 A)
  have Csep : ∀ ρ : ℝ≥0∞, SupportClassPair ρ (sepC1TuplesWithin D E n (centredBall D E ρ))
      (c1SupportedIn D E) (IsC1Fn D E) := fun ρ =>
    ⟨fun _ _ => Iff.rfl,
      fun _ => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩,
      fun A => lincomb_mem_of_linearSubspaceSet (hvs A).2.1⟩
  have Clip : ∀ ρ : ℝ≥0∞, SupportClassPair ρ (sepLipTuplesWithin D E n (centredBall D E ρ))
      (lipschitzSupportedIn D E) (IsLipschitzQ D E) := fun ρ =>
    ⟨fun _ _ => Iff.rfl,
      fun _ => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩,
      fun A => lincomb_mem_of_linearSubspaceSet (hvs A).1⟩
  have Call : SupportClassPair (⊤ : ℝ≥0∞) (sepC1Tuples D E n) (c1SupportedIn D E)
      (IsC1Fn D E) :=
    ⟨fun _ _ => Iff.rfl,
      fun _ => ⟨fun h => ⟨h.1, h.2, fun _ => by simp [centredBall]⟩, fun h => ⟨h.1, h.2.1⟩⟩,
      fun A => lincomb_mem_of_linearSubspaceSet (hvs A).2.1⟩
  exact ⟨fun ρ _ => ⟨productStructure_of_pair (Csep ρ) hM hc, productStructure_of_pair (Clip ρ) hM hc⟩,
    multilinearIffOnOpenProducts_of_pair hn Call hM hc⟩
end YangMills.Construction.PeriodicSpace.Kind.MultilinearProducts
