import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.Continuum.FactsOfTheClassesOfTuples
import YangMills.Construction.ReflectionPositivity.ContinuityOfTheLimitOfABoundedLatticeApproximationProof
import YangMills.Construction.ReflectionPositivity.ReconstructionOfAFunctionalProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfConnectedFunctions
import YangMills.Construction.TotalDensitiesGiveASystem.ListOfAContinuousFunctionalWithAContraction
import YangMills.Construction.TotalDensitiesGiveASystem.ReconstructionOfAFamilyWithABound
import Mathlib
set_option autoImplicit false
open Filter Function Topology
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.TotalDensities.BoundedFamilyReconstruction
open YangMills.Construction.ReflectionPositivity.LimitContinuity (SatisfiesDifferenceBound)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.LatticeConventions (euclidNorm)
open YangMills.Construction.TestFunctions (c1NormR4 partialDerivR4 sharpNormR4 uniformNorm closedBallR4 setDistR4)
open YangMills.Construction.SeparatedTuples
section Continuity
private theorem uniformNorm_nonneg (g : RealValued) : 0 ≤ uniformNorm g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.uniformNorm_nonneg <;> assumption
private theorem c1NormR4_nonneg (g : RealValued) : 0 ≤ c1NormR4 g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
private theorem norm_le_c1NormR4 {g : RealValued} (hg : IsC1c g) (x : AmbientSpace) :
    ‖g x‖ ≤ c1NormR4 g := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  exact (le_ciSup (f := fun x => ‖g x‖) ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩ x).trans
    (le_max_left _ _)
private theorem c1NormR4_zero : c1NormR4 (0 : RealValued) = 0 := by apply _root_.YangMills.SharedProofs.p22097 <;> assumption
private theorem c1NormR4_pos {g : RealValued} (hg : IsC1c g) (h0 : g ≠ 0) :
    0 < c1NormR4 g := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  exact (norm_pos_iff.2 hx).trans_le (norm_le_c1NormR4 hg x)
private theorem isC1c_sub {a b : RealValued} (ha : IsC1c a)
    (hb : IsC1c b) : IsC1c (a - b) :=
  ⟨ContDiff.sub ha.1 hb.1, by simpa [sub_eq_add_neg] using ha.2.add hb.2.neg⟩
private theorem tsupport_sub_subset_of {a b : RealValued} {S : Set AmbientSpace} (hS : IsClosed S)
    (ha : tsupport a ⊆ S) (hb : tsupport b ⊆ S) : tsupport (a - b) ⊆ S := by apply _root_.YangMills.SharedProofs.p73657 <;> assumption
private theorem ofFn_isDisjointlySupported {k : ℕ} {g : Fin k → RealValued} {A : Fin k → Set AmbientSpace}
    (hA : Pairwise (Function.onFun Disjoint A)) (hg : ∀ l, IsC1c (g l))
    (hs : ∀ l, tsupport (g l) ⊆ A l) : IsDisjointlySupported (List.ofFn g) := by
  refine ⟨fun f hf => ?_, List.pairwise_ofFn.2 fun i j hij => (hA hij.ne).mono (hs i) (hs j)⟩
  obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
  exact hg l
private theorem ofFn_update_eq {k : ℕ} (g : Fin k → RealValued) (m : Fin k) (a : RealValued) :
    List.ofFn (Function.update g m a) =
      (List.ofFn g).take m ++ a :: (List.ofFn g).drop (m + 1) := by apply _root_.YangMills.SharedProofs.p53786 <;> assumption
private def IsProductBounded (σ : SepTuple → ℝ) (C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set AmbientSpace, (∀ l, IsCompact (A l)) →
    Pairwise (Function.onFun Disjoint A) →
    ∀ (g : Fin k → RealValued) (hg : IsDisjointlySupported (List.ofFn g)), (∀ l, tsupport (g l) ⊆ A l) →
      |σ ⟨List.ofFn g, hg⟩| ≤ C k A * ∏ l, c1NormR4 (g l)
private theorem exists_common_zero_of_neg {σ : SepTuple → ℝ} {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ}
    (hB : IsProductBounded σ C) {k : ℕ} (hk : 1 ≤ k) {A : Fin k → Set AmbientSpace}
    (hAc : ∀ l, IsCompact (A l)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hC : C k A < 0) {f f' : Fin k → RealValued} (hfC : ∀ l, IsC1c (f l))
    (hf'C : ∀ l, IsC1c (f' l)) (hs : ∀ l, tsupport (f l) ⊆ A l)
    (hs' : ∀ l, tsupport (f' l) ⊆ A l) : ∃ l, f l = 0 ∧ f' l = 0 := by
  by_contra hno
  have hch : ∀ l, ∃ g : RealValued, g ≠ 0 ∧ IsC1c g ∧ tsupport g ⊆ A l := by
    intro l
    by_cases h : f l = 0
    · exact ⟨f' l, fun h' => hno ⟨l, h, h'⟩, hf'C l, hs' l⟩
    · exact ⟨f l, h, hfC l, hs l⟩
  choose g hg0 hgC hgs using hch
  have hsep := ofFn_isDisjointlySupported hAd hgC hgs
  have hpos : 0 < ∏ l, c1NormR4 (g l) :=
    Finset.prod_pos fun l _ => c1NormR4_pos (hgC l) (hg0 l)
  have hb := hB k hk A hAc hAd g hsep hgs
  have hneg := mul_neg_of_neg_of_pos hC hpos
  exact absurd (abs_nonneg _) (not_le.2 (hb.trans_lt hneg))
private theorem satisfiesDifferenceBound_of (F : TupleFunctional) (hm : F.IsEntrywiseLinear)
    {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ} (hB : IsProductBounded F C)
    {N : RealValued → ℝ} (hN0 : N 0 = 0) (hNn : ∀ g, 0 ≤ N g)
    (hc : ∀ g, IsC1c g → c1NormR4 g ≤ N g) :
    SatisfiesDifferenceBound F C N := by
  intro k hk A hAc hAd f f' hf hf' hs
  have hfC : ∀ l, IsC1c (f l) := fun l =>
    hf.1 (f l) ((List.mem_ofFn' _ _).2 ⟨l, rfl⟩)
  have hf'C : ∀ l, IsC1c (f' l) := fun l =>
    hf'.1 (f' l) ((List.mem_ofFn' _ _).2 ⟨l, rfl⟩)
  have hsf : ∀ l, tsupport (f l) ⊆ A l := fun l => Set.subset_union_left.trans (hs l)
  have hsf' : ∀ l, tsupport (f' l) ⊆ A l := fun l => Set.subset_union_right.trans (hs l)
  rcases lt_or_ge (C k A) 0 with hC | hC
  · obtain ⟨l₀, h0, h0'⟩ := exists_common_zero_of_neg hB hk hAc hAd hC hfC hf'C hsf hsf'
    have hz : ∀ (g : Fin k → RealValued) (hg : IsDisjointlySupported (List.ofFn g)),
        (∀ l, tsupport (g l) ⊆ A l) → g l₀ = 0 → F ⟨List.ofFn g, hg⟩ = 0 := by
      intro g hg hgs hg0
      have hp : ∏ l, c1NormR4 (g l) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l₀) (by rw [hg0, c1NormR4_zero])
      have hb := hB k hk A hAc hAd g hg hgs
      rw [hp, mul_zero] at hb
      exact abs_nonpos_iff.1 hb
    have hsum : ∑ l, N (f l - f' l) * ∏ l' ∈ Finset.univ.erase l, max (N (f l')) (N (f' l')) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = l₀
      · subst hl
        rw [h0, h0', sub_zero, hN0, zero_mul]
      · rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hl, Finset.mem_univ l₀⟩)
          (by rw [h0, h0', hN0, max_self]), mul_zero]
    rw [hz f hf hsf h0, hz f' hf' hsf' h0', hsum]
    simp
  · set hyb : ℕ → Fin k → RealValued := fun m l => if (l : ℕ) < m then f' l else f l with hhyb
    have hybC : ∀ m l, IsC1c (hyb m l) := fun m l => by
      simp only [hhyb]
      split_ifs
      exacts [hf'C l, hfC l]
    have hybS : ∀ m l, tsupport (hyb m l) ⊆ A l := fun m l => by
      simp only [hhyb]
      split_ifs
      exacts [hsf' l, hsf l]
    have hybSep : ∀ m, IsDisjointlySupported (List.ofFn (hyb m)) := fun m =>
      ofFn_isDisjointlySupported hAd (hybC m) (hybS m)
    set d : Fin k → RealValued := fun m => f m - f' m with hd
    have hdC : ∀ m, IsC1c (d m) := fun m =>
      isC1c_sub (hfC m) (hf'C m)
    have hdS : ∀ m, tsupport (d m) ⊆ A m := fun m =>
      tsupport_sub_subset_of (hAc m).isClosed (hsf m) (hsf' m)
    set mid : Fin k → Fin k → RealValued := fun m => Function.update (hyb m) m (d m) with hmid
    have midC : ∀ m l, IsC1c (mid m l) := fun m l => by
      by_cases h : l = m
      · subst h
        simpa [hmid] using hdC l
      · simpa [hmid, Function.update_of_ne h] using hybC m l
    have midS : ∀ m l, tsupport (mid m l) ⊆ A l := fun m l => by
      by_cases h : l = m
      · subst h
        simpa [hmid] using hdS l
      · simpa [hmid, Function.update_of_ne h] using hybS m l
    have midSep : ∀ m, IsDisjointlySupported (List.ofFn (mid m)) := fun m =>
      ofFn_isDisjointlySupported hAd (midC m) (midS m)
    have hleft : ∀ m : Fin k, hyb m = Function.update (hyb m) m (f m) := fun m => by
      funext l
      by_cases h : l = m
      · subst h
        simp [hhyb]
      · simp [Function.update_of_ne h]
    have hright : ∀ m : Fin k, hyb (m + 1) = Function.update (hyb m) m (f' m) := fun m => by
      funext l
      by_cases h : l = m
      · subst h
        simp [hhyb]
      · have hne : (l : ℕ) ≠ m := fun h' => h (Fin.ext h')
        simp only [Function.update_of_ne h, hhyb]
        by_cases hlt : (l : ℕ) < m
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ (l : ℕ) < m + 1 := by omega
          simp [hlt, this]
    have step : ∀ m : Fin k, F ⟨List.ofFn (hyb m), hybSep m⟩ -
        F ⟨List.ofFn (hyb (m + 1)), hybSep (m + 1)⟩ = F ⟨List.ofFn (mid m), midSep m⟩ := fun m => by
      have h := hm ((List.ofFn (hyb m)).take m) ((List.ofFn (hyb m)).drop (m + 1)) (f m) (f' m)
        1 (-1) ⟨List.ofFn (hyb m), hybSep m⟩ ⟨List.ofFn (hyb (m + 1)), hybSep (m + 1)⟩
        ⟨List.ofFn (mid m), midSep m⟩
        (by
          show List.ofFn (hyb m) = _
          conv_lhs => rw [hleft m]
          exact ofFn_update_eq _ _ _)
        (by
          show List.ofFn (hyb (m + 1)) = _
          rw [hright m]
          exact ofFn_update_eq _ _ _)
        (by
          show List.ofFn (mid m) = _
          have ha : (1 : ℝ) • f m + (-1 : ℝ) • f' m = d m := by
            simp [hd, sub_eq_add_neg]
          rw [ha]
          exact ofFn_update_eq _ _ _)
      rw [h]
      ring
    have e0 : (⟨List.ofFn f, hf⟩ : SepTuple) = ⟨List.ofFn (hyb 0), hybSep 0⟩ :=
      Subtype.ext (congrArg List.ofFn (funext fun l => by simp [hhyb]))
    have ek : (⟨List.ofFn f', hf'⟩ : SepTuple) = ⟨List.ofFn (hyb k), hybSep k⟩ :=
      Subtype.ext (congrArg List.ofFn (funext fun l => by simp [hhyb]))
    have tele : F ⟨List.ofFn f, hf⟩ - F ⟨List.ofFn f', hf'⟩ =
        ∑ m : Fin k, F ⟨List.ofFn (mid m), midSep m⟩ := by
      rw [e0, ek, ← Finset.sum_range_sub' (fun m => F ⟨List.ofFn (hyb m), hybSep m⟩) k,
        ← Fin.sum_univ_eq_sum_range (fun m => F ⟨List.ofFn (hyb m), hybSep m⟩ -
          F ⟨List.ofFn (hyb (m + 1)), hybSep (m + 1)⟩) k]
      exact Finset.sum_congr rfl fun m _ => step m
    rw [tele, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have hself : mid m m = d m := by simp [hmid]
    calc |F ⟨List.ofFn (mid m), midSep m⟩|
        ≤ C k A * ∏ l, c1NormR4 (mid m l) := hB k hk A hAc hAd _ _ (midS m)
      _ ≤ C k A * ∏ l, N (mid m l) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => c1NormR4_nonneg _)
            fun l _ => hc _ (midC m l)) hC
      _ = C k A * (N (d m) * ∏ l ∈ Finset.univ.erase m, N (mid m l)) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m), hself]
      _ ≤ C k A * (N (f m - f' m) *
            ∏ l ∈ Finset.univ.erase m, max (N (f l)) (N (f' l))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun _ _ => hNn _) fun l hl => ?_) (hNn _)) hC
          have hlm : l ≠ m := (Finset.mem_erase.1 hl).1
          simp only [hmid, Function.update_of_ne hlm, hhyb]
          split_ifs
          exacts [le_max_right _ _, le_max_left _ _]
private theorem isAdmissiblyContinuous_of_bound (F : TupleFunctional)
    {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ} (hd : SatisfiesDifferenceBound F C c1NormR4) :
    F.IsAdmissiblyContinuous := by apply _root_.YangMills.SharedProofs.p63308 <;> assumption
end Continuity
section Bound
open YangMills.Construction.LimitTheorem YangMills.Construction.TestSpaces
variable {c : ℕ → ℝ → ℝ → ℝ} {S : CumulantFamily}
private def blockProductSum (c : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ) : ℝ :=
  ∑ η ∈ (partitionsNoSingletons (Fin n)).attach, ∏ J ∈ η.1.attach, c J.1.card d R
private theorem prod_over_blocks {n : ℕ} {η : Finset (Finset (Fin n))} (hη : η ∈ partitionsNoSingletons (Fin n))
    (a : Fin n → ℝ) : ∏ J ∈ η, ∏ i ∈ J, a i = ∏ i, a i := by
  have h₁ : η ∈ ClusterExpansion.SymGraph.partitions (Fin n) := by
    have h := hη
    simp only [partitionsNoSingletons, Finset.mem_filter] at h
    exact h.1
  have h₂ : ClusterExpansion.SymGraph.IsPartition η := by simpa [ClusterExpansion.SymGraph.partitions] using h₁
  obtain ⟨-, hd, hu⟩ := h₂
  have hu' : η.biUnion id = (Finset.univ : Finset (Fin n)) := by convert hu
  have h := Finset.prod_biUnion (s := η) (t := id) (f := a) hd
  rw [hu'] at h
  simpa using h.symm
private theorem prod_orderEmbOfFin {n : ℕ} (J : Finset (Fin n)) (a : Fin n → ℝ) :
    ∏ k, a (J.orderEmbOfFin rfl k) = ∏ i ∈ J, a i := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
private theorem sharpNormR4_nonneg (f : RealValued) : 0 ≤ sharpNormR4 1 f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
private theorem abs_centredOfCumulants_le (hc : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R)
    (hP : HasBallSupportBound c S) {n : ℕ} (X : SepTupleOfCard n) {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hb : ∀ i, ∃ x, tsupport (X.1 i) ⊆ closedBallR4 x R)
    (hs : ∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4 (tsupport (X.1 i)) (tsupport (X.1 l))) :
    |centredOfCumulants S ⟨n, X⟩| ≤ blockProductSum c n d R * ∏ i, sharpNormR4 1 (X.1 i) := by
  unfold centredOfCumulants blockProductSum
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun η _ => ?_)
  rw [Finset.abs_prod, ← prod_over_blocks η.2 fun i => sharpNormR4 1 (X.1 i), ← Finset.prod_attach η.1,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J _ => ?_
  have h2 := two_le_card_of_mem_partitionsNoSingletons η.2 J.2
  have h := hP J.1.card h2 R d hR hd (sepRestrict X J.1) (fun k => hb (J.1.orderEmbOfFin rfl k)) (fun k l hkl =>
    hs (J.1.orderEmbOfFin rfl k) (J.1.orderEmbOfFin rfl l) fun e => hkl ((J.1.orderEmbOfFin rfl).injective e))
  refine h.trans (le_of_eq ?_)
  congr 1
  exact prod_orderEmbOfFin J.1 fun i => sharpNormR4 1 (X.1 i)
private theorem exists_pos_lower_bound {ι : Type*} [Finite ι] (d : ι → ℝ) (h : ∀ i, 0 < d i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ d i := by apply _root_.YangMills.Construction.BoundsOnEverySide.SubsequentialLimits.exists_pos_lower_bound <;> assumption
open YangMills.Construction.TorusMetric (euclidNormVec) in
private theorem exists_pos_separation {n : ℕ} (K : Fin n → Set (Fin 4 → ℝ)) (hK : ∀ l, IsCompact (K l))
    (hd : ∀ l l', l ≠ l' → Disjoint (K l) (K l')) :
    ∃ d : ℝ, 0 < d ∧ ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', d ≤ euclidNormVec (x - y) := by
  have h₁ : ∀ p : Fin n × Fin n, ∃ d : ℝ, 0 < d ∧ (p.1 ≠ p.2 →
      ∀ x ∈ K p.1, ∀ y ∈ K p.2, d ≤ euclidNormVec (x - y)) := by
    rintro ⟨l, l'⟩
    by_cases hne : l = l'
    · exact ⟨1, one_pos, fun h => (h hne).elim⟩
    obtain ⟨δ, hδ, hdis⟩ := (hd l l' hne).exists_thickenings (hK l) (hK l').isClosed
    refine ⟨δ, hδ, fun _ x hx y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h₂ : ‖x - y‖ ≤ euclidNormVec (x - y) :=
      SeparatedTuplesR4.norm_le_euclidNormVec _
    have h₃ : dist y x < δ := by
      rw [dist_comm, dist_eq_norm]
      linarith
    have h₄ : y ∈ Metric.thickening δ (K l) := Metric.mem_thickening_iff.2 ⟨x, hx, h₃⟩
    have h₅ : y ∈ Metric.thickening δ (K l') := Metric.self_subset_thickening hδ _ hy
    exact Set.disjoint_left.1 hdis h₄ h₅
  choose d hd₁ hd₂ using h₁
  obtain ⟨e, he, hle⟩ := exists_pos_lower_bound d hd₁
  exact ⟨e, he, fun l l' hne x hx y hy => (hle (l, l')).trans (hd₂ (l, l') hne x hx y hy)⟩
abbrev _root_.YangMills.SharedProofs.p33435 := @exists_pos_separation
open YangMills.Construction.TorusMetric (euclidNormVec) in
private theorem exists_pos_radius {n : ℕ} (K : Fin n → Set (Fin 4 → ℝ)) (hK : ∀ l, IsCompact (K l)) :
    ∃ R : ℝ, 0 < R ∧ ∀ l, ∀ x ∈ K l, euclidNormVec x ≤ R := by
  have hc : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  obtain ⟨B, hB⟩ := (isCompact_iUnion hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, fun l x hx => ?_⟩
  have h₁ := hB x (Set.mem_iUnion.2 ⟨l, hx⟩)
  rw [Real.norm_eq_abs] at h₁
  have h₂ := le_abs_self (euclidNormVec x)
  have h₃ := le_abs_self B
  linarith
abbrev _root_.YangMills.SharedProofs.p71691 := @exists_pos_radius
private theorem mem_disjointSupportTuples_of {k : ℕ} {g : Fin k → RealValued} (hg : IsDisjointlySupported (List.ofFn g)) :
    g ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) k := by
  refine ⟨fun i => ?_, fun i i' hi => ?_⟩
  · have h := hg.1 (g i) ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
    exact ⟨h.1, h.2, Set.subset_univ _⟩
  · have hp := List.pairwise_ofFn.1 hg.2
    rcases lt_or_gt_of_ne hi with h | h
    · exact hp h
    · exact (hp h).symm
private theorem centredOf_ofFn {k : ℕ} {g : Fin k → RealValued} (hg : IsDisjointlySupported (List.ofFn g))
    (hm : g ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) k) :
    centredOf S ⟨List.ofFn g, hg⟩ = centredOfCumulants S ⟨k, ⟨g, hm⟩⟩ := by
  have e : (⟨List.ofFn g, hg⟩ : SeparatedTuples.SepTuple) = TupleLists.toList ⟨k, ⟨g, hm⟩⟩ := rfl
  show centredOfCumulants S (TupleLists.ofList ⟨List.ofFn g, hg⟩) = _
  rw [e, TupleLists.ofList_toList]
private theorem centredOf_isAdmissiblyContinuous (hbd : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hc : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R) (hP : HasBallSupportBound c S)
    (hm : (centredOf S).IsEntrywiseLinear) : (centredOf S).IsAdmissiblyContinuous := by
  have ex : ∀ (k : ℕ) (A : Fin k → Set AmbientSpace), ∃ b : ℝ, (∀ l, IsCompact (A l)) →
      Pairwise (Function.onFun Disjoint A) → ∀ (g : Fin k → RealValued) (hg : IsDisjointlySupported (List.ofFn g)),
        (∀ l, tsupport (g l) ⊆ A l) →
        |centredOf S ⟨List.ofFn g, hg⟩| ≤ b * ∏ l, c1NormR4 (g l) := by
    intro k A
    by_cases h : (∀ l, IsCompact (A l)) ∧ Pairwise (Function.onFun Disjoint A)
    · obtain ⟨hA, hD⟩ := h
      obtain ⟨d, hd, hsep⟩ := exists_pos_separation A hA fun l l' hne => hD hne
      obtain ⟨R, hR, hrad⟩ := exists_pos_radius A hA
      refine ⟨|blockProductSum c k d R| * 80 ^ k, fun _ _ g hg hs => ?_⟩
      have hm' := mem_disjointSupportTuples_of hg
      rw [centredOf_ofFn hg hm']
      have h₁ := abs_centredOfCumulants_le hc hP (⟨g, hm'⟩ : SepTupleOfCard k) hR hd (fun i => ⟨0, fun x hx => by
        have := hrad i x (hs i hx)
        simpa [closedBallR4] using this⟩) (fun i l hil => by
        refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
        exact ENNReal.ofReal_le_ofReal (hsep i l hil a (hs i ha) b (hs l hb)))
      have hC : ∀ l, IsC1c (g l) := fun l => hg.1 _ ((List.mem_ofFn' _ _).2 ⟨l, rfl⟩)
      refine h₁.trans ?_
      have h₂ : ∏ i, sharpNormR4 1 (g i) ≤ 80 ^ k * ∏ l, c1NormR4 (g l) := by
        have : ∏ i, sharpNormR4 1 (g i) ≤ ∏ i, (80 * c1NormR4 (g i)) :=
          Finset.prod_le_prod (fun i _ => sharpNormR4_nonneg _) fun i _ => by
            simpa using (hbd.2.1 1 le_rfl (g i) (hC i)).2
        rw [Finset.prod_mul_distrib] at this
        simpa using this
      calc _ ≤ |blockProductSum c k d R| * ∏ i, sharpNormR4 1 (g i) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.prod_nonneg fun i _ => sharpNormR4_nonneg _)
        _ ≤ |blockProductSum c k d R| * (80 ^ k * ∏ l, c1NormR4 (g l)) :=
            mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
        _ = _ := by ring
    · exact ⟨0, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose C hC using ex
  have hB : IsProductBounded (centredOf S) C := fun k _ A hA hD g hg hs => hC k A hA hD g hg hs
  exact isAdmissiblyContinuous_of_bound _ (satisfiesDifferenceBound_of _ hm hB c1NormR4_zero c1NormR4_nonneg fun _ _ => le_rfl)
end Bound
section Multilinear
open YangMills.Construction.LimitTheorem YangMills.Construction.TestSpaces YangMills.Construction.AmbientPoints
variable {S : CumulantFamily}
private theorem centredOf_isEntrywiseLinear (hCen : CentredOfConnectedFamilyProperties)
    (hTwo : SeparatedClasses.ClassFacts) (hcl : LimitProperties S) (s : Conventions.StandingParameters) :
    (centredOf S).IsEntrywiseLinear := by
  refine ((hTwo s).1.1 _).2 fun n hn => ?_
  let F : ConnectedFamily s .euclidean := ⟨(fun n hn X => S n hn (Continuum.SeparatedFourTuples.sepLenEquiv s n X)), hcl.multilinear s⟩
  have h := (hCen s .euclidean F).2.2.1 n hn
  have e : ofLength (fun X : R4TupleForms.FinTuple s =>
      centredOf S (R4TupleForms.listOf X)) n = ofLength F.centred n := by
    funext f
    have e₁ := centredOfMaps_r4 ((fun n hn X => S n hn (Continuum.SeparatedFourTuples.sepLenEquiv s n X))) S (fun _ _ _ => rfl) f
    refine Eq.trans ?_ e₁.symm
    exact centredOf_ofFn _ _
  rwa [e]
end Multilinear
section Translations
open YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace posClass timeBasisVec)
open YangMills.Construction.ReflectionPositivity.FormProperties (shiftedSpan)
private theorem timeComponent_smul_timeBasisVec (t : ℝ) : TimeAxis.timeComponent (t • timeBasisVec) = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
private theorem inner_posClass (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) (F G : PositiveSpan) :
    inner ℂ (posClass σ h F) (posClass σ h G) = reflectionForm σ F G :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := FormSpace (reflectionForm σ) h) F G
variable (hAct : BasicFacts.PushSpanProperties)
include hAct
private theorem pushSpan_translate_mem {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    pushSpan (translate v) F.1 ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.Reconstruction.pushSpan_translate_mem <;> assumption
private theorem shiftedSpan_val {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    (shiftedSpan v F).1 = pushSpan (translate v) F.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_shiftedSpan <;> assumption
private theorem reflectedCorrelation_eq {w : AmbientSpace} (hw : 0 ≤ TimeAxis.timeComponent w) (σ : TupleFunctional)
    (F : PositiveSpan) : reflectedCorrelation σ F w = reflectionForm σ F (shiftedSpan w F) := by apply _root_.YangMills.Construction.ReflectionPositivity.Reconstruction.reflectedCorrelation_eq <;> assumption
omit hAct in
private def shiftMap (hAct : BasicFacts.PushSpanProperties) (v : AmbientSpace) (hv : 0 ≤ TimeAxis.timeComponent v) :
    PositiveSpan →ₗ[ℂ] PositiveSpan :=
  (pushSpan (translate v)).restrict fun F hF => pushSpan_translate_mem hAct hv ⟨F, hF⟩
private theorem shiftMap_apply {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    shiftMap hAct v hv F = shiftedSpan v F :=
  Subtype.ext (shiftedSpan_val hAct hv F).symm
end Translations
section Contraction
open YangMills.Construction.LimitTheorem YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.TimeAxis (timeReflection upperHalfSpace)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec timeBasisVec temporalHyperplane)
open YangMills.Construction.ReflectionPositivity.FormProperties (shiftedSpan)
variable {c : ℕ → ℝ → ℝ → ℝ} {S : CumulantFamily}
private theorem sharpNormR4_comp (f : RealValued) (r : AmbientSpace ≃ AmbientSpace)
    (hr : ∀ x y, euclidNormVec (r x - r y) = euclidNormVec (x - y)) :
    sharpNormR4 1 (f ∘ r) = sharpNormR4 1 f := by
  have e₁ : uniformNorm (f ∘ r) = uniformNorm f := r.surjective.iSup_comp fun x => ‖f x‖
  have e₂ : TestFunctions.lipConstR4 (f ∘ r) = TestFunctions.lipConstR4 f := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
    · have h₁ := h (r.symm x) (r.symm y)
      have h₂ := hr (r.symm x) (r.symm y)
      simp only [Function.comp, Equiv.apply_symm_apply] at h₁ h₂
      unfold TestFunctions.euclidDistR4 at h₁ ⊢
      rwa [h₂.symm] at h₁
    · have h₁ := h (r x) (r y)
      unfold TestFunctions.euclidDistR4 at h₁ ⊢
      rwa [hr] at h₁
  simp only [sharpNormR4, e₁, e₂]
private theorem abs_apply_le_euclidNormVec (x : Fin 4 → ℝ) (μ : Fin 4) : |x μ| ≤ euclidNormVec x := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem exists_pos_time_floor {n : ℕ} (K : Fin n → Set AmbientSpace) (hK : ∀ l, IsCompact (K l))
    (hp : ∀ l, K l ⊆ upperHalfSpace) : ∃ δ : ℝ, 0 < δ ∧ ∀ l, ∀ x ∈ K l, δ ≤ TimeAxis.timeComponent x := by
  have h₁ : ∀ l, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K l, δ ≤ TimeAxis.timeComponent x := by
    intro l
    rcases (K l).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun x hx => by simp [h] at hx⟩
    · have hc : Continuous (TimeAxis.timeComponent : AmbientSpace → ℝ) := continuous_apply _
      obtain ⟨x₀, hx₀, hmin⟩ := (hK l).exists_isMinOn h hc.continuousOn
      exact ⟨_, hp l hx₀, fun x hx => hmin hx⟩
  choose d hd₁ hd₂ using h₁
  obtain ⟨e, he, hle⟩ := exists_pos_lower_bound d hd₁
  exact ⟨e, he, fun l x hx => (hle l).trans (hd₂ l x hx)⟩
private theorem involutive_timeReflection : Function.Involutive timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeReflection_involutive <;> assumption
private theorem invMap_timeReflection : SeparatedTuples.invMap timeReflection = timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.invMap_timeReflection <;> assumption
private theorem timeReflection_continuous : Continuous timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.continuous_timeReflection <;> assumption
private def timeReflectionHomeomorph : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := timeReflection
  invFun := timeReflection
  left_inv := involutive_timeReflection
  right_inv := involutive_timeReflection
  continuous_toFun := timeReflection_continuous
  continuous_invFun := timeReflection_continuous
private theorem euclidNormVec_timeReflection_sub (x y : AmbientSpace) :
    euclidNormVec (timeReflection x - timeReflection y) = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.isEuclidIsometry_timeReflection <;> assumption
private theorem timeComponent_timeReflection (x : AmbientSpace) :
    TimeAxis.timeComponent (timeReflection x) = -TimeAxis.timeComponent x := by
  simp [TimeAxis.timeComponent, TimeAxis.timeIdx, timeReflection]
private theorem invMap_translate (v : AmbientSpace) :
    SeparatedTuples.invMap (SeparatedTuples.translate v) = SeparatedTuples.translate (-v) :=
  funext fun x => by
    have hi : Function.Injective (SeparatedTuples.translate v) := fun a b h => add_right_cancel h
    have h := Function.leftInverse_invFun hi (x + -v)
    have e : SeparatedTuples.translate v (x + -v) = x := by simp [SeparatedTuples.translate]
    rwa [e] at h
private theorem push_val {r : AmbientSpace → AmbientSpace} {X : SepTuple} (hr : IsDisjointlySupported (pushList r X.1)) :
    (push r X).1 = X.1.map fun f => f ∘ SeparatedTuples.invMap r := by
  unfold push
  rw [dif_pos hr]
  rfl
private theorem map_eq_ofFn_get (l : List RealValued) (k : RealValued → RealValued) :
    l.map k = List.ofFn fun i => k (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn]
  rfl
private theorem exists_bound_juxt (hc : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R)
    (hP : HasBallSupportBound c S) (hFacts : SeparatedTuples.BasicFacts.MainFacts) {X Y : SepTuple}
    (hX : X ∈ supportedIn upperHalfSpace) (hY : Y ∈ supportedIn upperHalfSpace) :
    ∃ b : ℝ, ∀ t : ℝ, 0 ≤ t →
      |centredOf S (SepTuple.juxt (push timeReflection X) (push (translate (t • timeBasisVec)) Y))| ≤ b := by
  have hA := TupleLists.get_mem_disjointSupportTuples X
  have hB := TupleLists.get_mem_disjointSupportTuples Y
  set a := X.1.get with ha
  set b := Y.1.get with hb
  have hKa : ∀ i, IsCompact (tsupport (a i)) := fun i => (hA.1 i).2.1
  have hKb : ∀ i, IsCompact (tsupport (b i)) := fun i => (hB.1 i).2.1
  obtain ⟨δ₁, hδ₁, hf₁⟩ := exists_pos_time_floor _ hKa fun i => hX _ (List.get_mem _ i)
  obtain ⟨δ₂, hδ₂, hf₂⟩ := exists_pos_time_floor _ hKb fun i => hY _ (List.get_mem _ i)
  obtain ⟨d₁, hd₁, hs₁⟩ := exists_pos_separation _ hKa fun l l' h => hA.2 h
  obtain ⟨d₂, hd₂, hs₂⟩ := exists_pos_separation _ hKb fun l l' h => hB.2 h
  obtain ⟨R₁, hR₁, hr₁⟩ := exists_pos_radius _ hKa
  obtain ⟨R₂, hR₂, hr₂⟩ := exists_pos_radius _ hKb
  set d := min (min d₁ d₂) (min δ₁ δ₂) with hd
  have hdpos : 0 < d := lt_min (lt_min hd₁ hd₂) (lt_min hδ₁ hδ₂)
  set R := max R₁ R₂ with hR
  have hRpos : 0 < R := lt_max_of_lt_left hR₁
  set W := ∑ i, sharpNormR4 1 (a i) + ∑ j, sharpNormR4 1 (b j) with hW
  have hWa : ∀ i, sharpNormR4 1 (a i) ≤ W := fun i =>
    (Finset.single_le_sum (f := fun i => sharpNormR4 1 (a i)) (fun _ _ => sharpNormR4_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sharpNormR4_nonneg _))
  have hWb : ∀ i, sharpNormR4 1 (b i) ≤ W := fun i =>
    (Finset.single_le_sum (f := fun i => sharpNormR4 1 (b i)) (fun _ _ => sharpNormR4_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sharpNormR4_nonneg _))
  refine ⟨|blockProductSum c (X.1.length + Y.1.length) d R| * W ^ (X.1.length + Y.1.length), fun t ht => ?_⟩
  set v : AmbientSpace := t • timeBasisVec with hv
  have htv : TimeAxis.timeComponent v = t := by
    simp [hv, timeBasisVec, TimeAxis.timeComponent, PeriodicLattice.coordVec]
  have hsepθ : IsDisjointlySupported (pushList timeReflection X.1) :=
    (hFacts.1 timeReflection (fun x y => euclidNormVec_timeReflection_sub x y) X X).1
  have hsepτ : IsDisjointlySupported (pushList (translate v) Y.1) :=
    (hFacts.1 _ (isEuclidIsometry_translate v) Y Y).1
  have hvX := push_val hsepθ
  have hvY := push_val hsepτ
  rw [invMap_timeReflection] at hvX
  rw [invMap_translate] at hvY
  have hXt : ∀ f ∈ X.1, ∀ x ∈ tsupport (f ∘ timeReflection), TimeAxis.timeComponent x < 0 := fun f hf x hx => by
    have h₁ : timeReflection x ∈ tsupport f := by
      have := (tsupport_comp_eq_preimage f timeReflectionHomeomorph).le hx
      exact this
    have h₂ : 0 < TimeAxis.timeComponent (timeReflection x) := hX f hf h₁
    rw [timeComponent_timeReflection] at h₂
    linarith
  have hYt : ∀ f ∈ Y.1, ∀ x ∈ tsupport (f ∘ translate (-v)), 0 < TimeAxis.timeComponent x := fun f hf x hx => by
    have h₁ : translate (-v) x ∈ tsupport f := by
      have := (tsupport_comp_eq_preimage f (Homeomorph.addRight (-v))).le hx
      exact this
    have h₂ : 0 < TimeAxis.timeComponent (translate (-v) x) := hY f hf h₁
    have e : TimeAxis.timeComponent (translate (-v) x) = TimeAxis.timeComponent x - t := by
      show TimeAxis.timeComponent (x + -v) = _
      rw [← htv]
      simp [TimeAxis.timeComponent, sub_eq_add_neg]
    rw [e] at h₂
    linarith
  have hdef : SepTuple.Composable (push timeReflection X) (push (translate v) Y) := by
    intro f hf h hh
    rw [hvX] at hf
    rw [hvY] at hh
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.1 hf
    obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.1 hh
    exact Set.disjoint_left.2 fun x h₁ h₂ => absurd (hXt f₀ hf₀ x h₁) (not_lt.2 (hYt h₀ hh₀ x h₂).le)
  let g : Fin (X.1.length + Y.1.length) → RealValued :=
    Fin.append (fun i => a i ∘ timeReflection) (fun j => b j ∘ translate (-v))
  have hlist : (SepTuple.juxt (push timeReflection X) (push (translate v) Y)).1 = List.ofFn g := by
    rw [SepTuple.juxt_val hdef, hvX, hvY, map_eq_ofFn_get X.1, map_eq_ofFn_get Y.1, List.ofFn_fin_append]
  have hsep : IsDisjointlySupported (List.ofFn g) :=
    hlist ▸ (SepTuple.juxt (push timeReflection X) (push (translate v) Y)).2
  have hm := mem_disjointSupportTuples_of hsep
  have e : centredOf S (SepTuple.juxt (push timeReflection X) (push (translate v) Y)) =
      TestSpaces.centredOfCumulants S ⟨_, ⟨g, hm⟩⟩ := by
    rw [← centredOf_ofFn hsep hm]
    exact congrArg _ (Subtype.ext hlist)
  rw [e]
  have hL : ∀ i, g (Fin.castAdd Y.1.length i) = a i ∘ timeReflection := fun i => Fin.append_left _ _ i
  have hRt : ∀ j, g (Fin.natAdd X.1.length j) = b j ∘ translate (-v) := fun j => Fin.append_right _ _ j
  have sL : ∀ i x, x ∈ tsupport (a i ∘ timeReflection) → timeReflection x ∈ tsupport (a i) := fun i x hx =>
    (tsupport_comp_eq_preimage (a i) timeReflectionHomeomorph).le hx
  have sR : ∀ j x, x ∈ tsupport (b j ∘ translate (-v)) → x + -v ∈ tsupport (b j) := fun j x hx =>
    (tsupport_comp_eq_preimage (b j) (Homeomorph.addRight (-v))).le hx
  have hball : ∀ i, ∃ x, tsupport ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 i) ⊆ closedBallR4 x R := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · refine ⟨0, fun x hx => ?_⟩
      have hx' : x ∈ tsupport (a i ∘ timeReflection) := by
        have := hx
        simpa only [hL] using this
      have h₁ := hr₁ i _ (sL i x hx')
      have h₂ := euclidNormVec_timeReflection_sub x 0
      have h₃ : timeReflection (0 : AmbientSpace) = 0 := by
        funext μ
        fin_cases μ <;> simp [timeReflection]
      rw [h₃] at h₂
      simp only [sub_zero] at h₂
      show euclidNormVec (x - 0) ≤ R
      rw [sub_zero, ← h₂]
      exact h₁.trans (le_max_left _ _)
    · refine ⟨v, fun x hx => ?_⟩
      have hx' : x ∈ tsupport (b j ∘ translate (-v)) := by
        have := hx
        simpa only [hRt] using this
      have h₁ := hr₂ j _ (sR j x hx')
      show euclidNormVec (x - v) ≤ R
      rw [sub_eq_add_neg]
      exact h₁.trans (le_max_right _ _)
  have hdist : ∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4
      (tsupport ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 i)) (tsupport ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 l)) := by
    have hLL : ∀ i l, i ≠ l → ∀ x ∈ tsupport (a i ∘ timeReflection), ∀ y ∈ tsupport (a l ∘ timeReflection),
        d ≤ euclidNormVec (x - y) := fun i l hil x hx y hy => by
      have h₁ := hs₁ i l hil _ (sL i x hx) _ (sL l y hy)
      rw [euclidNormVec_timeReflection_sub] at h₁
      exact (min_le_left _ _).trans ((min_le_left _ _).trans h₁)
    have hRR : ∀ i l, i ≠ l → ∀ x ∈ tsupport (b i ∘ translate (-v)), ∀ y ∈ tsupport (b l ∘ translate (-v)),
        d ≤ euclidNormVec (x - y) := fun i l hil x hx y hy => by
      have h₁ := hs₂ i l hil _ (sR i x hx) _ (sR l y hy)
      have e₁ : x + -v - (y + -v) = x - y := by abel
      rw [e₁] at h₁
      exact (min_le_left _ _).trans ((min_le_right _ _).trans h₁)
    have hLR : ∀ i j, ∀ x ∈ tsupport (a i ∘ timeReflection), ∀ y ∈ tsupport (b j ∘ translate (-v)),
        d ≤ euclidNormVec (x - y) := fun i j x hx y hy => by
      have h₁ := hf₁ i _ (sL i x hx)
      have h₂ := hf₂ j _ (sR j y hy)
      rw [timeComponent_timeReflection] at h₁
      have e₁ : TimeAxis.timeComponent (y + -v) = TimeAxis.timeComponent y - t := by
        rw [← htv]
        simp [TimeAxis.timeComponent, sub_eq_add_neg]
      rw [e₁] at h₂
      have h₃ := abs_apply_le_euclidNormVec (x - y) TimeAxis.timeIdx
      have h₄ : (x - y) TimeAxis.timeIdx = TimeAxis.timeComponent x - TimeAxis.timeComponent y := rfl
      rw [h₄] at h₃
      have h₅ := neg_abs_le (TimeAxis.timeComponent x - TimeAxis.timeComponent y)
      have h₆ : d ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hsym : ∀ x y : AmbientSpace, euclidNormVec (x - y) = euclidNormVec (y - x) := fun x y => by
      unfold euclidNormVec
      congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp only [Pi.sub_apply]
      ring
    intro i l hil
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    revert hil hx hy
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> refine Fin.addCases (fun l => ?_) (fun k => ?_) l
    · intro hil hx hy
      simp only [hL] at hx hy
      exact hLL i l (fun e => hil (by rw [e])) x hx y hy
    · intro _ hx hy
      simp only [hL, hRt] at hx hy
      exact hLR i k x hx y hy
    · intro _ hx hy
      simp only [hL, hRt] at hx hy
      rw [hsym]
      exact hLR l j y hy x hx
    · intro hil hx hy
      simp only [hRt] at hx hy
      exact hRR j k (fun e => hil (by rw [e])) x hx y hy
  refine (abs_centredOfCumulants_le hc hP (⟨g, hm⟩ : TestSpaces.SepTupleOfCard _) hRpos hdpos hball hdist).trans ?_
  have hprod : ∏ i, sharpNormR4 1 ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 i) ≤ W ^ (X.1.length + Y.1.length) := by
    have h₁ : ∀ i, sharpNormR4 1 ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 i) ≤ W := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · show sharpNormR4 1 (g _) ≤ W
        rw [hL]
        exact (sharpNormR4_comp (a i) ⟨timeReflection, timeReflection, involutive_timeReflection, involutive_timeReflection⟩
          euclidNormVec_timeReflection_sub).le.trans (hWa i)
      · show sharpNormR4 1 (g _) ≤ W
        rw [hRt]
        refine (sharpNormR4_comp (b j) (Equiv.addRight (-v)) fun x y => ?_).le.trans (hWb j)
        show euclidNormVec (x + -v - (y + -v)) = _
        congr 1
        abel
    calc _ ≤ ∏ _i : Fin (X.1.length + Y.1.length), W :=
          Finset.prod_le_prod (fun i _ => sharpNormR4_nonneg _) fun i _ => h₁ i
      _ = _ := by simp
  calc _ ≤ |blockProductSum c (X.1.length + Y.1.length) d R| * ∏ i, sharpNormR4 1 ((⟨g, hm⟩ : TestSpaces.SepTupleOfCard _).1 i) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.prod_nonneg fun i _ => sharpNormR4_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
private theorem exists_bound_reflectionForm (hc : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R)
    (hP : HasBallSupportBound c S) (hFacts : SeparatedTuples.BasicFacts.MainFacts) (G G' : PositiveSpan) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖reflectionForm (centredOf S) G (shiftedSpan (t • timeBasisVec) G')‖ ≤ B := by
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  have hq := isSesquilinear_reflectionForm (centredOf S)
  have htime : ∀ t : ℝ, 0 ≤ t → 0 ≤ TimeAxis.timeComponent (t • timeBasisVec) := fun t ht => by
    rw [timeComponent_smul_timeBasisVec]
    exact ht
  have hadd : ∀ (t : ℝ) (ht : 0 ≤ t) (A B : PositiveSpan),
      shiftedSpan (t • timeBasisVec) (A + B) = shiftedSpan (t • timeBasisVec) A + shiftedSpan (t • timeBasisVec) B :=
    fun t ht A B => by
    rw [← shiftMap_apply hAct (htime t ht), map_add,
      shiftMap_apply hAct (htime t ht),
      shiftMap_apply hAct (htime t ht)]
  have hsmul : ∀ (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (A : PositiveSpan),
      shiftedSpan (t • timeBasisVec) (z • A) = z • shiftedSpan (t • timeBasisVec) A := fun t ht z A => by
    rw [← shiftMap_apply hAct (htime t ht), map_smul,
      shiftMap_apply hAct (htime t ht)]
  have h₁ : ∀ (X : supportedIn upperHalfSpace) (G' : PositiveSpan), ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖reflectionForm (centredOf S) (posTupleVec X) (shiftedSpan (t • timeBasisVec) G')‖ ≤ B := by
    rintro X ⟨G', hG'⟩
    refine Submodule.span_induction (p := fun x hx => ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖reflectionForm (centredOf S) (posTupleVec X) (shiftedSpan (t • timeBasisVec) ⟨x, hx⟩)‖ ≤ B) ?_ ?_ ?_ ?_ hG'
    · rintro _ ⟨Y, rfl⟩
      obtain ⟨b, hb⟩ := exists_bound_juxt hc hP hFacts X.2 Y.2
      refine ⟨b, fun t ht => ?_⟩
      have e : reflectionForm (centredOf S) (posTupleVec X) (shiftedSpan (t • timeBasisVec) (posTupleVec Y)) =
          (centredOf S (SepTuple.juxt (push timeReflection X.1) (push (translate (t • timeBasisVec)) Y.1)) : ℂ) := by
        unfold reflectionForm
        rw [shiftedSpan_val hAct (htime t ht)]
        simp only [reflectConj, posTupleVec, conjugation_basisVec, pushSpan, linearExtend_basisVec,
          formalMul_basisVec, TupleFunctional.spanExtension]
      have e' := congrArg norm e
      refine le_trans (le_of_eq ?_) (hb t ht)
      rw [Complex.norm_real, Real.norm_eq_abs] at e'
      exact e'
    · refine ⟨0, fun t ht => ?_⟩
      have e : shiftedSpan (t • timeBasisVec) (⟨0, Submodule.zero_mem _⟩ : PositiveSpan) = 0 := by
        rw [← shiftMap_apply hAct (htime t ht)]
        exact map_zero _
      have e₂ := hq.smul_right 0 (posTupleVec X) 0
      rw [zero_smul, zero_mul] at e₂
      rw [e, e₂, norm_zero]
    · rintro x y hx hy ⟨B₁, h₁⟩ ⟨B₂, h₂⟩
      refine ⟨B₁ + B₂, fun t ht => ?_⟩
      have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : PositiveSpan) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, hadd t ht, hq.add_right]
      exact (norm_add_le _ _).trans (add_le_add (h₁ t ht) (h₂ t ht))
    · rintro z x hx ⟨B, h⟩
      refine ⟨‖z‖ * B, fun t ht => ?_⟩
      have e : (⟨z • x, Submodule.smul_mem _ z hx⟩ : PositiveSpan) = z • ⟨x, hx⟩ := rfl
      rw [e, hsmul t ht, hq.smul_right, norm_mul]
      exact mul_le_mul_of_nonneg_left (h t ht) (norm_nonneg _)
  rcases G with ⟨G, hG⟩
  refine Submodule.span_induction (p := fun x hx => ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
    ‖reflectionForm (centredOf S) ⟨x, hx⟩ (shiftedSpan (t • timeBasisVec) G')‖ ≤ B) ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨X, rfl⟩
    exact h₁ X G'
  · refine ⟨0, fun t _ => ?_⟩
    have e₂ := hq.smul_left 0 (⟨0, Submodule.zero_mem _⟩ : PositiveSpan) (shiftedSpan (t • timeBasisVec) G')
    rw [zero_smul, map_zero, zero_mul] at e₂
    have e₃ : ‖reflectionForm (centredOf S) 0 (shiftedSpan (t • timeBasisVec) G')‖ = 0 := by rw [e₂, norm_zero]
    exact e₃.le
  · rintro x y hx hy ⟨B₁, h₁⟩ ⟨B₂, h₂⟩
    refine ⟨B₁ + B₂, fun t ht => ?_⟩
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : PositiveSpan) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, hq.add_left]
    exact (norm_add_le _ _).trans (add_le_add (h₁ t ht) (h₂ t ht))
  · rintro z x hx ⟨B, h⟩
    refine ⟨‖z‖ * B, fun t ht => ?_⟩
    have e : (⟨z • x, Submodule.smul_mem _ z hx⟩ : PositiveSpan) = z • ⟨x, hx⟩ := rfl
    rw [e, hq.smul_left, norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (h t ht) (norm_nonneg _)
private theorem le_of_sq_le_mul_succ {A B : ℝ} {b : ℕ → ℝ} (hA : 0 ≤ A) (hB : ∀ k, b k ≤ B)
    (hsq : ∀ k, b k ^ 2 ≤ A * b (k + 1)) (hb₀ : 0 ≤ b 0) : b 0 ≤ A := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : 0 < b 0 := hA.trans_lt hlt
  rcases hA.eq_or_lt with h0 | hApos
  · have h := hsq 0
    rw [← h0, zero_mul] at h
    nlinarith [pow_pos hb 2]
  · set r := b 0 / A with hr
    have hr₁ : 1 < r := (one_lt_div hApos).2 hlt
    have key : ∀ k, A * r ^ (2 ^ k) ≤ b k := by
      intro k
      induction k with
      | zero =>
        have e : A * r ^ (2 ^ 0) = b 0 := by
          rw [pow_zero, pow_one, hr]
          field_simp
        exact e.le
      | succ k ih =>
        have h₁ := hsq k
        have h₂ : (A * r ^ (2 ^ k)) ^ 2 ≤ b k ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
        have h₃ : A * (A * r ^ (2 ^ (k + 1))) ≤ A * b (k + 1) := by
          have e : A * (A * r ^ (2 ^ (k + 1))) = (A * r ^ (2 ^ k)) ^ 2 := by
            rw [pow_succ 2 k, pow_mul]
            ring
          rw [e]
          exact h₂.trans h₁
        exact le_of_mul_le_mul_left h₃ hApos
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr₁).eventually_gt_atTop (B / A)).exists
    have h₃ : r ^ k ≤ r ^ (2 ^ k) := pow_le_pow_right₀ hr₁.le Nat.lt_two_pow_self.le
    have h₄ : r ^ (2 ^ k) ≤ B / A := by
      rw [le_div_iff₀ hApos]
      have := (key k).trans (hB k)
      linarith
    linarith
private theorem reflectedCorrelation_le (hprop : ReflectionPositivity.FormProperties.Assertion)
    (hAct : BasicFacts.PushSpanProperties)
    {σ : TupleFunctional} (hT : σ.IsTranslateInvariant) (hRP : σ.IsReflectionPositive temporalHyperplane)
    (hB : ∀ F : PositiveSpan, ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖reflectionForm σ F (shiftedSpan (t • timeBasisVec) F)‖ ≤ B)
    (F : PositiveSpan) {t : ℝ} (ht : 0 < t) :
    reflectedCorrelation σ F ((2 * t) • timeBasisVec) ≤ reflectionForm σ F F := by
  have h := ((hprop σ F F).1 hRP).1
  have hin : ∀ G H, inner ℂ (posClass σ h G) (posClass σ h H) = reflectionForm σ G H :=
    inner_posClass σ h
  have hdouble : ∀ s : ℝ, 0 ≤ s → reflectedCorrelation σ F ((2 * s) • timeBasisVec) =
      reflectionForm σ (shiftedSpan (s • timeBasisVec) F) (shiftedSpan (s • timeBasisVec) F) :=
    fun s hs => (((hprop σ F F).2.2.1 hT).1 s hs).2
  have hcorr : ∀ s : ℝ, 0 ≤ s → reflectedCorrelation σ F ((2 * s) • timeBasisVec) =
      reflectionForm σ F (shiftedSpan ((2 * s) • timeBasisVec) F) := fun s hs =>
    reflectedCorrelation_eq hAct (by
      rw [timeComponent_smul_timeBasisVec]
      linarith) σ F
  have hsq : ∀ G, reflectionForm σ G G = ((‖posClass σ h G‖ ^ 2 : ℝ) : ℂ) := fun G => by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  obtain ⟨B, hBb⟩ := hB F
  let b : ℕ → ℝ := fun k => ‖posClass σ h (shiftedSpan ((2 ^ k * t) • timeBasisVec) F)‖ ^ 2
  have hbv : ∀ k, (b k : ℂ) = reflectionForm σ F (shiftedSpan ((2 * (2 ^ k * t)) • timeBasisVec) F) := fun k => by
    have hs : (0 : ℝ) ≤ 2 ^ k * t := by positivity
    rw [← hcorr _ hs, hdouble _ hs, hsq]
  have hnorm : ∀ k, b k = ‖reflectionForm σ F (shiftedSpan ((2 * (2 ^ k * t)) • timeBasisVec) F)‖ := fun k => by
    rw [← hbv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle := le_of_sq_le_mul_succ (A := ‖posClass σ h F‖ ^ 2) (B := B) (b := b) (by positivity)
    (fun k => by
      rw [hnorm]
      exact hBb _ (by positivity))
    (fun k => by
      have h₁ : b k ≤ ‖posClass σ h F‖ * ‖posClass σ h (shiftedSpan ((2 * (2 ^ k * t)) • timeBasisVec) F)‖ := by
        rw [hnorm, ← hin]
        exact norm_inner_le_norm _ _
      have h₂ : (2 : ℝ) * (2 ^ k * t) = 2 ^ (k + 1) * t := by ring
      rw [h₂] at h₁
      have h₃ : 0 ≤ b k := by positivity
      calc b k ^ 2 ≤ (‖posClass σ h F‖ * ‖posClass σ h (shiftedSpan ((2 ^ (k + 1) * t) • timeBasisVec) F)‖) ^ 2 :=
            pow_le_pow_left₀ h₃ h₁ 2
        _ = _ := by
          show _ = ‖posClass σ h F‖ ^ 2 * ‖posClass σ h (shiftedSpan ((2 ^ (k + 1) * t) • timeBasisVec) F)‖ ^ 2
          ring)
    (by positivity)
  have e₀ : b 0 = ‖posClass σ h (shiftedSpan (t • timeBasisVec) F)‖ ^ 2 := by
    show ‖posClass σ h (shiftedSpan (((2 : ℝ) ^ 0 * t) • timeBasisVec) F)‖ ^ 2 = _
    simp
  rw [hdouble t ht.le, hsq, hsq]
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · simp only [Complex.ofReal_re]
    rw [← e₀]
    exact hle
  · rw [Complex.ofReal_im, Complex.ofReal_im]
end Contraction
section TheProof
open YangMills.Construction.LimitTheorem YangMills.Construction.ReflectionPositivity.TupleForm
open YangMills.Construction.SpectralTheory MeasureTheory
open YangMills.Construction.ReflectionPositivity.Reconstruction (temporalHyperplane timeBasisVec)
open YangMills.Construction.ReflectionPositivity.ContractionFunctionals (IsAdmissible)
private theorem exists_rigidMotion_of_hyperoctahedral (w : TorusTransport.hyperoctahedral) :
    ∃ r : Motions.RigidMotion, IsHyperoctahedralMotion r ∧ r.toFun = w.1 := by apply _root_.YangMills.SharedProofs.p35926 <;> assumption
theorem boundedFamilyReconstruction_holds (hCen : AmbientPoints.CentredOfConnectedFamilyProperties)
    (hTwo : SeparatedClasses.ClassFacts)
    (hbd : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hprop : ReflectionPositivity.FormProperties.Assertion)
    (hFacts : SeparatedTuples.BasicFacts.MainFacts)
    (hIdent : LimitTheorem.CutoffRepresentatives.IdentificationsHold)
    (hList : ContractionFunctionalReconstructs) : reconstructionOfBoundedFamily := by
  intro c S hc hcl hP
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  have hL : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
  let s : Conventions.StandingParameters := ⟨13, hL, 1, 1⟩
  have hm := centredOf_isEntrywiseLinear hCen hTwo hcl s
  have hcont := centredOf_isAdmissiblyContinuous hbd hc hP hm
  have ha : 0 < InfiniteLattice.refinedSpacing 13 ((1 : ℕ+) : ℕ) := by
    simp only [InfiniteLattice.refinedSpacing, PeriodicLattice.meshSize]
    positivity
  let U₀ : CutoffLattice.FieldsAt 13 ((1 : ℕ+) : ℕ) :=
    CutoffLattice.fieldOfValues ha fun _ => 1
  have hS := (hIdent 13 hL (fun _ => 1) (fun _ => Measure.dirac U₀) (fun _ => inferInstance) S).2.2
  have hinvM : ∀ r, IsHyperoctahedralMotion r → IsMotionInvariant (centredOf S) r :=
    fun r hr => (hS.2.1 r).2 (hcl.invariant r hr)
  have hsym : (centredOf S).IsPermInvariant := hS.1.2 hcl.symmetric
  have hT : (centredOf S).IsTranslateInvariant := fun v => by
    have h := hinvM (shiftMotion v) ⟨1, fun x => by simp [shiftMotion]⟩
    have e : (shiftMotion v).toFun = SeparatedTuples.translate v := by
      funext x
      simp [Motions.RigidMotion.toFun, shiftMotion, SeparatedTuples.translate]
    unfold IsMotionInvariant at h
    rwa [e] at h
  have hRP : (centredOf S).IsReflectionPositive temporalHyperplane :=
    hcl.reflectionPositive temporalHyperplane ⟨TimeAxis.timeIdx, rfl⟩
  have hθ : (centredOf S).IsInvariant TimeAxis.timeReflection := by
    let w : TorusTransport.hyperoctahedral :=
      ⟨TorusLifts.signedCoordinateEquiv 1 ![1, 1, 1, -1], 1, ![1, 1, 1, -1], rfl⟩
    obtain ⟨r, hr, e⟩ := exists_rigidMotion_of_hyperoctahedral w
    have h := hinvM r hr
    unfold IsMotionInvariant at h
    have e₂ : r.toFun = TimeAxis.timeReflection := by
      rw [e]
      funext x μ
      refine (TorusTransport.signedCoordinateEquiv_apply 1 ![1, 1, 1, -1] x μ).trans ?_
      fin_cases μ <;> simp [TimeAxis.timeReflection]
    rwa [e₂] at h
  have hB := fun F => exists_bound_reflectionForm hc hP hFacts F F
  have hcontr := fun (F : PositiveSpan) (t : ℝ) (ht : 0 < t) => reflectedCorrelation_le hprop hAct hT hRP hB F ht
  have hcn : ReflectionPositivity.Reconstruction.ContractionHypotheses (centredOf S) (Set.Ioi 0) :=
    { continuous := hcont
      translateInvariant := hT
      reflectionPositive := hRP
      subset_pos := subset_rfl
      dense := subset_closure
      contraction := fun F t ht => hcontr F t ht }
  have hH : IsAdmissible (centredOf S) :=
    { contraction := ⟨_, hcn⟩
      permInvariant := hsym
      timeReflect_invariant := hθ }
  exact ⟨hm, hcont, hList _ hcont hH hinvM⟩
end TheProof
end YangMills.Construction.TotalDensities.BoundedFamilyReconstruction
end
