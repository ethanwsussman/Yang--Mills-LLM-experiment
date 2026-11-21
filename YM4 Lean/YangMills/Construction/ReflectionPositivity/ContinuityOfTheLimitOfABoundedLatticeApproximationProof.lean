import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpaceProof
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.ContinuityOfTheLimitOfABoundedLatticeApproximation
import YangMills.Construction.ReflectionPositivity.MovingTestFunctions
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellDataProof
import Mathlib
set_option autoImplicit false
open Filter Function Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContinuity
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open YangMills.Construction.LatticeConventions (euclidNorm)
open YangMills.Construction.TestFunctions (c1NormR4 partialDerivR4 sharpNormR4 uniformNorm)
open YangMills.Construction.SeparatedTuples
private theorem uniformNorm_nonneg (g : RealValued) : 0 ≤ uniformNorm g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.uniformNorm_nonneg <;> assumption
private theorem c1NormR4_nonneg (g : RealValued) : 0 ≤ c1NormR4 g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
private theorem norm_le_c1NormR4 {g : RealValued} (hg : IsC1c g) (x : AmbientSpace) :
    ‖g x‖ ≤ c1NormR4 g := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  exact (le_ciSup (f := fun x => ‖g x‖) ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩ x).trans
    (le_max_left _ _)
private theorem hasDerivAt_along_axis {g : RealValued} (hg : TestFunctions.IsC1R4 g) (μ : Fin 4)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => g (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)))
      (fderiv ℝ g x (Pi.single μ 1)) 0 := by apply _root_.YangMills.Construction.SeparatedTuples.BasicFacts.hasDerivAt_coordLine_of_contDiff <;> assumption
abbrev _root_.YangMills.SharedProofs.p48546 := @hasDerivAt_along_axis
private theorem partialDerivR4_eq {g : RealValued} (hg : TestFunctions.IsC1R4 g) (μ : Fin 4)
    (x : AmbientSpace) : partialDerivR4 μ g x = fderiv ℝ g x (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.partialDerivR4_eq_fderiv <;> assumption
private theorem norm_partialDerivR4_le {g : RealValued} (hg : IsC1c g)
    (μ : Fin 4) (x : AmbientSpace) : ‖partialDerivR4 μ g x‖ ≤ c1NormR4 g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.norm_partialDerivR4_le_c1NormR4 <;> assumption
private theorem c1NormR4_add_le {a b : RealValued} (ha : IsC1c a)
    (hb : IsC1c b) : c1NormR4 (a + b) ≤ c1NormR4 a + c1NormR4 b := by
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun μ => ciSup_le fun x => ?_)
  · exact (norm_add_le _ _).trans (add_le_add (norm_le_c1NormR4 ha x) (norm_le_c1NormR4 hb x))
  · have h : partialDerivR4 μ (a + b) x = partialDerivR4 μ a x + partialDerivR4 μ b x := by
      rw [partialDerivR4_eq ha.1, partialDerivR4_eq hb.1]
      exact ((hasDerivAt_along_axis ha.1 μ x).add (hasDerivAt_along_axis hb.1 μ x)).deriv
    rw [h]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_partialDerivR4_le ha μ x) (norm_partialDerivR4_le hb μ x))
private theorem c1NormR4_zero : c1NormR4 (0 : RealValued) = 0 := by
  refine le_antisymm (max_le (ciSup_le fun x => ?_) (ciSup_le fun μ => ciSup_le fun x => ?_))
    (c1NormR4_nonneg _)
  · simp
  · simp [partialDerivR4]
abbrev _root_.YangMills.SharedProofs.p22097 := @c1NormR4_zero
private theorem c1NormR4_pos {g : RealValued} (hg : IsC1c g) (h0 : g ≠ 0) :
    0 < c1NormR4 g := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  exact (norm_pos_iff.2 hx).trans_le (norm_le_c1NormR4 hg x)
private theorem isC1c_sub {a b : RealValued} (ha : IsC1c a)
    (hb : IsC1c b) : IsC1c (a - b) :=
  ⟨ContDiff.sub ha.1 hb.1, by simpa [sub_eq_add_neg] using ha.2.add hb.2.neg⟩
private theorem tsupport_sub_subset_of {a b : RealValued} {S : Set AmbientSpace} (hS : IsClosed S)
    (ha : tsupport a ⊆ S) (hb : tsupport b ⊆ S) : tsupport (a - b) ⊆ S := by
  refine closure_minimal (fun x hx => ?_) hS
  by_contra h
  have ha0 : a x = 0 := image_eq_zero_of_notMem_tsupport fun h' => h (ha h')
  have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport fun h' => h (hb h')
  exact hx (by simp [ha0, hb0])
abbrev _root_.YangMills.SharedProofs.p73657 := @tsupport_sub_subset_of
private theorem isDisjointlySupported_ofFn {k : ℕ} {g : Fin k → RealValued} {A : Fin k → Set AmbientSpace}
    (hA : Pairwise (Function.onFun Disjoint A)) (hg : ∀ l, IsC1c (g l))
    (hs : ∀ l, tsupport (g l) ⊆ A l) : IsDisjointlySupported (List.ofFn g) := by
  refine ⟨fun f hf => ?_, List.pairwise_ofFn.2 fun i j hij => (hA hij.ne).mono (hs i) (hs j)⟩
  obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
  exact hg l
private theorem ofFn_update_eq {k : ℕ} (g : Fin k → RealValued) (m : Fin k) (a : RealValued) :
    List.ofFn (Function.update g m a) =
      (List.ofFn g).take m ++ a :: (List.ofFn g).drop (m + 1) := by
  have h : List.ofFn (Function.update g m a) = (List.ofFn g).set m a := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
      by_cases hi : i = m <;> simp [hi, eq_comm]
  rw [h, List.set_eq_take_append_cons_drop]
  simp
abbrev _root_.YangMills.SharedProofs.p53786 := @ofFn_update_eq
private theorem componentAt_eq (Y : SepTuple) {i : ℕ} (hi : i < Y.1.length) : Y.componentAt i = Y.1[i] :=
  List.getD_eq_getElem _ _ hi
private theorem componentAt_isC1c (Y : SepTuple) {i : ℕ} (hi : i < Y.1.length) :
    IsC1c (Y.componentAt i) := by
  rw [componentAt_eq Y hi]
  exact Y.2.1 _ (List.getElem_mem hi)
private theorem ofFn_componentAt (Y : SepTuple) {k : ℕ} (h : Y.size = k) :
    List.ofFn (fun i : Fin k => Y.componentAt i) = Y.1 := by
  subst h
  apply List.ext_getElem
  · simp [SepTuple.size]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    exact componentAt_eq Y h2
private def BoundedByProducts (σ : SepTuple → ℝ) (C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set AmbientSpace, (∀ l, IsCompact (A l)) →
    Pairwise (Function.onFun Disjoint A) →
    ∀ (g : Fin k → RealValued) (hg : IsDisjointlySupported (List.ofFn g)), (∀ l, tsupport (g l) ⊆ A l) →
      |σ ⟨List.ofFn g, hg⟩| ≤ C k A * ∏ l, c1NormR4 (g l)
private theorem boundedByProducts_of_convergesTo {L : ℕ} {T : LimitConventions.ApproxTriple L}
    {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ} {σ : SepTuple → ℝ}
    (hC : LatticeApproximation.IsC1ConstantFamily T C) (hlim : LimitConventions.ApproxTriple.ConvergesTo T σ) :
    BoundedByProducts σ C := by
  intro k hk A hAc hAd g hg hs
  exact le_of_tendsto (hlim ⟨List.ofFn g, hg⟩).abs
    (Eventually.of_forall fun j => hC k hk A hAc hAd j g hg hs)
private theorem exists_vanishing_slot_of_neg {σ : SepTuple → ℝ} {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ}
    (hB : BoundedByProducts σ C) {k : ℕ} (hk : 1 ≤ k) {A : Fin k → Set AmbientSpace}
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
  have hsep := isDisjointlySupported_ofFn hAd hgC hgs
  have hpos : 0 < ∏ l, c1NormR4 (g l) :=
    Finset.prod_pos fun l _ => c1NormR4_pos (hgC l) (hg0 l)
  have hb := hB k hk A hAc hAd g hsep hgs
  have hneg := mul_neg_of_neg_of_pos hC hpos
  exact absurd (abs_nonneg _) (not_le.2 (hb.trans_lt hneg))
private theorem satisfiesDifferenceBound_of (F : TupleFunctional) (hm : F.IsEntrywiseLinear)
    {C : ∀ k : ℕ, (Fin k → Set AmbientSpace) → ℝ} (hB : BoundedByProducts F C)
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
  · obtain ⟨l₀, h0, h0'⟩ := exists_vanishing_slot_of_neg hB hk hAc hAd hC hfC hf'C hsf hsf'
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
      isDisjointlySupported_ofFn hAd (hybC m) (hybS m)
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
      isDisjointlySupported_ofFn hAd (midC m) (midS m)
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
    F.IsAdmissiblyContinuous := by
  rintro r₀ s X ⟨-, hlen, A, hAc, hAd, hsup, hconv⟩
  rcases Nat.eq_zero_or_pos X.size with h0 | hk
  · have hX : X.1 = [] := List.length_eq_zero_iff.1 h0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hs : (s r).1 = [] := List.length_eq_zero_iff.1 ((hlen r hr).trans h0)
    exact congrArg F (Subtype.ext (hX.trans hs.symm))
  · have key : ∀ r, r₀ ≤ r → |F (s r) - F X| ≤ C X.size A *
        ∑ l : Fin X.size, c1NormR4 ((s r).componentAt l - X.componentAt l) *
          ∏ l' ∈ Finset.univ.erase l,
            max (c1NormR4 ((s r).componentAt l')) (c1NormR4 (X.componentAt l')) := by
      intro r hr
      have e1 := ofFn_componentAt (s r) (hlen r hr)
      have e2 := ofFn_componentAt X (k := X.size) rfl
      have h1 : IsDisjointlySupported (List.ofFn fun l : Fin X.size => (s r).componentAt l) := by
        rw [e1]
        exact (s r).2
      have h2 : IsDisjointlySupported (List.ofFn fun l : Fin X.size => X.componentAt l) := by
        rw [e2]
        exact X.2
      have h := hd X.size hk A hAc hAd (fun l => (s r).componentAt l) (fun l => X.componentAt l) h1 h2
        (hsup r hr)
      have t1 : (⟨_, h1⟩ : SepTuple) = s r := Subtype.ext e1
      have t2 : (⟨_, h2⟩ : SepTuple) = X := Subtype.ext e2
      rwa [t1, t2] at h
    have hsC : ∀ r, r₀ ≤ r → ∀ l : Fin X.size, IsC1c ((s r).componentAt l) :=
      fun r hr l => componentAt_isC1c (s r) (by
        have := hlen r hr
        unfold SepTuple.size at this
        rw [this]
        exact l.2)
    have hXC : ∀ l : Fin X.size, IsC1c (X.componentAt l) := fun l =>
      componentAt_isC1c X l.2
    set b : Fin X.size → ℝ := fun l => c1NormR4 (X.componentAt l) + 1 with hb
    have hsmall : ∀ᶠ r in atTop, ∀ l : Fin X.size,
        c1NormR4 ((s r).componentAt l - X.componentAt l) < 1 :=
      eventually_all.2 fun l => (hconv l).eventually (Iio_mem_nhds zero_lt_one)
    have hto : Tendsto (fun r => |C X.size A| *
        ∑ l : Fin X.size, c1NormR4 ((s r).componentAt l - X.componentAt l) *
          ∏ l' ∈ Finset.univ.erase l, b l') atTop (𝓝 0) := by
      have h := (tendsto_finsetSum Finset.univ fun l _ =>
        (hconv l).mul_const (∏ l' ∈ Finset.univ.erase l, b l')).const_mul |C X.size A|
      simpa using h
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hto
    filter_upwards [eventually_ge_atTop r₀, hsmall] with r hr hr1
    have hmax : ∀ l : Fin X.size,
        max (c1NormR4 ((s r).componentAt l)) (c1NormR4 (X.componentAt l)) ≤ b l := fun l => by
      refine max_le ?_ (by simp [hb])
      have hadd := c1NormR4_add_le (isC1c_sub (hsC r hr l) (hXC l)) (hXC l)
      rw [sub_add_cancel] at hadd
      have := hr1 l
      simp only [hb]
      linarith
    have hS0 : 0 ≤ ∑ l : Fin X.size, c1NormR4 ((s r).componentAt l - X.componentAt l) *
        ∏ l' ∈ Finset.univ.erase l,
          max (c1NormR4 ((s r).componentAt l')) (c1NormR4 (X.componentAt l')) :=
      Finset.sum_nonneg fun l _ => mul_nonneg (c1NormR4_nonneg _)
        (Finset.prod_nonneg fun _ _ => le_max_of_le_left (c1NormR4_nonneg _))
    rw [Real.dist_eq]
    calc |F (s r) - F X| ≤ _ := key r hr
      _ ≤ |C X.size A| * _ := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod
            (fun _ _ => le_max_of_le_left (c1NormR4_nonneg _)) fun l' _ => hmax l')
            (c1NormR4_nonneg _)) (abs_nonneg _)
abbrev _root_.YangMills.SharedProofs.p63308 := @isAdmissiblyContinuous_of_bound
private theorem norm_le_euclidNorm (u : AmbientSpace) : ‖u‖ ≤ euclidNorm u := by
  rw [LatticeConventions.euclidNorm_eq_norm]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ =>
    PiLp.norm_apply_le (WithLp.toLp 2 u) μ
private theorem composable_near (hm : MovingTests.TranslatesTendsto) (X Y : SepTuple)
    (v : AmbientSpace) (h : SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v' : AmbientSpace, euclidNorm (v' - v) ≤ δ →
      SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X) ∧
        SepTuple.Composable (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X) Y := by
  by_contra hno
  have hseq : ∀ r : ℕ, ∃ w : AmbientSpace, euclidNorm (w - v) ≤ 1 / ((r : ℝ) + 1) ∧
      ¬ (SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate w) X) ∧
        SepTuple.Composable (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate w) X) Y) := fun r => by
    by_contra hr
    push Not at hr
    exact hno ⟨1 / ((r : ℝ) + 1), by positivity, hr⟩
  choose w hw hn using hseq
  have hlim : Tendsto w atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun r => (norm_le_euclidNorm _).trans (hw r)) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨r₀, _, h1, _, h2, _⟩ := (hm 1 le_rfl X w v hlim).2 Y h
  exact hn r₀ ⟨h1 r₀ le_rfl, h2 r₀ le_rfl⟩
private theorem tendsto_juxt_left (hm : MovingTests.TranslatesTendsto) (F : TupleFunctional)
    (hF : F.IsAdmissiblyContinuous) (X Y : SepTuple) (v : AmbientSpace)
    (h : SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)) :
    Tendsto (fun v' : AmbientSpace => F (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X))) (𝓝 v)
      (𝓝 (F (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)))) := by
  refine tendsto_of_seq_tendsto fun w hw => ?_
  obtain ⟨r₀, _, _, h1, _, _⟩ := (hm 1 le_rfl X w v hw).2 Y h
  exact hF r₀ _ _ h1
private theorem tendsto_juxt_right (hm : MovingTests.TranslatesTendsto) (F : TupleFunctional)
    (hF : F.IsAdmissiblyContinuous) (X Y : SepTuple) (v : AmbientSpace)
    (h : SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)) :
    Tendsto (fun v' : AmbientSpace => F (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X) Y)) (𝓝 v)
      (𝓝 (F (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X) Y))) := by
  refine tendsto_of_seq_tendsto fun w hw => ?_
  obtain ⟨r₀, _, _, _, _, h2⟩ := (hm 1 le_rfl X w v hw).2 Y h
  exact hF r₀ _ _ h2
private theorem span_expansion (W : FormalSpan) : W = ∑ Y ∈ W.support, W Y • basisVec Y := by apply _root_.YangMills.Construction.ReflectionsAndOneInsertion.formalSpan_eq_sum <;> assumption
private theorem pushSpan_eq (r : AmbientSpace → AmbientSpace) (Z : FormalSpan) :
    pushSpan r Z = ∑ X ∈ Z.support, Z X • basisVec (_root_.YangMills.Construction.SeparatedTuples.push r X) := by
  simp [pushSpan, SeparatedTuples.linearExtend, Finsupp.linearCombination_apply, Finsupp.sum]
private theorem spanExtension_mul_left (F : TupleFunctional) (W Z : FormalSpan) (r : AmbientSpace → AmbientSpace) :
    F.spanExtension (formalMul W (pushSpan r Z)) =
      ∑ Y ∈ W.support, ∑ X ∈ Z.support,
        (W Y * Z X) * (F (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push r X)) : ℂ) := by
  have h := formalMul_sum W.support Z.support (fun Y => W Y) (fun X => Z X) id
    (fun X => _root_.YangMills.Construction.SeparatedTuples.push r X)
  simp only [id] at h
  rw [← span_expansion W, ← pushSpan_eq] at h
  rw [h]
  simp [TupleFunctional.spanExtension, linearExtend_basisVec, map_sum]
private theorem spanExtension_mul_right (F : TupleFunctional) (W Z : FormalSpan) (r : AmbientSpace → AmbientSpace) :
    F.spanExtension (formalMul (pushSpan r Z) W) =
      ∑ X ∈ Z.support, ∑ Y ∈ W.support,
        (Z X * W Y) * (F (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push r X) Y) : ℂ) := by
  have h := formalMul_sum Z.support W.support (fun X => Z X) (fun Y => W Y)
    (fun X => _root_.YangMills.Construction.SeparatedTuples.push r X) id
  simp only [id] at h
  rw [← span_expansion W, ← pushSpan_eq] at h
  rw [h]
  simp [TupleFunctional.spanExtension, linearExtend_basisVec, map_sum]
private theorem translationContinuousOnSpans_of
    (hm : MovingTests.TranslatesTendsto) (F : TupleFunctional) (hF : F.IsAdmissiblyContinuous) :
    TranslationContinuousOnSpans F := by
  intro Z W v hdef
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ X ∈ Z.support, ∀ Y ∈ W.support,
      ∀ v' : AmbientSpace, euclidNorm (v' - v) ≤ δ →
        SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X) ∧
          SepTuple.Composable (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v') X) Y := by
    refine (Filter.eventually_all_finset _).2 fun X hX =>
      (Filter.eventually_all_finset _).2 fun Y hY => ?_
    obtain ⟨δ₀, hδ₀, H⟩ := composable_near hm X Y v (hdef X hX Y hY)
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ v' hv'
    exact H v' (hv'.trans hδ.2.le)
  obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ0, fun v' hv' X hX Y hY => hδ X hX Y hY v' hv', ?_, ?_⟩
  · simp only [spanExtension_mul_left]
    refine tendsto_finsetSum _ fun Y hY => tendsto_finsetSum _ fun X hX => ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_juxt_left hm F hF X Y v (hdef X hX Y hY))).const_mul _
  · simp only [spanExtension_mul_right]
    refine tendsto_finsetSum _ fun X hX => tendsto_finsetSum _ fun Y hY => ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_juxt_right hm F hF X Y v (hdef X hX Y hY))).const_mul _
theorem limitIsContinuousFunctional_of
    (hcov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hbd : ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hmov : MovingTests.Statement) : LimitIsContinuousFunctional := by
  intro D T C σ _ hC hlim
  have hj : ∀ j, ∃ τ : TupleFunctional,
      (∀ X : SepTuple, τ X = ∫ U, T.tupleRep j X U ∂T.state j) ∧
        τ.IsPermInvariant ∧ τ.IsEntrywiseLinear := fun j =>
    (hcov D.L D.isAdmissible T j).2.2.2.2
  choose τ hτ hτs hτm using hj
  have hempty : σ SepTuple.nil = 1 := by
    refine tendsto_nhds_unique (hlim SepTuple.nil) (tendsto_const_nhds.congr fun j => ?_)
    rw [← hτ j, (τ j).map_nil]
  let F : TupleFunctional := ⟨σ, hempty⟩
  have hsym : F.IsPermInvariant := fun X ς =>
    tendsto_nhds_unique (hlim (X.reorder ς)) ((hlim X).congr fun j => by
      rw [← hτ j, ← hτ j, hτs j X ς])
  have hmul : F.IsEntrywiseLinear := by
    intro A B f f' α α' X X' Z hX hX' hZ
    refine tendsto_nhds_unique (hlim Z)
      ((((hlim X).const_mul α).add ((hlim X').const_mul α')).congr fun j => ?_)
    rw [← hτ j, ← hτ j, ← hτ j, hτm j A B f f' α α' X X' Z hX hX' hZ]
  have hB : BoundedByProducts F C := boundedByProducts_of_convergesTo hC hlim
  have hd1 : SatisfiesDifferenceBound σ C c1NormR4 :=
    satisfiesDifferenceBound_of F hmul hB c1NormR4_zero c1NormR4_nonneg fun _ _ => le_rfl
  have hcont : F.IsAdmissiblyContinuous := isAdmissiblyContinuous_of_bound F hd1
  have hsharp : ∀ M : ℝ, 1 ≤ M → SatisfiesDifferenceBound σ C (sharpNormR4 M) := by
    intro M hM
    have hle : ∀ g, IsC1c g → c1NormR4 g ≤ sharpNormR4 M g :=
      fun g hg => (hbd.2.1 M hM g hg).1
    have hn : ∀ g : RealValued, 0 ≤ sharpNormR4 M g := fun g =>
      (uniformNorm_nonneg g).trans (le_max_left _ _)
    have h0C : IsC1c (0 : RealValued) :=
      ⟨contDiff_const, HasCompactSupport.zero⟩
    have h0 : sharpNormR4 M (0 : RealValued) = 0 := by
      refine le_antisymm ?_ (hn 0)
      have := (hbd.2.1 M hM 0 h0C).2
      rwa [c1NormR4_zero, mul_zero] at this
    exact satisfiesDifferenceBound_of F hmul hB h0 hn hle
  refine ⟨F, rfl, hsym, hmul, hd1, hcont, hsharp, ?_,
    translationContinuousOnSpans_of hmov.1 F hcont⟩
  intro X Y v h
  obtain ⟨δ, hδ, H⟩ := composable_near hmov.1 X Y v h
  exact ⟨δ, hδ, H, tendsto_juxt_left hmov.1 F hcont X Y v h, tendsto_juxt_right hmov.1 F hcont X Y v h⟩
end YangMills.Construction.ReflectionPositivity.LimitContinuity
end
