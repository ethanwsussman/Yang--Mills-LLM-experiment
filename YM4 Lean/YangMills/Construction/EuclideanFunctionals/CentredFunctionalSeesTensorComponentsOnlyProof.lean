import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.LimitsOfLatticeFamilies.LinearRelationsAmongTensors
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TensorComponents
section Basics
variable {𝕜 : Type*} [RCLike 𝕜]
theorem supp_eq_tsupport (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem disjoint_supp_iff (f g : R4 → 𝕜) :
    Disjoint (supp f) (supp g) ↔ Disjoint (tsupport f) (tsupport g) := by
  rw [supp_eq_tsupport, supp_eq_tsupport]
def SepFamily {n : ℕ} (f : Fin n → R4 → 𝕜) : Prop :=
  (∀ i, ContDiff ℝ 1 (f i) ∧ HasCompactSupport (f i)) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))
theorem SepFamily.comp {n m : ℕ} {f : Fin n → R4 → 𝕜} (hf : SepFamily f) {e : Fin m → Fin n}
    (he : Function.Injective e) : SepFamily (f ∘ e) :=
  ⟨fun i => hf.1 (e i), fun _ _ hij => hf.2 (he.ne hij)⟩
theorem tsupport_smul_add_smul_subset (a b : 𝕜) (f g : R4 → 𝕜) :
    tsupport (a • f + b • g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport f).union (isClosed_tsupport g))
  by_contra hn
  simp only [Set.mem_union, not_or] at hn
  apply hx
  simp [image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
theorem contDiff_hasCompactSupport_smul_add_smul (a b : 𝕜) {f g : R4 → 𝕜}
    (hf : ContDiff ℝ 1 f ∧ HasCompactSupport f) (hg : ContDiff ℝ 1 g ∧ HasCompactSupport g) :
    ContDiff ℝ 1 (a • f + b • g) ∧ HasCompactSupport (a • f + b • g) :=
  ⟨(hf.1.const_smul a).add (hg.1.const_smul b),
    IsCompact.of_isClosed_subset (IsCompact.union hf.2 hg.2) (isClosed_tsupport _)
      (tsupport_smul_add_smul_subset a b f g)⟩
theorem SepFamily.update_smul_add_smul {n : ℕ} {f : Fin n → R4 → 𝕜} {i : Fin n} {g : R4 → 𝕜}
    (hf : SepFamily f) (hg : SepFamily (Function.update f i g)) (a b : 𝕜) :
    SepFamily (Function.update f i (a • f i + b • g)) := by
  have hgi : ContDiff ℝ 1 g ∧ HasCompactSupport g := by
    have := hg.1 i
    rwa [Function.update_self] at this
  have hgd : ∀ l, l ≠ i → Disjoint (tsupport g) (tsupport (f l)) := fun l hl => by
    have := hg.2 hl.symm
    simp only [Function.update_self, Function.update_of_ne hl] at this
    exact this
  have key : ∀ l, l ≠ i → Disjoint (tsupport (a • f i + b • g)) (tsupport (f l)) := fun l hl =>
    Set.disjoint_of_subset_left (tsupport_smul_add_smul_subset a b _ _)
      (Set.disjoint_union_left.2 ⟨hf.2 hl.symm, hgd l hl⟩)
  refine ⟨fun k => ?_, fun k l hkl => ?_⟩
  · by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact contDiff_hasCompactSupport_smul_add_smul a b (hf.1 k) hgi
    · rw [Function.update_of_ne hk]
      exact hf.1 k
  · show Disjoint (tsupport (Function.update f i (a • f i + b • g) k))
      (tsupport (Function.update f i (a • f i + b • g) l))
    by_cases hk : k = i
    · subst hk
      have hl : l ≠ k := hkl.symm
      rw [Function.update_self, Function.update_of_ne hl]
      exact key l hl
    · by_cases hl : l = i
      · subst hl
        rw [Function.update_self, Function.update_of_ne hk]
        exact (key k hk).symm
      · rw [Function.update_of_ne hk, Function.update_of_ne hl]
        exact hf.2 hkl
end Basics
theorem complexFamily_iff {n : ℕ} (h : Fin n → R4 → ℂ) :
    ComplexComponents h ↔ 1 ≤ n ∧ SepFamily h := by
  constructor
  · intro H
    refine ⟨H.one_le, fun i => (mem_C1c_iff _).1 (H.mem i), fun i j hij => ?_⟩
    exact (disjoint_supp_iff _ _).1 (H.disjoint hij)
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun i => (mem_C1c_iff _).2 (h₂ i), fun i j hij => ?_⟩
    exact (disjoint_supp_iff _ _).2 (h₃ hij)
theorem ofFn_mem_sepN_iff {n : ℕ} (f : Fin n → R4 → ℝ) :
    List.ofFn f ∈ sepN n ↔ SepFamily f := by
  constructor
  · rintro ⟨-, h₁, h₂⟩
    refine ⟨fun i => (mem_C1c_iff _).1 (h₁ _ (List.mem_ofFn.2 ⟨i, rfl⟩)), fun i j hij => ?_⟩
    have h₃ := List.pairwise_ofFn.1 h₂
    rcases lt_or_gt_of_ne hij with h | h
    · exact (disjoint_supp_iff _ _).1 (h₃ h)
    · exact ((disjoint_supp_iff _ _).1 (h₃ h)).symm
  · rintro ⟨h₁, h₂⟩
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact (mem_C1c_iff _).2 (h₁ i)
    · exact List.pairwise_ofFn.2 fun i j hij => (disjoint_supp_iff _ _).2 (h₂ hij.ne)
theorem ofFn_mem_sepAll_iff {n : ℕ} (f : Fin n → R4 → ℝ) :
    List.ofFn f ∈ sepAll ↔ SepFamily f := by
  rw [← ofFn_mem_sepN_iff]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
    have hl : m = n := hm.1.symm.trans List.length_ofFn
    exact hl ▸ hm
  · exact fun h => Ambient.separatedN_subset_separatedAll _ _ n h
theorem setDist_pos_of_disjoint {A B : Set R4} (hA : IsCompact A) (hB : IsCompact B)
    (h : Disjoint A B) : 0 < Ambient.setDist defaultMirrorData Ambient.euclidean A B := by
  obtain ⟨δ, hδ, hd⟩ := h.exists_thickenings hA hB.isClosed
  have hab : ∀ a ∈ A, ∀ b ∈ B, δ ≤ TorusMetric.euclidNormVec (a - b) := fun a ha b hb => by
    have hab : δ ≤ dist a b := by
      by_contra hlt
      have h₁ : b ∈ Metric.thickening δ A :=
        Metric.mem_thickening_iff.2 ⟨a, ha, by rw [dist_comm]; exact not_le.1 hlt⟩
      have h₂ : b ∈ Metric.thickening δ B :=
        Metric.mem_thickening_iff.2 ⟨b, hb, by simpa using hδ⟩
      exact Set.disjoint_left.1 hd h₁ h₂
    refine hab.trans ?_
    rw [dist_eq_norm]
    exact SeparatedTuplesR4.norm_le_euclidNormVec _
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ)
    (le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hab a ha b hb))
theorem fn_update_smul_add_smul (S : ConnFamily) {m : ℕ} (hm : 2 ≤ m) (j : Fin m)
    {f : Fin m → R4 → ℝ} {g : R4 → ℝ} (hf : SepFamily f) (hg : SepFamily (Function.update f j g))
    (a a' : ℝ) :
    Ambient.evalOrZero (S.fn m hm) (List.ofFn (Function.update f j (a • f j + a' • g))) =
      a * Ambient.evalOrZero (S.fn m hm) (List.ofFn f) +
        a' * Ambient.evalOrZero (S.fn m hm) (List.ofFn (Function.update f j g)) := by
  classical
  let A : Fin m → Set R4 := fun k => if k = j then tsupport (f j) ∪ tsupport g else tsupport (f k)
  have hgj : HasCompactSupport g := by
    have := (hg.1 j).2
    rwa [Function.update_self] at this
  have hcomp : ∀ k, IsCompact (A k) := fun k => by
    by_cases hk : k = j
    · simp only [A, hk, if_true]
      exact IsCompact.union (hf.1 j).2 hgj
    · simp only [A, hk, if_false]
      exact (hf.1 k).2
  have hgd : ∀ l, l ≠ j → Disjoint (tsupport g) (tsupport (f l)) := fun l hl => by
    have := hg.2 hl.symm
    simp only [Function.update_self, Function.update_of_ne hl] at this
    exact this
  have hdis : Pairwise fun k l => Disjoint (A k) (A l) := fun k l hkl => by
    by_cases hk : k = j
    · have hl : l ≠ j := fun e => hkl (hk.trans e.symm)
      simp only [A, hk, hl, if_true, if_false]
      exact Set.disjoint_union_left.2 ⟨hf.2 hl.symm, hgd l hl⟩
    · by_cases hl : l = j
      · simp only [A, hk, hl, if_true, if_false]
        exact (Set.disjoint_union_left.2 ⟨hf.2 (Ne.symm hk), hgd k hk⟩).symm
      · simp only [A, hk, hl, if_false]
        exact hf.2 hkl
  have hA : Pairwise fun k l =>
      0 < Ambient.setDist defaultMirrorData Ambient.euclidean (A k) (A l) :=
    fun k l hkl => setDist_pos_of_disjoint (hcomp k) (hcomp l) (hdis hkl)
  have hfA : ∀ k, f k ∈ Ambient.compactC1SuppIn defaultMirrorData Ambient.euclidean (A k) :=
    fun k => by
      refine ⟨(mem_C1c_iff _).2 (hf.1 k), ?_⟩
      show supp (f k) ⊆ A k
      rw [supp_eq_tsupport]
      by_cases hk : k = j
      · subst hk
        simp only [A, if_true]
        exact Set.subset_union_left
      · simp only [A, hk, if_false]
        exact subset_rfl
  have hgA : g ∈ Ambient.compactC1SuppIn defaultMirrorData Ambient.euclidean (A j) := by
    refine ⟨(mem_C1c_iff _).2 ?_, ?_⟩
    · have := hg.1 j
      rwa [Function.update_self] at this
    · show supp g ⊆ A j
      rw [supp_eq_tsupport]
      simp only [A, if_true]
      exact Set.subset_union_right
  exact S.fn_multilinear m hm A hA f hfA j g hgA a a'
def tupleComponents (X : FnList) {n : ℕ} (e : X.length = n) : Fin n → R4 → ℝ :=
  fun l => X.get (Fin.cast e.symm l)
theorem ofFn_tupleComponents (X : FnList) {n : ℕ} (e : X.length = n) :
    List.ofFn (tupleComponents X e) = X := by
  subst e
  exact List.ofFn_get X
theorem tupleComponents_ofFn {n : ℕ} (f : Fin n → R4 → ℝ) :
    tupleComponents (List.ofFn f) List.length_ofFn = f := by
  funext l
  simp [tupleComponents]
theorem centeredFn_eq_sum (S : ConnFamily) (X : FnList) {n : ℕ} (e : X.length = n)
    (hX : X ∈ sepAll) :
    centeredFn S ⟨X, hX⟩ = ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
      S.evalAt J.card (List.ofFn fun k : Fin J.card => tupleComponents X e (J.orderEmbOfFin rfl k)) := by
  subst e
  rfl
def blockFactor (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) (J : Finset (Fin n)) : ℝ :=
  S.evalAt J.card (List.ofFn fun k : Fin J.card => f (J.orderEmbOfFin rfl k))
theorem centeredAt_ofFn (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) (hf : SepFamily f) :
    centeredAt S (List.ofFn f) =
      ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, blockFactor S f J := by
  have hX : List.ofFn f ∈ sepAll := (ofFn_mem_sepAll_iff f).2 hf
  have h := centeredFn_eq_sum S (List.ofFn f) List.length_ofFn hX
  rw [tupleComponents_ofFn] at h
  exact (dif_pos hX).trans h
theorem blockFactor_update_of_notMem (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ) {i : Fin n}
    (c : R4 → ℝ) {J : Finset (Fin n)} (hi : i ∉ J) :
    blockFactor S (Function.update f i c) J = blockFactor S f J := by
  have h : (fun k : Fin J.card => Function.update f i c (J.orderEmbOfFin rfl k)) =
      fun k => f (J.orderEmbOfFin rfl k) := by
    funext k
    have hm := J.orderEmbOfFin_mem rfl k
    exact Function.update_of_ne (fun e => hi (by rwa [e] at hm)) _ _
  rw [blockFactor, blockFactor, h]
theorem blockFactor_update_smul_add_smul (S : ConnFamily) {n : ℕ} {f : Fin n → R4 → ℝ}
    {g : R4 → ℝ} {i : Fin n} {J : Finset (Fin n)} (hi : i ∈ J) (hJ : 2 ≤ J.card)
    (hf : SepFamily f) (hg : SepFamily (Function.update f i g)) (a a' : ℝ) :
    blockFactor S (Function.update f i (a • f i + a' • g)) J =
      a * blockFactor S f J + a' * blockFactor S (Function.update f i g) J := by
  have he : Function.Injective (J.orderEmbOfFin rfl) := (J.orderEmbOfFin rfl).injective
  obtain ⟨j, hj⟩ : ∃ j, J.orderEmbOfFin rfl j = i := by
    have : i ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    exact this
  have hu : ∀ c, (fun k => Function.update f i c (J.orderEmbOfFin rfl k)) =
      Function.update (f ∘ J.orderEmbOfFin rfl) j c := fun c => by
    rw [← hj]
    exact Function.update_comp_eq_of_injective f he j c
  have hg' : SepFamily (Function.update (f ∘ J.orderEmbOfFin rfl) j g) := by
    rw [← hu g]
    exact hg.comp he
  have h := fn_update_smul_add_smul S hJ j (hf.comp he) hg' a a'
  have hfj : (f ∘ J.orderEmbOfFin rfl) j = f i := congrArg f hj
  rw [hfj] at h
  have hr : ∀ Y, S.evalAt J.card Y = Ambient.evalOrZero (S.fn J.card hJ) Y := fun Y => dif_pos hJ
  rw [blockFactor, blockFactor, blockFactor, hu, hu]
  exact (hr _).trans (h.trans (congrArg₂ (· + ·) (congrArg (a * ·) (hr _).symm)
    (congrArg (a' * ·) (hr _).symm)))
theorem prod_blockFactor_update_smul_add_smul (S : ConnFamily) {n : ℕ}
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ SetPartition.nonSingletonPartitions n) {f : Fin n → R4 → ℝ} {g : R4 → ℝ}
    {i : Fin n} (hf : SepFamily f) (hg : SepFamily (Function.update f i g)) (a a' : ℝ) :
    ∏ J ∈ π.parts, blockFactor S (Function.update f i (a • f i + a' • g)) J =
      a * ∏ J ∈ π.parts, blockFactor S f J +
        a' * ∏ J ∈ π.parts, blockFactor S (Function.update f i g) J := by
  classical
  obtain ⟨J₀, hJ₀, hi⟩ := π.exists_mem (Finset.mem_univ i)
  have hcard : 2 ≤ J₀.card := by
    have h₁ := (LatticeLimits.ModelSpace.mem_nonSingletonPartitions_iff π).1 hπ J₀ hJ₀
    have h₂ := (π.nonempty_of_mem_parts hJ₀).card_pos
    omega
  have hne : ∀ J ∈ π.parts.erase J₀, i ∉ J := fun J hJ hiJ =>
    (Finset.mem_erase.1 hJ).1 (π.eq_of_mem_parts (Finset.mem_erase.1 hJ).2 hJ₀ hiJ hi)
  have e₁ : ∏ J ∈ π.parts.erase J₀, blockFactor S (Function.update f i (a • f i + a' • g)) J =
      ∏ J ∈ π.parts.erase J₀, blockFactor S f J :=
    Finset.prod_congr rfl fun J hJ => blockFactor_update_of_notMem S f _ (hne J hJ)
  have e₂ : ∏ J ∈ π.parts.erase J₀, blockFactor S (Function.update f i g) J =
      ∏ J ∈ π.parts.erase J₀, blockFactor S f J :=
    Finset.prod_congr rfl fun J hJ => blockFactor_update_of_notMem S f _ (hne J hJ)
  rw [← Finset.mul_prod_erase _ _ hJ₀, ← Finset.mul_prod_erase _ (blockFactor S f) hJ₀,
    ← Finset.mul_prod_erase _ (blockFactor S (Function.update f i g)) hJ₀, e₁, e₂,
    blockFactor_update_smul_add_smul S hi hcard hf hg a a']
  ring
theorem centeredAt_update_smul_add_smul (S : ConnFamily) {n : ℕ} {f : Fin n → R4 → ℝ}
    {g : R4 → ℝ} {i : Fin n} (hf : SepFamily f) (hg : SepFamily (Function.update f i g))
    (a a' : ℝ) :
    centeredAt S (List.ofFn (Function.update f i (a • f i + a' • g))) =
      a * centeredAt S (List.ofFn f) +
        a' * centeredAt S (List.ofFn (Function.update f i g)) := by
  rw [centeredAt_ofFn S _ (hf.update_smul_add_smul hg a a'), centeredAt_ofFn S f hf,
    centeredAt_ofFn S _ hg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun π hπ => prod_blockFactor_update_smul_add_smul S hπ hf hg a a'
theorem isRealMultilinear (S : ConnFamily) : IsRealMultilinear S := by
  intro n _ i f g hf hg a a'
  have hf' := (ofFn_mem_sepN_iff f).1 hf
  have hg' := (ofFn_mem_sepN_iff _).1 hg
  exact ⟨(ofFn_mem_sepN_iff _).2 (hf'.update_smul_add_smul hg' a a'),
    centeredAt_update_smul_add_smul S hf' hg' a a',
    fun hn => fn_update_smul_add_smul S hn i hf' hg' a a'⟩
theorem supportIn_eq_tsupport (f : R4 → ℝ) :
    LatticeLimits.ModelSpace.supportIn stdParamsR4 LatticeLimits.ModelSpace.euclidean f =
      tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem isCompactIn_iff (Z : Set R4) :
    LatticeLimits.ModelSpace.IsCompactIn stdParamsR4 LatticeLimits.ModelSpace.euclidean Z ↔
      IsCompact Z :=
  SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) Z
theorem mem_sepTuplesIn_top_iff {q : ℕ} (f : Fin q → R4 → ℝ) :
    f ∈ LatticeLimits.ModelSpace.sepTuplesIn stdParamsR4
      LatticeLimits.ModelSpace.euclidean q ⊤ ↔ SepFamily f := by
  rw [LatticeLimits.ModelSpace.sepTuplesIn_top]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun i => ⟨h₁ i, ?_⟩, fun i k hik => ?_⟩
    · have h := h₂ i
      rw [supportIn_eq_tsupport] at h
      exact (isCompactIn_iff _).1 h
    · have h := h₃ i k hik
      rw [supportIn_eq_tsupport, supportIn_eq_tsupport] at h
      exact h
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => (h₁ i).1, fun i => ?_, fun i k hik => ?_⟩
    · rw [supportIn_eq_tsupport]
      exact (isCompactIn_iff _).2 (h₁ i).2
    · rw [supportIn_eq_tsupport, supportIn_eq_tsupport]
      exact h₂ hik
def orderFunctional (S : ConnFamily) (q : ℕ) :
    LatticeLimits.ModelSpace.TupleFunctional
      (LatticeLimits.ModelSpace.sepTuplesIn stdParamsR4
        LatticeLimits.ModelSpace.euclidean q ⊤) :=
  fun f => centeredAt S (List.ofFn (f.1 : Fin q → R4 → ℝ))
theorem orderFunctional_extend (S : ConnFamily) {q : ℕ} {x : Fin q → R4 → ℝ}
    (hx : SepFamily x) :
    (orderFunctional S q).extend x = centeredAt S (List.ofFn x) :=
  LatticeLimits.ModelSpace.TupleFunctional.extend_of_mem _ ((mem_sepTuplesIn_top_iff x).2 hx)
def InC1On (B : Set R4) (x : R4 → ℝ) : Prop :=
  (ContDiff ℝ 1 x ∧ HasCompactSupport x) ∧ tsupport x ⊆ B
theorem inC1On_of_mem {B : Set R4} {x : R4 → ℝ}
    (hx : x ∈ LatticeLimits.ModelSpace.c1CompactSupp stdParamsR4
      LatticeLimits.ModelSpace.euclidean B) : InC1On B x := by
  obtain ⟨h₁, h₂, h₃⟩ := hx
  rw [supportIn_eq_tsupport] at h₂ h₃
  exact ⟨⟨h₁, (isCompactIn_iff _).1 h₂⟩, h₃⟩
theorem sepFamily_of_inC1On {q : ℕ} {A : Fin q → Set R4}
    (hA : ∀ l k, l ≠ k → Disjoint (A l) (A k))
    {x : Fin q → R4 → ℝ} (hx : ∀ l, InC1On (A l) (x l)) : SepFamily x :=
  ⟨fun l => (hx l).1, fun l k hlk => (hA l k hlk).mono (hx l).2 (hx k).2⟩
theorem orderFunctional_update_smul_add_smul (S : ConnFamily) {q : ℕ} {A : Fin q → Set R4}
    (hA : ∀ l k, l ≠ k → Disjoint (A l) (A k)) {g : Fin q → R4 → ℝ}
    (hg : ∀ l, InC1On (A l) (g l)) (i : Fin q) {u v : R4 → ℝ} (hu : InC1On (A i) u)
    (hv : InC1On (A i) v) (α β : ℝ) :
    (orderFunctional S q).extend (Function.update g i (α • u + β • v)) =
      α * (orderFunctional S q).extend (Function.update g i u) +
        β * (orderFunctional S q).extend (Function.update g i v) := by
  have hs : ∀ w, InC1On (A i) w → SepFamily (Function.update g i w) := by
    intro w hw
    refine sepFamily_of_inC1On hA fun l => ?_
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self]
      exact hw
    · rw [Function.update_of_ne hl]
      exact hg l
  have hsu := hs u hu
  have hsv := hs v hv
  have hsv' : SepFamily (Function.update (Function.update g i u) i v) := by
    rw [Function.update_idem]
    exact hsv
  have hc := hsu.update_smul_add_smul hsv' α β
  have h := centeredAt_update_smul_add_smul S hsu hsv' α β
  simp only [Function.update_self, Function.update_idem] at h hc
  exact (orderFunctional_extend S hc).trans (h.trans (congrArg₂ (· + ·)
    (congrArg (α * ·) (orderFunctional_extend S hsu).symm)
    (congrArg (β * ·) (orderFunctional_extend S hsv).symm)))
theorem orderFunctional_isMultilinearSep (S : ConnFamily) (q : ℕ) :
    LatticeLimits.ModelSpace.IsMultilinearSep (orderFunctional S q) := by
  intro A _ hA g hg i u hu v hv α β
  exact orderFunctional_update_smul_add_smul S hA (fun l => inC1On_of_mem (hg l)) i
    (inC1On_of_mem hu) (inC1On_of_mem hv) α β
def restrictLength (q : ℕ) (F : FreeSep) : FreeSep := F.filter fun X => X.1.length = q
theorem length_of_mem_restrictLength {q : ℕ} {F : FreeSep} {X : sepAll}
    (h : X ∈ (restrictLength q F).support) : X.1.length = q := by
  rw [restrictLength, Finsupp.support_filter, Finset.mem_filter] at h
  exact h.2
theorem eq_sum_restrictLength (F : FreeSep) :
    F = ∑ q ∈ F.support.image (fun X => X.1.length), restrictLength q F := by
  classical
  ext X
  rw [Finsupp.finsetSum_apply]
  simp only [restrictLength, Finsupp.filter_apply]
  rw [Finset.sum_ite_eq _ X.1.length (fun _ => F X)]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (Finset.mem_image.2 ⟨X, Finsupp.mem_support_iff.2 fun e => hne e, rfl⟩)
theorem tensorComp_single (q : ℕ) (X : sepAll) (c : ℂ) :
    tensorComp q (Finsupp.single X c) = c • tensorAt q X := by
  simp [tensorComp, liftLin]
theorem tensorComp_restrictLength_self (q : ℕ) (F : FreeSep) :
    tensorComp q (restrictLength q F) = tensorComp q F := by
  induction F using Finsupp.induction_linear with
  | zero =>
    have h : restrictLength q (0 : FreeSep) = 0 := Finsupp.filter_zero _
    rw [h]
  | add F G hF hG =>
    have h : restrictLength q (F + G) = restrictLength q F + restrictLength q G :=
      Finsupp.filter_add
    rw [h, map_add, map_add, hF, hG]
  | single X c =>
    by_cases hX : X.1.length = q
    · have h : restrictLength q (Finsupp.single X c) = Finsupp.single X c :=
        Finsupp.filter_single_of_pos _ hX
      rw [h]
    · have h : restrictLength q (Finsupp.single X c) = 0 := Finsupp.filter_single_of_neg _ hX
      rw [h, map_zero, tensorComp_single, tensorAt_of_length_ne X hX, smul_zero]
theorem tensorComp_restrictLength_of_ne {q r : ℕ} (hr : r ≠ q) (F : FreeSep) :
    tensorComp r (restrictLength q F) = 0 := by
  induction F using Finsupp.induction_linear with
  | zero =>
    have h : restrictLength q (0 : FreeSep) = 0 := Finsupp.filter_zero _
    rw [h, map_zero]
  | add F G hF hG =>
    have h : restrictLength q (F + G) = restrictLength q F + restrictLength q G :=
      Finsupp.filter_add
    rw [h, map_add, hF, hG, add_zero]
  | single X c =>
    by_cases hX : X.1.length = q
    · have h : restrictLength q (Finsupp.single X c) = Finsupp.single X c :=
        Finsupp.filter_single_of_pos _ hX
      rw [h, tensorComp_single, tensorAt_of_length_ne X (fun e => hr (e.symm.trans hX)),
        smul_zero]
    · have h : restrictLength q (Finsupp.single X c) = 0 := Finsupp.filter_single_of_neg _ hX
      rw [h, map_zero]
theorem centeredFnFree_eq_sum (S : ConnFamily) (G : FreeSep) :
    centeredFnFree S G = ∑ X ∈ G.support, G X * (centeredFn S X : ℂ) := by
  simp [centeredFnFree, liftReal, liftLin, Finsupp.linearCombination_apply, Finsupp.sum]
theorem tensorComp_eq_sum (q : ℕ) (G : FreeSep) :
    tensorComp q G = ∑ X ∈ G.support, G X • tensorAt q X := by
  simp [tensorComp, liftLin, Finsupp.linearCombination_apply, Finsupp.sum]
theorem sepFamily_tupleComponents (X : sepAll) {n : ℕ} (e : X.1.length = n) :
    SepFamily (tupleComponents X.1 e) := by
  rw [← ofFn_mem_sepAll_iff, ofFn_tupleComponents]
  exact X.2
theorem centeredFnFree_eq_zero_of_length (hT : LatticeLimits.TensorRelations.Claim)
    (S : ConnFamily) {q : ℕ} (hq : 1 ≤ q) {G : FreeSep} (hG : ∀ X ∈ G.support, X.1.length = q)
    (h0 : tensorComp q G = 0) : centeredFnFree S G = 0 := by
  classical
  let f : G.support → LatticeLimits.ModelSpace.sepTuplesIn stdParamsR4
      LatticeLimits.ModelSpace.euclidean q ⊤ := fun t =>
    ⟨tupleComponents t.1.1 (hG t.1 t.2), (mem_sepTuplesIn_top_iff _).2 (sepFamily_tupleComponents t.1 _)⟩
  have hten : ∀ t : G.support,
      LatticeLimits.ModelSpace.cTensor stdParamsR4 LatticeLimits.ModelSpace.euclidean
        (f t).1 = tensorAt q t.1 := fun t => by
    rw [tensorAt_of_length t.1 (hG t.1 t.2)]
    funext y
    show ((∏ l, tupleComponents t.1.1 (hG t.1 t.2) l (y l) : ℝ) : ℂ) =
      ∏ l, ((tupleComponents t.1.1 (hG t.1 t.2) l (y l) : ℝ) : ℂ)
    exact Complex.ofReal_prod _ _
  have hsum : ∑ t : G.support, G t.1 • LatticeLimits.ModelSpace.cTensor stdParamsR4
      LatticeLimits.ModelSpace.euclidean (f t).1 = 0 := by
    have h₁ := tensorComp_eq_sum q G
    rw [h0, ← Finset.sum_coe_sort G.support (fun X => G X • tensorAt q X)] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) h₁.symm
    rw [hten t]
    rfl
  have hrel := ((hT stdParamsR4 LatticeLimits.ModelSpace.euclidean q ⊤ hq (by simp)).1
    (orderFunctional S q) (orderFunctional_isMultilinearSep S q)).1 G.support f (fun t => G t.1) hsum
  have hval : ∀ t : G.support, orderFunctional S q (f t) = centeredFn S t.1 := fun t => by
    show centeredAt S (List.ofFn (tupleComponents t.1.1 (hG t.1 t.2))) = _
    rw [ofFn_tupleComponents]
    exact dif_pos t.1.2
  rw [centeredFnFree_eq_sum, ← Finset.sum_coe_sort G.support (fun X => G X * (centeredFn S X : ℂ))]
  refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) hrel
  rw [hval t]
def freeNil : FreeSep := toFree (Ambient.emptyList defaultMirrorData Ambient.euclidean).1
theorem tensorCompZero_freeNil : tensorCompZero freeNil = 1 :=
  (liftLin_toFree _ _).trans (if_pos rfl)
theorem tensorComp_freeNil {r : ℕ} (hr : r ≠ 0) : tensorComp r freeNil = 0 :=
  (liftLin_toFree _ _).trans (tensorAt_of_length_ne _ fun e => hr e.symm)
theorem centeredFnFree_freeNil (hV : CenteredInitialValues.InitialValues) (S : ConnFamily) :
    centeredFnFree S freeNil = 1 := by
  have h : centeredFnFree S freeNil =
      (centeredFn S (Ambient.emptyList defaultMirrorData Ambient.euclidean) : ℂ) :=
    liftLin_toFree _ _
  rw [h, (hV S).1]
  simp
theorem centeredFnFree_of_length_zero (hV : CenteredInitialValues.InitialValues) (S : ConnFamily)
    {G : FreeSep} (hG : ∀ X ∈ G.support, X.1.length = 0) :
    centeredFnFree S G = tensorCompZero G := by
  have h₀ : tensorCompZero G = ∑ X ∈ G.support, G X * tensorAtZero X := by
    simp [tensorCompZero, liftLin, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [centeredFnFree_eq_sum, h₀]
  refine Finset.sum_congr rfl fun X hX => ?_
  have hl := hG X hX
  have e : X = Ambient.emptyList defaultMirrorData Ambient.euclidean :=
    Subtype.ext (List.eq_nil_of_length_eq_zero hl)
  have h₁ : tensorAtZero X = 1 := if_pos hl
  rw [h₁]
  rw [e, (hV S).1]
  simp
theorem centeredFnFree_eq_zero_of_tensorComp (hT : LatticeLimits.TensorRelations.Claim)
    (hV : CenteredInitialValues.InitialValues) (S : ConnFamily) {D : FreeSep}
    (hD : ∀ n, tensorComp n D = 0) : centeredFnFree S D = 0 := by
  have h := congrArg (centeredFnFree S) (eq_sum_restrictLength D)
  rw [map_sum] at h
  rw [h]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hc : tensorComp q (restrictLength q D) = 0 := by
    rw [tensorComp_restrictLength_self, hD]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [centeredFnFree_of_length_zero hV S fun X hX => length_of_mem_restrictLength hX,
      ← tensorComp_zero_apply _ (fun i => i.elim0), hc]
    rfl
  · exact centeredFnFree_eq_zero_of_length hT S hq (fun X hX => length_of_mem_restrictLength hX) hc
theorem respectsSameTensors (hT : LatticeLimits.TensorRelations.Claim)
    (hV : CenteredInitialValues.InitialValues) (S : ConnFamily) :
    RespectsSameTensors S := fun F F' h => by
  have hs := (sameTensors_iff F F').1 h
  have hz := centeredFnFree_eq_zero_of_tensorComp hT hV S (D := F - F') fun n => by
    rw [map_sub, hs n, sub_self]
  rw [map_sub] at hz
  exact sub_eq_zero.1 hz
theorem hasSoleTensorComp_smul_add_smul {q : ℕ} {A A' : TestSpaces.PointTuple q → ℂ}
    {F F' : FreeSep} (h : HasSoleTensorComp q A F) (h' : HasSoleTensorComp q A' F') (x x' : ℂ) :
    HasSoleTensorComp q (x • A + x' • A') (x • F + x' • F') :=
  ⟨by rw [map_add, map_smul, map_smul, h.1, h'.1], fun r hr => by
    rw [map_add, map_smul, map_smul, h.2 r hr, h'.2 r hr, smul_zero, smul_zero, add_zero]⟩
theorem centeredFnFree_eq_of_hasSoleTensorComp (hT : LatticeLimits.TensorRelations.Claim)
    (hV : CenteredInitialValues.InitialValues) (S : ConnFamily) {q : ℕ}
    {A : TestSpaces.PointTuple q → ℂ} {F F' : FreeSep} (h : HasSoleTensorComp q A F)
    (h' : HasSoleTensorComp q A F') :
    centeredFnFree S F = centeredFnFree S F' :=
  respectsSameTensors hT hV S F F' ((sameTensors_iff _ _).2 fun n => by
    by_cases hn : n = q
    · subst hn
      rw [h.1, h'.1]
    · rw [h.2 n hn, h'.2 n hn])
theorem hasSoleTensorComp_complexTuple (hR : TupleRules.TupleSpanActionRules) {n : ℕ}
    {h : Fin n → R4 → ℂ} (H : ComplexComponents h) :
    HasSoleTensorComp n (tensorOfFns h) (complexTuple h) := by
  obtain ⟨-, -, -, -, -, -, -, hC, -⟩ := hR
  obtain ⟨-, -, h₂, h₃, h₄, -⟩ := hC Set.univ isOpen_univ timeFlip n h H fun _ => Set.subset_univ _
  refine ⟨h₂, fun q hq => ?_⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq'
  · funext e
    rw [tensorComp_zero_apply, h₃]
    rfl
  · exact h₄ q hq' hq
theorem hasSoleTensorComp_smul_freeNil (A : TestSpaces.PointTuple 0 → ℂ)
    (e : TestSpaces.PointTuple 0) :
    HasSoleTensorComp 0 A (A e • freeNil) := by
  refine ⟨?_, fun r hr => by rw [map_smul, tensorComp_freeNil hr, smul_zero]⟩
  funext e'
  have he : e' = e := funext fun l => l.elim0
  rw [tensorComp_zero_apply, map_smul, tensorCompZero_freeNil, he]
  simp
theorem tensorRealizedAsSoleComp (hR : TupleRules.TupleSpanActionRules) (q : ℕ) :
    TensorRealizedAsSoleComp q := by
  intro A hA
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨_, hasSoleTensorComp_smul_freeNil A fun l => l.elim0⟩
  · have hq' : q ≠ 0 := by omega
    simp only [sepTensorSpan, if_neg hq'] at hA
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, h₁, h₂, rfl⟩ := hx
      exact ⟨_, hasSoleTensorComp_complexTuple hR ⟨hq, h₁, h₂⟩⟩
    | zero => exact ⟨0, map_zero _, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF⟩ := hx
      obtain ⟨F', hF'⟩ := hy
      exact ⟨F + F', by rw [map_add, hF.1, hF'.1], fun r hr => by
        rw [map_add, hF.2 r hr, hF'.2 r hr, add_zero]⟩
    | smul a x _ hx =>
      obtain ⟨F, hF⟩ := hx
      exact ⟨a • F, by rw [map_smul, hF.1], fun r hr => by rw [map_smul, hF.2 r hr, smul_zero]⟩
theorem centeredOnTensor_eq (hT : LatticeLimits.TensorRelations.Claim)
    (hR : TupleRules.TupleSpanActionRules) (hV : CenteredInitialValues.InitialValues)
    (S : ConnFamily) {q : ℕ} {A : TestSpaces.PointTuple q → ℂ} {F : FreeSep}
    (hA : A ∈ sepTensorSpan q) (hF : HasSoleTensorComp q A F) :
    centeredOnTensor S q A = centeredFnFree S F :=
  centeredFnFree_eq_of_hasSoleTensorComp hT hV S
    (Classical.epsilon_spec (tensorRealizedAsSoleComp hR q A hA)) hF
theorem tsupport_ofReal_comp (f : R4 → ℝ) : tsupport (fun x => (f x : ℂ)) = tsupport f := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem SepFamily.ofReal {n : ℕ} {f : Fin n → R4 → ℝ} (hf : SepFamily f) :
    SepFamily fun l x => (f l x : ℂ) := by
  refine ⟨fun i => ⟨Complex.ofRealCLM.contDiff.comp (hf.1 i).1, ?_⟩, fun i j hij => ?_⟩
  · show IsCompact (tsupport fun x => (f i x : ℂ))
    rw [tsupport_ofReal_comp]
    exact (hf.1 i).2
  · show Disjoint (tsupport fun x => (f i x : ℂ)) (tsupport fun x => (f j x : ℂ))
    rw [tsupport_ofReal_comp, tsupport_ofReal_comp]
    exact hf.2 hij
theorem tensorComp_mem_sepTensorSpan (F : FreeSep) (q : ℕ) :
    tensorComp q F ∈ sepTensorSpan q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [sepTensorSpan]
  · have hq' : q ≠ 0 := by omega
    simp only [sepTensorSpan, if_neg hq']
    rw [tensorComp_eq_sum]
    refine Submodule.sum_mem _ fun X _ => Submodule.smul_mem _ _ ?_
    by_cases hX : X.1.length = q
    · rw [tensorAt_of_length X hX]
      have H : ComplexComponents (cplxEntries X.1 hX) :=
        (complexFamily_iff _).2 ⟨hq, (sepFamily_tupleComponents X hX).ofReal⟩
      exact Submodule.subset_span ⟨_, H.mem, H.disjoint, rfl⟩
    · rw [tensorAt_of_length_ne X hX]
      exact zero_mem _
theorem eqFinsumOverOrders (hT : LatticeLimits.TensorRelations.Claim)
    (hR : TupleRules.TupleSpanActionRules) (hV : CenteredInitialValues.InitialValues)
    (S : ConnFamily) : EqFinsumOverOrders S := by
  intro F
  classical
  have hpart : ∀ q, HasSoleTensorComp q (tensorComp q F) (restrictLength q F) := fun q =>
    ⟨tensorComp_restrictLength_self q F, fun _ hr => tensorComp_restrictLength_of_ne hr F⟩
  have hval : ∀ q, centeredOnTensor S q (tensorComp q F) =
      centeredFnFree S (restrictLength q F) := fun q =>
    centeredOnTensor_eq hT hR hV S (tensorComp_mem_sepTensorSpan F q) (hpart q)
  have hsub : (Function.support fun q => centeredOnTensor S q (tensorComp q F)) ⊆
      ↑(F.support.image fun X => X.1.length) := by
    intro q hq
    by_contra hn
    apply hq
    show centeredOnTensor S q (tensorComp q F) = 0
    have hz : restrictLength q F = 0 := Finsupp.ext fun X => by
      rw [restrictLength, Finsupp.filter_apply]
      split_ifs with h
      · by_contra hne
        exact hn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨X, Finsupp.mem_support_iff.2 hne, h⟩))
      · rfl
    rw [hval, hz, map_zero]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  calc centeredFnFree S F
      = centeredFnFree S (∑ q ∈ F.support.image (fun X => X.1.length), restrictLength q F) :=
        congrArg _ (eq_sum_restrictLength F)
    _ = ∑ q ∈ F.support.image (fun X => X.1.length),
        centeredFnFree S (restrictLength q F) := map_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun q _ => (hval q).symm
theorem tensorOfFns_update_smul_add_smul {n : ℕ} (h : Fin n → R4 → ℂ) (i : Fin n) (g : R4 → ℂ)
    (a a' : ℂ) :
    tensorOfFns (Function.update h i (a • h i + a' • g)) =
      a • tensorOfFns h + a' • tensorOfFns (Function.update h i g) := by
  classical
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, tensorOfFns_apply, smul_eq_mul]
  have e₁ : ∏ l ∈ Finset.univ.erase i, Function.update h i (a • h i + a' • g) l (x l) =
      ∏ l ∈ Finset.univ.erase i, h l (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have e₂ : ∏ l ∈ Finset.univ.erase i, Function.update h i g l (x l) =
      ∏ l ∈ Finset.univ.erase i, h l (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => h l (x l)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => Function.update h i g l (x l)) (Finset.mem_univ i),
    e₁, e₂]
  simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem isComplexMultilinear (hT : LatticeLimits.TensorRelations.Claim)
    (hR : TupleRules.TupleSpanActionRules) (hV : CenteredInitialValues.InitialValues)
    (S : ConnFamily) : IsComplexMultilinear S := by
  intro n i a a' h g H Hg
  have hh := (complexFamily_iff h).1 H
  have hgs := (complexFamily_iff _).1 Hg
  have Hc : ComplexComponents (Function.update h i (a • h i + a' • g)) :=
    (complexFamily_iff _).2 ⟨hh.1, hh.2.update_smul_add_smul hgs.2 a a'⟩
  refine ⟨Hc.disjoint, ?_⟩
  have h₂ := hasSoleTensorComp_smul_add_smul (hasSoleTensorComp_complexTuple hR H)
    (hasSoleTensorComp_complexTuple hR Hg) a a'
  rw [← tensorOfFns_update_smul_add_smul] at h₂
  rw [centeredFnFree_eq_of_hasSoleTensorComp hT hV S (hasSoleTensorComp_complexTuple hR Hc) h₂,
    map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
theorem expandsOverReImParts (hT : LatticeLimits.TensorRelations.Claim)
    (hR : TupleRules.TupleSpanActionRules) (hV : CenteredInitialValues.InitialValues)
    (S : ConnFamily) : ExpandsOverReImParts S := by
  intro n h H
  obtain ⟨-, -, -, -, -, -, -, hC, -⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE⟩ :=
    hC Set.univ isOpen_univ timeFlip n h H fun _ => Set.subset_univ _
  rw [← respectsSameTensors hT hV S _ _ hE, TupleRules.fullyExpanded, map_sum]
  exact Finset.sum_congr rfl fun ε _ => by rw [map_smul, smul_eq_mul]
theorem centeredSeesTensorComps (hT : LatticeLimits.TensorRelations.Claim)
    (hR : TupleRules.TupleSpanActionRules) (hV : CenteredInitialValues.InitialValues) :
    CenteredSeesTensorComps := fun S =>
  ⟨isRealMultilinear S, respectsSameTensors hT hV S,
    ⟨fun q => ⟨tensorRealizedAsSoleComp hR q,
        fun _ _ _ _ hF hF' => centeredFnFree_eq_of_hasSoleTensorComp hT hV S hF hF',
        fun A hA A' hA' x x' => by
          obtain ⟨F, hF⟩ := tensorRealizedAsSoleComp hR q A hA
          obtain ⟨F', hF'⟩ := tensorRealizedAsSoleComp hR q A' hA'
          have hs : x • A + x' • A' ∈ sepTensorSpan q :=
            Submodule.add_mem _ (Submodule.smul_mem _ _ hA) (Submodule.smul_mem _ _ hA')
          rw [centeredOnTensor_eq hT hR hV S hs (hasSoleTensorComp_smul_add_smul hF hF' x x'),
            centeredOnTensor_eq hT hR hV S hA hF, centeredOnTensor_eq hT hR hV S hA' hF', map_add,
            map_smul, map_smul, smul_eq_mul, smul_eq_mul]⟩,
      fun A e => by
        have hA : A ∈ sepTensorSpan 0 := by simp [sepTensorSpan]
        rw [centeredOnTensor_eq hT hR hV S hA (hasSoleTensorComp_smul_freeNil A e), map_smul,
          centeredFnFree_freeNil hV S]
        simp,
      fun q h H => centeredOnTensor_eq hT hR hV S
        (by
          have hq : q ≠ 0 := by have := H.one_le; omega
          simp only [sepTensorSpan, if_neg hq]
          exact Submodule.subset_span ⟨h, H.mem, H.disjoint, rfl⟩)
        (hasSoleTensorComp_complexTuple hR H),
      tensorComp_mem_sepTensorSpan, eqFinsumOverOrders hT hR hV S⟩,
    isComplexMultilinear hT hR hV S, expandsOverReImParts hT hR hV S⟩
end YangMills.Construction.EuclideanFunctionals.TensorComponents
