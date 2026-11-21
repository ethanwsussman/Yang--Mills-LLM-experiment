import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.Continuum.TelescopingOverRotatedEntries
import YangMills.Construction.PeriodicOperators.SymbolOfAProductProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Orthogonal TestFunctions SeparatedTuples
open TorusMetric (euclidNormVec)
namespace Rotations.OrthogonalSetting.TelescopingProof
open InfiniteLattice (AmbientSpace)
theorem euclidNormVec_eq_euclidean_norm (u : AmbientSpace) :
    euclidNormVec u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_zero_vec : euclidNormVec (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_add_le_add (v w : AmbientSpace) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
theorem euclidNormVec_sub_symm (x y : AmbientSpace) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_matMap_sub_le (Q : orthogonalGroupFour) (x : AmbientSpace) :
    euclidNormVec (OrthogonalAction.matMap Q x - x) ≤
      matrixOperatorNorm (Q.1 - 1) * euclidNormVec x := by
  have hle := (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (Q.1 - 1)).le_opNorm
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))
  rw [Matrix.toEuclideanCLM_toLp, Matrix.sub_mulVec, Matrix.one_mulVec] at hle
  rw [euclidNormVec_eq_euclidean_norm, euclidNormVec_eq_euclidean_norm x]
  exact hle
def nbhdOf (r : ℝ) (S : Set AmbientSpace) : Set AmbientSpace :=
  {x | ∃ y ∈ S, euclidNormVec (x - y) ≤ r}
theorem subset_nbhdOf {r : ℝ} (hr : 0 ≤ r) (S : Set AmbientSpace) : S ⊆ nbhdOf r S :=
  fun x hx => ⟨x, hx, by simpa [euclidNormVec_zero_vec] using hr⟩
theorem nbhdOf_subset_closedBall {d R₀ : ℝ} (hd : 0 < d) {S : Set AmbientSpace}
    (hS : S ⊆ closedBallR4 0 R₀) : nbhdOf (d / 4) S ⊆ closedBallR4 0 (R₀ + d) := by
  rintro x ⟨y, hy, hxy⟩
  have hy' : euclidNormVec (y - 0) ≤ R₀ := hS hy
  have htri := euclidNormVec_add_le_add (x - y) (y - 0)
  have e : x - y + (y - 0) = x - 0 := by abel
  rw [e] at htri
  show euclidNormVec (x - 0) ≤ R₀ + d
  linarith
theorem half_le_dist_of_mem_nbhdOf {d : ℝ} (hd : 0 < d) {S T : Set AmbientSpace}
    (hST : ENNReal.ofReal d ≤ setDistR4 S T) {x y : AmbientSpace}
    (hx : x ∈ nbhdOf (d / 4) S) (hy : y ∈ nbhdOf (d / 4) T) :
    d / 2 ≤ euclidNormVec (x - y) := by
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  have h₁ : setDistR4 S T ≤ ENNReal.ofReal (euclidNormVec (x' - y')) :=
    iInf₂_le_of_le x' hx' (iInf₂_le y' hy')
  have hnn : 0 ≤ euclidNormVec (x' - y') := Real.sqrt_nonneg _
  have h₂ : d ≤ euclidNormVec (x' - y') :=
    (ENNReal.ofReal_le_ofReal_iff hnn).1 (hST.trans h₁)
  have h₃ := euclidNormVec_add_le_add (x' - x) (x - y')
  have h₄ := euclidNormVec_add_le_add (x - y) (y - y')
  have e₃ : x' - x + (x - y') = x' - y' := by abel
  have e₄ : x - y + (y - y') = x - y' := by abel
  rw [e₃] at h₃
  rw [e₄] at h₄
  have e₅ : euclidNormVec (x' - x) = euclidNormVec (x - x') := euclidNormVec_sub_symm _ _
  linarith
theorem half_le_setDist_of_subset_nbhdOf {d : ℝ} (hd : 0 < d) {S T S' T' : Set AmbientSpace}
    (hST : ENNReal.ofReal d ≤ setDistR4 S T) (hS : S' ⊆ nbhdOf (d / 4) S)
    (hT : T' ⊆ nbhdOf (d / 4) T) :
    ENNReal.ofReal (d / 2) ≤ setDistR4 S' T' :=
  le_iInf₂ fun _ ha => le_iInf₂ fun _ hb =>
    ENNReal.ofReal_le_ofReal (half_le_dist_of_mem_nbhdOf hd hST (hS ha) (hT hb))
theorem disjoint_of_subset_nbhdOf {d : ℝ} (hd : 0 < d) {S T S' T' : Set AmbientSpace}
    (hST : ENNReal.ofReal d ≤ setDistR4 S T) (hS : S' ⊆ nbhdOf (d / 4) S)
    (hT : T' ⊆ nbhdOf (d / 4) T) : Disjoint S' T' := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have hle := half_le_dist_of_mem_nbhdOf hd hST (hS hx) (hT hx')
  rw [sub_self, euclidNormVec_zero_vec] at hle
  linarith
theorem orthogonalAct_mem_nbhdOf (laws : OrthogonalAction.Laws.Statement) {d R₀ : ℝ}
    {Q : orthogonalGroupFour}
    (hQ : matrixOperatorNorm (Q.1 - 1) * R₀ ≤ d / 4) {f : RealValued}
    (hf : IsC1c f) (hs : tsupport f ⊆ closedBallR4 0 R₀) :
    IsC1c (orthogonalAct Q f) ∧
      tsupport (orthogonalAct Q f) ⊆ nbhdOf (d / 4) (tsupport f) := by
  obtain ⟨hC, -, hsupp, -⟩ := (laws.1 Q Q).1 f hf
  refine ⟨hC, ?_⟩
  rw [hsupp]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  have hx' : euclidNormVec (x - 0) ≤ R₀ := hs hx
  rw [sub_zero] at hx'
  have hn : 0 ≤ matrixOperatorNorm (Q.1 - 1) := norm_nonneg _
  exact (euclidNormVec_matMap_sub_le Q x).trans
    ((mul_le_mul_of_nonneg_left hx' hn).trans hQ)
theorem sub_mem_nbhdOf {d : ℝ} (hd : 0 < d) {f g : RealValued}
    (hf : IsC1c f) (hg : IsC1c g)
    (hs : tsupport f ⊆ nbhdOf (d / 4) (tsupport g)) :
    IsC1c (f - g) ∧ tsupport (f - g) ⊆ nbhdOf (d / 4) (tsupport g) := by
  refine ⟨⟨ContDiff.sub hf.1 hg.1, ?_⟩, ?_⟩
  · exact HasCompactSupport.sub hf.2 hg.2
  · have hsub : tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by
      refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))
      intro x hx
      by_contra hn
      simp only [Set.mem_union, not_or] at hn
      have h₁ : f x = 0 := image_eq_zero_of_notMem_tsupport hn.1
      have h₂ : g x = 0 := image_eq_zero_of_notMem_tsupport hn.2
      exact (Function.mem_support.mp hx) (by simp [h₁, h₂])
    exact hsub.trans (Set.union_subset hs (subset_nbhdOf (by positivity) _))
theorem list_eq_of_getD {Y Y' : List RealValued} (hl : Y.length = Y'.length)
    (hget : ∀ i, i < Y.length → Y.getD i 0 = Y'.getD i 0) : Y = Y' := by
  refine List.ext_getElem hl fun i h₁ h₂ => ?_
  have := hget i h₁
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this
theorem getD_set_eq (Y : List RealValued) (n i : ℕ) (v : RealValued) (hi : i < Y.length) :
    (Y.set n v).getD i 0 = if n = i then v else Y.getD i 0 := by
  have hi' : i < (Y.set n v).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi, List.getElem_set]
theorem length_rotateElementsOn (Q : orthogonalGroupFour) (J : Finset ℕ) (X : List RealValued) :
    (rotateEntriesOn Q J X).length = X.length := by
  simp [rotateEntriesOn]
theorem getD_rotateTermsOn (Q : orthogonalGroupFour) (J : Finset ℕ) (X : List RealValued)
    (i : ℕ) (hi : i < X.length) :
    (rotateEntriesOn Q J X).getD i 0 =
      if i + 1 ∈ J then orthogonalAct Q (X.getD i 0) else X.getD i 0 := by
  have hi' : i < (rotateEntriesOn Q J X).length := by rwa [length_rotateElementsOn]
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi]
  simp [rotateEntriesOn, add_comm]
theorem prod_map_eq_prod_Icc (g : RealValued → ℝ) (Y : List RealValued) :
    (Y.map g).prod = ∏ l ∈ Finset.Icc 1 Y.length, g (Y.getD (l - 1) 0) := by
  have h₀ : (Y.map g).prod = ∏ i ∈ Finset.range Y.length, g (Y.getD i 0) := by
    induction Y with
    | nil => simp
    | cons f Y ih => simp [Finset.prod_range_succ', ih, mul_comm]
  have h₁ : Finset.Icc 1 Y.length = Finset.Ico (0 + 1) (Y.length + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h₀, h₁, ← Finset.prod_Ico_add' (fun l => g (Y.getD (l - 1) 0)) 0 Y.length 1,
    Finset.range_eq_Ico]
  simp
theorem bound_of_components_in_nbhdOf {M : ℝ} {σ : TupleFunctional} {B : ℕ → ℝ → ℝ → ℝ}
    (hB : HasSeparatedBounds M σ B) {k : ℕ} {d R₀ : ℝ} (hk : 1 ≤ k) (hd : 0 < d)
    (hR : 0 < R₀) {X Y : List RealValued} (hX : X.length = k) (hY : Y.length = k)
    (hsupp : ∀ f ∈ X, tsupport f ⊆ closedBallR4 0 R₀)
    (hsep : X.Pairwise (fun f g => ENNReal.ofReal d ≤ setDistR4 (tsupport f) (tsupport g)))
    (hent : ∀ i, i < k → IsC1c (Y.getD i 0) ∧
      tsupport (Y.getD i 0) ⊆ nbhdOf (d / 4) (tsupport (X.getD i 0))) :
    ∃ hs : IsDisjointlySupported Y, |σ ⟨Y, hs⟩| ≤
      B k (d / 2) (R₀ + d) * ∏ l ∈ Finset.Icc 1 k, sharpNormR4 M (Y.getD (l - 1) 0) := by
  have hXd : ∀ i j, i < j → j < k → ENNReal.ofReal d ≤
      setDistR4 (tsupport (X.getD i 0)) (tsupport (X.getD j 0)) := by
    intro i j hij hj
    have hi' : i < X.length := by omega
    have hj' : j < X.length := by omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
    exact List.pairwise_iff_getElem.1 hsep i j hi' hj' hij
  have hs : IsDisjointlySupported Y := by
    refine ⟨fun f hf => ?_, List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
      have := (hent i (by omega)).1
      rwa [List.getD_eq_getElem _ _ hi] at this
    · have h₁ := (hent i (by omega)).2
      have h₂ := (hent j (by omega)).2
      rw [List.getD_eq_getElem _ _ hi] at h₁
      rw [List.getD_eq_getElem _ _ hj] at h₂
      exact disjoint_of_subset_nbhdOf hd (hXd i j hij (by omega)) h₁ h₂
  refine ⟨hs, ?_⟩
  have hb := (hB k hk (d / 2) (R₀ + d) (by positivity) (by positivity)).2 ⟨Y, hs⟩ hY ?_ ?_
  · have e := prod_map_eq_prod_Icc (sharpNormR4 M) Y
    rw [hY] at e
    rwa [e] at hb
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
    have hi₀ : i < Y.length := hi
    have hi' : i < k := by omega
    have hX' : i < X.length := by omega
    have h₁ := (hent i hi').2
    rw [List.getD_eq_getElem _ _ hi₀] at h₁
    refine ⟨0, h₁.trans (nbhdOf_subset_closedBall hd (hsupp _ ?_))⟩
    rw [List.getD_eq_getElem _ _ hX']
    exact List.getElem_mem hX'
  · refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
    have hi₀ : i < Y.length := hi
    have hj₀ : j < Y.length := hj
    have h₁ := (hent i (by omega)).2
    have h₂ := (hent j (by omega)).2
    rw [List.getD_eq_getElem _ _ hi₀] at h₁
    rw [List.getD_eq_getElem _ _ hj₀] at h₂
    exact half_le_setDist_of_subset_nbhdOf hd (hXd i j hij (by omega)) h₁ h₂
theorem set_eq_take_append_drop (Y : List RealValued) (n : ℕ) (v : RealValued)
    (hn : n < Y.length) :
    Y.set n v = Y.take n ++ v :: Y.drop (n + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hn]
theorem rotatedEntriesTelescoping_holds (laws : OrthogonalAction.Laws.Statement) :
    RotatedEntriesTelescoping := by
  intro M σ B hM hmult hB k d R₀ h hk hd hR hlen hsupp hsep Q I hQ hI
  have hXlen : h.1.length = k := hlen
  have hbase : ∀ i, i < k → IsC1c (h.1.getD i 0) ∧
      tsupport (h.1.getD i 0) ⊆ closedBallR4 0 R₀ := by
    intro i hi
    have hi' : i < h.1.length := by omega
    rw [List.getD_eq_getElem _ _ hi']
    have hm := List.getElem_mem hi'
    exact ⟨h.2.1 _ hm, hsupp _ hm⟩
  have hd4 : (0 : ℝ) ≤ d / 4 := by positivity
  have hrot : ∀ (J : Finset ℕ) (i : ℕ), i < k →
      IsC1c ((rotateEntriesOn Q J h.1).getD i 0) ∧
      tsupport ((rotateEntriesOn Q J h.1).getD i 0) ⊆
        nbhdOf (d / 4) (tsupport (h.1.getD i 0)) := by
    intro J i hi
    rw [getD_rotateTermsOn Q J h.1 i (by omega)]
    split_ifs
    · exact orthogonalAct_mem_nbhdOf laws hQ (hbase i hi).1 (hbase i hi).2
    · exact ⟨(hbase i hi).1, subset_nbhdOf hd4 _⟩
  have hlenJ : ∀ J : Finset ℕ, (rotateEntriesOn Q J h.1).length = k := fun J => by
    rw [length_rotateElementsOn, hXlen]
  have hsepJ : ∀ J : Finset ℕ, IsDisjointlySupported (rotateEntriesOn Q J h.1) := fun J =>
    (bound_of_components_in_nbhdOf hB hk hd hR hXlen (hlenJ J) hsupp hsep (hrot J)).1
  have hnorm : ∀ i, i < k → ∀ J : Finset ℕ,
      sharpNormR4 M ((rotateEntriesOn Q J h.1).getD i 0) = sharpNormR4 M (h.1.getD i 0) := by
    intro i hi J
    rw [getD_rotateTermsOn Q J h.1 i (by omega)]
    split_ifs
    · exact ((laws.1 Q Q).1 _ (hbase i hi).1).2.2.2.1 M hM
    · rfl
  have key : ∀ J : Finset ℕ, J ⊆ Finset.Icc 1 k →
      |σ ⟨rotateEntriesOn Q J h.1, hsepJ J⟩ - σ h| ≤
        B k (d / 2) (R₀ + d) *
          ∑ l ∈ J, sharpNormR4 M (orthogonalAct Q (h.componentAt (l - 1)) - h.componentAt (l - 1)) *
            ∏ l' ∈ (Finset.Icc 1 k).erase l, sharpNormR4 M (h.componentAt (l' - 1)) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      have e : rotateEntriesOn Q ∅ h.1 = h.1 := by
        refine list_eq_of_getD (length_rotateElementsOn Q ∅ h.1) fun i hi => ?_
        rw [length_rotateElementsOn] at hi
        rw [getD_rotateTermsOn Q ∅ h.1 i hi]
        simp
      have e' : (⟨rotateEntriesOn Q ∅ h.1, hsepJ ∅⟩ : SepTuple) = h := Subtype.ext e
      rw [e']
      simp
    | insert a J ha ih =>
      intro hJ
      have haI : a ∈ Finset.Icc 1 k := hJ (Finset.mem_insert_self a J)
      have hJ' : J ⊆ Finset.Icc 1 k := (Finset.subset_insert a J).trans hJ
      obtain ⟨ha1, hak⟩ := Finset.mem_Icc.1 haI
      have hp : a - 1 < k := by omega
      have hpa : a - 1 + 1 = a := by omega
      have hpY : a - 1 < (rotateEntriesOn Q J h.1).length := by rw [hlenJ]; exact hp
      have hfC := (hbase _ hp).1
      have hQf := orthogonalAct_mem_nbhdOf laws hQ hfC (hbase _ hp).2
      have hdiff := sub_mem_nbhdOf hd hQf.1 hfC hQf.2
      obtain ⟨hZs, hZb⟩ := bound_of_components_in_nbhdOf (Y := (rotateEntriesOn Q J h.1).set (a - 1)
        (orthogonalAct Q (h.1.getD (a - 1) 0) - h.1.getD (a - 1) 0)) hB hk hd hR hXlen
        (by rw [List.length_set, hlenJ]) hsupp hsep (by
          intro i hi
          rw [getD_set_eq _ _ _ _ (by rw [hlenJ]; exact hi)]
          split_ifs with hai
          · subst hai
            exact hdiff
          · exact hrot J i hi)
      have e₁ : rotateEntriesOn Q (insert a J) h.1 =
          (rotateEntriesOn Q J h.1).take (a - 1) ++
            orthogonalAct Q (h.1.getD (a - 1) 0) :: (rotateEntriesOn Q J h.1).drop (a - 1 + 1) := by
        rw [← set_eq_take_append_drop _ _ _ hpY]
        refine list_eq_of_getD (by rw [List.length_set, hlenJ, hlenJ]) fun i hi => ?_
        have hi' : i < h.1.length := by rwa [length_rotateElementsOn] at hi
        have hi'' : i < (rotateEntriesOn Q J h.1).length := by rw [hlenJ]; omega
        rw [getD_set_eq _ _ _ _ hi'', getD_rotateTermsOn Q _ h.1 i hi',
          getD_rotateTermsOn Q J h.1 i hi']
        by_cases hai : a - 1 = i
        · subst hai
          rw [if_pos rfl, if_pos (by rw [hpa]; exact Finset.mem_insert_self a J)]
        · have hne : i + 1 ≠ a := by omega
          rw [if_neg hai]
          simp [Finset.mem_insert, hne]
      have e₂ : rotateEntriesOn Q J h.1 =
          (rotateEntriesOn Q J h.1).take (a - 1) ++
            h.1.getD (a - 1) 0 :: (rotateEntriesOn Q J h.1).drop (a - 1 + 1) := by
        rw [← set_eq_take_append_drop _ _ _ hpY]
        refine list_eq_of_getD (by rw [List.length_set]) fun i hi => ?_
        rw [getD_set_eq _ _ _ _ hi]
        by_cases hai : a - 1 = i
        · subst hai
          rw [if_pos rfl, getD_rotateTermsOn Q J h.1 _ (by omega), hpa, if_neg ha]
        · rw [if_neg hai]
      have e₃ : (rotateEntriesOn Q J h.1).set (a - 1)
            (orthogonalAct Q (h.1.getD (a - 1) 0) - h.1.getD (a - 1) 0) =
          (rotateEntriesOn Q J h.1).take (a - 1) ++
            ((1 : ℝ) • orthogonalAct Q (h.1.getD (a - 1) 0) + (-1 : ℝ) • h.1.getD (a - 1) 0) ::
              (rotateEntriesOn Q J h.1).drop (a - 1 + 1) := by
        rw [set_eq_take_append_drop _ _ _ hpY]
        congr 2
        simp [sub_eq_add_neg]
      have hm := hmult _ _ _ _ 1 (-1) ⟨_, hsepJ (insert a J)⟩ ⟨_, hsepJ J⟩ ⟨_, hZs⟩ e₁ e₂ e₃
      have hprod : ∏ l ∈ Finset.Icc 1 k, sharpNormR4 M
            (((rotateEntriesOn Q J h.1).set (a - 1)
              (orthogonalAct Q (h.1.getD (a - 1) 0) - h.1.getD (a - 1) 0)).getD (l - 1) 0) =
          sharpNormR4 M (orthogonalAct Q (h.componentAt (a - 1)) - h.componentAt (a - 1)) *
            ∏ l' ∈ (Finset.Icc 1 k).erase a, sharpNormR4 M (h.componentAt (l' - 1)) := by
        rw [← Finset.mul_prod_erase _ _ haI]
        congr 1
        · rw [getD_set_eq _ _ _ _ hpY, if_pos rfl]
          rfl
        · refine Finset.prod_congr rfl fun l hl => ?_
          obtain ⟨hla, hlI⟩ := Finset.mem_erase.1 hl
          obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.1 hlI
          have hlk' : l - 1 < k := by omega
          rw [getD_set_eq _ _ _ _ (by rw [hlenJ]; exact hlk'), if_neg (by omega)]
          exact hnorm _ hlk' J
      rw [hprod] at hZb
      have hih := ih hJ'
      rw [Finset.sum_insert ha, mul_add]
      have ht : σ ⟨rotateEntriesOn Q (insert a J) h.1, hsepJ (insert a J)⟩ - σ h =
          σ ⟨_, hZs⟩ + (σ ⟨rotateEntriesOn Q J h.1, hsepJ J⟩ - σ h) := by
        rw [hm]
        ring
      rw [ht]
      exact (abs_add_le _ _).trans (add_le_add hZb hih)
  exact ⟨hsepJ I, key I hI⟩
end Rotations.OrthogonalSetting.TelescopingProof
end YangMills.Construction
end
