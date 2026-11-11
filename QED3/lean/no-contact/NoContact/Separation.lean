module

public import NoContact.Multilinear

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace NoContact

/-- The no-contact assertion for all smaller positive arities and all open sets. -/
def KnownBelow (n : ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ], 0 < Fintype.card κ → Fintype.card κ < n →
    ∀ (U : Set X), IsOpen U → ∀ (D : Form κ), Local U D → GradientZero U D →
      ∀ f : κ → L2, (∀ i, Supported U (f i)) → D f = 0

/-- One compactly supported entry separated from all other entries forces vanishing. -/
theorem one_separated_zero {ι : Type} [Fintype ι] (hcard : 1 < Fintype.card ι)
    (ih : KnownBelow (Fintype.card ι)) {U : Set X} (hU : IsOpen U)
    (D : Form ι) (hlocal : Local U D) (hgrad : GradientZero U D)
    (f : ι → L2) (i : ι) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (hfi : Supported K (f i)) (hrest : ∀ j, j ≠ i → Supported (U \ K) (f j)) :
    D f = 0 := by
  classical
  let P : ι → Prop := fun j => j ≠ i
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hpos : 0 < Fintype.card {j // P j} := Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
  have hlt : Fintype.card {j // P j} < Fintype.card ι := Fintype.card_subtype_lt (x := i) (by simp [P])
  have hzero := ih {j // P j} hpos hlt (U \ K) (hU.sdiff hK.isClosed)
    (freeze D P f)
  have hloc : Local (U \ K) (freeze D P f) := by
    intro L hL hLU hdis g hg
    let K' : ι → Set X := fun j => if h : j ≠ i then L ⟨j, h⟩ else K
    apply hlocal K'
    · intro j
      by_cases hj : j ≠ i
      · simpa only [K', dite_eq_left hj] using hL ⟨j, hj⟩
      · simpa only [K', dite_eq_right hj] using hK
    · intro j
      by_cases hj : j ≠ i
      · simpa only [K', dite_eq_left hj] using (hLU ⟨j, hj⟩).trans (sdiff_subset : U \ K ⊆ U)
      · simpa only [K', dite_eq_right hj] using hKU
    · intro a b hab
      by_cases ha : a ≠ i <;> by_cases hb : b ≠ i
      · simpa only [K', dite_eq_left ha, dite_eq_left hb] using hdis
          (show (⟨a, ha⟩ : {j // P j}) ≠ ⟨b, hb⟩ from fun h => hab (congrArg Subtype.val h))
      · simpa only [K', dite_eq_left ha, dite_eq_right hb] using (Set.disjoint_left.mpr
          (fun x (hx : x ∈ L ⟨a, ha⟩) (hy : x ∈ K) => (hLU ⟨a, ha⟩ hx).2 hy))
      · simpa only [K', dite_eq_right ha, dite_eq_left hb] using (Set.disjoint_left.mpr
          (fun x (hx : x ∈ K) (hy : x ∈ L ⟨b, hb⟩) => (hLU ⟨b, hb⟩ hy).2 hx))
      · exact (hab (by simpa using (not_not.mp ha).trans (not_not.mp hb).symm)).elim
    · intro j
      by_cases hj : j ≠ i
      · simpa [assemble, P, K', hj] using hg ⟨j, hj⟩
      · have heq : j = i := not_not.mp hj
        subst j
        simpa [assemble, P, K'] using hfi
  have hgr : GradientZero (U \ K) (freeze D P f) :=
    gradientZero_freeze hgrad sdiff_subset P f (by
      intro j hj
      have heq : j = i := by simpa [P] using hj
      subst j
      exact hfi.mono hKU)
  simpa using hzero hloc hgr (fun j => f j) (fun j => hrest j j.property)

/-- Two nonempty groups, one supported in a compact set and the other outside it,
force vanishing. -/
theorem compact_group_separated_zero {ι : Type} [Fintype ι]
    (hcard : 1 < Fintype.card ι) (ih : KnownBelow (Fintype.card ι))
    {U : Set X} (hU : IsOpen U) (D : Form ι) (hlocal : Local U D)
    (hgrad : GradientZero U D) (P : ι → Prop) (hP : ∃ i, P i) (hPc : ∃ i, ¬ P i)
    (f : ι → L2) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (hinside : ∀ i, ¬ P i → Supported K (f i))
    (houtside : ∀ i, P i → Supported (U \ K) (f i)) : D f = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hP
  obtain ⟨j₀, hj₀⟩ := hPc
  have hpos : 0 < Fintype.card {i // P i} := Fintype.card_pos_iff.mpr ⟨⟨i₀, hi₀⟩⟩
  have hlt : Fintype.card {i // P i} < Fintype.card ι := Fintype.card_subtype_lt hj₀
  have hloc : Local (U \ K) (freeze D P f) := by
    intro L hL hLU hdis g hg
    let i : {i // P i} := ⟨i₀, hi₀⟩
    apply one_separated_zero hcard ih hU D hlocal hgrad (assemble P f g) i₀
      (L i) (hL i) ((hLU i).trans sdiff_subset)
    · simpa [assemble, i, hi₀] using hg i
    · intro j hji
      by_cases hj : P j
      · have hne : (⟨j, hj⟩ : {i // P i}) ≠ i := fun h => hji (congrArg Subtype.val h)
        have hsub : L ⟨j, hj⟩ ⊆ U \ L i := by
          intro x hx
          exact ⟨(hLU ⟨j, hj⟩ hx).1,
            fun hxi => Set.disjoint_left.mp (hdis hne) hx hxi⟩
        simpa [assemble, hj] using (hg ⟨j, hj⟩).mono hsub
      · have hsub : K ⊆ U \ L i := by
          intro x hx
          exact ⟨hKU hx, fun hxi => (hLU i hxi).2 hx⟩
        simpa [assemble, hj] using (hinside j hj).mono hsub
  have hgr := gradientZero_freeze (V := U \ K) hgrad sdiff_subset P f
    (fun i hi => (hinside i hi).mono hKU)
  simpa using ih {i // P i} hpos hlt (U \ K) (hU.sdiff hK.isClosed)
    (freeze D P f) hloc hgr (fun i => f i) (fun i => houtside i i.property)

/-- Extend vanishing for compactly separated groups to measurable separated groups. -/
theorem splitZero_of_lower {ι : Type} [Fintype ι]
    (hcard : 1 < Fintype.card ι) (ih : KnownBelow (Fintype.card ι))
    {U : Set X} (hU : IsOpen U) (D : Form ι) (hlocal : Local U D)
    (hgrad : GradientZero U D) : SplitZero U D := by
  classical
  intro s hs P f hP hPc hf hin hout
  let S : ι → Set X := fun i => if P i then U ∩ s else U ∩ sᶜ
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    by_cases hi : P i <;> simp only [S, hi, ite_true, ite_false]
    · exact hU.measurableSet.inter hs
    · exact hU.measurableSet.inter hs.compl
  refine continuous_zero_of_compact S hS D D.cont ?_ f ?_
  · intro g hg
    choose K hK hKS hgK using hg
    let T : Set X := ⋃ i : {i // ¬ P i}, K i
    have hT : IsCompact T := isCompact_iUnion (fun i => hK i)
    have hTU : T ⊆ U := by
      intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hxi⟩
      have hxiS : x ∈ U ∩ sᶜ := by simpa [S, i.property] using hKS i hxi
      exact hxiS.1
    apply compact_group_separated_zero hcard ih hU D hlocal hgrad P hP hPc g T hT hTU
    · intro i hi
      exact (hgK i).mono (subset_iUnion (fun j : {i // ¬ P i} => K j) ⟨i, hi⟩)
    · intro i hi
      apply (hgK i).mono
      intro x hx
      have hxS : x ∈ U ∩ s := by simpa [S, hi] using hKS i hx
      refine ⟨hxS.1, ?_⟩
      intro hxT
      rcases mem_iUnion.mp hxT with ⟨j, hxj⟩
      have hxSc : x ∈ U ∩ sᶜ := by simpa [S, j.property] using hKS j hxj
      exact hxSc.2 hxS.2
  · intro i
    by_cases hi : P i
    · simp only [S, hi, ite_true]
      filter_upwards [hf i, hin i hi] with x h₁ h₂
      intro hx
      by_cases hxU : x ∈ U
      · exact h₂ (fun hxs => hx ⟨hxU, hxs⟩)
      · exact h₁ hxU
    · simp only [S, hi, ite_false]
      filter_upwards [hf i, hout i hi] with x h₁ h₂
      intro hx
      by_cases hxU : x ∈ U
      · exact h₂ (fun hxs => hx ⟨hxU, hxs⟩)
      · exact h₁ hxU

end NoContact
