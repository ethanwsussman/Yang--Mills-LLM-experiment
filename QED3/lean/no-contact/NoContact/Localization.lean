module

public import NoContact.Separation

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace NoContact

/-- If one entry is supported in `s`, cutting all entries to `s` preserves the form. -/
theorem localize {ι : Type} [Fintype ι] {U s : Set X} (D : Form ι)
    (hD : SplitZero U D) (hs : MeasurableSet s) (f : ι → L2)
    (hf : ∀ i, Supported U (f i)) (i : ι) (hi : Supported s (f i)) :
    D f = D (fun j => cut s hs (f j)) := by
  classical
  let a : ι → L2 := fun j => cut s hs (f j)
  let b : ι → L2 := fun j => cut sᶜ hs.compl (f j)
  have hab : a + b = f := by
    funext j
    exact cut_add_compl s hs (f j)
  rw [← hab, D.map_add_univ]
  change (∑ t : Finset ι, D (t.piecewise a b)) = D (fun j => cut s hs ((a + b) j))
  have hrhs : (fun j => cut s hs ((a + b) j)) = a := by
    rw [hab]
  rw [hrhs]
  calc
    (∑ t : Finset ι, D (t.piecewise a b)) = D ((Finset.univ : Finset ι).piecewise a b) := by
      apply Fintype.sum_eq_single
      intro t ht
      by_cases he : t = ∅
      · subst t
        simp only [Finset.piecewise_empty]
        apply D.map_coord_zero i
        exact cut_zero_of_disjoint hs.compl disjoint_compl_left hi
      · apply hD s hs (fun j => j ∈ t) (t.piecewise a b)
        · exact Finset.nonempty_iff_ne_empty.mpr he
        · by_contra h
          apply ht
          apply Finset.eq_univ_of_forall
          intro j
          by_contra hj
          exact h ⟨j, hj⟩
        · intro j
          by_cases hj : j ∈ t
          · simpa [Finset.piecewise, hj, a] using
              (cut_supported_inter hs (hf j)).mono inter_subset_right
          · simpa [Finset.piecewise, hj, b] using
              (cut_supported_inter hs.compl (hf j)).mono inter_subset_right
        · intro j hj
          simpa [Finset.piecewise, hj, a] using cut_supported s hs (f j)
        · intro j hj
          simpa [Finset.piecewise, hj, b] using cut_supported sᶜ hs.compl (f j)
    _ = D a := by simp

/-- Constant-vector indicators depend complex-linearly on the vector. -/
def compactIndicatorLinear (K : Set X) (hK : IsCompact K) : E →ₗ[ℂ] L2 where
  toFun := compactIndicator K hK
  map_add' c d := (indicatorConstLp_add (p := 2)).symm
  map_smul' c d := by
    apply Lp.ext
    filter_upwards [compactIndicator_ae K hK (c • d), compactIndicator_ae K hK d,
      Lp.coeFn_smul c (compactIndicator K hK d)] with x h₁ h₂ h₃
    by_cases hx : x ∈ K <;> simp_all

/-- A coordinate indicator in one slot forces zero. A cutoff potential
supplies that coordinate on the compact set; indicator localization moves
the cutoff to another slot before using the gradient hypothesis. -/
theorem coordinate_indicator_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι) {U : Set X} (hU : IsOpen U)
    (D : Form ι) (hsplit : SplitZero U D) (hgrad : GradientZero U D)
    (f : ι → L2) (hf : ∀ j, Supported U (f j)) (i : ι)
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) (k : Fin 3) :
    D (update f i (compactIndicator K hK (EuclideanSpace.single k 1))) = 0 := by
  classical
  obtain ⟨u, hu⟩ := exists_coordinate_potential hU hK hKU k
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  let c : L2 := compactIndicator K hK (EuclideanSpace.single k 1)
  let v : ι → L2 := update f i c
  let w : ι → L2 := update (fun j => cut K hK.measurableSet (f j)) i u.gradientLp
  have hc : Supported K c := compactIndicator_supported K hK _
  have hvU : ∀ l, Supported U (v l) := by
    intro l
    by_cases hl : l = i
    · subst l
      simpa [v] using hc.mono hKU
    · simpa [v, hl] using hf l
  have hwU : ∀ l, Supported U (w l) := by
    intro l
    by_cases hl : l = i
    · subst l
      simpa [w] using u.gradientLp_supported
    · simpa [w, hl] using (cut_supported K hK.measurableSet (f l)).mono hKU
  have hvK : Supported K (v i) := by simpa [v] using hc
  have hwK : Supported K (w j) := by
    simpa [w, hji] using cut_supported K hK.measurableSet (f j)
  have hv := localize D hsplit hK.measurableSet v hvU i hvK
  have hw := localize D hsplit hK.measurableSet w hwU j hwK
  have heq : (fun l => cut K hK.measurableSet (v l)) =
      (fun l => cut K hK.measurableSet (w l)) := by
    funext l
    by_cases hl : l = i
    · subst l
      simp only [v, w, update_self]
      rw [cut_eq_self hK.measurableSet hc,
        cut_gradient_eq_compactIndicator hK u _ hu]
    · simp only [v, w, update_of_ne hl]
      rw [cut_eq_self hK.measurableSet (cut_supported K hK.measurableSet (f l))]
  calc
    D (update f i c) = D (fun l => cut K hK.measurableSet (v l)) := hv
    _ = D (fun l => cut K hK.measurableSet (w l)) := congrArg D heq
    _ = D w := hw.symm
    _ = 0 := hgrad i u w hwU (by simp [w])

/-- Coordinate indicators and density give vanishing on all supported fields. -/
theorem zero_of_splitZero {ι : Type} [Fintype ι]
    (hcard : 1 < Fintype.card ι) {U : Set X} (hU : IsOpen U)
    (D : Form ι) (hsplit : SplitZero U D) (hgrad : GradientZero U D)
    (f : ι → L2) (hf : ∀ j, Supported U (f j)) : D f = 0 := by
  classical
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  let L : L2 →L[ℂ] ℂ := D.toContinuousLinearMap f i
  have hcompact : ∀ K, ∀ hK : IsCompact K, K ⊆ U → ∀ c,
      compactIndicator K hK c ∈ L.ker := by
    intro K hK hKU c
    let T : E →ₗ[ℂ] ℂ := L.toLinearMap.comp (compactIndicatorLinear K hK)
    have hT : ∀ k : Fin 3, T (EuclideanSpace.single k 1) = 0 := by
      intro k
      exact coordinate_indicator_zero hcard hU D hsplit hgrad f hf i K hK hKU k
    have hc : c = ∑ k : Fin 3, c k • EuclideanSpace.single k (1 : ℂ) := by
      ext k
      simp [Pi.single_apply]
    change T c = 0
    rw [hc, map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_smul, hT k, smul_zero]
  have hz := supported_mem_of_compactIndicators U hU.measurableSet L.ker L.isClosed_ker
    hcompact (hf i)
  change D (update f i (f i)) = 0 at hz
  simpa using hz

end NoContact
