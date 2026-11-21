import YangMills.Construction.TorusOrFourSpace.ProductsAndProjectionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleProducts
open MetricNotions
section PiOfMetricSpace
variable {X : Type*} [MetricSpace X] {n : ℕ}
def piDist (y y' : Fin n → X) : ℝ := Real.sqrt (∑ i, dist (y i) (y' i) ^ 2)
theorem dist_le_piDist (y y' : Fin n → X) (i : Fin n) :
    dist (y i) (y' i) ≤ piDist y y' :=
  Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (f := fun j => dist (y j) (y' j) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i))
theorem isOpenWrt_of_isOpen {U : Set X} (h : IsOpen U) : IsOpenWrt dist U := by
  intro x hx
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 h x hx
  exact ⟨ε, hε, fun y hy => hb (by rwa [Metric.mem_ball, dist_comm])⟩
theorem isCompact_of_isCompactWrt {Z : Set X} (hZ : IsCompactWrt dist Z) : IsCompact Z := by
  refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
  obtain ⟨𝒰, hsub, hfin, hcov'⟩ := hZ (Set.range U)
    (by rintro _ ⟨i, rfl⟩; exact isOpenWrt_of_isOpen (hU i)) (by rwa [Set.sUnion_range])
  obtain ⟨t, -, ht, hc⟩ :=
    (Set.exists_subset_image_finite_and (f := U) (s := Set.univ)
      (p := fun 𝒲 => Z ⊆ ⋃₀ 𝒲)).1 ⟨𝒰, by simpa using hsub, hfin, hcov'⟩
  refine ⟨ht.toFinset, fun z hz => ?_⟩
  obtain ⟨_, ⟨i, hi, rfl⟩, hzi⟩ := hc hz
  exact Set.mem_biUnion (by simpa using hi) hzi
theorem isOpen_of_isOpenWrt_piDist {U : Set (Fin n → X)}
    (hU : IsOpenWrt piDist U) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨r, hr, h⟩ := hU y hy
  have hc : Continuous fun y' : Fin n → X => piDist y y' :=
    Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => (continuous_const.dist (continuous_apply i)).pow 2)
  have h0 : piDist y y = 0 := by simp [piDist]
  have hn : {y' | piDist y y' < r} ∈ nhds y :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa [h0] using hr)
  exact Filter.mem_of_superset hn fun y' hy' => h y' hy'
theorem isOpenWrt_pi [Nonempty (Fin n)] (Ω : Fin n → Set X)
    (h : ∀ i, IsOpenWrt dist (Ω i)) : IsOpenWrt piDist {y | ∀ i, y i ∈ Ω i} := by
  intro y hy
  choose r hr hb using fun i => h i (y i) (hy i)
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min r
  exact ⟨r i₀, hr i₀, fun y' hy' i => hb i (y' i)
    (lt_of_le_of_lt (dist_le_piDist y y' i) (lt_of_lt_of_le hy' (hi₀ i)))⟩
theorem isClosedWrt_pi (Ω : Fin n → Set X) (h : ∀ i, IsClosedWrt dist (Ω i)) :
    IsClosedWrt piDist {y | ∀ i, y i ∈ Ω i} := by
  intro y hy
  have hex : ∃ i, y i ∉ Ω i := by simpa using hy
  obtain ⟨i, hi⟩ := hex
  obtain ⟨r, hr, hb⟩ := h i (y i) hi
  exact ⟨r, hr, fun y' hy' hmem =>
    hb (y' i) (lt_of_le_of_lt (dist_le_piDist y y' i) hy') (hmem i)⟩
theorem isCompactWrt_pi (Ω : Fin n → Set X) (h : ∀ i, IsCompactWrt dist (Ω i)) :
    IsCompactWrt piDist {y | ∀ i, y i ∈ Ω i} := by
  intro 𝒰 hopen hcov
  have hK : IsCompact (Set.pi Set.univ Ω) :=
    isCompact_univ_pi fun i => isCompact_of_isCompactWrt (h i)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun U : 𝒰 => (U : Set (Fin n → X)))
    (fun U => isOpen_of_isOpenWrt_piDist (hopen U U.2)) (by
      intro y hy
      obtain ⟨U, hU, hyU⟩ :=
        hcov (show y ∈ {y : Fin n → X | ∀ i, y i ∈ Ω i} from fun i => hy i (Set.mem_univ i))
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hyU⟩)
  refine ⟨(fun U : 𝒰 => (U : Set (Fin n → X))) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
  · rintro _ ⟨U, -, rfl⟩
    exact U.2
  · intro y hy
    have hmem := ht (show y ∈ Set.pi Set.univ Ω from fun i _ => hy i)
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨U, hU, hyU⟩ := hmem
    exact ⟨U, ⟨U, hU, rfl⟩, hyU⟩
theorem isCompactWrt_image_eval (i : Fin n) (K : Set (Fin n → X))
    (hK : IsCompactWrt piDist K) :
    IsCompactWrt dist ((fun y : Fin n → X => y i) '' K) := by
  intro 𝒰 hopen hcov
  obtain ⟨𝒱, hsub, hfin, hc⟩ := hK ((fun U : Set X => (fun y : Fin n → X => y i) ⁻¹' U) '' 𝒰)
    (by
      rintro _ ⟨U, hU, rfl⟩ y hy
      obtain ⟨r, hr, h⟩ := hopen U hU (y i) hy
      exact ⟨r, hr, fun y' hy' => h _ (lt_of_le_of_lt (dist_le_piDist y y' i) hy')⟩)
    (by
      intro y hy
      obtain ⟨U, hU, hyU⟩ := hcov ⟨y, hy, rfl⟩
      exact ⟨_, ⟨U, hU, rfl⟩, hyU⟩)
  obtain ⟨𝒰', hs, hf, hc'⟩ :=
    (Set.exists_subset_image_finite_and
      (f := fun U : Set X => (fun y : Fin n → X => y i) ⁻¹' U) (s := 𝒰)
      (p := fun 𝒲 => K ⊆ ⋃₀ 𝒲)).1 ⟨𝒱, hsub, hfin, hc⟩
  refine ⟨𝒰', hs, hf, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU⟩ := hc' hy
  exact ⟨U, hU, hyU⟩
theorem isContinuousWrt_dist_eval (i i' : Fin n) :
    IsContinuousWrt piDist dist (fun y : Fin n → X => dist (y i) (y i')) := by
  intro x ε hε
  refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
  have h1 := dist_le_piDist x y i
  have h2 := dist_le_piDist x y i'
  have h3 := dist_dist_dist_le (x i) (x i') (y i) (y i')
  linarith
end PiOfMetricSpace
theorem statement_holds (hQuot : Kind.QuotientCompactC1.Claim) :
    Statement := by
  intro P K p
  obtain ⟨-, hz, hs, ht, -⟩ := (hQuot P K).1
  let _ : MetricSpace (K.Pt P) :=
    { dist := Kind.quotDist P K
      dist_self := fun y => (hz y y).2 rfl
      dist_comm := hs
      dist_triangle := ht
      eq_of_dist_eq_zero := fun h => (hz _ _).1 h }
  have : Nonempty (Fin (p : ℕ)) := ⟨⟨0, p.pos⟩⟩
  exact ⟨fun Ω => ⟨isOpenWrt_pi Ω, isClosedWrt_pi Ω, isCompactWrt_pi Ω⟩,
    fun i => ⟨fun y y' => dist_le_piDist y y' i,
      fun L hL => isCompactWrt_image_eval i L hL⟩,
    fun i i' _ => isContinuousWrt_dist_eval i i'⟩
end YangMills.Construction.PeriodicSpace.TupleProducts
