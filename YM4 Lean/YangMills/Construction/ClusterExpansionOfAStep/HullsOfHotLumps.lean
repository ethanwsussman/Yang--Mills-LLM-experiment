import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
section MinimalHull
variable (P : StepParameters) {n : ℕ} [NeZero n]
open Classical in
def hotLumpsIn (U : TorusField n) (X : Finset (TorusSite n)) : Finset (Finset (TorusSite n)) :=
  (torusHotLumps P U).filter (· ⊆ X)
def lumpCore (U : TorusField n) (X : Finset (TorusSite n)) : Finset (TorusSite n) :=
  (hotLumpsIn P U X).biUnion id
open Classical in
def nearPlaquettes (U : TorusField n) (X : Finset (TorusSite n)) : Finset (TorusPlaquette n) :=
  (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter fun p =>
    ∃ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ thickening lumpRange (lumpCore P U X)
def componentEnergy (U : TorusField n) (X : Finset (TorusSite n)) : ℝ :=
  ∑ p ∈ nearPlaquettes P U X, plaquetteEnergy U p.1 p.2.1 p.2.2
def minimalHull (r : ℕ) (U : TorusField n) : Finset (TorusSite n) :=
  thickening (2 * r) (torusHotSites P U)
variable {P} {r : ℕ} {U : TorusField n} {Y : Finset (TorusSite n)}
theorem supDist_lt_of_mem_torusHotLumps (hP : P.Admissible) (hdvd : P.side ∣ n)
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps P U)
    {x x' : TorusSite n} (hx : x ∈ l) (hx' : x' ∈ l) : supDist x x' < 2 ^ 15 := by
  classical
  obtain ⟨_, _, _, _, _, z, _, rfl⟩ := (mem_torusHotLumps_iff P hP hdvd U l).mp hl
  have h1 := (Finset.mem_filter.mp hx).2
  have h2 := (Finset.mem_filter.mp hx').2
  exact supDist_lt_of_lumpCorner_eq hP hdvd (h2.trans h1.symm)
omit [NeZero n] in
theorem mem_torusHotSites_iff {z : TorusSite n} :
    z ∈ torusHotSites P U ↔ ∃ l ∈ torusHotLumps P U, z ∈ l := by
  simp [torusHotSites]
omit [NeZero n] in
theorem mem_lumpCore {X : Finset (TorusSite n)} {z : TorusSite n} :
    z ∈ lumpCore P U X ↔ ∃ l ∈ torusHotLumps P U, l ⊆ X ∧ z ∈ l := by
  classical
  simp only [lumpCore, hotLumpsIn, Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, h3⟩
    exact ⟨l, h1, h2, h3⟩
  · rintro ⟨l, h1, h2, h3⟩
    exact ⟨l, ⟨h1, h2⟩, h3⟩
theorem chainConnected_of_supDist_le_two_mul (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y)
    {x z : TorusSite n} (hx : x ∈ torusHotSites P U) (hz : supDist z x ≤ 2 * r) :
    ChainConnected r Y x z := by
  obtain ⟨v, h1, h2⟩ := exists_midpoint x z r (by rw [supDist_comm]; exact hz)
  have hxY : x ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩)
  have hvY : v ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_comm]; omega⟩)
  have hzY : z ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, hz⟩)
  exact (chainConnected_of_supDist_le hxY hvY h1).trans (chainConnected_of_supDist_le hvY hzY h2)
theorem thickening_subset_of_mem_chainComponents (hP : P.Admissible) (hdvd : P.side ∣ n)
    (hr : 2 ^ 16 ≤ r) (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y)
    {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y)
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps P U) {x : TorusSite n} (hxl : x ∈ l)
    (hxX : x ∈ X) : thickening (2 * r) l ⊆ X := by
  intro z hz
  obtain ⟨x', hx', hzx'⟩ := (mem_thickening _ _ _).mp hz
  have hs : ∀ {u : TorusSite n}, u ∈ l → u ∈ torusHotSites P U := fun hu =>
    mem_torusHotSites_iff.mpr ⟨l, hl, hu⟩
  have hxY : x ∈ Y := subset_of_mem_chainComponents hX hxX
  have hx'Y : x' ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x', hs hx', by rw [supDist_self]; omega⟩)
  have hzY : z ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x', hs hx', hzx'⟩)
  have h1 : ChainConnected r Y x x' := chainConnected_of_supDist_le hxY hx'Y
    (by have := supDist_lt_of_mem_torusHotLumps hP hdvd hl hxl hx'; omega)
  exact mem_of_chainConnected_of_mem_chainComponents hX hxX hzY
    (h1.trans (chainConnected_of_supDist_le_two_mul hsub (hs hx') hzx'))
theorem subset_thickening_self (l : Finset (TorusSite n)) (m : ℕ) : l ⊆ thickening m l :=
  fun x hx => (mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩
theorem subset_of_mem_torusHotLumps_of_mem (hP : P.Admissible) (hdvd : P.side ∣ n)
    (hr : 2 ^ 16 ≤ r) (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y)
    {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y)
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps P U) {x : TorusSite n} (hxl : x ∈ l)
    (hxX : x ∈ X) : l ⊆ X :=
  (subset_thickening_self l _).trans
    (thickening_subset_of_mem_chainComponents hP hdvd hr hsub hX hl hxl hxX)
theorem minimalHull_isHullState : IsHullState P r U (minimalHull P r U) := by
  classical
  refine ⟨subset_rfl, fun X hX => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
  obtain ⟨x, hx, hyx⟩ := (mem_thickening _ _ _).mp hy
  obtain ⟨l, hl, hxl⟩ := mem_torusHotSites_iff.mp hx
  have hxY : x ∈ minimalHull P r U :=
    (mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩
  have hj : ChainConnected r (minimalHull P r U) y x :=
    chainConnected_symm (chainConnected_of_supDist_le_two_mul subset_rfl hx hyx)
  exact ⟨l, hl, x, Finset.mem_inter.mpr ⟨hxl, Finset.mem_filter.mpr ⟨hxY, hj⟩⟩⟩
theorem eq_thickening_lumpCore_of_mem_chainComponents (hP : P.Admissible) (hdvd : P.side ∣ n)
    (hr : 2 ^ 16 ≤ r) {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r (minimalHull P r U)) :
    X = thickening (2 * r) (lumpCore P U X) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp (subset_of_mem_chainComponents hX hz)
    obtain ⟨l, hl, hxl⟩ := mem_torusHotSites_iff.mp hx
    have hxY : x ∈ minimalHull P r U :=
      (mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩
    have hxX : x ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hz hxY
      (chainConnected_symm (chainConnected_of_supDist_le_two_mul subset_rfl hx hzx))
    exact (mem_thickening _ _ _).mpr ⟨x, mem_lumpCore.mpr
      ⟨l, hl, subset_of_mem_torusHotLumps_of_mem hP hdvd hr subset_rfl hX hl hxl hxX, hxl⟩, hzx⟩
  · intro hz
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
    obtain ⟨l, hl, hlX, hxl⟩ := mem_lumpCore.mp hx
    exact thickening_subset_of_mem_chainComponents hP hdvd hr subset_rfl hX hl hxl (hlX hxl)
      ((mem_thickening _ _ _).mpr ⟨x, hxl, hzx⟩)
omit [NeZero n] in
theorem lumpCore_subset_torusHotSites (X : Finset (TorusSite n)) :
    lumpCore P U X ⊆ torusHotSites P U := by
  intro z hz
  obtain ⟨l, hl, _, hzl⟩ := mem_lumpCore.mp hz
  exact mem_torusHotSites_iff.mpr ⟨l, hl, hzl⟩
theorem eq_minimalHull_of_forall_eq_thickening (hY : IsHullState P r U Y)
    (h : ∀ X ∈ chainComponents r Y, X = thickening (2 * r) (lumpCore P U X)) :
    Y = minimalHull P r U := by
  refine Finset.Subset.antisymm (fun y hy => ?_) hY.1
  obtain ⟨X, hX, hyX⟩ := exists_mem_chainComponents (r := r) hy
  rw [h X hX] at hyX
  obtain ⟨x, hx, hyx⟩ := (mem_thickening _ _ _).mp hyX
  exact (mem_thickening _ _ _).mpr ⟨x, lumpCore_subset_torusHotSites X hx, hyx⟩
theorem supDist_le_four_of_mem_plaquetteVertices (p : TorusPlaquette n) {z z' : TorusSite n}
    (hz : z ∈ plaquetteVertices p.1 p.2.1 p.2.2) (hz' : z' ∈ plaquetteVertices p.1 p.2.1 p.2.2) :
    supDist z z' ≤ 4 := by
  obtain ⟨x, μ, ν⟩ := p
  have key : ∀ w ∈ plaquetteVertices x μ ν, supDist x w ≤ 2 := by
    intro w hw
    have a := supDist_add_unitStep_le (n := n) x μ
    have b := supDist_add_unitStep_le (n := n) x ν
    have c := supDist_add_unitStep_le (n := n) (x + TorusFields.unitStep n μ) ν
    have s1 := supDist_triangle x (x + TorusFields.unitStep n μ)
      (x + TorusFields.unitStep n μ + TorusFields.unitStep n ν)
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [supDist_self]; omega
    · omega
    · omega
    · omega
  have h1 := key z hz
  have h2 := key z' hz'
  have := supDist_triangle z x z'
  rw [supDist_comm z x] at this
  omega
theorem eq_of_mem_nearPlaquettes (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y)
    (hr : 2 ^ 16 ≤ r) {X X' : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y)
    (hX' : X' ∈ chainComponents r Y) {p : TorusPlaquette n}
    (hp : p ∈ nearPlaquettes P U X) (hp' : p ∈ nearPlaquettes P U X') : X = X' := by
  classical
  obtain ⟨-, z, hzc, hz⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, z', hzc', hz'⟩ := Finset.mem_filter.mp hp'
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨x', hx', hzx'⟩ := (mem_thickening _ _ _).mp hz'
  obtain ⟨l, hl, hlX, hxl⟩ := mem_lumpCore.mp hx
  obtain ⟨l', hl', hlX', hxl'⟩ := mem_lumpCore.mp hx'
  have hd : supDist x x' ≤ r := by
    have h1 := supDist_triangle x z x'
    have h2 := supDist_triangle z z' x'
    have h3 := supDist_le_four_of_mem_plaquetteVertices p hzc hzc'
    rw [supDist_comm x z] at h1
    have hw : lumpRange = 2 ^ 12 := rfl
    rw [hw] at hzx hzx'
    omega
  exact eq_of_chainConnected_of_mem_chainComponents hX hX' (hlX hxl) (hlX' hxl')
    (chainConnected_of_supDist_le (subset_of_mem_chainComponents hX (hlX hxl))
      (subset_of_mem_chainComponents hX' (hlX' hxl')) hd)
theorem mem_plaquettesIn_iff_forall_vertex {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by
  classical
  simp [plaquettesIn]
theorem exists_mem_nearPlaquettes (hP : P.Admissible) (hdvd : P.side ∣ n) (hr : 2 ^ 16 ≤ r)
    (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y) {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) {z : TorusSite n}
    (hzc : z ∈ plaquetteVertices p.1 p.2.1 p.2.2)
    (hz : z ∈ thickening lumpRange (torusHotSites P U)) :
    ∃ X ∈ chainComponents r Y, p ∈ nearPlaquettes P U X := by
  classical
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨l, hl, hxl⟩ := mem_torusHotSites_iff.mp hx
  have hxY : x ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩)
  obtain ⟨X, hX, hxX⟩ := exists_mem_chainComponents (r := r) hxY
  refine ⟨X, hX, Finset.mem_filter.mpr ⟨hp, z, hzc, (mem_thickening _ _ _).mpr ⟨x, ?_, hzx⟩⟩⟩
  exact mem_lumpCore.mpr ⟨l, hl, subset_of_mem_torusHotLumps_of_mem hP hdvd hr hsub hX hl hxl hxX, hxl⟩
theorem exists_vertex_mem_thickening_of_mem_nearPlaquettes {X : Finset (TorusSite n)}
    {p : TorusPlaquette n} (hp : p ∈ nearPlaquettes P U X) :
    ∃ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ thickening lumpRange (torusHotSites P U) := by
  classical
  obtain ⟨-, z, hzc, hz⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
  exact ⟨z, hzc, (mem_thickening _ _ _).mpr ⟨x, lumpCore_subset_torusHotSites X hx, hzx⟩⟩
theorem wilsonAction_univ_eq_add_sum_componentEnergy (hP : P.Admissible) (hdvd : P.side ∣ n)
    (hr : 2 ^ 16 ≤ r) (hsub : thickening (2 * r) (torusHotSites P U) ⊆ Y) :
    wilsonAction Finset.univ U =
      wilsonAction (Finset.univ \ thickening lumpRange (torusHotSites P U)) U +
        ∑ X ∈ chainComponents r Y, componentEnergy P U X := by
  classical
  have hu : plaquettesIn (Finset.univ : Finset (TorusSite n)) =
      plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites P U)) ∪
        (chainComponents r Y).biUnion (nearPlaquettes P U) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_biUnion, mem_plaquettesIn_iff_forall_vertex,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, -⟩
      by_cases h : ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2,
          z ∉ thickening lumpRange (torusHotSites P U)
      · exact Or.inl ⟨h1, h⟩
      · push Not at h
        obtain ⟨z, hzc, hz⟩ := h
        exact Or.inr (exists_mem_nearPlaquettes hP hdvd hr hsub
          (mem_plaquettesIn_iff_forall_vertex.mpr ⟨h1, fun _ _ => Finset.mem_univ _⟩) hzc hz)
    · rintro (⟨h1, -⟩ | ⟨X, -, hp⟩)
      · exact ⟨h1, fun _ _ => trivial⟩
      · exact ⟨(mem_plaquettesIn_iff_forall_vertex.mp (Finset.mem_filter.mp hp).1).1,
          fun _ _ => trivial⟩
  have hdis : Disjoint (plaquettesIn (Finset.univ \ thickening lumpRange (torusHotSites P U)))
      ((chainComponents r Y).biUnion (nearPlaquettes P U)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨X, -, hpX⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨z, hzc, hz⟩ := exists_vertex_mem_thickening_of_mem_nearPlaquettes hpX
    exact (Finset.mem_sdiff.mp ((mem_plaquettesIn_iff_forall_vertex.mp hp).2 z hzc)).2 hz
  have hpair : (↑(chainComponents r Y) : Set (Finset (TorusSite n))).PairwiseDisjoint
      (nearPlaquettes P U) := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun p hp hp' => hne (eq_of_mem_nearPlaquettes hsub hr hX hX' hp hp')
  unfold TorusFields.wilsonAction
  rw [hu, Finset.sum_union hdis, Finset.sum_biUnion hpair]
  rfl
end MinimalHull
end YangMills.Construction.TorusLumps
end
