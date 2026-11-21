import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.OpenSetsAndBallsOfSeveralPoints
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.TupleTopology
open Kind
variable {p : ℕ+}
noncomputable def euclidDist (x y : Coords p) : ℝ :=
  Real.sqrt (∑ i, (x - y) i ^ 2)
theorem abs_sub_apply_le_euclidDist (x y : Coords p) (i : Fin (4 * (p : ℕ))) :
    |x i - y i| ≤ euclidDist x y := by
  apply Real.abs_le_sqrt
  have hi : (x i - y i) ^ 2 = (x - y) i ^ 2 := by simp
  rw [hi]
  exact Finset.single_le_sum (f := fun i => (x - y) i ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ i)
theorem dist_le_euclidDist (x y : Coords p) : dist x y ≤ euclidDist x y := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.dist_eq]
  exact abs_sub_apply_le_euclidDist x y i
theorem continuous_euclidDist (x : Coords p) :
    Continuous fun y : Coords p => euclidDist x y := by
  unfold euclidDist
  simp only [Pi.sub_apply]
  fun_prop
theorem isOpen_of_forall_euclidBall (V : Set (Coords p))
    (h : ∀ x ∈ V, ∃ r : ℝ, 0 < r ∧ ∀ y, euclidDist x y < r → y ∈ V) : IsOpen V := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨r, hr, hV⟩ := h x hx
  have ho : IsOpen {y | euclidDist x y < r} :=
    isOpen_lt (continuous_euclidDist x) continuous_const
  have hself : x ∈ {y | euclidDist x y < r} := by
    simpa [euclidDist] using hr
  exact Filter.mem_of_superset (ho.mem_nhds hself) fun y hy => hV y hy
theorem exists_euclidBall_subset_of_isOpen {U : Set (Coords p)} (hU : IsOpen U) {x : Coords p}
    (hx : x ∈ U) : ∃ r : ℝ, 0 < r ∧ ∀ y, euclidDist x y < r → y ∈ U := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, fun y h => hb ?_⟩
  rw [Metric.mem_ball, dist_comm]
  exact (dist_le_euclidDist x y).trans_lt h
theorem isCompact_euclidClosedBall (x : Coords p) (r : ℝ) :
    IsCompact {y | euclidDist x y ≤ r} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_euclidDist x) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := x) (r := r)).subset fun y h => ?_
  rw [Metric.mem_closedBall, dist_comm]
  exact (dist_le_euclidDist x y).trans h
theorem quotientOpenAndBalls_of_distanceAndLifts
    (lifts : TupleMetric.QuotientDistanceAndLifts) : QuotientOpenAndBalls := by
  intro D E p
  obtain ⟨⟨onto, -⟩, least, ⟨-, -, symm, tri⟩, nearest, -⟩ := lifts D E p
  have shrink : ∀ x y : Coords p,
      Tuple.tupleDist D E (Tuple.proj D E x) (Tuple.proj D E y) ≤ euclidDist x y :=
    fun x y => (least x y).2
  have nearer : ∀ (x : Coords p) (z : E.Tuple D p), ∃ y : Coords p,
      Tuple.proj D E y = z ∧ euclidDist x y = Tuple.tupleDist D E (Tuple.proj D E x) z :=
    nearest
  have images : ∀ U : Set (Coords p), IsOpen U →
      Tuple.IsOpenT D E (Tuple.proj D E '' U) := by
    intro U hU z hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨r, hr, hball⟩ := exists_euclidBall_subset_of_isOpen hU hx
    refine ⟨r, hr, fun z' hz' => ?_⟩
    obtain ⟨y, hlift, hy⟩ := nearer x z'
    exact ⟨y, hball y (by rw [hy]; exact hz'), hlift⟩
  have reads : ∀ Ω : Set (E.Tuple D p),
      Tuple.IsOpenT D E Ω ↔ IsOpen (Tuple.proj D E ⁻¹' Ω) := by
    intro Ω
    constructor
    · intro hΩ
      refine isOpen_of_forall_euclidBall _ fun x hx => ?_
      obtain ⟨r, hr, hball⟩ := hΩ _ hx
      exact ⟨r, hr, fun y hy => hball _ ((shrink x y).trans_lt hy)⟩
    · intro hΩ
      have himage := images _ hΩ
      rwa [Set.image_preimage_eq Ω onto] at himage
  refine ⟨?_, images, reads, ?_, ?_⟩
  · intro x ε hε
    exact ⟨ε, hε, fun y h => (shrink x y).trans_lt h⟩
  · intro F
    constructor
    · intro hF
      refine continuous_def.2 fun V hV => isOpen_of_forall_euclidBall _ fun x hx => ?_
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ hx
      obtain ⟨δ, hδ, hnear⟩ := hF (Tuple.proj D E x) ε hε
      refine ⟨δ, hδ, fun y hy => hball ?_⟩
      rw [Metric.mem_ball, dist_comm]
      exact hnear _ ((shrink x y).trans_lt hy)
    · intro hF z ε hε
      have hopen : Tuple.IsOpenT D E (F ⁻¹' Metric.ball (F z) ε) :=
        (reads _).2 (Metric.isOpen_ball.preimage hF)
      obtain ⟨δ, hδ, hball⟩ := hopen z (Metric.mem_ball_self hε)
      refine ⟨δ, hδ, fun z' hz' => ?_⟩
      have hin : dist (F z') (F z) < ε := hball z' hz'
      rwa [dist_comm] at hin
  · intro z r hr
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have hu' : Tuple.tupleDist D E u z < r := hu
      refine ⟨r - Tuple.tupleDist D E u z, sub_pos.2 hu', fun w hw => ?_⟩
      have h1 := symm w u
      have h2 := tri w u z
      show Tuple.tupleDist D E w z < r
      linarith
    · intro a ha b hb
      have ha' : Tuple.tupleDist D E a z < r := ha
      have hb' : Tuple.tupleDist D E b z < r := hb
      have h1 := symm z b
      have h2 := tri a z b
      linarith
    · obtain ⟨x, rfl⟩ := onto z
      intro cover hopen hcover
      have hcov : {y | euclidDist x y ≤ r} ⊆
          ⋃ U ∈ cover, Tuple.proj D E ⁻¹' U := by
        intro y hy
        have hle : Tuple.tupleDist D E (Tuple.proj D E y) (Tuple.proj D E x) ≤ r := by
          rw [symm]
          exact (shrink x y).trans hy
        obtain ⟨U, hU, hin⟩ := hcover hle
        exact Set.mem_biUnion hU hin
      obtain ⟨finer, hsub, hfin, hfiner⟩ := (isCompact_euclidClosedBall x r).elim_finite_subcover_image
        (fun U hU => (reads U).1 (hopen U hU)) hcov
      refine ⟨finer, hsub, hfin, fun u hu => ?_⟩
      have hu' : Tuple.tupleDist D E u (Tuple.proj D E x) ≤ r := hu
      obtain ⟨y, rfl, hy⟩ := nearer x u
      have hmem : y ∈ {y | euclidDist x y ≤ r} := by
        show euclidDist x y ≤ r
        rw [hy, symm]
        exact hu'
      obtain ⟨U, hU, hin⟩ := Set.mem_iUnion₂.1 (hfiner hmem)
      exact ⟨U, hU, hin⟩
end YangMills.Construction.PeriodicSpace.TupleTopology
