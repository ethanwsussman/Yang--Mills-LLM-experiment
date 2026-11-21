import YangMills.Construction.Lattice.CubesVerticesAndEdgesOfThePartitionProof
import YangMills.Construction.Lattice.AdjacentCubesWithThreeCubesInEachDirectionProof
import YangMills.Construction.Lattice.MinimaThatSetTheSizesProof
import YangMills.Construction.Lattice.VerticesAndCornersOfCubesOfAPartition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeVertexCorners
open CubeLifts
def signVec (b : Fin 4 → Bool) : Fin 4 → ℝ := fun μ => if b μ then 1 else -1
theorem signVec_isSigns (b : Fin 4 → Bool) :
    LevelUnitPartition.IsSigns (signVec b) := by apply _root_.YangMills.Construction.TorusBound.PartitionCells.signVec_isSigns <;> assumption
theorem exists_signVec_eq {ε : Fin 4 → ℝ} (hε : LevelUnitPartition.IsSigns ε) :
    ∃ b, signVec b = ε := by
  refine ⟨fun μ => decide (ε μ = 1), ?_⟩
  funext μ
  rcases hε μ with h | h <;> norm_num [signVec, h]
theorem signVec_injective : Function.Injective signVec := by
  intro b b' h
  have key : ∀ x y : Bool,
      (if x then (1 : ℝ) else -1) = (if y then (1 : ℝ) else -1) → x = y := by
    intro x y hxy
    cases x <;> cases y <;> first | rfl | (exfalso; norm_num at hxy)
  funext μ
  exact key _ _ (congrFun h μ)
theorem card_bool_choices : Nat.card (Fin 4 → Bool) = 16 := by
  simp [Nat.card_eq_fintype_card]
variable {S : LevelUnitPartition}
theorem proj_eq_iff (x : S.Points) (w : Fin 4 → ℝ) :
    S.proj w = x ↔ S.IsPointLift x w := by apply _root_.YangMills.Construction.PeriodicLattice.ThreeWideNeighbours.proj_eq_iff_isPointLift <;> assumption
theorem exists_site_of_mem_cubes {Δ : Set S.Points} (h : Δ ∈ S.cubes) :
    ∃ y : Site S.params.L S.params.m S.index, cubeAround y = Δ := h
theorem cubeAround_mem_cubes (y : Site S.params.L S.params.m S.index) :
    cubeAround y ∈ S.cubes := ⟨y, rfl⟩
theorem isPeriodVector_of_proj_eq (hT : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (h : S.proj w = S.proj w') : IsPeriodVector S (w - w') := by apply _root_.YangMills.Construction.PeriodicLattice.MinimalTreeSizesProof.isPeriodVector_sub_of_proj_eq <;> assumption
theorem proj_eq_of_isPeriodVector (hT : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (h : IsPeriodVector S (w - w')) : S.proj w = S.proj w' := by
  obtain ⟨x, hx, hx'⟩ := (hT.2.2.2.2.2.2.2.1 w w').2 h
  rw [(proj_eq_iff _ _).2 hx, (proj_eq_iff _ _).2 hx']
theorem side_pos (hT : TorusInCubeUnits S) : (0 : ℝ) < (S.side : ℝ) := by
  exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
theorem exists_pointLift (hT : TorusInCubeUnits S)
    (y : Site S.params.L S.params.m S.index) :
    ∃ c, S.IsPointLift (y : S.Points) c :=
  hT.2.2.2.2.2.2.1 _
theorem signs_eq_of_isPeriodVector (hT : TorusInCubeUnits S) (hN : ShortVectorsNotPeriods S)
    {ε ε' r : Fin 4 → ℝ} (hε : LevelUnitPartition.IsSigns ε)
    (hε' : LevelUnitPartition.IsSigns ε')
    (hr : r = ((S.side : ℝ) / 2) • (ε - ε')) (hp : IsPeriodVector S r) : ε = ε' := by
  by_contra hne
  refine hN.1 r ?_ ?_ hp
  · intro h0
    apply hne
    funext μ
    have h1 := congrFun (hr.symm.trans h0) μ
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (half_pos (side_pos hT)).ne'
    linarith
  · intro μ
    subst hr
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases hε μ with h | h <;> rcases hε' μ with h' | h' <;> rw [h, h']
    · left; ring
    · right; left; ring
    · right; right; ring
    · left; ring
theorem corner_mem_closedBox (hV : VertexAndEdgeLifts S) {c ε : Fin 4 → ℝ}
    (hc : IsCubeCentre S c) (hε : LevelUnitPartition.IsSigns ε) :
    c + ((S.side : ℝ) / 2) • ε ∈ S.closedBox c :=
  ((hV.2.2.2.2.2 c hc).ge ⟨ε, hε, rfl⟩).1
theorem mem_of_isCornerOf (hC : SiteAndCubeLifts S) (hV : VertexAndEdgeLifts S)
    {v : S.Points} {Δ : Set S.Points} (h : S.IsCornerOf v Δ) : v ∈ Δ := by
  obtain ⟨y, rfl, c, hc, ε, hε, rfl⟩ := h
  rw [hC.2.1 y c hc]
  exact mem_image_of_mem _ (corner_mem_closedBox hV ((hC.1 c).1 ⟨y, hc⟩) hε)
theorem isCornerOf_of_mem (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) {v : S.Points} (hv : S.IsVertex v)
    {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes) (h : v ∈ Δ) : S.IsCornerOf v Δ := by
  obtain ⟨y, rfl⟩ := exists_site_of_mem_cubes hΔ
  obtain ⟨c, hc⟩ := exists_pointLift hT y
  have hcent : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
  rw [hC.2.1 y c hc] at h
  obtain ⟨x, hx, hxv⟩ := h
  have hxV : x ∈ S.vertexSet := hV.2.1 v x hv ((proj_eq_iff _ _).1 hxv)
  obtain ⟨ε, hε, rfl⟩ := (hV.2.2.2.2.2 c hcent).le ⟨hx, hxV⟩
  exact ⟨y, rfl, c, hc, ε, hε, hxv.symm⟩
theorem mem_region_iff (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) {X : Set S.Points} (hX : IsPartitionRegion S.index X)
    {v : S.Points} (hv : S.IsVertex v) :
    v ∈ X ↔ ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ := by
  obtain ⟨C, hCsub, rfl⟩ := hX
  constructor
  · rintro ⟨Δ, hΔ, hvΔ⟩
    exact ⟨Δ, ⟨hCsub hΔ, subset_sUnion_of_mem hΔ⟩, isCornerOf_of_mem hT hC hV hv (hCsub hΔ) hvΔ⟩
  · rintro ⟨Δ, ⟨-, hsub⟩, hcorner⟩
    exact hsub (mem_of_isCornerOf hC hV hcorner)
theorem cubesContaining_eq (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) :
    S.cubesContaining (S.proj w) =
      {Δ | ∃ ε, LevelUnitPartition.IsSigns ε ∧
        EdgeGraphCubeProperties.IsCubeCentredAt S Δ
          (S.proj (w - ((S.side : ℝ) / 2) • ε))} := by
  have hvert : S.IsVertex (S.proj w) := (hV.1 _).2 ⟨w, hw, rfl⟩
  ext Δ
  constructor
  · rintro ⟨hΔ, hwΔ⟩
    obtain ⟨y, rfl⟩ := exists_site_of_mem_cubes hΔ
    obtain ⟨c, hc⟩ := exists_pointLift hT y
    have hcent : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
    rw [hC.2.1 y c hc] at hwΔ
    obtain ⟨x, hx, hxw⟩ := hwΔ
    have hxV : x ∈ S.vertexSet := hV.2.1 _ x hvert ((proj_eq_iff _ _).1 hxw)
    obtain ⟨ε, hε, rfl⟩ := (hV.2.2.2.2.2 c hcent).le ⟨hx, hxV⟩
    refine ⟨ε, hε, y, ?_, rfl⟩
    have hp := isPeriodVector_of_proj_eq hT hxw.symm
    have hsame : S.proj (w - ((S.side : ℝ) / 2) • ε) = S.proj c := by
      apply proj_eq_of_isPeriodVector hT
      have hd : w - ((S.side : ℝ) / 2) • ε - c = w - (c + ((S.side : ℝ) / 2) • ε) := by
        abel
      rw [hd]
      exact hp
    rw [hsame]
    exact ((proj_eq_iff _ _).2 hc).symm
  · rintro ⟨ε, hε, y, hy, rfl⟩
    have hc := (proj_eq_iff _ _).1 hy.symm
    have hcent := (hC.1 _).1 ⟨y, hc⟩
    refine ⟨cubeAround_mem_cubes y, ?_⟩
    rw [hC.2.1 y _ hc]
    exact ⟨_, corner_mem_closedBox hV hcent hε, by rw [sub_add_cancel]⟩
theorem ncard_cubesContaining (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) (hN : ShortVectorsNotPeriods S) {v : S.Points}
    (hv : S.IsVertex v) : (S.cubesContaining v).ncard = 16 := by
  obtain ⟨w, hw, rfl⟩ := (hV.1 v).1 hv
  have hcent : ∀ b, IsCubeCentre S (w - ((S.side : ℝ) / 2) • signVec b) := by
    intro b μ
    obtain ⟨a, ha⟩ := hw μ
    by_cases hb : b μ
    · refine ⟨a, ?_⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, signVec, hb, if_true, ha]
      ring
    · refine ⟨a + 1, ?_⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, signVec, hb, ha]
      push_cast
      norm_num
      ring
  choose y hy using fun b => (hC.1 _).2 (hcent b)
  have hset : S.cubesContaining (S.proj w) = range (fun b => cubeAround (y b)) := by
    rw [cubesContaining_eq hT hC hV hw]
    ext Δ
    constructor
    · rintro ⟨ε, hε, y', hy', rfl⟩
      obtain ⟨b, rfl⟩ := exists_signVec_eq hε
      refine ⟨b, ?_⟩
      change cubeAround (y b) = cubeAround y'
      rw [hC.2.1 (y b) _ (hy b), hC.2.1 y' _ ((proj_eq_iff _ _).1 hy'.symm)]
    · rintro ⟨b, rfl⟩
      exact ⟨signVec b, signVec_isSigns b, y b, ((proj_eq_iff _ _).2 (hy b)).symm, rfl⟩
  have hinj : Function.Injective fun b => cubeAround (y b) := by
    intro b b' h
    have hyy : y b = y b' := by
      by_contra hne
      exact hC.2.2.1 _ _ hne h
    have hp : IsPeriodVector S ((w - ((S.side : ℝ) / 2) • signVec b) -
        (w - ((S.side : ℝ) / 2) • signVec b')) :=
      (hT.2.2.2.2.2.2.2.1 _ _).1 ⟨(y b : S.Points), hy b, by rw [hyy]; exact hy b'⟩
    refine signVec_injective (signs_eq_of_isPeriodVector hT hN (signVec_isSigns b')
      (signVec_isSigns b) ?_ hp).symm
    rw [smul_sub]
    abel
  rw [hset, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ, card_bool_choices]
theorem ncard_corners (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hN : ShortVectorsNotPeriods S) {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes) :
    {v | S.IsCornerOf v Δ}.ncard = 16 := by
  obtain ⟨y, rfl⟩ := exists_site_of_mem_cubes hΔ
  obtain ⟨c, hc⟩ := exists_pointLift hT y
  have hset : {v | S.IsCornerOf v (cubeAround y)} =
      range (fun b => S.proj (c + ((S.side : ℝ) / 2) • signVec b)) := by
    ext v
    constructor
    · rintro ⟨y', hyy, c', hc', ε, hε, rfl⟩
      have hy : y' = y := by
        by_contra hne
        exact hC.2.2.1 _ _ hne hyy.symm
      subst hy
      obtain ⟨b, rfl⟩ := exists_signVec_eq hε
      refine ⟨b, ?_⟩
      change S.proj (c + ((S.side : ℝ) / 2) • signVec b) =
        S.proj (c' + ((S.side : ℝ) / 2) • signVec b)
      apply proj_eq_of_isPeriodVector hT
      have hd : c + ((S.side : ℝ) / 2) • signVec b -
          (c' + ((S.side : ℝ) / 2) • signVec b) = c - c' := by abel
      rw [hd]
      exact (hT.2.2.2.2.2.2.2.1 _ _).1 ⟨_, hc, hc'⟩
    · rintro ⟨b, rfl⟩
      exact ⟨y, rfl, c, hc, signVec b, signVec_isSigns b, rfl⟩
  have hinj : Function.Injective
      fun b => S.proj (c + ((S.side : ℝ) / 2) • signVec b) := by
    intro b b' h
    refine signVec_injective (signs_eq_of_isPeriodVector hT hN (signVec_isSigns b)
      (signVec_isSigns b') ?_ (isPeriodVector_of_proj_eq hT h))
    rw [smul_sub]
    abel
  rw [hset, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ, card_bool_choices]
theorem partitionCubeVertexCornerIncidence_holds (hLifts : CubeLifts.Statement) :
    PartitionCubeVertexCornerIncidence := by
  intro S X hX
  obtain ⟨hT, -, hC, hV, -, hN⟩ := hLifts.2.2 S
  exact ⟨fun v hv Δ hΔ => ⟨isCornerOf_of_mem hT hC hV hv hΔ, mem_of_isCornerOf hC hV⟩,
    fun v hv => mem_region_iff hT hC hV hX hv,
    fun v hv => ncard_cubesContaining hT hC hV hN hv,
    fun w hw => cubesContaining_eq hT hC hV hw,
    fun Δ hΔ => ncard_corners hT hC hN hΔ⟩
end YangMills.Construction.PeriodicLattice.CubeVertexCorners
end
