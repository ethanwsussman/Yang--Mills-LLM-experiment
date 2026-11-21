import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPathsProof
import YangMills.Construction.Towers.ContourFamiliesAtTheSideInfinity
import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpace
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScalingOfStepSets
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem image_eq_of_forall_mem_iff {X Y : Type*} {f : X → Y} (hf : Function.Surjective f)
    {S : Set X} {T : Set Y} (h : ∀ x, x ∈ S ↔ f x ∈ T) : f '' S = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, (h x).2 hy, rfl⟩
section Steps
variable {a a' : ℝ}
theorem link_opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem opposite_forwardFrom (z : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom z μ).opposite =
      backwardLink (z + InfiniteLattice.axisStep a μ) μ :=
  InfiniteLattice.Link.ext rfl (by
    simp [InfiniteLattice.Link.opposite, InfiniteLattice.Link.forwardFrom, backwardLink])
theorem opposite_backwardLink (z : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (backwardLink z μ).opposite =
      InfiniteLattice.Link.forwardFrom (z - InfiniteLattice.axisStep a μ) μ :=
  InfiniteLattice.Link.ext rfl (by
    simp [InfiniteLattice.Link.opposite, InfiniteLattice.Link.forwardFrom, backwardLink])
theorem mem_forwardSteps {μ : Fin 4} {b : InfiniteLattice.Link a} (m : ℕ) :
    ∀ x : InfiniteLattice.LatticePoint a, b ∈ forwardSteps x μ m ↔
      ∃ t < m, b = InfiniteLattice.Link.forwardFrom (x + t • InfiniteLattice.axisStep a μ) μ := by
  induction m with
  | zero => intro x; simp [forwardSteps]
  | succ m ih =>
    intro x
    simp only [forwardSteps, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨t + 1, by omega, ?_⟩
        rw [succ_nsmul', add_assoc]
    · rintro ⟨t, ht, rfl⟩
      cases t with
      | zero => left; simp
      | succ t =>
        right
        refine ⟨t, by omega, ?_⟩
        rw [succ_nsmul', add_assoc]
theorem mem_backwardSteps {μ : Fin 4} {b : InfiniteLattice.Link a} (m : ℕ) :
    ∀ x : InfiniteLattice.LatticePoint a, b ∈ backwardSteps x μ m ↔
      ∃ t < m, b = backwardLink (x - t • InfiniteLattice.axisStep a μ) μ := by
  induction m with
  | zero => intro x; simp [backwardSteps]
  | succ m ih =>
    intro x
    simp only [backwardSteps, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨t + 1, by omega, ?_⟩
        rw [succ_nsmul', sub_sub]
    · rintro ⟨t, ht, rfl⟩
      cases t with
      | zero => left; simp
      | succ t =>
        right
        refine ⟨t, by omega, ?_⟩
        rw [succ_nsmul', sub_sub]
theorem opposite_mem_signedSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℤ}
    {b : InfiniteLattice.Link a} (hb : b ∈ signedSteps x μ n) :
    b.opposite ∈ signedSteps (x + n • InfiniteLattice.axisStep a μ) μ (-n) := by
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [signedSteps, Int.natCast_nonneg, if_true, Int.toNat_natCast] at hb
    obtain ⟨t, ht, rfl⟩ := (mem_forwardSteps m x).1 hb
    obtain ⟨d, rfl⟩ : ∃ d, m = t + 1 + d := ⟨m - 1 - t, by omega⟩
    have hneg : ¬ (0 : ℤ) ≤ -((t + 1 + d : ℕ) : ℤ) := by omega
    simp only [signedSteps, hneg, if_false, neg_neg, Int.toNat_natCast]
    refine (mem_backwardSteps _ _).2 ⟨d, by omega, ?_⟩
    rw [opposite_forwardFrom]
    congr 1
    rw [natCast_zsmul, add_nsmul, add_nsmul, one_nsmul]
    abel
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
    obtain rfl : n = -(m : ℤ) := by omega
    have hneg : ¬ (0 : ℤ) ≤ -(m : ℤ) := by omega
    simp only [signedSteps, hneg, if_false, neg_neg, Int.toNat_natCast] at hb
    obtain ⟨t, ht, rfl⟩ := (mem_backwardSteps m x).1 hb
    obtain ⟨d, rfl⟩ : ∃ d, m = t + 1 + d := ⟨m - 1 - t, by omega⟩
    simp only [signedSteps, neg_neg, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    refine (mem_forwardSteps _ _).2 ⟨d, by omega, ?_⟩
    rw [opposite_backwardLink]
    congr 1
    rw [neg_zsmul, natCast_zsmul, add_nsmul, add_nsmul, one_nsmul]
    abel
theorem coe_zsmul_axisStep (n : ℤ) (μ ν : Fin 4) :
    ((n • InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) ν =
      if ν = μ then (n : ℝ) * a else 0 := by
  by_cases h : ν = μ
  · subst h
    simp [InfiniteLattice.axisStep]
  · simp [InfiniteLattice.axisStep, h]
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4}
    {n : ℤ} (h : IsAxisDisplacement x x' μ n) : axisPath x x' = signedSteps x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  unfold axisPath
  rw [dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = q at hs ⊢
  obtain ⟨μ', n'⟩ := q
  have e : n • InfiniteLattice.axisStep a μ = n' • InfiniteLattice.axisStep a μ' := h.symm.trans hs
  have hc : ∀ ν, (if ν = μ then (n : ℝ) * a else 0) = if ν = μ' then (n' : ℝ) * a else 0 := by
    intro ν
    rw [← coe_zsmul_axisStep, ← coe_zsmul_axisStep, e]
  by_cases hn : n = 0
  · subst hn
    have h0 : n' = 0 := by
      by_contra hn'
      have := hc μ'
      simp only [if_true, Int.cast_zero, zero_mul, ite_self] at this
      exact mul_ne_zero (by exact_mod_cast hn') ha this.symm
    subst h0
    simp [signedSteps, forwardSteps]
  · have hna : (n : ℝ) * a ≠ 0 := mul_ne_zero (by exact_mod_cast hn) ha
    have hμ : μ = μ' := by
      by_contra hne
      have := hc μ
      simp only [if_true, hne, if_false] at this
      exact hna this
    subst hμ
    have := hc μ
    simp only [if_true] at this
    have hnn : (n' : ℝ) = n := (mul_right_cancel₀ ha this).symm
    have : n' = n := by exact_mod_cast hnn
    subst this
    rfl
theorem opposite_mem_axisPath (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a}
    {b : InfiniteLattice.Link a} (hb : b ∈ axisPath x x') :
    b.opposite ∈ axisPath x' x := by
  by_cases hex : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x x' q.1 q.2
  · obtain ⟨⟨μ, n⟩, h⟩ := hex
    have h' : IsAxisDisplacement x' x μ (-n) := by
      have h2 : x' - x = n • InfiniteLattice.axisStep a μ := h
      change x - x' = (-n) • InfiniteLattice.axisStep a μ
      rw [neg_zsmul, ← h2]
      abel
    rw [axisPath_eq_signedSteps ha h] at hb
    rw [axisPath_eq_signedSteps ha h']
    have hx : x' = x + n • InfiniteLattice.axisStep a μ := by
      have h2 : x' - x = n • InfiniteLattice.axisStep a μ := h
      rw [← h2]
      abel
    rw [hx]
    exact opposite_mem_signedSteps hb
  · unfold axisPath at hb
    rw [dif_neg hex] at hb
    simp at hb
variable {L : ℕ}
theorem isPivotLink_opposite (ha : a' ≠ 0) {c : InfiniteLattice.Link a}
    {b : InfiniteLattice.Link a'} (h : IsPivotLink L a' c b) :
    IsPivotLink L a' c.opposite b.opposite :=
  ⟨⟨h.1.2, h.1.1⟩, opposite_mem_axisPath ha h.2⟩
end Steps
theorem existsUnique_pivotLink {L k i : ℕ} (ha : meshAt L k i ≠ 0)
    (P : StepsEdgesAndCorridors L k (i + 1)) (c : FullSpace.Edge L k (i + 1)) :
    ∃! b : FullSpace.Edge L k i, IsPivotLink L (meshAt L k i) c b := by
  have hpos : ∀ (c' : FullSpace.Edge L k (i + 1)) (μ : Fin 4),
      c'.terminal - c'.initial = InfiniteLattice.axisStep (meshAt L k (i + 1)) μ →
        ∃! b : FullSpace.Edge L k i, IsPivotLink L (meshAt L k i) c' b := by
    intro c' μ h
    obtain ⟨b, hb, hu⟩ := P.existsUnique_corridorEdge c' μ h
    exact ⟨b, ⟨hb.2, hb.1⟩, fun b' hb' => hu b' ⟨hb'.2, hb'.1⟩⟩
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · exact hpos c μ h
  · have h' : c.opposite.terminal - c.opposite.initial =
        InfiniteLattice.axisStep (meshAt L k (i + 1)) μ := by
      change c.initial - c.terminal = _
      rw [← neg_sub, h, neg_neg]
    obtain ⟨b, hb, hu⟩ := hpos c.opposite μ h'
    refine ⟨b.opposite, ?_, fun b' hb' => ?_⟩
    · have := isPivotLink_opposite ha hb
      rwa [link_opposite_opposite] at this
    · have := hu b'.opposite (isPivotLink_opposite ha hb')
      rw [← this, link_opposite_opposite]
section Displays
theorem smul_sum_single (D a' : ℝ) (ν : Fin 4 → ℤ) :
    D • (∑ μ, Pi.single μ ((ν μ : ℝ) * a') : AmbientSpace) =
      ∑ μ, Pi.single μ ((ν μ : ℝ) * (D * a')) := by
  funext κ
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring
variable {L : ℕ} {a b : ℝ}
theorem mem_cubeOfOrder_iff_smul {D : ℝ} (hD : D ≠ 0) (a' : ℝ) (r : ℕ)
    {y : InfiniteLattice.LatticePoint a} {y' : InfiniteLattice.LatticePoint b}
    (hy : (y' : AmbientSpace) = D • (y : AmbientSpace)) (p : AmbientSpace) :
    p ∈ cubeOfOrder L a' r y ↔ D • p ∈ cubeOfOrder L (D * a') r y' := by
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, hν, by rw [smul_add, smul_sum_single, hy]⟩
  · rintro ⟨ν, hν, h⟩
    refine ⟨ν, hν, ?_⟩
    rw [hy, ← smul_sum_single, ← smul_add] at h
    exact smul_right_injective AmbientSpace hD h
end Displays
theorem meshAt_succ {L : ℕ} (hL : 0 < L) (k i : ℕ) :
    meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.meshAt_succ <;> assumption
theorem meshAt_ne_zero {L : ℕ} (hL : 0 < L) (k i : ℕ) : meshAt L k i ≠ 0 :=
  zpow_ne_zero _ (by exact_mod_cast hL.ne')
theorem coe_mem_latticeSubgroup {L k i : ℕ} (hL : 0 < L) (y : FullSpace.Vertex L k (i + 1)) :
    (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  obtain ⟨n, hn⟩ := y.2
  refine ⟨fun μ => n μ * (L : ℤ), fun μ => ?_⟩
  rw [hn μ, meshAt_succ hL]
  push_cast
  ring
theorem coe_toFiner {a a' : ℝ} {y : InfiniteLattice.LatticePoint a}
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
section Scaling
variable {L k j : ℕ} (hL : 0 < L) (hj : j ≤ k)
omit hj in
theorem scalingFactor_ne_zero (hL : 0 < L) : (L : ℝ) ^ (k - j) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast hL.ne')
theorem mem_cube_iff (i i' : ℕ) (y : FullSpace.Vertex L k i') (p : AmbientSpace) :
    p ∈ cube L (meshAt L k i) y ↔
      FullSpace.scaling hL k j p ∈ cube L (meshAt L j i) (FullSpace.scaleVertex hL hj i' y) := by
  rw [← pow_mul_meshAt hL hj i]
  exact mem_cubeOfOrder_iff_smul (scalingFactor_ne_zero hL) _ 1 rfl p
theorem mem_doubleCube_iff (i i' : ℕ) (c : FullSpace.Edge L k i') (p : AmbientSpace) :
    p ∈ doubleCube L (meshAt L k i) c ↔
      FullSpace.scaling hL k j p ∈
        doubleCube L (meshAt L j i) (FullSpace.scaleEdge hL hj i' c) :=
  or_congr (mem_cube_iff hL hj i i' c.initial p) (mem_cube_iff hL hj i i' c.terminal p)
theorem mem_linkCorridor_iff (i i' : ℕ) (c : FullSpace.Edge L k i') (b : FullSpace.Edge L k i) :
    b ∈ linkCorridor L (meshAt L k i) c ↔
      FullSpace.scaleEdge hL hj i b ∈
        linkCorridor L (meshAt L j i) (FullSpace.scaleEdge hL hj i' c) :=
  and_congr (mem_cube_iff hL hj i i' c.initial _) (mem_cube_iff hL hj i i' c.terminal _)
theorem mem_doubleCubeLinks_iff (i i' : ℕ) (c : FullSpace.Edge L k i')
    (b : FullSpace.Edge L k i) :
    b ∈ doubleCubeLinks L (meshAt L k i) c ↔
      FullSpace.scaleEdge hL hj i b ∈
        doubleCubeLinks L (meshAt L j i) (FullSpace.scaleEdge hL hj i' c) :=
  and_congr (mem_doubleCube_iff hL hj i i' c _) (mem_doubleCube_iff hL hj i i' c _)
theorem scaleEdge_forwardFrom (i : ℕ) (x : FullSpace.Vertex L k i) (μ : Fin 4) :
    FullSpace.scaleEdge hL hj i (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.scaleVertex hL hj i x) μ :=
  InfiniteLattice.Link.ext rfl (by
    change FullSpace.scaleVertex hL hj i (x + InfiniteLattice.axisStep _ μ) = _ + _
    rw [map_add, scaleVertex_axisStep])
theorem scaleEdge_backwardLink (i : ℕ) (x : FullSpace.Vertex L k i) (μ : Fin 4) :
    FullSpace.scaleEdge hL hj i (backwardLink x μ) =
      backwardLink (FullSpace.scaleVertex hL hj i x) μ :=
  InfiniteLattice.Link.ext rfl (by
    change FullSpace.scaleVertex hL hj i (x - InfiniteLattice.axisStep _ μ) = _ - _
    rw [map_sub, scaleVertex_axisStep])
theorem map_forwardSteps (i : ℕ) (μ : Fin 4) (m : ℕ) :
    ∀ x : FullSpace.Vertex L k i, (forwardSteps x μ m).map (FullSpace.scaleEdge hL hj i) =
      forwardSteps (FullSpace.scaleVertex hL hj i x) μ m := by
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    simp only [forwardSteps, List.map_cons, ih, scaleEdge_forwardFrom, map_add,
      scaleVertex_axisStep]
theorem map_backwardSteps (i : ℕ) (μ : Fin 4) (m : ℕ) :
    ∀ x : FullSpace.Vertex L k i, (backwardSteps x μ m).map (FullSpace.scaleEdge hL hj i) =
      backwardSteps (FullSpace.scaleVertex hL hj i x) μ m := by
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    simp only [backwardSteps, List.map_cons, ih, scaleEdge_backwardLink, map_sub,
      scaleVertex_axisStep]
theorem map_signedSteps (i : ℕ) (x : FullSpace.Vertex L k i) (μ : Fin 4) (n : ℤ) :
    (signedSteps x μ n).map (FullSpace.scaleEdge hL hj i) =
      signedSteps (FullSpace.scaleVertex hL hj i x) μ n := by
  unfold signedSteps
  split_ifs
  · exact map_forwardSteps hL hj i μ _ x
  · exact map_backwardSteps hL hj i μ _ x
theorem map_stepsInOrder (i : ℕ) (ν : Fin 4 → ℤ) (l : List (Fin 4)) :
    ∀ x : FullSpace.Vertex L k i, (stepsInOrder ν x l).map (FullSpace.scaleEdge hL hj i) =
      stepsInOrder ν (FullSpace.scaleVertex hL hj i x) l := by
  induction l with
  | nil => intro x; rfl
  | cons μ l ih =>
    intro x
    simp only [stepsInOrder, List.map_append, ih, map_signedSteps, map_add, map_zsmul,
      scaleVertex_axisStep]
theorem isAxisDisplacement_scaleVertex_iff (i : ℕ) (x x' : FullSpace.Vertex L k i) (μ : Fin 4)
    (n : ℤ) :
    IsAxisDisplacement (FullSpace.scaleVertex hL hj i x) (FullSpace.scaleVertex hL hj i x') μ n ↔
      IsAxisDisplacement x x' μ n := by
  unfold IsAxisDisplacement
  rw [← map_sub, ← scaleVertex_axisStep hL hj i μ, ← map_zsmul]
  exact (FullSpace.scaleVertex hL hj i).injective.eq_iff
theorem map_axisPath (i : ℕ) (x x' : FullSpace.Vertex L k i) :
    (axisPath x x').map (FullSpace.scaleEdge hL hj i) =
      axisPath (FullSpace.scaleVertex hL hj i x) (FullSpace.scaleVertex hL hj i x') := by
  by_cases hex : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x x' q.1 q.2
  · obtain ⟨⟨μ, n⟩, h⟩ := hex
    rw [axisPath_eq_signedSteps (meshAt_ne_zero hL k i) h,
      axisPath_eq_signedSteps (meshAt_ne_zero hL j i)
        ((isAxisDisplacement_scaleVertex_iff hL hj i x x' μ n).2 h)]
    exact map_signedSteps hL hj i x μ n
  · have hex' : ¬ ∃ q : Fin 4 × ℤ, IsAxisDisplacement (FullSpace.scaleVertex hL hj i x)
        (FullSpace.scaleVertex hL hj i x') q.1 q.2 := fun ⟨q, h⟩ =>
      hex ⟨q, (isAxisDisplacement_scaleVertex_iff hL hj i x x' q.1 q.2).1 h⟩
    unfold axisPath
    rw [dif_neg hex, dif_neg hex']
    rfl
theorem scaleVertex_toFiner (i : ℕ) (y : FullSpace.Vertex L k (i + 1)) :
    FullSpace.scaleVertex hL hj i (toFiner (meshAt L k i) y) =
      toFiner (meshAt L j i) (FullSpace.scaleVertex hL hj (i + 1) y) := by
  apply Subtype.ext
  rw [coe_toFiner (coe_mem_latticeSubgroup hL (FullSpace.scaleVertex hL hj (i + 1) y)),
    FullSpace.coe_scaleVertex, FullSpace.coe_scaleVertex, coe_toFiner (coe_mem_latticeSubgroup hL y)]
theorem isPivotLink_scaleEdge (i : ℕ) {c : FullSpace.Edge L k (i + 1)} {b : FullSpace.Edge L k i}
    (h : IsPivotLink L (meshAt L k i) c b) :
    IsPivotLink L (meshAt L j i) (FullSpace.scaleEdge hL hj (i + 1) c)
      (FullSpace.scaleEdge hL hj i b) := by
  refine ⟨(mem_linkCorridor_iff hL hj i (i + 1) c b).1 h.1, ?_⟩
  have e : axisPath (toFiner (meshAt L j i) (FullSpace.scaleEdge hL hj (i + 1) c).initial)
      (toFiner (meshAt L j i) (FullSpace.scaleEdge hL hj (i + 1) c).terminal) =
      (axisPath (toFiner (meshAt L k i) c.initial)
        (toFiner (meshAt L k i) c.terminal)).map (FullSpace.scaleEdge hL hj i) := by
    rw [map_axisPath, scaleVertex_toFiner, scaleVertex_toFiner]
    rfl
  rw [e]
  exact List.mem_map_of_mem h.2
theorem isCubeOffset_scaleVertex_iff (i i' : ℕ) (y : FullSpace.Vertex L k i')
    (x : FullSpace.Vertex L k i) (ν : Fin 4 → ℤ) :
    IsCubeOffset L (FullSpace.scaleVertex hL hj i' y) (FullSpace.scaleVertex hL hj i x) ν ↔
      IsCubeOffset L y x ν := by
  unfold IsCubeOffset
  refine and_congr_left' ?_
  rw [FullSpace.coe_scaleVertex, FullSpace.coe_scaleVertex, ← map_sub, FullSpace.scaling_apply,
    ← pow_mul_meshAt hL hj i, ← smul_sum_single]
  exact (smul_right_injective AmbientSpace (scalingFactor_ne_zero hL)).eq_iff
theorem cubeOffset_scaleVertex (i i' : ℕ) (y : FullSpace.Vertex L k i')
    (x : FullSpace.Vertex L k i) :
    cubeOffset L (FullSpace.scaleVertex hL hj i' y) (FullSpace.scaleVertex hL hj i x) =
      cubeOffset L y x := by
  unfold cubeOffset
  congr 1
  funext ν
  exact propext (isCubeOffset_scaleVertex_iff hL hj i i' y x ν)
end Scaling
section Contours
variable {a' : ℝ}
def orderedAxisPaths (ν : Fin 4 → ℤ) (z : InfiniteLattice.LatticePoint a') :
    Set (List (InfiniteLattice.Link a')) :=
  Set.range fun σ : Fin (supportAxes ν).card ≃ supportAxes ν =>
    stepsInOrder ν z ((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4))
theorem contourSet_eq {L : ℕ} {a : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    contourSet L y x = orderedAxisPaths (cubeOffset L y x) (toFiner a' y) := rfl
theorem image_orderedAxisPaths {L k j : ℕ} (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (ν : Fin 4 → ℤ)
    (z : FullSpace.Vertex L k i) :
    FullSpace.scalePath hL hj i '' orderedAxisPaths ν z =
      orderedAxisPaths ν (FullSpace.scaleVertex hL hj i z) := by
  unfold orderedAxisPaths
  rw [← Set.range_comp]
  congr 1
  funext σ
  exact map_stepsInOrder hL hj i ν _ z
end Contours
end YangMills.Construction.Tower.FullSpace.ScalingOfStepSets
namespace YangMills.Construction.Tower
open FullSpace.ScalingOfStepSets in
theorem FullSpaceScalingPreservesStepSets.proof
    (h₁ : FullSpace.CubesCorridorsPivotEdgesAndPaths) :
    FullSpaceScalingPreservesStepSets.Statement := by
  intro L hL hstd k j hj hj1 i hi
  have hk1 : 1 ≤ k := hj1.trans hj
  obtain ⟨-, -, P, -⟩ := h₁ L hstd k (i + 1) 1 hk1 (by omega) (by omega) le_rfl (by omega)
  obtain ⟨-, -, P', -⟩ := h₁ L hstd j (i + 1) 1 hj1 (by omega) (by omega) le_rfl (by omega)
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun y x _ => ?_, fun c => ?_⟩
  · exact image_eq_of_forall_mem_iff (FullSpace.scaling hL k j).surjective
      (mem_doubleCube_iff hL hj i (i + 1) c)
  · exact image_eq_of_forall_mem_iff (FullSpace.scaleEdge hL hj i).surjective
      (mem_linkCorridor_iff hL hj i (i + 1) c)
  · obtain ⟨b, hb, hu⟩ := existsUnique_pivotLink (meshAt_ne_zero hL k i) P c
    obtain ⟨b', hb', hu'⟩ :=
      existsUnique_pivotLink (meshAt_ne_zero hL j i) P' (FullSpace.scaleEdge hL hj (i + 1) c)
    have e₁ : FullSpace.pivotLink L (meshAt L k i) c = b :=
      hu _ (Classical.epsilon_spec ⟨b, hb⟩)
    have e₂ : FullSpace.pivotLink L (meshAt L j i) (FullSpace.scaleEdge hL hj (i + 1) c) = b' :=
      hu' _ (Classical.epsilon_spec ⟨b', hb'⟩)
    rw [e₁, e₂]
    exact hu' _ (isPivotLink_scaleEdge hL hj i hb)
  · rw [contourSet_eq, contourSet_eq, cubeOffset_scaleVertex hL hj i (i + 1),
      image_orderedAxisPaths, scaleVertex_toFiner]
  · exact image_eq_of_forall_mem_iff (FullSpace.scaleEdge hL hj i).surjective
      (mem_doubleCubeLinks_iff hL hj i (i + 1) c)
end YangMills.Construction.Tower
end
