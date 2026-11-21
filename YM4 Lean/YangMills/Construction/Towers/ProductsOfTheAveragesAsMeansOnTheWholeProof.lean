import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLatticeProof
import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocksOfTheWholeLatticeProof
import YangMills.Construction.Towers.ProductsOfTheAveragesAsMeansOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratedSmoothing
open InfiniteLattice Matrices
theorem sum_map_walk_eq_smul_finsum {X Y P P₀ : Type*} (F : P → ComplexMatrix2)
    (B : P₀ → ComplexMatrix2) (S : X → Set Y)
    (hS : ∀ x, (S x).Finite) (W : X → ℕ → List P) (W₀ : Y → ℕ → List P₀) (edge : X → P)
    (next : X → X) (shift : Y → Y) (r : ℕ) (w : ℂ) (hzero : ∀ x, W x 0 = [])
    (hsucc : ∀ x N, W x (N + 1) = edge x :: W (next x) N)
    (hadd : ∀ z N, W₀ z (r + N * r) = W₀ z r ++ W₀ (shift z) (N * r))
    (hnil : ∀ z, W₀ z 0 = [])
    (hF : ∀ x, F (edge x) = w • ∑ᶠ z ∈ S x, ((W₀ z r).map B).sum)
    (hT : ∀ x (f : Y → ComplexMatrix2), ∑ᶠ z ∈ S (next x), f z = ∑ᶠ z ∈ S x, f (shift z))
    (N : ℕ) : ∀ x, ((W x N).map F).sum =
      w • ∑ᶠ z ∈ S x, ((W₀ z (N * r)).map B).sum := by
  induction N with
  | zero =>
    intro x
    simp [hzero, hnil]
  | succ N ih =>
    intro x
    rw [hsucc, List.map_cons, List.sum_cons, hF, ih, hT, ← smul_add,
      ← finsum_mem_add_distrib (hS x)]
    congr 1
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    rw [show (N + 1) * r = r + N * r by ring, hadd, List.map_append, List.sum_append]
section Walks
variable {a a' : ℝ}
theorem forwardSteps_add (x : LatticePoint a) (μ : Fin 4) (p q : ℕ) :
    forwardSteps x μ (p + q) =
      forwardSteps x μ p ++ forwardSteps (x + p • axisStep a μ) μ q := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.forwardSteps_add <;> assumption
theorem backwardSteps_add (x : LatticePoint a) (μ : Fin 4) (p q : ℕ) :
    backwardSteps x μ (p + q) =
      backwardSteps x μ p ++ backwardSteps (x - p • axisStep a μ) μ q := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.backwardSteps_add <;> assumption
theorem length_forwardSteps (x : LatticePoint a) (μ : Fin 4) (N : ℕ) :
    (forwardSteps x μ N).length = N := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.length_forwardSteps <;> assumption
theorem length_backwardSteps (x : LatticePoint a) (μ : Fin 4) (N : ℕ) :
    (backwardSteps x μ N).length = N := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.length_backwardSteps <;> assumption
theorem coe_nsmul_axisStep (N : ℕ) (μ : Fin 4) :
    ((N • axisStep a' μ : LatticePoint a') : AmbientSpace) = Pi.single μ ((N : ℝ) * a') := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.coe_nsmul_axisStep <;> assumption
theorem crossingPath_eq_forwardSteps {N : ℕ} (ha' : a' ≠ 0) (hN : a = (N : ℝ) * a')
    (c : Link a) (μ : Fin 4) (hc : c.terminal - c.initial = axisStep a μ)
    (x : LatticePoint a') : crossingPath c x = forwardSteps x μ N := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.crossingPath_of_forward <;> assumption
theorem crossingPath_eq_backwardSteps {N : ℕ} (hN0 : 0 < N) (ha' : a' ≠ 0)
    (hN : a = (N : ℝ) * a')
    (c : Link a) (μ : Fin 4) (hc : c.terminal - c.initial = -axisStep a μ)
    (x : LatticePoint a') : crossingPath c x = backwardSteps x μ N := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.crossingPath_of_backward <;> assumption
theorem edgeFormPathSum_crossingPath_initial (ha : a ≠ 0) (B : Link a → ComplexMatrix2)
    (c : Link a) : edgeFormPathSum B (crossingPath c c.initial) = B c := by
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · rw [crossingPath_eq_forwardSteps (N := 1) ha (by simp) c μ h]
    have hc : c = Link.forwardFrom c.initial μ := by
      apply Link.ext
      · rfl
      · have : c.terminal = c.initial + axisStep a μ := by rw [← h]; abel
        simp [Link.forwardFrom, this]
    simp only [forwardSteps, edgeFormPathSum, sumAlong, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← hc]
  · rw [crossingPath_eq_backwardSteps (N := 1) one_pos ha (by simp) c μ h]
    have hc : c = backwardLink c.initial μ := by
      apply Link.ext
      · rfl
      · have : c.terminal = c.initial + -axisStep a μ := by rw [← h]; abel
        simp [backwardLink, this, sub_eq_add_neg]
    simp only [backwardSteps, edgeFormPathSum, sumAlong, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← hc]
end Walks
section Blocks
variable {a a' : ℝ}
theorem ncard_points_of_cubeOfOrder {L n N : ℕ} (y : LatticePoint a)
    (hcard : (cubeOfOrder L a' n y).ncard = N)
    (hsub : cubeOfOrder L a' n y ⊆ (latticeSubgroup a' : Set AmbientSpace)) :
    {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y}.ncard = N := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.ncard_points_of_cube <;> assumption
theorem points_of_cubeOfOrder_add {L n : ℕ} (y w : LatticePoint a)
    (w₀ : LatticePoint a') (h : (w₀ : AmbientSpace) = w) :
    {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n (y + w)} =
      (fun z => z + w₀) ''
        {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y} := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.points_of_cube_add <;> assumption
theorem finsum_points_of_cubeOfOrder_add {L n : ℕ} (y w : LatticePoint a)
    (w₀ : LatticePoint a') (h : (w₀ : AmbientSpace) = w)
    (f : LatticePoint a' → ComplexMatrix2) :
    ∑ᶠ x ∈ {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n (y + w)}, f x =
      ∑ᶠ z ∈ {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y},
        f (z + w₀) := by
  have hinj : Function.Injective fun z : LatticePoint a' => z + w₀ := add_left_injective w₀
  rw [points_of_cubeOfOrder_add y w w₀ h, finsum_mem_image hinj.injOn]
end Blocks
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem meshAt_succ {L : ℕ} (hL : 0 < L) (k m : ℕ) :
    meshAt L k (m + 1) = (L : ℝ) * meshAt L k m := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.meshAt_succ <;> assumption
theorem meshAt_add {L : ℕ} (hL : 0 < L) (k i m : ℕ) :
    meshAt L k (i + m) = ((L ^ m : ℕ) : ℝ) * meshAt L k i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, meshAt_succ hL, ih]
    push_cast
    ring
section Tower
variable {L k : ℕ}
abbrev cubeVertexSet (L k i n : ℕ) {l : ℕ} (y : FullSpace.Vertex L k l) :
    Set (FullSpace.Vertex L k i) :=
  {x | (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) n y}
theorem cubeVertexSet_zero {i l : ℕ} (y : FullSpace.Vertex L k l)
    (x₀ : FullSpace.Vertex L k i)
    (h : (x₀ : AmbientSpace) = y) : cubeVertexSet L k i 0 y = {x₀} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨ν, hν, hx⟩
    have h0 : ν = 0 := by
      funext μ
      have := hν μ
      simp only [pow_zero, sub_self] at this
      have h2 : |ν μ| ≤ 0 := by linarith
      simpa using abs_nonpos_iff.mp h2
    subst h0
    apply Subtype.ext
    rw [h]
    simpa using hx
  · rintro rfl
    exact ⟨0, by simp, by simpa using h⟩
theorem ncard_cubeVertexSet (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i m : ℕ} (hk : 1 ≤ k) (hm : i + m ≤ k)
    (y : FullSpace.Vertex L k (i + m)) : (cubeVertexSet L k i m y).ncard = L ^ (4 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [cubeVertexSet_zero (i := i) y y rfl]
    simp
  · have hb := (hY L hL k (i + m) m hk (by omega) hm hpos (by omega)).1
    have h1 := hb.cube_ncard y
    have h2 := hb.iUnion_cube
    rw [Nat.add_sub_cancel] at h1 h2
    refine ncard_points_of_cubeOfOrder y h1 ?_
    rw [← h2]
    exact subset_iUnion
      (fun y : FullSpace.Vertex L k (i + m) => cubeOfOrder L (meshAt L k i) m y) y
theorem finite_cubeVertexSet (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i m : ℕ} (hk : 1 ≤ k) (hm : i + m ≤ k)
    (y : FullSpace.Vertex L k (i + m)) : (cubeVertexSet L k i m y).Finite := by
  have hL0 : 0 < L := by have := hL.2; omega
  apply finite_of_ncard_pos
  rw [ncard_cubeVertexSet hY hL hk hm y]
  positivity
theorem finite_cubeVertices (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m + 1 ≤ k)
    (y : FullSpace.Vertex L k (m + 1)) :
    (cubeVertices L (meshAt L k m) y).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.finite_cubeVertices <;> assumption
theorem cubeVertexSet_one {i : ℕ} (y : FullSpace.Vertex L k (i + 1)) :
    cubeVertexSet L k i 1 y =
        ⋃ x ∈ cubeVertices L (meshAt L k i) y, cubeVertexSet L k i 0 x ∧
      (cubeVertices L (meshAt L k i) y).PairwiseDisjoint
        fun x => cubeVertexSet L k i 0 x := by
  have h0 : ∀ x : FullSpace.Vertex L k i, cubeVertexSet L k i 0 x = {x} :=
    fun x => cubeVertexSet_zero x x rfl
  constructor
  · simp only [h0, biUnion_of_singleton]
    rfl
  · intro x _ x' _ hne
    simpa only [Function.onFun, h0] using disjoint_singleton.2 hne
theorem cubeVertexSet_succ (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i m : ℕ} (hm : i + m + 1 ≤ k)
    (y : FullSpace.Vertex L k (i + m + 1)) :
    cubeVertexSet L k i (m + 1) y =
        ⋃ x ∈ cubeVertices L (meshAt L k (i + m)) y, cubeVertexSet L k i m x ∧
      (cubeVertices L (meshAt L k (i + m)) y).PairwiseDisjoint
        fun x => cubeVertexSet L k i m x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact cubeVertexSet_one y
  · have hd := (hY L hL k (i + m + 1) (m + 1) (by omega) (by omega) hm (by omega)
      (by omega)).2.1 (by omega) y
    have h1 := hd.cube_eq_biUnion
    have h2 := hd.pairwiseDisjoint_subcube
    rw [show i + m + 1 - (m + 1) = i by omega] at h1 h2
    constructor
    · ext z
      simp only [mem_iUnion]
      change (z : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) (m + 1) y ↔ _
      rw [h1]
      simp only [mem_iUnion]
      rfl
    · intro x hx x' hx' hne
      exact disjoint_left.2 fun z hz hz' => disjoint_left.1 (h2 hx hx' hne) hz hz'
theorem inverseFourthPowerWeight_mul {L : ℕ} (m : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L * ((L : ℂ) ^ (4 * m))⁻¹ =
      ((L : ℂ) ^ (4 * (m + 1)))⁻¹ := by
  have h : PeriodicLattice.inverseFourthPowerWeight L = ((L : ℂ) ^ 4)⁻¹ := by
    simp [PeriodicLattice.inverseFourthPowerWeight, zpow_neg]
  rw [h, ← mul_inv, ← pow_add]
  congr 2
  ring
theorem average_of_averages (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i m : ℕ} (hm : i + m + 1 ≤ k)
    (y : FullSpace.Vertex L k (i + m + 1)) (f : FullSpace.Vertex L k i → ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k (i + m)) y,
        ((L : ℂ) ^ (4 * m))⁻¹ • ∑ᶠ z ∈ cubeVertexSet L k i m x, f z =
      ((L : ℂ) ^ (4 * (m + 1)))⁻¹ • ∑ᶠ z ∈ cubeVertexSet L k i (m + 1) y, f z := by
  have hk : 1 ≤ k := by omega
  have hm' : i + m ≤ k := by omega
  have hfin := finite_cubeVertices hY hL hm y
  obtain ⟨hU, hD⟩ := cubeVertexSet_succ hY hL hm y
  rw [← smul_finsum_mem hfin, smul_smul, inverseFourthPowerWeight_mul, hU,
    finsum_mem_biUnion hD hfin fun x _ => finite_cubeVertexSet hY hL hk hm' x]
variable {i m : ℕ}
theorem edgeFormPathSum_forwardSteps (hL : 0 < L)
    (hfin : ∀ x : FullSpace.Vertex L k (i + m), (cubeVertexSet L k i m x).Finite)
    (F : FullSpace.Edge L k (i + m) → ComplexMatrix2) (B : FullSpace.Edge L k i → ComplexMatrix2)
    (w : ℂ)
    (hc : ∀ c : FullSpace.Edge L k (i + m),
      F c = w • ∑ᶠ z ∈ cubeVertexSet L k i m c.initial, edgeFormPathSum B (crossingPath c z))
    (μ : Fin 4) (N : ℕ) (x : FullSpace.Vertex L k (i + m)) :
    edgeFormPathSum F (forwardSteps x μ N) =
      w • ∑ᶠ z ∈ cubeVertexSet L k i m x,
        edgeFormPathSum B (forwardSteps z μ (N * L ^ m)) := by
  have ha₀ := (meshAt_pos hL k i).ne'
  have hN := meshAt_add hL k i m
  refine sum_map_walk_eq_smul_finsum F B (fun x => cubeVertexSet L k i m x) hfin
    (fun x N => forwardSteps x μ N) (fun z N => forwardSteps z μ N)
    (fun x => Link.forwardFrom x μ) (fun x => x + axisStep (meshAt L k (i + m)) μ)
    (fun z => z + (L ^ m) • axisStep (meshAt L k i) μ) (L ^ m) w
    (fun _ => rfl) (fun _ _ => rfl) (fun z N => forwardSteps_add z μ _ _) (fun _ => rfl)
    ?_ ?_ N x
  · intro x
    rw [hc (Link.forwardFrom x μ)]
    have hstep : (Link.forwardFrom x μ).terminal - (Link.forwardFrom x μ).initial =
        axisStep (meshAt L k (i + m)) μ := by simp [Link.forwardFrom]
    simp only [crossingPath_eq_forwardSteps ha₀ hN (Link.forwardFrom x μ) μ hstep]
    rfl
  · intro x f
    exact finsum_points_of_cubeOfOrder_add x (axisStep (meshAt L k (i + m)) μ)
      ((L ^ m) • axisStep (meshAt L k i) μ)
      (by rw [coe_nsmul_axisStep, ← hN]; rfl) f
theorem edgeFormPathSum_backwardSteps (hL : 0 < L)
    (hfin : ∀ x : FullSpace.Vertex L k (i + m), (cubeVertexSet L k i m x).Finite)
    (F : FullSpace.Edge L k (i + m) → ComplexMatrix2) (B : FullSpace.Edge L k i → ComplexMatrix2)
    (w : ℂ)
    (hc : ∀ c : FullSpace.Edge L k (i + m),
      F c = w • ∑ᶠ z ∈ cubeVertexSet L k i m c.initial, edgeFormPathSum B (crossingPath c z))
    (μ : Fin 4) (N : ℕ) (x : FullSpace.Vertex L k (i + m)) :
    edgeFormPathSum F (backwardSteps x μ N) =
      w • ∑ᶠ z ∈ cubeVertexSet L k i m x,
        edgeFormPathSum B (backwardSteps z μ (N * L ^ m)) := by
  have ha₀ := (meshAt_pos hL k i).ne'
  have hN := meshAt_add hL k i m
  refine sum_map_walk_eq_smul_finsum F B (fun x => cubeVertexSet L k i m x) hfin
    (fun x N => backwardSteps x μ N) (fun z N => backwardSteps z μ N)
    (fun x => backwardLink x μ) (fun x => x - axisStep (meshAt L k (i + m)) μ)
    (fun z => z - (L ^ m) • axisStep (meshAt L k i) μ) (L ^ m) w
    (fun _ => rfl) (fun _ _ => rfl) (fun z N => backwardSteps_add z μ _ _) (fun _ => rfl)
    ?_ ?_ N x
  · intro x
    rw [hc (backwardLink x μ)]
    have hstep : (backwardLink x μ).terminal - (backwardLink x μ).initial =
        -axisStep (meshAt L k (i + m)) μ := by simp [backwardLink]
    simp only [crossingPath_eq_backwardSteps (pow_pos hL m) ha₀ hN (backwardLink x μ) μ hstep]
    rfl
  · intro x f
    simp only [sub_eq_add_neg]
    exact finsum_points_of_cubeOfOrder_add x (-axisStep (meshAt L k (i + m)) μ)
      (-((L ^ m) • axisStep (meshAt L k i) μ))
      (by rw [AddSubgroup.coe_neg, AddSubgroup.coe_neg, coe_nsmul_axisStep, ← hN]; rfl) f
theorem vertex_iterate_eq_mean (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (P : ∀ l, i ≤ l → (FullSpace.Vertex L k i → ComplexMatrix2) →
      FullSpace.Vertex L k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1),
      P (l + 1) h' = vertexSmoothing (a := meshAt L k (l + 1)) L ∘ P l h)
    (f : FullSpace.Vertex L k i → ComplexMatrix2) (n : ℕ) (hn : i + n ≤ k)
    (y : FullSpace.Vertex L k (i + n)) :
    P (i + n) (Nat.le_add_right i n) f y =
      ((L : ℂ) ^ (4 * n))⁻¹ • ∑ᶠ x ∈ cubeVertexSet L k i n y, f x := by
  induction n with
  | zero =>
    have key : ∀ y : FullSpace.Vertex L k i, P i le_rfl f y =
        ((L : ℂ) ^ (4 * 0))⁻¹ • ∑ᶠ x ∈ cubeVertexSet L k i 0 y, f x := by
      intro y
      rw [h0, cubeVertexSet_zero y y rfl, finsum_mem_singleton]
      simp
    exact key y
  | succ m ih =>
    have hm : i + m + 1 ≤ k := hn
    have key : ∀ y : FullSpace.Vertex L k (i + m + 1),
        P (i + m + 1) (Nat.le_add_right i (m + 1)) f y =
          ((L : ℂ) ^ (4 * (m + 1)))⁻¹ • ∑ᶠ x ∈ cubeVertexSet L k i (m + 1) y, f x := by
      intro y
      rw [← average_of_averages hY hL hm y f, hs (i + m) (Nat.le_add_right i m)]
      change PeriodicLattice.inverseFourthPowerWeight L •
          ∑ᶠ x ∈ cubeVertices L (meshAt L k (i + m)) y,
            P (i + m) (Nat.le_add_right i m) f x = _
      congr 1
      exact finsum_congr fun x => finsum_congr fun _ => ih (by omega) x
    exact key y
theorem crossing_iterate_eq_mean (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (P : ∀ l, i ≤ l → (FullSpace.Edge L k i → ComplexMatrix2) →
      FullSpace.Edge L k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1),
      P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h)
    (B : FullSpace.Edge L k i → ComplexMatrix2) (n : ℕ) (hn : i + n ≤ k)
    (c : FullSpace.Edge L k (i + n)) :
    P (i + n) (Nat.le_add_right i n) B c =
      ((L : ℂ) ^ (4 * n))⁻¹ •
        ∑ᶠ x ∈ cubeVertexSet L k i n c.initial, edgeFormPathSum B (crossingPath c x) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have ha₀ := (meshAt_pos hL0 k i).ne'
  induction n with
  | zero =>
    have key : ∀ c : FullSpace.Edge L k i, P i le_rfl B c =
        ((L : ℂ) ^ (4 * 0))⁻¹ •
          ∑ᶠ x ∈ cubeVertexSet L k i 0 c.initial, edgeFormPathSum B (crossingPath c x) := by
      intro c
      rw [h0, cubeVertexSet_zero c.initial c.initial rfl, finsum_mem_singleton,
        edgeFormPathSum_crossingPath_initial ha₀]
      simp
    exact key c
  | succ m ih =>
    have hm : i + m + 1 ≤ k := hn
    have hm' : i + m ≤ k := by omega
    have ham := (meshAt_pos hL0 k (i + m)).ne'
    have hfin := fun x : FullSpace.Vertex L k (i + m) => finite_cubeVertexSet hY hL hk hm' x
    have hs' : meshAt L k (i + m + 1) = ((L : ℕ) : ℝ) * meshAt L k (i + m) :=
      meshAt_succ hL0 k (i + m)
    have hs₁ : meshAt L k (i + m + 1) = ((L * L ^ m : ℕ) : ℝ) * meshAt L k i := by
      have := meshAt_add hL0 k i (m + 1)
      rw [pow_succ'] at this
      exact this
    have key : ∀ c : FullSpace.Edge L k (i + m + 1),
        P (i + m + 1) (Nat.le_add_right i (m + 1)) B c =
          ((L : ℂ) ^ (4 * (m + 1)))⁻¹ • ∑ᶠ x ∈ cubeVertexSet L k i (m + 1) c.initial,
            edgeFormPathSum B (crossingPath c x) := by
      intro c
      rw [← average_of_averages hY hL hm c.initial, hs (i + m) (Nat.le_add_right i m)]
      change PeriodicLattice.inverseFourthPowerWeight L •
          ∑ᶠ x ∈ cubeVertices L (meshAt L k (i + m)) c.initial,
            edgeFormPathSum (P (i + m) (Nat.le_add_right i m) B) (crossingPath c x) = _
      congr 1
      refine finsum_congr fun x => finsum_congr fun _ => ?_
      obtain ⟨μ, h | h⟩ := c.isAdjacent
      · rw [crossingPath_eq_forwardSteps ham hs' c μ h,
          edgeFormPathSum_forwardSteps hL0 hfin _ B _ (ih hm') μ L x]
        simp only [crossingPath_eq_forwardSteps ha₀ hs₁ c μ h]
      · rw [crossingPath_eq_backwardSteps hL0 ham hs' c μ h,
          edgeFormPathSum_backwardSteps hL0 hfin _ B _ (ih hm') μ L x]
        simp only [crossingPath_eq_backwardSteps (Nat.mul_pos hL0 (pow_pos hL0 m)) ha₀ hs₁ c μ h]
    exact key c
theorem length_crossingPath (hL : 0 < L) (n : ℕ) (c : FullSpace.Edge L k (i + n))
    (x : FullSpace.Vertex L k i) : (crossingPath c x).length = L ^ n := by
  have ha₀ := (meshAt_pos hL k i).ne'
  have hN := meshAt_add hL k i n
  obtain ⟨μ, h | h⟩ := c.isAdjacent
  · rw [crossingPath_eq_forwardSteps ha₀ hN c μ h, length_forwardSteps]
  · rw [crossingPath_eq_backwardSteps (pow_pos hL n) ha₀ hN c μ h, length_backwardSteps]
end Tower
def matrixSize (X : ComplexMatrix2) : ℝ≥0∞ := ENNReal.ofReal ‖X‖
theorem matrixSize_list_sum_le (l : List ComplexMatrix2) (M : ℝ≥0∞)
    (h : ∀ X ∈ l, matrixSize X ≤ M) :
    matrixSize l.sum ≤ l.length * M := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.magnitude_list_sum_le <;> assumption
theorem matrixSize_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ComplexMatrix2)
    (M : ℝ≥0∞)
    (h : ∀ i ∈ s, matrixSize (f i) ≤ M) : matrixSize (∑ i ∈ s, f i) ≤ s.card * M := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.magnitude_finset_sum_le_card_mul <;> assumption
theorem matrixSize_le_maxOperatorNorm {ι : Type*} (f : ι → ComplexMatrix2) (i : ι) :
    matrixSize (f i) ≤ maxOperatorNorm f := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_le_maxOperatorNorm <;> assumption
theorem matrixSize_mean_le (c : ℕ) (Y : ComplexMatrix2) (M : ℝ≥0∞) (h : matrixSize Y ≤ c * M) :
    matrixSize ((((c : ℝ)⁻¹ : ℝ) : ℂ) • Y) ≤ M := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.magnitude_inv_nat_smul_le <;> assumption
section Bound
variable {L k i : ℕ}
theorem maxOperatorNorm_crossing_iterate_le (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (P : ∀ l, i ≤ l → (FullSpace.Edge L k i → ComplexMatrix2) →
      FullSpace.Edge L k l → ComplexMatrix2)
    (h0 : ∀ h, P i h = id)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1),
      P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h)
    (B : FullSpace.Edge L k i → ComplexMatrix2) (n : ℕ) (hn : i + n ≤ k) :
    maxOperatorNorm (P (i + n) (Nat.le_add_right i n) B) ≤
      (L : ℝ≥0∞) ^ n * maxOperatorNorm B := by
  have hL0 : 0 < L := by have := hL.2; omega
  refine iSup_le fun c => ?_
  change matrixSize (P (i + n) (Nat.le_add_right i n) B c) ≤ _
  rw [crossing_iterate_eq_mean hY hL hk P h0 hs B n hn c]
  have hfin := finite_cubeVertexSet hY hL hk hn c.initial
  have hw : ((L : ℂ) ^ (4 * n))⁻¹ = ((((L ^ (4 * n) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hw]
  refine matrixSize_mean_le (L ^ (4 * n)) _ _ ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have key := matrixSize_finset_sum_le hfin.toFinset
    (fun x => edgeFormPathSum B (crossingPath c x))
    ((L : ℝ≥0∞) ^ n * maxOperatorNorm B) fun x _ => by
      have h1 := matrixSize_list_sum_le ((crossingPath c x).map B) (maxOperatorNorm B) (by
        intro X hX
        obtain ⟨b, _, rfl⟩ := List.mem_map.1 hX
        exact matrixSize_le_maxOperatorNorm B b)
      rw [List.length_map, length_crossingPath hL0 n c x] at h1
      have h2 : matrixSize (edgeFormPathSum B (crossingPath c x)) ≤
          ((L ^ n : ℕ) : ℝ≥0∞) * maxOperatorNorm B := h1
      simpa using h2
  rwa [← Set.ncard_eq_toFinset_card _ hfin, ncard_cubeVertexSet hY hL hk hn c.initial] at key
end Bound
theorem iterate_means_of_add_eq (hY : CubesCorridorsPivotEdgesAndPaths) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (i n j : ℕ) (e : i + n = j)
    (hj : j ≤ k) :
    (∀ P : (∀ l, i ≤ l → (FullSpace.Vertex L k i → ComplexMatrix2) →
        FullSpace.Vertex L k l → ComplexMatrix2),
      (∀ h, P i h = id) →
      (∀ l (h : i ≤ l) (h' : i ≤ l + 1),
        P (l + 1) h' = vertexSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ (hij : i ≤ j) (f : FullSpace.Vertex L k i → ComplexMatrix2) (y : FullSpace.Vertex L k j),
        P j hij f y = ((L : ℂ) ^ (4 * n))⁻¹ • ∑ᶠ x ∈ cubeVertexSet L k i n y, f x) ∧
    (∀ P : (∀ l, i ≤ l → (FullSpace.Edge L k i → ComplexMatrix2) →
        FullSpace.Edge L k l → ComplexMatrix2),
      (∀ h, P i h = id) →
      (∀ l (h : i ≤ l) (h' : i ≤ l + 1),
        P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ (hij : i ≤ j) (B : FullSpace.Edge L k i → ComplexMatrix2) (c : FullSpace.Edge L k j),
        P j hij B c = ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ cubeVertexSet L k i n c.initial, edgeFormPathSum B (crossingPath c x)) ∧
    (∀ (c : FullSpace.Edge L k j) (x : FullSpace.Vertex L k i),
      (crossingPath c x).length = L ^ n) ∧
    (∀ P : (∀ l, i ≤ l → (FullSpace.Edge L k i → ComplexMatrix2) →
        FullSpace.Edge L k l → ComplexMatrix2),
      (∀ h, P i h = id) →
      (∀ l (h : i ≤ l) (h' : i ≤ l + 1),
        P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ (hij : i ≤ j) (B : FullSpace.Edge L k i → ComplexMatrix2),
        maxOperatorNorm (P j hij B) ≤ (L : ℝ≥0∞) ^ n * maxOperatorNorm B) := by
  subst e
  have hL0 : 0 < L := by have := hL.2; omega
  exact ⟨fun P h0 hs _ f y => vertex_iterate_eq_mean hY hL P h0 hs f n hj y,
    fun P h0 hs _ B c => crossing_iterate_eq_mean hY hL hk P h0 hs B n hj c,
    fun c x => length_crossingPath hL0 n c x,
    fun P h0 hs _ B => maxOperatorNorm_crossing_iterate_le hY hL hk P h0 hs B n hj⟩
theorem iteratedSmoothingAsMeans_holds (hY : CubesCorridorsPivotEdgesAndPaths) :
    IteratedSmoothingAsMeans := by
  intro L hL k n j hk hn hj
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    iterate_means_of_add_eq hY hL hk (j - n) n j (Nat.sub_add_cancel hn) hj
  exact ⟨fun P h0 hs f y => h₁ P h0 hs (Nat.sub_le j n) f y,
    fun P h0 hs B c => h₂ P h0 hs (Nat.sub_le j n) B c,
    fun c x _ => h₃ c x,
    fun P h0 hs B => h₄ P h0 hs (Nat.sub_le j n) B⟩
end YangMills.Construction.Tower.FullSpace.IteratedSmoothing
end
