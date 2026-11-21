import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocksOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.Tower.TrivialLinearization (setAverage)
theorem setAverage_add {ι : Type*} {S : Set ι} (hS : S.Finite) (f g : ι → Matrices.ComplexMatrix2) :
    setAverage S (fun x => f x + g x) = setAverage S f + setAverage S g := by
  simp only [setAverage]
  rw [finsum_mem_add_distrib hS, smul_add]
theorem setAverage_zero {ι : Type*} (S : Set ι) :
    setAverage S (fun _ => (0 : Matrices.ComplexMatrix2)) = 0 := by
  simp [setAverage]
theorem setAverage_singleton {ι : Type*} (y : ι) (f : ι → Matrices.ComplexMatrix2) :
    setAverage {y} f = f y := by
  simp [setAverage]
theorem sum_along_walk_eq_setAverage {X Y P P₀ : Type*} (F : P → Matrices.ComplexMatrix2)
    (B : P₀ → Matrices.ComplexMatrix2) (S : X → Set Y)
    (hS : ∀ x, (S x).Finite) (W : X → ℕ → List P) (W₀ : Y → ℕ → List P₀) (edge : X → P)
    (next : X → X) (shift : Y → Y) (r : ℕ) (hzero : ∀ x, W x 0 = [])
    (hsucc : ∀ x N, W x (N + 1) = edge x :: W (next x) N)
    (hadd : ∀ z N, W₀ z (r + N * r) = W₀ z r ++ W₀ (shift z) (N * r))
    (hnil : ∀ z, W₀ z 0 = [])
    (hF : ∀ x, F (edge x) = setAverage (S x) fun z => ((W₀ z r).map B).sum)
    (hT : ∀ x (f : Y → Matrices.ComplexMatrix2),
      setAverage (S (next x)) f = setAverage (S x) fun z => f (shift z))
    (N : ℕ) : ∀ x, ((W x N).map F).sum =
      setAverage (S x) fun z => ((W₀ z (N * r)).map B).sum := by
  induction N with
  | zero =>
    intro x
    simp only [hzero, Nat.zero_mul, hnil, List.map_nil, List.sum_nil]
    exact (setAverage_zero _).symm
  | succ N ih =>
    intro x
    rw [hsucc, List.map_cons, List.sum_cons, hF, ih, hT, ← setAverage_add (hS x)]
    congr 1
    funext z
    rw [show (N + 1) * r = r + N * r by ring, hadd, List.map_append, List.sum_append]
section Walks
variable {a a' : ℝ}
theorem forwardSteps_add (x : LatticePoint a) (μ : Fin 4) (p q : ℕ) :
    forwardSteps x μ (p + q) =
      forwardSteps x μ p ++ forwardSteps (x + p • axisStep a μ) μ q := by
  induction p generalizing x with
  | zero => simp [forwardSteps]
  | succ p ih =>
    have hs : x + axisStep a μ + p • axisStep a μ = x + (p + 1) • axisStep a μ := by
      rw [succ_nsmul']
      abel
    rw [Nat.add_right_comm p 1 q, forwardSteps, ih (x + axisStep a μ), forwardSteps,
      List.cons_append, hs]
theorem backwardSteps_add (x : LatticePoint a) (μ : Fin 4) (p q : ℕ) :
    backwardSteps x μ (p + q) =
      backwardSteps x μ p ++ backwardSteps (x - p • axisStep a μ) μ q := by
  induction p generalizing x with
  | zero => simp [backwardSteps]
  | succ p ih =>
    have hs : x - axisStep a μ - p • axisStep a μ = x - (p + 1) • axisStep a μ := by
      rw [succ_nsmul']
      abel
    rw [Nat.add_right_comm p 1 q, backwardSteps, ih (x - axisStep a μ), backwardSteps,
      List.cons_append, hs]
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : LatticePoint a} {μ : Fin 4} {n : ℤ}
    (h : IsAxisDisplacement x x' μ n) : axisPath x x' = signedSteps x μ n := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfStepSets.axisPath_eq_signedSteps <;> assumption
theorem toFiner_eq_of_coe (y : LatticePoint a) (x : LatticePoint a')
    (h : (x : AmbientSpace) = y) : toFiner a' y = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.toFiner_eq <;> assumption
theorem coe_nsmul_axisStep (N : ℕ) (μ : Fin 4) :
    ((N • axisStep a' μ : LatticePoint a') : AmbientSpace) = Pi.single μ ((N : ℝ) * a') := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [axisStep]
  · simp [axisStep, Pi.single_eq_of_ne h]
theorem crossingPath_of_forward {N : ℕ} (ha' : a' ≠ 0) (hN : a = (N : ℝ) * a')
    (c : Link a) (μ : Fin 4) (hc : c.terminal - c.initial = axisStep a μ)
    (x : LatticePoint a') : crossingPath c x = forwardSteps x μ N := by
  have hv : toFiner a' (c.terminal - c.initial) = N • axisStep a' μ := by
    apply toFiner_eq_of_coe
    rw [hc, coe_nsmul_axisStep, ← hN]
    rfl
  have hd : IsAxisDisplacement x (shifted c x) μ (N : ℤ) := by
    change x + toFiner a' (c.terminal - c.initial) - x = (N : ℤ) • axisStep a' μ
    rw [hv]
    simp
  unfold crossingPath
  rw [axisPath_eq_signedSteps ha' hd, signedSteps, if_pos (by omega)]
  simp
theorem crossingPath_of_backward {N : ℕ} (hN0 : 0 < N) (ha' : a' ≠ 0) (hN : a = (N : ℝ) * a')
    (c : Link a) (μ : Fin 4) (hc : c.terminal - c.initial = -axisStep a μ)
    (x : LatticePoint a') : crossingPath c x = backwardSteps x μ N := by
  have hv : toFiner a' (c.terminal - c.initial) = -(N • axisStep a' μ) := by
    apply toFiner_eq_of_coe
    rw [hc, AddSubgroup.coe_neg, AddSubgroup.coe_neg, coe_nsmul_axisStep, ← hN]
    rfl
  have hd : IsAxisDisplacement x (shifted c x) μ (-(N : ℤ)) := by
    change x + toFiner a' (c.terminal - c.initial) - x = (-(N : ℤ)) • axisStep a' μ
    rw [hv]
    simp
  unfold crossingPath
  rw [axisPath_eq_signedSteps ha' hd, signedSteps, if_neg (by omega)]
  simp
end Walks
section Cubes
variable {a a' : ℝ}
theorem ncard_points_of_cube {L n N : ℕ} (y : LatticePoint a)
    (hcard : (cubeOfOrder L a' n y).ncard = N)
    (hsub : cubeOfOrder L a' n y ⊆ (latticeSubgroup a' : Set AmbientSpace)) :
    {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y}.ncard = N := by
  have himg : ((↑) : LatticePoint a' → AmbientSpace) ''
      {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y} =
        cubeOfOrder L a' n y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
  have := ncard_image_of_injective
    {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y}
    (Subtype.val_injective (p := fun p => p ∈ latticeSubgroup a'))
  rw [← this]
  exact (congrArg ncard himg).trans hcard
theorem points_of_cube_add {L n : ℕ} (y w : LatticePoint a)
    (w₀ : LatticePoint a') (h : (w₀ : AmbientSpace) = w) :
    {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n (y + w)} =
      (fun z => z + w₀) '' {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y} := by
  ext z
  constructor
  · rintro ⟨ν, hν, hz⟩
    refine ⟨z - w₀, ⟨ν, hν, ?_⟩, by simp⟩
    rw [AddSubgroup.coe_sub, hz, h, AddSubgroup.coe_add]
    abel
  · rintro ⟨x, ⟨ν, hν, hx⟩, rfl⟩
    refine ⟨ν, hν, ?_⟩
    rw [AddSubgroup.coe_add, hx, h, AddSubgroup.coe_add]
    abel
theorem setAverage_cube_add {L n : ℕ} (y w : LatticePoint a)
    (w₀ : LatticePoint a') (h : (w₀ : AmbientSpace) = w)
    (f : LatticePoint a' → Matrices.ComplexMatrix2) :
    setAverage {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n (y + w)} f =
      setAverage {x : LatticePoint a' | (x : AmbientSpace) ∈ cubeOfOrder L a' n y}
        fun z => f (z + w₀) := by
  have hinj : Function.Injective fun z : LatticePoint a' => z + w₀ := add_left_injective w₀
  rw [points_of_cube_add y w w₀ h]
  simp only [setAverage]
  rw [ncard_image_of_injective _ hinj, finsum_mem_image hinj.injOn]
end Cubes
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem meshAt_succ {L : ℕ} (hL : 0 < L) (k m : ℕ) :
    meshAt L k (m + 1) = (L : ℝ) * meshAt L k m := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.meshAt_succ <;> assumption
theorem meshAt_eq_pow_mul {L : ℕ} (hL : 0 < L) (k m : ℕ) :
    meshAt L k m = ((L ^ m : ℕ) : ℝ) * meshAt L k 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [meshAt_succ hL, ih]
    push_cast
    ring
section Levels
variable {L k : ℕ}
theorem baseVerticesOfCube_zero (y : Vertex L k 0) :
    TrivialLinearization.baseVerticesOfCube L k 0 y = {y} := by
  ext x
  simp only [TrivialLinearization.baseVerticesOfCube, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨ν, hν, h⟩
    have h0 : ν = 0 := by
      funext μ
      have := hν μ
      simp only [pow_zero, sub_self] at this
      have h2 : |ν μ| ≤ 0 := by linarith
      simpa using abs_nonpos_iff.mp h2
    subst h0
    apply Subtype.ext
    simpa using h
  · rintro rfl
    exact ⟨0, by simp, by simp⟩
theorem ncard_baseVerticesOfCube (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hk : 1 ≤ k) (hm : m ≤ k)
    (y : Vertex L k m) :
    (TrivialLinearization.baseVerticesOfCube L k m y).ncard = L ^ (4 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [baseVerticesOfCube_zero]
    simp
  · have hb := (hY L hL k m m hk hpos hm hpos le_rfl).1
    have h1 := hb.cube_ncard y
    have h2 := hb.iUnion_cube
    rw [Nat.sub_self] at h1 h2
    refine ncard_points_of_cube y h1 ?_
    rw [← h2]
    exact subset_iUnion (fun y : Vertex L k m => cubeOfOrder L (meshAt L k 0) m y) y
theorem finite_baseVerticesOfCube (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hk : 1 ≤ k) (hm : m ≤ k)
    (y : Vertex L k m) :
    (TrivialLinearization.baseVerticesOfCube L k m y).Finite := by
  have hL0 : 0 < L := by have := hL.2; omega
  apply finite_of_ncard_pos
  rw [ncard_baseVerticesOfCube hY hL hk hm y]
  positivity
theorem finite_cubeVertices (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m + 1 ≤ k)
    (y : Vertex L k (m + 1)) :
    (cubeVertices L (meshAt L k m) y).Finite := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hb := (hY L hL k (m + 1) 1 (by omega) (by omega) hm le_rfl (by omega)).1
  have h1 : (cubeOfOrder L (meshAt L k m) 1 y).ncard = L ^ (4 * 1) := hb.cube_ncard y
  have h2 : (⋃ y : Vertex L k (m + 1), cubeOfOrder L (meshAt L k m) 1 y) =
      (latticeSubgroup (meshAt L k m) : Set AmbientSpace) := hb.iUnion_cube
  have h3 := ncard_points_of_cube y h1 (by
    rw [← h2]
    exact subset_iUnion
      (fun y : Vertex L k (m + 1) => cubeOfOrder L (meshAt L k m) 1 y) y)
  apply finite_of_ncard_pos
  change {x : LatticePoint (meshAt L k m) |
    (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k m) 1 y}.ncard > 0
  rw [h3]
  positivity
theorem baseVerticesOfCube_succ_eq_biUnion (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m + 1 ≤ k)
    (y : Vertex L k (m + 1)) :
    TrivialLinearization.baseVerticesOfCube L k (m + 1) y =
        ⋃ x ∈ cubeVertices L (meshAt L k m) y,
          TrivialLinearization.baseVerticesOfCube L k m x ∧
      (cubeVertices L (meshAt L k m) y).PairwiseDisjoint
        fun x => TrivialLinearization.baseVerticesOfCube L k m x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · constructor
    · simp only [baseVerticesOfCube_zero, biUnion_of_singleton]
      rfl
    · intro x _ x' _ hne
      simpa only [Function.onFun, baseVerticesOfCube_zero] using
        disjoint_singleton.2 hne
  · have hd := (hY L hL k (m + 1) (m + 1) (by omega) (by omega) hm (by omega) le_rfl).2.1
      (by omega) y
    have h1 := hd.cube_eq_biUnion
    have h2 := hd.pairwiseDisjoint_subcube
    rw [Nat.sub_self] at h1 h2
    constructor
    · ext z
      simp only [mem_iUnion]
      change (z : AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) (m + 1) y ↔ _
      rw [h1]
      simp only [mem_iUnion]
      rfl
    · intro x hx x' hx' hne
      exact disjoint_left.2 fun z hz hz' => disjoint_left.1 (h2 hx hx' hne) hz hz'
theorem inverseFourthPowerWeight_mul {L : ℕ} (m : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L * (((L ^ (4 * m) : ℕ) : ℂ))⁻¹ =
      (((L ^ (4 * (m + 1)) : ℕ) : ℂ))⁻¹ := by
  have h : PeriodicLattice.inverseFourthPowerWeight L = ((L : ℂ) ^ 4)⁻¹ := by
    simp [PeriodicLattice.inverseFourthPowerWeight, zpow_neg]
  rw [h]
  push_cast
  rw [← mul_inv, ← pow_add]
  congr 2
  ring
theorem setAverage_of_setAverages (hY : CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m + 1 ≤ k)
    (y : Vertex L k (m + 1)) (f : Vertex L k 0 → Matrices.ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k m) y,
        setAverage (TrivialLinearization.baseVerticesOfCube L k m x) f =
      setAverage (TrivialLinearization.baseVerticesOfCube L k (m + 1) y) f := by
  have hk : 1 ≤ k := by omega
  have hm' : m ≤ k := by omega
  have hfin := finite_cubeVertices hY hL hm y
  obtain ⟨hU, hD⟩ := baseVerticesOfCube_succ_eq_biUnion hY hL hm y
  have hmean : ∀ x : Vertex L k m,
      setAverage (TrivialLinearization.baseVerticesOfCube L k m x) f =
        (((L ^ (4 * m) : ℕ) : ℂ))⁻¹ •
          ∑ᶠ z ∈ TrivialLinearization.baseVerticesOfCube L k m x, f z := by
    intro x
    simp only [setAverage]
    rw [ncard_baseVerticesOfCube hY hL hk hm' x]
  simp only [hmean]
  rw [← smul_finsum_mem hfin, smul_smul, inverseFourthPowerWeight_mul]
  simp only [setAverage]
  rw [ncard_baseVerticesOfCube hY hL hk hm y, hU,
    finsum_mem_biUnion hD hfin fun x _ => finite_baseVerticesOfCube hY hL hk hm' x]
variable {m : ℕ}
theorem edgeFormPathSum_forwardSteps (hL : 0 < L)
    (hfin : ∀ x : Vertex L k m, (TrivialLinearization.baseVerticesOfCube L k m x).Finite)
    (F : Edge L k m → Matrices.ComplexMatrix2) (B : Edge L k 0 → Matrices.ComplexMatrix2)
    (hc : ∀ c : Edge L k m,
      F c = setAverage (TrivialLinearization.baseVerticesOfCube L k m c.initial)
        fun z => edgeFormPathSum B (crossingPath c z))
    (μ : Fin 4) (N : ℕ) (x : Vertex L k m) :
    edgeFormPathSum F (forwardSteps x μ N) =
      setAverage (TrivialLinearization.baseVerticesOfCube L k m x)
        fun z => edgeFormPathSum B (forwardSteps z μ (N * L ^ m)) := by
  have ha₀ := (meshAt_pos hL k 0).ne'
  have hN := meshAt_eq_pow_mul hL k m
  refine sum_along_walk_eq_setAverage F B
    (fun x => TrivialLinearization.baseVerticesOfCube L k m x) hfin
    (fun x N => forwardSteps x μ N) (fun z N => forwardSteps z μ N)
    (fun x => Link.forwardFrom x μ) (fun x => x + axisStep (meshAt L k m) μ)
    (fun z => z + (L ^ m) • axisStep (meshAt L k 0) μ) (L ^ m)
    (fun _ => rfl) (fun _ _ => rfl) (fun z N => forwardSteps_add z μ _ _) (fun _ => rfl)
    ?_ ?_ N x
  · intro x
    rw [hc (Link.forwardFrom x μ)]
    have hstep : (Link.forwardFrom x μ).terminal - (Link.forwardFrom x μ).initial =
        axisStep (meshAt L k m) μ := by simp [Link.forwardFrom]
    simp only [crossingPath_of_forward ha₀ hN (Link.forwardFrom x μ) μ hstep]
    rfl
  · intro x f
    exact setAverage_cube_add x (axisStep (meshAt L k m) μ)
      ((L ^ m) • axisStep (meshAt L k 0) μ)
      (by rw [coe_nsmul_axisStep, ← hN]; rfl) f
theorem edgeFormPathSum_backwardSteps (hL : 0 < L)
    (hfin : ∀ x : Vertex L k m, (TrivialLinearization.baseVerticesOfCube L k m x).Finite)
    (F : Edge L k m → Matrices.ComplexMatrix2) (B : Edge L k 0 → Matrices.ComplexMatrix2)
    (hc : ∀ c : Edge L k m,
      F c = setAverage (TrivialLinearization.baseVerticesOfCube L k m c.initial)
        fun z => edgeFormPathSum B (crossingPath c z))
    (μ : Fin 4) (N : ℕ) (x : Vertex L k m) :
    edgeFormPathSum F (backwardSteps x μ N) =
      setAverage (TrivialLinearization.baseVerticesOfCube L k m x)
        fun z => edgeFormPathSum B (backwardSteps z μ (N * L ^ m)) := by
  have ha₀ := (meshAt_pos hL k 0).ne'
  have hN := meshAt_eq_pow_mul hL k m
  refine sum_along_walk_eq_setAverage F B
    (fun x => TrivialLinearization.baseVerticesOfCube L k m x) hfin
    (fun x N => backwardSteps x μ N) (fun z N => backwardSteps z μ N)
    (fun x => backwardLink x μ) (fun x => x - axisStep (meshAt L k m) μ)
    (fun z => z - (L ^ m) • axisStep (meshAt L k 0) μ) (L ^ m)
    (fun _ => rfl) (fun _ _ => rfl) (fun z N => backwardSteps_add z μ _ _) (fun _ => rfl)
    ?_ ?_ N x
  · intro x
    rw [hc (backwardLink x μ)]
    have hstep : (backwardLink x μ).terminal - (backwardLink x μ).initial =
        -axisStep (meshAt L k m) μ := by simp [backwardLink]
    simp only [crossingPath_of_backward (pow_pos hL m) ha₀ hN (backwardLink x μ) μ hstep]
    rfl
  · intro x f
    simp only [sub_eq_add_neg]
    exact setAverage_cube_add x (-axisStep (meshAt L k m) μ)
      (-((L ^ m) • axisStep (meshAt L k 0) μ))
      (by rw [AddSubgroup.coe_neg, AddSubgroup.coe_neg, coe_nsmul_axisStep, ← hN]; rfl) f
end Levels
theorem iterateAverages (hY : CubesCorridorsPivotEdgesAndPaths) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k m : ℕ) (hm : m ≤ k) :
    TrivialLinearization.IterateAverages L k m := by
  have hL0 : 0 < L := by have := hL.2; omega
  induction m with
  | zero =>
    have ha₀ := (meshAt_pos hL0 k 0).ne'
    refine ⟨fun B _ c => ?_, fun l _ y => ?_⟩
    · rw [baseVerticesOfCube_zero, setAverage_singleton]
      change B c = edgeFormPathSum B (crossingPath c c.initial)
      obtain ⟨μ, h | h⟩ := c.isAdjacent
      · rw [crossingPath_of_forward (N := 1) ha₀ (by simp) c μ h]
        have hc : c = Link.forwardFrom c.initial μ := by
          apply Link.ext
          · rfl
          · have : c.terminal = c.initial + axisStep (meshAt L k 0) μ := by rw [← h]; abel
            simp [Link.forwardFrom, this]
        simp only [forwardSteps, edgeFormPathSum, sumAlong, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        rw [← hc]
      · rw [crossingPath_of_backward (N := 1) one_pos ha₀ (by simp) c μ h]
        have hc : c = backwardLink c.initial μ := by
          apply Link.ext
          · rfl
          · have : c.terminal = c.initial + -axisStep (meshAt L k 0) μ := by rw [← h]; abel
            simp [backwardLink, this, sub_eq_add_neg]
        simp only [backwardSteps, edgeFormPathSum, sumAlong, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        rw [← hc]
    · rw [baseVerticesOfCube_zero, setAverage_singleton]
      rfl
  | succ m ih =>
    have hk : 1 ≤ k := by omega
    have hm' : m ≤ k := by omega
    have ha₀ := (meshAt_pos hL0 k 0).ne'
    have ham := (meshAt_pos hL0 k m).ne'
    obtain ⟨ih₁, ih₂⟩ := ih hm'
    have hfin := fun x : Vertex L k m => finite_baseVerticesOfCube hY hL hk hm' x
    have hs : meshAt L k (m + 1) = ((L : ℕ) : ℝ) * meshAt L k m :=
      meshAt_succ hL0 k m
    have hs₀ : meshAt L k (m + 1) = ((L ^ (m + 1) : ℕ) : ℝ) * meshAt L k 0 :=
      meshAt_eq_pow_mul hL0 k (m + 1)
    have hs₁ : meshAt L k (m + 1) = ((L * L ^ m : ℕ) : ℝ) * meshAt L k 0 := by
      rw [hs₀, pow_succ']
    refine ⟨fun B hB c => ?_, fun l hl y => ?_⟩
    · rw [← setAverage_of_setAverages hY hL hm c.initial]
      change PeriodicLattice.inverseFourthPowerWeight L •
          ∑ᶠ x ∈ cubeVertices L (meshAt L k m) c.initial,
          edgeFormPathSum (crossingSmoothingIter L k m B) (crossingPath c x) = _
      congr 1
      refine finsum_congr fun x => finsum_congr fun _ => ?_
      obtain ⟨μ, h | h⟩ := c.isAdjacent
      · rw [crossingPath_of_forward ham hs c μ h,
          edgeFormPathSum_forwardSteps hL0 hfin _ B (ih₁ B hB) μ L x]
        simp only [crossingPath_of_forward ha₀ hs₁ c μ h]
      · rw [crossingPath_of_backward hL0 ham hs c μ h,
          edgeFormPathSum_backwardSteps hL0 hfin _ B (ih₁ B hB) μ L x]
        simp only [crossingPath_of_backward (Nat.mul_pos hL0 (pow_pos hL0 m)) ha₀ hs₁ c μ h]
    · rw [← setAverage_of_setAverages hY hL hm y]
      change PeriodicLattice.inverseFourthPowerWeight L •
          ∑ᶠ x ∈ cubeVertices L (meshAt L k m) y,
          vertexSmoothingIter L k m l x = _
      congr 1
      exact finsum_congr fun x => finsum_congr fun _ => ih₂ l hl x
theorem statement_holds (hY : CubesCorridorsPivotEdgesAndPaths) : Statement := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages.iterateAverages <;> assumption
end YangMills.Construction.Tower.FullSpace.IteratesAsCubeAverages
end
