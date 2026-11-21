import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.Lattice.CosetsCoordinatesAndDistances
import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequenceProof
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import YangMills.Construction.Lattice.MixedDerivativeOfTheTotalSourceEnergyProof
import YangMills.Construction.RunningCouplingSlope.KernelsNearTheCellsAreBoundedProof
import YangMills.Construction.Torus.CoveringMapOnSmallBallsProof
import YangMills.Construction.Weighted.LayerCutoffConstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound.Coordinates
open Set TorusMetric
open PeriodicLattice hiding supNormVec
section Norms
variable {S : ℝ}
theorem zero_le_supNormVec (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
theorem abs_apply_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
theorem supNormVec_le_of_forall_abs_le {v : Fin 4 → ℝ} {r : ℝ} (hr : ∀ μ, |v μ| ≤ r) :
    supNormVec v ≤ r :=
  Finset.sup'_le _ _ fun μ _ => hr μ
theorem supNormVec_le_supNormVec_of_abs_le {u v : Fin 4 → ℝ} (huv : ∀ μ, |u μ| ≤ |v μ|) :
    supNormVec u ≤ supNormVec v :=
  supNormVec_le_of_forall_abs_le fun μ => (huv μ).trans (abs_apply_le_supNormVec v μ)
theorem euclidNormVec_le_euclidNormVec_of_abs_le {u v : Fin 4 → ℝ} (huv : ∀ μ, |u μ| ≤ |v μ|) :
    euclidNormVec u ≤ euclidNormVec v := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
theorem supNormVec_le_euclidNormVec (v : Fin 4 → ℝ) : supNormVec v ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37493 <;> assumption
theorem euclidNormVec_le_two_mul_supNormVec (v : Fin 4 → ℝ) :
    euclidNormVec v ≤ 2 * supNormVec v := by
  have hnn := zero_le_supNormVec v
  have hsq : ∀ μ, v μ ^ 2 ≤ supNormVec v ^ 2 := fun μ =>
    sq_le_sq.2 ((abs_apply_le_supNormVec v μ).trans (le_abs_self _))
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_four]
  linarith [hsq 0, hsq 1, hsq 2, hsq 3]
theorem torusProj_vec_add (u v : Fin 4 → ℝ) : torusProj S (u + v) = torusProj S u + torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_vec_sub (u v : Fin 4 → ℝ) : torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem isLeast_norms_of_abs_eq_norm {x : Torus4 S} {b : Fin 4 → ℝ} (hb : torusProj S b = x)
    (hbn : ∀ μ, |b μ| = ‖x μ‖) :
    IsLeast (supNormVec '' (torusProj S ⁻¹' {x})) (supNormVec b) ∧
      IsLeast (euclidNormVec '' (torusProj S ⁻¹' {x})) (euclidNormVec b) := by
  have hle : ∀ v : Fin 4 → ℝ, torusProj S v = x → ∀ μ, |b μ| ≤ |v μ| := fun v hv μ => by
    rw [hbn, ← hv]
    exact addCircle_norm_coe_le_abs _
  refine ⟨⟨⟨b, hb, rfl⟩, ?_⟩, ⟨⟨b, hb, rfl⟩, ?_⟩⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact supNormVec_le_supNormVec_of_abs_le (hle v hv)
  · rintro _ ⟨v, hv, rfl⟩
    exact euclidNormVec_le_euclidNormVec_of_abs_le (hle v hv)
theorem exists_lift_isLeast_norms (x : Torus4 S) :
    ∃ b : Fin 4 → ℝ, torusProj S b = x ∧ (∀ μ, |b μ| = ‖x μ‖) ∧
      IsLeast (supNormVec '' (torusProj S ⁻¹' {x})) (torusSupNorm x) ∧
      IsLeast (euclidNormVec '' (torusProj S ⁻¹' {x})) (torusEuclidNorm x) ∧
      torusSupNorm x = supNormVec b ∧ torusEuclidNorm x = euclidNormVec b := by
  choose b hb hbn using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S b = x := funext hb
  obtain ⟨hsup, heuc⟩ := isLeast_norms_of_abs_eq_norm hproj hbn
  have esup : torusSupNorm x = supNormVec b := hsup.csInf_eq
  have eeuc : torusEuclidNorm x = euclidNormVec b := heuc.csInf_eq
  exact ⟨b, hproj, hbn, esup ▸ hsup, eeuc ▸ heuc, esup, eeuc⟩
theorem torusSupNorm_le_of_torusProj_eq {x : Torus4 S} {v : Fin 4 → ℝ} (hv : torusProj S v = x) :
    torusSupNorm x ≤ supNormVec v := by apply _root_.YangMills.Construction.SeparatedSequences.AntitoneBlocks.torusSupNorm_le_of_torusProj_eq <;> assumption
theorem torusEuclidNorm_le_of_torusProj_eq {x : Torus4 S} {v : Fin 4 → ℝ}
    (hv : torusProj S v = x) : torusEuclidNorm x ≤ euclidNormVec v := by apply _root_.YangMills.Construction.TestFunctions.SmallBalls.torusEuclidNorm_le_of_proj_eq <;> assumption
theorem torusSupNorm_sub_symm (x y : Torus4 S) : torusSupNorm (x - y) = torusSupNorm (y - x) := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.torusSupNorm_sub_comm <;> assumption
theorem torusEuclidNorm_sub_symm (x y : Torus4 S) :
    torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm <;> assumption
theorem torusSupNorm_add_le_add (x y : Torus4 S) :
    torusSupNorm (x + y) ≤ torusSupNorm x + torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem torusEuclidNorm_add_le_add (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
theorem torusSupNorm_eq_pi_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem continuous_torusProj_vec : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
end Norms
section Level
variable {D : Setup} {j : ℕ}
theorem blockingFactor_cast_pos (D : Setup) : (0 : ℝ) < (D.L : ℝ) := by apply _root_.YangMills.Construction.TotalEnergyDerivative.Estimates.L_cast_pos <;> assumption
theorem meshSize_depthOf_pos (D : Setup) (j : ℕ) : 0 < meshSize D.L (D.depthOf j) :=
  zpow_pos (blockingFactor_cast_pos D) _
theorem physicalCubeSide_pos (D : Setup) (j : ℕ) : 0 < D.physicalCubeSide j := by
  have hM : (0 : ℝ) < (D.cubeSide : ℝ) := by
    have := blockingFactor_cast_pos D
    simp only [Setup.cubeSide, Nat.cast_pow]
    positivity
  exact mul_pos hM (meshSize_depthOf_pos D j)
theorem setup_side_pos (D : Setup) : 0 < D.side := by
  have := blockingFactor_cast_pos D
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  positivity
theorem exists_side_eq_physicalCubeSide_mul (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : ∃ n : ℤ, D.side = D.physicalCubeSide j * (n : ℝ) := by
  have hT := (H.2.2 (D.levelUnitPartition hj h)).1
  have hn : _root_.YangMills.Construction.PeriodicLattice.CubeLifts.scaledTorusSide (D.levelUnitPartition hj h) =
      ((D.levelUnitPartition hj h).cubeCount : ℝ) * ((D.levelUnitPartition hj h).side : ℝ) :=
    hT.2.2.2.2.2.1
  have hM : ((D.levelUnitPartition hj h).side : ℝ) = (D.cubeSide : ℝ) := rfl
  have hu : D.side * (D.L : ℝ) ^ D.depthOf j =
      ((D.levelUnitPartition hj h).cubeCount : ℝ) * (D.cubeSide : ℝ) := by
    rw [← hM, ← hn]
    rfl
  have ha : meshSize D.L (D.depthOf j) * (D.L : ℝ) ^ D.depthOf j = 1 := by
    rw [meshSize, zpow_neg]
    exact inv_mul_cancel₀ (zpow_pos (blockingFactor_cast_pos D) _).ne'
  refine ⟨((D.levelUnitPartition hj h).cubeCount : ℤ), ?_⟩
  have : D.side = (D.side * (D.L : ℝ) ^ D.depthOf j) * meshSize D.L (D.depthOf j) := by
    rw [mul_assoc, mul_comm ((D.L : ℝ) ^ D.depthOf j), ha, mul_one]
  rw [this, hu]
  simp only [Setup.physicalCubeSide, Int.cast_natCast]
  ring
theorem torusCover_eq_of_isLiftOfPoint {y : D.Torus} {w w' : Fin 4 → ℝ}
    (hw : D.IsLiftOfPoint y w) (hw' : D.IsLiftOfPoint y w') : D.torusCover w' = D.torusCover w :=
  (show D.torusCover w' = y from hw').trans (show D.torusCover w = y from hw).symm
theorem exists_coord_eq_add_physicalCubeSide_mul {n : ℤ}
    (hn : D.side = D.physicalCubeSide j * (n : ℝ)) {w w' : Fin 4 → ℝ}
    (hc : D.torusCover w' = D.torusCover w) (μ : Fin 4) :
    ∃ r : ℤ, w' μ = w μ + D.physicalCubeSide j * (r : ℝ) := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hc
  refine ⟨n * k μ, ?_⟩
  have hμ : w' μ = w μ + D.side * (k μ : ℝ) := congrFun hk μ
  rw [hμ, hn]
  push_cast
  ring
theorem isGridPoint_add_mul_int {σ t : ℝ} (ht : IsGridPoint σ t) (r : ℤ) :
    IsGridPoint σ (t + σ * (r : ℝ)) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨a + r, by push_cast; ring⟩
theorem cosetProperties_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : CosetProperties D j := by
  obtain ⟨n, hn⟩ := exists_side_eq_physicalCubeSide_mul H hj h
  have hσ := physicalCubeSide_pos D j
  have hlt : D.physicalCubeSide j < D.side := by
    have hp : D.physicalCubeSide j ≤ D.side / 2 := h
    linarith [setup_side_pos D]
  refine ⟨⟨n, hn⟩, hσ, hlt, ?_, ?_, ?_⟩
  · ext t
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a + n, by rw [hn]; push_cast; ring⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a - n, rfl⟩, by rw [hn]; push_cast; ring⟩
  · ext t
    constructor
    · rintro ⟨_, ht, rfl⟩
      have := isGridPoint_add_mul_int ht n
      rwa [← hn] at this
    · intro ht
      refine ⟨t + D.physicalCubeSide j * ((-n : ℤ) : ℝ), isGridPoint_add_mul_int ht (-n), ?_⟩
      show t + D.physicalCubeSide j * ((-n : ℤ) : ℝ) + D.side = t
      rw [hn]
      push_cast
      ring
  · intro C hC y μ w w' hw hw' hmem
    obtain ⟨r, hr⟩ :=
      exists_coord_eq_add_physicalCubeSide_mul hn (torusCover_eq_of_isLiftOfPoint hw hw') μ
    simp only [mem_insert_iff, mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · obtain ⟨a, ha⟩ := hmem
      exact ⟨a + r, by rw [hr, ha]; push_cast; ring⟩
    · rw [hr]
      exact isGridPoint_add_mul_int hmem r
theorem centreLifts_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : CentreLifts D j := by
  obtain ⟨n, hn⟩ := exists_side_eq_physicalCubeSide_mul H hj h
  intro w
  constructor
  · rintro ⟨c, hc⟩ μ
    obtain ⟨a, ha⟩ := c.2
    have hu : D.torusCover (fun μ => (a μ : ℝ) * meshSize D.L (D.cubeScaleIndex j)) =
        (c : D.Torus) :=
      funext fun μ => (ha μ).symm
    obtain ⟨r, hr⟩ := exists_coord_eq_add_physicalCubeSide_mul hn (hc.trans hu.symm) μ
    refine ⟨a μ + r, ?_⟩
    rw [hr, ← Setup.cubeSide_mul_meshSize]
    simp only [Setup.physicalCubeSide, Int.cast_add]
    ring
  · intro hw
    choose a ha using hw
    refine ⟨⟨D.torusCover w, a, fun μ => ?_⟩, rfl⟩
    show ((w μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = _
    rw [ha μ, mul_comm, ← Setup.cubeSide_mul_meshSize]
theorem cubeMembershipByLifts_holds (D : Setup) (j : ℕ) : CubeMembershipByLifts D j := by
  intro c w hw y
  have hmem : y ∈ D.cubeCentredAt c ↔
      torusSupNorm (y - (c : D.Torus)) ≤ D.physicalCubeSide j / 2 := by
    show torusSupNorm (y - (c : D.Torus)) ≤ meshSize D.L (D.cubeScaleIndex j) / 2 ↔ _
    rw [← Setup.cubeSide_mul_meshSize]
  rw [hmem]
  constructor
  · intro hle
    obtain ⟨b, hb, -, -, -, e, -⟩ := exists_lift_isLeast_norms (y - (c : D.Torus))
    refine ⟨w + b, ?_, fun μ => ?_⟩
    · have hwc : torusProj (PeriodicLattice.torusSide D.L D.m) w = (c : D.Torus) := hw
      show torusProj (PeriodicLattice.torusSide D.L D.m) (w + b) = y
      rw [torusProj_vec_add, hb, hwc]
      abel
    · have hμ : |b μ| ≤ D.physicalCubeSide j / 2 := (abs_apply_le_supNormVec b μ).trans (e ▸ hle)
      have hbμ : (w + b - w) μ = b μ := by simp
      rw [hbμ]
      exact abs_le.1 hμ
  · rintro ⟨w', hw', hI⟩
    have hc : torusProj (PeriodicLattice.torusSide D.L D.m) (w' - w) = y - (c : D.Torus) := by
      rw [torusProj_vec_sub]
      exact congrArg₂ _ hw' hw
    exact (torusSupNorm_le_of_torusProj_eq hc).trans
      (supNormVec_le_of_forall_abs_le fun μ => abs_le.2 (hI μ))
theorem isPointLift_iff_isLiftOfPoint (hj : j ≤ D.K) (h : D.LevelFits j) (x : D.Torus)
    (w : Fin 4 → ℝ) :
    (D.levelUnitPartition hj h).IsPointLift x w ↔
      D.IsLiftOfPoint x (meshSize D.L (D.depthOf j) • w) := by
  have hL : D.L ≠ 0 := by
    have := D.isAdmissible.2
    omega
  exact (levelProj_eq_iff_isLevelLift hL _ _ _ x w).symm
theorem mem_vertexSet_iff_isGridPoint (hj : j ≤ D.K) (h : D.LevelFits j) (w : Fin 4 → ℝ) :
    w ∈ (D.levelUnitPartition hj h).vertexSet ↔
      ∀ μ, IsGridPoint (D.physicalCubeSide j) ((meshSize D.L (D.depthOf j) • w) μ) := by
  have ha := meshSize_depthOf_pos D j
  have hM : ((D.levelUnitPartition hj h).side : ℝ) = (D.cubeSide : ℝ) := rfl
  refine forall_congr' fun μ => exists_congr fun a => ?_
  rw [hM]
  simp only [Pi.smul_apply, smul_eq_mul, Setup.physicalCubeSide]
  constructor
  · intro e
    rw [e]
    ring
  · intro e
    apply mul_left_cancel₀ ha.ne'
    rw [e]
    ring
theorem meshSize_smul_inv_smul (D : Setup) (j : ℕ) (w : Fin 4 → ℝ) :
    meshSize D.L (D.depthOf j) • (meshSize D.L (D.depthOf j))⁻¹ • w = w :=
  smul_inv_smul₀ (meshSize_depthOf_pos D j).ne' w
theorem cubeVerticesByLifts_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : CubeVerticesByLifts hj h := by
  have hS := (H.2.2 (D.levelUnitPartition hj h)).2.2.1
  have hM : ((D.levelUnitPartition hj h).side : ℝ) = (D.cubeSide : ℝ) := rfl
  intro c w hw v
  constructor
  · rintro ⟨y, hy, c', hc', ε, hε, rfl⟩
    have hyc : y = c := by
      by_contra hne
      exact hS.2.2.1 y c hne hy.symm
    subst hyc
    refine ⟨ε, hε, ?_⟩
    have hl := (isPointLift_iff_isLiftOfPoint hj h _ _).1 hc'
    obtain ⟨k, hk⟩ :=
      TestFunctions.exists_latticeTranslate_of_torusProj_eq (torusCover_eq_of_isLiftOfPoint hw hl)
    rw [Setup.proj_levelUnitPartition, smul_add, hk, add_right_comm, Setup.torusCover,
      TestFunctions.torusProj_add_latticeTranslate, smul_smul, hM]
    congr 3
    ring
  · rintro ⟨ε, hε, rfl⟩
    refine ⟨c, rfl, (meshSize D.L (D.depthOf j))⁻¹ • w, ?_, ε, hε, ?_⟩
    · rw [isPointLift_iff_isLiftOfPoint, meshSize_smul_inv_smul]
      exact hw
    · rw [Setup.proj_levelUnitPartition, smul_add, meshSize_smul_inv_smul, smul_smul, hM]
      congr 3
      ring
theorem isHalfIntegralCoord_torusCover_iff (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (μ : Fin 4) (u : Fin 4 → ℝ) :
    D.IsHalfIntegralCoord j μ (D.torusCover u) ↔ IsGridPoint (D.physicalCubeSide j) (u μ) := by
  obtain ⟨n, hn⟩ := exists_side_eq_physicalCubeSide_mul H hj h
  refine ⟨fun hh => hh u rfl, fun hu w hw => ?_⟩
  obtain ⟨r, hr⟩ := exists_coord_eq_add_physicalCubeSide_mul hn hw μ
  rw [hr]
  exact isGridPoint_add_mul_int hu r
theorem isLevelVertex_iff_exists_grid_lift (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (v : D.Torus) :
    D.IsLevelVertex hj h v ↔
      ∃ w : Fin 4 → ℝ, (∀ μ, IsGridPoint (D.physicalCubeSide j) (w μ)) ∧ v = D.torusCover w := by
  have hV := (H.2.2 (D.levelUnitPartition hj h)).2.2.2.1
  refine (hV.1 v).trans ?_
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, (mem_vertexSet_iff_isGridPoint hj h w).1 hw, Setup.proj_levelUnitPartition hj h w⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(meshSize D.L (D.depthOf j))⁻¹ • w, (mem_vertexSet_iff_isGridPoint hj h _).2 ?_, ?_⟩
    · rwa [meshSize_smul_inv_smul]
    · rw [Setup.proj_levelUnitPartition, meshSize_smul_inv_smul]
theorem vertexIffHalfIntegral_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : VertexIffHalfIntegral hj h := by
  intro v
  rw [isLevelVertex_iff_exists_grid_lift H hj h]
  constructor
  · rintro ⟨w, hw, rfl⟩ μ
    exact (isHalfIntegralCoord_torusCover_iff H hj h μ w).2 (hw μ)
  · intro hv
    exact ⟨TestFunctions.liftPoint v, fun μ => hv μ _ (TestFunctions.torusProj_liftPoint v),
      (TestFunctions.torusProj_liftPoint v).symm⟩
theorem isLevelEdge_iff_exists_grid_lift (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (A : Set D.Torus) :
    D.IsLevelEdge hj h A ↔
      ∃ (w : Fin 4 → ℝ) (ν : Fin 4), (∀ μ, IsGridPoint (D.physicalCubeSide j) (w μ)) ∧
        A = D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν := by
  have hV := (H.2.2 (D.levelUnitPartition hj h)).2.2.2.1
  refine (hV.2.2.1 A).trans ?_
  constructor
  · rintro ⟨w, hw, ν, rfl⟩
    exact ⟨_, ν, (mem_vertexSet_iff_isGridPoint hj h w).1 hw,
      Setup.edgeAt_levelUnitPartition hj h w ν⟩
  · rintro ⟨w, ν, hw, rfl⟩
    refine ⟨(meshSize D.L (D.depthOf j))⁻¹ • w, (mem_vertexSet_iff_isGridPoint hj h _).2 ?_, ν, ?_⟩
    · rwa [meshSize_smul_inv_smul]
    · rw [Setup.edgeAt_levelUnitPartition, meshSize_smul_inv_smul]
theorem isEdgeAxis_iff_exists_grid_lift (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (ν : Fin 4) (A : Set D.Torus) :
    D.IsEdgeAxis hj h ν A ↔
      ∃ w : Fin 4 → ℝ, (∀ μ, IsGridPoint (D.physicalCubeSide j) (w μ)) ∧
        A = D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν := by
  constructor
  · rintro ⟨v, w, hv, hw, rfl⟩
    exact ⟨w, fun μ => (vertexIffHalfIntegral_of_cubeLifts H hj h v).1 hv μ w hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨D.torusCover w, w, (isLevelVertex_iff_exists_grid_lift H hj h _).2 ⟨w, hw, rfl⟩,
      rfl, rfl⟩
theorem isEdgeEndpoint_iff_exists_grid_lift (hj : j ≤ D.K)
    (h : D.LevelFits j) (A : Set D.Torus) (x : D.Torus) :
    (D.levelUnitPartition hj h).IsEdgeEndpoint A x ↔
      ∃ (w : Fin 4 → ℝ) (ν : Fin 4), (∀ μ, IsGridPoint (D.physicalCubeSide j) (w μ)) ∧
        A = D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν ∧
        (x = D.torusCover w ∨ x = D.torusCover (w + D.physicalCubeSide j • coordVec ν)) := by
  have hM : ((D.levelUnitPartition hj h).side : ℝ) = (D.cubeSide : ℝ) := rfl
  have hproj : ∀ (w : Fin 4 → ℝ) (ν : Fin 4),
      (D.levelUnitPartition hj h).proj (w + ((D.levelUnitPartition hj h).side : ℝ) •
        coordVec ν) =
      D.torusCover (meshSize D.L (D.depthOf j) • w + D.physicalCubeSide j • coordVec ν) := by
    intro w ν
    rw [Setup.proj_levelUnitPartition, smul_add, smul_smul, hM, mul_comm]
  constructor
  · rintro ⟨w, hw, ν, rfl, hx⟩
    refine ⟨_, ν, (mem_vertexSet_iff_isGridPoint hj h w).1 hw,
      Setup.edgeAt_levelUnitPartition hj h w ν, ?_⟩
    rcases hx with rfl | rfl
    · exact Or.inl (Setup.proj_levelUnitPartition hj h w)
    · exact Or.inr (hproj w ν)
  · rintro ⟨w, ν, hw, rfl, hx⟩
    refine ⟨(meshSize D.L (D.depthOf j))⁻¹ • w, (mem_vertexSet_iff_isGridPoint hj h _).2 ?_, ν,
      ?_, ?_⟩
    · rwa [meshSize_smul_inv_smul]
    · rw [Setup.edgeAt_levelUnitPartition, meshSize_smul_inv_smul]
    · rcases hx with rfl | rfl
      · left
        rw [Setup.proj_levelUnitPartition, meshSize_smul_inv_smul]
      · right
        rw [hproj, meshSize_smul_inv_smul]
theorem add_smul_coordVec_apply_of_ne (w : Fin 4 → ℝ) (t : ℝ) {μ ν : Fin 4} (hμ : μ ≠ ν) :
    (w + t • coordVec ν) μ = w μ := by
  simp [coordVec, Pi.single_eq_of_ne hμ]
theorem add_smul_coordVec_apply_self (w : Fin 4 → ℝ) (t : ℝ) (ν : Fin 4) :
    (w + t • coordVec ν) ν = w ν + t := by
  simp [coordVec]
theorem eq_zero_or_eq_of_isGridPoint_add {σ g t : ℝ} (hσ : 0 < σ) (hg : IsGridPoint σ g)
    (hgt : IsGridPoint σ (g + t)) (h0 : 0 ≤ t) (h1 : t ≤ σ) : t = 0 ∨ t = σ := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb⟩ := hgt
  have ht : t = σ * ((b - a : ℤ) : ℝ) := by
    push_cast
    linear_combination hb - ha
  have hn0 : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
    rw [ht] at h0
    exact (mul_nonneg_iff_of_pos_left hσ).1 h0
  have hn1 : ((b - a : ℤ) : ℝ) ≤ 1 := by
    rw [ht] at h1
    exact le_of_mul_le_mul_left (by simpa using h1) hσ
  have hn0' : 0 ≤ b - a := by exact_mod_cast hn0
  have hn1' : b - a ≤ 1 := by exact_mod_cast hn1
  obtain e | e : b - a = 0 ∨ b - a = 1 := by omega
  · left
    rw [ht, e]
    simp
  · right
    rw [ht, e]
    simp
theorem edgeParametrization_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : EdgeParametrization hj h :=
  fun A => isLevelEdge_iff_exists_grid_lift H hj h A
theorem mem_and_isHalfIntegralCoord_of_isEdgeEndpoint (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) {A : Set D.Torus} {x : D.Torus}
    (hx : (D.levelUnitPartition hj h).IsEdgeEndpoint A x) :
    x ∈ A ∧ ∀ μ, D.IsHalfIntegralCoord j μ x := by
  obtain ⟨w, ν, hw, hA, e⟩ := (isEdgeEndpoint_iff_exists_grid_lift hj h A x).1 hx
  have hσ := physicalCubeSide_pos D j
  clear hx
  subst hA
  rcases e with e | e
  · subst e
    exact ⟨⟨w, ⟨0, le_rfl, hσ.le, by simp⟩, rfl⟩,
      fun μ => (isHalfIntegralCoord_torusCover_iff H hj h μ w).2 (hw μ)⟩
  · subst e
    refine ⟨⟨_, ⟨D.physicalCubeSide j, hσ.le, le_rfl, rfl⟩, rfl⟩, fun μ => ?_⟩
    refine (isHalfIntegralCoord_torusCover_iff H hj h μ _).2 ?_
    by_cases hμ : μ = ν
    · subst hμ
      rw [add_smul_coordVec_apply_self]
      simpa using isGridPoint_add_mul_int (hw μ) 1
    · rw [add_smul_coordVec_apply_of_ne _ _ hμ]
      exact hw μ
theorem edgeCoordinates_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : EdgeCoordinates hj h := by
  intro A ν _ hd
  obtain ⟨w, hw, rfl⟩ := (isEdgeAxis_iff_exists_grid_lift H hj h ν A).1 hd
  have hσ := physicalCubeSide_pos D j
  refine ⟨fun μ hμ => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨_, ⟨t, -, -, rfl⟩, rfl⟩ _ ⟨_, ⟨t', -, -, rfl⟩, rfl⟩
    show (((w + t • coordVec ν) μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
      (((w + t' • coordVec ν) μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m))
    rw [add_smul_coordVec_apply_of_ne _ _ hμ, add_smul_coordVec_apply_of_ne _ _ hμ]
  · rintro _ ⟨_, ⟨t, -, -, rfl⟩, rfl⟩
    refine (isHalfIntegralCoord_torusCover_iff H hj h μ _).2 ?_
    rw [add_smul_coordVec_apply_of_ne _ _ hμ]
    exact hw μ
  · rintro _ ⟨_, ⟨t, ht0, ht, rfl⟩, rfl⟩
    constructor
    · intro hh
      have hg := (isHalfIntegralCoord_torusCover_iff H hj h ν _).1 hh
      rw [add_smul_coordVec_apply_self] at hg
      refine (isEdgeEndpoint_iff_exists_grid_lift hj h _ _).2 ⟨w, ν, hw, rfl, ?_⟩
      rcases eq_zero_or_eq_of_isGridPoint_add hσ (hw ν) hg ht0 ht with rfl | rfl
      · left
        exact congrArg D.torusCover (by simp)
      · right
        rfl
    · intro he
      exact (mem_and_isHalfIntegralCoord_of_isEdgeEndpoint H hj h he).2 ν
theorem edgeAxisUnique_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : EdgeAxisUnique hj h := by
  intro A hA
  obtain ⟨w, ν, hw, rfl⟩ := (isLevelEdge_iff_exists_grid_lift H hj h A).1 hA
  have hσ := physicalCubeSide_pos D j
  refine ⟨ν, (isEdgeAxis_iff_exists_grid_lift H hj h ν _).2 ⟨w, hw, rfl⟩, fun ν' hd' => ?_⟩
  by_contra hne
  have hc := edgeCoordinates_of_cubeLifts H hj h _ ν' hA hd'
  have hmid : D.torusCover (w + (D.physicalCubeSide j / 2) • coordVec ν) ∈
      D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν :=
    ⟨_, ⟨D.physicalCubeSide j / 2, by positivity, by linarith, rfl⟩, rfl⟩
  have hh := (hc.1 ν (Ne.symm hne)).2 _ hmid
  have hg := (isHalfIntegralCoord_torusCover_iff H hj h ν _).1 hh
  rw [add_smul_coordVec_apply_self] at hg
  rcases eq_zero_or_eq_of_isGridPoint_add hσ (hw ν)
    (by
      obtain ⟨a, ha⟩ := hg
      obtain ⟨b, hb⟩ := hw ν
      exact absurd (show (2 : ℤ) * (a - b) = 1 by
        have h2 : D.physicalCubeSide j * (2 * ((a : ℝ) - b) - 1) = 0 := by
          linear_combination (-2 : ℝ) * ha + 2 * hb
        have h3 : 2 * ((a : ℝ) - b) - 1 = 0 := (mul_eq_zero.1 h2).resolve_left hσ.ne'
        have h4 : (2 : ℝ) * ((a : ℝ) - b) = 1 := by linarith
        exact_mod_cast h4) (by omega))
    (by positivity : (0 : ℝ) ≤ D.physicalCubeSide j / 2) (by linarith) with e | e <;> linarith
theorem edgeEndpointsByLifts_of_cubeLifts (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) : EdgeEndpointsByLifts hj h := by
  intro w ν hw
  have hσ := physicalCubeSide_pos D j
  have hlt : D.physicalCubeSide j < D.side := (cosetProperties_of_cubeLifts H hj h).2.2.1
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨⟨_, ⟨t, ht0, ht, rfl⟩, rfl⟩, hhalf⟩ :=
        mem_and_isHalfIntegralCoord_of_isEdgeEndpoint H hj h hx
      have hg := (isHalfIntegralCoord_torusCover_iff H hj h ν _).1 (hhalf ν)
      rw [add_smul_coordVec_apply_self] at hg
      rcases eq_zero_or_eq_of_isGridPoint_add hσ (hw ν) hg ht0 ht with rfl | rfl
      · left
        exact congrArg D.torusCover (by simp)
      · right
        rfl
    · rintro (rfl | rfl)
      · exact (isEdgeEndpoint_iff_exists_grid_lift hj h _ _).2 ⟨w, ν, hw, rfl, Or.inl rfl⟩
      · exact (isEdgeEndpoint_iff_exists_grid_lift hj h _ _).2 ⟨w, ν, hw, rfl, Or.inr rfl⟩
  · intro heq
    obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq heq.symm
    have hν : w ν + D.physicalCubeSide j = w ν + D.side * (k ν : ℝ) := by
      have := congrFun hk ν
      rwa [add_smul_coordVec_apply_self] at this
    have hk' : D.physicalCubeSide j = D.side * (k ν : ℝ) := by linarith
    have hs := setup_side_pos D
    have h0 : (0 : ℝ) < (k ν : ℝ) := by
      rw [hk'] at hσ
      exact (mul_pos_iff_of_pos_left hs).1 hσ
    have h1 : (k ν : ℝ) < 1 := by
      rw [hk'] at hlt
      exact lt_of_mul_lt_mul_left (by simpa using hlt) hs.le
    have h0' : 0 < k ν := by exact_mod_cast h0
    have h1' : k ν < 1 := by exact_mod_cast h1
    omega
theorem isSupClosed_of_isLevelEdge (H : CubeLifts.Statement) (hj : j ≤ D.K)
    (h : D.LevelFits j) (A : Set D.Torus) (hA : D.IsLevelEdge hj h A) :
    IsSupClosed D A := by
  obtain ⟨w, ν, -, rfl⟩ := (isLevelEdge_iff_exists_grid_lift H hj h A).1 hA
  have himage : D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν =
      (fun t : ℝ => D.torusCover (w + t • coordVec ν)) '' Icc 0 (D.physicalCubeSide j) := by
    ext y
    constructor
    · rintro ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
      exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
  have hcont : Continuous fun t : ℝ => D.torusCover (w + t • coordVec ν) :=
    continuous_torusProj_vec.comp (by fun_prop)
  have hclosed : IsClosed (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) := by
    rw [himage]
    exact (isCompact_Icc.image hcont).isClosed
  intro x hx
  refine hclosed.closure_subset_iff.2 subset_rfl (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨a, ha, hlt⟩ := hx ε hε
  exact ⟨a, ha, by rw [dist_eq_norm, ← torusSupNorm_eq_pi_norm]; exact hlt⟩
theorem cosetsAndDistancesStatement_of_cubeLifts (H : CubeLifts.Statement) :
    CosetsAndDistancesStatement := by
  intro D j hj h
  refine ⟨cosetProperties_of_cubeLifts H hj h, centreLifts_of_cubeLifts H hj h,
    cubeMembershipByLifts_holds D j, cubeVerticesByLifts_of_cubeLifts H hj h,
    vertexIffHalfIntegral_of_cubeLifts H hj h, edgeParametrization_of_cubeLifts H hj h,
    edgeAxisUnique_of_cubeLifts H hj h, edgeCoordinates_of_cubeLifts H hj h,
    edgeEndpointsByLifts_of_cubeLifts H hj h, ?_, ?_, ?_, ?_, isSupClosed_of_isLevelEdge H hj h⟩
  · intro x
    obtain ⟨b, -, -, h₁, h₂, -⟩ := exists_lift_isLeast_norms x
    exact ⟨h₁, h₂⟩
  · intro x
    obtain ⟨b, -, -, -, -, e₁, e₂⟩ := exists_lift_isLeast_norms x
    rw [e₁, e₂]
    exact ⟨supNormVec_le_euclidNormVec b, euclidNormVec_le_two_mul_supNormVec b⟩
  · intro x y z
    refine ⟨torusSupNorm_sub_symm x y, torusEuclidNorm_sub_symm x y, ?_, ?_, fun h0 => ?_⟩
    · simpa using torusSupNorm_add_le_add (x - y) (y - z)
    · simpa using torusEuclidNorm_add_le_add (x - y) (y - z)
    · rw [torusSupNorm_eq_pi_norm] at h0
      exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  · intro u v
    exact ⟨torusSupNorm_le_of_torusProj_eq (torusProj_vec_sub u v),
      torusEuclidNorm_le_of_torusProj_eq (torusProj_vec_sub u v)⟩
end Level
end YangMills.Construction.TorusBound.Coordinates
end
