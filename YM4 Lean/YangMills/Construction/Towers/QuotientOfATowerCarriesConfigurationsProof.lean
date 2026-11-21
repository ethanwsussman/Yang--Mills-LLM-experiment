import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPaths
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.QuotientMapOnBondsProof
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurations
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FieldProjection
variable {L n k i : ℕ}
theorem familyDiameter_eq_of_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → Matrices.ComplexMatrix2} {V' : ι' → Matrices.ComplexMatrix2}
    (h : ∀ s, V' (e s) = V s) :
    Matrices.ComplexMatrix2.familyDiameter V = Matrices.ComplexMatrix2.familyDiameter V' := by
  unfold Matrices.ComplexMatrix2.familyDiameter
  refine Eq.trans ?_ ((e.prodCongr e).iSup_comp
    (g := fun p : ι' × ι' => Matrices.ComplexMatrix2.operatorNorm (V' p.1 * (V' p.2)⁻¹ - 1)))
  exact iSup_congr fun p => by simp [h]
theorem complexLogMean_eq_of_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → Matrices.ComplexMatrix2} {V' : ι' → Matrices.ComplexMatrix2}
    (h : ∀ s, V' (e s) = V s) :
    PeriodicLattice.complexLogMean V = PeriodicLattice.complexLogMean V' := by
  have h' : ∀ s', V' s' = V (e.symm s') := fun s' => by rw [← h, e.apply_symm_apply]
  have hmean : ∀ W, Matrices.ComplexMatrix2.IsLogMean PeriodicLattice.complexGaugeGroup V W ↔
      Matrices.ComplexMatrix2.IsLogMean PeriodicLattice.complexGaugeGroup V' W := by
    intro W
    unfold Matrices.ComplexMatrix2.IsLogMean
    refine and_congr_right fun _ => and_congr ?_ ?_
    · exact ⟨fun a s' => by rw [h']; exact a _, fun a s => by rw [← h]; exact a _⟩
    · rw [Fintype.sum_equiv e (fun s => Matrices.ComplexMatrix2.logSeries (V s * W⁻¹))
        (fun s => Matrices.ComplexMatrix2.logSeries (V' s * W⁻¹)) (fun s => by rw [h])]
  have hnear : ∀ W, (∃ s, Matrices.ComplexMatrix2.operatorNorm (V s * W⁻¹ - 1) ≤
        PeriodicLattice.complexMeanTolerance) ↔
      ∃ s', Matrices.ComplexMatrix2.operatorNorm (V' s' * W⁻¹ - 1) ≤
        PeriodicLattice.complexMeanTolerance := by
    intro W
    exact ⟨fun ⟨s, hs⟩ => ⟨e s, by rw [h]; exact hs⟩,
      fun ⟨s', hs⟩ => ⟨e.symm s', by rw [← h']; exact hs⟩⟩
  unfold PeriodicLattice.complexLogMean
  congr 1
  funext W
  exact propext (and_congr (hmean W) (hnear W))
theorem exists_orderEquiv_of_eq {S S' : Finset (Fin 4)} (h : S = S') :
    ∃ e : (Fin S.card ≃ S) ≃ (Fin S'.card ≃ S'), ∀ σ,
      (List.finRange S'.card).map (fun s => ((e σ s : S') : Fin 4)) =
        (List.finRange S.card).map (fun s => ((σ s : S) : Fin 4)) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.exists_ordering_equiv <;> assumption
def projVertexHom (L n k i : ℕ) : FullSpace.Vertex L k i →+ Tower.Vertex L n k i :=
  AddMonoidHom.mk' (FullSpace.projVertex L n k i) fun x y =>
    Subtype.ext (funext fun μ => by simp [FullSpace.projVertex, TorusMetric.torusProj])
theorem projVertex_axisStep (μ : Fin 4) :
    FullSpace.projVertex L n k i (InfiniteLattice.axisStep (Tower.meshAt L k i) μ) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_axisStep <;> assumption
theorem projVertex_add_axisStep (x : FullSpace.Vertex L k i) (μ : Fin 4) :
    FullSpace.projVertex L n k i (x + InfiniteLattice.axisStep (Tower.meshAt L k i) μ) =
      FullSpace.projVertex L n k i x +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
  rw [← projVertex_axisStep]
  exact map_add (projVertexHom L n k i) _ _
theorem projVertex_sub_axisStep (x : FullSpace.Vertex L k i) (μ : Fin 4) :
    FullSpace.projVertex L n k i (x - InfiniteLattice.axisStep (Tower.meshAt L k i) μ) =
      FullSpace.projVertex L n k i x -
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
  rw [← projVertex_axisStep]
  exact map_sub (projVertexHom L n k i) _ _
theorem projVertex_add_zsmul_axisStep (x : FullSpace.Vertex L k i) (μ : Fin 4) (m : ℤ) :
    FullSpace.projVertex L n k i (x + m • InfiniteLattice.axisStep (Tower.meshAt L k i) μ) =
      FullSpace.projVertex L n k i x +
        m • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
  rw [← projVertex_axisStep]
  have h1 := map_add (projVertexHom L n k i) x (m • InfiniteLattice.axisStep (Tower.meshAt L k i) μ)
  rw [map_zsmul] at h1
  exact h1
def ProjEdgeEndpoints (L n k i : ℕ) : Prop :=
  ∀ b : FullSpace.Edge L k i,
    (FullSpace.projEdge L n k i b).source = FullSpace.projVertex L n k i b.initial ∧
      (FullSpace.projEdge L n k i b).target = FullSpace.projVertex L n k i b.terminal
theorem projEdge_forwardFrom (hB : ProjEdgeEndpoints L n k i) (x : FullSpace.Vertex L k i)
    (μ : Fin 4) :
    FullSpace.projEdge L n k i (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (FullSpace.projVertex L n k i x) μ :=
  PeriodicLattice.Bond.ext (hB _).1 ((hB _).2.trans (projVertex_add_axisStep x μ))
theorem projEdge_backwardLink (hB : ProjEdgeEndpoints L n k i) (x : FullSpace.Vertex L k i)
    (μ : Fin 4) :
    FullSpace.projEdge L n k i (FullSpace.backwardLink x μ) =
      PeriodicLattice.Bond.backwardFrom (FullSpace.projVertex L n k i x) μ :=
  PeriodicLattice.Bond.ext (hB _).1 ((hB _).2.trans (projVertex_sub_axisStep x μ))
theorem map_forwardSteps (hB : ProjEdgeEndpoints L n k i) (x : FullSpace.Vertex L k i)
    (μ : Fin 4) (m : ℕ) :
    (FullSpace.forwardSteps x μ m).map (FullSpace.projEdge L n k i) =
      PeriodicLattice.forwardAxisPath (FullSpace.projVertex L n k i x) μ m := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [FullSpace.forwardSteps, PeriodicLattice.forwardAxisPath, List.map_cons, ih,
      projEdge_forwardFrom hB, projVertex_add_axisStep]
theorem map_backwardSteps (hB : ProjEdgeEndpoints L n k i) (x : FullSpace.Vertex L k i)
    (μ : Fin 4) (m : ℕ) :
    (FullSpace.backwardSteps x μ m).map (FullSpace.projEdge L n k i) =
      PeriodicLattice.backwardAxisPath (FullSpace.projVertex L n k i x) μ m := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [FullSpace.backwardSteps, PeriodicLattice.backwardAxisPath, List.map_cons, ih,
      projEdge_backwardLink hB, projVertex_sub_axisStep]
theorem map_signedSteps (hB : ProjEdgeEndpoints L n k i) (x : FullSpace.Vertex L k i)
    (μ : Fin 4) (m : ℤ) :
    (FullSpace.signedSteps x μ m).map (FullSpace.projEdge L n k i) =
      PeriodicLattice.flowAlong (FullSpace.projVertex L n k i x) μ m := by
  unfold FullSpace.signedSteps PeriodicLattice.flowAlong
  split_ifs
  · exact map_forwardSteps hB x μ _
  · exact map_backwardSteps hB x μ _
theorem projPath_stepsInOrder (hB : ProjEdgeEndpoints L n k i) (ν : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k i) (l : List (Fin 4)) :
    FullSpace.projPath L n k i (FullSpace.stepsInOrder ν x l) =
      PeriodicLattice.stepsThroughAxes ν (FullSpace.projVertex L n k i x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    have h := ih (x + ν μ • InfiniteLattice.axisStep (Tower.meshAt L k i) μ)
    unfold FullSpace.projPath at h ⊢
    simp only [FullSpace.stepsInOrder, PeriodicLattice.stepsThroughAxes, List.map_append, h,
      map_signedSteps hB, projVertex_add_zsmul_axisStep]
theorem pathHolonomy_projPath {P : Set (FullSpace.Edge L k i)}
    {V : FullSpace.Edge L k i → Matrices.ComplexMatrix2}
    {V' : Tower.Edge L n k i → Matrices.ComplexMatrix2}
    (hV : ∀ b ∈ P, V' (FullSpace.projEdge L n k i b) = V b) {Γ : List (FullSpace.Edge L k i)}
    (hΓ : ∀ b ∈ Γ, b ∈ P) :
    PeriodicLattice.pathHolonomy V' (FullSpace.projPath L n k i Γ) =
      FullSpace.linkHolonomy V Γ := by
  unfold PeriodicLattice.pathHolonomy FullSpace.linkHolonomy FullSpace.projPath
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun b hb => hV b (hΓ b hb)
theorem meshAt_succ (hL : 0 < L) : Tower.meshAt L k (i + 1) = (L : ℝ) * Tower.meshAt L k i := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold Tower.meshAt
  have : ((i + 1 : ℕ) : ℤ) - (k : ℤ) = ((i : ℤ) - (k : ℤ)) + 1 := by push_cast; ring
  rw [this, zpow_add_one₀ h, mul_comm]
theorem coe_toFiner (hL : 0 < L) (y : FullSpace.Vertex L k (i + 1)) :
    ((FullSpace.toFiner (Tower.meshAt L k i) y : FullSpace.Vertex L k i) :
      InfiniteLattice.AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.coe_toFiner <;> assumption
theorem coe_toSublattice (hL : 0 < L) (y : Tower.Vertex L n k (i + 1)) :
    ((PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k i) :
      Tower.Vertex L n k i) : PeriodicLattice.FourTorus L n) = y := by
  have hle : PeriodicLattice.levelDepth k (i + 1) ≤ PeriodicLattice.levelDepth k i := by
    simp only [PeriodicLattice.levelDepth]
    push_cast
    omega
  have h : ∃ x : Tower.Vertex L n k i, (x : PeriodicLattice.FourTorus L n) = y :=
    ⟨⟨y, PeriodicLattice.sublattice_mono hL n hle y.2⟩, rfl⟩
  exact Classical.epsilon_spec h
theorem projVertex_toFiner (hL : 0 < L) (y : FullSpace.Vertex L k (i + 1)) :
    FullSpace.projVertex L n k i (FullSpace.toFiner (Tower.meshAt L k i) y) =
      PeriodicLattice.Site.toSublattice (FullSpace.projVertex L n k (i + 1) y)
        (PeriodicLattice.levelDepth k i) := by
  refine Subtype.ext ?_
  rw [coe_toSublattice hL]
  show TorusMetric.torusProj _ _ = TorusMetric.torusProj _ _
  rw [coe_toFiner hL]
theorem isCubeOffset_cubeOffset {y : FullSpace.Vertex L k (i + 1)} {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y) :
    FullSpace.IsCubeOffset L y x (FullSpace.cubeOffset L y x) := by
  obtain ⟨ν, hν, he⟩ := hx
  have h : ∃ ν, FullSpace.IsCubeOffset L y x ν :=
    ⟨ν, by rw [he]; abel, fun μ => by simpa using hν μ⟩
  exact Classical.epsilon_spec h
theorem isBlockOffset_projVertex {y : FullSpace.Vertex L k (i + 1)} {x : FullSpace.Vertex L k i}
    {ν : Fin 4 → ℤ} (h : FullSpace.IsCubeOffset L y x ν) :
    PeriodicLattice.IsBlockOffset (FullSpace.projVertex L n k (i + 1) y)
      (FullSpace.projVertex L n k i x) ν := by
  refine ⟨funext fun ρ => ?_, h.2⟩
  have hρ : (x : InfiniteLattice.AmbientSpace) ρ - (y : InfiniteLattice.AmbientSpace) ρ =
      (ν ρ : ℝ) * Tower.meshAt L k i := by
    have h1 := congrFun h.1 ρ
    simpa [Finset.sum_apply, Pi.single_apply] using h1
  have h2 : (∑ μ, PeriodicLattice.pointOnAxis L n μ
      ((ν μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i))) ρ =
      (((ν ρ : ℝ) * Tower.meshAt L k i : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rw [Finset.sum_apply]
    simp [PeriodicLattice.pointOnAxis, Pi.single_apply, Tower.meshSize_levelDepth]
  rw [h2, ← hρ]
  simp [FullSpace.projVertex, TorusMetric.torusProj]
def UniqueBlockOffsets (L n k i : ℕ) : Prop :=
  ∀ (z : Tower.Vertex L n k (i + 1)) (x : Tower.Vertex L n k i),
    (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock z →
      ∃! ν : Fin 4 → ℤ, PeriodicLattice.IsBlockOffset z x ν
theorem cubeOffset_eq_blockOffset (hU : UniqueBlockOffsets L n k i)
    {y : FullSpace.Vertex L k (i + 1)} {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y)
    (hb : (FullSpace.projVertex L n k i x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock (FullSpace.projVertex L n k (i + 1) y)) :
    FullSpace.cubeOffset L y x =
      PeriodicLattice.blockOffset (FullSpace.projVertex L n k (i + 1) y)
        (FullSpace.projVertex L n k i x) := by
  obtain ⟨ν, hν, huniq⟩ := hU _ _ hb
  have h1 := huniq _ (isBlockOffset_projVertex (isCubeOffset_cubeOffset hx))
  have h2 : PeriodicLattice.IsBlockOffset (FullSpace.projVertex L n k (i + 1) y)
      (FullSpace.projVertex L n k i x)
      (PeriodicLattice.blockOffset (FullSpace.projVertex L n k (i + 1) y)
        (FullSpace.projVertex L n k i x)) :=
    Classical.epsilon_spec (⟨ν, hν⟩ : ∃ ν, PeriodicLattice.IsBlockOffset _ _ ν)
  exact h1.trans (huniq _ h2).symm
theorem exists_contourOrderEquiv (hL : 0 < L) (hB : ProjEdgeEndpoints L n k i)
    (hU : UniqueBlockOffsets L n k i)
    {y : FullSpace.Vertex L k (i + 1)} {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y)
    (hb : (FullSpace.projVertex L n k i x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock (FullSpace.projVertex L n k (i + 1) y)) :
    ∃ e : FullSpace.ContourOrder L y x ≃
        PeriodicLattice.AxisOrdering (FullSpace.projVertex L n k (i + 1) y)
          (FullSpace.projVertex L n k i x),
      ∀ σ, FullSpace.projPath L n k i (FullSpace.contour L y x σ) =
        PeriodicLattice.orderedContour (FullSpace.projVertex L n k (i + 1) y)
          (FullSpace.projVertex L n k i x) (e σ) := by
  have hν := cubeOffset_eq_blockOffset hU hx hb
  have hS : FullSpace.offsetSupport L y x =
      PeriodicLattice.offsetAxes (FullSpace.projVertex L n k (i + 1) y)
        (FullSpace.projVertex L n k i x) := by
    ext μ
    simp [FullSpace.offsetSupport, PeriodicLattice.offsetAxes, hν]
  obtain ⟨e, he⟩ := exists_orderEquiv_of_eq hS
  refine ⟨e, fun σ => ?_⟩
  unfold FullSpace.contour PeriodicLattice.orderedContour
  rw [he σ, ← hν, projPath_stepsInOrder hB, projVertex_toFiner hL]
structure EdgeHypotheses (L n k i : ℕ) (c : FullSpace.Edge L k (i + 1)) : Prop where
  L_pos : 0 < L
  endpoints : ProjEdgeEndpoints L n k i
  endpoints_succ : ProjEdgeEndpoints L n k (i + 1)
  proj_positive : (FullSpace.projEdge L n k (i + 1) c).IsPositivelyOriented
  unique_offsets : UniqueBlockOffsets L n k i
  preserves_sets : FullSpace.ProjPreservesSets L n k i c
  paths_in_cubes : FullSpace.PathsStayInCubes L k (i + 1)
  cube_partition : FullSpace.CubesOfOrderPartition L k (i + 1) 1
namespace EdgeHypotheses
variable {c : FullSpace.Edge L k (i + 1)}
theorem source_eq (h : EdgeHypotheses L n k i c) :
    (FullSpace.projEdge L n k (i + 1) c).source = FullSpace.projVertex L n k (i + 1) c.initial :=
  (h.endpoints_succ c).1
theorem target_eq (h : EdgeHypotheses L n k i c) :
    (FullSpace.projEdge L n k (i + 1) c).target = FullSpace.projVertex L n k (i + 1) c.terminal :=
  (h.endpoints_succ c).2
theorem cube_image (h : EdgeHypotheses L n k i c) {y : FullSpace.Vertex L k (i + 1)}
    (hy : y = c.initial ∨ y = c.terminal) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L n) '' FullSpace.cube L (Tower.meshAt L k i) y =
      PeriodicLattice.unitBlock (FullSpace.projVertex L n k (i + 1) y) := by
  rcases hy with rfl | rfl
  · rw [← h.source_eq]
    exact h.preserves_sets.cube_initial
  · rw [← h.target_eq]
    exact h.preserves_sets.cube_terminal
theorem cube_subset_doubleCube {y : FullSpace.Vertex L k (i + 1)}
    (hy : y = c.initial ∨ y = c.terminal) :
    FullSpace.cube L (Tower.meshAt L k i) y ⊆ FullSpace.doubleCube L (Tower.meshAt L k i) c := by
  rcases hy with rfl | rfl
  · exact subset_union_left
  · exact subset_union_right
theorem cube_subset_lattice (h : EdgeHypotheses L n k i c) (y : FullSpace.Vertex L k (i + 1)) :
    FullSpace.cube L (Tower.meshAt L k i) y ⊆
      (InfiniteLattice.latticeSubgroup (Tower.meshAt L k i) : Set InfiniteLattice.AmbientSpace) := by
  intro p hp
  have he : (⋃ y : FullSpace.Vertex L k (i + 1), FullSpace.cube L (Tower.meshAt L k i) y) =
      (InfiniteLattice.latticeSubgroup (Tower.meshAt L k i) : Set InfiniteLattice.AmbientSpace) :=
    h.cube_partition.iUnion_cube
  rw [← he]
  exact mem_iUnion.2 ⟨y, hp⟩
theorem projVertex_injective (h : EdgeHypotheses L n k i c) {x x' : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k i) c)
    (hx' : (x' : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k i) c)
    (he : FullSpace.projVertex L n k i x = FullSpace.projVertex L n k i x') : x = x' :=
  Subtype.ext (h.preserves_sets.injOn_doubleCube hx hx' (congrArg Subtype.val he))
theorem bijOn_doubleCubeLinks (h : EdgeHypotheses L n k i c) :
    BijOn (FullSpace.projEdge L n k i) (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c)
      (PeriodicLattice.bondsInDoubleBlock (FullSpace.projEdge L n k (i + 1) c)) := by
  have hinj : InjOn (FullSpace.projEdge L n k i)
      (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) := by
    intro b hb b' hb' he
    have ht : b.initial = b'.initial := h.projVertex_injective hb.1 hb'.1 (by
      rw [← (h.endpoints b).1, ← (h.endpoints b').1, he])
    have hh : b.terminal = b'.terminal := h.projVertex_injective hb.2 hb'.2 (by
      rw [← (h.endpoints b).2, ← (h.endpoints b').2, he])
    exact InfiniteLattice.Link.ext ht hh
  rw [← h.preserves_sets.doubleCubeLinks_image]
  exact hinj.bijOn_image
theorem bijOn_cubeVertices (h : EdgeHypotheses L n k i c) {y : FullSpace.Vertex L k (i + 1)}
    (hy : y = c.initial ∨ y = c.terminal) :
    BijOn (FullSpace.projVertex L n k i) (FullSpace.cubeVertices L (Tower.meshAt L k i) y)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (FullSpace.projVertex L n k (i + 1) y)) := by
  refine ⟨fun x hx => ?_, fun x hx x' hx' he => ?_, fun x' hx' => ?_⟩
  · show (FullSpace.projVertex L n k i x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock (FullSpace.projVertex L n k (i + 1) y)
    rw [← h.cube_image hy]
    exact ⟨x, hx, rfl⟩
  · exact h.projVertex_injective (cube_subset_doubleCube hy hx) (cube_subset_doubleCube hy hx') he
  · have hm : (x' : PeriodicLattice.FourTorus L n) ∈
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) ''
          FullSpace.cube L (Tower.meshAt L k i) y := by
      rw [h.cube_image hy]
      exact hx'
    obtain ⟨p, hp, hpx⟩ := hm
    exact ⟨⟨p, h.cube_subset_lattice y hp⟩, hp, Subtype.ext hpx⟩
theorem contour_subset (h : EdgeHypotheses L n k i c) {y : FullSpace.Vertex L k (i + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y)
    (σ : FullSpace.ContourOrder L y x) :
    ∀ b ∈ FullSpace.contour L y x σ, b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c := by
  have hs := h.paths_in_cubes.contour_vertex_mem y x hx (FullSpace.contour L y x σ)
    (mem_range_self σ)
  intro b hb
  exact ⟨cube_subset_doubleCube hy (hs b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))),
    cube_subset_doubleCube hy (hs b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩)))⟩
theorem crossing_subset (h : EdgeHypotheses L n k i c) {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) c.initial) :
    ∀ b ∈ FullSpace.crossingPath c x, b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c := by
  have hs := h.paths_in_cubes.crossing_vertex_mem c x hx
  intro b hb
  exact ⟨hs b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    hs b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
theorem coe_shifted (h : EdgeHypotheses L n k i c) (x : FullSpace.Vertex L k i) :
    ((FullSpace.shifted c x : FullSpace.Vertex L k i) : InfiniteLattice.AmbientSpace) =
      (x : InfiniteLattice.AmbientSpace) +
        ((c.terminal - c.initial : FullSpace.Vertex L k (i + 1)) : InfiniteLattice.AmbientSpace) := by
  unfold FullSpace.shifted
  rw [AddSubgroup.coe_add, coe_toFiner h.L_pos]
theorem shifted_mem_cube (h : EdgeHypotheses L n k i c) {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) c.initial) :
    ((FullSpace.shifted c x : FullSpace.Vertex L k i) : InfiniteLattice.AmbientSpace) ∈
      FullSpace.cube L (Tower.meshAt L k i) c.terminal := by
  have ht : FullSpace.cube L (Tower.meshAt L k i) (c.initial + (c.terminal - c.initial)) =
      (fun p : InfiniteLattice.AmbientSpace =>
        p + ((c.terminal - c.initial : FullSpace.Vertex L k (i + 1)) :
          InfiniteLattice.AmbientSpace)) ''
        FullSpace.cube L (Tower.meshAt L k i) c.initial :=
    h.cube_partition.cube_add c.initial (c.terminal - c.initial)
  rw [add_sub_cancel] at ht
  rw [ht, h.coe_shifted]
  exact ⟨x, hx, rfl⟩
theorem crossingPath_toFiner (h : EdgeHypotheses L n k i c) :
    FullSpace.crossingPath c (FullSpace.toFiner (Tower.meshAt L k i) c.initial) =
      FullSpace.axisPath (FullSpace.toFiner (Tower.meshAt L k i) c.initial)
        (FullSpace.toFiner (Tower.meshAt L k i) c.terminal) := by
  have he : FullSpace.shifted c (FullSpace.toFiner (Tower.meshAt L k i) c.initial) =
      FullSpace.toFiner (Tower.meshAt L k i) c.terminal := by
    refine Subtype.ext ?_
    rw [h.coe_shifted, coe_toFiner h.L_pos, coe_toFiner h.L_pos, AddSubgroup.coe_sub]
    abel
  unfold FullSpace.crossingPath
  rw [he]
theorem toFiner_initial_mem (h : EdgeHypotheses L n k i c) :
    ((FullSpace.toFiner (Tower.meshAt L k i) c.initial : FullSpace.Vertex L k i) :
      InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) c.initial := by
  rw [coe_toFiner h.L_pos]
  exact h.cube_partition.center_mem c.initial
section Values
variable {V : FullSpace.Edge L k i → Matrices.ComplexMatrix2}
  {V' : Tower.Edge L n k i → Matrices.ComplexMatrix2}
theorem exists_contourHolonomies_equiv (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b)
    {y : FullSpace.Vertex L k (i + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y) :
    ∃ e : FullSpace.ContourOrder L y x ≃
        PeriodicLattice.AxisOrdering (FullSpace.projVertex L n k (i + 1) y)
          (FullSpace.projVertex L n k i x),
      ∀ σ, PeriodicLattice.contourHolonomies V' (FullSpace.projVertex L n k (i + 1) y)
        (FullSpace.projVertex L n k i x) (e σ) = FullSpace.contourHolonomies L V y x σ := by
  have hb : (FullSpace.projVertex L n k i x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock (FullSpace.projVertex L n k (i + 1) y) := by
    rw [← h.cube_image hy]
    exact ⟨x, hx, rfl⟩
  obtain ⟨e, he⟩ := exists_contourOrderEquiv h.L_pos h.endpoints h.unique_offsets hx hb
  refine ⟨e, fun σ => ?_⟩
  unfold PeriodicLattice.contourHolonomies FullSpace.contourHolonomies
  rw [← he σ]
  exact pathHolonomy_projPath hV (h.contour_subset hy hx σ)
theorem familyDiameter_eq (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b)
    {y : FullSpace.Vertex L k (i + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y) :
    Matrices.ComplexMatrix2.familyDiameter (FullSpace.contourHolonomies L V y x) =
      Matrices.ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies V'
        (FullSpace.projVertex L n k (i + 1) y) (FullSpace.projVertex L n k i x)) := by
  obtain ⟨e, he⟩ := h.exists_contourHolonomies_equiv hV hy hx
  exact familyDiameter_eq_of_equiv e he
theorem complexContourMean_eq (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b)
    {y : FullSpace.Vertex L k (i + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k i}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k i) y) :
    FullSpace.complexContourMean L V y x =
      PeriodicLattice.complexMeanContourHolonomy V' (FullSpace.projVertex L n k (i + 1) y)
        (FullSpace.projVertex L n k i x) := by
  obtain ⟨e, he⟩ := h.exists_contourHolonomies_equiv hV hy hx
  exact complexLogMean_eq_of_equiv e he
theorem transportAlong_eq (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b) :
    FullSpace.transportAlong V c =
      PeriodicLattice.parallelTransport V' (FullSpace.projEdge L n k (i + 1) c) := by
  unfold FullSpace.transportAlong PeriodicLattice.parallelTransport
  rw [← h.preserves_sets.axisPath_eq]
  refine (pathHolonomy_projPath hV fun b hb => ?_).symm
  rw [← h.crossingPath_toFiner] at hb
  exact h.crossing_subset h.toFiner_initial_mem b hb
theorem crossingDefect_eq (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b)
    {x : FullSpace.Vertex L k i}
    (hx : x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) c.initial) :
    FullSpace.crossingDefect L V c x =
      PeriodicLattice.complexCrossingDefect V' (FullSpace.projEdge L n k (i + 1) c)
        (FullSpace.projVertex L n k i x) := by
  have hcross : FullSpace.linkHolonomy V (FullSpace.crossingPath c x) =
      PeriodicLattice.pathHolonomy V' (PeriodicLattice.crossingPath
        (FullSpace.projEdge L n k (i + 1) c) (FullSpace.projVertex L n k i x)) := by
    rw [← h.preserves_sets.crossingPath_eq x hx]
    exact (pathHolonomy_projPath hV (h.crossing_subset hx)).symm
  unfold FullSpace.crossingDefect PeriodicLattice.complexCrossingDefect
  rw [← h.preserves_sets.shifted_eq x hx, h.source_eq, h.target_eq, hcross, h.transportAlong_eq hV,
    h.complexContourMean_eq hV (Or.inl rfl) hx,
    h.complexContourMean_eq hV (Or.inr rfl) (h.shifted_mem_cube hx)]
theorem forall_cubeVertices_iff (h : EdgeHypotheses L n k i c) {y : FullSpace.Vertex L k (i + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {p : FullSpace.Vertex L k i → Prop}
    {q : Tower.Vertex L n k i → Prop}
    (hpq : ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) y,
      (p x ↔ q (FullSpace.projVertex L n k i x))) :
    (∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) y, p x) ↔
      ∀ x' ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (FullSpace.projVertex L n k (i + 1) y), q x' := by
  have hb := h.bijOn_cubeVertices (n := n) hy
  constructor
  · intro a x' hx'
    obtain ⟨x, hx, rfl⟩ := hb.surjOn hx'
    exact (hpq x hx).1 (a x hx)
  · intro a x hx
    exact (hpq x hx).2 (a _ (hb.mapsTo hx))
theorem mem_domain_iff (h : EdgeHypotheses L n k i c)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b)
    (hc : FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup
      (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V)
    (hc' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
      (PeriodicLattice.bondsInDoubleBlock (FullSpace.projEdge L n k (i + 1) c)) V') :
    V ∈ FullSpace.complexDomainNearOne L c ↔
      V' ∈ PeriodicLattice.complexAveragingDomainNearOne (FullSpace.projEdge L n k (i + 1) c) := by
  have hd {y : FullSpace.Vertex L k (i + 1)} (hy : y = c.initial ∨ y = c.terminal) :
      (∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) y,
        Matrices.ComplexMatrix2.familyDiameter (FullSpace.contourHolonomies L V y x) <
          Averaging.centreOfMassDiameter) ↔
      ∀ x' ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (FullSpace.projVertex L n k (i + 1) y),
        Matrices.ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies V'
          (FullSpace.projVertex L n k (i + 1) y) x') < Averaging.centreOfMassDiameter :=
    h.forall_cubeVertices_iff hy fun x hx => by rw [h.familyDiameter_eq hV hy hx]
  have hw : (∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) c.initial,
        Matrices.ComplexMatrix2.operatorNorm (FullSpace.crossingDefect L V c x - 1) < 1) ↔
      ∀ x' ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (FullSpace.projEdge L n k (i + 1) c).source,
        Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexCrossingDefect V'
          (FullSpace.projEdge L n k (i + 1) c) x' - 1) < 1 := by
    rw [h.source_eq]
    exact h.forall_cubeVertices_iff (Or.inl rfl) fun x hx => by rw [h.crossingDefect_eq hV hx]
  have ht := hd (Or.inl rfl)
  have hh := hd (Or.inr rfl)
  rw [← h.source_eq] at ht
  rw [← h.target_eq] at hh
  have e1 : V ∈ FullSpace.complexDomain L c ↔
      V' ∈ PeriodicLattice.complexAveragingDomain (FullSpace.projEdge L n k (i + 1) c) :=
    ⟨fun a => ⟨hc', ht.1 a.2.1, hh.1 a.2.2⟩, fun a => ⟨hc, ht.2 a.2.1, hh.2 a.2.2⟩⟩
  exact and_congr e1 hw
theorem complexSmoothing_eq (h : EdgeHypotheses L n k i c) (hpos : c.IsPositivelyOriented)
    (hV : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      V' (FullSpace.projEdge L n k i b) = V b) :
    FullSpace.complexSmoothing L V c =
      PeriodicLattice.complexBlockAverage V' (FullSpace.projEdge L n k (i + 1) c) := by
  have hsum : ∑ᶠ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) c.initial,
        Matrices.ComplexMatrix2.logSeries (FullSpace.crossingDefect L V c x) =
      ∑ᶠ x' ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
          (FullSpace.projEdge L n k (i + 1) c).source,
        Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexCrossingDefect V'
          (FullSpace.projEdge L n k (i + 1) c) x') := by
    rw [h.source_eq]
    exact finsum_mem_eq_of_bijOn (FullSpace.projVertex L n k i) (h.bijOn_cubeVertices (Or.inl rfl))
      fun x hx => by rw [h.crossingDefect_eq hV hx]
  simp only [FullSpace.complexSmoothing, PeriodicLattice.complexBlockAverage, if_pos hpos,
    if_pos h.proj_positive, FullSpace.complexSmoothingPositive,
    PeriodicLattice.complexBlockAverageOnPositive]
  rw [hsum, h.transportAlong_eq hV]
end Values
theorem projPreservesFields (h : EdgeHypotheses L n k i c)
    (hcarry : ∀ V : FullSpace.Edge L k i → Matrices.ComplexMatrix2,
      FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup
          (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V →
        (∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
          FullSpace.projField L n k i (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V
            (FullSpace.projEdge L n k i b) = V b) ∧
        PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
          (PeriodicLattice.bondsInDoubleBlock (FullSpace.projEdge L n k (i + 1) c))
          (FullSpace.projField L n k i
            (FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V))
    (hpos : c.IsPositivelyOriented) : FullSpace.ProjPreservesFields L n k i c where
  projField_spec := hcarry
  mem_complexDomain_iff := fun V hV => h.mem_domain_iff (hcarry V hV).1 hV (hcarry V hV).2
  complexContourMean_eq := fun V hV _ hy _ hx =>
    h.complexContourMean_eq (hcarry V hV.1.1).1 hy hx
  complexSmoothing_eq := fun V hV => h.complexSmoothing_eq hpos (hcarry V hV.1.1).1
end EdgeHypotheses
theorem projPreservesFieldsEverywhere_holds (hSets : Tower.ProjectionCarriesSetsStatement)
    (hBonds : Tower.EdgeProjectionProperties)
    (hCombs : PeriodicLattice.BlockContoursAndCombs)
    (hBlocks : FullSpace.CubesCorridorsPivotEdgesAndPaths) :
    FullSpace.ProjPreservesFieldsEverywhere := by
  intro L hL hstd k hk n hn i hik c hc
  have hb := hBonds L n k i hstd hn hik.le
  have hb' := hBonds L n k (i + 1) hstd hn hik
  have hy := hBlocks L hstd k (i + 1) 1 hk (by omega) hik le_rfl (by omega)
  have h : EdgeHypotheses L n k i c :=
    { L_pos := hL
      endpoints := fun b => ⟨(hb.1 b).1, (hb.1 b).2.1⟩
      endpoints_succ := fun b => ⟨(hb'.1 b).1, (hb'.1 b).2.1⟩
      proj_positive := (hb'.1 c).2.2.1 hc
      unique_offsets := fun z x hx => (hCombs L n k hstd hn i hik z x hx).1
      preserves_sets := ((hSets L hL hstd k hk n hn).2 i hik c hc)
      paths_in_cubes := hy.2.2.2
      cube_partition := hy.1 }
  have hrev : ∀ b ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
      b.opposite ∈ FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c :=
    fun b hb => ⟨hb.2, hb.1⟩
  exact h.projPreservesFields (fun V hV => (hb.2 _ _ hrev h.bijOn_doubleCubeLinks).2 V hV) hc
end YangMills.Construction.Tower.FieldProjection
end
