import YangMills.Construction.Towers.AtMostOneStraightPath
import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorus
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurationsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
open InfiniteLattice (AmbientSpace)
namespace ProjectionSets
variable {L n k i : ℕ}
theorem projVertex_add (x y : Vertex L k i) :
    projVertex L n k i (x + y) = projVertex L n k i x + projVertex L n k i y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projVertex, TorusMetric.torusProj]
def vertexHom (L n k i : ℕ) : Vertex L k i →+ YangMills.Construction.Tower.Vertex L n k i :=
  AddMonoidHom.mk' (projVertex L n k i) projVertex_add
theorem projVertex_zsmul (m : ℤ) (x : Vertex L k i) :
    projVertex L n k i (m • x) = m • projVertex L n k i x :=
  map_zsmul (vertexHom L n k i) m x
theorem projVertex_sub (x y : Vertex L k i) :
    projVertex L n k i (x - y) = projVertex L n k i x - projVertex L n k i y := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_sub <;> assumption
theorem projVertex_axisStep (μ : Fin 4) :
    projVertex L n k i (InfiniteLattice.axisStep (meshAt L k i) μ) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_axisStep <;> assumption
section Flows
variable (hends : ∀ b : Edge L k i,
  (projEdge L n k i b).source = projVertex L n k i b.initial ∧
    (projEdge L n k i b).target = projVertex L n k i b.terminal)
include hends
theorem projEdge_forwardFrom (x : Vertex L k i) (μ : Fin 4) :
    projEdge L n k i (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (projVertex L n k i x) μ := by apply _root_.YangMills.Construction.Tower.FieldProjection.projEdge_forwardFrom <;> assumption
theorem projEdge_backwardLink (x : Vertex L k i) (μ : Fin 4) :
    projEdge L n k i (backwardLink x μ) =
      PeriodicLattice.Bond.backwardFrom (projVertex L n k i x) μ := by apply _root_.YangMills.Construction.Tower.FieldProjection.projEdge_backwardLink <;> assumption
theorem map_forwardSteps (x : Vertex L k i) (μ : Fin 4) (m : ℕ) :
    (forwardSteps x μ m).map (projEdge L n k i) =
      PeriodicLattice.forwardAxisPath (projVertex L n k i x) μ m := by apply _root_.YangMills.Construction.Tower.FieldProjection.map_forwardSteps <;> assumption
theorem map_backwardSteps (x : Vertex L k i) (μ : Fin 4) (m : ℕ) :
    (backwardSteps x μ m).map (projEdge L n k i) =
      PeriodicLattice.backwardAxisPath (projVertex L n k i x) μ m := by apply _root_.YangMills.Construction.Tower.FieldProjection.map_backwardSteps <;> assumption
theorem map_signedSteps (x : Vertex L k i) (μ : Fin 4) (m : ℤ) :
    (signedSteps x μ m).map (projEdge L n k i) =
      PeriodicLattice.flowAlong (projVertex L n k i x) μ m := by apply _root_.YangMills.Construction.Tower.FieldProjection.map_signedSteps <;> assumption
theorem map_stepsInOrder (ν : Fin 4 → ℤ) (x : Vertex L k i) (l : List (Fin 4)) :
    (stepsInOrder ν x l).map (projEdge L n k i) =
      PeriodicLattice.stepsThroughAxes ν (projVertex L n k i x) l := by apply _root_.YangMills.Construction.Tower.FieldProjection.projPath_stepsInOrder <;> assumption
theorem map_axisPath (hS : Tower.AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hik : i ≤ k)
    {x x' : Vertex L k i} {μ : Fin 4} {q : ℤ}
    (hx : x' - x = q • InfiniteLattice.axisStep (meshAt L k i) μ)
    (hq : ((|q| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n / 2) :
    (axisPath x x').map (projEdge L n k i) =
      PeriodicLattice.axialPath (projVertex L n k i x) (projVertex L n k i x') := by
  obtain ⟨hside, hinf⟩ := hS L hL k i hik
  have hxq : projVertex L n k i x' - projVertex L n k i x =
      q • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
    rw [← projVertex_sub, hx, projVertex_zsmul, projVertex_axisStep]
  rw [(hinf.2 x x' μ μ q q hx hx).2, ((hside n hn).2 _ _ μ μ q q hxq hq hxq hq).2,
    map_signedSteps hends]
end Flows
def axisOrder {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange _).map fun j => ((σ j : S) : Fin 4)
theorem range_axisOrder_congr {α : Type*} {S S' : Finset (Fin 4)} (h : S = S')
    (f : List (Fin 4) → α) :
    range (fun σ : Fin S.card ≃ S => f (axisOrder σ)) =
      range (fun σ : Fin S'.card ≃ S' => f (axisOrder σ)) := by
  subst h
  rfl
theorem meshAt_succ (hL : 0 < L) :
    meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by apply _root_.YangMills.Construction.Tower.FieldProjection.meshAt_succ <;> assumption
theorem blocking_length_lt_half_side (hL : 13 ≤ L) (hn : 0 < n) (hik : i < k) :
    ((|(L : ℤ)| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n / 2 := by
  have hL0 : 0 < L := by omega
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hle : meshAt L k (i + 1) ≤ 1 :=
    zpow_le_one_of_nonpos₀ h1.le (by omega)
  rw [meshAt_succ hL0] at hle
  have hpow : (L : ℝ) ^ 1 ≤ (L : ℝ) ^ n := pow_le_pow_right₀ h1.le hn
  have habs : ((|(L : ℤ)| : ℤ) : ℝ) = L := by simp
  rw [habs]
  unfold PeriodicLattice.torusSide
  linarith
theorem coe_toFiner (hL : 0 < L) (w : Vertex L k (i + 1)) :
    ((toFiner (meshAt L k i) w : Vertex L k i) : AmbientSpace) = w := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.coe_toFiner <;> assumption
theorem toSublattice_projVertex (hL : 0 < L) (y : Vertex L k (i + 1)) :
    (projVertex L n k (i + 1) y).toSublattice (PeriodicLattice.levelDepth k i) =
      projVertex L n k i (toFiner (meshAt L k i) y) := by
  have hy : ((projVertex L n k i (toFiner (meshAt L k i) y) :
      YangMills.Construction.Tower.Vertex L n k i) : PeriodicLattice.FourTorus L n) =
      projVertex L n k (i + 1) y := by
    show TorusMetric.torusProj _ _ = TorusMetric.torusProj _ _
    rw [coe_toFiner hL]
  refine Subtype.ext (Eq.trans ?_ hy.symm)
  exact Classical.epsilon_spec
    (p := fun x : YangMills.Construction.Tower.Vertex L n k i =>
      (x : PeriodicLattice.FourTorus L n) = projVertex L n k (i + 1) y) ⟨_, hy⟩
theorem toFiner_axisStep (hL : 0 < L) (μ : Fin 4) :
    toFiner (meshAt L k i) (InfiniteLattice.axisStep (meshAt L k (i + 1)) μ) =
      (L : ℤ) • InfiniteLattice.axisStep (meshAt L k i) μ := by
  refine Subtype.ext ?_
  rw [coe_toFiner hL]
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [InfiniteLattice.axisStep, meshAt_succ hL]
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem toFiner_sub (hL : 0 < L) (y y' : Vertex L k (i + 1)) :
    toFiner (meshAt L k i) y' - toFiner (meshAt L k i) y =
      toFiner (meshAt L k i) (y' - y) := by
  refine Subtype.ext ?_
  simp only [AddSubgroup.coe_sub, coe_toFiner hL]
theorem shifted_toFiner (hL : 0 < L) (c : Edge L k (i + 1)) :
    shifted c (toFiner (meshAt L k i) c.initial) =
      toFiner (meshAt L k i) c.terminal := by
  refine Subtype.ext ?_
  show ((toFiner (meshAt L k i) c.initial +
    toFiner (meshAt L k i) (c.terminal - c.initial) : Vertex L k i) : AmbientSpace) = _
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, coe_toFiner hL]
  abel
theorem isCubeOffset_of_mem {y : Vertex L k (i + 1)} {x : Vertex L k i}
    (hx : x ∈ cubeVertices L (meshAt L k i) y) :
    IsCubeOffset L y x (cubeOffset L y x) := by
  obtain ⟨ν, hb, he⟩ := hx
  refine Classical.epsilon_spec (p := IsCubeOffset L y x) ⟨ν, ?_, ?_⟩
  · rw [he]
    abel
  · simpa using hb
theorem isBlockOffset_projVertex {y : Vertex L k (i + 1)} {x : Vertex L k i}
    {ν : Fin 4 → ℤ} (h : IsCubeOffset L y x ν) :
    PeriodicLattice.IsBlockOffset (projVertex L n k (i + 1) y) (projVertex L n k i x) ν := by apply _root_.YangMills.Construction.Tower.FieldProjection.isBlockOffset_projVertex <;> assumption
theorem image_contourSet (hC : PeriodicLattice.BlockContoursAndCombs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hik : i < k)
    (hends : ∀ b : Edge L k i,
      (projEdge L n k i b).source = projVertex L n k i b.initial ∧
        (projEdge L n k i b).target = projVertex L n k i b.terminal)
    {y : Vertex L k (i + 1)} {x : Vertex L k i}
    (hx : x ∈ cubeVertices L (meshAt L k i) y)
    (hblock : ((projVertex L n k i x : YangMills.Construction.Tower.Vertex L n k i) :
      PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock (projVertex L n k (i + 1) y)) :
    projPath L n k i '' contourSet L y x =
      PeriodicLattice.contourSet (projVertex L n k (i + 1) y) (projVertex L n k i x) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hw := isBlockOffset_projVertex (n := n) (isCubeOffset_of_mem hx)
  have hd : PeriodicLattice.blockOffset (projVertex L n k (i + 1) y)
      (projVertex L n k i x) = cubeOffset L y x :=
    (hC L n k hL hn i hik _ _ hblock).1.unique
      (Classical.epsilon_spec (p := PeriodicLattice.IsBlockOffset _ _) ⟨_, hw⟩) hw
  have hS : offsetSupport L y x =
      PeriodicLattice.offsetAxes (projVertex L n k (i + 1) y) (projVertex L n k i x) := by
    unfold offsetSupport PeriodicLattice.offsetAxes
    rw [hd]
  have e := range_axisOrder_congr hS (fun l => PeriodicLattice.stepsThroughAxes
    (PeriodicLattice.blockOffset (projVertex L n k (i + 1) y) (projVertex L n k i x))
    ((projVertex L n k (i + 1) y).toSublattice (PeriodicLattice.levelDepth k i)) l)
  unfold contourSet
  rw [← Set.range_comp]
  refine Eq.trans ?_ e
  congr 1
  funext σ
  show (stepsInOrder (cubeOffset L y x) (toFiner (meshAt L k i) y)
    (axisOrder σ)).map (projEdge L n k i) = _
  rw [map_stepsInOrder hends, hd, toSublattice_projVertex hL0]
theorem projSublattices_holds (L n k : ℕ) : ProjSublattices L n k := by
  intro i _
  ext p
  constructor
  · rintro ⟨x, ⟨m, hm⟩, rfl⟩
    refine ⟨m, fun μ => ?_⟩
    simp [TorusMetric.torusProj, hm μ, meshSize_levelDepth]
  · rintro ⟨m, hm⟩
    refine ⟨fun μ => (m μ : ℝ) * meshAt L k i, ⟨m, fun μ => rfl⟩, funext fun μ => ?_⟩
    rw [hm μ, meshSize_levelDepth]
    rfl
end ProjectionSets
end Tower.FullSpace
namespace Tower
open InfiniteLattice (AmbientSpace)
open FullSpace FullSpace.ProjectionSets in
theorem projectionCarriesSets
    (hQ : EdgeProjectionProperties)
    (hK : FullSpace.DoubleCubeLinksAndTorusImage)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hS : AxisPathUniqueness.AxisPathsUnique)
    (hC : PeriodicLattice.BlockContoursAndCombs) :
    ProjectionCarriesSetsStatement := by
  intro L hL0 hL k hk n hn
  refine ⟨projSublattices_holds L n k, fun i hik c hc => ?_⟩
  have hends : ∀ b : FullSpace.Edge L k i,
      (projEdge L n k i b).source = projVertex L n k i b.initial ∧
        (projEdge L n k i b).target = projVertex L n k i b.terminal := fun b =>
    ⟨((hQ L n k i hL hn hik.le).1 b).1, ((hQ L n k i hL hn hik.le).1 b).2.1⟩
  obtain ⟨-, hK'⟩ := hK L k (i + 1) hL (by omega) hik c hc
  obtain ⟨hdt, hdh, -, hinj, hbt, hbh, hbij⟩ := hK' n hn
  have hcubes := hB L hL k (i + 1) 1 hk (by omega) hik le_rfl (by omega)
  have hpart : CubesOfOrderPartition L k (i + 1) 1 := hcubes.1
  have hsteps : StepsEdgesAndCorridors L k (i + 1) := hcubes.2.2.1
  have hpaths : PathsStayInCubes L k (i + 1) := hcubes.2.2.2
  obtain ⟨μ, hμ⟩ := hc
  have hlen := blocking_length_lt_half_side (L := L) (n := n) (k := k) (i := i) hL.2 hn hik
  have hshift : toFiner (meshAt L k i) (c.terminal - c.initial) =
      (L : ℤ) • InfiniteLattice.axisStep (meshAt L k i) μ := by
    rw [hμ, toFiner_axisStep hL0]
  have htrans : ∀ x : FullSpace.Vertex L k i,
      projVertex L n k i (shifted c x) =
        PeriodicLattice.shiftAcross (projEdge L n k (i + 1) c) (projVertex L n k i x) := by
    intro x
    show projVertex L n k i (x + toFiner (meshAt L k i) (c.terminal - c.initial)) =
      projVertex L n k i x + ((projEdge L n k (i + 1) c).target -
        (projEdge L n k (i + 1) c).source).toSublattice (PeriodicLattice.levelDepth k i)
    rw [projVertex_add, hdt, hdh, ← projVertex_sub, toSublattice_projVertex hL0]
  have hcross : ∀ x : FullSpace.Vertex L k i,
      projPath L n k i (crossingPath c x) =
        PeriodicLattice.crossingPath (projEdge L n k (i + 1) c) (projVertex L n k i x) := by
    intro x
    show (axisPath x (shifted c x)).map (projEdge L n k i) =
      PeriodicLattice.axialPath (projVertex L n k i x)
        (PeriodicLattice.shiftAcross (projEdge L n k (i + 1) c) (projVertex L n k i x))
    rw [← htrans x]
    refine map_axisPath hends hS hL hn hik.le (μ := μ) (q := (L : ℤ)) ?_ hlen
    show x + toFiner (meshAt L k i) (c.terminal - c.initial) - x = _
    rw [add_sub_cancel_left, hshift]
  have hstraight : (axisPath (toFiner (meshAt L k i) c.initial)
        (toFiner (meshAt L k i) c.terminal)).map (projEdge L n k i) =
      PeriodicLattice.axialPath
        ((projEdge L n k (i + 1) c).source.toSublattice (PeriodicLattice.levelDepth k i))
        ((projEdge L n k (i + 1) c).target.toSublattice (PeriodicLattice.levelDepth k i)) := by
    rw [hdt, hdh, toSublattice_projVertex hL0, toSublattice_projVertex hL0]
    refine map_axisPath hends hS hL hn hik.le (μ := μ) (q := (L : ℤ)) ?_ hlen
    rw [toFiner_sub hL0, hshift]
  have hpivot : projEdge L n k i (FullSpace.pivotLink L (meshAt L k i) c) =
      PeriodicLattice.pivot (projEdge L n k (i + 1) c) := by
    obtain ⟨b, hb, huniq⟩ := hsteps.existsUnique_corridorEdge c μ hμ
    have hp : FullSpace.IsPivotLink L (meshAt L k i) c
        (FullSpace.pivotLink L (meshAt L k i) c) :=
      Classical.epsilon_spec (p := FullSpace.IsPivotLink L (meshAt L k i) c) ⟨b, hb.2, hb.1⟩
    have hpb : FullSpace.pivotLink L (meshAt L k i) c = b := huniq _ ⟨hp.2, hp.1⟩
    have hqb : PeriodicLattice.IsPivot (projEdge L n k (i + 1) c)
        (projEdge L n k i b) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [(hends b).1, hdt, ← hbt]
        exact ⟨_, hb.2.1, rfl⟩
      · rw [(hends b).2, hdh, ← hbh]
        exact ⟨_, hb.2.2, rfl⟩
      · rw [← hstraight]
        exact List.mem_map.2 ⟨b, hb.1, rfl⟩
    have hspec : PeriodicLattice.IsPivot (projEdge L n k (i + 1) c)
        (PeriodicLattice.pivot (projEdge L n k (i + 1) c)) :=
      Classical.epsilon_spec
        (p := PeriodicLattice.IsPivot (projEdge L n k (i + 1) c)) ⟨_, hqb⟩
    obtain ⟨⟨hct, hch⟩, hs⟩ := hspec
    rw [← hstraight] at hs
    obtain ⟨b', hb', he⟩ := List.mem_map.1 hs
    have htail : (toFiner (meshAt L k i) c.initial : FullSpace.Vertex L k i) ∈
        cubeVertices L (meshAt L k i) c.initial := by
      show ((toFiner (meshAt L k i) c.initial : FullSpace.Vertex L k i) : AmbientSpace) ∈
        cube L (meshAt L k i) c.initial
      rw [coe_toFiner hL0]
      exact hpart.center_mem c.initial
    have hb'' : b' ∈ crossingPath c (toFiner (meshAt L k i) c.initial) := by
      show b' ∈ axisPath _ (shifted c _)
      rw [shifted_toFiner hL0]
      exact hb'
    have hsite : ∀ z : FullSpace.Vertex L k i, (z = b'.initial ∨ z = b'.terminal) →
        (z : AmbientSpace) ∈ doubleCube L (meshAt L k i) c := fun z hz =>
      hpaths.crossing_vertex_mem c _ htail z (Or.inr (Or.inr ⟨b', hb'', hz⟩))
    have hcorr : b' ∈ linkCorridor L (meshAt L k i) c := by
      constructor
      · rw [← he, (hends b').1, hdt, ← hbt] at hct
        obtain ⟨w, hw, hwe⟩ := hct
        have := hinj (Or.inl hw) (hsite _ (Or.inl rfl)) hwe
        rw [← this]
        exact hw
      · rw [← he, (hends b').2, hdh, ← hbh] at hch
        obtain ⟨w, hw, hwe⟩ := hch
        have := hinj (Or.inr hw) (hsite _ (Or.inr rfl)) hwe
        rw [← this]
        exact hw
    rw [hpb, ← huniq b' ⟨hb', hcorr⟩, he]
  refine
    { injOn_doubleCube := hinj
      cube_initial := by rw [hdt]; exact hbt
      cube_terminal := by rw [hdh]; exact hbh
      contourSet_image := ?_
      shifted_eq := fun x _ => htrans x
      crossingPath_eq := fun x _ => hcross x
      axisPath_eq := hstraight
      pivotLink_eq := hpivot
      doubleCubeLinks_image := hbij.image_eq }
  intro y hy x hx
  refine image_contourSet hC hL hn hik hends hx ?_
  rcases hy with rfl | rfl
  · rw [← hbt]
    exact ⟨_, hx, rfl⟩
  · rw [← hbh]
    exact ⟨_, hx, rfl⟩
end Tower
end YangMills.Construction
end
