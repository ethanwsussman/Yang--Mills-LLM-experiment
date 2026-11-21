import YangMills.Construction.Towers.FunctionsOfTheCellsOfATowerAreReadAtTheirPlacesProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import YangMills.Construction.Towers.SiteAverageOfATowerIsAMapOfPeriodicFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.VertexSmoothingPeriodicProof
open OneStepChart
open InfiniteLattice (AmbientSpace)
theorem coe_integerPoint {L k j : ℕ} (hL : 0 < L) (hjk : j ≤ k) (z : Fin 4 → ℤ) :
    ((integerPoint (meshAt L k j) z : InfiniteLattice.LatticePoint (meshAt L k j)) : AmbientSpace) =
      fun μ => (z μ : ℝ) := by apply _root_.YangMills.Construction.Tower.UnitScale.CellsReadAtPlaces.coe_integerPoint <;> assumption
theorem weightedSum_eq_kernelSum {L : ℕ} {ι : Type*} {S : Set ι} [DecidablePred (· ∈ S)]
    (hS : S.Finite) (f : ι → Matrices.ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ S, f x =
      ∑ᶠ p, (if p ∈ S then (L : ℝ) ^ (-4 : ℤ) else 0) • f p := by
  rw [smul_finsum_mem hS, finsum_mem_def]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx, if_pos hx]
    ext a b
    simp [PeriodicLattice.inverseFourthPowerWeight]
  · simp [indicator_of_notMem hx, if_neg hx]
section Step
variable {L k j : ℕ}
theorem cubeVertices_finite
    (hP : FullSpace.RefinedCubesPartition L k 1 (j + 1)) (hL : 0 < L)
    (y : FullSpace.Vertex L k (j + 1)) :
    (FullSpace.cubeVertices L (meshAt L k j) y).Finite := by
  have hcard : (FullSpace.cube L (meshAt L k j) y).ncard = L ^ (4 * 1) := hP.ncard_eq y
  have hfin : (FullSpace.cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hcard]; exact pow_ne_zero _ hL.ne')
  exact hfin.preimage Subtype.val_injective.injOn
theorem cubeVertices_shift
    (hP : FullSpace.RefinedCubesPartition L k 1 (j + 1)) (hL : 0 < L) (hjk : j < k)
    (y : FullSpace.Vertex L k (j + 1)) (w : Fin 4 → ℤ) :
    BijOn (fun x : FullSpace.Vertex L k j => x + integerPoint _ w)
      (FullSpace.cubeVertices L (meshAt L k j) y)
      (FullSpace.cubeVertices L (meshAt L k j) (y + integerPoint _ w)) := by
  have hcoarse := coe_integerPoint (k := k) (j := j + 1) hL hjk w
  have hfine := coe_integerPoint (k := k) (j := j) hL hjk.le w
  have hshift : FullSpace.cube L (meshAt L k j) (y + integerPoint _ w) =
      FullSpace.spaceTranslation ((integerPoint (meshAt L k (j + 1)) w :
        InfiniteLattice.LatticePoint (meshAt L k (j + 1))) : AmbientSpace) ''
        FullSpace.cube L (meshAt L k j) y := hP.image_add y _
  refine ⟨fun x hx => ?_, fun x _ x' _ h => add_right_cancel h, fun x hx => ?_⟩
  · show ((x + integerPoint _ w : FullSpace.Vertex L k j) : AmbientSpace) ∈
      FullSpace.cube L (meshAt L k j) (y + integerPoint _ w)
    rw [hshift]
    refine ⟨(x : AmbientSpace), hx, ?_⟩
    show (x : AmbientSpace) + _ = _
    rw [hcoarse]
    simp only [AddSubgroup.coe_add, hfine]
  · have hxmem : (x : AmbientSpace) ∈ FullSpace.cube L (meshAt L k j) (y + integerPoint _ w) := hx
    rw [hshift] at hxmem
    obtain ⟨q, hq, hqx⟩ := hxmem
    refine ⟨x - integerPoint _ w, ?_, by simp⟩
    have hqe : ((x - integerPoint _ w : FullSpace.Vertex L k j) : AmbientSpace) = q := by
      simp only [AddSubgroup.coe_sub, hfine, ← hqx]
      show q + _ - _ = q
      rw [hcoarse]
      simp
    show ((x - integerPoint _ w : FullSpace.Vertex L k j) : AmbientSpace) ∈
      FullSpace.cube L (meshAt L k j) y
    rw [hqe]
    exact hq
theorem projVertex_bijOn_cube {m : ℕ} (hP : FullSpace.RefinedCubesPartition L k 1 (j + 1))
    (hcarry : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      FullSpace.ProjPreservesSets L m k j c)
    (hproj : ∀ e : FullSpace.Edge L k (j + 1),
      (FullSpace.projEdge L m k (j + 1) e).source = FullSpace.projVertex L m k (j + 1) e.initial)
    (y : FullSpace.Vertex L k (j + 1)) :
    BijOn (FullSpace.projVertex L m k j) (FullSpace.cubeVertices L (meshAt L k j) y)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projVertex L m k (j + 1) y)) := by
  have hpos : (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [InfiniteLattice.Link.forwardFrom]⟩
  have hsets := hcarry _ hpos
  have himage : TorusMetric.torusProj (PeriodicLattice.torusSide L m) ''
      FullSpace.cube L (meshAt L k j) y =
      PeriodicLattice.unitBlock (FullSpace.projVertex L m k (j + 1) y) := by
    have h := hsets.cube_initial
    rwa [hproj] at h
  have hinj : InjOn (TorusMetric.torusProj (PeriodicLattice.torusSide L m))
      (FullSpace.cube L (meshAt L k j) y) :=
    hsets.injOn_doubleCube.mono subset_union_left
  refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x hx => ?_⟩
  · show ((FullSpace.projVertex L m k j x : Vertex L m k j) : PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.unitBlock (FullSpace.projVertex L m k (j + 1) y)
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  · exact Subtype.ext (hinj hx hx' (congrArg Subtype.val h))
  · have hxmem : (x : PeriodicLattice.FourTorus L m) ∈
        PeriodicLattice.unitBlock (FullSpace.projVertex L m k (j + 1) y) := hx
    rw [← himage] at hxmem
    obtain ⟨q, hq, hqx⟩ := hxmem
    have hlat : q ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
      hP.subset_sublattice y hq
    exact ⟨⟨q, hlat⟩, hq, Subtype.ext hqx⟩
end Step
theorem vertexSmoothingIsPeriodic_holds (hCubes : BlockPathContourPivotStatement)
    (hTorus : PeriodicCoarseningStep.Holds)
    (hFull : FullSpace.OneStepComplexForms.OneStepClaim)
    (hEdges : EdgeProjectionProperties)
    (hSets : ProjectionCarriesSetsStatement) : VertexSmoothingIsPeriodic := by
  intro L hL m k j hm hj
  have hL0 : 0 < L := by have := hL.2; omega
  have hP : FullSpace.RefinedCubesPartition L k 1 (j + 1) :=
    (hCubes L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hFull L hL k j hj).vertexSmoothing_mapsTo
  · exact (hTorus L hL m k j hm hj).vertexSmoothing_mapsTo
  · intro f _
    funext y
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) y, f (FullSpace.projVertex L m k j x) =
      PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
          (FullSpace.projVertex L m k (j + 1) y), f x
    congr 1
    exact finsum_mem_eq_of_bijOn _
      (projVertex_bijOn_cube hP ((hSets L hL0 hL k (by omega) m hm).2 j hj)
        (fun e => ((hEdges L m k (j + 1) hL hm hj).1 e).1) y) fun _ _ => rfl
  · intro z f _
    funext y
    show PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) y, f (x + integerPoint _ (-z)) =
      PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) (y + integerPoint _ (-z)), f x
    congr 1
    exact finsum_mem_eq_of_bijOn _ (cubeVertices_shift hP hL0 hj y (-z)) fun _ _ => rfl
  · classical
    refine ⟨fun y x => if x ∈ FullSpace.cubeVertices L (meshAt L k j) y then
      (L : ℝ) ^ (-4 : ℤ) else 0, fun y => ?_, fun f _ y => ?_⟩
    · refine (cubeVertices_finite hP hL0 y).subset fun x hx => ?_
      by_contra hn
      exact hx (if_neg hn)
    · exact weightedSum_eq_kernelSum (L := L) (cubeVertices_finite hP hL0 y) f
end YangMills.Construction.Tower.UnitScale.VertexSmoothingPeriodicProof
end
