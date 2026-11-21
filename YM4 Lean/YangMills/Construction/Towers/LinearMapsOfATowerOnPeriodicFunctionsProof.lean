import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.ContourMeansOfATowerAreMapsOfPeriodicFunctions
import YangMills.Construction.Towers.CrossingAverageOfATowerIsAMapOfPeriodicFunctions
import YangMills.Construction.Towers.DifferencesAndRestrictionsOfATowerAreMapsOfPeriodicFunctions
import YangMills.Construction.Towers.FunctionsOfTheCellsOfATowerAreReadAtTheirPlaces
import YangMills.Construction.Towers.FunctionsOffTheCoarseSitesAreReadAtTheirPlaces
import YangMills.Construction.Towers.LinearMapsOfATowerOnPeriodicFunctions
import YangMills.Construction.Towers.MapsOfTwoSidesFromPeriodicLinearMaps
import YangMills.Construction.Towers.SiteAverageOfATowerIsAMapOfPeriodicFunctions
import YangMills.Construction.Towers.SumsAndCompositesOfPeriodicLinearMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.PeriodicTowerMaps
open OneStepChart
theorem agreeWithTorusMaps
    (hTwo : PeriodicOperatorIsTwoScaleMap)
    (hAlg : PeriodicOperatorAlgebra.Statement)
    (hCells : CellsReadAtPlaces.Statement)
    (hFine : FineOnlyVertexCoordinates.Statement)
    (hCob : CoboundaryRestrictionPeriodicity.Statement)
    (hCross : CrossingSmoothingIsPeriodicOperator)
    (hVert : VertexSmoothingIsPeriodic)
    (hCont : ContourAveragesPeriodic.Statement)
    (hFull : FullSpace.OneStepComplexForms.OneStepClaim)
    (hPer : PeriodicCoarseningStep.Holds) :
    AgreeWithTorusMaps := by
  intro L hL m k hm
  have hL0 : 0 < L := by have := hL.2; omega
  have hpos : 0 < 2 * L ^ m := by positivity
  have alg := hAlg _ hpos
  have two := hTwo _ hpos
  have vtx : ∀ j, j ≤ k → CellCoordinates (2 * L ^ m) (vertexFunctions L m k j) :=
    fun j h => (hCells L hL m k j hm h).1.some
  have edg : ∀ j, j ≤ k → CellCoordinates (2 * L ^ m) (edgeForms L m k j) :=
    fun j h => (hCells L hL m k j hm h).2.1.some
  have fac : ∀ j, j ≤ k → CellCoordinates (2 * L ^ m) (faceFunctions L m k j) :=
    fun j h => (hCells L hL m k j hm h).2.2.some
  have fine : ∀ j, j < k → CellCoordinates (2 * L ^ m) (fineOnlyVertexFunctions L m k j) :=
    fun j h => (hFine L hL m k j hm h).some
  obtain ⟨dVert, dEdge, res⟩ := hCob L hL m k hm
  have crs := fun j (h : j < k) => hCross L hL m k j hm h
  have sm := fun j (h : j < k) => hVert L hL m k j hm h
  have cub := fun j (h : j < k) => (hCont L hL m k j hm h).1
  have fcub := fun j (h : j < k) => (hCont L hL m k j hm h).2
  have lin : ∀ j (h : j < k), PeriodicOperator (edgeForms L m k j) (edgeForms L m k (j + 1))
      (FullSpace.linearSmoothing L) (Tower.linearSmoothing L m k j) := by
    intro j h
    have dc := alg.comp _ _ _ (edg j h.le) (vtx (j + 1) h) (edg (j + 1) h) _ _ _ _
      (cub j h) (dVert (j + 1) h)
    have df := alg.sub _ _ (edg j h.le) (edg (j + 1) h) _ _ _ _ (crs j h) dc
    exact alg.congr _ _ (edg j h.le) (edg (j + 1) h) _ _ _ _ df
      (fun f hf => (hFull L hL k j h).linearSmoothing_eq f hf)
      (fun f hf => (hPer L hL m k j hm h).linearSmoothing_eq f hf)
  have linIt : ∀ j, j ≤ k → PeriodicOperator (edgeForms L m k 0) (edgeForms L m k j)
      (FullSpace.linearSmoothingIter L k j) (Tower.linearSmoothingIter L m k j) := by
    intro j
    induction j with
    | zero => exact fun _ => alg.id _ (edg 0 (Nat.zero_le k))
    | succ j ih =>
      intro h
      exact alg.comp _ _ _ (edg 0 (Nat.zero_le k)) (edg j (by omega)) (edg (j + 1) h) _ _ _ _
        (ih (by omega)) (lin j h)
  have crsIt : ∀ j, j ≤ k → PeriodicOperator (edgeForms L m k 0) (edgeForms L m k j)
      (FullSpace.crossingSmoothingIter L k j) (Tower.crossingSmoothingIter L m k j) := by
    intro j
    induction j with
    | zero => exact fun _ => alg.id _ (edg 0 (Nat.zero_le k))
    | succ j ih =>
      intro h
      exact alg.comp _ _ _ (edg 0 (Nat.zero_le k)) (edg j (by omega)) (edg (j + 1) h) _ _ _ _
        (ih (by omega)) (crs j h)
  have smIt : ∀ j, j ≤ k → PeriodicOperator (vertexFunctions L m k 0) (vertexFunctions L m k j)
      (FullSpace.vertexSmoothingIter L k j) (Tower.vertexSmoothingIter L m k j) := by
    intro j
    induction j with
    | zero => exact fun _ => alg.id _ (vtx 0 (Nat.zero_le k))
    | succ j ih =>
      intro h
      exact alg.comp _ _ _ (vtx 0 (Nat.zero_le k)) (vtx j (by omega)) (vtx (j + 1) h) _ _ _ _
        (ih (by omega)) (sm j h)
  have summand : ∀ i j, i < j → j ≤ k →
      PeriodicOperator (edgeForms L m k 0) (vertexFunctions L m k j)
      (fun B => FullSpace.restrictVertexFunction (Tower.meshAt L k j)
        (FullSpace.cubeContourAverage L (a := Tower.meshAt L k (i + 1))
          (FullSpace.crossingSmoothingIter L k i B)))
      (fun B => Tower.restrictVertexFunction j
        (Tower.cubeContourAverage L m k i (Tower.crossingSmoothingIter L m k i B))) := by
    intro i j hij hj
    have hi : i < k := by omega
    have head := alg.comp _ _ _ (edg 0 (Nat.zero_le k)) (edg i hi.le) (vtx (i + 1) hi) _ _ _ _
      (crsIt i hi.le) (cub i hi)
    exact alg.comp _ _ _ (edg 0 (Nat.zero_le k)) (vtx (i + 1) hi) (vtx j hj) _ _ _ _ head
      (res (i + 1) j hij hj)
  have partialSums : ∀ j, j ≤ k → ∀ r, r ≤ j →
      PeriodicOperator (edgeForms L m k 0) (vertexFunctions L m k j)
      (fun B => ∑ i ∈ Finset.range r, FullSpace.restrictVertexFunction (Tower.meshAt L k j)
        (FullSpace.cubeContourAverage L (a := Tower.meshAt L k (i + 1))
          (FullSpace.crossingSmoothingIter L k i B)))
      (fun B => ∑ i ∈ Finset.range r, Tower.restrictVertexFunction j
        (Tower.cubeContourAverage L m k i (Tower.crossingSmoothingIter L m k i B))) := by
    intro j hj r
    induction r with
    | zero =>
      intro _
      exact alg.congr _ _ (edg 0 (Nat.zero_le k)) (vtx j hj) _ _ _ _
        (alg.zero _ _ (edg 0 (Nat.zero_le k)) (vtx j hj))
        (fun _ _ => Finset.sum_empty) (fun _ _ => Finset.sum_empty)
    | succ r ih =>
      intro hr
      exact alg.congr _ _ (edg 0 (Nat.zero_le k)) (vtx j hj) _ _ _ _
        (alg.add _ _ (edg 0 (Nat.zero_le k)) (vtx j hj) _ _ _ _ (ih (by omega))
          (summand r j (by omega) hj))
        (fun f _ => Finset.sum_range_succ _ _) (fun f _ => Finset.sum_range_succ _ _)
  have cubIt : ∀ j, j ≤ k → PeriodicOperator (edgeForms L m k 0) (vertexFunctions L m k j)
      (FullSpace.cubeContourAverageIter L k j) (Tower.cubeContourAverageIter L m k j) :=
    fun j hj => partialSums j hj j le_rfl
  exact
    { vertexCoboundary := fun j h => two _ _ (vtx j h) (edg j h) _ _ (dVert j h)
      edgeCoboundary := fun j h => two _ _ (edg j h) (fac j h) _ _ (dEdge j h)
      restrict := fun j h => two _ _ (vtx j h.le) (vtx (j + 1) h) _ _
        (res j (j + 1) (Nat.le_succ j) h)
      linear := fun j h => two _ _ (edg j h.le) (edg (j + 1) h) _ _ (lin j h)
      crossing := fun j h => two _ _ (edg j h.le) (edg (j + 1) h) _ _ (crs j h)
      cubeContour := fun j h => two _ _ (edg j h.le) (vtx (j + 1) h) _ _ (cub j h)
      vertexSmoothing := fun j h => two _ _ (vtx j h.le) (vtx (j + 1) h) _ _ (sm j h)
      fineOnlyContour := fun j h => two _ _ (edg j h.le) (fine j h) _ _ (fcub j h)
      linearIter := fun j h => two _ _ (edg 0 (Nat.zero_le k)) (edg j h) _ _ (linIt j h)
      crossingIter := fun j h => two _ _ (edg 0 (Nat.zero_le k)) (edg j h) _ _ (crsIt j h)
      vertexSmoothingIter := fun j h => two _ _ (vtx 0 (Nat.zero_le k)) (vtx j h) _ _ (smIt j h)
      cubeContourIter := fun j h => two _ _ (edg 0 (Nat.zero_le k)) (vtx j h) _ _ (cubIt j h) }
end YangMills.Construction.Tower.UnitScale.PeriodicTowerMaps
end
