import YangMills.Construction.InequalityOnMirroredCopies.CentreOfACopyProof
import YangMills.Construction.SystemOfAdmissibleConstants.MeansAndValuesOfACellFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open ChessboardTori ReflectedCopies
open InfiniteLattice (periodicGibbsSet smearedEnergy)
open ReflectionsAndOneInsertion (complexSmeared)
namespace CellFunctionMeans
private theorem sub_const_mem_cellObservables {D : ChessboardSetup} {S : Set InfiniteLattice.AmbientSpace}
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (z : ℂ) :
    (fun U => F U - z) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.SharedProofs.p60740 <;> assumption
private theorem chessboardNormOfCell_add_const_le (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) {D : ChessboardSetup} (g : ReflectionGrid D)
    (hg : g.HasAdmissibleSide) (h2 : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {S : Set InfiniteLattice.AmbientSpace} (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (z : ℂ) {E : D.GaugeField → ℂ} (hE : ∀ U, E U = F U + z) :
    g.chessboardNormOfCell S E ≤ g.chessboardNormOfCell S F + ‖z‖ := by
  obtain ⟨-, hii, -⟩ := hC D g hg h2
  obtain ⟨-, -, -, -, -, -, htor, -, -⟩ := hG D g hg
  obtain ⟨-, -, -, -, -, hread, -⟩ := htor h2
  have hR := (hread S hS F hF).1
  have hcell : D.proj '' S ∈ g.torusCellSet := ⟨S, hS, rfl⟩
  obtain ⟨hlaws, h1mem, h1⟩ := hii _ hcell
  obtain ⟨hzmem, hz⟩ := (hlaws _ h1mem).2.1 z
  have hadd := ((hlaws _ hR).1 _ hzmem).2
  have heq : D.liftedObservable E = D.liftedObservable F + z • (fun _ => (1 : ℂ)) := by
    funext U
    simp [ChessboardSetup.liftedObservable, hE]
  unfold ReflectionGrid.chessboardNormOfCell
  rw [heq]
  rw [hz, h1, mul_one] at hadd
  exact hadd
end CellFunctionMeans
theorem cellFunctionMeanBounds_holds
    (hK : ReflectedCopies.CopyCentreBound) (hO : ReflectedCopies.SmearedMemCellObservables)
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides) (hG : MirrorGridsAllSides.ReflectionGridProperties) :
    CellFunctionMeanBounds := by
  intro D A b hA hb hI c ϱ h hh
  obtain ⟨κ, htor, hst⟩ := hK D A b hA hb hI c ϱ h hh
  have hobs := hO D c ϱ h hh
  refine ⟨κ, fun ν hν => ?_, fun m' hm' => (htor m' hm').2, fun e he => ?_⟩
  · have hb' := hst ν hν
    have hv : MirrorGridsAllSides.GridSetup.integralOf D ν (complexSmeared D h) =
        ((∫ U, smearedEnergy h U ∂ν : ℝ) : ℂ) :=
      integral_ofReal
    rwa [hv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb'
  · have hmem : ∀ x : ℝ, centredSmeared D h x ∈ ReflectionGrid.cellObservables (D := D) c.cell :=
      fun x => CellFunctionMeans.sub_const_mem_cellObservables hobs (x : ℂ)
    refine ⟨hmem e, fun m' hm' => ?_⟩
    have hshift := CellFunctionMeans.chessboardNormOfCell_add_const_le hC hG (D := D.withExponent m')
      (c.grid.withExponent m') c.hasAdmissibleSide hm' c.cell_mem_cellSet (hmem κ) (((κ - e : ℝ)) : ℂ)
      (E := centredSmeared D h e) fun U => by
        simp only [centredSmeared, Complex.ofReal_sub]
        ring
    have hnorm : ‖(((κ - e : ℝ)) : ℂ)‖ = |e - κ| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [hnorm] at hshift
    have hval := (htor m' hm').1
    linarith
end YangMills.Construction.AdmissibleConstants
end
