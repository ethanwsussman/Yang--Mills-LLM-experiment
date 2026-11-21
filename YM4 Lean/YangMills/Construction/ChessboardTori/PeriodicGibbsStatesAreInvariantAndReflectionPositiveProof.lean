import YangMills.Construction.ChessboardTori.PeriodicGibbsStatesAreInvariantAndReflectionPositive
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivity
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.PeriodicStateSymmetries
open YangMills.Construction.InfiniteLattice (IsSymmetricUnder IsReflectionPositiveAt LatticeMirror GaugeField
  AmbientSpace IsPeriodicGibbs LatticeSymmetry)
open YangMills.Construction.InfiniteLattice.PeriodicGibbsAtSpacing (HasSymmetriesAndReflectionPositivity)
theorem latticeSymmetry_ext {a : ℝ} {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem exists_mem_hyperoctahedralLinearGroup_of_mem {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ InfiniteLattice.hypercubicGroup) :
    ∃ w' ∈ InfiniteLattice.hyperoctahedralLinearGroup, ∀ x, w' x = w x := by
  obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  have hinj : Function.Injective (InfiniteLattice.frameLinearMap f) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    have h := congrFun hx (f.1.symm i)
    rcases Int.units_eq_one_or (f.2 (f.1.symm i)) with hs | hs <;>
      simpa [InfiniteLattice.frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, hs] using h
  refine ⟨LinearEquiv.ofBijective (InfiniteLattice.frameLinearMap f)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, ?_, fun x => rfl⟩
  exact (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff _).mpr ⟨f.1, f.2, fun x j => rfl⟩
theorem isSymmetricUnder_and_isReflectionPositiveAt
    (hM : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement)
    {a : ℝ} (ha : 0 < a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (hν : HasSymmetriesAndReflectionPositivity ν) (P : LatticeMirror a) :
    IsSymmetricUnder ν P.symmetry ∧ IsReflectionPositiveAt ν P := by
  obtain ⟨hsets, -, -, -, -, hrefl, -, -, hwords⟩ := hM ⟨a, ha⟩
  obtain ⟨Q, hQ, hpts⟩ := (hsets P.plane).mp ⟨P, rfl⟩
  obtain ⟨hinv, -, -, hpos⟩ := hν.2.2 Q hQ
  have heq : P.symmetry = LatticeConventions.NormalHyperplane.reflectSymmetry hQ :=
    latticeSymmetry_ext (hrefl Q hQ P hpts.symm).1
  exact ⟨heq ▸ hinv, ((hwords Q hQ P hpts.symm ν).1).mpr hpos⟩
theorem holds (hGibbs : InfiniteLattice.PeriodicGibbsAtSpacing.Statement)
    (hM : LatticeConventions.LatticeMirrorsAndReflectionPositivity.Statement) : Statement := by
  intro D ν hν
  have hν' : IsPeriodicGibbs D.β ν := hν
  have : IsProbabilityMeasure ν := hν'.1.1
  have hP : HasSymmetriesAndReflectionPositivity ν :=
    (hGibbs D.mesh D.mesh_pos D.β D.beta_pos).1 ν hν'
  refine ⟨hP.1, fun i c hc => isSymmetricUnder_and_isReflectionPositiveAt hM D.mesh_pos ν hP _,
    fun i i' c _ _ P _ => isSymmetricUnder_and_isReflectionPositiveAt hM D.mesh_pos ν hP P,
    fun w => ?_⟩
  obtain ⟨w', hw', h⟩ := exists_mem_hyperoctahedralLinearGroup_of_mem w.2
  exact hP.2.1 _ w' hw' fun x => (h x).symm
end YangMills.Construction.ChessboardTori.PeriodicStateSymmetries
end
