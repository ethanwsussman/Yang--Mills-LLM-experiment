import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import YangMills.Construction.Lattice.DirichletLaplacianWithItsBoundaryTermProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
open SeparatedSequences.BaseParameters (bondAxis)
noncomputable section
namespace DirichletCurl
variable {L m K : ℕ}
theorem meshSize_coe_ne_zero (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by apply _root_.YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary.meshSize_coe_ne_zero <;> assumption
theorem unitStep_apply_self (j : ℤ) (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.SharedProofs.p39116 <;> assumption
theorem unitStep_apply_of_ne (j : ℤ) {μ ν : Fin 4} (h : ν ≠ μ) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν = 0 := by
  change Pi.single (M := fun _ => AddCircle (torusSide L m)) μ
    ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ν = 0
  simp [Pi.single_eq_of_ne h]
theorem unitStep_ne_zero (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) (μ : Fin 4) :
    unitStep L m j μ ≠ 0 := by
  intro h
  have h' := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  simp only [unitStep_apply_self] at h'
  exact meshSize_coe_ne_zero hL hj h'
theorem unitStep_ne_unitStep (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) {μ ν : Fin 4} (hne : μ ≠ ν) :
    unitStep L m j μ ≠ unitStep L m j ν := by
  intro h
  have h' := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  simp only [unitStep_apply_self, unitStep_apply_of_ne j hne] at h'
  exact meshSize_coe_ne_zero hL hj h'
theorem unitStep_add_unitStep_ne_zero (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) {μ ν : Fin 4}
    (hne : μ ≠ ν) : unitStep L m j μ + unitStep L m j ν ≠ 0 := by
  intro h
  have h' := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  simp only [AddSubgroup.coe_add, Pi.add_apply, unitStep_apply_self,
    unitStep_apply_of_ne j hne, add_zero, AddSubgroup.coe_zero, Pi.zero_apply] at h'
  exact meshSize_coe_ne_zero hL hj h'
variable {t : ℕ} {Ω : Set (FourTorus L m)}
theorem interiorBonds_subset_framedBonds (φ : BondFrame) :
    interiorBonds K Ω ⊆ framedBonds K Ω φ := by apply _root_.YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary.interiorBonds_subset_framedBonds <;> assumption
end DirichletCurl
end
end YangMills.Construction
