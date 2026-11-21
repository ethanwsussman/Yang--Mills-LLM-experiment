import YangMills.Construction.DirichletOperator.ScaledCoordinatesOfTheBareLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BareDilation.CurlForm
open Set
open RegionSequence RegionSequence.NestedRegions
variable {L j N : ℕ} {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
theorem dilateEquiv_axisMultiple (R : DilationData 𝒯 S r) (μ : Fin 4) :
    R.dilateEquiv (PeriodicLattice.axisMultiple μ S.fineMesh.h) =
      (Dirichlet.unitStep 4 𝒯.side 𝒯.ξ μ : 𝒯.Point) := by
  funext ν
  change AddCircle.equivAddCircle (N : ℝ) 𝒯.side R.period_ne_zero R.side_ne_zero
      (PeriodicLattice.axisMultiple μ S.fineMesh.h ν) = ((Pi.single μ 𝒯.ξ : Fin 4 → ℝ) ν : AddCircle 𝒯.side)
  by_cases h : ν = μ
  · subst h
    simpa [PeriodicLattice.axisMultiple] using R.circle_mesh_eq
  · simp [PeriodicLattice.axisMultiple, Pi.single_eq_of_ne h]
def curlLinearMap : (𝒯.FineBond → ℝ) →ₗ[ℝ] (𝒯.FinePlaquette → ℝ) where
  toFun := curlTorus
  map_add' A B := by
    funext p
    simp only [curlTorus, Dirichlet.forwardDiff, comp, Pi.add_apply]
    ring
  map_smul' c A := by
    funext p
    simp only [curlTorus, Dirichlet.forwardDiff, comp, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
end YangMills.Construction.BareDilation.CurlForm
