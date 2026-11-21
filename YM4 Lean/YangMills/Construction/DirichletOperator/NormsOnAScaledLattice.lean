import YangMills.Construction.DirichletOperator.ScaledCoordinatesOfTheBareLattice
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.BareDilation
variable {L j N : ℕ}
structure PulledNorms {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N}
    {r : ℝ} (D : DilationData 𝒯 S r) : Prop where
  lOneNorm_eq : ∀ u u' : PeriodicLattice.Torus 4 N,
    Torus.lOneNorm (D.dilateEquiv u - D.dilateEquiv u') = r * PeriodicLattice.taxicabDist u u'
  supNorm_eq : ∀ u u' : PeriodicLattice.Torus 4 N,
    Torus.supNorm (D.dilateEquiv u - D.dilateEquiv u') = r * PeriodicLattice.maxDist u u'
  exists_near : ∀ u : PeriodicLattice.Torus 4 N, ∃ x : PeriodicLattice.DilatedSite 4 S.fineMesh r,
    x ∈ PeriodicLattice.dilatedBall S.fineMesh r u
  bondInner_eq : ∀ A A' : 𝒯.FineBond → ℝ,
    bondInner A A' = PeriodicLattice.dilatedInner 4 S.fineMesh r (D.pullBond A) (D.pullBond A')
  tensorInner_one_eq : ∀ J J' : 𝒯.Tensor 1,
    tensorInner J J' =
      PeriodicLattice.dilatedInner 4 S.fineMesh r (D.pullTensorOne J) (D.pullTensorOne J')
  tensorInner_two_eq : ∀ J J' : 𝒯.Tensor 2,
    tensorInner J J' =
      PeriodicLattice.dilatedInner 4 S.fineMesh r (D.pullTensorTwo J) (D.pullTensorTwo J')
  supSite_eq : ∀ ζ : 𝒯.FineSite → ℝ,
    supSite ζ = PeriodicLattice.dilatedFunSupNorm (D.pullSite ζ)
  supBond_eq : ∀ A : 𝒯.FineBond → ℝ, supBond A = PeriodicLattice.dilatedSupNorm (D.pullBond A)
  supTensor_eq : ∀ J : 𝒯.Tensor 1,
    supTensor J = PeriodicLattice.dilatedSupNorm (D.pullTensorOne J)
  holderSite_eq : ∀ (α t : ℝ) (ζ : 𝒯.FineSite → ℝ),
    holderSite α t ζ = PeriodicLattice.funHolderAt t α (D.pullSite ζ)
  holderBond_eq : ∀ (α t : ℝ) (A : 𝒯.FineBond → ℝ),
    holderBond α t A = PeriodicLattice.fieldHolderAt t α (D.pullBond A)
  holderTensor_eq : ∀ (α t : ℝ) (J : 𝒯.Tensor 1),
    holderTensor α t J = PeriodicLattice.fieldHolderAt t α (D.pullTensorOne J)
end YangMills.Construction.BareDilation
