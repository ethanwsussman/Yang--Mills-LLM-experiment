import YangMills.Construction.InfiniteLattice.ObservablesThatReadASet
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
structure IsUnitalStarClosed {Ω : Type*} (𝒜 : Set (Ω → ℂ)) : Prop where
  add_mem : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A + B ∈ 𝒜
  mul_mem : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B ∈ 𝒜
  smul_mem : ∀ (z : ℂ), ∀ A ∈ 𝒜, z • A ∈ 𝒜
  conj_mem : ∀ A ∈ 𝒜, (fun ω => starRingEnd ℂ (A ω)) ∈ 𝒜
  const_mem : ∀ z : ℂ, (fun _ => z) ∈ 𝒜
namespace RegionReadout
def TruncationContinuousAndCharacterizes (L K : ℕ) : Prop :=
  ∀ S : Set AmbientSpace,
    Continuous (LatticePhases.truncate S :
      GaugeFieldAtScale L K → GaugeFieldAtScale L K) ∧
    ∀ F : GaugeFieldAtScale L K → ℂ, IsBoundedObservable F →
      List.TFAE
        [F ∈ cutoffRegionObservables L K S,
         ∀ U V : GaugeFieldAtScale L K,
           (∀ b : Link (PeriodicLattice.meshSize L (K : ℤ)), b.LiesIn S → U b = V b) → F U = F V,
         F = F ∘ LatticePhases.truncate S]
def RegionAlgebrasMonotone (L K : ℕ) : Prop :=
  (∀ S : Set AmbientSpace,
    IsUnitalStarClosed (cutoffRegionObservables L K S) ∧
      IsUnitalStarClosed (cutoffLocalRegionObservables L K S)) ∧
  (∀ S T : Set AmbientSpace, S ⊆ T →
    cutoffRegionObservables L K S ⊆ cutoffRegionObservables L K T ∧
      cutoffLocalRegionObservables L K S ⊆ cutoffLocalRegionObservables L K T) ∧
  (∀ S : Set AmbientSpace, cutoffLocalRegionObservables L K S ⊆ cutoffRegionObservables L K S) ∧
  cutoffRegionObservables L K Set.univ = {F | IsBoundedObservable F}
def RegionAlgebrasInterAndLocal (L K : ℕ) : Prop :=
  (∀ S T : Set AmbientSpace,
    cutoffRegionObservables L K S ∩ cutoffRegionObservables L K T =
      cutoffRegionObservables L K (S ∩ T)) ∧
  ∀ S : Set AmbientSpace,
    cutoffLocalRegionObservables L K S =
        {F | IsBoundedObservable F ∧ IsLocalObservable F ∧ IsRegionMeasurable S F} ∧
      cutoffLocalRegionObservables L K S =
        ⋃ Q ∈ {Q : Set AmbientSpace | Bornology.IsBounded Q}, cutoffRegionObservables L K (S ∩ Q)
def Summary : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K →
    TruncationContinuousAndCharacterizes L K ∧ RegionAlgebrasMonotone L K ∧
      RegionAlgebrasInterAndLocal L K
end RegionReadout
end YangMills.Construction.InfiniteLattice
end
