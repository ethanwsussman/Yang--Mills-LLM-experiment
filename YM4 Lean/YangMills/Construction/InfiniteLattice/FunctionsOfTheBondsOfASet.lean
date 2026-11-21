import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsStarClosedFunctionAlgebra (M : Set (GaugeField (1 : ℝ) → ℂ)) : Prop :=
  (∃ V : Submodule ℂ (GaugeField (1 : ℝ) → ℂ), (V : Set (GaugeField (1 : ℝ) → ℂ)) = M) ∧
  (∀ F ∈ M, ∀ G ∈ M, F * G ∈ M) ∧
  (∀ F ∈ M, (fun U => starRingEnd ℂ (F U)) ∈ M) ∧
  ∀ c : ℂ, (fun _ => c) ∈ M
def LinkLocalFunctions.Statement : Prop :=
  (∀ (S : Set AmbientSpace) (F : GaugeField (1 : ℝ) → ℂ), IsBoundedObservable F →
    (F ∈ unitRegionObservables S ↔
      ∀ U U' : GaugeField (1 : ℝ), (∀ b : Link (1 : ℝ), b.IsWithin S → U b = U' b) →
        F U = F U')) ∧
  (∀ S : Set AmbientSpace, IsStarClosedFunctionAlgebra (unitRegionObservables S)) ∧
  (∀ S S' : Set AmbientSpace, S ⊆ S' → unitRegionObservables S ⊆ unitRegionObservables S') ∧
  (∀ S S' : Set AmbientSpace,
    unitRegionObservables S ∩ unitRegionObservables S' = unitRegionObservables (S ∩ S')) ∧
  IsStarClosedFunctionAlgebra {F | IsBoundedObservable F ∧ IsLocalObservable F} ∧
  (∀ μ : Fin 4, IsStarClosedFunctionAlgebra
    (halfSpaceLocalObservables μ : Set (GaugeField (1 : ℝ) → ℂ))) ∧
  ∀ μ : Fin 4, ∀ F ∈ halfSpaceLocalObservables μ,
    ∃ Q : Set AmbientSpace, Bornology.IsBounded Q ∧
      F ∈ unitRegionObservables (closedHalfSpace μ ∩ Q)
end YangMills.Construction.InfiniteLattice
