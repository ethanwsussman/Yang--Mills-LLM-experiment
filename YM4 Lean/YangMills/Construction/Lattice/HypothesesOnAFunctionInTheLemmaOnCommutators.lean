import YangMills.Construction.Lattice.SitesNearASiteAndTheirCells
import YangMills.Construction.PeriodicLattice.LevelProjectionAndLiftedCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences
namespace SeparatedRegions
variable {L m : ℕ} (S : ScaleData)
def pulledBack (f : FourTorus L m → ℝ) : (Fin 4 → ℝ) → ℝ :=
  f ∘ levelProj L m S.levels S.unitLevel
def firstPartialDeriv (f : FourTorus L m → ℝ) (μ : Fin 4) (w : Fin 4 → ℝ) : ℝ :=
  fderiv ℝ (pulledBack S f) w (Pi.single μ 1)
def secondPartialDeriv (f : FourTorus L m → ℝ) (μ ν : Fin 4) (w : Fin 4 → ℝ) : ℝ :=
  fderiv ℝ (firstPartialDeriv S f ν) w (Pi.single μ 1)
structure IsCommutatorTestFunction (Ω : ℕ → Set (FourTorus L m)) (f : FourTorus L m → ℝ)
    (θ : ℝ) : Prop where
  one_le_theta : 1 ≤ θ
  contDiffOn_nhd : ∃ U : Set (FourTorus L m), IsOpen U ∧ Ω 0 ⊆ U ∧
    ContDiffOn ℝ 2 (pulledBack S f) (levelProj L m S.levels S.unitLevel ⁻¹' U)
  abs_le_one : ∀ y ∈ layerPoints S Ω, ∀ p ∈ nearbyCellsUnion S Ω y, |f p| ≤ 1
  first_deriv_bound : ∀ y ∈ layerPoints S Ω, ∀ w : Fin 4 → ℝ,
    levelProj L m S.levels S.unitLevel w ∈ nearbyCellsUnion S Ω y → ∀ μ : Fin 4,
      layerPointMesh S Ω y * |firstPartialDeriv S f μ w| ≤ θ⁻¹
  second_deriv_bound : ∀ y ∈ layerPoints S Ω, ∀ w : Fin 4 → ℝ,
    levelProj L m S.levels S.unitLevel w ∈ nearbyCellsUnion S Ω y → ∀ μ ν : Fin 4,
      layerPointMesh S Ω y ^ 2 * |secondPartialDeriv S f μ ν w| ≤ θ⁻¹
end SeparatedRegions
end YangMills.Construction
