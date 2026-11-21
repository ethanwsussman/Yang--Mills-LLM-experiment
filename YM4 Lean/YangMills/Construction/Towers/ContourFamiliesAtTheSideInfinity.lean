import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {a a' : ℝ}
def LinksJoin : AmbientSpace → AmbientSpace → List (InfiniteLattice.Link a') → Prop
  | p, q, [] => p = q
  | p, q, b :: Γ => (b.initial : AmbientSpace) = p ∧ LinksJoin (b.terminal : AmbientSpace) q Γ
def supportAxes (ν : Fin 4 → ℤ) : Finset (Fin 4) :=
  Finset.univ.filter fun μ => ν μ ≠ 0
def IsStaircasePath (ν : Fin 4 → ℤ) (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a')
    (σ : Fin (supportAxes ν).card ≃ supportAxes ν)
    (Γ : List (InfiniteLattice.Link a')) : Prop :=
  IsLinkPath Γ ∧ LinksJoin (y : AmbientSpace) (x : AmbientSpace) Γ ∧
    ∃ y' : InfiniteLattice.LatticePoint a', (y' : AmbientSpace) = y ∧
      Γ = stepsInOrder ν y'
        ((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4))
def IsStaircaseFamily (L : ℕ) (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a')
    (𝒢 : Set (List (InfiniteLattice.Link a'))) : Prop :=
  ∃ ν : Fin 4 → ℤ, IsCubeOffset L y x ν ∧
    (∀ σ, ∃! Γ, IsStaircasePath ν y x σ Γ) ∧
    𝒢 = {Γ | ∃ σ, IsStaircasePath ν y x σ Γ}
def StaircaseContoursWellDefined : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ k → 1 ≤ j → j ≤ k →
    ∀ y : Vertex L k j, ∀ x ∈ cube L (Tower.meshAt L k (j - 1)) y,
      ∃ s : Vertex L k (j - 1), (s : AmbientSpace) = x ∧
        (∃! 𝒢, IsStaircaseFamily L y s 𝒢) ∧
        IsStaircaseFamily L y s (contourSet L y s) ∧
        (∀ Γ ∈ contourSet L y s, IsLinkPath Γ) ∧
        (contourSet L y s).Nonempty ∧
        (contourSet L y s).Finite
end YangMills.Construction.Tower.FullSpace
end
