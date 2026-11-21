import YangMills.Construction.InfiniteLattice.MirrorGridsCopiesAndChessboardValuesOfMultipleReflections
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MultipleReflections
namespace Setup.Grid
variable {D : Setup} (G : D.Grid)
def EdgeOverSpacingOdd (j : ℤ) : Prop :=
  G.edge / D.mesh = (D.L : ℝ) ^ (j + ((D.K : ℕ) : ℤ)) ∧
  (∃ n : ℤ, Odd n ∧ (D.L : ℝ) ^ (j + ((D.K : ℕ) : ℤ)) = (n : ℝ)) ∧
  ∃ i : ℤ, G.edge / 2 = D.mesh * ((i : ℝ) + 1 / 2)
def WallsBisectLinks : Prop :=
  ∀ (α : Fin 4) (n : ℤ), ∃ P : InfiniteLattice.LatticeMirror D.mesh,
    P.cls = .axial α ∧ P.plane = G.wall α n ∧ P.BisectsLinks
def TileCentersAreSites : Prop :=
  ∀ k : Fin 4 → ℤ, G.tileCenter k ∈ CutoffLattice.latticeAt D.L (D.K : ℕ)
def UniqueElementBetweenTiles : Prop :=
  ∀ k k' : Fin 4 → ℤ, ∃ g : G.reflectionGroup,
    (∀ h : G.reflectionGroup,
      ((h : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) '' G.tile k = G.tile k' ↔ h = g) ∧
    ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) = G.tileReflection k k' ∧
    G.orientation g = (((tileSign k k' : ℤˣ) : ℤ) : ℝ)
def IsCoordinateMove (α : Fin 4) (δ : ℝ → ℝ) : Prop :=
  (∃ n : ℤ, ∀ y, δ y = y + 2 * (n : ℝ) * G.edge) ∨
    ∃ n : ℤ, ∀ y, δ y = 2 * (G.shift α + (n : ℝ) * G.edge) - y
def ActsCoordinatewise (f : AmbientSpace → AmbientSpace) : Prop :=
  ∃ δ : Fin 4 → ℝ → ℝ, (∀ α, G.IsCoordinateMove α (δ α)) ∧ ∀ x α, f x α = δ α (x α)
def GroupEqCoordinatewiseMaps : Prop :=
  (∀ g : G.reflectionGroup,
    G.ActsCoordinatewise ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace)) ∧
  ∀ f : AmbientSpace → AmbientSpace, G.ActsCoordinatewise f →
    ∃ g : G.reflectionGroup, ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) = f
end Setup.Grid
def GridElementaryFacts : Prop :=
  ∀ (D : Setup) (G : D.Grid) (j : ℤ), G.edge = (D.L : ℝ) ^ j →
    G.EdgeOverSpacingOdd j ∧
    G.WallsBisectLinks ∧
    G.TileCentersAreSites ∧
    G.UniqueElementBetweenTiles ∧
    G.GroupEqCoordinatewiseMaps
end MultipleReflections
end YangMills.Construction
end
