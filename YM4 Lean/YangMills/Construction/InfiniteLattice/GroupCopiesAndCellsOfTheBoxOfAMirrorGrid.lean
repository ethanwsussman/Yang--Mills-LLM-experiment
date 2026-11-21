import YangMills.Construction.InfiniteLattice.MirrorGridsCopiesAndChessboardValuesOfMultipleReflections
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace Setup.Grid
variable {D : Setup} (G : D.Grid)
def orientationUnit (g : G.reflectionGroup) : ℤˣ :=
  open Classical in if G.orientation g = 1 then 1 else -1
def ElementsPermuteTiles : Prop :=
  ∀ g : G.reflectionGroup,
    (∃ s : D.LatticeSymmetry,
      s.toFun = ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace)) ∧
    ∀ k : Fin 4 → ℤ, ∃ k' : Fin 4 → ℤ,
      (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k = G.tile k' ∧
      (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tileInterior k = G.tileInterior k'
def OrientationIsHom : Prop :=
  (∃ φ : G.reflectionGroup →* ℤˣ, ∀ g : G.reflectionGroup,
      (((φ g : ℤˣ) : ℤ) : ℝ) = G.orientation g) ∧
  ∀ (μ : Fin 4) (n : ℤ) (g : G.reflectionGroup),
    (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) = G.wallReflectEquiv μ n → G.orientation g = -1
def TileReflectionsCompose : Prop :=
  (∀ k : Fin 4 → ℤ, G.tileReflection k k = id) ∧
  (∀ (g : G.reflectionGroup) (k k' k'' : Fin 4 → ℤ),
    (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'' →
    ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) ∘ G.tileReflection k k' =
      G.tileReflection k k'') ∧
  (∀ k k' k'' : Fin 4 → ℤ, G.tileReflection k' k'' ∘ G.tileReflection k k' = G.tileReflection k k'') ∧
  ∀ k k' k'' : Fin 4 → ℤ, tileSign k' k'' * tileSign k k' = tileSign k k''
def ReflectedCopyRules : Prop :=
  ∀ (k k' : Fin 4 → ℤ) (F : D.GaugeField → ℂ), F ∈ G.tileAlgebra k →
    G.reflectedCopy k k' F ∈ G.tileAlgebra k' ∧
    G.reflectedCopy k k F = F ∧
    InfiniteLattice.observableSupNorm (G.reflectedCopy k k' F) = InfiniteLattice.observableSupNorm F ∧
    ∀ (g : G.reflectionGroup) (k'' : Fin 4 → ℤ),
      (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) '' G.tile k' = G.tile k'' →
      Conventions.signedConjFun (G.orientationUnit g)
        ((G.toLatticeSymmetry D.isAdmissible g).actOn (G.reflectedCopy k k' F)) =
      G.reflectedCopy k k'' F
def TilesPerSideEven (j : ℤ) : Prop :=
  j ≤ ((D.m : ℕ) : ℤ) ∧
  G.tilesPerSide = 2 * (D.L : ℝ) ^ (((D.m : ℕ) : ℤ) - j) ∧
  ∃ n : ℤ, Even n ∧ 2 ≤ n ∧ G.tilesPerSide = n
def PeriodShiftsInGroup : Prop :=
  ∀ v ∈ InfiniteLattice.latticeSubgroup D.side, ∃ hv : v ∈ InfiniteLattice.latticeSubgroup D.mesh,
    (∃ g : G.reflectionGroup,
      ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) =
        (InfiniteLattice.shift ⟨v, hv⟩).toFun ∧
      G.orientation g = 1) ∧
    ∃ q : Fin 4 → ℤ, (∀ μ, (q μ : ℝ) = v μ / G.edge) ∧
      (∃ p : Fin 4 → ℤ, ∀ μ, (q μ : ℝ) = G.tilesPerSide * (p μ : ℝ)) ∧
      ∀ k : Fin 4 → ℤ,
        (InfiniteLattice.shift ⟨v, hv⟩).toFun '' G.tile k = G.tile (k + q)
def TilesCongruentToBoxTile : Prop :=
  (∀ k₀ : Fin 4 → ℤ, ∀ S ∈ G.tiling,
    ∃! S' : Set AmbientSpace, S' ∈ G.tile '' {k | k - k₀ ∈ G.boxTileIndices} ∧ G.AreCongruent S S') ∧
  ∀ S ∈ G.tiling, ∃! S' : Set AmbientSpace, S' ∈ G.boxTiles ∧ G.AreCongruent S S'
def BoxTilesSignBalanced (k : Fin 4 → ℤ) : Prop :=
  (G.boxTileIndices.ncard : ℝ) = G.tilesPerSide ^ 4 ∧
  (({k' | k' ∈ G.boxTileIndices ∧ tileSign k k' = 1} : Set (Fin 4 → ℤ)).ncard : ℝ) =
    G.tilesPerSide ^ 4 / 2 ∧
  (({k' | k' ∈ G.boxTileIndices ∧ tileSign k k' = -1} : Set (Fin 4 → ℤ)).ncard : ℝ) =
    G.tilesPerSide ^ 4 / 2
end Setup.Grid
def GridGroupAndBoxTiles : Prop :=
  ∀ (D : Setup) (G : D.Grid) (j : ℤ), G.edge = (D.L : ℝ) ^ j →
    G.ElementsPermuteTiles ∧
    G.OrientationIsHom ∧
    G.TileReflectionsCompose ∧
    G.ReflectedCopyRules ∧
    (2 * G.edge ≤ D.side →
      G.TilesPerSideEven j ∧
      G.PeriodShiftsInGroup ∧
      G.TilesCongruentToBoxTile ∧
      ∀ k : Fin 4 → ℤ, G.BoxTilesSignBalanced k)
end YangMills.Construction.MultipleReflections
end
