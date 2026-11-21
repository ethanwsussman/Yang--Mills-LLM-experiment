import YangMills.Construction.Geometry.ToriGeneralSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
inductive UnitSpacingLattice : Type where
  | intLattice (L : ℕ) (blockingHyp : Blocking.DimFourOddBlockingFactorGeThirteen 4 L)
      (origin : Fin 4 → ℤ) : UnitSpacingLattice
  | torusLevel (D : GeneralTorus.ScaleData) (last_spacing_eq_one : D.levelSpacing D.lastLevel = 1)
      (side_evenMultiple : GeneralTorus.IsEvenMultipleOf D.torusSide (D.L : ℝ)) : UnitSpacingLattice
namespace UnitSpacingLattice
def blockFactor : UnitSpacingLattice → ℕ
  | .intLattice L .. => L
  | .torusLevel D .. => D.L
def Point : UnitSpacingLattice → Type
  | .intLattice .. => Fin 4 → ℤ
  | .torusLevel D .. => D.SiteAt D.lastLevel
instance (Λ : UnitSpacingLattice) : AddCommGroup Λ.Point :=
  match Λ with
  | .intLattice .. => inferInstanceAs (AddCommGroup (Fin 4 → ℤ))
  | .torusLevel D .. => inferInstanceAs (AddCommGroup (D.SiteAt D.lastLevel))
def basisVec : (Λ : UnitSpacingLattice) → Fin 4 → Λ.Point
  | .intLattice .., μ => (Pi.single μ 1 : Fin 4 → ℤ)
  | .torusLevel D .., μ => GeneralTorus.unitStep D.torusSide (D.levelSpacing D.lastLevel) μ
def coordDist : (Λ : UnitSpacingLattice) → Λ.Point → Λ.Point → Fin 4 → ℝ
  | .intLattice .., x, y, ν =>
      |(((show Fin 4 → ℤ from x) ν - (show Fin 4 → ℤ from y) ν : ℤ) : ℝ)|
  | .torusLevel D .., x, y, ν =>
      ‖((show D.SiteAt D.lastLevel from x) : D.Space) ν -
        ((show D.SiteAt D.lastLevel from y) : D.Space) ν‖
def CoordEq : (Λ : UnitSpacingLattice) → Λ.Point → Λ.Point → Fin 4 → Prop
  | .intLattice .., x, y, ν => (show Fin 4 → ℤ from x) ν = (show Fin 4 → ℤ from y) ν
  | .torusLevel D .., x, y, ν =>
      ((show D.SiteAt D.lastLevel from x) : D.Space) ν =
        ((show D.SiteAt D.lastLevel from y) : D.Space) ν
def blockCenters : (Λ : UnitSpacingLattice) → Set Λ.Point
  | .intLattice L _ y₀ => {y : Fin 4 → ℤ | ∃ k : Fin 4 → ℤ, y = y₀ + (L : ℤ) • k}
  | .torusLevel D .. =>
      {y : D.SiteAt D.lastLevel | (y : D.Space) ∈ D.levelSublattice (D.lastLevel + 1)}
variable (Λ : UnitSpacingLattice)
def cube (y : Λ.Point) : Set Λ.Point :=
  {x | ∀ ν, Λ.coordDist x y ν ≤ ((Λ.blockFactor : ℝ) - 1) / 2}
@[ext]
structure Edge where
  src : Λ.Point
  axis : Fin 4
@[ext]
structure CenterEdge where
  src : Λ.Point
  src_mem : src ∈ Λ.blockCenters
  axis : Fin 4
@[ext]
structure Face where
  origin : Point Λ
  ax₁ : Fin 4
  ax₂ : Fin 4
  ax₁_lt_ax₂ : ax₁ < ax₂
variable {Λ}
def Edge.tgt (b : Λ.Edge) : Λ.Point := b.src + Λ.basisVec b.axis
def CenterEdge.tgt (c : Λ.CenterEdge) : Λ.Point :=
  c.src + Λ.blockFactor • Λ.basisVec c.axis
def Face.vertices (p : Λ.Face) : Set Λ.Point :=
  {p.origin, p.origin + Λ.basisVec p.ax₁, p.origin + Λ.basisVec p.ax₁ + Λ.basisVec p.ax₂,
    p.origin + Λ.basisVec p.ax₂}
def blockAverage (B : Λ.Edge → ℝ) (c : Λ.CenterEdge) : ℝ :=
  (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) *
    ∑ᶠ x ∈ Λ.cube c.src, ∑ i ∈ Finset.range Λ.blockFactor,
      B ⟨x + i • Λ.basisVec c.axis, c.axis⟩
def Edge.InCube (b : Λ.Edge) (y : Λ.Point) : Prop :=
  b.src ∈ Λ.cube y ∧ b.tgt ∈ Λ.cube y
variable (Λ)
def axialTree (y : Λ.Point) : Set Λ.Edge :=
  {b | b.InCube y ∧ ∀ ν, ν < b.axis → Λ.CoordEq b.src y ν}
variable {Λ}
def edgeCorridor (c : Λ.CenterEdge) : Set Λ.Edge :=
  {b | b.src ∈ Λ.cube c.src ∧ b.tgt ∈ Λ.cube c.tgt}
end UnitSpacingLattice
end YangMills.Construction
