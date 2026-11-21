import YangMills.Construction.Dirichlet.CubeCoverAndWalks
import YangMills.Construction.WeightedGreen.ExpansionConstants
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Dirichlet.CoverCount
open Torus Dirichlet
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def LiesAtLevel (n : ℕ) (x : PeriodicTorus d S) : Prop :=
  (n ≤ 𝒮.t ∧ x ∈ shell 𝒮.Ω n) ∨ (n = 0 ∧ x ∉ 𝒮.Ω 0)
structure CoverCubeBounds : Prop where
  finite_cubes : 𝒮.coverCubes.Finite
  exists_level : ∀ x : PeriodicTorus d S, ∃ n, LiesAtLevel 𝒮 n x
  level_adjacent : ∀ (n m : ℕ) (x : PeriodicTorus d S) (Q : CentredCube d S),
    Q ∈ 𝒮.coverCubesAt m →
    x ∈ tsupport (𝒮.cubeBump Q) → LiesAtLevel 𝒮 n x →
    (m : ℤ) = (n : ℤ) - 1 ∨ m = n ∨ m = n + 1
  encard_near_centres_le : ∀ (m : ℕ) (x : PeriodicTorus d S),
    {Q | Q ∈ 𝒮.coverCubesAt m ∧ supNorm (x - Q.centre) < 𝒮.blockWidth m}.encard ≤
      (2 ^ d : ℕ∞)
  encard_supports_le : ∀ x : PeriodicTorus d S,
    {Q | Q ∈ 𝒮.coverCubes ∧ x ∈ tsupport (𝒮.cubeBump Q)}.encard ≤
      (WeightedGreen.cubeOverlap d : ℕ∞)
def coverCubeBounds_statement : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S),
      3 * L * (L + 12) ≤ 𝒮.M → L * (L + 9) ≤ 𝒮.R₁ * 𝒮.M →
      CoverCubeBounds 𝒮
end Dirichlet.CoverCount
end YangMills.Construction
