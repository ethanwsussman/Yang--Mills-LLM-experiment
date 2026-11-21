import YangMills.Construction.TorusOrFourSpace.FiniteCoversByBallsAndPartitionsOfUnity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
structure RadiusRatio where
  val : ℝ
  val_mem : val ∈ Set.Ioo (0 : ℝ) (1 / 4)
namespace Kind
variable (P : Params) (ρ : RadiusRatio)
def ballRadius : Kind → ℝ
  | euclidean => 1
  | torus => ρ.val * P.side
structure TorusPartitionChoice where
  numBalls : ℕ
  center : Fin numBalls → Pt P torus
  cover : BallsCoverTorus P center (ballRadius P ρ torus)
  Idx : Type
  [fintypeIdx : Fintype Idx]
  bump : Idx → Pt P torus → ℝ
  subordinate : IsSubordinatePartitionOfUnity P center (ballRadius P ρ torus) bump
attribute [instance] TorusPartitionChoice.fintypeIdx
variable {P ρ}
def thetaNumber (χ : TorusPartitionChoice P ρ) : Kind → ℝ
  | euclidean => 1
  | torus => ∑ a, (1 + 40 * P.M * lipConstQ P torus (χ.bump a))
end Kind
end YangMills.Construction.PeriodicSpace
