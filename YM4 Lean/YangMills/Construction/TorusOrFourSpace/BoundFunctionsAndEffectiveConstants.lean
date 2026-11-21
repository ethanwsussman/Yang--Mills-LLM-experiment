import YangMills.Construction.TorusOrFourSpace.RadiusPartitionOfUnityAndTheNumberTheta
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
structure BoundFamily where
  val : ℕ → ℝ → ℝ → ℝ
  nonneg : ∀ n, 2 ≤ n → ∀ d R, 0 < d → 0 < R → 0 ≤ val n d R
  antitoneOn : ∀ n, 2 ≤ n → ∀ R, 0 < R → AntitoneOn (fun d => val n d R) (Set.Ioi 0)
namespace Kind
variable {P : Params} {θ : RadiusRatio}
open Classical in
def effConst (Φ : TorusPartitionChoice P θ) (Y : Kind) (C : BoundFamily) (n : ℕ)
    (d R : ℝ) : ℝ :=
  if R ∈ allowedRadii P Y then C.val n d R
  else thetaNumber Φ Y ^ n * C.val n d (ballRadius P θ Y)
end Kind
end YangMills.Construction.PeriodicSpace
