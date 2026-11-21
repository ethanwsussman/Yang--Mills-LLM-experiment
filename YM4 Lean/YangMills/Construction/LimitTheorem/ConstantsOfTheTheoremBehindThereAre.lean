import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.LimitTheorem
structure ExistentialConstants where
  perBall : ℕ → ℝ → ℝ → ℝ
  A : ℝ → ℝ → ℝ
  B : ℝ → ℝ
  κStar : ℝ
  kE : ℕ
  cE : ℝ
  CE : ℝ
  κ : ℝ
  clusterConst : SeparatedTuples.SepTuple → SeparatedTuples.SepTuple → ℝ
  clusterRadius : SeparatedTuples.SepTuple → SeparatedTuples.SepTuple → ℝ
structure LawConstants where
  d₀ : ℝ
  ηBar : ℝ → ℝ
structure ExistentialConstants.SideConditions (K : ExistentialConstants) : Prop where
  κStar_nonneg : 0 ≤ K.κStar
  perBall_antitoneOn : ∀ n : ℕ, 2 ≤ n → ∀ R : ℝ, 0 < R → AntitoneOn (fun d => K.perBall n d R) (Ioi 0)
  perBall_pos : ∀ n : ℕ, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 < K.perBall n d R
  A_pos : ∀ d R : ℝ, 0 < d → 0 < R → 0 < K.A d R
  B_pos : ∀ R : ℝ, 0 < R → 0 < K.B R
  kE_pos : 0 < K.kE
  cE_pos : 0 < K.cE
  CE_pos : 0 < K.CE
  κ_pos : 0 < K.κ
  clusterConst_pos : ∀ X Y : SeparatedTuples.SepTuple, 0 < K.clusterConst X Y
  clusterRadius_pos : ∀ X Y : SeparatedTuples.SepTuple, 0 < K.clusterRadius X Y
structure LawConstants.SideConditions (E : LawConstants) : Prop where
  d₀_mem : E.d₀ ∈ Ioo (0 : ℝ) 1
  ηBar_monotoneOn : MonotoneOn E.ηBar (Ioc 0 E.d₀)
  ηBar_mem : ∀ d ∈ Ioc 0 E.d₀, E.ηBar d ∈ Icc (0 : ℝ) (1 / 3)
  ηBar_tendsto : Tendsto E.ηBar (𝓝[>] 0) (𝓝 0)
def ExistentialConstants.toConditionConstants (K : ExistentialConstants) (E : LawConstants) :
    ConditionConstants where
  perBallConst := K.perBall
  A := K.A
  B := K.B
  κStar := K.κStar
  kE := K.kE
  cE := K.cE
  CE := K.CE
  κ := K.κ
  clusterCoeff := 0
  radiusCoeff := 0
  secondMoment := fun _ _ _ => 0
  d₀ := E.d₀
  ηBar := E.ηBar
end YangMills.Construction.LimitTheorem
end
