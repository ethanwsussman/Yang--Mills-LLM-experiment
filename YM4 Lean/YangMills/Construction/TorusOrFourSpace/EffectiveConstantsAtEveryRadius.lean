import YangMills.Construction.TorusOrFourSpace.BoundFunctionsAndEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable {D : Params} {θ : RadiusRatio}
abbrev effConstAt (P : TorusPartitionChoice D θ) (E : Kind)
    (C : BoundFamily) (n : ℕ) (d R : ℝ) : ℝ :=
  effConst P E C n d R
theorem side_pos (D : Params) : 0 < D.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
theorem ballRadius_mem_allowedRadii (D : Params) (θ : RadiusRatio) (E : Kind) :
    ballRadius D θ E ∈ allowedRadii D E := by
  cases E with
  | euclidean => exact Set.mem_Ioi.2 one_pos
  | torus =>
    have hside := side_pos D
    obtain ⟨hlo, hhi⟩ := θ.val_mem
    refine ⟨mul_pos hlo hside, ?_⟩
    change θ.val * D.side < D.side / 4
    nlinarith
theorem bump_support_subset_ball (P : TorusPartitionChoice D θ) (a : P.Idx) :
    ∃ x : Pt D torus, supportQ D torus (P.bump a) ⊆
        torusBall D x (ballRadius D θ torus) ∧
      ∃ S, IsClosedBallWithRadius D torus S (ballRadius D θ torus) ∧
        supportQ D torus (P.bump a) ⊆ S := by
  obtain ⟨j, hj⟩ := P.subordinate.support_subset a
  refine ⟨P.center j, hj, closedBallAbout D torus (P.center j) (ballRadius D θ torus),
    ⟨(ballRadius_mem_allowedRadii D θ torus).1, P.center j, rfl⟩, ?_⟩
  exact fun y hy => show quotDist D torus y (P.center j) ≤ _ from le_of_lt (hj hy)
theorem effConstAt_of_mem (P : TorusPartitionChoice D θ) (E : Kind)
    (C : BoundFamily) (n : ℕ) (d : ℝ) {R : ℝ} (hR : R ∈ allowedRadii D E) :
    effConstAt P E C n d R = C.val n d R :=
  if_pos hR
theorem effConstAt_of_not_mem (P : TorusPartitionChoice D θ) (E : Kind)
    (C : BoundFamily) (n : ℕ) (d : ℝ) {R : ℝ} (hR : R ∉ allowedRadii D E) :
    effConstAt P E C n d R =
      thetaNumber P E ^ n * C.val n d (ballRadius D θ E) :=
  if_neg hR
end YangMills.Construction.PeriodicSpace.Kind
