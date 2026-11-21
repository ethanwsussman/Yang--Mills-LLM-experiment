import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChainProof
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikelyProof
import YangMills.Construction.ResponseInTheExpansion.TheStepsOfTheLocalChainFormStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepReturn StepFloors WeightedResponses BlockAverages
namespace LocalChainWellPosed
private theorem isWellPosed_of_floors {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hyMin : T.floorMin ≤ y)
    (hyOne : 1 ≤ y) {S : StepSetup} (hon : S.OnParameters T y) (hmoved : |S.nextCoupling - S.coupling| ≤ 2 * T.B)
    (hsym : S.IsSymmetricWeight) (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 S.coupling) :
    S.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
variable {ℓ : TorusLumps.StepParameters}
private theorem flow_hasExpansion (hret : ExpansionReturnsAt ℓ) {β : ℝ}
    (hzero : HasExpansion ℓ 0 β (wilsonWeight β)) {K : ℕ}
    (hflow : ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    ∀ s ≤ K, HasExpansion ℓ s (couplingFlow ℓ β s).1 (couplingFlow ℓ β s).2 ∧
      |(couplingFlow ℓ β (s + 1)).1 - (couplingFlow ℓ β s).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p25177 <;> assumption
private theorem stage_depth {T : StageTower ℓ} (h0 : T.base.depth = 0) : ∀ s, (T.stage s).depth = s := by
  intro s
  induction s with
  | zero => exact h0
  | succ s ih =>
    show (T.stage s).depth + 1 = s + 1
    rw [ih]
private theorem stage_functional {T : StageTower ℓ} {β : ℝ} (h0 : T.base.functional = wilsonWeight β) {K : ℕ}
    (hx : ∀ j ≤ K, (T.stage j).coupling = (couplingFlow ℓ β j).1) :
    ∀ s ≤ K + 1, (T.stage s).functional = (couplingFlow ℓ β s).2 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.LocalEventLikely.stage_functional_eq <;> assumption
end LocalChainWellPosed
open LocalChainWellPosed in
theorem localChainStepsWellPosed (hFl : EventuallyFloorConditions) : localChainStepsWellPosedStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ T _ _ hT _ _ _ _ => ?_⟩
  have hC : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hC one_pos
  refine ⟨max (max T.floorMin yF) 1, fun y hy hret hW Tw β k N nn x₀ hloc s hs => ?_⟩
  have h₁ : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h₂ : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h₃ : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hst := hloc.onFamily
  have hβ : y ≤ β := hloc.coupling_ge 0 (Nat.zero_le _)
  have hexp := flow_hasExpansion hret (hW β hβ) hloc.coupling_ge
  have hdepth := stage_depth hst.startsAtWilson.depth_eq s
  have hx : ∀ j ≤ k + 2 * localChainDepth (T.stepParameters y) β k,
      (Tw.stage j).coupling = (couplingFlow (T.stepParameters y) β j).1 :=
    fun j hj => hst.coupling_eq j (by
      have : j ≤ k + 2 * chainDepth (couplingFlow (T.stepParameters y) β k).1 := hj
      omega)
  have hfun := stage_functional hst.startsAtWilson.functional_eq hx s (by omega)
  have hs' : s ≤ k + 2 * chainDepth (couplingFlow (T.stepParameters y) β k).1 := hs
  have hnext : (Tw.stage s).nextCoupling = (couplingFlow (T.stepParameters y) β (s + 1)).1 :=
    hst.coupling_eq (s + 1) (by omega)
  have hmove : |(Tw.stage s).nextCoupling - (Tw.stage s).coupling| ≤ 2 * T.B := by
    rw [hnext, hx s hs]
    exact (hexp s hs').2
  have hon := hst.onFamily s hs'
  have hsym : (Tw.stage s).toStepSetup.IsSymmetricWeight := by
    intro m _ hm
    show Measurable ((Tw.stage s).functional m) ∧ _
    rw [show (Tw.stage s).toStepSetup.functional = (Tw.stage s).functional from rfl, hfun]
    exact (hexp s hs').1.1 m hm
  refine ⟨hdepth, hx s hs, hmove, isWellPosed_of_floors hT h₁ h₃ hon hmove hsym (hyF _ (h₂.trans hon.le_coupling))⟩
end YangMills.Construction.ResponseInTheExpansion
end
