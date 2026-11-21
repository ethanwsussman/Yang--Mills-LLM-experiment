import YangMills.Construction.ClusterExpansionOfAStep.StateOverAColdField
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.ResponseIntegralIsCarried
import YangMills.Construction.ResponseInTheExpansion.ResponseIsCarried
import YangMills.Construction.ResponseInTheExpansion.ResponseIsTheIntegralOfItsCases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings RenormalizationStepParameters StepGas TorusLumps TorusFields StepFloors BlockAverages
  ColdStepAtMirrorFrames
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hsym : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
theorem stepResponseIsometryInvariant_holds (hC : responseEqCaseIntegralStatement)
    (hI : blockResponseIntegralIsometryInvariantStatement) (hS : coldFieldStateStatement)
    (hA : KernelImageIsDensity) (hFl : EventuallyFloorConditions) :
    StepResponseIsometryInvariant := by
  unfold StepResponseIsometryInvariant HoldsAtEveryStep
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ?_⟩
  have hCpos : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hCpos one_pos
  refine ⟨max (max T.floorMin yF) 1, fun y hy R A _ hAt hL hsym => ?_⟩
  have h1 : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h2 : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h3 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hon := hAt.onFamily
  have hR := isWellPosed_of_onParameters hT h1 h3 hon hAt.abs_sub_le hsym (hyF R.coupling (h2.trans hon.le_coupling))
  have hresp := hAt.admissible
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.params.side)
  obtain ⟨c1, c2, c3⟩ := hC R A hL hR hresp
  refine ⟨fun n _ hn y V Y hY => c1 n hn y V Y hY, fun n _ hn g y W W' hW => ?_, fun n _ hn g y W W' _ hW => ?_⟩
  · have hn₀ : R.params.n₀ ≤ n := (Nat.le_mul_of_pos_left _ (by omega)).trans hn.2
    rw [c2 n hn, c2 n hn]
    exact hI R A hR hresp n hn₀ g y W W' hW
  · have hexp : HasExpansion R.params R.depth R.coupling R.functional :=
      ⟨hR.functional_spec, R.density, hR.hasExpansions.1, R.labels, R.labelWeight, R.clusterFactor,
        R.siteDensity, hR.hasExpansions.2⟩
    have hker := hA R.params hR.admissible R.depth R.coupling R.functional hR.coupling_pos hR.range_ge_base
      hexp n hn
    have e : ∀ V : TorusField n,
        coarseStateWeight R ∅ V (emptyCoarseState R) = kernelImage R.params R.coupling R.functional n V :=
      fun V => (hS R hR n hn).1 V _
    show caseMean R ∅ W' (emptyCoarseState R) (caseResponse A W' (g.mapSite y) (constOneWeight _)) =
      caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y (constOneWeight _))
    unfold caseMean
    rw [c3 n hn, c3 n hn, e, e, hI R A hR hresp n hn g y W W' hW, hker.2.2.2.2 g W W' hW]
end YangMills.Construction.ResponseInTheExpansion
end
