import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.TotalDensitiesGiveASystem.EveryComponentIsALimitOfStates
import YangMills.Construction.TotalDensitiesGiveASystem.ThePhasesApproachEveryComponent
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities.ComponentLimits
open InfiniteLattice (IsRegularConditionalByIntegrals)
private def trivialDemands : AssignmentConstraints where
  property _ := True
  sideFloor _ := 0
  derivBoundFloor _ := 0
  rateCeiling _ := 1
  thresholdCeiling _ _ := 1
  n₀Floor _ _ _ := 0
  CsFloor _ _ _ := 0
  NFloor _ := 0
private theorem trivialDemands_satisfiable : trivialDemands.Satisfiable :=
  ⟨fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
      ⟨0, fun _ _ => trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩, fun _ => one_pos, fun _ _ => one_pos⟩
private theorem tendsto_succPNat : Tendsto Nat.succPNat atTop atTop := by apply _root_.YangMills.SharedProofs.p14344 <;> assumption
theorem componentsAreLimitsOfStates_holds
    (hP : TotalDensitiesGiveASystem.phasesApproachComponentsStatement)
    (hT : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs) : ComponentsAreLimitsOfStates := by
  refine ⟨trivialDemands, trivialDemands_satisfiable, fun T hDr _ =>
    ⟨0, fun y _ => ⟨0, fun g hg _ Z hZ Q S hQ A hA ξ n hn X => ?_⟩⟩⟩
  have hL : Conventions.IsAdmissibleBlockingFactor (T.stepParameters y).side :=
    ⟨hDr.L_odd, le_trans (by norm_num) hDr.L_ge⟩
  have hβ : ∀ j, 0 < Q.coupling j := fun j => by
    have h1 : SequencePassage.passageThreshold (2 * T.B) g ≤ Q.coupling j := (Q.pair j).2.1
    have h2 : SequencePassage.passageThreshold (2 * T.B) g = g ^ (-2 : ℤ) + 2 * T.B := rfl
    have h3 : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
    have h4 : (1 : ℝ) ≤ T.B := hDr.B_ge
    linarith
  have hE : ∀ j κ, IsRegularConditionalByIntegrals (Q.state j) κ →
      ∀ᵐ U ∂Q.state j, (κ U).1 ∈ Z (Q.cutoff j) (Q.coupling j) := fun j κ hκ => by
    have hper : Q.state j ∈
        InfiniteLattice.periodicGibbsSet (T.stepParameters y).side (Q.cutoff j) (Q.coupling j) :=
      (hT _ (Q.cutoff j) hL (Q.cutoff j).pos (Q.coupling j) (hβ j)).2 (Q.isLimit j)
    exact hZ.ergodicComponents_mem (Q.cutoff j) (Q.coupling j) (Q.pair j) hL (hβ j)
      ⟨Q.state j, hper⟩ (Q.isLimit j) κ hκ
  obtain ⟨ρ, hρ, hρp, hlim⟩ := hP (T.stepParameters y).side hL _ Q S hβ hQ A hA ξ n hn X
    (fun j => Z (Q.cutoff j) (Q.coupling j)) hE
  exact ⟨Nat.succPNat, fun l => ρ (Nat.succPNat l), tendsto_succPNat, fun l => hρ _, fun l => hρp _,
    hlim.comp tendsto_succPNat⟩
end YangMills.Construction.TotalDensities.ComponentLimits
end
