import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheEnergyAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.TheHessianHasKernels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative
variable {F : BlockFrame}
private theorem interpolatedCoords_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρ m V ζ = coordsAboveFrame true a ρ 0 V ζ := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
private theorem threshold_pos : EventuallyInParameters fun T => 0 < T.σ := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun r _ =>
    ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y _ => hσ⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem hessianDecay_of_energyKernelBounds (h₁ : EnergyKernelBounds)
    (h₂ : JointMixedDerivEqDerivAlong) (h₃ : DerivAlongRulesHold) :
    HessianDecay := by
  obtain ⟨D, hD, hK⟩ := h₁
  refine ⟨fun T k => D T 2 k, fun T k => hD T 2 k,
    EventuallyInParameters.mono (EventuallyInParameters.and hK threshold_pos) ?_⟩
  rintro T ⟨hE, hσ⟩ t F V i j k c X hF hV hX
  classical
  let G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := fun ζ V' =>
    chartedEnergy T.a (interpolatedCoords 0 T.a T.chainParams.ρA (frameRadius T.coupling) V' ζ) V'
  have hG : ∀ ζ V', G ζ V' = chartedEnergyAtMinimizer T.a T.ρA V' ζ := by
    intro ζ V'
    show chartedEnergy T.a _ V' = chartedEnergy T.a _ V'
    rw [interpolatedCoords_zero]
    rfl
  have hρ : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := by
    intro b
    have : 0 < T.ballRadius := by
      unfold StepParameters.ballRadius
      positivity
    simpa using this.le
  have hmove := hE T.coupling t F V 0 0 le_rfl hF hV le_rfl zero_le_one hρ
  have hR : ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval G V c X) (0, 0) :=
    (h₂ F V G 0 k c X).1 ⟨i.1⟩ fun l b w hl hw => (hmove l k b w c X hl hw hX).1
  let eI : StepVariable (finiteCells F) := bondVariation i.1 (EuclideanSpace.single i.2 1)
  let eJ : StepVariable (finiteCells F) := bondVariation j.1 (EuclideanSpace.single j.2 1)
  let hatI : StepVariable (finiteCells F) × (Fin k → ℝ) := (eI, 0)
  let hatJ : StepVariable (finiteCells F) × (Fin k → ℝ) := (eJ, 0)
  let R := rotatedEval G V c X
  let Q : StepVariable (finiteCells F) × (Fin k → ℝ) → ℝ := derivAlong R [hatJ, hatI]
  have hrules := h₃.1 (StepVariable (finiteCells F) × (Fin k → ℝ)) ℝ
  have hrulesQ := h₃.1 (Fin k → ℝ) ℝ
  have hev : ∀ᶠ σ' in 𝓝 (0 : Fin k → ℝ),
      chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) 0 i j = Q (0, σ') := by
    have hc : ContinuousAt (fun σ' : Fin k → ℝ => ((0 : StepVariable (finiteCells F)), σ')) 0 := by
      fun_prop
    have h2 := (hR 2).eventually (by simp)
    filter_upwards [hc.eventually h2] with σ' hσ'
    have h := h₃.2 (StepVariable (finiteCells F) × (Fin k → ℝ)) (StepVariable (finiteCells F)) ℝ R
      (ContinuousLinearMap.inl ℝ _ _) (0, σ') 0 [eJ, eI] (by simpa using hσ')
    have e1 : (fun t' : StepVariable (finiteCells F) =>
        R ((0, σ') + ContinuousLinearMap.inl ℝ _ (Fin k → ℝ) t')) =
        chartedEnergyAtMinimizer T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) := by
      funext t'
      simp [R, rotatedEval, hG]
    rw [e1] at h
    have e2 : (([eJ, eI] : List (StepVariable (finiteCells F))).map
        (ContinuousLinearMap.inl ℝ _ (Fin k → ℝ))) = [hatJ, hatI] := by
      simp [hatJ, hatI]
    rw [e2] at h
    have e0 : chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) 0 i j =
        derivAlong (chartedEnergyAtMinimizer T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V)) [eJ, eI] 0 := rfl
    rw [e0]
    simpa [Q] using h
  have hQ : ∀ m : ℕ, ContDiffAt ℝ (m : WithTop ℕ∞) Q (0, 0) := by
    intro m
    exact hrules.contDiffAt R (0, 0) m [hatJ, hatI] (by simpa using hR (m + 2))
  have hsm : ∀ m : ℕ, ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ' : Fin k → ℝ =>
      chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) 0 i j) 0 := by
    intro m
    have hP : ContDiffAt ℝ (m : WithTop ℕ∞) (fun σ' : Fin k → ℝ => ((0 : StepVariable (finiteCells F)), σ')) 0 :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.comp (0 : Fin k → ℝ) (hQ m) hP) hev
  refine ⟨hsm, ?_⟩
  let b : Fin 2 → ↥(chordBonds (finiteCells F)) := ![j.1, i.1]
  let u : Fin 2 → EuclideanSpace ℝ (Fin 3) := ![EuclideanSpace.single j.2 1, EuclideanSpace.single i.2 1]
  have hu : ∀ l, ‖u l‖ = 1 := by
    intro l
    fin_cases l <;> simp [u]
  have hbound := (hmove 2 k b u c X le_rfl hu hX).2
  have hval : bondDeriv (fun V' => chartedHessian T.a T.ρA V' 0 i j) V c X = jointMixedDeriv G 0 V b u c X := by
    rw [(h₂ F V G 0 k c X).2 2 b u (by simpa using hR (2 + k))]
    have hbasis := parameterBasis k
    have s1 : bondDeriv (fun V' => chartedHessian T.a T.ρA V' 0 i j) V c X =
        derivAlong (fun σ' => chartedHessian T.a T.ρA (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X σ') V) 0 i j)
          (parameterBasis k) 0 :=
      hrulesQ.iteratedFDeriv_eq _ 0 k _ (hsm k)
    rw [s1, (hrulesQ.congr _ _ 0 _ hev).self_of_nhds]
    have s2 := h₃.2 (StepVariable (finiteCells F) × (Fin k → ℝ)) (Fin k → ℝ) ℝ Q
      (ContinuousLinearMap.inr ℝ _ _) 0 0 (parameterBasis k) (by simpa using hQ _)
    have e3 : (fun t' : Fin k → ℝ => Q (0 + ContinuousLinearMap.inr ℝ (StepVariable (finiteCells F)) _ t')) =
        fun σ' => Q (0, σ') := by
      funext t'
      simp
    rw [e3] at s2
    rw [s2]
    have e4 : (0 : StepVariable (finiteCells F) × (Fin k → ℝ)) +
        ContinuousLinearMap.inr ℝ (StepVariable (finiteCells F)) (Fin k → ℝ) 0 = (0, 0) := by
      simp
    rw [e4]
    show derivAlong (derivAlong R [hatJ, hatI]) _ _ = _
    rw [← hrules.append]
    have e5 : pointDirections (k := k) b u = [hatJ, hatI] := by
      simp [pointDirections, b, u, variableDirection, hatJ, hatI, eJ, eI, bondVariation, List.ofFn_succ]
    have e6 : parameterDirections ↥(chordBonds (finiteCells F)) (EuclideanSpace ℝ (Fin 3)) (parameterBasis k) =
        (parameterBasis k).map (ContinuousLinearMap.inr ℝ (StepVariable (finiteCells F)) (Fin k → ℝ)) := by
      simp [parameterDirections]
    rw [e5, e6]
    exact hrules.perm R _ _ _ List.perm_append_comm (hR _)
  rw [hval]
  refine hbound.trans (le_of_eq ?_)
  have e7 : chordBondCells b = {enclosingCell i.1.1.1, enclosingCell j.1.1.1} := by
    ext z
    simp [chordBondCells, b, Fin.exists_fin_two, eq_comm, or_comm]
  rw [e7]
end YangMills.Construction.ReferenceDensity
end
