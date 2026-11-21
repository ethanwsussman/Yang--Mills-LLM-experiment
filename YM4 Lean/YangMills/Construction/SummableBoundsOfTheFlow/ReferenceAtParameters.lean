import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def StepParameters.ρA (T : StepParameters) : ℝ := T.chainParams.ρA
def StepParameters.lam (T : StepParameters) : ℝ := T.chainParams.lam
def StepParameters.referenceDensity (T : StepParameters) (t : ℕ) : TorusLumps.LocalDensity :=
  ReferenceDensity.referenceFamily T.a T.ρA T.lam T.L t
def StepParameters.localReference (T : StepParameters) (t : ℕ) : LocalFamily :=
  localFamilyOfDensity (T.referenceDensity t)
def StepParameters.stepDensity (T : StepParameters) (t : ℕ) : TorusLumps.LocalDensity :=
  ReferenceDensity.stepDensityFamily T.a T.ρA T.lam T.L t
def StepParameters.oneLoopCoeff (T : StepParameters) (t : ℕ) : ℝ :=
  ReferenceDensity.oneLoopCoefficient T.a T.ρA T.lam T.L t
def StepParameters.secondCoeff (T : StepParameters) (t : ℕ) : ℝ :=
  ScaledVariables.secondStepCoefficient T.a T.ρA T.lam T.L t
def StepParameters.secondOrderDensity (T : StepParameters) (t : ℕ) : TorusLumps.LocalDensity :=
  densityOfTopFamily T.L t (ScaledVariables.secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t))
def StepParameters.minimizerDensity (T : StepParameters) (t : ℕ) (x : ℝ) : TorusLumps.LocalDensity :=
  ScaledVariables.minimizerDensities T.a T.ρA T.ballRadius T.lam x T.p T.L t (T.localReference t)
structure StepParameters.Compatible (T : StepParameters) (ℓ : TorusLumps.StepParameters) : Prop where
  coupling_eq : ℓ.coupling = T.a
  side_eq : ℓ.side = T.L
  threshold_eq : ℓ.threshold = T.σ
  rt_eq : ℓ.rt = T.κ
  n₁_eq : ℓ.n₁ = (T.L : ℝ) ^ (1 / 640 : ℝ)
  n₀_eq : ℓ.n₀ = T.n₀
  E_eq : ℓ.E = T.E
  E₃_eq : ℓ.E₃ = T.energyRatio
def StepParameters.AdmitsReference (T : StepParameters) : Prop :=
  4 * TorusLumps.expansionConstant T.Cs (TorusLumps.maxOfFirstFour T.chainParams.N) T.κ
      ((T.L : ℝ) ^ (1 / 640 : ℝ)) ≤ T.E ∧
    ∃ ℓ : TorusLumps.StepParameters, T.Compatible ℓ ∧ ℓ.Admissible
def StepParameters.IsBoundedFamilyOrderSix (T : StepParameters) (e : ℕ → ℝ) (t : ℕ)
    (f : LocalFamily) : Prop :=
  FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f ∧
    Interpolation.HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate 6 e f
def EventuallyOrdered (P : StepParameters → Prop) : Prop :=
  EventuallyInParameters fun T => T.IsOrdered → 1 ≤ T.n₀ → P T
theorem EventuallyInParameters.mono {c₁ c₂ : StepParameters → Prop}
    (h₁ : EventuallyInParameters c₁) (h : ∀ T, c₁ T → c₂ T) :
    EventuallyInParameters c₂ := by
  intro a ha
  obtain ⟨L₀, g⟩ := h₁ a ha
  refine ⟨L₀, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨Ct₀, g⟩ := g L hL hL₀ c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, g⟩ := g Ct hCt
  refine ⟨κ₀, hκ₀, fun κ h0 hκ => ?_⟩
  obtain ⟨η₀, hη₀, g⟩ := g κ h0 hκ
  refine ⟨η₀, hη₀, fun η₃ h0 h1 hη => ?_⟩
  obtain ⟨N₀, g⟩ := g η₃ h0 h1 hη
  refine ⟨N₀, fun k hN => ?_⟩
  obtain ⟨σ₀, hσ₀, g⟩ := g k hN
  refine ⟨σ₀, hσ₀, fun σ h0 hσ p hp => ?_⟩
  obtain ⟨C₀, g⟩ := g σ h0 hσ p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, g⟩ := g Cs hCs E hE
  refine ⟨m₀, fun n₀ hn => ?_⟩
  obtain ⟨C₁, g⟩ := g n₀ hn
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, g⟩ := g CE hCE
  exact ⟨y₀, fun y₁ hy => h _ (g y₁ hy)⟩
theorem EventuallyInParameters.and {c₁ c₂ : StepParameters → Prop}
    (h₁ : EventuallyInParameters c₁) (h₂ : EventuallyInParameters c₂) :
    EventuallyInParameters fun T => c₁ T ∧ c₂ T := by
  intro a ha
  obtain ⟨L₁, g₁⟩ := h₁ a ha
  obtain ⟨L₂, g₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun L hL hLe c hc => ?_⟩
  obtain ⟨A₁, g₁⟩ := g₁ L hL (le_trans (le_max_left _ _) hLe) c hc
  obtain ⟨A₂, g₂⟩ := g₂ L hL (le_trans (le_max_right _ _) hLe) c hc
  refine ⟨max A₁ A₂, fun Ct hCt => ?_⟩
  obtain ⟨k₁, p₁, g₁⟩ := g₁ Ct (le_trans (le_max_left _ _) hCt)
  obtain ⟨k₂, p₂, g₂⟩ := g₂ Ct (le_trans (le_max_right _ _) hCt)
  refine ⟨min k₁ k₂, lt_min p₁ p₂, fun κ h0 hκ => ?_⟩
  obtain ⟨e₁, q₁, g₁⟩ := g₁ κ h0 (le_trans hκ (min_le_left _ _))
  obtain ⟨e₂, q₂, g₂⟩ := g₂ κ h0 (le_trans hκ (min_le_right _ _))
  refine ⟨min e₁ e₂, lt_min q₁ q₂, fun η₃ h0 h1 hη => ?_⟩
  obtain ⟨N₁, g₁⟩ := g₁ η₃ h0 h1 (le_trans hη (min_le_left _ _))
  obtain ⟨N₂, g₂⟩ := g₂ η₃ h0 h1 (le_trans hη (min_le_right _ _))
  refine ⟨max N₁ N₂, fun k hN => ?_⟩
  obtain ⟨s₁, r₁, g₁⟩ := g₁ k (le_trans (le_max_left _ _) hN)
  obtain ⟨s₂, r₂, g₂⟩ := g₂ k (le_trans (le_max_right _ _) hN)
  refine ⟨min s₁ s₂, lt_min r₁ r₂, fun σ h0 hσ p hp => ?_⟩
  obtain ⟨B₁, g₁⟩ := g₁ σ h0 (le_trans hσ (min_le_left _ _)) p hp
  obtain ⟨B₂, g₂⟩ := g₂ σ h0 (le_trans hσ (min_le_right _ _)) p hp
  refine ⟨max B₁ B₂, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₁, g₁⟩ := g₁ Cs (le_trans (le_max_left _ _) hCs) E hE
  obtain ⟨m₂, g₂⟩ := g₂ Cs (le_trans (le_max_right _ _) hCs) E hE
  refine ⟨max m₁ m₂, fun n₀ hn => ?_⟩
  obtain ⟨D₁, g₁⟩ := g₁ n₀ (le_trans (le_max_left _ _) hn)
  obtain ⟨D₂, g₂⟩ := g₂ n₀ (le_trans (le_max_right _ _) hn)
  refine ⟨max D₁ D₂, fun CE hCE => ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ CE (le_trans (le_max_left _ _) hCE)
  obtain ⟨y₂, g₂⟩ := g₂ CE (le_trans (le_max_right _ _) hCE)
  exact ⟨max y₁ y₂, fun y hy => ⟨g₁ y (le_trans (le_max_left _ _) hy), g₂ y (le_trans (le_max_right _ _) hy)⟩⟩
theorem EventuallyOrdered.mono {c₁ c₂ : StepParameters → Prop} (h₁ : EventuallyOrdered c₁)
    (h : ∀ T, T.IsOrdered → 1 ≤ T.n₀ → c₁ T → c₂ T) : EventuallyOrdered c₂ :=
  EventuallyInParameters.mono h₁ fun T g hT hn => h T hT hn (g hT hn)
theorem EventuallyOrdered.and {c₁ c₂ : StepParameters → Prop} (h₁ : EventuallyOrdered c₁)
    (h₂ : EventuallyOrdered c₂) : EventuallyOrdered fun T => c₁ T ∧ c₂ T :=
  EventuallyInParameters.mono (EventuallyInParameters.and h₁ h₂) fun _ g hT hn => ⟨g.1 hT hn, g.2 hT hn⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end
