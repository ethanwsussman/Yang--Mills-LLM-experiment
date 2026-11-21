import YangMills.Construction.GrowingTori.MultilinearityOfTheConnectedFunctions
import YangMills.Construction.GrowingTori.TransportOfFunctionsAndTuplesThroughTheBall
import YangMills.Construction.InfiniteLattice.MultilinearityOfTheConnectedCurvatureFunctions
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BallTuples
namespace ConnectedMultilinearity
open TestFunctions (IsLipschitzFor euclidDistTorus)
open SourcesAndGluing (ballR4)
open TorusCumulants.Multilinearity (FunctionalRealLinear)
variable (D : PeriodicSpace.Params) (K : ℕ+) {β : ℝ}
abbrev cutoffStanding : Conventions.StandingParameters := ⟨D.L, D.isAdmissible, K, D.m⟩
theorem connectedOfReal_eq (hβ : 0 < β) {n : ℕ} (u : Fin n → D.Torus → ℝ) :
    connectedOfReal D K hβ u = SchwingerFunctions.connectedSchwinger D.L D.m K β u :=
  (couplingData D K hβ).connected_ofReal u
theorem realLipschitzLinearity
    (hM : TorusCumulants.Multilinearity.claim)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hβ : 0 < β) {n : ℕ} (hn : 2 ≤ n) : RealLipschitzLinearity D K hβ n := by
  have hlin : FunctionalRealLinear (cutoffStanding D K) β n :=
    (hM.2 (cutoffStanding D K) β n hβ (by omega)).2.2.1
  refine ⟨fun u hu => ?_, fun u l f' f'' c' c'' hu hf' hf'' => ?_, fun u hu hd => ?_⟩
  · rw [connectedOfReal_eq]
    exact (hlin u hu).1
  · simp only [connectedOfReal_eq]
    exact (hlin u hu).2 l f' f'' c' c'' hf' hf''
  · exact ⟨(hC ((couplingData D K hβ).withDir 0)).2.2.1.2 n u hn hd hu |>.1,
      connectedOfReal_eq D K hβ u⟩
theorem periodize_update {n : ℕ} (X : FnTuple n) (l : Fin n) (f : R4Fun) :
    periodize D (Function.update X l f) =
      Function.update (periodize D X) l (TestFunctions.periodize D.side f) := by
  funext i
  by_cases hi : i = l
  · subst hi
    simp [periodize_apply]
  · simp [periodize_apply, Function.update_of_ne hi]
theorem separatedTupleLinearity
    (hT : PeriodizationThroughBall.PeriodizationLemma) (hβ : 0 < β) {n : ℕ}
    (hn : 2 ≤ n) (hreal : RealLipschitzLinearity D K hβ n) :
    SeparatedTupleLinearity D K β n := by
  have hconn : ∀ Y : FnTuple n,
      connectedFn D K β Y = connectedOfReal D K hβ (periodize D Y) :=
    fun Y => (connectedOfReal_eq D K hβ _).symm
  have hlip : ∀ (ρ : ℝ) (Y : FnTuple n), IsPeriodizable D ρ Y →
      ∀ l, IsLipschitzFor euclidDistTorus (periodize D Y l) := fun ρ Y hY =>
    ((hT D ρ hY.1 hY.2.1).2.2.2.2 n (by omega) Y hY).1
  have hlinear : ∀ ρ : ℝ, 0 < ρ → ρ ≤ BallPeriodization.ballRadius D →
      ∀ (X : FnTuple n) (l : Fin n) (f' f'' : R4Fun) (c' c'' : ℝ),
        Function.update X l f' ∈ lipTuplesBall n ρ →
        Function.update X l f'' ∈ lipTuplesBall n ρ →
        Function.update X l (c' • f' + c'' • f'') ∈ lipTuplesBall n ρ →
        connectedFn D K β (Function.update X l (c' • f' + c'' • f'')) =
          (c' : ℂ) * connectedFn D K β (Function.update X l f') +
            (c'' : ℂ) * connectedFn D K β (Function.update X l f'') := by
    intro ρ h0 hle X l f' f'' c' c'' h₁ h₂ h₃
    have t₁ : IsPeriodizable D ρ (Function.update X l f') := ⟨h0, hle, h₁.1, h₁.2⟩
    have t₂ : IsPeriodizable D ρ (Function.update X l f'') := ⟨h0, hle, h₂.1, h₂.2⟩
    have b₁ : BallPeriodization.IsPeriodizableInBall D ρ f' := by
      simpa using t₁.apply l
    have b₂ : BallPeriodization.IsPeriodizableInBall D ρ f'' := by
      simpa using t₂.apply l
    have l₁ : IsLipschitzFor euclidDistTorus (TestFunctions.periodize D.side f') := by
      simpa [periodize_apply] using hlip ρ _ t₁ l
    have l₂ : IsLipschitzFor euclidDistTorus (TestFunctions.periodize D.side f'') := by
      simpa [periodize_apply] using hlip ρ _ t₂ l
    have hcomb : TestFunctions.periodize D.side (c' • f' + c'' • f'') =
        fun x => c' * TestFunctions.periodize D.side f' x +
          c'' * TestFunctions.periodize D.side f'' x := by
      rw [((hT D ρ h0 hle).2.1 ℝ).2.1 f' f'' c' c'' b₁ b₂ |>.2]
      funext x
      simp
    have h := hreal.map_update_add (periodize D (Function.update X l f')) l
      (TestFunctions.periodize D.side f') (TestFunctions.periodize D.side f'') c' c''
      (hlip ρ _ t₁) l₁ l₂
    have u₀ : Function.update (periodize D (Function.update X l f')) l
        (fun x => c' * TestFunctions.periodize D.side f' x +
          c'' * TestFunctions.periodize D.side f'' x) =
        periodize D (Function.update X l (c' • f' + c'' • f'')) := by
      rw [periodize_update, periodize_update, Function.update_idem, hcomb]
    have u₁ : Function.update (periodize D (Function.update X l f')) l
        (TestFunctions.periodize D.side f') = periodize D (Function.update X l f') := by
      rw [periodize_update, Function.update_idem]
    have u₂ : Function.update (periodize D (Function.update X l f')) l
        (TestFunctions.periodize D.side f'') = periodize D (Function.update X l f'') := by
      rw [periodize_update, periodize_update, Function.update_idem]
    rw [u₀, u₁, u₂] at h
    rw [hconn, hconn, hconn]
    exact h
  refine ⟨fun ρ X v hX hv => ?_, fun ρ h0 hle X hX => ?_, hlinear,
    fun ρ h0 hle X hX l hl => ?_⟩
  · have hv' : v = periodize D X := funext fun l =>
      ((((hT D ρ hX.1 hX.2.1).2.1 ℝ).1 (X l) (hX.apply l)).2.2.2.1 (v l)).1 (hv l)
    rw [hv']
    rfl
  · rw [hconn]
    exact hreal.im_eq_zero _ (hlip ρ X ⟨h0, hle, hX.1, hX.2⟩)
  · have hu : Function.update X l 0 = X := by
      rw [← hl, Function.update_eq_self]
    have h := hlinear ρ h0 hle X l 0 0 0 0 (by rwa [hu]) (by rwa [hu])
      (by simpa [hu] using hX)
    simpa [hu] using h
end ConnectedMultilinearity
open ConnectedMultilinearity in
theorem ConnectedMultilinearity.statement_holds
    (hM : TorusCumulants.Multilinearity.claim)
    (hT : PeriodizationThroughBall.PeriodizationLemma)
    (hC : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    ConnectedMultilinearity.Statement :=
  ⟨hM.1, fun D K _ hβ _ hn =>
    have hreal := realLipschitzLinearity D K hM hC hβ hn
    ⟨hreal, separatedTupleLinearity D K hT hβ hn hreal⟩⟩
end YangMills.Construction.BallTuples
end
