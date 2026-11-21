import YangMills.Construction.Cumulants.MomentExpansionUnderTwoMeasures
import YangMills.Construction.InfiniteLattice.MultilinearityOfTheConnectedCurvatureFunctions
import YangMills.Construction.InfiniteLattice.TransportToATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TorusCumulants.Multilinearity
open Cumulants LatticeProbability SeparatedFamilies
open Probability (IsBoundedRealRV)
theorem mixedCumulant_realLinear (hC : Cumulants.MomentComparison.momentExpansionAndStability) :
    MixedCumulantRealLinear := by
  intro Ω _ μ _ n k Y Y' Y'' c c' hY hY' hY'' hk
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt k.isLt)
  let G : ℕ → Ω → ℝ := fun j => if h : j - 1 < n then Y ⟨j - 1, h⟩ else 0
  have hG : Cumulants.MomentComparison.shiftedFamily n G = Y := by
    funext i
    simp [Cumulants.MomentComparison.shiftedFamily, G]
  have hb : ∀ i ∈ Finset.Icc 1 n, IsBoundedRealRV (G i) := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have hlt : i - 1 < n := by omega
    have hGi : G i = Y ⟨i - 1, hlt⟩ := by simp [G, hlt]
    rw [hGi]
    exact hY _
  obtain ⟨-, -, him, -, hlin⟩ := (hC Ω n G hn hb).1 μ
  rw [hG] at him hlin
  refine ⟨him, ?_⟩
  have h := hlin k Y' Y'' c c' hY' hY''
  rw [← hk, Function.update_eq_self] at h
  exact h
variable (s : Conventions.StandingParameters)
theorem observableVector_update {n : ℕ} (h : Fin n → s.Torus → ℝ) (k : Fin n) (g : s.Torus → ℝ) :
    observableVector s (Function.update h k g) =
      Function.update (observableVector s h) k (observableOn s g) := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [observableVector]
  · simp [observableVector, Function.update_of_ne hi]
theorem observableOn_linearCombination (hO : ObservablesBoundedRV s)
    (g g' : s.Torus → ℝ) (a a' : ℝ) :
    observableOn s (fun u => a * g u + a' * g' u) =
      fun U => a * observableOn s g U + a' * observableOn s g' U := by
  obtain ⟨-, -, ⟨B, T, -, hT⟩, -⟩ := hO
  have hfun : (fun u => a * g u + a' * g' u) = a • g + a' • g' := by
    funext u
    simp
  have h := hT (a • g + a' • g')
  rw [map_add, map_smul, map_smul] at h
  rw [hfun, ← h]
  funext U
  simp [hT]
theorem cumulantFunctional_realLinear (hCI : MixedCumulantRealLinear) (β : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hprob : IsProbabilityMeasure (gibbsMeasureOn s β))
    (hO : ObservablesBoundedRV s)
    (hL : ∀ f : Fin n → s.Torus → ℝ, CumulantEqMixedCumulant s β f) :
    FunctionalRealLinear s β n := by
  have hval : ∀ f : Fin n → s.Torus → ℝ, cumulantFunctional s.L s.m s.K β f =
      mixedCumulant (gibbsMeasureOn s β) (observableVector s f) := fun f => (hL f).1
  have hbd : ∀ f : Fin n → s.Torus → ℝ, ∀ i, IsBoundedRealRV (observableVector s f i) :=
    fun f i => hO.1 (f i)
  intro h _
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact (hCI (GaugeConfig s) (gibbsMeasureOn s β) n ⟨0, hn⟩ (observableVector s h)
      (observableVector s h ⟨0, hn⟩) (observableVector s h ⟨0, hn⟩) 1 0 (hbd h) (hbd h _) (hbd h _)
      (by funext x; simp)).1
  · intro k g g' a a' _ _
    rw [hval, hval, hval]
    have hk : observableVector s (Function.update h k fun u => a * g u + a' * g' u) k =
        fun x => a * observableOn s g x + a' * observableOn s g' x := by
      rw [observableVector_update, Function.update_self, observableOn_linearCombination s hO]
    have hlin := (hCI (GaugeConfig s) (gibbsMeasureOn s β) n k
      (observableVector s (Function.update h k fun u => a * g u + a' * g' u))
      (observableOn s g) (observableOn s g') a a'
      (hbd _) (hO.1 g) (hO.1 g') hk).2
    simp only [observableVector_update, Function.update_idem] at hlin ⊢
    exact hlin
theorem periodizedFamily_update {n : ℕ} (L m : ℕ) (Y : Fin n → (Fin 4 → ℝ) → ℝ) (k : Fin n)
    (f : (Fin 4 → ℝ) → ℝ) :
    periodizedFamily L m (Function.update Y k f) =
      Function.update (periodizedFamily L m Y) k
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [periodizedFamily, SchwingerFunctions.periodizeAll]
  · simp [periodizedFamily, SchwingerFunctions.periodizeAll, Function.update_of_ne hi]
theorem isLipschitzFor_euclidDistR4 {f : (Fin 4 → ℝ) → ℝ} (hf : IsEuclidLipschitz f) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|C|, abs_nonneg _, fun x y => ?_⟩
  have hd : 0 ≤ TestFunctions.euclidDistR4 x y := Real.sqrt_nonneg _
  calc ‖f x - f y‖ = |f x - f y| := Real.norm_eq_abs _
    _ ≤ C * TestFunctions.euclidDistR4 x y := hC x y
    _ ≤ |C| * TestFunctions.euclidDistR4 x y := mul_le_mul_of_nonneg_right (le_abs_self C) hd
theorem admissibleData_of_radius {ρ : ℝ} (hρ : IsAdmissibleRadius s.L s.m ρ) :
    PeriodicTransport.AdmissibleData s.L s.m ρ :=
  ⟨s.isAdmissible, s.m.pos, hρ.pos, hρ.two_mul_add_two_le⟩
theorem supportedInBall_apply {n : ℕ} {ρ : ℝ} {Y : Fin n → (Fin 4 → ℝ) → ℝ}
    (hY : Y ∈ separatedLipschitzSetIn n (ENNReal.ofReal ρ)) (i : Fin n) :
    PeriodicTransport.SupportedInBall ρ (Y i) :=
  ⟨hY.1.hasCompactSupport i, hY.2 i⟩
theorem periodize_apply_isTorusLipschitz (hT : PeriodicTransport.MainClaim) {n : ℕ} {ρ : ℝ}
    (hρ : IsAdmissibleRadius s.L s.m ρ) {Y : Fin n → (Fin 4 → ℝ) → ℝ}
    (hY : Y ∈ separatedLipschitzSetIn n (ENNReal.ofReal ρ)) (i : Fin n) :
    IsTorusLipschitz s (TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (Y i)) :=
  ((hT s.L s.m ρ (Y i) (Y i) (admissibleData_of_radius s hρ) (supportedInBall_apply hY i)
    (supportedInBall_apply hY i)).2.2.2.2.1
      (isLipschitzFor_euclidDistR4 (hY.1.lipschitz i))).1
theorem cumulantOfFamily_realAdditive (hT : PeriodicTransport.MainClaim) (β : ℝ) (n : ℕ)
    (hlin : FunctionalRealLinear s β n) {ρ : ℝ} (hρ : IsAdmissibleRadius s.L s.m ρ) :
    FamilyFunctionalRealAdditive s β n ρ := by
  intro Y hY
  have hLip : ∀ i, IsTorusLipschitz s (periodizedFamily s.L s.m Y i) :=
    fun i => periodize_apply_isTorusLipschitz s hT hρ hY i
  have hentry : ∀ k, periodizedFamily s.L s.m Y k =
      TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (Y k) := fun _ => rfl
  have hhom : ∀ (k : Fin n) (c : ℝ),
      Function.update Y k (c • Y k) ∈ separatedLipschitzSetIn n (ENNReal.ofReal ρ) →
      cumulantOfFamily s.L s.m s.K β (Function.update Y k (c • Y k)) =
        (c : ℂ) * cumulantOfFamily s.L s.m s.K β Y := by
    intro k c _
    have hc := supportedInBall_apply hY k
    have ht := (hT s.L s.m ρ (Y k) (Y k) (admissibleData_of_radius s hρ) hc hc).2.2.2.1 c 0
    have hform : TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (c • Y k) =
        fun u => c * periodizedFamily s.L s.m Y k u + 0 * periodizedFamily s.L s.m Y k u := by
      simp only [zero_smul, add_zero] at ht
      rw [ht]
      funext u
      simp [hentry]
    have h := (hlin (periodizedFamily s.L s.m Y) hLip).2 k (periodizedFamily s.L s.m Y k)
      (periodizedFamily s.L s.m Y k) c 0 (hLip k) (hLip k)
    simp only [Function.update_eq_self] at h
    unfold cumulantOfFamily
    rw [periodizedFamily_update, hform, h]
    simp
  refine ⟨(hlin (periodizedFamily s.L s.m Y) hLip).1, ?_, hhom, ?_⟩
  · intro k f' h1 _
    have hc := supportedInBall_apply hY k
    have hc' : PeriodicTransport.SupportedInBall ρ f' := by
      simpa using supportedInBall_apply h1 k
    have hLip' : IsTorusLipschitz s
        (TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) f') := by
      simpa using periodize_apply_isTorusLipschitz s hT hρ h1 k
    have ht := (hT s.L s.m ρ (Y k) f' (admissibleData_of_radius s hρ) hc hc').2.2.2.1 1 1
    have hform : TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) (Y k + f') =
        fun u => (1 : ℝ) * periodizedFamily s.L s.m Y k u +
          (1 : ℝ) * TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) f' u := by
      simp only [one_smul] at ht
      rw [ht]
      funext u
      simp [hentry]
    have h := (hlin (periodizedFamily s.L s.m Y) hLip).2 k (periodizedFamily s.L s.m Y k)
      (TestFunctions.periodize (PeriodicLattice.torusSide s.L s.m) f') 1 1 (hLip k) hLip'
    simp only [Function.update_eq_self] at h
    unfold cumulantOfFamily
    rw [periodizedFamily_update, periodizedFamily_update, hform, h]
    simp
  · intro k hk
    have hupd : Function.update Y k ((0 : ℝ) • Y k) = Y := by
      rw [zero_smul, ← hk, Function.update_eq_self]
    have h := hhom k 0 (by rw [hupd]; exact hY)
    rw [hupd] at h
    simpa using h
theorem claim_holds (hC : Cumulants.MomentComparison.momentExpansionAndStability)
    (hP : LatticeProbability.ProbabilitySpaceTheorem.claim) (hT : PeriodicTransport.MainClaim) :
    claim := by
  have hCI := mixedCumulant_realLinear hC
  refine ⟨hCI, fun s β n hβ hn => ?_⟩
  obtain ⟨hW, -, hD, hO, hL, -⟩ := hP s β hβ
  have hprob : IsProbabilityMeasure (gibbsMeasureOn s β) := hW.2.2.1
  have hlin := cumulantFunctional_realLinear s hCI β n hn hprob hO fun f => hL n f hn
  refine ⟨fun h _ => ⟨hprob, fun i => hO.1 (h i), (hL n h hn).1⟩, ?_, hlin, ?_, fun ρ hρ =>
    cumulantOfFamily_realAdditive s hT β n hlin hρ⟩
  · obtain ⟨Λ, -, -, hΛ, -⟩ := hO.2.2.2
    exact ⟨⟨Λ, hΛ⟩, fun h hh => (hD.2.1 h hh).1⟩
  · intro Y hY
    refine ⟨cumulantOfFamily s.L s.m s.K β Y, fun ρ hρ hs =>
      ⟨⟨hρ.pos, ⟨hY, hs⟩, ?_⟩, rfl⟩⟩
    have h := hρ.two_mul_add_two_le
    simp only [PeriodicLattice.torusSide]
    linarith
end YangMills.Construction.TorusCumulants.Multilinearity
