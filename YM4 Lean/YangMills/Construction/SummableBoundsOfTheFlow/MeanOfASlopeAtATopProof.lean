import YangMills.Construction.SummableBoundsOfTheFlow.MeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfASlopeAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates
namespace Cumulants
variable {F : BlockFrame}
namespace SlopeMeanAtTop
theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (U : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G U c X = G U := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.bondDeriv_zero <;> assumption
end SlopeMeanAtTop
set_option maxHeartbeats 1600000 in
open SlopeMeanAtTop in
theorem slopeMeanDerivBounds_holds : slopeMeanDerivBounds := by
  intro F s a ρA x m ρ κ p φ V Y Hf μ b₁ b₂ b₃ b₄ b₅ hκ h₂ h₃ h₄ hExp hmean hB hmid hcov
  set Φ : StepVariable (finiteCells F) → ℝ := fun η => interpolatedExponentOfTerms s a ρA x m φ η V with hΦ
  have covU : ∀ f g, gibbsCovariance μ Φ f g = ballCovariance (cutoffFactor ρ p) Φ f g := fun f g => by
    simp only [gibbsCovariance, ballCovariance, hmean]
  have thirdU : ∀ f g u, gibbsCumulantThree μ Φ f g u = ballThirdCumulant (cutoffFactor ρ p) Φ f g u := fun f g u => by
    simp only [gibbsCumulantThree, ballThirdCumulant, hmean]
  have fourthU : ∀ f g u v, gibbsCumulantFour μ Φ f g u v =
      ballFourthCumulant (cutoffFactor ρ p) Φ f g u v := fun f g u v => by
    simp only [gibbsCumulantFour, ballFourthCumulant, hmean]
  have hH0 : (fun η => Hf η V) = fieldDeriv (Hf) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) := by
    funext η
    unfold fieldDeriv
    rw [bondDeriv_zero]
  have small : ∀ {k : ℕ} (b : ℝ), 0 ≤ b → ∀ c : Fin k → F.Site F.top × Fin 4,
      b * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ))) ≤ b * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := fun b hb c => by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hb
    have h0 : (0 : ℝ) ≤ (bondSpan Y c : ℝ) := Nat.cast_nonneg _
    have : κ / 2 ^ 6 * (bondSpan Y c : ℝ) ≤ κ / 16 * (bondSpan Y c : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ h0
      norm_num
      linarith
    linarith
  refine ⟨fun k c X hk hX => ?_, fun c X hX => ?_⟩
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · have e0 : bondDeriv (gibbsMeanAt μ (interpolatedExponentOfTerms s a ρA x m φ) (Hf)) V c X =
          gibbsMean μ Φ (fieldDeriv (Hf) V c X) := by
        rw [bondDeriv_zero]
        unfold gibbsMeanAt
        congr 1
      have t0 := hmid 0 c X (by norm_num) hX
      rw [e0]
      refine t0.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith
    · have t0 := hmid 1 c X (by norm_num) hX
      have t1 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c X)| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        rw [covU]
        exact (hB.covariance 0 1 1 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) c X c (by norm_num) (by norm_num) (fun l => l.elim0) hX (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩)])).trans (small b₂ (by assumption) c)
      have q1 : 0 ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₂ (Real.exp_pos _).le
      have q2 : 0 ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₃ (Real.exp_pos _).le
      have q3 : 0 ≤ b₄ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₄ (Real.exp_pos _).le
      rw [hExp.deriv_one c X, hH0]
      rw [abs_le] at t0 t1 ⊢
      constructor <;> linarith [t0.1, t0.2, t1.1, t1.2]
    · have t0 := hmid 2 c X (by norm_num) hX
      have t1 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        rw [covU]
        exact (hB.covariance 1 1 2 (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (fun _ => hX 1) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩), Or.inl ⟨0, rfl⟩])).trans (small b₂ (by assumption) c)
      have t2 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1))| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        rw [covU]
        exact (hB.covariance 1 1 2 (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) c (by norm_num) (by norm_num) (fun _ => hX 0) (fun _ => hX 1) (by intro l; fin_cases l; exacts [Or.inl ⟨0, rfl⟩, Or.inr (⟨0, rfl⟩)])).trans (small b₂ (by assumption) c)
      have t3 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c X)| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        rw [covU]
        exact (hB.covariance 0 2 2 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) c X c (by norm_num) (by norm_num) (fun l => l.elim0) hX (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩), Or.inr (⟨1, rfl⟩)])).trans (small b₂ (by assumption) c)
      have t4 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        rw [thirdU]
        exact (hB.third 0 1 1 2 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by norm_num) (fun l => l.elim0) (fun _ => hX 1) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (Or.inr (⟨0, rfl⟩)), Or.inr (Or.inl ⟨0, rfl⟩)])).trans (small b₃ (by assumption) c)
      have q1 : 0 ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₂ (Real.exp_pos _).le
      have q2 : 0 ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₃ (Real.exp_pos _).le
      have q3 : 0 ≤ b₄ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₄ (Real.exp_pos _).le
      rw [hExp.deriv_two c X, hH0]
      simp only [fieldDerivOne]
      rw [abs_le] at t0 t1 t2 t3 t4 ⊢
      constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]
  · have m0 := hmid 3 c X (by norm_num) hX
    have c5 := hcov c X hX
    rw [← covU, hH0] at c5
    have t1 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V ![c 1, c 2] ![X 1, X 2]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 2 1 3 ![c 1, c 2] ![X 1, X 2] (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by intro l; fin_cases l; exacts [hX 1, hX 2]) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩), Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩])).trans (small b₂ (by assumption) c)
    have t2 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V ![c 0, c 2] ![X 0, X 2]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1))| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 2 1 3 ![c 0, c 2] ![X 0, X 2] (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) c (by norm_num) (by norm_num) (by intro l; fin_cases l; exacts [hX 0, hX 2]) (fun _ => hX 1) (by intro l; fin_cases l; exacts [Or.inl ⟨0, rfl⟩, Or.inr (⟨0, rfl⟩), Or.inl ⟨1, rfl⟩])).trans (small b₂ (by assumption) c)
    have t3 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V ![c 0, c 1] ![X 0, X 1]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2))| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 2 1 3 ![c 0, c 1] ![X 0, X 1] (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) c (by norm_num) (by norm_num) (by intro l; fin_cases l; exacts [hX 0, hX 1]) (fun _ => hX 2) (by intro l; fin_cases l; exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr (⟨0, rfl⟩)])).trans (small b₂ (by assumption) c)
    have t4 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 0, c 1] ![X 0, X 1])| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 1 2 3 (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) ![c 0, c 1] ![X 0, X 1] c (by norm_num) (by norm_num) (fun _ => hX 2) (by intro l; fin_cases l; exacts [hX 0, hX 1]) (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩), Or.inr (⟨1, rfl⟩), Or.inl ⟨0, rfl⟩])).trans (small b₂ (by assumption) c)
    have t5 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 0, c 2] ![X 0, X 2])| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 1 2 3 (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) ![c 0, c 2] ![X 0, X 2] c (by norm_num) (by norm_num) (fun _ => hX 1) (by intro l; fin_cases l; exacts [hX 0, hX 2]) (by intro l; fin_cases l; exacts [Or.inr (⟨0, rfl⟩), Or.inl ⟨0, rfl⟩, Or.inr (⟨1, rfl⟩)])).trans (small b₂ (by assumption) c)
    have t6 : |gibbsCovariance μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 1, c 2] ![X 1, X 2])| ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [covU]
      exact (hB.covariance 1 2 3 (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) ![c 1, c 2] ![X 1, X 2] c (by norm_num) (by norm_num) (fun _ => hX 0) (by intro l; fin_cases l; exacts [hX 1, hX 2]) (by intro l; fin_cases l; exacts [Or.inl ⟨0, rfl⟩, Or.inr (⟨0, rfl⟩), Or.inr (⟨1, rfl⟩)])).trans (small b₂ (by assumption) c)
    have t7 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 1 1 1 3 (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by norm_num) (fun _ => hX 2) (fun _ => hX 1) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (Or.inr (⟨0, rfl⟩)), Or.inr (Or.inl ⟨0, rfl⟩), Or.inl ⟨0, rfl⟩])).trans (small b₃ (by assumption) c)
    have t8 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 1 1 1 3 (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by norm_num) (fun _ => hX 1) (fun _ => hX 2) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (Or.inr (⟨0, rfl⟩)), Or.inl ⟨0, rfl⟩, Or.inr (Or.inl ⟨0, rfl⟩)])).trans (small b₃ (by assumption) c)
    have t9 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 1 1 1 3 (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) c (by norm_num) (by norm_num) (by norm_num) (fun _ => hX 0) (fun _ => hX 2) (fun _ => hX 1) (by intro l; fin_cases l; exacts [Or.inl ⟨0, rfl⟩, Or.inr (Or.inr (⟨0, rfl⟩)), Or.inr (Or.inl ⟨0, rfl⟩)])).trans (small b₃ (by assumption) c)
    have u1 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 1, c 2] ![X 1, X 2]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 0 2 1 3 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) ![c 1, c 2] ![X 1, X 2] (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by norm_num) (fun l => l.elim0) (by intro l; fin_cases l; exacts [hX 1, hX 2]) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (Or.inr (⟨0, rfl⟩)), Or.inr (Or.inl ⟨0, rfl⟩), Or.inr (Or.inl ⟨1, rfl⟩)])).trans (small b₃ (by assumption) c)
    have u2 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 0, c 2] ![X 0, X 2]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 0 2 1 3 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) ![c 0, c 2] ![X 0, X 2] (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) c (by norm_num) (by norm_num) (by norm_num) (fun l => l.elim0) (by intro l; fin_cases l; exacts [hX 0, hX 2]) (fun _ => hX 1) (by intro l; fin_cases l; exacts [Or.inr (Or.inl ⟨0, rfl⟩), Or.inr (Or.inr (⟨0, rfl⟩)), Or.inr (Or.inl ⟨1, rfl⟩)])).trans (small b₃ (by assumption) c)
    have u3 : |gibbsCumulantThree μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V ![c 0, c 1] ![X 0, X 1]) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2))| ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [thirdU]
      exact (hB.third 0 2 1 3 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) ![c 0, c 1] ![X 0, X 1] (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) c (by norm_num) (by norm_num) (by norm_num) (fun l => l.elim0) (by intro l; fin_cases l; exacts [hX 0, hX 1]) (fun _ => hX 2) (by intro l; fin_cases l; exacts [Or.inr (Or.inl ⟨0, rfl⟩), Or.inr (Or.inl ⟨1, rfl⟩), Or.inr (Or.inr (⟨0, rfl⟩))])).trans (small b₃ (by assumption) c)
    have u4 : |gibbsCumulantFour μ Φ (fieldDeriv (Hf) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1)) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0))| ≤ b₄ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      rw [fourthU]
      exact (hB.fourth 0 1 1 1 3 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) (fun _ : Fin 1 => c 2) (fun _ : Fin 1 => X 2) (fun _ : Fin 1 => c 1) (fun _ : Fin 1 => X 1) (fun _ : Fin 1 => c 0) (fun _ : Fin 1 => X 0) c (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun l => l.elim0) (fun _ => hX 2) (fun _ => hX 1) (fun _ => hX 0) (by intro l; fin_cases l; exacts [Or.inr (Or.inr (Or.inr (⟨0, rfl⟩))), Or.inr (Or.inr (Or.inl ⟨0, rfl⟩)), Or.inr (Or.inl ⟨0, rfl⟩)])).trans (small b₄ (by assumption) c)
    have q1 : 0 ≤ b₂ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₂ (Real.exp_pos _).le
    have q2 : 0 ≤ b₃ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₃ (Real.exp_pos _).le
    have q3 : 0 ≤ b₄ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := mul_nonneg h₄ (Real.exp_pos _).le
    rw [hExp.deriv_three c X, hH0]
    simp only [fieldDerivOne, fieldDerivTwo]
    rw [abs_le] at m0 c5 t1 t2 t3 t4 t5 t6 t7 t8 t9 u1 u2 u3 u4 ⊢
    constructor <;> linarith [m0.1, m0.2, c5.1, c5.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2, u1.1, u1.2, u2.1, u2.2, u3.1, u3.2, u4.1, u4.2]
end Cumulants
end YangMills.Construction
end
