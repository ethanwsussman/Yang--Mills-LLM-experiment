import YangMills.Construction.FourPointCondition.ConnectedFunctionsAreHomogeneous
import YangMills.Construction.InfiniteLattice.MultilinearityOfTheConnectedCurvatureFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
open TestFunctions PeriodicLattice ResponseInTheExpansion Conventions
private theorem isLipschitzFor_const_mul {X : Type*} {dist : X → X → ℝ} (a : ℝ) {f : X → ℝ}
    (h : IsLipschitzFor dist f) :
    IsLipschitzFor dist (fun x => a * f x) := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨|a| * C, by positivity, fun x y => ?_⟩
  have e : ‖a * f x - a * f y‖ = |a| * ‖f x - f y‖ := by
    rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg a)
abbrev _root_.YangMills.SharedProofs.p11306 := @isLipschitzFor_const_mul
private theorem cumulantFunctional_scale_finset (hM : TorusCumulants.Multilinearity.claim)
    (s : StandingParameters) (β : ℝ) (n : ℕ) (f : Fin n → s.Torus → ℝ) (c : Fin n → ℝ) (hβ : 0 < β) (hn : 1 ≤ n)
    (hf : ∀ i, IsLipschitzFor euclidDistTorus (f i)) (t : Finset (Fin n)) :
    TorusCumulants.cumulantFunctional s.L s.m s.K β (fun i x => (if i ∈ t then c i else 1) * f i x) =
      ((∏ i ∈ t, c i : ℝ) : ℂ) * TorusCumulants.cumulantFunctional s.L s.m s.K β f := by
  obtain ⟨-, -, hLin, -⟩ := (hM.2 s β n hβ hn)
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    set g : Fin n → s.Torus → ℝ := fun i x => (if i ∈ t then c i else 1) * f i x with hg
    have hl : ∀ i, IsLipschitzFor euclidDistTorus (g i) := fun i => isLipschitzFor_const_mul _ (hf i)
    have key := (hLin g hl).2 a (g a) (g a) (c a) 0 (hl a) (hl a)
    have e : (fun i x => (if i ∈ insert a t then c i else 1) * f i x) =
        Function.update g a (fun u => c a * g a u + 0 * g a u) := by
      funext i x
      by_cases hi : i = a
      · subst hi
        simp [hg, ha]
      · have : i ∈ insert a t ↔ i ∈ t := by simp [hi]
        simp [hg, Function.update_of_ne hi, this]
    rw [e, key, Function.update_eq_self, ih, Finset.prod_insert ha]
    push_cast
    ring
theorem connectedFunctionsHomogeneous
    (hM : TorusCumulants.Multilinearity.claim) :
    connectedFunctionsHomogeneousStatement := by
  refine ⟨fun s β n f c hβ hn hf => ⟨?_, ?_⟩, fun S q f c => ?_⟩
  · obtain ⟨-, -, hLin, -⟩ := (hM.2 s β n hβ hn)
    exact (hLin f hf).1
  · have := cumulantFunctional_scale_finset hM s β n f c hβ hn hf Finset.univ
    simp only [Finset.mem_univ, if_true] at this
    exact this
  · unfold gaussianCumulantLimit
    rw [mul_left_comm (∏ i, c i)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext u
    rw [Finset.prod_mul_distrib, mul_assoc]
end YangMills.Construction.FourPointCondition
end
