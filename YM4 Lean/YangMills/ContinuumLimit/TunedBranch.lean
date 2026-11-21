import YangMills.ContinuumLimit.TuningAtAdmissibleTables
set_option autoImplicit false
open Set
namespace YangMills.ContinuumLimit
open YangMills.Construction

theorem tuned_branch_of_le {T : RenormalizationStepParameters.ParameterAssignment} {y lam cr : ℝ}
    {Kr : WeightedResponses.ResponseParameters} (ht : RunTable T y Kr lam cr) (K : ℕ)
    {P b₀ b : ℝ} (hP : runFloor T y cr ≤ P) (htrial : IsTunedAt T y P K b₀) (hb : b₀ ≤ b) :
    let p := TotalDensityFlow.coupling (T.stepParameters y) b K
    IsTunedAt T y p K b ∧ (3 / 4 : ℝ) * (b - b₀) ≤ p - P ∧ p - P ≤ (5 / 4 : ℝ) * (b - b₀) := by
  let f := fun β => TotalDensityFlow.coupling (T.stepParameters y) β K
  let I := runDomain T y K
  obtain ⟨_, ⟨hopen, hupper, _, hstay, _⟩, ⟨hreg, _, hder⟩, hrange, _, _⟩ :=
    tuned_at_runFloor_closed ht K
  have h₀ : b₀ ∈ I := (hrange P hP).2 b₀ htrial
  have h₁ : b ∈ I := hupper hb h₀
  have hcv : Convex ℝ I := hupper.ordConnected.convex
  have hdiff : DifferentiableOn ℝ f (interior I) := by
    rw [hopen.interior_eq]
    exact hreg.differentiableOn (by norm_num)
  have hlo := hcv.mul_sub_le_image_sub_of_le_deriv (f := f) hreg.continuousOn hdiff
    (fun a ha => (hder a (interior_subset ha)).1) b₀ h₀ b h₁ hb
  have hhi := hcv.image_sub_le_mul_sub_of_deriv_le (f := f) hreg.continuousOn hdiff
    (fun a ha => (hder a (interior_subset ha)).2) b₀ h₀ b h₁ hb
  have hp₀ : f b₀ = P := htrial.2
  rw [hp₀] at hlo hhi
  have h := hstay b h₁
  exact ⟨⟨⟨h.1, fun j hj => h.2 j (Nat.lt_succ_of_lt hj)⟩, rfl⟩, hlo, hhi⟩

end YangMills.ContinuumLimit

