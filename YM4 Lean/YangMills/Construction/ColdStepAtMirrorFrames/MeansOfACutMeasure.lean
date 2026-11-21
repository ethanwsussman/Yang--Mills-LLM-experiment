import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def IsBoundedContinuousOn (ι : Type) (ρ : ℝ) (f : BondField ι → ℝ) : Prop :=
  ContinuousOn f (openPolyball ι ρ) ∧ ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M
structure IsPositiveUnitalForm {ι : Type} [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) :
    Prop where
  map_one : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => 1) = 1
  congr_on : ∀ f g : BondField ι → ℝ, (∀ η ∈ openPolyball ι ρ, f η = g η) →
    ballExpectation (cutoffFactor ρ p) Ψ f = ballExpectation (cutoffFactor ρ p) Ψ g
  congr_potential : ∀ Ψ' f : BondField ι → ℝ, (∀ η ∈ openPolyball ι ρ, Ψ η = Ψ' η) →
    ballExpectation (cutoffFactor ρ p) Ψ f = ballExpectation (cutoffFactor ρ p) Ψ' f
  mono : ∀ f g : BondField ι → ℝ, IsBoundedContinuousOn ι ρ f → IsBoundedContinuousOn ι ρ g →
    (∀ η ∈ openPolyball ι ρ, f η ≤ g η) →
    ballExpectation (cutoffFactor ρ p) Ψ f ≤ ballExpectation (cutoffFactor ρ p) Ψ g
  map_add : ∀ f g : BondField ι → ℝ, IsBoundedContinuousOn ι ρ f → IsBoundedContinuousOn ι ρ g →
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => f η + g η) =
      ballExpectation (cutoffFactor ρ p) Ψ f + ballExpectation (cutoffFactor ρ p) Ψ g
  map_smul : ∀ (c : ℝ) (f : BondField ι → ℝ),
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => c * f η) = c * ballExpectation (cutoffFactor ρ p) Ψ f
section BoundedContinuous
variable {ι : Type} {ρ : ℝ} {f g : BondField ι → ℝ}
theorem IsBoundedContinuousOn.const (c : ℝ) : IsBoundedContinuousOn ι ρ (fun _ => c) :=
  ⟨continuousOn_const, |c|, fun _ _ => le_rfl⟩
theorem IsBoundedContinuousOn.add (hf : IsBoundedContinuousOn ι ρ f) (hg : IsBoundedContinuousOn ι ρ g) :
    IsBoundedContinuousOn ι ρ (fun η => f η + g η) := by
  obtain ⟨cf, M, hM⟩ := hf
  obtain ⟨cg, N, hN⟩ := hg
  exact ⟨cf.add cg, M + N, fun η hη => (abs_add_le _ _).trans (add_le_add (hM η hη) (hN η hη))⟩
theorem IsBoundedContinuousOn.mul (hf : IsBoundedContinuousOn ι ρ f) (hg : IsBoundedContinuousOn ι ρ g) :
    IsBoundedContinuousOn ι ρ (fun η => f η * g η) := by
  obtain ⟨cf, M, hM⟩ := hf
  obtain ⟨cg, N, hN⟩ := hg
  refine ⟨cf.mul cg, |M| * |N|, fun η hη => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hM η hη).trans (le_abs_self M)) ((hN η hη).trans (le_abs_self N))
    (abs_nonneg _) (abs_nonneg _)
theorem IsBoundedContinuousOn.neg (hf : IsBoundedContinuousOn ι ρ f) :
    IsBoundedContinuousOn ι ρ (fun η => - f η) := by
  obtain ⟨cf, M, hM⟩ := hf
  exact ⟨cf.neg, M, fun η hη => by simpa using hM η hη⟩
theorem IsBoundedContinuousOn.sub (hf : IsBoundedContinuousOn ι ρ f) (hg : IsBoundedContinuousOn ι ρ g) :
    IsBoundedContinuousOn ι ρ (fun η => f η - g η) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg
theorem IsBoundedContinuousOn.sum {α : Type} (s : Finset α) (h : α → BondField ι → ℝ)
    (hh : ∀ a ∈ s, IsBoundedContinuousOn ι ρ (h a)) :
    IsBoundedContinuousOn ι ρ (fun η => ∑ a ∈ s, h a η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsBoundedContinuousOn.const (ι := ι) (ρ := ρ) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hh a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hh b (Finset.mem_insert_of_mem hb))
theorem IsBoundedContinuousOn.norm_sq_apply (hρ : 0 < ρ) (b : ι) :
    IsBoundedContinuousOn ι ρ (fun η => ‖η b‖ ^ 2) := by
  refine ⟨(((continuous_apply b).norm).pow 2).continuousOn, ρ ^ 2, fun η hη => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hη b).le 2
end BoundedContinuous
theorem IsPositiveUnitalForm.map_zero {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    (E : IsPositiveUnitalForm ρ p Ψ) : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => 0) = 0 := by
  have := E.map_smul 0 (fun _ => 1)
  simpa using this
theorem IsPositiveUnitalForm.map_sum {ι α : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    (E : IsPositiveUnitalForm ρ p Ψ) (s : Finset α) (h : α → BondField ι → ℝ)
    (hh : ∀ a ∈ s, IsBoundedContinuousOn ι ρ (h a)) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => ∑ a ∈ s, h a η) =
      ∑ a ∈ s, ballExpectation (cutoffFactor ρ p) Ψ (h a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using E.map_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [E.map_add _ _ (hh a (Finset.mem_insert_self a s))
      (IsBoundedContinuousOn.sum s h fun b hb => hh b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hh b (Finset.mem_insert_of_mem hb)]
theorem IsPositiveUnitalForm.map_sub {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    (E : IsPositiveUnitalForm ρ p Ψ) {f g : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f)
    (hg : IsBoundedContinuousOn ι ρ g) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => f η - g η) =
      ballExpectation (cutoffFactor ρ p) Ψ f - ballExpectation (cutoffFactor ρ p) Ψ g := by
  have h1 := E.map_add f (fun η => (-1) * g η) hf (by simpa using hg.neg)
  have h2 := E.map_smul (-1) g
  have e : (fun η => f η - g η) = fun η => f η + (-1) * g η := by
    funext η
    ring
  rw [e, h1, h2]
  ring
theorem IsPositiveUnitalForm.abs_le {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    (E : IsPositiveUnitalForm ρ p Ψ) {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) {M : ℝ}
    (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤ M) : |ballExpectation (cutoffFactor ρ p) Ψ f| ≤ M := by
  have hu := E.mono f (fun _ => M) hf (IsBoundedContinuousOn.const M)
    (fun η hη => (le_abs_self _).trans (h η hη))
  have hl := E.mono (fun _ => -M) f (IsBoundedContinuousOn.const (-M)) hf
    (fun η hη => by linarith [neg_abs_le (f η), h η hη])
  have eM : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => M) = M := by
    have := E.map_smul M (fun _ => 1)
    rw [E.map_one] at this
    simpa using this
  have eN : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => -M) = -M := by
    have := E.map_smul (-M) (fun _ => 1)
    rw [E.map_one] at this
    simpa using this
  rw [eM] at hu
  rw [eN] at hl
  exact _root_.abs_le.mpr ⟨hl, hu⟩
def CutoffExpectationIsPositiveForm : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ),
    0 < ρ → IsCutoff ρ p → Continuous Ψ → IsPositiveUnitalForm ρ p Ψ
end YangMills.Construction.ColdStepAtMirrorFrames
end
