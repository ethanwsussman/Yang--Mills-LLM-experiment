import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace C1ViaLift
theorem torusCover_map_add (s : Conventions.StandingParameters) (x y : Fin 4 → ℝ) :
    ModelSpace.torusCover s (x + y) = ModelSpace.torusCover s x + ModelSpace.torusCover s y := rfl
theorem torusCover_surj (s : Conventions.StandingParameters) :
    Function.Surjective (ModelSpace.torusCover s) := by
  intro z
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (z μ)
  exact ⟨v, funext hv⟩
theorem proj_surj (s : Conventions.StandingParameters) (Y : ModelSpace) :
    Function.Surjective (ModelSpace.proj s Y) := by
  cases Y with
  | euclidean => exact Function.surjective_id
  | torus => exact torusCover_surj s
theorem isC1_iff_comp_proj (s : Conventions.StandingParameters) (Y : ModelSpace)
    (f : Y.Carrier s → ℝ) :
    ModelSpace.IsC1 s Y f ↔ TestFunctions.IsC1R4 (f ∘ ModelSpace.proj s Y) := by
  cases Y with
  | euclidean => exact Iff.rfl
  | torus => exact Iff.rfl
theorem gradR4_add_of_add_invariant (F : (Fin 4 → ℝ) → ℝ) (a : Fin 4 → ℝ)
    (hF : ∀ x, F (x + a) = F x) (x : Fin 4 → ℝ) :
    ModelSpace.gradR4 F (x + a) = ModelSpace.gradR4 F x := by
  funext μ
  have h : (fun t : ℝ => F (x + a + t • Pi.single μ (1 : ℝ))) =
      fun t : ℝ => F (x + t • Pi.single μ (1 : ℝ)) := by
    funext t
    rw [add_right_comm x a, hF]
  simp only [ModelSpace.gradR4, TestFunctions.partialDerivR4, h]
theorem exists_isGradOnTorus (s : Conventions.StandingParameters) (f : s.Torus → ℝ) :
    ∃ g, ModelSpace.IsGradOnTorus s f g := by
  choose v hv using torusCover_surj s
  refine ⟨fun z => ModelSpace.gradR4 (f ∘ ModelSpace.torusCover s) (v z), ?_⟩
  funext x
  have hker : ModelSpace.torusCover s (v (ModelSpace.torusCover s x) - x) = 0 := by
    have h := torusCover_map_add s x (v (ModelSpace.torusCover s x) - x)
    rw [add_sub_cancel, hv] at h
    exact (left_eq_add.1 h)
  have hinv : ∀ y, (f ∘ ModelSpace.torusCover s) (y + (v (ModelSpace.torusCover s x) - x)) =
      (f ∘ ModelSpace.torusCover s) y := by
    intro y
    simp only [Function.comp, torusCover_map_add, hker, add_zero]
  have h := gradR4_add_of_add_invariant _ _ hinv x
  rw [add_sub_cancel] at h
  exact h
theorem grad_comp_proj (s : Conventions.StandingParameters) (Y : ModelSpace)
    (f : Y.Carrier s → ℝ) :
    ModelSpace.grad s Y f ∘ ModelSpace.proj s Y = ModelSpace.gradR4 (f ∘ ModelSpace.proj s Y) := by
  cases Y with
  | euclidean => rfl
  | torus => exact Classical.epsilon_spec (exists_isGradOnTorus s f)
theorem claim_holds : C1ViaLift.Claim := by
  intro s Y
  refine ⟨isC1_iff_comp_proj s Y, ?_, ?_⟩
  · intro f _
    refine ⟨grad_comp_proj s Y f, fun g hg => ?_⟩
    funext z
    obtain ⟨x, rfl⟩ := proj_surj s Y z
    exact (congrFun hg x).trans (congrFun (grad_comp_proj s Y f) x).symm
  · intro f g hf hg
    have hf' : ContDiff ℝ 1 (f ∘ ModelSpace.proj s Y) := (isC1_iff_comp_proj s Y f).1 hf
    have hg' : ContDiff ℝ 1 (g ∘ ModelSpace.proj s Y) := (isC1_iff_comp_proj s Y g).1 hg
    refine ⟨fun α β => (isC1_iff_comp_proj s Y _).2 ?_, (isC1_iff_comp_proj s Y _).2 ?_⟩
    · exact (hf'.const_smul α).add (hg'.const_smul β)
    · exact hf'.mul hg'
end C1ViaLift
end YangMills.Construction.LatticeLimits
end
