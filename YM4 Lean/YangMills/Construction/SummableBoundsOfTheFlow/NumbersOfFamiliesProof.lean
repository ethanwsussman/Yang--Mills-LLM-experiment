import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensitiesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.FamilyNorms
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
private theorem trivialField_isCold {ℓ : StepParameters} (hℓ : ℓ.Admissible) (n : ℕ) :
    IsCold ℓ.threshold (trivialField n) := by
  intro x μ ν _
  have : curvature (trivialField n) x μ ν = 0 := by
    simp [curvature, holonomy, trivialField]
  rw [this]
  exact hℓ.σ_pos
private theorem eventually_le_and_ne_zero {ℓ : StepParameters} (hℓ : ℓ.Admissible) :
    ∀ᶠ n : ℕ in Filter.atTop, ℓ.n₀ ≤ n ∧ n ≠ 0 := by
  filter_upwards [Filter.eventually_ge_atTop (max ℓ.n₀ 1)] with n hn
  exact ⟨le_trans (le_max_left _ _) hn, by have := le_trans (le_max_right ℓ.n₀ 1) hn; omega⟩
private theorem mixedDeriv_add_eventually {ℓ : StepParameters} (hℓ : ℓ.Admissible) {f f' : LocalDensity}
    (hf : IsAdmissibleDensity ℓ f) (hf' : IsAdmissibleDensity ℓ f') (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    ∀ᶠ n : ℕ in Filter.atTop,
      mixedDeriv ((f + f') n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
        mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] +
        mixedDeriv (f' n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] := by
  filter_upwards [eventually_le_and_ne_zero hℓ] with n hn
  haveI : NeZero n := ⟨hn.2⟩
  have a := (hf.smooth n hn.1 0 (trivialField n) (trivialField_isCold hℓ n) 2
    ![bondFrom 0 c, bondFrom 0 c'] ![X, X']).of_le (m := 2) (by norm_num)
  have b := (hf'.smooth n hn.1 0 (trivialField n) (trivialField_isCold hℓ n) 2
    ![bondFrom 0 c, bondFrom 0 c'] ![X, X']).of_le (m := 2) (by norm_num)
  unfold mixedDeriv
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 2) (x := (0 : Fin 2 → ℝ)) a b
  have h2 : (fun s : Fin 2 → ℝ =>
        (f + f') n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] s (trivialField n))) =
      (fun s : Fin 2 → ℝ => f n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] s (trivialField n))) +
      (fun s : Fin 2 → ℝ => f' n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] s (trivialField n))) :=
    rfl
  rw [h2, this]
  rfl
private theorem mixedDeriv_smul_eventually {ℓ : StepParameters} (hℓ : ℓ.Admissible) (r : ℝ)
    {f : LocalDensity} (hf : IsAdmissibleDensity ℓ f) (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    ∀ᶠ n : ℕ in Filter.atTop,
      mixedDeriv ((r • f) n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
        r * mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] := by
  filter_upwards [eventually_le_and_ne_zero hℓ] with n hn
  haveI : NeZero n := ⟨hn.2⟩
  have a := (hf.smooth n hn.1 0 (trivialField n) (trivialField_isCold hℓ n) 2
    ![bondFrom 0 c, bondFrom 0 c'] ![X, X']).of_le (m := 2) (by norm_num)
  unfold mixedDeriv
  have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := 2) (x := (0 : Fin 2 → ℝ)) (a := r) a
  have h2 : (fun s : Fin 2 → ℝ =>
        (r • f) n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] s (trivialField n))) =
      r • (fun s : Fin 2 → ℝ => f n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] s (trivialField n))) :=
    rfl
  rw [h2, this]
  rfl
private theorem tendsto_secondDerivLimit (f : LocalDensity) (hl : HasLimitSecondDeriv f) (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    Filter.Tendsto (fun n : ℕ => mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (secondDerivLimit f c c' X X')) := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.tendsto_secondDerivLimit <;> assumption
private theorem secondDerivLimit_add {ℓ : StepParameters} (hℓ : ℓ.Admissible) {f f' : LocalDensity}
    (hf : IsAdmissibleDensity ℓ f) (hf' : IsAdmissibleDensity ℓ f') (hl : HasLimitSecondDeriv f)
    (hl' : HasLimitSecondDeriv f') :
    HasLimitSecondDeriv (f + f') ∧ ∀ c c' X X', secondDerivLimit (f + f') c c' X X' =
      secondDerivLimit f c c' X X' + secondDerivLimit f' c c' X X' := by
  have key : ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions), Filter.Tendsto
      (fun n : ℕ => mixedDeriv ((f + f') n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (secondDerivLimit f c c' X X' + secondDerivLimit f' c c' X X')) := by
    intro c c' X X'
    refine Filter.Tendsto.congr' ?_
      ((tendsto_secondDerivLimit f hl c c' X X').add (tendsto_secondDerivLimit f' hl' c c' X X'))
    filter_upwards [mixedDeriv_add_eventually hℓ hf hf' c c' X X'] with n hn
    exact hn.symm
  exact ⟨fun c c' X X' => ⟨_, key c c' X X'⟩, fun c c' X X' => (key c c' X X').limUnder_eq⟩
private theorem secondDerivLimit_smul {ℓ : StepParameters} (hℓ : ℓ.Admissible) (r : ℝ) {f : LocalDensity}
    (hf : IsAdmissibleDensity ℓ f) (hl : HasLimitSecondDeriv f) :
    HasLimitSecondDeriv (r • f) ∧
      ∀ c c' X X', secondDerivLimit (r • f) c c' X X' = r * secondDerivLimit f c c' X X' := by
  have key : ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions), Filter.Tendsto
      (fun n : ℕ => mixedDeriv ((r • f) n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (r * secondDerivLimit f c c' X X')) := by
    intro c c' X X'
    refine Filter.Tendsto.congr' ?_ ((tendsto_secondDerivLimit f hl c c' X X').const_mul r)
    filter_upwards [mixedDeriv_smul_eventually hℓ r hf c c' X X'] with n hn
    exact hn.symm
  exact ⟨fun c c' X X' => ⟨_, key c c' X X'⟩, fun c c' X X' => (key c c' X X').limUnder_eq⟩
theorem curvatureValueLinearity : curvatureValueLinearityStatement := by
  intro ℓ hℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f f' v v' hf hf' hv hv'
    obtain ⟨l, e⟩ := secondDerivLimit_add hℓ hf hf' hv.1 hv'.1
    refine ⟨l, ?_⟩
    have : limitFormTerm (f + f') unitPlaneCurvature unitPlaneCurvature =
        fun cc => limitFormTerm f unitPlaneCurvature unitPlaneCurvature cc +
          limitFormTerm f' unitPlaneCurvature unitPlaneCurvature cc := by
      funext cc
      simp only [limitFormTerm, e]
    rw [this]
    exact hv.2.add hv'.2
  · intro r f v hf hv
    obtain ⟨l, e⟩ := secondDerivLimit_smul hℓ r hf hv.1
    refine ⟨l, ?_⟩
    have : limitFormTerm (r • f) unitPlaneCurvature unitPlaneCurvature =
        fun cc => r * limitFormTerm f unitPlaneCurvature unitPlaneCurvature cc := by
      funext cc
      simp only [limitFormTerm, e]
    rw [this]
    exact hv.2.mul_left r
  · intro f f' v v' hf hf' hv hv'
    obtain ⟨l, e⟩ := secondDerivLimit_add hℓ hf hf' hv.1 hv'.1
    refine ⟨l, fun A A' hA hA' => ?_⟩
    have : limitFormTerm (f + f') A A' = fun cc => limitFormTerm f A A' cc + limitFormTerm f' A A' cc := by
      funext cc
      simp only [limitFormTerm, e]
    rw [this, add_mul]
    exact (hv.2 A A' hA hA').add (hv'.2 A A' hA hA')
  · intro r f v hf hv
    obtain ⟨l, e⟩ := secondDerivLimit_smul hℓ r hf hv.1
    refine ⟨l, fun A A' hA hA' => ?_⟩
    have : limitFormTerm (r • f) A A' = fun cc => r * limitFormTerm f A A' cc := by
      funext cc
      simp only [limitFormTerm, e]
    rw [this, mul_assoc]
    exact (hv.2 A A' hA hA').mul_left r
end YangMills.Construction.FamilyNorms
end
