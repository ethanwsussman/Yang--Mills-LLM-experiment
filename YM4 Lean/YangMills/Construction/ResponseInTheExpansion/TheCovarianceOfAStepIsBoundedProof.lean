import YangMills.Construction.ResponseInTheExpansion.TheCovarianceOfAStepIsBounded
import YangMills.Construction.ResponseInTheExpansion.TheHessianOfAStepHasAFloor
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames TorusFields StepCosts WeightedResponses
section Algebra
private theorem abs_dotProduct_inv_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ)
    (hH : H.PosDef) {lam : ℝ} (hlam : 0 < lam)
    (hfloor : ∀ v : ι → ℝ, lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ H.mulVec v) (l l' : ι → ℝ) :
    |l ⬝ᵥ H⁻¹.mulVec l'| ≤ lam⁻¹ * (∑ b, |l b|) * ∑ b, |l' b| := by
  obtain ⟨w, hw⟩ : ∃ w, w = H⁻¹.mulVec l' := ⟨_, rfl⟩
  rw [← hw]
  have hunit : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit
  have hHw : H.mulVec w = l' := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  obtain ⟨S, hS⟩ : ∃ S, S = Real.sqrt (∑ b, w b ^ 2) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ Real.sqrt_nonneg _
  have hSS : S ^ 2 = ∑ b, w b ^ 2 := by
    rw [hS]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hwS : ∀ b, |w b| ≤ S := by
    intro b
    rw [hS]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun b => w b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have hdot : ∀ m : ι → ℝ, |m ⬝ᵥ w| ≤ (∑ b, |m b|) * S := by
    intro m
    unfold dotProduct
    calc |∑ b, m b * w b| ≤ ∑ b, |m b * w b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, |m b| * S := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hwS b) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hfl := hfloor w
  rw [hHw] at hfl
  have hA : 0 ≤ ∑ b, |l' b| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : lam * S ^ 2 ≤ (∑ b, |l' b|) * S := by
    rw [hSS]
    calc lam * ∑ b, w b ^ 2 ≤ w ⬝ᵥ l' := hfl
      _ = l' ⬝ᵥ w := dotProduct_comm _ _
      _ ≤ |l' ⬝ᵥ w| := le_abs_self _
      _ ≤ _ := hdot l'
  have h2 : lam * S ≤ ∑ b, |l' b| := by
    rcases hS0.eq_or_lt with h | h
    · rw [← h, mul_zero]
      exact hA
    · have h3 : (lam * S) * S ≤ (∑ b, |l' b|) * S := by nlinarith
      exact le_of_mul_le_mul_right h3 h
  have h3 : S ≤ lam⁻¹ * ∑ b, |l' b| := by
    rw [inv_mul_eq_div, le_div_iff₀ hlam]
    linarith
  calc |l ⬝ᵥ w| ≤ (∑ b, |l b|) * S := hdot l
    _ ≤ (∑ b, |l b|) * (lam⁻¹ * ∑ b, |l' b|) :=
      mul_le_mul_of_nonneg_left h3 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by ring
private theorem sum_abs_sum_ite_le {γ δ : Type*} [Fintype γ] (s : Finset δ) (f : γ → δ)
    [∀ (c : γ) (b : δ), Decidable (f c = b)] (h : γ → ℝ) :
    ∑ b : ↥s, |∑ c, if f c = b.1 then h c else 0| ≤ ∑ c, |h c| := by
  calc ∑ b : ↥s, |∑ c, if f c = b.1 then h c else 0|
      ≤ ∑ b : ↥s, ∑ c, |if f c = b.1 then h c else 0| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, ∑ b : ↥s, |if f c = b.1 then h c else 0| := Finset.sum_comm
    _ ≤ ∑ c, |h c| := by
      refine Finset.sum_le_sum fun c _ => ?_
      by_cases hc : f c ∈ s
      · rw [Finset.sum_eq_single (⟨f c, hc⟩ : ↥s)]
        · simp
        · intro b _ hb
          have hne : f c ≠ b.1 := fun e => hb (Subtype.ext e.symm)
          simp [hne]
        · simp
      · have hne : ∀ b : ↥s, f c ≠ b.1 := fun b e => hc (e ▸ b.2)
        simp [hne, abs_nonneg]
end Algebra
private theorem abs_stepCovariance_le {a : ℝ} {L u n : ℕ} [NeZero L] [NeZero n] {lam : ℝ} (hlam : 0 < lam)
    (hP : (trivialHessian a L u n).PosDef)
    (hfloor : ∀ v : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ,
      lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian a L u n).mulVec v)
    (h h' : TorusBond (n * L) → ℝ) :
    |stepCovariance a L u n h h'| ≤ lam⁻¹ * (∑ b, |h b|) * ∑ b, |h' b| := by
  dsimp only [stepCovariance]
  refine (abs_dotProduct_inv_mulVec_le _ hP hlam hfloor _ _).trans ?_
  have hinv : 0 ≤ lam⁻¹ := (inv_pos.2 hlam).le
  have e1 := sum_abs_sum_ite_le (chordBonds (finiteCells (torusFrame L u n)))
    (fun c : TorusBond (n * L) => (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2)) h
  have e2 := sum_abs_sum_ite_le (chordBonds (finiteCells (torusFrame L u n)))
    (fun c : TorusBond (n * L) => (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2)) h'
  exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hinv) e2 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg hinv (Finset.sum_nonneg fun _ _ => abs_nonneg _))
theorem stepCovarianceBounded (hF : stepHessianLowerBoundStatement) :
    stepCovarianceBoundedStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hL⟩ := hF a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hodd hL₀ T hTa hTL hD hC hO hrt' hC₀ => ?_⟩
  obtain ⟨y₀, hy⟩ := hL L hodd hL₀ T hTa hTL hD hC hO hrt' hC₀
  refine ⟨y₀, fun y h1 h2 h3 => ?_⟩
  obtain ⟨lam, hlam, hH⟩ := hy y h1 h2 h3
  refine ⟨lam⁻¹, fun u n _ h h' hn _ => ?_⟩
  obtain ⟨hP, hfloor⟩ := hH u n hn
  exact abs_stepCovariance_le hlam hP hfloor h h'
end YangMills.Construction.ResponseInTheExpansion
end
