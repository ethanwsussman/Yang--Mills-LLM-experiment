import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.PlainAlignment
open BlockAverages FiniteDifferences TorusFields TorusLumps TorusContours TorusPaths LineCalculus
variable {k : ℕ}
section EraseCoord
def eraseCoord (j : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun l => if l = j then 0 else ContinuousLinearMap.proj l
theorem eraseCoord_apply (j : Fin k) (t : Fin k → ℝ) : eraseCoord j t = Function.update t j 0 := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp [eraseCoord]
  · simp [eraseCoord, hl]
theorem eraseCoord_single (j : Fin k) : eraseCoord j (Pi.single j 1) = 0 := by
  rw [eraseCoord_apply]
  funext l
  by_cases hl : l = j
  · subst hl
    simp
  · simp [hl]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem eq_comp_eraseCoord {f : (Fin k → ℝ) → E} {j : Fin k} (h : ∀ t, f (Function.update t j 0) = f t) :
    f = f ∘ eraseCoord j := by
  funext t
  simp only [Function.comp, eraseCoord_apply, h]
theorem fderiv_single_eq_zero_of_update_invariant {f : (Fin k → ℝ) → E} (hf : DifferentiableAt ℝ f 0)
    (j : Fin k) (h : ∀ t, f (Function.update t j 0) = f t) : fderiv ℝ f 0 (Pi.single j 1) = 0 := by
  have hd : DifferentiableAt ℝ f (eraseCoord j 0) := by
    rw [map_zero]
    exact hf
  have e := fderiv_of_eventuallyEq_comp (f := f) (g := f) (h := eraseCoord j) (x := 0)
    (Filter.Eventually.of_forall fun t => congrFun (eq_comp_eraseCoord h) t) hd (eraseCoord j).differentiableAt
  rw [e, ContinuousLinearMap.fderiv]
  simp [eraseCoord_single]
theorem second_fderiv_eq_zero_of_update_invariant {f : (Fin k → ℝ) → E} (hf : ContDiffAt ℝ 2 f 0)
    (j : Fin k) (h : ∀ t, f (Function.update t j 0) = f t) (e e' : Fin k → ℝ)
    (he : e = Pi.single j 1 ∨ e' = Pi.single j 1) : fderiv ℝ (fderiv ℝ f) 0 e e' = 0 := by
  have hd : ContDiffAt ℝ 2 f (eraseCoord j 0) := by
    rw [map_zero]
    exact hf
  have hl : ContDiffAt ℝ 2 (eraseCoord j) (0 : Fin k → ℝ) := (eraseCoord j).contDiff.contDiffAt
  have e1 := second_fderiv_of_eventuallyEq_comp (f := f) (g := f) (h := eraseCoord j) (x := 0)
    (Filter.Eventually.of_forall fun t => congrFun (eq_comp_eraseCoord h) t) hd hl e e'
  have h1 : fderiv ℝ (eraseCoord j) = fun _ => eraseCoord j := by
    funext q
    exact (eraseCoord j).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (eraseCoord j)) 0 = 0 := by
    rw [h1]
    simp
  rw [e1, h2, h1]
  rcases he with rfl | rfl <;> simp [eraseCoord_single]
end EraseCoord
variable {n : ℕ} [NeZero n] {L : ℕ}
def plainAlignmentDefect (L : ℕ) (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion) (U : TorusField (n * L)) : ℝ :=
  alignmentDefect v (plainContourAverage L x μ U)
omit [NeZero n] in
theorem plainAlignmentDefect_perturb (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    (c : Fin k → TorusBond (n * L)) (X : Fin k → imaginaryQuaternions) (U : TorusField (n * L)) :
    (fun t => plainAlignmentDefect L x μ v (perturb c X t U)) =
      alignmentDefect v ∘ perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U := rfl
omit [NeZero n] in
theorem perturbedWordAverage_zero (x : TorusSite n) (μ : Fin 4) (c : Fin k → TorusBond (n * L))
    (X : Fin k → imaginaryQuaternions) (U : TorusField (n * L)) :
    perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U 0 =
      plainContourAverage L x μ U := by
  show wordAverage _ _ _ (perturb c X 0 U) = _
  rw [perturb_zero]
  rfl
omit [NeZero n] in
theorem contDiffThreeAt_plainAlignmentDefect (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    {U : TorusField (n * L)} (hne : plainContourAverage L x μ U ≠ 0) :
    ContDiffThreeAt (plainAlignmentDefect L x μ v) U := by
  intro k c X
  rw [plainAlignmentDefect_perturb]
  have h1 : ContDiffAt ℝ 3 (alignmentDefect v)
      (perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U 0) := by
    rw [perturbedWordAverage_zero]
    exact contDiffAt_alignmentDefect v hne
  exact h1.comp (0 : Fin k → ℝ) ((contDiff_perturbedWordAverage _ _ _ c X U).of_le le_top).contDiffAt
theorem norm_single_le_one (l : Fin k) : ‖(Pi.single l 1 : Fin k → ℝ)‖ ≤ 1 := by
  rw [Pi.norm_single]
  simp
theorem exists_mixedDeriv_plainAlignmentDefect_bound (hL : Odd L) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) [NeZero n] (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    (U : TorusField (n * L)), 1 / 2 ≤ ‖plainContourAverage L x μ U‖ →
    (∀ (c : Fin 1 → TorusBond (n * L)) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      |mixedDeriv (plainAlignmentDefect L x μ v) U c X| ≤ C) ∧
    (∀ (c : Fin 2 → TorusBond (n * L)) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |mixedDeriv (plainAlignmentDefect L x μ v) U c X| ≤ C) := by
  obtain ⟨K, hK1, hK⟩ := exists_bound_iteratedFDeriv_norm_annulus
  have hA := one_le_letterDerivBound
  set B : ℝ := (8 * letterDerivBound) ^ (5 * L) with hBdef
  refine ⟨(K + 1) * B + (K * B ^ 2 + (K + 1) * B), by positivity, fun n _ x μ v U hU => ?_⟩
  have hκ := contourWeight_nonneg L
  have hI : contourWeight L * (contourIndex L).card ≤ 1 := (contourWeight_mul_card hL).le
  have hN : ∀ e ∈ contourIndex L, (contourWord L x μ e).length ≤ 5 * L := fun e he =>
    length_contourWord_le hL x μ he
  have hq0 : ∀ {k : ℕ} (c : Fin k → TorusBond (n * L)) (X : Fin k → imaginaryQuaternions),
      ‖perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U 0‖ ≤ 2 ∧
      1 / 2 ≤ ‖perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U 0‖ := by
    intro k c X
    rw [perturbedWordAverage_zero]
    exact ⟨(norm_wordAverage_le hκ _ _ hI U).trans (by norm_num), hU⟩
  have hKB : 0 ≤ K * B ^ 2 + (K + 1) * B := by positivity
  have hK1B : 0 ≤ (K + 1) * B := by positivity
  constructor
  · intro c X hX
    have hq : ContDiffAt ℝ 2
        (perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U) 0 :=
      ((contDiff_perturbedWordAverage _ _ _ c X U).of_le le_top).contDiffAt
    have hb := norm_iteratedFDeriv_perturbedWordAverage_le hκ _ _ hI hN c X hX (by norm_num) U (j := 1)
      (by norm_num)
    have h1 := norm_fderiv_alignmentDefect_comp_le (fun p a b => (hK p a b).1) v hq (hq0 c X).2 (hq0 c X).1 hb
      (Pi.single 0 1)
    unfold mixedDeriv
    rw [plainAlignmentDefect_perturb, iteratedFDeriv_one_apply]
    have h2 := norm_single_le_one (k := 1) 0
    rw [← Real.norm_eq_abs]
    calc _ ≤ (K + 1) * B * ‖(Pi.single 0 1 : Fin 1 → ℝ)‖ := h1
      _ ≤ (K + 1) * B * 1 := mul_le_mul_of_nonneg_left h2 hK1B
      _ ≤ _ := by linarith
  · intro c X hX
    have hq : ContDiffAt ℝ 2
        (perturbedWordAverage (contourWeight L) (contourIndex L) (contourWord L x μ) c X U) 0 :=
      ((contDiff_perturbedWordAverage _ _ _ c X U).of_le le_top).contDiffAt
    have hb1 := norm_iteratedFDeriv_perturbedWordAverage_le hκ _ _ hI hN c X hX (by norm_num) U (j := 1)
      (by norm_num)
    have hb2 := norm_iteratedFDeriv_perturbedWordAverage_le hκ _ _ hI hN c X hX (by norm_num) U (j := 2)
      (by norm_num)
    have h1 := norm_second_fderiv_alignmentDefect_comp_le hK v hq (hq0 c X).2 (hq0 c X).1 hb1 hb2
      (Pi.single 0 1) (Pi.single 1 1)
    unfold mixedDeriv
    rw [plainAlignmentDefect_perturb, iteratedFDeriv_two_apply]
    have h2 := norm_single_le_one (k := 2) 0
    have h3 := norm_single_le_one (k := 2) 1
    rw [← Real.norm_eq_abs]
    have h4 : (K * B ^ 2 + (K + 1) * B) * ‖(Pi.single 0 1 : Fin 2 → ℝ)‖ * ‖(Pi.single 1 1 : Fin 2 → ℝ)‖ ≤
        (K * B ^ 2 + (K + 1) * B) * 1 * 1 := by gcongr
    calc _ ≤ _ := h1
      _ ≤ _ := h4
      _ ≤ _ := by linarith
omit [NeZero n] in
theorem plainContourAverage_congr {x : TorusSite n} {μ : Fin 4} {U U' : TorusField (n * L)}
    (h : ∀ e ∈ contourIndex L, ∀ b ∈ contourWord L x μ e, U b.1.1 b.1.2 = U' b.1.1 b.1.2) :
    plainContourAverage L x μ U = plainContourAverage L x μ U' := by
  unfold plainContourAverage wordAverage
  have h1 : ∑ e ∈ contourIndex L, ((wordHolonomy U (contourWord L x μ e) : UnitQuaternion) : ℍ[ℝ]) =
      ∑ e ∈ contourIndex L, ((wordHolonomy U' (contourWord L x μ e) : UnitQuaternion) : ℍ[ℝ]) :=
    Finset.sum_congr rfl fun e he => by rw [wordHolonomy_congr _ (h e he)]
  rw [h1]
omit [NeZero n] in
theorem plainAlignmentDefect_perturb_update (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    (c : Fin k → TorusBond (n * L)) (X : Fin k → imaginaryQuaternions) (U : TorusField (n * L)) (j : Fin k)
    (hoff : ∀ e ∈ contourIndex L, ∀ b ∈ contourWord L x μ e, c j ≠ b.1) (t : Fin k → ℝ) :
    plainAlignmentDefect L x μ v (perturb c X (Function.update t j 0) U) =
      plainAlignmentDefect L x μ v (perturb c X t U) := by
  have hm : plainContourAverage L x μ (perturb c X (Function.update t j 0) U) =
      plainContourAverage L x μ (perturb c X t U) := by
    unfold plainContourAverage wordAverage
    have h : ∑ e ∈ contourIndex L,
        ((wordHolonomy (perturb c X (Function.update t j 0) U) (contourWord L x μ e) : UnitQuaternion) : ℍ[ℝ]) =
        ∑ e ∈ contourIndex L, ((wordHolonomy (perturb c X t U) (contourWord L x μ e) : UnitQuaternion) : ℍ[ℝ]) :=
      Finset.sum_congr rfl fun e he => by rw [wordHolonomy_perturb_update c X t U _ j 0 (hoff e he)]
    rw [h]
  unfold plainAlignmentDefect
  rw [hm]
omit [NeZero n] in
theorem mixedDeriv_one_plainAlignmentDefect_eq_zero (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    (c : Fin 1 → TorusBond (n * L)) (X : Fin 1 → imaginaryQuaternions)
    {U : TorusField (n * L)} (hne : plainContourAverage L x μ U ≠ 0)
    (hoff : ∀ e ∈ contourIndex L, ∀ b ∈ contourWord L x μ e, c 0 ≠ b.1) :
    mixedDeriv (plainAlignmentDefect L x μ v) U c X = 0 := by
  have hs := contDiffThreeAt_plainAlignmentDefect (L := L) x μ v hne 1 c X
  unfold mixedDeriv
  rw [iteratedFDeriv_one_apply]
  exact fderiv_single_eq_zero_of_update_invariant (hs.differentiableAt (by norm_num)) 0
    (plainAlignmentDefect_perturb_update x μ v c X U 0 hoff)
omit [NeZero n] in
theorem mixedDeriv_two_plainAlignmentDefect_eq_zero (x : TorusSite n) (μ : Fin 4) (v : UnitQuaternion)
    (c : Fin 2 → TorusBond (n * L)) (X : Fin 2 → imaginaryQuaternions)
    {U : TorusField (n * L)} (hne : plainContourAverage L x μ U ≠ 0) (j : Fin 2)
    (hoff : ∀ e ∈ contourIndex L, ∀ b ∈ contourWord L x μ e, c j ≠ b.1) :
    mixedDeriv (plainAlignmentDefect L x μ v) U c X = 0 := by
  have hs := contDiffThreeAt_plainAlignmentDefect (L := L) x μ v hne 2 c X
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply]
  refine second_fderiv_eq_zero_of_update_invariant (hs.of_le (by norm_num)) j
    (plainAlignmentDefect_perturb_update x μ v c X U j hoff) _ _ ?_
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
end YangMills.Construction.PlainAlignment
end
