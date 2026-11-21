import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.LawInAState.TheAxialLogIsTheCirculation
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CurvatureKernel
open TorusFields TorusLumps AxialForms LatticeSums StateLaw AxialLogarithm ResponseInTheExpansion BlockAverages BoxForm
variable {n : ℕ}
def axialFormCoeff (z : TorusSite n) (c : LatticeBond) (p : TorusPlaquette n) : ℝ :=
  axialForm (fun a μ ν => if ((z + siteOfInt a, μ, ν) : TorusPlaquette n) = p then 1 else 0) c
def curvatureKernel (u : TorusField n → ℝ) (z : TorusSite n) (m : ℕ) (p p' : TorusPlaquette n) : ℝ :=
  ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian u (bondFrom z c) (bondFrom z c') *
    (axialFormCoeff z c p * axialFormCoeff z c' p')
theorem intervalSum_finset_sum {ι : Type*} (T : Finset ι) (m : ℤ) (F : ι → ℤ → ℝ) :
    intervalSum m (fun j => ∑ p ∈ T, F p j) = ∑ p ∈ T, intervalSum m (F p) := by
  have h := intervalSum_eq_sub (fun m => ∑ p ∈ T, intervalSum m (F p)) (fun j => ∑ p ∈ T, F p j)
    (fun m => by simp only [intervalSum_succ, Finset.sum_add_distrib]) m
  simpa [intervalSum_zero] using h
theorem intervalSum_eq_zero {m : ℤ} {F : ℤ → ℝ} (h : ∀ j, |j| ≤ |m| → F j = 0) : intervalSum m F = 0 := by
  have := abs_intervalSum_le m F 0 (fun j hj => by rw [h j hj, abs_zero])
  simpa using this
theorem intervalSum_congr {m : ℤ} {F G : ℤ → ℝ} (h : ∀ j, |j| ≤ |m| → F j = G j) :
    intervalSum m F = intervalSum m G := by
  have h1 := intervalSum_sub m F G
  rw [intervalSum_eq_zero (fun j hj => sub_eq_zero.2 (h j hj))] at h1
  linarith
theorem offsetSupNorm_truncate_le (a : Fin 4 → ℤ) (ν : Fin 4) {j : ℤ} (hj : |j| ≤ |a ν|) :
    offsetSupNorm (truncate a ν j) ≤ offsetSupNorm a := by
  refine Finset.sup_le fun i _ => ?_
  have hi := natAbs_le_offsetSupNorm a i
  have hv := natAbs_le_offsetSupNorm a ν
  simp only [truncate]
  split_ifs with h1 h2
  · exact hi
  · have : j.natAbs ≤ (a ν).natAbs := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hj
      exact_mod_cast hj
    omega
  · simp
theorem abs_axialForm_le {D : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ} {c : LatticeBond} {t : ℝ}
    (h : ∀ ν, c.2 < ν → ∀ j, |j| ≤ |c.1 ν| → |D (truncate c.1 ν j) c.2 ν| ≤ t) (ht : 0 ≤ t) :
    |axialForm D c| ≤ 4 * offsetSupNorm c.1 * t := by
  unfold axialForm
  rw [abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin 4, (offsetSupNorm c.1 : ℝ) * t := Finset.sum_le_sum fun l _ => by
        split_ifs with hl
        · refine (abs_intervalSum_le _ _ t fun j hj => h l hl j hj).trans ?_
          have := abs_le_offsetSupNorm c.1 l
          gcongr
        · simp only [abs_zero]
          positivity
    _ = _ := by
      simp
      ring
theorem axialForm_eq_sum_coeff [NeZero n] (z : TorusSite n) (c : LatticeBond) (T : Finset (TorusPlaquette n))
    (D : TorusPlaquette n → ℝ)
    (hT : ∀ ν, c.2 < ν → ∀ j, |j| ≤ |c.1 ν| → ((z + siteOfInt (truncate c.1 ν j), c.2, ν) : TorusPlaquette n) ∈ T) :
    axialForm (fun a μ ν => D (z + siteOfInt a, μ, ν)) c = ∑ p ∈ T, axialFormCoeff z c p * D p := by
  unfold axialFormCoeff axialForm
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hν : c.2 < ν
  · simp only [hν, if_true]
    have e1 : intervalSum (c.1 ν) (fun j => D (z + siteOfInt (truncate c.1 ν j), c.2, ν)) =
        intervalSum (c.1 ν) (fun j => ∑ p ∈ T, D p *
          (if ((z + siteOfInt (truncate c.1 ν j), c.2, ν) : TorusPlaquette n) = p then 1 else 0)) := by
      refine intervalSum_congr fun j hj => ?_
      simp [hT ν hν j hj]
    rw [e1, intervalSum_finset_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalSum_const_mul, mul_comm]
  · simp [hν]
theorem abs_axialFormCoeff_le [NeZero n] (z : TorusSite n) (c : LatticeBond) (p : TorusPlaquette n) :
    |axialFormCoeff z c p| ≤ 4 * offsetSupNorm c.1 := by
  have := abs_axialForm_le
    (D := fun a μ ν => if ((z + siteOfInt a, μ, ν) : TorusPlaquette n) = p then 1 else 0) (c := c) (t := 1)
    (fun ν _ j _ => by split_ifs <;> simp) zero_le_one
  simpa [axialFormCoeff] using this
theorem axialFormCoeff_eq_zero_of_lt [NeZero n] (z : TorusSite n) (c : LatticeBond) (p : TorusPlaquette n)
    (h : offsetSupNorm c.1 < supDist p.1 z) :
    axialFormCoeff z c p = 0 := by
  unfold axialFormCoeff axialForm
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun ν _ => ?_
  split_ifs
  · refine intervalSum_eq_zero fun j hj => if_neg ?_
    intro e
    have e1 : z + siteOfInt (truncate c.1 ν j) = p.1 := congrArg Prod.fst e
    have h1 := LatticeSums.supDist_add_siteOfInt_le z (truncate c.1 ν j)
    have h2 := offsetSupNorm_truncate_le c.1 ν hj
    rw [e1] at h1
    omega
  · rfl
def bondPairWeight (r : ℝ) (cc : LatticeBond × LatticeBond) : ℝ :=
  (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 *
    Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ)))
theorem sum_bondPairWeight_le {r : ℝ} (hr : 0 < r) (s : Finset (LatticeBond × LatticeBond)) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ cc ∈ s, P ≤ max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ)) :
    ∑ cc ∈ s, bondPairWeight r cc ≤ bondWeightSum (r / 4) 3 ^ 2 * Real.exp (-(r / 2 * P)) := by
  set g : LatticeBond → ℝ := fun c =>
    (1 + (offsetSupNorm c.1 : ℝ)) ^ 3 * Real.exp (-(r / 4) * offsetSupNorm c.1) with hg
  have hg0 : ∀ c, 0 ≤ g c := fun c => by positivity
  have h1 : ∀ cc ∈ s, bondPairWeight r cc ≤ Real.exp (-(r / 2 * P)) * (g cc.1 * g cc.2) := by
    intro cc hcc
    have hb := hP cc hcc
    have e1 : Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ))) ≤
        Real.exp (-(r / 2 * P)) * (Real.exp (-(r / 4) * offsetSupNorm cc.1.1) *
          Real.exp (-(r / 4) * offsetSupNorm cc.2.1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have m1 := le_max_left (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ)
      have m2 := le_max_right (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ)
      nlinarith
    unfold bondPairWeight
    calc _ ≤ (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 *
          (Real.exp (-(r / 2 * P)) *
          (Real.exp (-(r / 4) * offsetSupNorm cc.1.1) * Real.exp (-(r / 4) * offsetSupNorm cc.2.1))) := by gcongr
      _ = _ := by
        simp only [hg]
        ring
  have hr4 : 0 < r / 4 := by positivity
  have h2 : ∑ cc ∈ s, g cc.1 * g cc.2 ≤ bondWeightSum (r / 4) 3 ^ 2 := by
    have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := fun cc hcc =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hcc, Finset.mem_image_of_mem _ hcc⟩
    calc _ ≤ ∑ cc ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd), g cc.1 * g cc.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun cc _ _ => mul_nonneg (hg0 _) (hg0 _)
      _ = (∑ c ∈ s.image Prod.fst, g c) * ∑ c ∈ s.image Prod.snd, g c := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ bondWeightSum (r / 4) 3 * bondWeightSum (r / 4) 3 :=
          mul_le_mul (sum_le_bondWeightSum hr4 3 _) (sum_le_bondWeightSum hr4 3 _)
            (Finset.sum_nonneg fun _ _ => hg0 _) (bondWeightSum_nonneg _ _)
      _ = _ := by ring
  calc _ ≤ ∑ cc ∈ s, Real.exp (-(r / 2 * P)) * (g cc.1 * g cc.2) := Finset.sum_le_sum h1
    _ = Real.exp (-(r / 2 * P)) * ∑ cc ∈ s, g cc.1 * g cc.2 := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(r / 2 * P)) * bondWeightSum (r / 4) 3 ^ 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring
theorem sum_kernel_form_eq {ι κ : Type*} (T : Finset ι) (s : Finset κ) (Q : κ → κ → ℝ) (A : κ → ι → ℝ)
    (x : ι → ℝ) :
    ∑ p ∈ T, ∑ p' ∈ T, (∑ c ∈ s, ∑ c' ∈ s, Q c c' * (A c p * A c' p')) * (x p * x p') =
      ∑ c ∈ s, ∑ c' ∈ s, Q c c' * ((∑ p ∈ T, A c p * x p) * ∑ p' ∈ T, A c' p' * x p') := by
  have e : ∀ c c', Q c c' * ((∑ p ∈ T, A c p * x p) * ∑ p' ∈ T, A c' p' * x p') =
      ∑ p ∈ T, ∑ p' ∈ T, Q c c' * (A c p * A c' p') * (x p * x p') := by
    intro c c'
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => e c c']
  simp only [Finset.sum_mul]
  calc _ = ∑ p ∈ T, ∑ c ∈ s, ∑ p' ∈ T, ∑ c' ∈ s, Q c c' * (A c p * A c' p') * (x p * x p') :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ c ∈ s, ∑ p ∈ T, ∑ p' ∈ T, ∑ c' ∈ s, Q c c' * (A c p * A c' p') * (x p * x p') := Finset.sum_comm
    _ = ∑ c ∈ s, ∑ p ∈ T, ∑ c' ∈ s, ∑ p' ∈ T, Q c c' * (A c p * A c' p') * (x p * x p') :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm
def curvatureKernelExpansionStatement : Prop :=
  ∀ σ E E₃ r : ℝ, 0 < σ → 0 ≤ E → 0 ≤ E₃ → 0 < r → ∃ C c : ℝ, 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (w : ℕ → ℝ) (u : TorusField n → ℝ), 16 ≤ n →
      (∀ m : ℕ, Real.exp (r * m) ≤ w m) →
      IsRegularObservable σ E E₃ w z u →
      (∀ (W W' : TorusField n) (m : ℕ), IsCold σ W → IsCold σ W' → 2 * m + 2 < n → FieldsAgreeNear W W' z z m →
        |u W - u W'| ≤ E / w m) →
      (∀ p p', curvatureKernel u z (n / 4) p p' = curvatureKernel u z (n / 4) p' p) ∧
      (∀ p p', |curvatureKernel u z (n / 4) p p'| ≤
        C * Real.exp (-(c * max (supDist p.1 z : ℝ) (supDist p'.1 z : ℝ)))) ∧
      ∀ (W : TorusField n) (g : TorusSite n → UnitQuaternion) (v : TorusBond n → imaginaryQuaternions)
        (ρ s t : ℝ), IsCold σ W → 1 ≤ ρ → 4 * ρ + 4 ≤ n →
        0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → IsSmallOnBall W g v z ρ s t →
        |u W - u (trivialField n) - (1 / 2) * ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ),
            curvatureKernel u z (n / 4) p p' *
              ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')| ≤
          C * (t ^ 3 + t * s ^ 2 + Real.exp (-(c * ρ)))
end YangMills.Construction.CurvatureKernel
end
