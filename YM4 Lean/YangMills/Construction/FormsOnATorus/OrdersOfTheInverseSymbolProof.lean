import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.LawOnABoxOfTheFlow.SymbolOfTheLimitForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.LimitForms
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
private def AxisJet (f : ℝ → ℂ) (t₀ ρ : ℝ) (m : ℤ) (B : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, ContDiffAt ℝ d f t₀ ∧ ‖iteratedDeriv d f t₀‖ ≤ B d * ρ ^ (m - (d : ℤ))
private theorem AxisJet.add {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B B' : ℕ → ℝ} (hf : AxisJet f t₀ ρ m B) (hg : AxisJet g t₀ ρ m B') :
    AxisJet (fun t => f t + g t) t₀ ρ m (fun d => B d + B' d) := by
  intro d
  refine ⟨(hf d).1.add (hg d).1, ?_⟩
  have : iteratedDeriv d (fun t => f t + g t) t₀ = iteratedDeriv d f t₀ + iteratedDeriv d g t₀ :=
    iteratedDeriv_add (hf d).1 (hg d).1
  rw [this, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf d).2 (hg d).2)
private theorem AxisJet.neg {f : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : AxisJet f t₀ ρ m B) :
    AxisJet (fun t => -f t) t₀ ρ m B := by
  intro d
  refine ⟨(hf d).1.neg, ?_⟩
  have : iteratedDeriv d (fun t => -f t) t₀ = -iteratedDeriv d f t₀ := by
    simpa using iteratedDeriv_neg d f t₀
  rw [this, norm_neg]
  exact (hf d).2
private def jetConvBound (B B' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * B i * B' (d - i)
private theorem AxisJet.mul {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m m' : ℤ} {B B' : ℕ → ℝ} (hρ : 0 < ρ)
    (hf : AxisJet f t₀ ρ m B) (hg : AxisJet g t₀ ρ m' B') :
    AxisJet (fun t => f t * g t) t₀ ρ (m + m') (jetConvBound B B') := by
  intro d
  refine ⟨(hf d).1.mul (hg d).1, ?_⟩
  have e : iteratedDeriv d (fun t => f t * g t) t₀ =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℂ) * iteratedDeriv i f t₀ * iteratedDeriv (d - i) g t₀ :=
    iteratedDeriv_mul (hf d).1 (hg d).1
  rw [e, jetConvBound, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have h1 := (hf i).2
  have h2 := (hg (d - i)).2
  have h3 : ρ ^ (m + m' - (d : ℤ)) = ρ ^ (m - (i : ℤ)) * ρ ^ (m' - ((d - i : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hρ.ne']
    congr 1
    have : ((d - i : ℕ) : ℤ) = d - i := by omega
    omega
  rw [h3]
  have h4 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  calc (d.choose i : ℝ) * ‖iteratedDeriv i f t₀‖ * ‖iteratedDeriv (d - i) g t₀‖
      = (d.choose i : ℝ) * (‖iteratedDeriv i f t₀‖ * ‖iteratedDeriv (d - i) g t₀‖) := by ring
    _ ≤ (d.choose i : ℝ) * (B i * ρ ^ (m - (i : ℤ)) * (B' (d - i) * ρ ^ (m' - ((d - i : ℕ) : ℤ)))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring
private theorem AxisJet.congr {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : AxisJet f t₀ ρ m B)
    (h : g =ᶠ[nhds t₀] f) : AxisJet g t₀ ρ m B := by
  intro d
  refine ⟨(hf d).1.congr_of_eventuallyEq h, ?_⟩
  rw [h.iteratedDeriv_eq]
  exact (hf d).2
private theorem AxisJet.lowerOrder {f : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hρ : 0 < ρ) (hρ7 : ρ ≤ 7) (hB : ∀ d, 0 ≤ B d)
    (hf : AxisJet f t₀ ρ (m + 1) B) : AxisJet f t₀ ρ m (fun d => 7 * B d) := by
  intro d
  refine ⟨(hf d).1, (hf d).2.trans ?_⟩
  have e : ρ ^ (m + 1 - (d : ℤ)) = ρ * ρ ^ (m - (d : ℤ)) := by
    rw [show m + 1 - (d : ℤ) = 1 + (m - d) by ring, zpow_add₀ hρ.ne', zpow_one]
  rw [e]
  have h1 : 0 ≤ ρ ^ (m - (d : ℤ)) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hρ7 h1
  have h3 := mul_le_mul_of_nonneg_left h2 (hB d)
  linarith
private theorem contDiffAt_inv_entry {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : V → Matrix (Fin 4) (Fin 4) ℂ} {x : V} {d : ℕ}
    (hA : ∀ i j, ContDiffAt ℝ d (fun t => A t i j) x) (hdet : IsUnit (A x).det) (i j : Fin 4) :
    ContDiffAt ℝ d (fun t => (A t)⁻¹ i j) x := by
  have hD : ∀ B : V → Matrix (Fin 4) (Fin 4) ℂ, (∀ i j, ContDiffAt ℝ d (fun t => B t i j) x) →
      ContDiffAt ℝ d (fun t => (B t).det) x := by
    intro B hB
    simp only [Matrix.det_apply]
    refine ContDiffAt.sum fun σ _ => ?_
    refine ContDiffAt.const_smul _ ?_
    exact contDiffAt_prod fun k _ => hB _ _
  have hdet' : (A x).det ≠ 0 := hdet.ne_zero
  have e : (fun t => (A t)⁻¹ i j) = fun t => ((A t).det)⁻¹ * (A t).adjugate i j := by
    funext t
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  refine ((hD A hA).inv hdet').mul ?_
  simp only [Matrix.adjugate_apply]
  refine hD _ fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simp only [Matrix.updateRow_ne h, Matrix.transpose_apply]
    exact hA _ _
private theorem contDiffAt_det_of_entries {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : V → Matrix (Fin 4) (Fin 4) ℂ} {x : V} {d : ℕ}
    (hB : ∀ i j, ContDiffAt ℝ d (fun t => B t i j) x) : ContDiffAt ℝ d (fun t => (B t).det) x := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  refine ContDiffAt.const_smul _ ?_
  exact contDiffAt_prod fun k _ => hB _ _
private def jetInvBound (B : ℕ → ℝ) (c₀ : ℝ) : ℕ → ℝ
  | 0 => c₀
  | d + 1 => 16 * c₀ * ∑ e : Fin (d + 1), ((d + 1).choose (e + 1) : ℝ) * B (e + 1) * jetInvBound B c₀ (d - e)
decreasing_by omega
private theorem AxisJet.inv_entry {A : ℝ → Matrix (Fin 4) (Fin 4) ℂ} {t₀ ρ c₀ : ℝ} {B : ℕ → ℝ} (hρ : 0 < ρ) (hc₀ : 0 ≤ c₀)
    (hA : ∀ i j, AxisJet (fun t => A t i j) t₀ ρ 2 B) (hdet : IsUnit (A t₀).det)
    (hN : ∀ i j, ‖(A t₀)⁻¹ i j‖ ≤ c₀ * ρ ^ (-2 : ℤ)) (i j : Fin 4) :
    AxisJet (fun t => (A t)⁻¹ i j) t₀ ρ (-2) (jetInvBound B c₀) := by
  have hsm : ∀ (d : ℕ) (i j : Fin 4), ContDiffAt ℝ d (fun t => (A t)⁻¹ i j) t₀ :=
    fun d i j => contDiffAt_inv_entry (fun a b => (hA a b d).1) hdet i j
  have hev : ∀ᶠ t in nhds t₀, IsUnit (A t).det := by
    have h1 : ContinuousAt (fun t => (A t).det) t₀ := (contDiffAt_det_of_entries (d := 0) fun a b => (hA a b 0).1).continuousAt
    filter_upwards [h1.eventually_ne hdet.ne_zero] with t ht
    exact isUnit_iff_ne_zero.2 ht
  have key : ∀ d : ℕ, ∀ a b : Fin 4,
      ‖iteratedDeriv d (fun t => (A t)⁻¹ a b) t₀‖ ≤ jetInvBound B c₀ d * ρ ^ ((-2 : ℤ) - (d : ℤ)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    cases d with
    | zero =>
      intro a b
      simpa [jetInvBound] using hN a b
    | succ d =>
      intro a b
      set nn : ℕ → Fin 4 → Fin 4 → ℂ := fun e i j => iteratedDeriv e (fun t => (A t)⁻¹ i j) t₀ with hnn
      set al : ℕ → Fin 4 → Fin 4 → ℂ := fun e i j => iteratedDeriv e (fun t => A t i j) t₀ with hal
      set S : ℝ := ∑ e ∈ Finset.range (d + 1), ((d + 1).choose (e + 1) : ℝ) * B (e + 1) * jetInvBound B c₀ (d - e) with hS
      set Rm : Matrix (Fin 4) (Fin 4) ℂ := fun i j => ∑ k, ∑ e ∈ Finset.range (d + 1),
        ((d + 1).choose (e + 1) : ℂ) * al (e + 1) i k * nn (d - e) k j with hRm
      set X : Matrix (Fin 4) (Fin 4) ℂ := fun i j => nn (d + 1) i j with hX
      have hid : A t₀ * X = -Rm := by
        ext i j
        have hconst : (fun t => ∑ k, A t i k * (A t)⁻¹ k j) =ᶠ[nhds t₀] fun _ => (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by
          filter_upwards [hev] with t ht
          rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ ht]
        have h0 : iteratedDeriv (d + 1) (fun t => ∑ k, A t i k * (A t)⁻¹ k j) t₀ = 0 := by
          rw [hconst.iteratedDeriv_eq]
          simp [iteratedDeriv_const]
        have h1 : iteratedDeriv (d + 1) (fun t => ∑ k, A t i k * (A t)⁻¹ k j) t₀ =
            ∑ k, iteratedDeriv (d + 1) (fun t => A t i k * (A t)⁻¹ k j) t₀ := by
          have := iteratedDeriv_sum (I := Finset.univ) (n := d + 1) (x := t₀) (𝕜 := ℝ)
            (f := fun k t => A t i k * (A t)⁻¹ k j) (fun k _ => (hA i k (d + 1)).1.mul (hsm (d + 1) k j))
          have e0 : (fun t => ∑ k, A t i k * (A t)⁻¹ k j) = ∑ k, fun t => A t i k * (A t)⁻¹ k j := by
            funext t
            simp [Finset.sum_apply]
          rw [e0]
          exact this
        have h2 : ∀ k, iteratedDeriv (d + 1) (fun t => A t i k * (A t)⁻¹ k j) t₀ =
            A t₀ i k * nn (d + 1) k j + ∑ e ∈ Finset.range (d + 1),
              ((d + 1).choose (e + 1) : ℂ) * al (e + 1) i k * nn (d - e) k j := by
          intro k
          have e1 : iteratedDeriv (d + 1) (fun t => A t i k * (A t)⁻¹ k j) t₀ =
              ∑ e ∈ Finset.range (d + 1 + 1), ((d + 1).choose e : ℂ) * iteratedDeriv e (fun t => A t i k) t₀ *
                iteratedDeriv (d + 1 - e) (fun t => (A t)⁻¹ k j) t₀ :=
            iteratedDeriv_mul (hA i k (d + 1)).1 (hsm (d + 1) k j)
          rw [e1, Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [hal, hnn, Nat.add_sub_add_right]
        rw [h1] at h0
        simp only [h2, Finset.sum_add_distrib] at h0
        rw [Matrix.mul_apply]
        simp only [Matrix.neg_apply, hRm, hX]
        exact eq_neg_of_add_eq_zero_left h0
      have hXe : X = -((A t₀)⁻¹ * Rm) := by
        have h1 := congrArg (fun Y => (A t₀)⁻¹ * Y) hid
        simp only [Matrix.mul_neg] at h1
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet] at h1
        exact h1
      have hRb : ∀ i j, ‖Rm i j‖ ≤ 4 * S * ρ ^ (-((d : ℤ) + 1)) := by
        intro i j
        have hin : ∀ k, ‖∑ e ∈ Finset.range (d + 1),
            ((d + 1).choose (e + 1) : ℂ) * al (e + 1) i k * nn (d - e) k j‖ ≤ S * ρ ^ (-((d : ℤ) + 1)) := by
          intro k
          rw [hS, Finset.sum_mul]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
          have he' : e ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 he)
          rw [norm_mul, norm_mul, Complex.norm_natCast]
          have b1 : ‖al (e + 1) i k‖ ≤ B (e + 1) * ρ ^ ((2 : ℤ) - ((e + 1 : ℕ) : ℤ)) := (hA i k (e + 1)).2
          have b2 : ‖nn (d - e) k j‖ ≤ jetInvBound B c₀ (d - e) * ρ ^ ((-2 : ℤ) - ((d - e : ℕ) : ℤ)) := ih (d - e) (by omega) k j
          have b3 : ρ ^ (-((d : ℤ) + 1)) = ρ ^ ((2 : ℤ) - ((e + 1 : ℕ) : ℤ)) * ρ ^ ((-2 : ℤ) - ((d - e : ℕ) : ℤ)) := by
            rw [← zpow_add₀ hρ.ne']
            congr 1
            have : ((d - e : ℕ) : ℤ) = d - e := by omega
            push_cast
            omega
          rw [b3]
          have b4 := mul_le_mul b1 b2 (norm_nonneg _) ((norm_nonneg _).trans b1)
          calc ((d + 1).choose (e + 1) : ℝ) * ‖al (e + 1) i k‖ * ‖nn (d - e) k j‖
              = ((d + 1).choose (e + 1) : ℝ) * (‖al (e + 1) i k‖ * ‖nn (d - e) k j‖) := by ring
            _ ≤ ((d + 1).choose (e + 1) : ℝ) * (B (e + 1) * ρ ^ ((2 : ℤ) - ((e + 1 : ℕ) : ℤ)) *
                  (jetInvBound B c₀ (d - e) * ρ ^ ((-2 : ℤ) - ((d - e : ℕ) : ℤ)))) :=
                mul_le_mul_of_nonneg_left b4 (by positivity)
            _ = _ := by ring
        calc ‖Rm i j‖ ≤ ∑ k : Fin 4, ‖∑ e ∈ Finset.range (d + 1),
              ((d + 1).choose (e + 1) : ℂ) * al (e + 1) i k * nn (d - e) k j‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin 4, S * ρ ^ (-((d : ℤ) + 1)) := Finset.sum_le_sum fun k _ => hin k
          _ = 4 * S * ρ ^ (-((d : ℤ) + 1)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
      have hval : nn (d + 1) a b = -∑ k, (A t₀)⁻¹ a k * Rm k b := by
        have := congrFun (congrFun hXe a) b
        simpa [Matrix.mul_apply] using this
      have hfin : ‖nn (d + 1) a b‖ ≤ 16 * c₀ * S * ρ ^ ((-2 : ℤ) - ((d + 1 : ℕ) : ℤ)) := by
        rw [hval, norm_neg]
        have b3 : ρ ^ ((-2 : ℤ) - ((d + 1 : ℕ) : ℤ)) = ρ ^ (-2 : ℤ) * ρ ^ (-((d : ℤ) + 1)) := by
          have e : ((-2 : ℤ) - ((d + 1 : ℕ) : ℤ)) = -2 + -((d : ℤ) + 1) := by
            push_cast
            ring
          rw [e, zpow_add₀ hρ.ne']
        rw [b3]
        calc ‖∑ k, (A t₀)⁻¹ a k * Rm k b‖ ≤ ∑ k : Fin 4, ‖(A t₀)⁻¹ a k * Rm k b‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin 4, (c₀ * ρ ^ (-2 : ℤ)) * (4 * S * ρ ^ (-((d : ℤ) + 1))) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul]
            exact mul_le_mul (hN a k) (hRb k b) (norm_nonneg _) (by positivity)
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
      have hinv : jetInvBound B c₀ (d + 1) = 16 * c₀ * S := by
        rw [jetInvBound, hS]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun e => ((d + 1).choose (e + 1) : ℝ) * B (e + 1) * jetInvBound B c₀ (d - e)) (d + 1)
      rw [hinv]
      exact hfin
  intro d
  exact ⟨hsm d i j, key d i j⟩
private theorem taylor_deriv_bounds {φ : ℝ → ℂ} {t₀ h A B : ℝ} (hφ : ContDiff ℝ 3 φ) (hB : ∀ t, ‖iteratedDeriv 3 φ t‖ ≤ B)
    (hh : 0 < h) (hA : ∀ u, |u| ≤ h → ‖φ (t₀ + u)‖ ≤ A) :
    ‖iteratedDeriv 1 φ t₀‖ ≤ A / h + B * h ^ 2 ∧ ‖iteratedDeriv 2 φ t₀‖ ≤ 4 * A / h ^ 2 + 2 * B * h := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have d1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have c1 : ContDiff ℝ 2 (deriv φ) := by
    have h3 : ContDiff ℝ ((2 : WithTop ℕ∞) + 1) φ := by
      have e : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
      rw [e]
      exact hφ
    exact ((contDiff_succ_iff_deriv (n := 2) (f := φ)).1 h3).2.2
  have d2 : Differentiable ℝ (deriv φ) := c1.differentiable (by norm_num)
  have c2 : ContDiff ℝ 1 (deriv (deriv φ)) := by
    have h3 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (deriv φ) := by
      have e : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
      rw [e]
      exact c1
    exact ((contDiff_succ_iff_deriv (n := 1) (f := deriv φ)).1 h3).2.2
  have d3 : Differentiable ℝ (deriv (deriv φ)) := c2.differentiable (by norm_num)
  have e1 : iteratedDeriv 1 φ = deriv φ := by simp [iteratedDeriv_eq_iterate]
  have e2 : iteratedDeriv 2 φ = deriv (deriv φ) := by simp [iteratedDeriv_eq_iterate]
  have e3 : iteratedDeriv 3 φ = deriv (deriv (deriv φ)) := by simp [iteratedDeriv_eq_iterate]
  rw [e1, e2]
  rw [e3] at hB
  set a₁ := deriv φ t₀ with ha₁
  set a₂ := deriv (deriv φ) t₀ with ha₂
  have s2 : ∀ u : ℝ, ‖deriv (deriv φ) (t₀ + u) - a₂‖ ≤ B * |u| := by
    intro u
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv φ)) (s := Set.univ) (C := B)
      (x := t₀) (y := t₀ + u) (fun x _ => d3 x) (fun x _ => hB x) convex_univ (Set.mem_univ _) (Set.mem_univ _)
    simpa using this
  have s1 : ∀ u : ℝ, ‖deriv φ (t₀ + u) - a₁ - (u : ℂ) * a₂‖ ≤ B * |u| * |u| := by
    intro u
    set g : ℝ → ℂ := fun v => deriv φ (t₀ + v) - a₁ - (v : ℂ) * a₂ with hg
    have hd : ∀ v ∈ Set.Icc (-|u|) |u|, HasDerivWithinAt g (deriv (deriv φ) (t₀ + v) - a₂) (Set.Icc (-|u|) |u|) v := by
      intro v _
      have h1 : HasDerivAt (fun v : ℝ => deriv φ (t₀ + v)) (deriv (deriv φ) (t₀ + v)) v := by
        simpa using ((d2 (t₀ + v)).hasDerivAt).comp_const_add t₀ v
      have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) * a₂) a₂ v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const a₂
      exact (((h1.sub_const a₁)).sub h2).hasDerivWithinAt
    have hb : ∀ v ∈ Set.Icc (-|u|) |u|, ‖deriv (deriv φ) (t₀ + v) - a₂‖ ≤ B * |u| := by
      intro v hv
      refine (s2 v).trans (mul_le_mul_of_nonneg_left ?_ hB0)
      exact abs_le.2 hv
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
      (x := 0) (y := u) (by simp) (by simp [neg_abs_le, le_abs_self])
    have g0 : g 0 = 0 := by simp [hg, ha₁]
    rw [g0, sub_zero, sub_zero] at this
    simpa [hg] using this
  have s0 : ∀ u : ℝ, ‖φ (t₀ + u) - φ t₀ - (u : ℂ) * a₁ - ((u : ℂ) ^ 2 / 2) * a₂‖ ≤ B * |u| * |u| * |u| := by
    intro u
    set g : ℝ → ℂ := fun v => φ (t₀ + v) - φ t₀ - (v : ℂ) * a₁ - ((v : ℂ) ^ 2 / 2) * a₂ with hg
    have hd : ∀ v ∈ Set.Icc (-|u|) |u|, HasDerivWithinAt g (deriv φ (t₀ + v) - a₁ - (v : ℂ) * a₂) (Set.Icc (-|u|) |u|) v := by
      intro v _
      have h1 : HasDerivAt (fun v : ℝ => φ (t₀ + v)) (deriv φ (t₀ + v)) v := by
        simpa using ((d1 (t₀ + v)).hasDerivAt).comp_const_add t₀ v
      have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) * a₁) a₁ v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const a₁
      have h3 : HasDerivAt (fun v : ℝ => ((v : ℂ) ^ 2 / 2) * a₂) ((v : ℂ) * a₂) v := by
        have h4 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by simpa using (hasDerivAt_id v).ofReal_comp
        have h5 := ((h4.pow 2).div_const 2).mul_const a₂
        refine h5.congr_deriv ?_
        norm_num
      exact ((h1.sub_const (φ t₀)).sub h2 |>.sub h3).hasDerivWithinAt
    have hb : ∀ v ∈ Set.Icc (-|u|) |u|, ‖deriv φ (t₀ + v) - a₁ - (v : ℂ) * a₂‖ ≤ B * |u| * |u| := by
      intro v hv
      have hv' : |v| ≤ |u| := abs_le.2 hv
      refine (s1 v).trans ?_
      have : B * |v| * |v| ≤ B * |u| * |u| := by
        have := mul_le_mul hv' hv' (abs_nonneg _) (abs_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left this hB0]
      exact this
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
      (x := 0) (y := u) (by simp) (by simp [neg_abs_le, le_abs_self])
    have g0 : g 0 = 0 := by simp [hg]
    rw [g0, sub_zero, sub_zero] at this
    simpa [hg] using this
  have habs : |h| = h := abs_of_pos hh
  have p1 := s0 h
  have p2 := s0 (-h)
  have q1 := hA h (by rw [habs])
  have q2 := hA (-h) (by rw [abs_neg, habs])
  have q0 := hA 0 (by simp [hh.le])
  rw [add_zero] at q0
  rw [abs_neg, habs] at p2
  rw [habs] at p1
  constructor
  · have e : (2 * (h : ℂ)) * a₁ = (φ (t₀ + h) - φ (t₀ + -h)) -
        ((φ (t₀ + h) - φ t₀ - (h : ℂ) * a₁ - ((h : ℂ) ^ 2 / 2) * a₂) -
          (φ (t₀ + -h) - φ t₀ - ((-h : ℝ) : ℂ) * a₁ - (((-h : ℝ) : ℂ) ^ 2 / 2) * a₂)) := by
      push_cast
      ring
    have b : ‖(2 * (h : ℂ)) * a₁‖ ≤ 2 * A + 2 * (B * h * h * h) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := norm_sub_le (φ (t₀ + h)) (φ (t₀ + -h))
      have := norm_sub_le (φ (t₀ + h) - φ t₀ - (h : ℂ) * a₁ - ((h : ℂ) ^ 2 / 2) * a₂)
        (φ (t₀ + -h) - φ t₀ - ((-h : ℝ) : ℂ) * a₁ - (((-h : ℝ) : ℂ) ^ 2 / 2) * a₂)
      linarith
    have n1 : ‖(2 * (h : ℂ)) * a₁‖ = 2 * h * ‖a₁‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
      simp
    rw [n1] at b
    have : ‖a₁‖ * (2 * h) ≤ (A / h + B * h ^ 2) * (2 * h) := by
      have e2 : (A / h + B * h ^ 2) * (2 * h) = 2 * A + 2 * (B * h * h * h) := by
        field_simp
      rw [e2]
      linarith
    exact le_of_mul_le_mul_right this (by positivity)
  · have e : ((h : ℂ) ^ 2) * a₂ = (φ (t₀ + h) + φ (t₀ + -h) - 2 * φ t₀) -
        ((φ (t₀ + h) - φ t₀ - (h : ℂ) * a₁ - ((h : ℂ) ^ 2 / 2) * a₂) +
          (φ (t₀ + -h) - φ t₀ - ((-h : ℝ) : ℂ) * a₁ - (((-h : ℝ) : ℂ) ^ 2 / 2) * a₂)) := by
      push_cast
      ring
    have b : ‖((h : ℂ) ^ 2) * a₂‖ ≤ 4 * A + 2 * (B * h * h * h) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have n2 : ‖φ (t₀ + h) + φ (t₀ + -h) - 2 * φ t₀‖ ≤ 4 * A := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_add_le (φ (t₀ + h)) (φ (t₀ + -h))
        have : ‖2 * φ t₀‖ = 2 * ‖φ t₀‖ := by simp
        linarith
      have := norm_add_le (φ (t₀ + h) - φ t₀ - (h : ℂ) * a₁ - ((h : ℂ) ^ 2 / 2) * a₂)
        (φ (t₀ + -h) - φ t₀ - ((-h : ℝ) : ℂ) * a₁ - (((-h : ℝ) : ℂ) ^ 2 / 2) * a₂)
      linarith
    have n1 : ‖((h : ℂ) ^ 2) * a₂‖ = h ^ 2 * ‖a₂‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, habs]
    rw [n1] at b
    have : ‖a₂‖ * h ^ 2 ≤ (4 * A / h ^ 2 + 2 * B * h) * h ^ 2 := by
      have e2 : (4 * A / h ^ 2 + 2 * B * h) * h ^ 2 = 4 * A + 2 * (B * h * h * h) := by
        field_simp
      rw [e2]
      linarith
    exact le_of_mul_le_mul_right this (by positivity)
private theorem two_sin_half_sq (x : ℝ) : (2 * Real.sin (x / 2)) ^ 2 = 2 - 2 * Real.cos x := by
  have h1 := Real.cos_two_mul (x / 2)
  have h2 := Real.sin_sq_add_cos_sq (x / 2)
  have e : 2 * (x / 2) = x := by ring
  rw [e] at h1
  rw [h1]
  linear_combination 4 * h2
abbrev _root_.YangMills.SharedProofs.p90038 := @two_sin_half_sq
private theorem two_sin_half_sq_le (x : ℝ) : (2 * Real.sin (x / 2)) ^ 2 ≤ x ^ 2 := by
  rw [two_sin_half_sq]
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith
private theorem sq_div_three_le_two_sin_half_sq {x : ℝ} (h1 : -Real.pi ≤ x) (h2 : x ≤ Real.pi) : x ^ 2 / 3 ≤ (2 * Real.sin (x / 2)) ^ 2 := by
  have hy0 : 0 ≤ |x| / 2 := by positivity
  have hy1 : |x| / 2 ≤ Real.pi / 2 := by
    have := abs_le.2 ⟨h1, h2⟩
    linarith
  have hs := Real.mul_le_sin hy0 hy1
  have e : Real.sin (x / 2) ^ 2 = Real.sin (|x| / 2) ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg, neg_sq]
  have h3 : (2 / Real.pi * (|x| / 2)) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  have h4 : (2 / Real.pi * (|x| / 2)) ^ 2 = x ^ 2 / Real.pi ^ 2 := by
    rw [mul_pow, div_pow, div_pow, sq_abs]
    field_simp
  have h5 : Real.pi ^ 2 ≤ 12 := by
    have := Real.pi_lt_d2
    nlinarith
  have h6 : x ^ 2 / 12 ≤ x ^ 2 / Real.pi ^ 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) h5
  rw [mul_pow, e]
  nlinarith
private theorem abs_sq_sub_two_sin_half_sq_le (x : ℝ) : |x ^ 2 - (2 * Real.sin (x / 2)) ^ 2| ≤ x ^ 4 := by
  rw [two_sin_half_sq]
  by_cases hx : |x| ≤ 1
  · have h1 := Real.cos_bound hx
    have h2 : |x| ^ 4 = x ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
    rw [h2] at h1
    have h3 : x ^ 2 - (2 - 2 * Real.cos x) = 2 * (Real.cos x - (1 - x ^ 2 / 2)) := by ring
    rw [h3, abs_mul]
    have h4 : (0 : ℝ) ≤ x ^ 4 := by positivity
    simp only [abs_two]
    linarith
  · rw [not_le] at hx
    have h1 := two_sin_half_sq_le x
    rw [two_sin_half_sq] at h1
    have h2 : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 := Real.cos_le_one x
    have h0 : 0 ≤ x ^ 2 - (2 - 2 * Real.cos x) := by linarith
    rw [abs_of_nonneg h0]
    have h4 := Real.neg_one_le_cos x
    nlinarith
private theorem sum_pow_four_le_momentumNormSq_sq (q : Fin 4 → ℝ) : ∑ l, q l ^ 4 ≤ momentumNormSq q ^ 2 := by
  simp only [momentumNormSq, sq (∑ l, q l ^ 2), Fin.sum_univ_four]
  nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3),
    mul_nonneg (sq_nonneg (q 0)) (sq_nonneg (q 1)), mul_nonneg (sq_nonneg (q 0)) (sq_nonneg (q 2)),
    mul_nonneg (sq_nonneg (q 0)) (sq_nonneg (q 3)), mul_nonneg (sq_nonneg (q 1)) (sq_nonneg (q 2)),
    mul_nonneg (sq_nonneg (q 1)) (sq_nonneg (q 3)), mul_nonneg (sq_nonneg (q 2)) (sq_nonneg (q 3))]
private theorem abs_momentumNormSq_sub_latticeSineNormSq_le (q : Fin 4 → ℝ) :
    |momentumNormSq q - latticeSineNormSq q| ≤ momentumNormSq q ^ 2 := by
  have e : momentumNormSq q - latticeSineNormSq q = ∑ l, (q l ^ 2 - (2 * Real.sin (q l / 2)) ^ 2) := by
    simp only [momentumNormSq, latticeSineNormSq, latticeSine, Finset.sum_sub_distrib]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun l _ => abs_sq_sub_two_sin_half_sq_le (q l)).trans (sum_pow_four_le_momentumNormSq_sq q))
private theorem latticeSineNormSq_le (q : Fin 4 → ℝ) : latticeSineNormSq q ≤ momentumNormSq q :=
  Finset.sum_le_sum fun l _ => two_sin_half_sq_le (q l)
private theorem momentumNormSq_div_three_le {q : Fin 4 → ℝ} (hq : q ∈ brillouinBox) : momentumNormSq q / 3 ≤ latticeSineNormSq q := by
  have h : ∀ l, q l ^ 2 / 3 ≤ latticeSine q l ^ 2 := fun l => sq_div_three_le_two_sin_half_sq (hq.1 l) (hq.2 l)
  have := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h l
  simp only [momentumNormSq, latticeSineNormSq, ← Finset.sum_div] at this ⊢
  exact this
private theorem latticeSineNormSq_nonneg (q : Fin 4 → ℝ) : 0 ≤ latticeSineNormSq q := Finset.sum_nonneg fun _ _ => sq_nonneg _
private def trigComb (b c t : ℝ) : ℂ := ((b * Real.cos t + c * Real.sin t : ℝ) : ℂ)
private theorem trigComb_hasDerivAt (b c t : ℝ) : HasDerivAt (trigComb b c) (trigComb c (-b) t) t := by
  have h1 : HasDerivAt (fun t : ℝ => b * Real.cos t + c * Real.sin t) (c * Real.cos t + -b * Real.sin t) t := by
    have := ((Real.hasDerivAt_cos t).const_mul b).add ((Real.hasDerivAt_sin t).const_mul c)
    refine this.congr_deriv ?_
    ring
  exact h1.ofReal_comp
private theorem trigComb_contDiff (b c : ℝ) : ContDiff ℝ ⊤ (trigComb b c) := by
  unfold trigComb
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin))
private theorem norm_trigComb_le (b c t : ℝ) : ‖trigComb b c t‖ ≤ |b| + |c| := by
  simp only [trigComb, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one t)
private theorem iteratedDeriv_trigComb (d : ℕ) : ∀ b c : ℝ, ∃ b' c' : ℝ, |b'| + |c'| = |b| + |c| ∧ iteratedDeriv d (trigComb b c) = trigComb b' c' := by
  induction d with
  | zero => exact fun b c => ⟨b, c, rfl, by simp⟩
  | succ d ih =>
    intro b c
    obtain ⟨b', c', h1, h2⟩ := ih c (-b)
    refine ⟨b', c', ?_, ?_⟩
    · rw [h1, abs_neg, add_comm]
    · rw [iteratedDeriv_succ']
      have : deriv (trigComb b c) = trigComb c (-b) := funext fun t => (trigComb_hasDerivAt b c t).deriv
      rw [this, h2]
private def sineNormSqLine (p : Fin 4 → ℝ) (l : Fin 4) (t : ℝ) : ℂ := (latticeSineNormSq (Function.update p l t) : ℂ)
private theorem sineNormSqLine_eq (p : Fin 4 → ℝ) (l : Fin 4) :
    ∃ a : ℂ, sineNormSqLine p l = fun t => a + trigComb (-2) 0 t := by
  refine ⟨((∑ l' ∈ Finset.univ.erase l, latticeSine p l' ^ 2 + 2 : ℝ) : ℂ), ?_⟩
  funext t
  have h1 : latticeSineNormSq (Function.update p l t) = latticeSine (Function.update p l t) l ^ 2 +
      ∑ l' ∈ Finset.univ.erase l, latticeSine (Function.update p l t) l' ^ 2 :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ l)).symm
  have h2 : latticeSine (Function.update p l t) l ^ 2 = 2 - 2 * Real.cos t := by
    simp only [latticeSine, Function.update_self]
    exact two_sin_half_sq t
  have h3 : ∑ l' ∈ Finset.univ.erase l, latticeSine (Function.update p l t) l' ^ 2 =
      ∑ l' ∈ Finset.univ.erase l, latticeSine p l' ^ 2 := by
    refine Finset.sum_congr rfl fun l' hl' => ?_
    have : l' ≠ l := (Finset.mem_erase.1 hl').1
    simp only [latticeSine, Function.update_of_ne this]
  simp only [sineNormSqLine, trigComb]
  rw [h1, h2, h3]
  push_cast
  ring
private theorem sineNormSqLine_contDiff (p : Fin 4 → ℝ) (l : Fin 4) : ContDiff ℝ ⊤ (sineNormSqLine p l) := by
  obtain ⟨a, ha⟩ := sineNormSqLine_eq p l
  rw [ha]
  exact contDiff_const.add (trigComb_contDiff _ _)
private theorem deriv_sineNormSqLine (p : Fin 4 → ℝ) (l : Fin 4) : deriv (sineNormSqLine p l) = trigComb 0 2 := by
  obtain ⟨a, ha⟩ := sineNormSqLine_eq p l
  rw [ha]
  funext t
  have := (trigComb_hasDerivAt (-2) 0 t).const_add a
  rw [this.deriv]
  simp [trigComb]
private theorem norm_iteratedDeriv_sineNormSqLine_le (p : Fin 4 → ℝ) (l : Fin 4) (d : ℕ) (t : ℝ) :
    ‖iteratedDeriv (d + 1) (sineNormSqLine p l) t‖ ≤ 2 := by
  rw [iteratedDeriv_succ', deriv_sineNormSqLine]
  obtain ⟨b', c', h1, h2⟩ := iteratedDeriv_trigComb d 0 2
  rw [h2]
  refine (norm_trigComb_le _ _ _).trans ?_
  rw [h1]
  simp
private theorem one_le_seven_pow_mul_inv {ρ : ℝ} (hρ : 0 < ρ) (hρ7 : ρ ≤ 7) (k : ℕ) : 1 ≤ 7 ^ k * (ρ ^ k)⁻¹ := by apply _root_.YangMills.SharedProofs.p22065 <;> assumption
private theorem remainder_axisJet {f : ℝ → ℂ} {U : ℕ → ℝ} {C₃ ρ t₀ : ℝ} (hρ : 0 < ρ) (hρ7 : ρ ≤ 7) (hC₃ : 0 ≤ C₃)
    (hsm : ContDiff ℝ ⊤ f) (hU : ∀ d t, ‖iteratedDeriv (d + 1) f t‖ ≤ U d)
    (h0 : ‖f t₀‖ ≤ C₃ * ρ ^ 4)
    (hsz : ρ < 1 → ∀ u, |u| ≤ ρ → ‖f (t₀ + u)‖ ≤ C₃ * (2 * ρ) ^ 4) :
    AxisJet f t₀ ρ 3 (fun d => 7 * C₃ + (16 * C₃ + U 2) + (64 * C₃ + 2 * U 2) + U 0 + U 1 + 7 ^ d * (if d = 0 then 0 else U (d - 1))) := by
  have hU0 : ∀ d, 0 ≤ U d := fun d => (norm_nonneg _).trans (hU d 0)
  intro d
  refine ⟨hsm.contDiffAt.of_le (by exact_mod_cast le_top), ?_⟩
  set B : ℕ → ℝ := fun d => 7 * C₃ + (16 * C₃ + U 2) + (64 * C₃ + 2 * U 2) + U 0 + U 1 + 7 ^ d * (if d = 0 then 0 else U (d - 1)) with hB
  have hBge : ∀ d, 0 ≤ 7 ^ d * (if d = 0 then (0 : ℝ) else U (d - 1)) := by
    intro d
    split_ifs
    · simp
    · exact mul_nonneg (by positivity) (hU0 _)
  by_cases d0 : d = 0
  · subst d0
    simp only [iteratedDeriv_zero]
    refine h0.trans ?_
    have e : ρ ^ ((3 : ℤ) - ((0 : ℕ) : ℤ)) = ρ ^ 3 := by
      norm_num
    rw [e]
    have h1 : C₃ * ρ ^ 4 ≤ 7 * C₃ * ρ ^ 3 := by
      have h2 : ρ ^ 4 = ρ * ρ ^ 3 := by ring
      rw [h2]
      have h3 : (0 : ℝ) ≤ ρ ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hρ7 h3]
    have h4 : 7 * C₃ ≤ B 0 := by
      have := hU0 0
      have := hU0 1
      have := hU0 2
      have hb0 : B 0 = 7 * C₃ + (16 * C₃ + U 2) + (64 * C₃ + 2 * U 2) + U 0 + U 1 := by simp [hB]
      rw [hb0]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
  by_cases hbig : 3 ≤ d
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
    have hd := hU (k + 2) (t₀)
    have h1 : ‖iteratedDeriv (k + 3) f t₀‖ ≤ U (k + 2) := hd
    have e : ρ ^ ((3 : ℤ) - ((k + 3 : ℕ) : ℤ)) = (ρ ^ k)⁻¹ := by
      have : ((3 : ℤ) - ((k + 3 : ℕ) : ℤ)) = -(k : ℤ) := by push_cast; ring
      rw [this, zpow_neg, zpow_natCast]
    rw [e]
    have h2 := one_le_seven_pow_mul_inv hρ hρ7 k
    have h3 : U (k + 2) ≤ 7 ^ (k + 3) * U (k + 2) * (ρ ^ k)⁻¹ := by
      have h5 : (7 : ℝ) ^ k ≤ 7 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h6 : 0 ≤ (ρ ^ k)⁻¹ := by positivity
      have h7 : 1 ≤ 7 ^ (k + 3) * (ρ ^ k)⁻¹ := h2.trans (mul_le_mul_of_nonneg_right h5 h6)
      have := mul_le_mul_of_nonneg_right h7 (hU0 (k + 2))
      linarith
    refine h1.trans (h3.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    simp only [hB]
    have : (if k + 3 = 0 then (0 : ℝ) else U (k + 3 - 1)) = U (k + 2) := by simp
    rw [this]
    have := hU0 0
    have := hU0 1
    have := hU0 2
    linarith
  have hc3 : ContDiff ℝ 3 f := hsm.of_le (by exact_mod_cast le_top)
  by_cases hone : 1 ≤ ρ
  · have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · have h1 := hU 0 t₀
      have e : ρ ^ ((3 : ℤ) - ((1 : ℕ) : ℤ)) = ρ ^ 2 := by norm_num
      rw [e]
      refine h1.trans ?_
      have h2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hone
      have h3 : U 0 ≤ B 1 := by
        have := hU0 1
        have := hU0 2
        have := hBge 1
        simp only [hB]
        linarith
      calc U 0 ≤ B 1 := h3
        _ ≤ B 1 * ρ ^ 2 := le_mul_of_one_le_right ((hU0 0).trans h3) h2
    · have h1 := hU 1 t₀
      have e : ρ ^ ((3 : ℤ) - ((2 : ℕ) : ℤ)) = ρ := by norm_num
      rw [e]
      refine h1.trans ?_
      have h3 : U 1 ≤ B 2 := by
        have := hU0 0
        have := hU0 2
        have := hBge 2
        simp only [hB]
        linarith
      calc U 1 ≤ B 2 := h3
        _ ≤ B 2 * ρ := le_mul_of_one_le_right ((hU0 1).trans h3) hone
  · rw [not_le] at hone
    have ht := taylor_deriv_bounds (t₀ := t₀) (h := ρ) (A := C₃ * (2 * ρ) ^ 4) (B := U 2) hc3 (fun t => hU 2 t) hρ (hsz hone)
    have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · have e : ρ ^ ((3 : ℤ) - ((1 : ℕ) : ℤ)) = ρ ^ 2 := by norm_num
      rw [e]
      refine ht.1.trans ?_
      have e2 : C₃ * (2 * ρ) ^ 4 / ρ + U 2 * ρ ^ 2 = (16 * C₃ * ρ + U 2) * ρ ^ 2 := by
        field_simp
        ring
      rw [e2]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h2 : 16 * C₃ * ρ ≤ 16 * C₃ := by nlinarith
      have := hU0 0
      have := hU0 1
      have := hU0 2
      have := hBge 1
      simp only [hB]
      linarith
    · have e : ρ ^ ((3 : ℤ) - ((2 : ℕ) : ℤ)) = ρ := by norm_num
      rw [e]
      refine ht.2.trans ?_
      have e2 : 4 * (C₃ * (2 * ρ) ^ 4) / ρ ^ 2 + 2 * U 2 * ρ = (64 * C₃ * ρ + 2 * U 2) * ρ := by
        field_simp
        ring
      rw [e2]
      refine mul_le_mul_of_nonneg_right ?_ hρ.le
      have h2 : 64 * C₃ * ρ ≤ 64 * C₃ := by nlinarith
      have := hU0 0
      have := hU0 1
      have := hU0 2
      have := hBge 2
      simp only [hB]
      linarith
private theorem inverse_bounds_of_coercive {M : Matrix (Fin 4) (Fin 4) ℂ} {a : ℝ} (ha : 0 < a)
    (hlow : ∀ ξ : Fin 4 → ℂ, a * ∑ i, ‖ξ i‖ ^ 2 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * M i j * ξ j).re) :
    IsUnit M.det ∧ ∀ i j, ‖M⁻¹ i j‖ ≤ a⁻¹ := by
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := hlow v
    have h2 : ∑ i, ∑ j, (starRingEnd ℂ) (v i) * M i j * v j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have h3 := congrFun hMv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h3
      simp only [mul_assoc]
      rw [← Finset.mul_sum, h3, mul_zero]
    rw [h2] at h1
    simp only [Complex.zero_re] at h1
    have h4 : ∑ i, ‖v i‖ ^ 2 ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      have := mul_pos ha hc
      linarith
    have h5 : ∑ i, ‖v i‖ ^ 2 = 0 := le_antisymm h4 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    apply hv
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 h5 i (Finset.mem_univ i)
    simpa using this
  refine ⟨hdet, fun i j => ?_⟩
  set ξ : Fin 4 → ℂ := fun k => M⁻¹ k j with hξ
  have hMξ : ∀ r, ∑ c, M r c * ξ c = if r = j then 1 else 0 := by
    intro r
    have := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) r) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have h1 := hlow ξ
  have h2 : ∑ r, ∑ c, (starRingEnd ℂ) (ξ r) * M r c * ξ c = (starRingEnd ℂ) (ξ j) := by
    have : ∀ r, ∑ c, (starRingEnd ℂ) (ξ r) * M r c * ξ c = (starRingEnd ℂ) (ξ r) * (if r = j then 1 else 0) := by
      intro r
      rw [← hMξ r, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [this]
    simp
  rw [h2] at h1
  set s := Real.sqrt (∑ k, ‖ξ k‖ ^ 2) with hs
  have hs2 : s ^ 2 = ∑ k, ‖ξ k‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hle : ∀ k, ‖ξ k‖ ≤ s := by
    intro k
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun k => ‖ξ k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have h3 : ((starRingEnd ℂ) (ξ j)).re ≤ s := by
    refine (Complex.re_le_norm _).trans ?_
    rw [RCLike.norm_conj]
    exact hle j
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h4 : a * s ^ 2 ≤ s := by rw [hs2]; linarith
  have h5 : s ≤ a⁻¹ := by
    by_cases h0 : s = 0
    · rw [h0]; positivity
    · have hp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      have h6 : a * s ≤ 1 := by
        have : a * s * s ≤ 1 * s := by nlinarith
        exact le_of_mul_le_mul_right this hp
      rw [← one_div, le_div_iff₀ ha]
      linarith
  exact (hle i).trans h5
private theorem sqrt_momentumNormSq_le_seven {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) : Real.sqrt (momentumNormSq p) ≤ 7 := by apply _root_.YangMills.SharedProofs.p34260 <;> assumption
private theorem sqrt_momentumNormSq_pos {p : Fin 4 → ℝ} (hp : p ≠ 0) : 0 < Real.sqrt (momentumNormSq p) := by apply _root_.YangMills.SharedProofs.p65178 <;> assumption
private theorem abs_le_sqrt_momentumNormSq (p : Fin 4 → ℝ) (l : Fin 4) : |p l| ≤ Real.sqrt (momentumNormSq p) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem momentumNormSq_update_le (p : Fin 4 → ℝ) (l : Fin 4) {u : ℝ} (hu : |u| ≤ Real.sqrt (momentumNormSq p)) :
    momentumNormSq (Function.update p l (p l + u)) ≤ 4 * momentumNormSq p := by
  have h1 : momentumNormSq (Function.update p l (p l + u)) = momentumNormSq p + 2 * p l * u + u ^ 2 := by
    simp only [momentumNormSq]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ l), ← Finset.add_sum_erase Finset.univ (fun l => p l ^ 2) (Finset.mem_univ l)]
    have : ∑ l' ∈ Finset.univ.erase l, Function.update p l (p l + u) l' ^ 2 = ∑ l' ∈ Finset.univ.erase l, p l' ^ 2 := by
      refine Finset.sum_congr rfl fun l' hl' => ?_
      rw [Function.update_of_ne (Finset.mem_erase.1 hl').1]
    rw [this, Function.update_self]
    ring
  have h0 : 0 ≤ momentumNormSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs := Real.sq_sqrt h0
  set ρ := Real.sqrt (momentumNormSq p)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have h2 := abs_le_sqrt_momentumNormSq p l
  have h3 : 2 * p l * u ≤ 2 * ρ * ρ := by
    have := mul_le_mul h2 hu (abs_nonneg _) hρ0
    have h4 := le_abs_self (p l * u)
    rw [abs_mul] at h4
    nlinarith
  have h4 : u ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  rw [h1]
  nlinarith
private theorem update_mem_brillouinBox {p : Fin 4 → ℝ} (l : Fin 4) {u : ℝ} (h1 : Real.sqrt (momentumNormSq p) < 1)
    (hu : |u| ≤ Real.sqrt (momentumNormSq p)) : Function.update p l (p l + u) ∈ brillouinBox := by
  have hpi := Real.pi_gt_three
  have hc : ∀ l', |p l'| < 1 := fun l' => (abs_le_sqrt_momentumNormSq p l').trans_lt h1
  constructor <;> intro l' <;> by_cases h : l' = l
  · subst h
    have := abs_lt.1 (hc l')
    have := abs_le.1 hu
    simp only [Function.update_self]
    linarith [(abs_lt.1 (hc l')).1, (abs_le.1 hu).1]
  · have := abs_lt.1 (hc l')
    simp only [Function.update_of_ne h]
    linarith [this.1]
  · subst h
    simp only [Function.update_self]
    linarith [(abs_lt.1 (hc l')).2, (abs_le.1 hu).2]
  · have := abs_lt.1 (hc l')
    simp only [Function.update_of_ne h]
    linarith [this.2]
private def diagSineLine (p : Fin 4 → ℝ) (l i j : Fin 4) (t : ℝ) : ℂ := if i = j then sineNormSqLine p l t else 0
private theorem sineNormSqLine_axisJet {p : Fin 4 → ℝ} (l : Fin 4) (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    AxisJet (sineNormSqLine p l) (p l) (Real.sqrt (momentumNormSq p)) 2 (fun d => 3 * 7 ^ d) := by
  have hρ := sqrt_momentumNormSq_pos hp0
  have hρ7 := sqrt_momentumNormSq_le_seven hp
  set ρ := Real.sqrt (momentumNormSq p) with hρd
  intro d
  refine ⟨(sineNormSqLine_contDiff p l).contDiffAt.of_le (by exact_mod_cast le_top), ?_⟩
  match d with
  | 0 =>
    have h0 : 0 ≤ momentumNormSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs : ρ ^ 2 = momentumNormSq p := Real.sq_sqrt h0
    have e : ρ ^ ((2 : ℤ) - ((0 : ℕ) : ℤ)) = ρ ^ 2 := by norm_num
    rw [e, iteratedDeriv_zero]
    simp only [sineNormSqLine, Function.update_eq_self, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (latticeSineNormSq_nonneg p)]
    have := latticeSineNormSq_le p
    have h2 : 0 ≤ ρ ^ 2 := by positivity
    norm_num
    linarith
  | 1 =>
    have e : ρ ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = ρ := by norm_num
    rw [e]
    have e2 : iteratedDeriv 1 (sineNormSqLine p l) = deriv (sineNormSqLine p l) := by simp [iteratedDeriv_eq_iterate]
    rw [e2, deriv_sineNormSqLine]
    simp only [trigComb, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |0 * Real.cos (p l) + 2 * Real.sin (p l)| ≤ 2 * |p l| := by
      rw [zero_mul, zero_add, abs_mul]
      have := Real.abs_sin_le_abs (x := p l)
      simp only [abs_two]
      linarith
    have h2 : |p l| ≤ ρ := abs_le_sqrt_momentumNormSq p l
    refine h1.trans ?_
    norm_num
    linarith
  | k + 2 =>
    have e : ρ ^ ((2 : ℤ) - ((k + 2 : ℕ) : ℤ)) = (ρ ^ k)⁻¹ := by
      have : ((2 : ℤ) - ((k + 2 : ℕ) : ℤ)) = -(k : ℤ) := by push_cast; ring
      rw [this, zpow_neg, zpow_natCast]
    rw [e]
    refine (norm_iteratedDeriv_sineNormSqLine_le p l (k + 1) _).trans ?_
    have h2 := one_le_seven_pow_mul_inv hρ hρ7 k
    have h5 : (7 : ℝ) ^ k ≤ 7 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h6 : 0 ≤ (ρ ^ k)⁻¹ := by positivity
    have h7 := mul_le_mul_of_nonneg_right h5 h6
    nlinarith
private theorem diagSineLine_axisJet {p : Fin 4 → ℝ} (l i j : Fin 4) (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    AxisJet (diagSineLine p l i j) (p l) (Real.sqrt (momentumNormSq p)) 2 (fun d => 3 * 7 ^ d) := by
  by_cases h : i = j
  · have : diagSineLine p l i j = sineNormSqLine p l := by
      funext t
      simp [diagSineLine, h]
    rw [this]
    exact sineNormSqLine_axisJet l hp hp0
  · have : diagSineLine p l i j = fun _ => 0 := by
      funext t
      simp [diagSineLine, h]
    rw [this]
    intro d
    refine ⟨contDiffAt_const, ?_⟩
    have hρ := sqrt_momentumNormSq_pos hp0
    rw [iteratedDeriv_const]
    simp only [ite_self, norm_zero]
    have := zpow_pos hρ ((2 : ℤ) - (d : ℤ))
    positivity
private theorem inv_smul_one_matrix {s : ℂ} (hs : s ≠ 0) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℂ))⁻¹ = s⁻¹ • 1 := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hs]
  simp
private theorem isUnit_det_smul_one {s : ℂ} (hs : s ≠ 0) : IsUnit (s • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, isUnit_iff_ne_zero]
  exact pow_ne_zero _ hs
set_option maxHeartbeats 4000000 in
private theorem inverseSymbol_orders_core (Tb : RenormalizationStepParameters.ParameterAssignment)
    (hS : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ c C : ℝ, 0 < c ∧ ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q →
      (∀ (i j : Fin 4) (p : Fin 4 → ℝ), AnalyticAt ℝ (midpointSymbol Q i j) p) ∧
      (∀ (p : Fin 4 → ℝ) (ξ : Fin 4 → ℂ), p ∈ brillouinBox →
        c * momentumNormSq p * ∑ i, ‖ξ i‖ ^ 2 ≤
          (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * midpointSymbol Q i j p * ξ j).re) ∧
      ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox →
        ‖midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0)‖ ≤ C * momentumNormSq p ^ 2)
    (hB : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ D : ℕ → ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q →
      (∀ (i j l : Fin 4) (d : ℕ) (p : Fin 4 → ℝ),
        ‖iteratedDeriv d (fun t : ℝ => midpointSymbol Q i j (Function.update p l t)) (p l)‖ ≤ D d) ∧
      (∀ (i j : Fin 4) (p : Fin 4 → ℝ), (midpointSymbol Q i j p).im = 0) ∧
      (∀ (i j : Fin 4) (p : Fin 4 → ℝ), midpointSymbol Q i j p = midpointSymbol Q j i p) ∧
      ∀ (i : Fin 4) (p : Fin 4 → ℝ),
        ∑ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
          ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = 0) :
    ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ Cs : ℕ → ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
    IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      IsUnit (momentumSymbolMatrix Q p).det ∧
      (∀ d : ℕ, ContDiffAt ℝ d (fun q => (momentumSymbolMatrix Q q)⁻¹ i j) p) ∧
      ∀ (l : Fin 4) (d : ℕ),
        ‖iteratedDeriv d (fun t : ℝ => (momentumSymbolMatrix Q (Function.update p l t))⁻¹ i j) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-2 - (d : ℤ)) ∧
        ‖iteratedDeriv d (fun t : ℝ => inverseSymbolDefect Q i j (Function.update p l t)) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-1 - (d : ℤ)) := by
  intro c₁ C₁ hc₁
  obtain ⟨c, C, hc, hS'⟩ := hS c₁ C₁ hc₁
  obtain ⟨D, hD⟩ := hB c₁ C₁ hc₁
  set C₃ : ℝ := |C| + 1 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  set U : ℕ → ℝ := fun d => D (d + 1) + 2 with hU
  set BE : ℕ → ℝ := fun d => 7 * C₃ + (16 * C₃ + U 2) + (64 * C₃ + 2 * U 2) + U 0 + U 1 + 7 ^ d * (if d = 0 then 0 else U (d - 1)) with hBE
  set BM : ℕ → ℝ := fun d => 7 * BE d + 3 * 7 ^ d with hBM
  set BN : ℕ → ℝ := jetInvBound BM c⁻¹ with hBN
  set BS : ℕ → ℝ := jetInvBound (fun d => 3 * 7 ^ d) 3 with hBS
  set BC : ℕ → ℝ := jetConvBound BN BE with hBC
  set BD : ℕ → ℝ := jetConvBound BS (fun d => BC d + BC d + BC d + BC d) with hBD
  refine ⟨fun d => |BN d| + |BD d|, fun k Q hQ i j p hp hp0 => ?_⟩
  obtain ⟨han, hlow, hup⟩ := hS' k Q hQ
  obtain ⟨hder, -, -, -⟩ := hD k Q hQ
  have hρ := sqrt_momentumNormSq_pos hp0
  have hρ7 := sqrt_momentumNormSq_le_seven hp
  have hms0 : 0 ≤ momentumNormSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Real.sqrt (momentumNormSq p) ^ 2 = momentumNormSq p := Real.sq_sqrt hms0
  set ρ := Real.sqrt (momentumNormSq p) with hρd
  have hlowM : ∀ q : Fin 4 → ℝ, q ∈ brillouinBox → q ≠ 0 → IsUnit (momentumSymbolMatrix Q q).det := by
    intro q hq hq0
    have hm : 0 < momentumNormSq q := by
      have := sqrt_momentumNormSq_pos hq0
      exact Real.sqrt_pos.1 this
    exact (inverse_bounds_of_coercive (a := c * momentumNormSq q) (by positivity) (fun ξ => hlow q ξ hq)).1
  have hNp : ∀ a b, ‖(momentumSymbolMatrix Q p)⁻¹ a b‖ ≤ c⁻¹ * ρ ^ (-2 : ℤ) := by
    intro a b
    have hm : 0 < momentumNormSq p := by rw [← hsq]; positivity
    have h1 := (inverse_bounds_of_coercive (a := c * momentumNormSq p) (by positivity) (fun ξ => hlow p ξ hp)).2 a b
    refine h1.trans (le_of_eq ?_)
    rw [mul_inv, ← hsq, zpow_neg]
    norm_cast
  have hdetp := hlowM p hp hp0
  have hsmooth : ∀ d : ℕ, ContDiffAt ℝ d (fun q => (momentumSymbolMatrix Q q)⁻¹ i j) p :=
    fun d => contDiffAt_inv_entry (fun a b => (han a b p).contDiffAt) hdetp i j
  refine ⟨hdetp, hsmooth, fun l d => ?_⟩
  have hD0 : ∀ d, 0 ≤ D d := fun d => (norm_nonneg _).trans (hder 0 0 0 d 0)
  have hU0 : ∀ d, 0 ≤ U d := fun d => by
    have := hD0 (d + 1)
    simp only [hU]
    linarith
  have hBE0 : ∀ d, 0 ≤ BE d := by
    intro d
    have a0 := hU0 0
    have a1 := hU0 1
    have a2 := hU0 2
    have a3 : 0 ≤ 7 ^ d * (if d = 0 then (0 : ℝ) else U (d - 1)) := by
      split_ifs
      · simp
      · exact mul_nonneg (by positivity) (hU0 _)
    simp only [hBE]
    linarith
  set t₀ := p l with ht₀
  set A : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun t => momentumSymbolMatrix Q (Function.update p l t) with hA
  have hAt₀ : A t₀ = momentumSymbolMatrix Q p := by simp [hA, ht₀]
  set sL : Fin 4 → Fin 4 → ℝ → ℂ := fun a b t => midpointSymbol Q a b (Function.update p l t) with hsL
  have hsmL : ∀ a b, ContDiff ℝ ⊤ (sL a b) := by
    intro a b
    refine contDiff_iff_contDiffAt.2 fun t => ?_
    have h1 : ContDiffAt ℝ ⊤ (midpointSymbol Q a b) (Function.update p l t) := (han a b _).contDiffAt
    have h2 : ContDiffAt ℝ ⊤ (fun t : ℝ => Function.update p l t) t := (contDiff_update ⊤ p l).contDiffAt
    exact h1.comp t h2
  have hdsm : ∀ a b, ContDiff ℝ ⊤ (diagSineLine p l a b) := by
    intro a b
    by_cases h : a = b
    · have : diagSineLine p l a b = sineNormSqLine p l := by
        funext t
        simp [diagSineLine, h]
      rw [this]
      exact sineNormSqLine_contDiff p l
    · have : diagSineLine p l a b = fun _ => 0 := by
        funext t
        simp [diagSineLine, h]
      rw [this]
      exact contDiff_const
  set E : Fin 4 → Fin 4 → ℝ → ℂ := fun a b t => sL a b t - diagSineLine p l a b t with hE
  have hEsm : ∀ a b, ContDiff ℝ ⊤ (E a b) := fun a b => (hsmL a b).sub (hdsm a b)
  have hEU : ∀ a b d t, ‖iteratedDeriv (d + 1) (E a b) t‖ ≤ U d := by
    intro a b d t
    have h1 : iteratedDeriv (d + 1) (E a b) t = iteratedDeriv (d + 1) (sL a b) t - iteratedDeriv (d + 1) (diagSineLine p l a b) t :=
      iteratedDeriv_sub ((hsmL a b).contDiffAt.of_le (by exact_mod_cast le_top))
        ((hdsm a b).contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖iteratedDeriv (d + 1) (sL a b) t‖ ≤ D (d + 1) := by
      have := hder a b l (d + 1) (Function.update p l t)
      simpa [hsL, Function.update_idem] using this
    have h3 : ‖iteratedDeriv (d + 1) (diagSineLine p l a b) t‖ ≤ 2 := by
      by_cases h : a = b
      · have : diagSineLine p l a b = sineNormSqLine p l := by
          funext t
          simp [diagSineLine, h]
        rw [this]
        exact norm_iteratedDeriv_sineNormSqLine_le p l d t
      · have : diagSineLine p l a b = fun _ => 0 := by
          funext t
          simp [diagSineLine, h]
        rw [this, iteratedDeriv_const]
        simp
    simp only [hU]
    linarith
  have hEbd : ∀ (q : Fin 4 → ℝ), q ∈ brillouinBox → ∀ a b,
      ‖midpointSymbol Q a b q - (if a = b then (latticeSineNormSq q : ℂ) else 0)‖ ≤ C₃ * momentumNormSq q ^ 2 := by
    intro q hq a b
    have h1 := hup a b q hq
    have hm : 0 ≤ momentumNormSq q ^ 2 := by positivity
    have hCC : C * momentumNormSq q ^ 2 ≤ |C| * momentumNormSq q ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) hm
    by_cases h : a = b
    · simp only [h, if_true] at h1 ⊢
      have h2 : ‖((momentumNormSq q - latticeSineNormSq q : ℝ) : ℂ)‖ ≤ momentumNormSq q ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_momentumNormSq_sub_latticeSineNormSq_le q
      have e : midpointSymbol Q b b q - (latticeSineNormSq q : ℂ) =
          (midpointSymbol Q b b q - (momentumNormSq q : ℂ)) + ((momentumNormSq q - latticeSineNormSq q : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      simp only [hC₃]
      linarith
    · simp only [h, if_false] at h1 ⊢
      simp only [hC₃]
      linarith
  have hEq : ∀ a b t, E a b t = midpointSymbol Q a b (Function.update p l t) -
      (if a = b then (latticeSineNormSq (Function.update p l t) : ℂ) else 0) := by
    intro a b t
    simp only [hE, hsL, diagSineLine, sineNormSqLine]
  have hρ4 : ρ ^ 4 = momentumNormSq p ^ 2 := by
    rw [← hsq]
    ring
  have hE0 : ∀ a b, ‖E a b t₀‖ ≤ C₃ * ρ ^ 4 := by
    intro a b
    rw [hEq]
    have : Function.update p l t₀ = p := by simp [ht₀]
    rw [this, hρ4]
    exact hEbd p hp a b
  have hEsz : ∀ a b, ρ < 1 → ∀ u, |u| ≤ ρ → ‖E a b (t₀ + u)‖ ≤ C₃ * (2 * ρ) ^ 4 := by
    intro a b h1 u hu
    rw [hEq]
    have hq := update_mem_brillouinBox l h1 hu
    have hb := hEbd _ hq a b
    have hm := momentumNormSq_update_le p l hu
    have hm0 : 0 ≤ momentumNormSq (Function.update p l (p l + u)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : momentumNormSq (Function.update p l (p l + u)) ^ 2 ≤ (2 * ρ) ^ 4 := by
      have e : (2 * ρ) ^ 4 = (4 * momentumNormSq p) ^ 2 := by
        rw [← hsq]
        ring
      rw [e]
      exact pow_le_pow_left₀ hm0 hm 2
    exact hb.trans (mul_le_mul_of_nonneg_left h2 hC₃0)
  have JE : ∀ a b, AxisJet (E a b) t₀ ρ 3 BE := fun a b =>
    remainder_axisJet hρ hρ7 hC₃0 (hEsm a b) (hEU a b) (hE0 a b) (hEsz a b)
  have JM : ∀ a b, AxisJet (fun t => A t a b) t₀ ρ 2 BM := by
    intro a b
    have h1 := ((JE a b).lowerOrder (m := 2) hρ hρ7 hBE0).add (diagSineLine_axisJet l a b hp hp0)
    refine AxisJet.congr h1 (Filter.Eventually.of_forall fun t => ?_)
    simp [hE, hsL, hA, momentumSymbolMatrix]
  have JN : ∀ a b, AxisJet (fun t => (A t)⁻¹ a b) t₀ ρ (-2) BN := fun a b =>
    AxisJet.inv_entry hρ (inv_nonneg.2 hc.le) JM (by rw [hAt₀]; exact hdetp) (fun a b => by rw [hAt₀]; exact hNp a b) a b
  set s : ℝ → ℂ := sineNormSqLine p l with hs
  have hsin : momentumNormSq p / 3 ≤ latticeSineNormSq p := momentumNormSq_div_three_le hp
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hsinpos : 0 < latticeSineNormSq p := by
    rw [← hsq] at hsin
    linarith [div_pos hρ2 (by norm_num : (0 : ℝ) < 3)]
  have hst₀ : s t₀ = (latticeSineNormSq p : ℂ) := by simp [hs, sineNormSqLine, ht₀]
  have hs0 : s t₀ ≠ 0 := by
    rw [hst₀]
    exact_mod_cast hsinpos.ne'
  have JA' : ∀ a b, AxisJet (fun t => (s t • (1 : Matrix (Fin 4) (Fin 4) ℂ)) a b) t₀ ρ 2 (fun d => 3 * 7 ^ d) := by
    intro a b
    refine AxisJet.congr (diagSineLine_axisJet l a b hp hp0) (Filter.Eventually.of_forall fun t => ?_)
    simp [diagSineLine, hs, Matrix.one_apply]
  have hN' : ∀ a b, ‖(s t₀ • (1 : Matrix (Fin 4) (Fin 4) ℂ))⁻¹ a b‖ ≤ 3 * ρ ^ (-2 : ℤ) := by
    intro a b
    rw [inv_smul_one_matrix hs0, hst₀]
    have h1 : ‖((latticeSineNormSq p : ℂ))⁻¹‖ ≤ 3 * ρ ^ (-2 : ℤ) := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsinpos, zpow_neg]
      have h2 : ρ ^ 2 / 3 ≤ latticeSineNormSq p := by rw [hsq]; exact hsin
      have h3 : (latticeSineNormSq p)⁻¹ ≤ (ρ ^ 2 / 3)⁻¹ := inv_anti₀ (by positivity) h2
      refine h3.trans (le_of_eq ?_)
      norm_cast
      field_simp
    by_cases h : a = b
    · simpa [Matrix.one_apply, h] using h1
    · simp only [Matrix.smul_apply, Matrix.one_apply, h, if_false, smul_zero, norm_zero]
      positivity
  have JS₀ := AxisJet.inv_entry hρ (by norm_num : (0 : ℝ) ≤ 3) JA' (isUnit_det_smul_one hs0) hN' 0 0
  have hscont : ContinuousAt s t₀ := (sineNormSqLine_contDiff p l).continuous.continuousAt
  have hsev : ∀ᶠ t in nhds t₀, s t ≠ 0 := hscont.eventually_ne hs0
  have JS : AxisJet (fun t => (s t)⁻¹) t₀ ρ (-2) BS := by
    refine AxisJet.congr JS₀ ?_
    filter_upwards [hsev] with t ht
    rw [inv_smul_one_matrix ht]
    simp
  have J1 : ∀ a, AxisJet (fun t => (A t)⁻¹ i a * E a j t) t₀ ρ (-2 + 3) BC := fun a => (JN i a).mul hρ (JE a j)
  have Jsum := (((J1 0).add (J1 1)).add (J1 2)).add (J1 3)
  have JD0 := (JS.mul hρ Jsum).neg
  have hdet_ev : ∀ᶠ t in nhds t₀, IsUnit (A t).det := by
    have h1 : ContinuousAt (fun t => (A t).det) t₀ := (contDiffAt_det_of_entries (d := 0) fun a b => (JM a b 0).1).continuousAt
    have h2 : (A t₀).det ≠ 0 := by
      rw [hAt₀]
      exact hdetp.ne_zero
    filter_upwards [h1.eventually_ne h2] with t ht
    exact isUnit_iff_ne_zero.2 ht
  have JD : AxisJet (fun t => inverseSymbolDefect Q i j (Function.update p l t)) t₀ ρ (-2 + (-2 + 3)) BD := by
    refine AxisJet.congr JD0 ?_
    filter_upwards [hsev, hdet_ev] with t ht hdt
    have h1 : ∑ a, (A t)⁻¹ i a * A t a j = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hdt]
    have h2 : ∑ a, (A t)⁻¹ i a * diagSineLine p l a j t = (A t)⁻¹ i j * s t := by
      simp [diagSineLine, hs]
    have h3 : ∑ a, (A t)⁻¹ i a * E a j t = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j - (A t)⁻¹ i j * s t := by
      rw [← h1, ← h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hE, hsL, hA, momentumSymbolMatrix]
      ring
    rw [Fin.sum_univ_four] at h3
    rw [h3]
    simp only [inverseSymbolDefect]
    have e : (latticeSineNormSq (Function.update p l t) : ℂ) = s t := rfl
    have eA : momentumSymbolMatrix Q (Function.update p l t) = A t := rfl
    rw [e, eA]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, if_true]
      field_simp
      ring
    · simp only [hij, Matrix.one_apply_ne (show i ≠ j from hij), if_false]
      field_simp
      ring
  have hnn : 0 < ρ ^ ((-2 : ℤ) - (d : ℤ)) := zpow_pos hρ _
  have hnn' : 0 < ρ ^ ((-1 : ℤ) - (d : ℤ)) := zpow_pos hρ _
  constructor
  · refine (JN i j d).2.trans (mul_le_mul_of_nonneg_right ?_ hnn.le)
    have := le_abs_self (BN d)
    have := abs_nonneg (BD d)
    linarith
  · have h1 := (JD d).2
    have e : ((-2 : ℤ) + (-2 + 3)) = -1 := by norm_num
    rw [e] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hnn'.le)
    have := le_abs_self (BD d)
    have := abs_nonneg (BN d)
    linarith
theorem inverseSymbolOrders_of_symbol_bounds (h1 : limitFormSymbolStatement) (h2 : symbolDerivBoundsStatement) :
    inverseSymbolOrdersStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h1 a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h2 a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL T hTa hTL hD hrt
  obtain ⟨y₁, G₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLL) T hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, G₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hLL) T hTa hTL hD (hrt.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, fun y hy hret hrow => ?_⟩
  exact inverseSymbol_orders_core T (G₁ y (le_trans (le_max_left _ _) hy) hret hrow) (G₂ y (le_trans (le_max_right _ _) hy) hret hrow)
end YangMills.Construction.LimitForms
end
