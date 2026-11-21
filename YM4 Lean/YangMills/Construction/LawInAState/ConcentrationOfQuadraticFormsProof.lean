import YangMills.Construction.LawInAState.ConcentrationOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace YangMills.Construction
open WickMoments
namespace QuadraticConcentration
section Coefficients
variable {ι : Type} [Fintype ι]
private lemma sum_fin_succ_cons_eq {n : ℕ} (G : (Fin (n + 1) → ι) → ℝ) :
    ∑ i, G i = ∑ a : ι, ∑ j : Fin n → ι, G (Fin.cons a j) := by
  refine Eq.trans ?_ (Fintype.sum_prod_type' (f := fun a j => G (Fin.cons a j)))
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => ι)) _ _ (fun x => rfl)).symm
private lemma sum_fun_fin_one (G : ι → ℝ) : ∑ i : Fin 1 → ι, G (i 0) = ∑ a, G a := by
  rw [sum_fin_succ_cons_eq]; simp
private lemma sum_fun_fin_two (G : ι → ι → ℝ) : ∑ i : Fin 2 → ι, G (i 0) (i 1) = ∑ a, ∑ b, G a b := by
  rw [sum_fin_succ_cons_eq]
  exact Finset.sum_congr rfl fun a _ => sum_fun_fin_one (G a)
private lemma sum_fun_fin_three (G : ι → ι → ι → ℝ) :
    ∑ i : Fin 3 → ι, G (i 0) (i 1) (i 2) = ∑ a, ∑ b, ∑ c, G a b c := by
  rw [sum_fin_succ_cons_eq]
  exact Finset.sum_congr rfl fun a _ => sum_fun_fin_two (G a)
private lemma sum_fun_fin_four (G : ι → ι → ι → ι → ℝ) :
    ∑ i : Fin 4 → ι, G (i 0) (i 1) (i 2) (i 3) = ∑ a, ∑ b, ∑ c, ∑ d, G a b c d := by
  rw [sum_fin_succ_cons_eq]
  exact Finset.sum_congr rfl fun a _ => sum_fun_fin_three (G a)
private def wickCoefficient {q : ℕ} (C : ι → ι → ℝ) (ξ : ι → ℝ) (i : Fin q → ι) : ℝ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin q))).filter (fun σ => σ * σ = 1),
    (-1 : ℝ) ^ (Finset.univ.filter fun a : Fin q => a < σ a).card *
      ((∏ a ∈ Finset.univ.filter (fun a : Fin q => a < σ a), C (i a) (i (σ a))) *
        ∏ a ∈ Finset.univ.filter (fun a : Fin q => σ a = a), ξ (i a))
private lemma wickPolynomial_eq_sum_coefficient {q : ℕ} (C : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C A ξ = ∑ i, A i * wickCoefficient C ξ i := by
  unfold wickPolynomial wickCoefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private lemma involutions_fin_one : (Finset.univ.filter fun σ : Equiv.Perm (Fin 1) => σ * σ = 1) = {1} := by
  decide +kernel
private lemma involutions_fin_two : (Finset.univ.filter fun σ : Equiv.Perm (Fin 2) => σ * σ = 1) =
    {1, Equiv.swap 0 1} := by
  decide +kernel
private lemma involutions_fin_three : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ * σ = 1) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} := by
  decide +kernel
private lemma involutions_fin_four : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) => σ * σ = 1) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 1 2, Equiv.swap 1 3,
      Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
      Equiv.swap 0 3 * Equiv.swap 1 2} := by
  decide +kernel
private lemma wickCoefficient_fin_one (C : ι → ι → ℝ) (ξ : ι → ℝ) (i : Fin 1 → ι) :
    wickCoefficient C ξ i = ξ (i 0) := by
  unfold wickCoefficient
  rw [involutions_fin_one, Finset.sum_singleton]
  rw [show (Finset.univ.filter fun a : Fin 1 => a < (1 : Equiv.Perm (Fin 1)) a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 1 => (1 : Equiv.Perm (Fin 1)) a = a) = {0} by decide +kernel]
  simp
private lemma wickCoefficient_fin_two (C : ι → ι → ℝ) (ξ : ι → ℝ) (i : Fin 2 → ι) :
    wickCoefficient C ξ i = ξ (i 0) * ξ (i 1) - C (i 0) (i 1) := by
  unfold wickCoefficient
  rw [involutions_fin_two, Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  simp only [
    show (Finset.univ.filter fun a : Fin 2 => a < (1 : Equiv.Perm (Fin 2)) a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 2 => (1 : Equiv.Perm (Fin 2)) a = a) = {0, 1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 2 => a < (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 2 => (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) a = a) = ∅ by decide +kernel]
  simp [Equiv.swap_apply_def]
  ring
private lemma wickCoefficient_fin_three (C : ι → ι → ℝ) (ξ : ι → ℝ) (i : Fin 3 → ι) :
    wickCoefficient C ξ i = ξ (i 0) * ξ (i 1) * ξ (i 2) - C (i 0) (i 1) * ξ (i 2) -
      C (i 0) (i 2) * ξ (i 1) - C (i 1) (i 2) * ξ (i 0) := by
  unfold wickCoefficient
  rw [involutions_fin_three, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  simp only [
    show (Finset.univ.filter fun a : Fin 3 => a < (1 : Equiv.Perm (Fin 3)) a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => (1 : Equiv.Perm (Fin 3)) a = a) = {0, 1, 2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => a < (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) a = a) = {2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => a < (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) a = a) = {1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => a < (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) a) = {1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 3 => (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) a = a) = {0} by decide +kernel]
  simp [Equiv.swap_apply_def]
  ring
private lemma wickCoefficient_fin_four (C : ι → ι → ℝ) (ξ : ι → ℝ) (i : Fin 4 → ι) :
    wickCoefficient C ξ i = ξ (i 0) * ξ (i 1) * ξ (i 2) * ξ (i 3) - C (i 0) (i 1) * ξ (i 2) * ξ (i 3) -
      C (i 0) (i 2) * ξ (i 1) * ξ (i 3) - C (i 0) (i 3) * ξ (i 1) * ξ (i 2) -
      C (i 1) (i 2) * ξ (i 0) * ξ (i 3) - C (i 1) (i 3) * ξ (i 0) * ξ (i 2) -
      C (i 2) (i 3) * ξ (i 0) * ξ (i 1) + C (i 0) (i 1) * C (i 2) (i 3) +
      C (i 0) (i 2) * C (i 1) (i 3) + C (i 0) (i 3) * C (i 1) (i 2) := by
  unfold wickCoefficient
  rw [involutions_fin_four]
  repeat rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_singleton]
  simp only [
    show (Finset.univ.filter fun a : Fin 4 => a < (1 : Equiv.Perm (Fin 4)) a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (1 : Equiv.Perm (Fin 4)) a = a) = {0, 1, 2, 3} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 1 : Equiv.Perm (Fin 4)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 1 : Equiv.Perm (Fin 4)) a = a) = {2, 3} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 2 : Equiv.Perm (Fin 4)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 2 : Equiv.Perm (Fin 4)) a = a) = {1, 3} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 3 : Equiv.Perm (Fin 4)) a) = {0} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 3 : Equiv.Perm (Fin 4)) a = a) = {1, 2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 1 2 : Equiv.Perm (Fin 4)) a) = {1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 1 2 : Equiv.Perm (Fin 4)) a = a) = {0, 3} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 1 3 : Equiv.Perm (Fin 4)) a) = {1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 1 3 : Equiv.Perm (Fin 4)) a = a) = {0, 2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 2 3 : Equiv.Perm (Fin 4)) a) = {2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 2 3 : Equiv.Perm (Fin 4)) a = a) = {0, 1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) a) = {0, 2} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) a = a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) a) = {0, 1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) a = a) = ∅ by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => a < (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) a) = {0, 1} by decide +kernel,
    show (Finset.univ.filter fun a : Fin 4 => (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) a = a) = ∅ by decide +kernel]
  simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply]
  ring
end Coefficients
section WickAlgebra
variable {ι : Type} [Fintype ι]
private lemma wickPolynomial_rank_one (C : ι → ι → ℝ) (g ξ : ι → ℝ) :
    wickPolynomial C (fun i : Fin 1 → ι => g (i 0)) ξ = ∑ a, g a * ξ a := by
  rw [wickPolynomial_eq_sum_coefficient]
  simp only [wickCoefficient_fin_one]
  exact sum_fun_fin_one (fun a => g a * ξ a)
private lemma wickPolynomial_rank_two (C : ι → ι → ℝ) (T : ι → ι → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C (fun i : Fin 2 → ι => T (i 0) (i 1)) ξ =
      ∑ a, ∑ b, T a b * (ξ a * ξ b - C a b) := by
  rw [wickPolynomial_eq_sum_coefficient]
  simp only [wickCoefficient_fin_two]
  exact sum_fun_fin_two (fun a b => T a b * (ξ a * ξ b - C a b))
private lemma wickPolynomial_rank_three (C : ι → ι → ℝ) (T : ι → ι → ι → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C (fun i : Fin 3 → ι => T (i 0) (i 1) (i 2)) ξ =
      ∑ a, ∑ b, ∑ c, T a b c * (ξ a * ξ b * ξ c - C a b * ξ c - C a c * ξ b - C b c * ξ a) := by
  rw [wickPolynomial_eq_sum_coefficient]
  simp only [wickCoefficient_fin_three]
  exact sum_fun_fin_three (fun a b c => T a b c * (ξ a * ξ b * ξ c - C a b * ξ c - C a c * ξ b - C b c * ξ a))
private lemma wickPolynomial_rank_four (C : ι → ι → ℝ) (T : ι → ι → ι → ι → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C (fun i : Fin 4 → ι => T (i 0) (i 1) (i 2) (i 3)) ξ =
      ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (ξ a * ξ b * ξ c * ξ d - C a b * ξ c * ξ d -
        C a c * ξ b * ξ d - C a d * ξ b * ξ c - C b c * ξ a * ξ d - C b d * ξ a * ξ c -
        C c d * ξ a * ξ b + C a b * C c d + C a c * C b d + C a d * C b c) := by
  rw [wickPolynomial_eq_sum_coefficient]
  simp only [wickCoefficient_fin_four]
  exact sum_fun_fin_four (fun a b c d => T a b c d * (ξ a * ξ b * ξ c * ξ d - C a b * ξ c * ξ d -
        C a c * ξ b * ξ d - C a d * ξ b * ξ c - C b c * ξ a * ξ d - C b d * ξ a * ξ c -
        C c d * ξ a * ξ b + C a b * C c d + C a c * C b d + C a d * C b c))
private lemma wickPolynomial_const_mul {q : ℕ} (C : ι → ι → ℝ) (c : ℝ) (A : (Fin q → ι) → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C (fun i => c * A i) ξ = c * wickPolynomial C A ξ := by
  simp only [wickPolynomial_eq_sum_coefficient, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
private lemma wickPolynomial_average {V : Type} [Fintype V] {q : ℕ} (C : ι → ι → ℝ)
    (T : V → (Fin q → ι) → ℝ) (ξ : ι → ℝ) :
    wickPolynomial C (fun i => average (fun v => T v i)) ξ =
      average (fun v => wickPolynomial C (T v) ξ) := by
  simp only [wickPolynomial_eq_sum_coefficient, average, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => by ring
private lemma sum_four_reorder (G : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, G a b c d = ∑ b, ∑ d, ∑ c, ∑ a, G a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, ∑ d, G a b c d = ∑ d, ∑ a, G a b c d := fun c => Finset.sum_comm
  simp only [this]
  rw [Finset.sum_comm]
private def tensorPairing (M M' : Matrix ι ι ℝ) (G : ι → ι → ι → ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, M a b * M' c d * G a b c d
private lemma tensorPairing_swap_right (M M' : Matrix ι ι ℝ) (h : M'.IsSymm) (G : ι → ι → ι → ι → ℝ) :
    tensorPairing M M' G = tensorPairing M M' (fun a b c d => G a b d c) := by
  unfold tensorPairing
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [h.apply c d]
private lemma tensorPairing_swap_left (M M' : Matrix ι ι ℝ) (h : M.IsSymm) (G : ι → ι → ι → ι → ℝ) :
    tensorPairing M M' G = tensorPairing M M' (fun a b c d => G b a c d) := by
  unfold tensorPairing
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [h.apply a b]
private lemma tensorPairing_contract (C M M' : Matrix ι ι ℝ) (h : M.IsSymm) (K : ι → ι → ℝ) :
    tensorPairing M M' (fun a b c d => C a c * K b d) = ∑ b, ∑ d, (M * C * M') b d * K b d := by
  unfold tensorPairing
  rw [sum_four_reorder]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [h.apply a b]
  ring
private def wickSquare (C M : Matrix ι ι ℝ) (ξ : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, M a b * (ξ a * ξ b - C a b)
private lemma wickSquare_mul_wickSquare (C M M' : Matrix ι ι ℝ) (hC : C.IsSymm) (hM : M.IsSymm) (hM' : M'.IsSymm)
    (ξ : ι → ℝ) :
    wickSquare C M ξ * wickSquare C M' ξ =
      wickPolynomial C (fun i : Fin 4 → ι => M (i 0) (i 1) * M' (i 2) (i 3)) ξ +
        4 * wickSquare C (M * C * M') ξ + 2 * Matrix.trace (M * C * M' * C) := by
  set k : ι → ι → ℝ := fun a b => ξ a * ξ b - C a b with hk
  have e0 : wickSquare C M ξ * wickSquare C M' ξ =
      tensorPairing M M' (fun a b c d => k a b * k c d) := by
    unfold wickSquare tensorPairing
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hk]
    ring
  have e4 : wickPolynomial C (fun i : Fin 4 → ι => M (i 0) (i 1) * M' (i 2) (i 3)) ξ =
      tensorPairing M M' (fun a b c d => ξ a * ξ b * ξ c * ξ d - C a b * ξ c * ξ d -
        C a c * ξ b * ξ d - C a d * ξ b * ξ c - C b c * ξ a * ξ d - C b d * ξ a * ξ c -
        C c d * ξ a * ξ b + C a b * C c d + C a c * C b d + C a d * C b c) :=
    wickPolynomial_rank_four C (fun a b c d => M a b * M' c d) ξ
  have split : ∀ (G₀ G₁ G₂ G₃ G₄ G₅ G₆ : ι → ι → ι → ι → ℝ),
      (∀ a b c d, k a b * k c d = G₀ a b c d + G₁ a b c d + G₂ a b c d + G₃ a b c d +
        G₄ a b c d + G₅ a b c d + G₆ a b c d) →
      tensorPairing M M' (fun a b c d => k a b * k c d) = tensorPairing M M' G₀ + tensorPairing M M' G₁ +
        tensorPairing M M' G₂ + tensorPairing M M' G₃ + tensorPairing M M' G₄ + tensorPairing M M' G₅ +
        tensorPairing M M' G₆ := by
    intro G₀ G₁ G₂ G₃ G₄ G₅ G₆ h
    unfold tensorPairing
    simp only [h, mul_add, Finset.sum_add_distrib]
  have hC' : ∀ a b, C a b = C b a := fun a b => (hC.apply b a)
  rw [e0, e4, split (fun a b c d => ξ a * ξ b * ξ c * ξ d - C a b * ξ c * ξ d -
        C a c * ξ b * ξ d - C a d * ξ b * ξ c - C b c * ξ a * ξ d - C b d * ξ a * ξ c -
        C c d * ξ a * ξ b + C a b * C c d + C a c * C b d + C a d * C b c)
    (fun a b c d => C a c * k b d) (fun a b c d => C a d * k b c)
    (fun a b c d => C b c * k a d) (fun a b c d => C b d * k a c)
    (fun a b c d => C a c * C b d) (fun a b c d => C a d * C b c)
    (fun a b c d => by simp only [hk]; ring)]
  have r2 : tensorPairing M M' (fun a b c d => C a d * k b c) =
      tensorPairing M M' (fun a b c d => C a c * k b d) := tensorPairing_swap_right M M' hM' _
  have r3 : tensorPairing M M' (fun a b c d => C b c * k a d) =
      tensorPairing M M' (fun a b c d => C a c * k b d) := tensorPairing_swap_left M M' hM _
  have r4 : tensorPairing M M' (fun a b c d => C b d * k a c) =
      tensorPairing M M' (fun a b c d => C a c * k b d) := by
    rw [tensorPairing_swap_left M M' hM, tensorPairing_swap_right M M' hM']
  have r6 : tensorPairing M M' (fun a b c d => C a d * C b c) =
      tensorPairing M M' (fun a b c d => C a c * C b d) := tensorPairing_swap_right M M' hM' _
  have r1 : tensorPairing M M' (fun a b c d => C a c * k b d) = wickSquare C (M * C * M') ξ :=
    tensorPairing_contract C M M' hM k
  have r5 : tensorPairing M M' (fun a b c d => C a c * C b d) = Matrix.trace (M * C * M' * C) := by
    rw [tensorPairing_contract C M M' hM (fun b d => C b d)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := M * C * M')]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hC' b d]
  rw [r2, r3, r4, r6, r5, r1]
  ring
private lemma wickSquare_mul_linear (C M : Matrix ι ι ℝ) (hM : M.IsSymm) (g ξ : ι → ℝ) :
    wickSquare C M ξ * ∑ c, g c * ξ c =
      wickPolynomial C (fun i : Fin 3 → ι => M (i 0) (i 1) * g (i 2)) ξ +
        2 * ∑ b, (M *ᵥ (C *ᵥ g)) b * ξ b := by
  rw [wickPolynomial_rank_three C (fun a b c => M a b * g c) ξ]
  have h1 : ∑ a, ∑ b, ∑ c, M a b * g c * (C a c * ξ b) = ∑ b, (M *ᵥ (C *ᵥ g)) b * ξ b := by
    rw [Finset.sum_comm]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hM.apply a b]
    ring
  have h2 : ∑ a, ∑ b, ∑ c, M a b * g c * (C b c * ξ a) = ∑ b, (M *ᵥ (C *ᵥ g)) b * ξ b := by
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hM.apply a b]
  have e : wickSquare C M ξ * ∑ c, g c * ξ c = ∑ a, ∑ b, ∑ c,
      (M a b * g c * (ξ a * ξ b * ξ c - C a b * ξ c - C a c * ξ b - C b c * ξ a) +
        M a b * g c * (C a c * ξ b) + M a b * g c * (C b c * ξ a)) := by
    unfold wickSquare
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [e]
  simp only [Finset.sum_add_distrib]
  rw [h1, h2]
  ring
private lemma linear_mul_linear (C : Matrix ι ι ℝ) (g g' ξ : ι → ℝ) :
    (∑ a, g a * ξ a) * ∑ b, g' b * ξ b =
      wickPolynomial C (fun i : Fin 2 → ι => g (i 0) * g' (i 1)) ξ + g ⬝ᵥ (C *ᵥ g') := by
  rw [wickPolynomial_rank_two C (fun a b => g a * g' b) ξ]
  have h : g ⬝ᵥ (C *ᵥ g') = ∑ a, ∑ b, g a * g' b * C a b := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma centeredQuadraticForm_eq_wickSquare (C M : Matrix ι ι ℝ) (hC : C.IsSymm) (hM : M.IsSymm)
    (F ξ : ι → ℝ) :
    centeredQuadraticForm C M F ξ =
      (1 / 2) * wickSquare C M ξ + ∑ a, (M *ᵥ F) a * ξ a + (1 / 2) * (F ⬝ᵥ M *ᵥ F) := by
  have h0 : F ⬝ᵥ M *ᵥ ξ = ∑ a, (M *ᵥ F) a * ξ a := by
    have : F ᵥ* M = M *ᵥ F := by
      rw [← Matrix.mulVec_transpose, hM.eq]
    rw [Matrix.dotProduct_mulVec, this]
    rfl
  have h0' : ξ ⬝ᵥ M *ᵥ F = ∑ a, (M *ᵥ F) a * ξ a := by
    rw [dotProduct_comm]
    rfl
  have h1 : (F + ξ) ⬝ᵥ M *ᵥ (F + ξ) =
      F ⬝ᵥ M *ᵥ F + 2 * ∑ a, (M *ᵥ F) a * ξ a + ξ ⬝ᵥ M *ᵥ ξ := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h0, h0']
    ring
  have h2 : ξ ⬝ᵥ M *ᵥ ξ = wickSquare C M ξ + Matrix.trace (M * C) := by
    simp only [wickSquare, dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hC.apply a b]
    ring
  unfold centeredQuadraticForm
  rw [h1, h2]
  ring
private lemma wickSquare_eq_wickPolynomial (C M : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    wickSquare C M ξ = wickPolynomial C (fun i : Fin 2 → ι => M (i 0) (i 1)) ξ :=
  (wickPolynomial_rank_two C M ξ).symm
private def quarticTensor (M M' : Matrix ι ι ℝ) (i : Fin 4 → ι) : ℝ :=
  (1 / 4) * (M (i 0) (i 1) * M' (i 2) (i 3))
private def matrixTensor (P : Matrix ι ι ℝ) (i : Fin 2 → ι) : ℝ := P (i 0) (i 1)
private def cubicTensor (M : Matrix ι ι ℝ) (g : ι → ℝ) (i : Fin 3 → ι) : ℝ :=
  (1 / 2) * (M (i 0) (i 1) * g (i 2))
private def vectorTensor (g : ι → ℝ) (i : Fin 1 → ι) : ℝ := g (i 0)
private def outerTensor (g g' : ι → ℝ) (i : Fin 2 → ι) : ℝ := g (i 0) * g' (i 1)
private lemma centeredQuadraticForm_eq_wick (C M : Matrix ι ι ℝ) (hC : C.IsSymm) (hM : M.IsSymm) (F ξ : ι → ℝ) :
    centeredQuadraticForm C M F ξ = wickPolynomial C (matrixTensor ((1 / 2 : ℝ) • M)) ξ +
      wickPolynomial C (vectorTensor (M *ᵥ F)) ξ + (1 / 2) * (F ⬝ᵥ M *ᵥ F) := by
  have e1 : wickPolynomial C (matrixTensor ((1 / 2 : ℝ) • M)) ξ = (1 / 2) * wickSquare C M ξ :=
    (wickPolynomial_const_mul C (1 / 2) (fun i : Fin 2 → ι => M (i 0) (i 1)) ξ).trans
      (by rw [wickSquare_eq_wickPolynomial])
  have e2 : wickPolynomial C (vectorTensor (M *ᵥ F)) ξ = ∑ a, (M *ᵥ F) a * ξ a :=
    wickPolynomial_rank_one C _ ξ
  rw [centeredQuadraticForm_eq_wickSquare C M hC hM, e1, e2]
private lemma centeredQuadraticForm_mul_sub (C M M' : Matrix ι ι ℝ) (hC : C.IsSymm) (hM : M.IsSymm)
    (hM' : M'.IsSymm) (F ξ : ι → ℝ) :
    centeredQuadraticForm C M F ξ * centeredQuadraticForm C M' F ξ - (1 / 2) * Matrix.trace (M * C * M' * C) =
      wickPolynomial C (quarticTensor M M') ξ + wickPolynomial C (matrixTensor (M * C * M')) ξ +
      wickPolynomial C (cubicTensor M (M' *ᵥ F)) ξ +
      wickPolynomial C (vectorTensor (M *ᵥ (C *ᵥ (M' *ᵥ F)))) ξ +
      wickPolynomial C (cubicTensor M' (M *ᵥ F)) ξ +
      wickPolynomial C (vectorTensor (M' *ᵥ (C *ᵥ (M *ᵥ F)))) ξ +
      wickPolynomial C (outerTensor (M *ᵥ F) (M' *ᵥ F)) ξ +
      wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M' *ᵥ F)) • M)) ξ +
      wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M *ᵥ F)) • M')) ξ +
      wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M' *ᵥ F)) • (M *ᵥ F))) ξ +
      wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M *ᵥ F)) • (M' *ᵥ F))) ξ +
      ((M *ᵥ F) ⬝ᵥ (C *ᵥ (M' *ᵥ F)) + (1 / 4) * ((F ⬝ᵥ M *ᵥ F) * (F ⬝ᵥ M' *ᵥ F))) := by
  set g := M *ᵥ F
  set g' := M' *ᵥ F
  set L : ℝ := ∑ a, g a * ξ a with hL
  set L' : ℝ := ∑ a, g' a * ξ a with hL'
  have a1 : wickPolynomial C (quarticTensor M M') ξ =
      (1 / 4) * wickPolynomial C (fun i : Fin 4 → ι => M (i 0) (i 1) * M' (i 2) (i 3)) ξ :=
    wickPolynomial_const_mul C (1 / 4) (fun i : Fin 4 → ι => M (i 0) (i 1) * M' (i 2) (i 3)) ξ
  have a2 : wickPolynomial C (matrixTensor (M * C * M')) ξ = wickSquare C (M * C * M') ξ :=
    (wickSquare_eq_wickPolynomial _ _ _).symm
  have a3 : wickPolynomial C (cubicTensor M g') ξ =
      (1 / 2) * wickPolynomial C (fun i : Fin 3 → ι => M (i 0) (i 1) * g' (i 2)) ξ :=
    wickPolynomial_const_mul C (1 / 2) (fun i : Fin 3 → ι => M (i 0) (i 1) * g' (i 2)) ξ
  have a3' : wickPolynomial C (cubicTensor M' g) ξ =
      (1 / 2) * wickPolynomial C (fun i : Fin 3 → ι => M' (i 0) (i 1) * g (i 2)) ξ :=
    wickPolynomial_const_mul C (1 / 2) (fun i : Fin 3 → ι => M' (i 0) (i 1) * g (i 2)) ξ
  have a4 : wickPolynomial C (vectorTensor (M *ᵥ (C *ᵥ g'))) ξ = ∑ b, (M *ᵥ (C *ᵥ g')) b * ξ b :=
    wickPolynomial_rank_one C _ ξ
  have a4' : wickPolynomial C (vectorTensor (M' *ᵥ (C *ᵥ g))) ξ = ∑ b, (M' *ᵥ (C *ᵥ g)) b * ξ b :=
    wickPolynomial_rank_one C _ ξ
  have a5 : wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ g')) • M)) ξ =
      ((1 / 4 : ℝ) * (F ⬝ᵥ g')) * wickSquare C M ξ :=
    (wickPolynomial_const_mul C _ (fun i : Fin 2 → ι => M (i 0) (i 1)) ξ).trans
      (by rw [wickSquare_eq_wickPolynomial])
  have a5' : wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ g)) • M')) ξ =
      ((1 / 4 : ℝ) * (F ⬝ᵥ g)) * wickSquare C M' ξ :=
    (wickPolynomial_const_mul C _ (fun i : Fin 2 → ι => M' (i 0) (i 1)) ξ).trans
      (by rw [wickSquare_eq_wickPolynomial])
  have a6 : wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ g')) • g)) ξ =
      ((1 / 2 : ℝ) * (F ⬝ᵥ g')) * L := by
    rw [hL, Finset.mul_sum]
    refine (wickPolynomial_rank_one C _ ξ).trans (Finset.sum_congr rfl fun a _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have a6' : wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ g)) • g')) ξ =
      ((1 / 2 : ℝ) * (F ⬝ᵥ g)) * L' := by
    rw [hL', Finset.mul_sum]
    refine (wickPolynomial_rank_one C _ ξ).trans (Finset.sum_congr rfl fun a _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have b1 := wickSquare_mul_wickSquare C M M' hC hM hM' ξ
  have b2 := wickSquare_mul_linear C M hM g' ξ
  have b2' := wickSquare_mul_linear C M' hM' g ξ
  have b3 := linear_mul_linear C g g' ξ
  rw [a1, a2, a3, a3', a4, a4', a5, a5', a6, a6', centeredQuadraticForm_eq_wickSquare C M hC hM,
    centeredQuadraticForm_eq_wickSquare C M' hC hM']
  have b3' : wickPolynomial C (outerTensor g g') ξ = L * L' - g ⬝ᵥ (C *ᵥ g') := by
    rw [hL, hL', b3]
    have : wickPolynomial C (outerTensor g g') ξ =
      wickPolynomial C (fun i : Fin 2 → ι => g (i 0) * g' (i 1)) ξ := rfl
    rw [this]
    ring
  rw [b3']
  have c1 : wickPolynomial C (fun i : Fin 4 → ι => M (i 0) (i 1) * M' (i 2) (i 3)) ξ =
      wickSquare C M ξ * wickSquare C M' ξ - 4 * wickSquare C (M * C * M') ξ -
        2 * Matrix.trace (M * C * M' * C) := by rw [b1]; ring
  have c2 : wickPolynomial C (fun i : Fin 3 → ι => M (i 0) (i 1) * g' (i 2)) ξ =
      wickSquare C M ξ * L' - 2 * ∑ b, (M *ᵥ (C *ᵥ g')) b * ξ b := by rw [hL', b2]; ring
  have c3 : wickPolynomial C (fun i : Fin 3 → ι => M' (i 0) (i 1) * g (i 2)) ξ =
      wickSquare C M' ξ * L - 2 * ∑ b, (M' *ᵥ (C *ᵥ g)) b * ξ b := by rw [hL, b2']; ring
  rw [c1, c2, c3]
  ring
end WickAlgebra
section Moments
open ProbabilityTheory
variable {ι : Type} [Fintype ι]
private lemma memLp_coordinate [DecidableEq ι] {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)}
    (h : IsCenteredGaussian C μ) (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) (i : ι)
    {p : ENNReal} (hp : p ≠ ⊤) : MemLp (fun ξ : ι → ℝ => ξ i) p μ := by
  haveI := h.1
  have hm : Measurable (fun ξ : ι → ℝ => ξ i) := measurable_pi_apply i
  haveI : IsProbabilityMeasure (μ.map (fun ξ : ι → ℝ => ξ i)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hc : 0 ≤ C i i := by
    have := hpos (Pi.single i 1)
    simpa [Pi.single_apply] using this
  have hlaw : μ.map (fun ξ : ι → ℝ => ξ i) = gaussianReal 0 (C i i).toNNReal := by
    refine Measure.ext_of_charFun (funext fun u => ?_)
    have hq : ∑ a, ∑ b, (Pi.single i u : ι → ℝ) a * C a b * (Pi.single i u : ι → ℝ) b =
        u ^ 2 * C i i := by
      simp [Pi.single_apply]
      ring
    have hl : ∀ ξ : ι → ℝ, ∑ a, (Pi.single i u : ι → ℝ) a * ξ a = u * ξ i := by
      intro ξ
      simp [Pi.single_apply]
    have key := h.2 (Pi.single i u)
    simp only [hq, hl] at key
    rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop), charFun_gaussianReal]
    calc ∫ x, Complex.exp (u * (x i : ℝ) * Complex.I) ∂μ
        = ∫ ξ : ι → ℝ, Complex.exp (Complex.I * ((u * ξ i : ℝ) : ℂ)) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
          simp only []
          push_cast
          ring_nf
      _ = _ := key
      _ = _ := by
          congr 1
          have : (((C i i).toNNReal : NNReal) : ℝ) = C i i := Real.coe_toNNReal _ hc
          simp only [this]
          push_cast
          ring
  have h1 : MemLp id p (μ.map (fun ξ : ι → ℝ => ξ i)) := by
    rw [hlaw]
    exact memLp_id_gaussianReal' p hp
  exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 h1
private def MemAllLp (μ : Measure (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ p : ENNReal, p ≠ ⊤ → MemLp f p μ
private lemma memAllLp_const {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ] (c : ℝ) :
    MemAllLp μ (fun _ => c) := fun p _ => memLp_const c
private lemma memAllLp_mul {μ : Measure (ι → ℝ)} {f g : (ι → ℝ) → ℝ} (hf : MemAllLp μ f)
    (hg : MemAllLp μ g) : MemAllLp μ (fun ξ => f ξ * g ξ) := by
  intro p hp
  haveI : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]⟩
  have h2 : 2 * p ≠ ⊤ := ENNReal.mul_ne_top (by simp) hp
  exact (hg _ h2).mul' (hf _ h2)
private lemma memAllLp_sum {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ] {κ : Type} (s : Finset κ)
    (f : κ → (ι → ℝ) → ℝ) (h : ∀ k ∈ s, MemAllLp μ (f k)) : MemAllLp μ (fun ξ => ∑ k ∈ s, f k ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memAllLp_const (μ := μ) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    intro p hp
    exact ((h a (Finset.mem_insert_self a s)) p hp).add
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)) p hp)
private lemma memAllLp_prod {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ] {κ : Type} (s : Finset κ)
    (f : κ → (ι → ℝ) → ℝ) (h : ∀ k ∈ s, MemAllLp μ (f k)) : MemAllLp μ (fun ξ => ∏ k ∈ s, f k ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memAllLp_const (μ := μ) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact memAllLp_mul (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))
private lemma memAllLp_wickPolynomial [DecidableEq ι] {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)}
    (h : IsCenteredGaussian C μ) (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) {q : ℕ}
    (A : (Fin q → ι) → ℝ) : MemAllLp μ (wickPolynomial C A) := by
  haveI := h.1
  have e : wickPolynomial C A = fun ξ => ∑ i, A i * wickCoefficient C ξ i :=
    funext fun ξ => wickPolynomial_eq_sum_coefficient C A ξ
  rw [e]
  refine memAllLp_sum _ _ fun i _ => memAllLp_mul (memAllLp_const _) ?_
  unfold wickCoefficient
  refine memAllLp_sum _ _ fun σ _ => memAllLp_mul (memAllLp_const _) (memAllLp_mul (memAllLp_const _) ?_)
  refine memAllLp_prod _ _ fun a _ => ?_
  exact fun p hp => memLp_coordinate h hpos (i a) hp
private def EvenMomentBound (μ : Measure (ι → ℝ)) (r : ℕ) (Y : (ι → ℝ) → ℝ) (b : ℝ) : Prop :=
  MemLp Y ((2 * r : ℕ) : ENNReal) μ ∧ 0 ≤ b ∧ ∫ ξ, Y ξ ^ (2 * r) ∂μ ≤ b ^ (2 * r)
private lemma integrable_pow_even {μ : Measure (ι → ℝ)} {r : ℕ} (hr : r ≠ 0) {Y : (ι → ℝ) → ℝ}
    (h : MemLp Y ((2 * r : ℕ) : ENNReal) μ) : Integrable (fun ξ => Y ξ ^ (2 * r)) μ := by
  have h1 := h.integrable_norm_pow (by omega)
  refine h1.congr (ae_of_all _ fun ξ => ?_)
  simp only [Real.norm_eq_abs]
  exact (even_two_mul r).pow_abs _
private lemma EvenMomentBound.mono {μ : Measure (ι → ℝ)} {r : ℕ} {Y : (ι → ℝ) → ℝ} {b b' : ℝ}
    (h : EvenMomentBound μ r Y b) (hb : b ≤ b') : EvenMomentBound μ r Y b' :=
  ⟨h.1, h.2.1.trans hb, h.2.2.trans (pow_le_pow_left₀ h.2.1 hb _)⟩
private lemma EvenMomentBound.add {μ : Measure (ι → ℝ)} {r : ℕ} (hr : r ≠ 0) {Y Z : (ι → ℝ) → ℝ} {b b' : ℝ}
    (h : EvenMomentBound μ r Y b) (h' : EvenMomentBound μ r Z b') :
    EvenMomentBound μ r (fun ξ => Y ξ + Z ξ) (2 * (b + b')) := by
  obtain ⟨m, hb, i⟩ := h
  obtain ⟨m', hb', i'⟩ := h'
  have hmem : MemLp (fun ξ => Y ξ + Z ξ) ((2 * r : ℕ) : ENNReal) μ := m.add m'
  refine ⟨hmem, by positivity, ?_⟩
  have hi := integrable_pow_even hr m
  have hi' := integrable_pow_even hr m'
  have hp : ∀ ξ, (Y ξ + Z ξ) ^ (2 * r) ≤ 2 ^ (2 * r - 1) * (Y ξ ^ (2 * r) + Z ξ ^ (2 * r)) :=
    fun ξ => (even_two_mul r).add_pow_le
  have h1 : ∫ ξ, (Y ξ + Z ξ) ^ (2 * r) ∂μ ≤
      ∫ ξ, 2 ^ (2 * r - 1) * (Y ξ ^ (2 * r) + Z ξ ^ (2 * r)) ∂μ :=
    integral_mono (integrable_pow_even hr hmem) ((hi.add hi').const_mul _) hp
  have h2 : ∫ ξ, 2 ^ (2 * r - 1) * (Y ξ ^ (2 * r) + Z ξ ^ (2 * r)) ∂μ =
      2 ^ (2 * r - 1) * (∫ ξ, Y ξ ^ (2 * r) ∂μ + ∫ ξ, Z ξ ^ (2 * r) ∂μ) := by
    rw [integral_const_mul, integral_add hi hi']
  have h3 : b ^ (2 * r) + b' ^ (2 * r) ≤ 2 * (b + b') ^ (2 * r) := by
    have e1 : b ^ (2 * r) ≤ (b + b') ^ (2 * r) := pow_le_pow_left₀ hb (by linarith) _
    have e2 : b' ^ (2 * r) ≤ (b + b') ^ (2 * r) := pow_le_pow_left₀ hb' (by linarith) _
    linarith
  have h4 : (2 : ℝ) ^ (2 * r - 1) * 2 = 2 ^ (2 * r) := by
    rw [← pow_succ]
    congr 1
    omega
  calc ∫ ξ, (Y ξ + Z ξ) ^ (2 * r) ∂μ ≤ 2 ^ (2 * r - 1) * (b ^ (2 * r) + b' ^ (2 * r)) := by
        rw [h2] at h1
        refine h1.trans (mul_le_mul_of_nonneg_left (add_le_add i i') (by positivity))
    _ ≤ 2 ^ (2 * r - 1) * (2 * (b + b') ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (2 * (b + b')) ^ (2 * r) := by
        rw [mul_pow, ← h4]
        ring
private lemma evenMomentBound_const {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ] (r : ℕ) (c : ℝ) :
    EvenMomentBound μ r (fun _ => c) |c| := by
  refine ⟨memLp_const c, abs_nonneg c, ?_⟩
  simp only [integral_const, probReal_univ, one_smul]
  exact ((even_two_mul r).pow_abs c).ge
private lemma evenMomentBound_wick {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} {q r : ℕ} (hr : r ≠ 0) {c s lam : ℝ}
    (hc : 1 ≤ c) (hs : 0 ≤ s) (hlam : lam = s ^ 2)
    (hmem : ∀ A : (Fin q → ι) → ℝ, MemLp (wickPolynomial C A) ((2 * r : ℕ) : ENNReal) μ)
    (hM : ∀ A : (Fin q → ι) → ℝ,
      ∫ ξ, wickPolynomial C A ξ ^ (2 * r) ∂μ ≤ c * (lam ^ q * ∑ i, A i ^ 2) ^ r)
    (A : (Fin q → ι) → ℝ) {N : ℝ} (hN : 0 ≤ N) (hA : ∑ i, A i ^ 2 ≤ N ^ 2) :
    EvenMomentBound μ r (wickPolynomial C A) (c * s ^ q * N) := by
  refine ⟨hmem A, by positivity, (hM A).trans ?_⟩
  have h0 : 0 ≤ ∑ i, A i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hl : 0 ≤ lam ^ q := by rw [hlam]; positivity
  have h1 : (lam ^ q * ∑ i, A i ^ 2) ^ r ≤ (s ^ q * N) ^ (2 * r) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (mul_nonneg hl h0) ?_ r
    rw [mul_pow, hlam, ← pow_mul, ← pow_mul, mul_comm q 2]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have h2 : c ≤ c ^ (2 * r) := le_self_pow₀ hc (by omega)
  calc c * (lam ^ q * ∑ i, A i ^ 2) ^ r ≤ c ^ (2 * r) * (s ^ q * N) ^ (2 * r) :=
        mul_le_mul h2 h1 (pow_nonneg (mul_nonneg hl h0) _) (by positivity)
    _ = (c * s ^ q * N) ^ (2 * r) := by rw [← mul_pow, mul_assoc]
end Moments
section NearPairs
variable {V : Type} [Fintype V]
open Classical in
private def nearPairDensity (Near : V → V → Prop) : ℝ :=
  ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) / (Fintype.card V : ℝ) ^ 2
private lemma nearPairDensity_nonneg (Near : V → V → Prop) : 0 ≤ nearPairDensity Near := by
  unfold nearPairDensity
  positivity
open Classical in
private lemma nearPairDensity_le_one [Nonempty V] (Near : V → V → Prop) : nearPairDensity Near ≤ 1 := by
  unfold nearPairDensity
  have hc : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    positivity
  rw [div_le_one hc]
  have h : (Finset.univ.filter fun p : V × V => Near p.1 p.2).card ≤ Fintype.card (V × V) :=
    Finset.card_le_univ _
  rw [Fintype.card_prod] at h
  have h' : ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) ≤
      (Fintype.card V : ℝ) * Fintype.card V := by exact_mod_cast h
  nlinarith
open Classical in
private lemma nearPairDensity_le [Nonempty V] (Near : V → V → Prop) {ρ : ℝ}
    (h : ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) ≤
      ρ * (Fintype.card V : ℝ) ^ 2) : nearPairDensity Near ≤ ρ := by
  unfold nearPairDensity
  have hc : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    positivity
  rw [div_le_iff₀ hc]
  exact h
private lemma sum_sq_average {κ : Type} [Fintype κ] (T : V → κ → ℝ) :
    ∑ i, average (fun v => T v i) ^ 2 =
      ((Fintype.card V : ℝ)⁻¹) ^ 2 * ∑ v, ∑ w, ∑ i, T v i * T w i := by
  unfold average
  have h : ∀ i, ((Fintype.card V : ℝ)⁻¹ * ∑ v, T v i) ^ 2 =
      ((Fintype.card V : ℝ)⁻¹) ^ 2 * ∑ v, ∑ w, T v i * T w i := by
    intro i
    rw [mul_pow, sq (∑ v, T v i), Finset.sum_mul_sum]
  simp only [h]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun v _ => Finset.sum_comm
open Classical in
private lemma average_pairs_le [Nonempty V] (Near : V → V → Prop) (G : V → V → ℝ) {n f : ℝ}
    (hn : 0 ≤ n) (hf : 0 ≤ f) (h1 : ∀ v w, G v w ≤ n) (h2 : ∀ v w, ¬ Near v w → G v w ≤ f) :
    ((Fintype.card V : ℝ)⁻¹) ^ 2 * ∑ v, ∑ w, G v w ≤ nearPairDensity Near * n + f := by
  have hc : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    positivity
  have hp : ∀ v w, G v w ≤ (if Near v w then n else 0) + f := by
    intro v w
    by_cases h : Near v w
    · simp only [h, if_true]; linarith [h1 v w]
    · simp only [h, if_false]; linarith [h2 v w h]
  have hs : ∑ v, ∑ w, G v w ≤
      ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) * n +
        (Fintype.card V : ℝ) ^ 2 * f := by
    calc ∑ v, ∑ w, G v w ≤ ∑ v, ∑ w, ((if Near v w then n else 0) + f) :=
          Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hp v w
      _ = ∑ p : V × V, ((if Near p.1 p.2 then n else 0) + f) :=
          (Fintype.sum_prod_type' (f := fun v w => (if Near v w then n else 0) + f)).symm
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
  unfold nearPairDensity
  rw [inv_pow]
  rw [inv_mul_le_iff₀ hc]
  calc _ ≤ _ := hs
    _ = _ := by field_simp
end NearPairs
section InnerProducts
variable {ι : Type} [Fintype ι]
private def frobeniusInner (X Y : Matrix ι ι ℝ) : ℝ := ∑ a, ∑ b, X a b * Y a b
private lemma frobeniusInner_self_nonneg (X : Matrix ι ι ℝ) : 0 ≤ frobeniusInner X X :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _
private lemma frobeniusInner_sq_le (X Y : Matrix ι ι ℝ) :
    frobeniusInner X Y ^ 2 ≤ frobeniusInner X X * frobeniusInner Y Y := by
  have e : ∀ X Y : Matrix ι ι ℝ, frobeniusInner X Y = ∑ x : ι × ι, X x.1 x.2 * Y x.1 x.2 :=
    fun X Y => (Fintype.sum_prod_type' (f := fun a b => X a b * Y a b)).symm
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun x => X x.1 x.2) (fun x => Y x.1 x.2)
  simp only [e, ← sq]
  exact h
private lemma selfDot_nonneg (x : ι → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun a _ => mul_self_nonneg _
private lemma dot_sq_le_selfDot (x y : ι → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) x y
  simp only [dotProduct, ← sq]
  exact h
private lemma abs_le_of_sq_le_mul {p x y K : ℝ} (h : p ^ 2 ≤ x * y) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ K) (hy : y ≤ K) : |p| ≤ K := by
  have hK : 0 ≤ K := hx0.trans hx
  refine abs_le_of_sq_le_sq ?_ hK
  nlinarith [mul_le_mul hx hy hy0 hK]
private lemma abs_frobeniusInner_le {X Y : Matrix ι ι ℝ} {K : ℝ} (hX : frobeniusInner X X ≤ K)
    (hY : frobeniusInner Y Y ≤ K) : |frobeniusInner X Y| ≤ K :=
  abs_le_of_sq_le_mul (frobeniusInner_sq_le X Y) (frobeniusInner_self_nonneg X)
    (frobeniusInner_self_nonneg Y) hX hY
private lemma abs_dot_le {x y : ι → ℝ} {K : ℝ} (hx : x ⬝ᵥ x ≤ K) (hy : y ⬝ᵥ y ≤ K) :
    |x ⬝ᵥ y| ≤ K :=
  abs_le_of_sq_le_mul (dot_sq_le_selfDot x y) (selfDot_nonneg x) (selfDot_nonneg y) hx hy
private lemma trace_mul_eq_frobeniusInner (X Y : Matrix ι ι ℝ) :
    Matrix.trace (X * Y) = frobeniusInner X Yᵀ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, frobeniusInner, Matrix.transpose_apply]
private lemma frobeniusInner_transpose (X Y : Matrix ι ι ℝ) : frobeniusInner Xᵀ Yᵀ = frobeniusInner X Y := by
  unfold frobeniusInner
  rw [Finset.sum_comm]
  rfl
private lemma selfDot_le_of_sq_le {u : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : (u ⬝ᵥ u) ^ 2 ≤ K * (u ⬝ᵥ u)) : u ⬝ᵥ u ≤ K := by
  by_contra hlt
  nlinarith
private lemma selfDot_mulVec_le (P : Matrix ι ι ℝ) (y : ι → ℝ) :
    (P *ᵥ y) ⬝ᵥ (P *ᵥ y) ≤ frobeniusInner P P * (y ⬝ᵥ y) := by
  unfold frobeniusInner
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := dot_sq_le_selfDot (fun b => P a b) y
  calc (P *ᵥ y) a * (P *ᵥ y) a = ((fun b => P a b) ⬝ᵥ y) ^ 2 := by
        rw [sq]
        rfl
    _ ≤ _ := h
private lemma frobeniusInner_mul_self_le {B X : Matrix ι ι ℝ} {b : ℝ}
    (hB : ∀ t : ι → ℝ, (B *ᵥ t) ⬝ᵥ (B *ᵥ t) ≤ b * (t ⬝ᵥ t)) :
    frobeniusInner (B * X) (B * X) ≤ b * frobeniusInner X X := by
  have e : ∀ Z : Matrix ι ι ℝ, frobeniusInner Z Z = ∑ j, (fun a => Z a j) ⬝ᵥ (fun a => Z a j) := by
    intro Z
    unfold frobeniusInner
    rw [Finset.sum_comm]
    rfl
  rw [e, e, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := hB (fun a => X a j)
  have c : (fun a => (B * X) a j) = B *ᵥ (fun a => X a j) := by
    funext a
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [c]
  exact h
private lemma dot_mulVec_of_isSymm {S : Matrix ι ι ℝ} (h : S.IsSymm) (s t : ι → ℝ) :
    s ⬝ᵥ S *ᵥ t = (S *ᵥ s) ⬝ᵥ t := by
  have : s ᵥ* S = S *ᵥ s := by
    rw [← Matrix.mulVec_transpose, h.eq]
  rw [Matrix.dotProduct_mulVec, this]
private lemma form_cauchySchwarz {C : Matrix ι ι ℝ} (hC : C.IsSymm) (hpos : ∀ t : ι → ℝ, 0 ≤ t ⬝ᵥ C *ᵥ t)
    (s t : ι → ℝ) : (s ⬝ᵥ C *ᵥ t) ^ 2 ≤ (s ⬝ᵥ C *ᵥ s) * (t ⬝ᵥ C *ᵥ t) := by
  have h : ∀ x : ℝ, 0 ≤ (t ⬝ᵥ C *ᵥ t) * (x * x) + (2 * (s ⬝ᵥ C *ᵥ t)) * x + s ⬝ᵥ C *ᵥ s := by
    intro x
    have h0 := hpos (s + x • t)
    have e1 : t ⬝ᵥ C *ᵥ s = s ⬝ᵥ C *ᵥ t := by
      rw [dot_mulVec_of_isSymm hC, dotProduct_comm]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, e1] at h0
    simp only [smul_eq_mul] at h0
    nlinarith [h0]
  have h1 := discrim_le_zero h
  unfold discrim at h1
  nlinarith [h1]
private lemma covariance_mulVec_le {C : Matrix ι ι ℝ} {lam : ℝ} (hC : C.IsSymm) (hlam : 0 ≤ lam)
    (hpos : ∀ t : ι → ℝ, 0 ≤ t ⬝ᵥ C *ᵥ t) (hle : ∀ t : ι → ℝ, t ⬝ᵥ C *ᵥ t ≤ lam * (t ⬝ᵥ t))
    (t : ι → ℝ) : (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ lam ^ 2 * (t ⬝ᵥ t) := by
  set u := C *ᵥ t with hu
  have h := form_cauchySchwarz hC hpos u t
  have hu0 := selfDot_nonneg u
  have ht0 := selfDot_nonneg t
  have h1 : u ⬝ᵥ C *ᵥ u ≤ lam * (u ⬝ᵥ u) := hle u
  have h2 : t ⬝ᵥ C *ᵥ t ≤ lam * (t ⬝ᵥ t) := hle t
  have h3 : (u ⬝ᵥ u) ^ 2 ≤ lam ^ 2 * (t ⬝ᵥ t) * (u ⬝ᵥ u) := by
    have e : (u ⬝ᵥ C *ᵥ t) = u ⬝ᵥ u := rfl
    rw [e] at h
    calc (u ⬝ᵥ u) ^ 2 ≤ (u ⬝ᵥ C *ᵥ u) * (t ⬝ᵥ C *ᵥ t) := h
      _ ≤ (lam * (u ⬝ᵥ u)) * (lam * (t ⬝ᵥ t)) :=
          mul_le_mul h1 h2 (hpos t) (mul_nonneg hlam hu0)
      _ = _ := by ring
  exact selfDot_le_of_sq_le (by positivity) h3
end InnerProducts
section FormFamilies
variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V]
private def PairedInnerBounds {q : ℕ} (T : V → (Fin q → ι) → ℝ) (Near : V → V → Prop) (n f : ℝ) : Prop :=
  (∀ v w, ∑ i, T v i * T w i ≤ n) ∧ ∀ v w, ¬ Near v w → ∑ i, T v i * T w i ≤ f
private lemma mul_le_of_abs_le_abs {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : x * y ≤ X * Y := by
  calc x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul x y
    _ ≤ X * Y := mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)
private lemma mul_mul_le_of_abs {c d x K X : ℝ} (hc : |c| ≤ K) (hd : |d| ≤ K) (hx : |x| ≤ X) :
    c * d * x ≤ K * K * X := by
  have hK : 0 ≤ K := (abs_nonneg c).trans hc
  calc c * d * x ≤ |c * d * x| := le_abs_self _
    _ = |c| * |d| * |x| := by rw [abs_mul, abs_mul]
    _ ≤ K * K * X := mul_le_mul (mul_le_mul hc hd (abs_nonneg d) hK) hx (abs_nonneg x)
        (mul_nonneg hK hK)
private lemma inner_quarticTensor (X X' Y Y' : Matrix ι ι ℝ) :
    ∑ i, quarticTensor X X' i * quarticTensor Y Y' i =
      (1 / 16) * (frobeniusInner X Y * frobeniusInner X' Y') := by
  refine (sum_fun_fin_four (fun a b c d => ((1 / 4) * (X a b * X' c d)) * ((1 / 4) * (Y a b * Y' c d)))).trans ?_
  have key : frobeniusInner X Y * frobeniusInner X' Y' =
      ∑ a, ∑ b, ∑ c, ∑ d, (X a b * Y a b) * (X' c d * Y' c d) := by
    unfold frobeniusInner
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
  rw [key]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring
private lemma inner_cubicTensor (X Y : Matrix ι ι ℝ) (g h : ι → ℝ) :
    ∑ i, cubicTensor X g i * cubicTensor Y h i = (1 / 4) * (frobeniusInner X Y * (g ⬝ᵥ h)) := by
  refine (sum_fun_fin_three (fun a b c => ((1 / 2) * (X a b * g c)) * ((1 / 2) * (Y a b * h c)))).trans ?_
  have key : frobeniusInner X Y * (g ⬝ᵥ h) = ∑ a, ∑ b, ∑ c, (X a b * Y a b) * (g c * h c) := by
    unfold frobeniusInner
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [dotProduct]
    rw [Finset.mul_sum]
  rw [key]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring
private lemma inner_matrixTensor (P Q : Matrix ι ι ℝ) :
    ∑ i, matrixTensor P i * matrixTensor Q i = frobeniusInner P Q :=
  sum_fun_fin_two (fun a b => P a b * Q a b)
private lemma inner_vectorTensor (g h : ι → ℝ) : ∑ i, vectorTensor g i * vectorTensor h i = g ⬝ᵥ h :=
  sum_fun_fin_one (fun a => g a * h a)
private lemma inner_outerTensor (g g' h h' : ι → ℝ) :
    ∑ i, outerTensor g g' i * outerTensor h h' i = (g ⬝ᵥ h) * (g' ⬝ᵥ h') := by
  refine (sum_fun_fin_two (fun a b => (g a * g' b) * (h a * h' b))).trans ?_
  simp only [dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma frobeniusInner_smul (c d : ℝ) (X Y : Matrix ι ι ℝ) :
    frobeniusInner (c • X) (d • Y) = c * d * frobeniusInner X Y := by
  unfold frobeniusInner
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring
private lemma dot_smul_smul (c d : ℝ) (x y : ι → ℝ) : (c • x) ⬝ᵥ (d • y) = c * d * (x ⬝ᵥ y) := by
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring
variable {F : ι → ℝ} {M : V → Matrix ι ι ℝ} {Near : V → V → Prop} {a A φ ε : ℝ}
private lemma family_selfDot_mulVec (h : IsAdmissibleFormFamily F M Near a A φ ε) (v : V) (t : ι → ℝ) :
    (M v *ᵥ t) ⬝ᵥ (M v *ᵥ t) ≤ a ^ 2 * (t ⬝ᵥ t) := by
  refine selfDot_le_of_sq_le (mul_nonneg (sq_nonneg a) (selfDot_nonneg t)) ?_
  have := h.op v (M v *ᵥ t) t
  nlinarith [this]
private lemma family_frobenius_self (h : IsAdmissibleFormFamily F M Near a A φ ε) (v : V) :
    frobeniusInner (M v) (M v) ≤ A := by
  have := h.hs v
  rwa [trace_mul_eq_frobeniusInner, (h.symm v).eq] at this
private lemma family_frobenius_eq_trace (h : IsAdmissibleFormFamily F M Near a A φ ε) (v w : V) :
    frobeniusInner (M v) (M w) = Matrix.trace (M v * M w) := by
  rw [trace_mul_eq_frobeniusInner, (h.symm w).eq]
private lemma family_abs_frobenius (h : IsAdmissibleFormFamily F M Near a A φ ε) (v w : V) :
    |frobeniusInner (M v) (M w)| ≤ A :=
  abs_frobeniusInner_le (family_frobenius_self h v) (family_frobenius_self h w)
private lemma family_abs_frobenius_far (h : IsAdmissibleFormFamily F M Near a A φ ε) {v w : V}
    (hf : ¬ Near v w) : |frobeniusInner (M v) (M w)| ≤ ε := by
  rw [family_frobenius_eq_trace h]
  exact h.far_trace v w hf
private lemma family_product_frobenius (h : IsAdmissibleFormFamily F M Near a A φ ε) (v w : V) :
    frobeniusInner (M v * M w) (M v * M w) ≤ a ^ 2 * A :=
  (frobeniusInner_mul_self_le (family_selfDot_mulVec h v)).trans
    (mul_le_mul_of_nonneg_left (family_frobenius_self h w) (sq_nonneg a))
private lemma family_product_frobenius_far (h : IsAdmissibleFormFamily F M Near a A φ ε) {v w : V}
    (hf : ¬ Near v w) : frobeniusInner (M v * M w) (M v * M w) ≤ ε ^ 2 := by
  have := h.far_product v w hf
  rwa [trace_mul_eq_frobeniusInner, Matrix.transpose_transpose] at this
private lemma family_product_frobenius_far_swap (h : IsAdmissibleFormFamily F M Near a A φ ε) {v w : V}
    (hf : ¬ Near v w) : frobeniusInner (M w * M v) (M w * M v) ≤ ε ^ 2 := by
  have e : M w * M v = (M v * M w)ᵀ := by
    rw [Matrix.transpose_mul, (h.symm v).eq, (h.symm w).eq]
  rw [e, frobeniusInner_transpose]
  exact family_product_frobenius_far h hf
private lemma family_abs_image_dot (h : IsAdmissibleFormFamily F M Near a A φ ε) (v w : V) :
    |(M v *ᵥ F) ⬝ᵥ (M w *ᵥ F)| ≤ A * φ ^ 2 :=
  abs_dot_le (h.image v) (h.image w)
private lemma frobeniusInner_sandwich_sq_le {C X X' Y Y' : Matrix ι ι ℝ} {lam : ℝ} (hCs : C.IsSymm)
    (hC : ∀ t : ι → ℝ, (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ lam ^ 2 * (t ⬝ᵥ t)) (hY : Y.IsSymm) (hY' : Y'.IsSymm) :
    frobeniusInner (X * C * X') (Y * C * Y') ^ 2 ≤
      (lam ^ 2 * frobeniusInner (Y * X) (Y * X)) * (lam ^ 2 * frobeniusInner (X' * Y') (X' * Y')) := by
  have e1 : frobeniusInner (X * C * X') (Y * C * Y') =
      Matrix.trace ((Y * X * C) * (X' * Y' * C)) := by
    have t : (Y * C * Y')ᵀ = Y' * C * Y := by
      simp only [Matrix.transpose_mul, hY.eq, hY'.eq, hCs.eq, Matrix.mul_assoc]
    have h1 : frobeniusInner (X * C * X') (Y * C * Y') = Matrix.trace ((X * C * X') * (Y' * C * Y)) := by
      rw [trace_mul_eq_frobeniusInner, ← t, Matrix.transpose_transpose]
    rw [h1, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hU : ∀ Z : Matrix ι ι ℝ, frobeniusInner (Z * C) (Z * C) ≤ lam ^ 2 * frobeniusInner Z Z := by
    intro Z
    have t : (Z * C)ᵀ = C * Zᵀ := by rw [Matrix.transpose_mul, hCs.eq]
    rw [← frobeniusInner_transpose, t, ← frobeniusInner_transpose Z Z]
    exact frobeniusInner_mul_self_le hC
  rw [e1, trace_mul_eq_frobeniusInner]
  have h2 := frobeniusInner_sq_le (Y * X * C) (X' * Y' * C)ᵀ
  rw [frobeniusInner_transpose] at h2
  exact h2.trans (mul_le_mul (hU _) (hU _) (frobeniusInner_self_nonneg _)
    (mul_nonneg (sq_nonneg _) (frobeniusInner_self_nonneg _)))
variable {M' : V → Matrix ι ι ℝ}
private lemma pairedBounds_quartic (h : IsAdmissibleFormFamily F M Near a A φ ε)
    (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => quarticTensor (M v) (M' v)) Near (A * A) (ε * A) := by
  constructor
  · intro v w
    simp only [inner_quarticTensor]
    have := mul_le_of_abs_le_abs (family_abs_frobenius h v w) (family_abs_frobenius h' v w)
    have hA : 0 ≤ A * A := mul_self_nonneg A
    linarith
  · intro v w hf
    simp only [inner_quarticTensor]
    have := mul_le_of_abs_le_abs (family_abs_frobenius_far h hf) (family_abs_frobenius h' v w)
    have hA : 0 ≤ ε * A :=
      mul_nonneg ((abs_nonneg _).trans (family_abs_frobenius_far h hf))
        ((abs_nonneg _).trans (family_abs_frobenius h' v w))
    linarith
private lemma pairedBounds_cubic (h : IsAdmissibleFormFamily F M Near a A φ ε)
    (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => cubicTensor (M v) (M' v *ᵥ F)) Near (A * (A * φ ^ 2)) (ε * (A * φ ^ 2)) := by
  constructor
  · intro v w
    simp only [inner_cubicTensor]
    have := mul_le_of_abs_le_abs (family_abs_frobenius h v w) (family_abs_image_dot h' v w)
    have hA : 0 ≤ A * (A * φ ^ 2) := mul_nonneg ((abs_nonneg _).trans (family_abs_frobenius h v w))
      ((abs_nonneg _).trans (family_abs_image_dot h' v w))
    linarith
  · intro v w hf
    simp only [inner_cubicTensor]
    have := mul_le_of_abs_le_abs (family_abs_frobenius_far h hf) (family_abs_image_dot h' v w)
    have hA : 0 ≤ ε * (A * φ ^ 2) := mul_nonneg ((abs_nonneg _).trans (family_abs_frobenius_far h hf))
      ((abs_nonneg _).trans (family_abs_image_dot h' v w))
    linarith
private lemma pairedBounds_outer (h : IsAdmissibleFormFamily F M Near a A φ ε)
    (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => outerTensor (M v *ᵥ F) (M' v *ᵥ F)) Near ((A * φ ^ 2) * (A * φ ^ 2))
      (ε * (A * φ ^ 2)) := by
  constructor
  · intro v w
    simp only [inner_outerTensor]
    exact mul_le_of_abs_le_abs (family_abs_image_dot h v w) (family_abs_image_dot h' v w)
  · intro v w hf
    simp only [inner_outerTensor]
    exact mul_le_of_abs_le_abs (h.far_image v w hf) (family_abs_image_dot h' v w)
private lemma pairedBounds_scaled_matrix (h : IsAdmissibleFormFamily F M Near a A φ ε)
    (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • M v)) Near
      ((A * φ ^ 2) * (A * φ ^ 2) * A) ((A * φ ^ 2) * (A * φ ^ 2) * ε) := by
  have hb : ∀ v, |(1 / 4 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)| ≤ A * φ ^ 2 := by
    intro v
    have := h'.self v
    have h0 := abs_nonneg (F ⬝ᵥ M' v *ᵥ F)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith
  constructor
  · intro v w
    simp only [inner_matrixTensor, frobeniusInner_smul]
    exact mul_mul_le_of_abs (hb v) (hb w) (family_abs_frobenius h v w)
  · intro v w hf
    simp only [inner_matrixTensor, frobeniusInner_smul]
    exact mul_mul_le_of_abs (hb v) (hb w) (family_abs_frobenius_far h hf)
private lemma pairedBounds_scaled_vector (h : IsAdmissibleFormFamily F M Near a A φ ε)
    (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • (M v *ᵥ F))) Near
      ((A * φ ^ 2) * (A * φ ^ 2) * (A * φ ^ 2)) ((A * φ ^ 2) * (A * φ ^ 2) * ε) := by
  have hb : ∀ v, |(1 / 2 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)| ≤ A * φ ^ 2 := by
    intro v
    have := h'.self v
    have h0 := abs_nonneg (F ⬝ᵥ M' v *ᵥ F)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  constructor
  · intro v w
    simp only [inner_vectorTensor, dot_smul_smul]
    exact mul_mul_le_of_abs (hb v) (hb w) (family_abs_image_dot h v w)
  · intro v w hf
    simp only [inner_vectorTensor, dot_smul_smul]
    exact mul_mul_le_of_abs (hb v) (hb w) (h.far_image v w hf)
private lemma pairedBounds_half_matrix (h : IsAdmissibleFormFamily F M Near a A φ ε) :
    PairedInnerBounds (fun v => matrixTensor ((1 / 2 : ℝ) • M v)) Near A ε := by
  have key : ∀ {x K : ℝ}, |x| ≤ K → (1 / 2 : ℝ) * (1 / 2) * x ≤ K := by
    intro x K hx
    have h1 := le_abs_self x
    have h2 := abs_nonneg x
    linarith
  constructor
  · intro v w
    simp only [inner_matrixTensor, frobeniusInner_smul]
    exact key (family_abs_frobenius h v w)
  · intro v w hf
    simp only [inner_matrixTensor, frobeniusInner_smul]
    exact key (family_abs_frobenius_far h hf)
private lemma pairedBounds_vector (h : IsAdmissibleFormFamily F M Near a A φ ε) :
    PairedInnerBounds (fun v => vectorTensor (M v *ᵥ F)) Near (A * φ ^ 2) ε := by
  constructor
  · intro v w
    simp only [inner_vectorTensor]
    exact (le_abs_self _).trans (family_abs_image_dot h v w)
  · intro v w hf
    simp only [inner_vectorTensor]
    exact (le_abs_self _).trans (h.far_image v w hf)
private lemma pairedBounds_sandwich {C : Matrix ι ι ℝ} {lam α : ℝ} (hlam : 0 ≤ lam) (hα : 0 ≤ α)
    (hαA : α ^ 2 = A) (ha : 0 ≤ a) (hCs : C.IsSymm)
    (hC : ∀ t : ι → ℝ, (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ lam ^ 2 * (t ⬝ᵥ t))
    (h : IsAdmissibleFormFamily F M Near a A φ ε) (h' : IsAdmissibleFormFamily F M' Near a A φ ε)
    (hε : 0 ≤ ε) :
    PairedInnerBounds (fun v => matrixTensor (M v * C * M' v)) Near (lam ^ 2 * (a ^ 2 * A))
      (lam ^ 2 * (ε * (a * α))) := by
  constructor
  · intro v w
    simp only [inner_matrixTensor]
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by rw [← hαA]; positivity))
    refine (frobeniusInner_sandwich_sq_le hCs hC (h.symm w) (h'.symm w)).trans ?_
    have e1 := family_product_frobenius h w v
    have e2 := family_product_frobenius h' v w
    have := mul_le_mul (mul_le_mul_of_nonneg_left e1 (sq_nonneg lam))
      (mul_le_mul_of_nonneg_left e2 (sq_nonneg lam))
      (mul_nonneg (sq_nonneg lam) (frobeniusInner_self_nonneg _))
      (mul_nonneg (sq_nonneg lam) (by rw [← hαA]; positivity))
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro v w hf
    simp only [inner_matrixTensor]
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    refine (frobeniusInner_sandwich_sq_le hCs hC (h.symm w) (h'.symm w)).trans ?_
    have e1 := family_product_frobenius_far_swap h hf
    have e2 := family_product_frobenius h' v w
    have := mul_le_mul (mul_le_mul_of_nonneg_left e1 (sq_nonneg lam))
      (mul_le_mul_of_nonneg_left e2 (sq_nonneg lam))
      (mul_nonneg (sq_nonneg lam) (frobeniusInner_self_nonneg _))
      (mul_nonneg (sq_nonneg lam) (by positivity))
    calc _ ≤ _ := this
      _ = _ := by rw [← hαA]; ring
private lemma pairedBounds_contracted {C : Matrix ι ι ℝ} {lam : ℝ} (hε : 0 ≤ ε)
    (hC : ∀ t : ι → ℝ, (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ lam ^ 2 * (t ⬝ᵥ t))
    (h : IsAdmissibleFormFamily F M Near a A φ ε) (h' : IsAdmissibleFormFamily F M' Near a A φ ε) :
    PairedInnerBounds (fun v => vectorTensor (M v *ᵥ (C *ᵥ (M' v *ᵥ F)))) Near
      (a ^ 2 * (lam ^ 2 * (A * φ ^ 2))) (ε * (lam ^ 2 * (A * φ ^ 2))) := by
  have hx : ∀ v, (C *ᵥ (M' v *ᵥ F)) ⬝ᵥ (C *ᵥ (M' v *ᵥ F)) ≤ lam ^ 2 * (A * φ ^ 2) := fun v =>
    (hC _).trans (mul_le_mul_of_nonneg_left (h'.image v) (sq_nonneg lam))
  have ht : ∀ v, (M v *ᵥ (C *ᵥ (M' v *ᵥ F))) ⬝ᵥ (M v *ᵥ (C *ᵥ (M' v *ᵥ F))) ≤
      a ^ 2 * (lam ^ 2 * (A * φ ^ 2)) := fun v =>
    (family_selfDot_mulVec h v _).trans (mul_le_mul_of_nonneg_left (hx v) (sq_nonneg a))
  constructor
  · intro v w
    simp only [inner_vectorTensor]
    exact (le_abs_self _).trans (abs_dot_le (ht v) (ht w))
  · intro v w hf
    simp only [inner_vectorTensor]
    set x := C *ᵥ (M' v *ᵥ F) with hxd
    set y := C *ᵥ (M' w *ᵥ F) with hyd
    have e : (M v *ᵥ x) ⬝ᵥ (M w *ᵥ y) = x ⬝ᵥ ((M v * M w) *ᵥ y) := by
      rw [← dot_mulVec_of_isSymm (h.symm v), Matrix.mulVec_mulVec]
    have hK : 0 ≤ lam ^ 2 * (A * φ ^ 2) := (selfDot_nonneg x).trans (hx v)
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    rw [e]
    have h1 := dot_sq_le_selfDot x ((M v * M w) *ᵥ y)
    have h2 := selfDot_mulVec_le (M v * M w) y
    have h3 : frobeniusInner (M v * M w) (M v * M w) * (y ⬝ᵥ y) ≤ ε ^ 2 * (lam ^ 2 * (A * φ ^ 2)) :=
      mul_le_mul (family_product_frobenius_far h hf) (hx w) (selfDot_nonneg y) (sq_nonneg ε)
    have h4 := mul_le_mul (hx v) (h2.trans h3) (selfDot_nonneg _) hK
    calc _ ≤ _ := h1
      _ ≤ _ := h4
      _ = _ := by ring
end FormFamilies
section AveragedMoments
variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty V]
private def WickMomentHypothesis (C : Matrix ι ι ℝ) (μ : Measure (ι → ℝ)) (lam c : ℝ) (q r : ℕ) : Prop :=
  ∀ A : (Fin q → ι) → ℝ, ∫ ξ, wickPolynomial C A ξ ^ (2 * r) ∂μ ≤ c * (lam ^ q * ∑ i, A i ^ 2) ^ r
private lemma evenMomentBound_average {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)} {Near : V → V → Prop}
    {lam c s : ℝ} {q r : ℕ} (hr : r ≠ 0) (hc : 1 ≤ c) (hs : 0 ≤ s) (hlam : lam = s ^ 2)
    (hL : ∀ A : (Fin q → ι) → ℝ, MemAllLp μ (wickPolynomial C A))
    (hM : WickMomentHypothesis C μ lam c q r)
    {T : V → (Fin q → ι) → ℝ} {n f N : ℝ} (hsp : PairedInnerBounds T Near n f) (hn : 0 ≤ n) (hf : 0 ≤ f)
    (hN : 0 ≤ N) (hle : nearPairDensity Near * n + f ≤ N ^ 2) :
    EvenMomentBound μ r (fun ξ => average (fun v => wickPolynomial C (T v) ξ)) (c * s ^ q * N) := by
  have e : (fun ξ => average (fun v => wickPolynomial C (T v) ξ)) =
      wickPolynomial C (fun i => average (fun v => T v i)) :=
    funext fun ξ => (wickPolynomial_average C T ξ).symm
  rw [e]
  refine evenMomentBound_wick hr hc hs hlam (fun A => hL A _ (ENNReal.natCast_ne_top _)) hM _ hN ?_
  rw [sum_sq_average]
  exact (average_pairs_le Near _ hn hf hsp.1 hsp.2).trans hle
private lemma average_fun_add (f g : V → ℝ) :
    average (fun v => f v + g v) = average f + average g := by
  unfold average
  rw [Finset.sum_add_distrib, mul_add]
private lemma average_fun_sub (f g : V → ℝ) :
    average (fun v => f v - g v) = average f - average g := by
  unfold average
  rw [Finset.sum_sub_distrib, mul_sub]
private lemma abs_average_le {f : V → ℝ} {K : ℝ} (h : ∀ v, |f v| ≤ K) : |average f| ≤ K := by
  have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold average
  rw [abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc]
  calc |∑ v, f v| ≤ ∑ v, |f v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, K := Finset.sum_le_sum fun v _ => h v
    _ = _ := by simp
private lemma average_add_twelve (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : V → ℝ) :
    average (fun v => f₁ v + f₂ v + f₃ v + f₄ v + f₅ v + f₆ v + f₇ v + f₈ v + f₉ v + f₁₀ v +
      f₁₁ v + f₁₂ v) = average f₁ + average f₂ + average f₃ + average f₄ + average f₅ +
      average f₆ + average f₇ + average f₈ + average f₉ + average f₁₀ + average f₁₁ +
      average f₁₂ := by
  simp only [average_fun_add]
private lemma sq_bound_rate {p rr e n z x : ℝ} (hp : 0 ≤ p) (hp' : p ≤ rr ^ 2) (hn : n ≤ x ^ 2)
    (hz : z ≤ x ^ 2) (hrr : 0 ≤ rr) (he : 0 ≤ e) : p * n + e ^ 2 * z ≤ (x * (rr + e)) ^ 2 := by
  have h1 : p * n ≤ rr ^ 2 * x ^ 2 :=
    (mul_le_mul_of_nonneg_left hn hp).trans (mul_le_mul_of_nonneg_right hp' (sq_nonneg x))
  have h2 : e ^ 2 * z ≤ e ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hz (sq_nonneg e)
  have h3 : 0 ≤ x ^ 2 * (rr * e) := mul_nonneg (sq_nonneg x) (mul_nonneg hrr he)
  nlinarith
private lemma sq_bound_split {p rr e n z x y : ℝ} (hp : 0 ≤ p) (hp' : p ≤ rr ^ 2) (hn : n ≤ x ^ 2)
    (hz : z ≤ y ^ 2) (hrr : 0 ≤ rr) (he : 0 ≤ e) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p * n + e ^ 2 * z ≤ (x * rr + y * e) ^ 2 := by
  have h1 : p * n ≤ rr ^ 2 * x ^ 2 :=
    (mul_le_mul_of_nonneg_left hn hp).trans (mul_le_mul_of_nonneg_right hp' (sq_nonneg x))
  have h2 : e ^ 2 * z ≤ e ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hz (sq_nonneg e)
  have h3 : 0 ≤ (x * rr) * (y * e) := mul_nonneg (mul_nonneg hx hrr) (mul_nonneg hy he)
  nlinarith
private lemma sq_bound_unit {p e n z x y : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hn : n ≤ x ^ 2)
    (hz : z ≤ y ^ 2) (he : 0 ≤ e) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p * n + e ^ 2 * z ≤ (x + y * e) ^ 2 := by
  have h := sq_bound_split (rr := 1) hp (by simpa using hp') hn hz zero_le_one he hx hy
  simpa using h
end AveragedMoments
section ProductAverages
variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty V]
private lemma nested_doubling_bound {b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ : ℝ}
    (n₁ : 0 ≤ b₁) (n₂ : 0 ≤ b₂) (n₃ : 0 ≤ b₃) (n₄ : 0 ≤ b₄) (n₅ : 0 ≤ b₅) (n₆ : 0 ≤ b₆)
    (n₇ : 0 ≤ b₇) (n₈ : 0 ≤ b₈) (n₉ : 0 ≤ b₉) (n₁₀ : 0 ≤ b₁₀) (n₁₁ : 0 ≤ b₁₁) (n₁₂ : 0 ≤ b₁₂)
    (p₁ : 0 ≤ w₁) (p₂ : 0 ≤ w₂) (p₃ : 0 ≤ w₃) (p₄ : 0 ≤ w₄) (p₅ : 0 ≤ w₅) (p₆ : 0 ≤ w₆)
    (p₇ : 0 ≤ w₇) (p₈ : 0 ≤ w₈)
    (h₁ : b₁ ≤ w₁) (h₂ : b₂ ≤ w₁) (h₃ : b₃ ≤ w₂) (h₄ : b₄ ≤ w₂) (h₅ : b₅ ≤ w₂) (h₆ : b₆ ≤ w₂)
    (h₇ : b₇ ≤ w₃ + w₄) (h₈ : b₈ ≤ w₅) (h₉ : b₉ ≤ w₅) (h₁₀ : b₁₀ ≤ w₆ + w₇) (h₁₁ : b₁₁ ≤ w₆ + w₇)
    (h₁₂ : b₁₂ ≤ w₃ + w₈) :
    2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (b₁ + b₂) + b₃) + b₄) + b₅) + b₆) + b₇) +
      b₈) + b₉) + b₁₀) + b₁₁) + b₁₂) ≤
      2 ^ 13 * (w₁ + w₂ + w₃ + w₄ + w₅ + w₆ + w₇ + w₈) := by
  norm_num
  linarith
private lemma mul_le_mul_factor {c u t : ℝ} (hc : 0 ≤ c) (hu : 1 ≤ u) (ht : 0 ≤ t) : c * t ≤ c * u * t := by
  have : c * t * 1 ≤ c * t * u := mul_le_mul_of_nonneg_left hu (mul_nonneg hc ht)
  nlinarith
private lemma le_mul_factor {c u t : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (ht : 0 ≤ t) : t ≤ c * u * t := by
  have h1 : 1 ≤ c * u := by nlinarith
  nlinarith
set_option maxHeartbeats 1000000 in
private lemma evenMomentBound_product_average {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)} {F : ι → ℝ}
    {M M' : V → Matrix ι ι ℝ} {Near : V → V → Prop} {a c s α e rr φ : ℝ}
    (ha : 0 ≤ a) (hc : 1 ≤ c) (hs : 0 ≤ s) (hα : 1 ≤ α) (he : 0 ≤ e) (hrr : 0 ≤ rr) (hφ : 0 ≤ φ)
    (hp : nearPairDensity Near ≤ rr ^ 2) (hCs : C.IsSymm)
    (hCop : ∀ t : ι → ℝ, (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ (s ^ 2) ^ 2 * (t ⬝ᵥ t))
    (hμ : IsProbabilityMeasure μ)
    (hL : ∀ (q : ℕ) (A : (Fin q → ι) → ℝ), MemAllLp μ (wickPolynomial C A))
    (m₁ : WickMomentHypothesis C μ (s ^ 2) c 1 8) (m₂ : WickMomentHypothesis C μ (s ^ 2) c 2 8)
    (m₃ : WickMomentHypothesis C μ (s ^ 2) c 3 8) (m₄ : WickMomentHypothesis C μ (s ^ 2) c 4 8)
    (h : IsAdmissibleFormFamily F M Near a (α ^ 2) φ (e ^ 2))
    (h' : IsAdmissibleFormFamily F M' Near a (α ^ 2) φ (e ^ 2)) :
    EvenMomentBound μ 8 (fun ξ => average (fun v => centeredQuadraticForm C (M v) F ξ *
        centeredQuadraticForm C (M' v) F ξ) -
        average (fun v => (1 / 2) * Matrix.trace (M v * C * M' v * C)))
      (2 ^ 13 * (c * (a + 1) * (s ^ 4 * α ^ 2 * (rr + e)) + c * (a + 1) * (s ^ 3 * α ^ 2 * φ * (rr + e)) +
        c * (a + 1) * (s ^ 2 * α ^ 2 * φ ^ 2) + c * (a + 1) * (s ^ 2 * (e * α) * φ) +
        c * (a + 1) * (s ^ 2 * α ^ 3 * φ ^ 2 * (rr + e)) +
        c * (a + 1) * (s * α ^ 3 * φ ^ 3 * (rr + e)) + c * (a + 1) * (s * α ^ 2 * φ ^ 2 * e) +
        c * (a + 1) * (α ^ 4 * φ ^ 4))) := by
  have hp0 := nearPairDensity_nonneg Near
  have hp1 := nearPairDensity_le_one Near
  have hα0 : 0 ≤ α := by linarith
  have he2 : 0 ≤ e ^ 2 := sq_nonneg e
  have hc0 : 0 ≤ c := by linarith
  have hα1 : α ≤ α ^ 2 := by nlinarith
  have hα2 : α ^ 2 ≤ (α ^ 2) ^ 2 := by nlinarith [sq_nonneg α]
  have hα3 : α ≤ (α ^ 2) ^ 2 := hα1.trans hα2
  set u : ℝ := a + 1 with hu
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hau : a ≤ u := by rw [hu]; linarith
  have hau2 : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ha hau 2
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hlam0 : 0 ≤ s ^ 2 := sq_nonneg s
  set η : ℝ := rr + e with hη
  have hη0 : 0 ≤ η := by rw [hη]; linarith
  have r8 : (8 : ℕ) ≠ 0 := by norm_num
  have g₁ := evenMomentBound_average (Near := Near) (T := fun v => quarticTensor (M v) (M' v)) r8 hc hs rfl
    (hL 4) m₄ (pairedBounds_quartic h h') (by positivity) (by positivity) (N := α ^ 2 * η) (by positivity)
    (sq_bound_rate hp0 hp (le_of_eq (by ring)) hα2 hrr he)
  have n₂ : (s ^ 2) ^ 2 * (a ^ 2 * α ^ 2) ≤ (u * s ^ 2 * α ^ 2) ^ 2 := by
    calc (s ^ 2) ^ 2 * (a ^ 2 * α ^ 2) ≤ (s ^ 2) ^ 2 * (u ^ 2 * (α ^ 2) ^ 2) := by gcongr
      _ = _ := by ring
  have z₂ : (s ^ 2) ^ 2 * (a * α) ≤ (u * s ^ 2 * α ^ 2) ^ 2 := by
    calc (s ^ 2) ^ 2 * (a * α) ≤ (s ^ 2) ^ 2 * (u ^ 2 * (α ^ 2) ^ 2) := by
          gcongr
          exact hau.trans hu2
      _ = _ := by ring
  have g₂ := evenMomentBound_average (Near := Near) (T := fun v => matrixTensor (M v * C * M' v)) r8 hc hs rfl
    (hL 2) m₂ (pairedBounds_sandwich hlam0 hα0 rfl ha hCs hCop h h' he2) (by positivity) (by positivity)
    (N := u * s ^ 2 * α ^ 2 * η) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_rate hp0 hp n₂ z₂ hrr he))
  have z₃ : α ^ 2 * φ ^ 2 ≤ (α ^ 2 * φ) ^ 2 := by
    calc α ^ 2 * φ ^ 2 ≤ (α ^ 2) ^ 2 * φ ^ 2 := by gcongr
      _ = _ := by ring
  have g₃ := evenMomentBound_average (Near := Near) (T := fun v => cubicTensor (M v) (M' v *ᵥ F)) r8 hc hs rfl
    (hL 3) m₃ (pairedBounds_cubic h h') (by positivity) (by positivity) (N := α ^ 2 * φ * η) (by positivity)
    (sq_bound_rate hp0 hp (le_of_eq (by ring)) z₃ hrr he)
  have g₅ := evenMomentBound_average (Near := Near) (T := fun v => cubicTensor (M' v) (M v *ᵥ F)) r8 hc hs rfl
    (hL 3) m₃ (pairedBounds_cubic h' h) (by positivity) (by positivity) (N := α ^ 2 * φ * η) (by positivity)
    (sq_bound_rate hp0 hp (le_of_eq (by ring)) z₃ hrr he)
  have n₄ : a ^ 2 * ((s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2)) ≤ (u * s ^ 2 * α * φ) ^ 2 := by
    calc a ^ 2 * ((s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2)) ≤ u ^ 2 * ((s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2)) := by gcongr
      _ = _ := by ring
  have z₄ : (s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2) ≤ (u * s ^ 2 * α * φ) ^ 2 := by
    calc (s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2) ≤ u ^ 2 * ((s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2)) := by
          have : 1 ≤ u ^ 2 := by nlinarith
          exact le_mul_of_one_le_left (by positivity) this
      _ = _ := by ring
  have g₄ := evenMomentBound_average (Near := Near) (T := fun v => vectorTensor (M v *ᵥ (C *ᵥ (M' v *ᵥ F))))
    r8 hc hs rfl (hL 1) m₁ (pairedBounds_contracted he2 hCop h h') (by positivity) (by positivity)
    (N := u * s ^ 2 * α * φ * η) (by positivity) (sq_bound_rate hp0 hp n₄ z₄ hrr he)
  have g₆ := evenMomentBound_average (Near := Near) (T := fun v => vectorTensor (M' v *ᵥ (C *ᵥ (M v *ᵥ F))))
    r8 hc hs rfl (hL 1) m₁ (pairedBounds_contracted he2 hCop h' h) (by positivity) (by positivity)
    (N := u * s ^ 2 * α * φ * η) (by positivity) (sq_bound_rate hp0 hp n₄ z₄ hrr he)
  have g₇ := evenMomentBound_average (Near := Near) (T := fun v => outerTensor (M v *ᵥ F) (M' v *ᵥ F))
    r8 hc hs rfl (hL 2) m₂ (pairedBounds_outer h h') (by positivity) (by positivity)
    (N := α ^ 2 * φ ^ 2 + α * φ * e) (by positivity)
    (sq_bound_unit (x := α ^ 2 * φ ^ 2) (y := α * φ) hp0 hp1 (le_of_eq (by ring)) (le_of_eq (by ring)) he
      (by positivity) (by positivity))
  have z₈ : (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) ≤ (α ^ 3 * φ ^ 2) ^ 2 := by
    calc (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) = (α ^ 2) ^ 2 * (φ ^ 2) ^ 2 := by ring
      _ ≤ ((α ^ 2) ^ 2 * α ^ 2) * (φ ^ 2) ^ 2 := by
          gcongr
          exact le_mul_of_one_le_right (by positivity) (by nlinarith)
      _ = _ := by ring
  have g₈ := evenMomentBound_average (Near := Near)
    (T := fun v => matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • M v)) r8 hc hs rfl (hL 2) m₂
    (pairedBounds_scaled_matrix h h') (by positivity) (by positivity) (N := α ^ 3 * φ ^ 2 * η) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_rate hp0 hp (n := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) * α ^ 2)
      (le_of_eq (by ring)) z₈ hrr he))
  have g₉ := evenMomentBound_average (Near := Near)
    (T := fun v => matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M v *ᵥ F)) • M' v)) r8 hc hs rfl (hL 2) m₂
    (pairedBounds_scaled_matrix h' h) (by positivity) (by positivity) (N := α ^ 3 * φ ^ 2 * η) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_rate hp0 hp (n := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) * α ^ 2)
      (le_of_eq (by ring)) z₈ hrr he))
  have g₁₀ := evenMomentBound_average (Near := Near)
    (T := fun v => vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • (M v *ᵥ F))) r8 hc hs rfl (hL 1) m₁
    (pairedBounds_scaled_vector h h') (by positivity) (by positivity)
    (N := α ^ 3 * φ ^ 3 * rr + α ^ 2 * φ ^ 2 * e) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_split (x := α ^ 3 * φ ^ 3) (y := α ^ 2 * φ ^ 2) hp0 hp
      (n := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2))
      (z := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2)) (le_of_eq (by ring)) (le_of_eq (by ring)) hrr he
      (by positivity) (by positivity)))
  have g₁₁ := evenMomentBound_average (Near := Near)
    (T := fun v => vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M v *ᵥ F)) • (M' v *ᵥ F))) r8 hc hs rfl (hL 1) m₁
    (pairedBounds_scaled_vector h' h) (by positivity) (by positivity)
    (N := α ^ 3 * φ ^ 3 * rr + α ^ 2 * φ ^ 2 * e) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_split (x := α ^ 3 * φ ^ 3) (y := α ^ 2 * φ ^ 2) hp0 hp
      (n := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2))
      (z := (α ^ 2 * φ ^ 2) * (α ^ 2 * φ ^ 2)) (le_of_eq (by ring)) (le_of_eq (by ring)) hrr he
      (by positivity) (by positivity)))
  set kk : ℝ := average (fun v => (M v *ᵥ F) ⬝ᵥ (C *ᵥ (M' v *ᵥ F)) +
    (1 / 4) * ((F ⬝ᵥ M v *ᵥ F) * (F ⬝ᵥ M' v *ᵥ F))) with hkk
  have hK : |kk| ≤ s ^ 2 * α ^ 2 * φ ^ 2 + α ^ 4 * φ ^ 4 := by
    refine abs_average_le fun v => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine abs_le_of_sq_le_sq ?_ (by positivity)
      have h1 := dot_sq_le_selfDot (M v *ᵥ F) (C *ᵥ (M' v *ᵥ F))
      have h2 : (C *ᵥ (M' v *ᵥ F)) ⬝ᵥ (C *ᵥ (M' v *ᵥ F)) ≤ (s ^ 2) ^ 2 * (α ^ 2 * φ ^ 2) :=
        (hCop _).trans (mul_le_mul_of_nonneg_left (h'.image v) (by positivity))
      have h3 := mul_le_mul (h.image v) h2 (selfDot_nonneg _) (by positivity)
      calc _ ≤ _ := h1
        _ ≤ _ := h3
        _ = _ := by ring
    · have h1 := h.self v
      have h2 := h'.self v
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_mul]
      have h3 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      have h5 := mul_nonneg (abs_nonneg (F ⬝ᵥ M v *ᵥ F)) (abs_nonneg (F ⬝ᵥ M' v *ᵥ F))
      linarith
  have g₁₂ := (evenMomentBound_const (μ := μ) 8 kk).mono hK
  have G := ((((((((((g₁.add r8 g₂).add r8 g₃).add r8 g₄).add r8 g₅).add r8 g₆).add r8 g₇).add r8
    g₈).add r8 g₉).add r8 g₁₀).add r8 g₁₁).add r8 g₁₂
  have e₀ : (fun ξ => average (fun v => centeredQuadraticForm C (M v) F ξ * centeredQuadraticForm C (M' v) F ξ) -
      average (fun v => (1 / 2) * Matrix.trace (M v * C * M' v * C))) =
      fun ξ => average (fun v => wickPolynomial C (quarticTensor (M v) (M' v)) ξ) +
        average (fun v => wickPolynomial C (matrixTensor (M v * C * M' v)) ξ) +
        average (fun v => wickPolynomial C (cubicTensor (M v) (M' v *ᵥ F)) ξ) +
        average (fun v => wickPolynomial C (vectorTensor (M v *ᵥ (C *ᵥ (M' v *ᵥ F)))) ξ) +
        average (fun v => wickPolynomial C (cubicTensor (M' v) (M v *ᵥ F)) ξ) +
        average (fun v => wickPolynomial C (vectorTensor (M' v *ᵥ (C *ᵥ (M v *ᵥ F)))) ξ) +
        average (fun v => wickPolynomial C (outerTensor (M v *ᵥ F) (M' v *ᵥ F)) ξ) +
        average (fun v => wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • M v)) ξ) +
        average (fun v => wickPolynomial C (matrixTensor (((1 / 4 : ℝ) * (F ⬝ᵥ M v *ᵥ F)) • M' v)) ξ) +
        average (fun v => wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M' v *ᵥ F)) • (M v *ᵥ F))) ξ) +
        average (fun v => wickPolynomial C (vectorTensor (((1 / 2 : ℝ) * (F ⬝ᵥ M v *ᵥ F)) • (M' v *ᵥ F))) ξ) +
        kk := by
    funext ξ
    refine (average_fun_sub _ _).symm.trans ?_
    refine (congrArg average (funext fun v =>
      centeredQuadraticForm_mul_sub C (M v) (M' v) hCs (h.symm v) (h'.symm v) F ξ)).trans ?_
    exact average_add_twelve _ _ _ _ _ _ _ _ _ _ _ _
  rw [e₀]
  refine EvenMomentBound.mono G ?_
  have hcu : ∀ t : ℝ, 0 ≤ t → c * t ≤ c * u * t := fun t ht => mul_le_mul_factor hc0 hu1 ht
  have hcu1 : ∀ t : ℝ, 0 ≤ t → t ≤ c * u * t := fun t ht => le_mul_factor hc hu1 ht
  have hrη : rr ≤ η := by rw [hη]; linarith
  have heη : e ≤ η := by rw [hη]; linarith
  refine nested_doubling_bound (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · calc c * s ^ 4 * (α ^ 2 * η) = c * (s ^ 4 * α ^ 2 * η) := by ring
      _ ≤ _ := hcu _ (by positivity)
  · exact le_of_eq (by ring)
  · calc c * s ^ 3 * (α ^ 2 * φ * η) = c * (s ^ 3 * α ^ 2 * φ * η) := by ring
      _ ≤ _ := hcu _ (by positivity)
  · calc c * s ^ 1 * (u * s ^ 2 * α * φ * η) = c * u * (s ^ 3 * α * φ * η) := by ring
      _ ≤ c * u * (s ^ 3 * α ^ 2 * φ * η) := by gcongr
  · calc c * s ^ 3 * (α ^ 2 * φ * η) = c * (s ^ 3 * α ^ 2 * φ * η) := by ring
      _ ≤ _ := hcu _ (by positivity)
  · calc c * s ^ 1 * (u * s ^ 2 * α * φ * η) = c * u * (s ^ 3 * α * φ * η) := by ring
      _ ≤ c * u * (s ^ 3 * α ^ 2 * φ * η) := by gcongr
  · calc c * s ^ 2 * (α ^ 2 * φ ^ 2 + α * φ * e) =
        c * (s ^ 2 * α ^ 2 * φ ^ 2) + c * (s ^ 2 * (e * α) * φ) := by ring
      _ ≤ _ := add_le_add (hcu _ (by positivity)) (hcu _ (by positivity))
  · calc c * s ^ 2 * (α ^ 3 * φ ^ 2 * η) = c * (s ^ 2 * α ^ 3 * φ ^ 2 * η) := by ring
      _ ≤ _ := hcu _ (by positivity)
  · calc c * s ^ 2 * (α ^ 3 * φ ^ 2 * η) = c * (s ^ 2 * α ^ 3 * φ ^ 2 * η) := by ring
      _ ≤ _ := hcu _ (by positivity)
  · calc c * s ^ 1 * (α ^ 3 * φ ^ 3 * rr + α ^ 2 * φ ^ 2 * e) =
        c * (s * α ^ 3 * φ ^ 3 * rr) + c * (s * α ^ 2 * φ ^ 2 * e) := by ring
      _ ≤ c * (s * α ^ 3 * φ ^ 3 * η) + c * (s * α ^ 2 * φ ^ 2 * e) := by gcongr
      _ ≤ _ := add_le_add (hcu _ (by positivity)) (hcu _ (by positivity))
  · calc c * s ^ 1 * (α ^ 3 * φ ^ 3 * rr + α ^ 2 * φ ^ 2 * e) =
        c * (s * α ^ 3 * φ ^ 3 * rr) + c * (s * α ^ 2 * φ ^ 2 * e) := by ring
      _ ≤ c * (s * α ^ 3 * φ ^ 3 * η) + c * (s * α ^ 2 * φ ^ 2 * e) := by gcongr
      _ ≤ _ := add_le_add (hcu _ (by positivity)) (hcu _ (by positivity))
  · exact add_le_add (hcu1 _ (by positivity)) (hcu1 _ (by positivity))
end ProductAverages
section Assembly
variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty V]
private lemma evenMomentBound_average_form {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)} {F : ι → ℝ}
    {M : V → Matrix ι ι ℝ} {Near : V → V → Prop} {a c s α e rr φ : ℝ}
    (hc : 1 ≤ c) (hs : 0 ≤ s) (hα : 1 ≤ α) (he : 0 ≤ e) (hrr : 0 ≤ rr) (hφ : 0 ≤ φ)
    (hp : nearPairDensity Near ≤ rr ^ 2) (hCs : C.IsSymm) (hμ : IsProbabilityMeasure μ)
    (hL : ∀ (q : ℕ) (A : (Fin q → ι) → ℝ), MemAllLp μ (wickPolynomial C A))
    (m₁ : WickMomentHypothesis C μ (s ^ 2) c 1 8) (m₂ : WickMomentHypothesis C μ (s ^ 2) c 2 8)
    (h : IsAdmissibleFormFamily F M Near a (α ^ 2) φ (e ^ 2)) :
    EvenMomentBound μ 8 (fun ξ => average (fun v => centeredQuadraticForm C (M v) F ξ))
      (2 ^ 3 * (c * (s ^ 2 * α * (rr + e)) + c * (s * α * φ * (rr + e)) + c * (s * e) +
        c * (α ^ 2 * φ ^ 2))) := by
  have hp0 := nearPairDensity_nonneg Near
  have hα0 : 0 ≤ α := by linarith
  have r8 : (8 : ℕ) ≠ 0 := by norm_num
  have g₁ := evenMomentBound_average (Near := Near) (T := fun v => matrixTensor ((1 / 2 : ℝ) • M v)) r8 hc hs rfl
    (hL 2) m₂ (pairedBounds_half_matrix h) (by positivity) (by positivity) (N := α * rr + 1 * e) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_split (x := α) (y := 1) hp0 hp (n := α ^ 2) (z := 1)
      le_rfl (by norm_num) hrr he hα0 zero_le_one))
  have g₂ := evenMomentBound_average (Near := Near) (T := fun v => vectorTensor (M v *ᵥ F)) r8 hc hs rfl
    (hL 1) m₁ (pairedBounds_vector h) (by positivity) (by positivity) (N := α * φ * rr + 1 * e) (by positivity)
    (le_trans (le_of_eq (by ring)) (sq_bound_split (x := α * φ) (y := 1) hp0 hp (n := α ^ 2 * φ ^ 2) (z := 1)
      (le_of_eq (by ring)) (by norm_num) hrr he (by positivity) zero_le_one))
  set kk : ℝ := average (fun v => (1 / 2) * (F ⬝ᵥ M v *ᵥ F)) with hkk
  have hK : |kk| ≤ α ^ 2 * φ ^ 2 := by
    refine abs_average_le fun v => ?_
    have h1 := h.self v
    have h2 := abs_nonneg (F ⬝ᵥ M v *ᵥ F)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have g₃ := (evenMomentBound_const (μ := μ) 8 kk).mono hK
  have G := (g₁.add r8 g₂).add r8 g₃
  have e₀ : (fun ξ => average (fun v => centeredQuadraticForm C (M v) F ξ)) =
      fun ξ => average (fun v => wickPolynomial C (matrixTensor ((1 / 2 : ℝ) • M v)) ξ) +
        average (fun v => wickPolynomial C (vectorTensor (M v *ᵥ F)) ξ) + kk := by
    funext ξ
    refine (congrArg average (funext fun v => centeredQuadraticForm_eq_wick C (M v) hCs (h.symm v) F ξ)).trans ?_
    rw [average_fun_add, average_fun_add]
  rw [e₀]
  refine EvenMomentBound.mono G ?_
  have b₁ : c * s ^ 2 * (α * rr + 1 * e) ≤ c * (s ^ 2 * α * (rr + e)) := by
    have : α * rr + 1 * e ≤ α * (rr + e) := by nlinarith
    calc c * s ^ 2 * (α * rr + 1 * e) ≤ c * s ^ 2 * (α * (rr + e)) := by gcongr
      _ = _ := by ring
  have b₂ : c * s ^ 1 * (α * φ * rr + 1 * e) ≤ c * (s * α * φ * (rr + e)) + c * (s * e) := by
    have : α * φ * rr ≤ α * φ * (rr + e) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc c * s ^ 1 * (α * φ * rr + 1 * e) ≤ c * s ^ 1 * (α * φ * (rr + e) + 1 * e) := by gcongr
      _ = _ := by ring
  have b₃ : α ^ 2 * φ ^ 2 ≤ c * (α ^ 2 * φ ^ 2) :=
    le_mul_of_one_le_left (by positivity) hc
  have n₁ : 0 ≤ c * s ^ 2 * (α * rr + 1 * e) := by positivity
  have n₂ : 0 ≤ c * s ^ 1 * (α * φ * rr + 1 * e) := by positivity
  have n₃ : 0 ≤ α ^ 2 * φ ^ 2 := by positivity
  norm_num
  linarith
private lemma evenMomentBound_single_form {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)} {F : ι → ℝ}
    {M : V → Matrix ι ι ℝ} {Near : V → V → Prop} {a c s α e φ : ℝ}
    (hc : 1 ≤ c) (hs : 0 ≤ s) (hα : 1 ≤ α) (hφ : 0 ≤ φ) (hCs : C.IsSymm)
    (hμ : IsProbabilityMeasure μ) (hL : ∀ (q : ℕ) (A : (Fin q → ι) → ℝ), MemAllLp μ (wickPolynomial C A))
    (m₁ : WickMomentHypothesis C μ (s ^ 2) c 1 16) (m₂ : WickMomentHypothesis C μ (s ^ 2) c 2 16)
    (h : IsAdmissibleFormFamily F M Near a (α ^ 2) φ (e ^ 2)) (v : V) :
    EvenMomentBound μ 16 (fun ξ => centeredQuadraticForm C (M v) F ξ)
      (2 ^ 3 * (c * (s ^ 2 * α) + c * (s * α * φ) + c * (α ^ 2 * φ ^ 2))) := by
  have hα0 : 0 ≤ α := by linarith
  have r16 : (16 : ℕ) ≠ 0 := by norm_num
  have hsq : ∀ {q : ℕ} (A : (Fin q → ι) → ℝ), ∑ i, A i ^ 2 = ∑ i, A i * A i := fun A =>
    Finset.sum_congr rfl fun i _ => sq (A i)
  have g₁ := evenMomentBound_wick (q := 2) r16 hc hs rfl (fun A => hL 2 A _ (ENNReal.natCast_ne_top _)) m₂
    (matrixTensor ((1 / 2 : ℝ) • M v)) hα0 (by
      rw [hsq, inner_matrixTensor, frobeniusInner_smul]
      have h1 := family_frobenius_self h v
      have h2 := frobeniusInner_self_nonneg (M v)
      linarith)
  have g₂ := evenMomentBound_wick (q := 1) r16 hc hs rfl (fun A => hL 1 A _ (ENNReal.natCast_ne_top _)) m₁
    (vectorTensor (M v *ᵥ F)) (N := α * φ) (by positivity) (by
      rw [hsq, inner_vectorTensor]
      refine (h.image v).trans (le_of_eq (by ring)))
  have hK : |(1 / 2 : ℝ) * (F ⬝ᵥ M v *ᵥ F)| ≤ α ^ 2 * φ ^ 2 := by
    have h1 := h.self v
    have h2 := abs_nonneg (F ⬝ᵥ M v *ᵥ F)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have g₃ := (evenMomentBound_const (μ := μ) 16 ((1 / 2 : ℝ) * (F ⬝ᵥ M v *ᵥ F))).mono hK
  have G := (g₁.add r16 g₂).add r16 g₃
  have e₀ : (fun ξ => centeredQuadraticForm C (M v) F ξ) =
      fun ξ => wickPolynomial C (matrixTensor ((1 / 2 : ℝ) • M v)) ξ +
        wickPolynomial C (vectorTensor (M v *ᵥ F)) ξ + (1 / 2) * (F ⬝ᵥ M v *ᵥ F) :=
    funext fun ξ => centeredQuadraticForm_eq_wick C (M v) hCs (h.symm v) F ξ
  rw [e₀]
  refine EvenMomentBound.mono G ?_
  have b₁ : c * s ^ 2 * α = c * (s ^ 2 * α) := by ring
  have b₂ : c * s ^ 1 * (α * φ) = c * (s * α * φ) := by ring
  have b₃ : α ^ 2 * φ ^ 2 ≤ c * (α ^ 2 * φ ^ 2) :=
    le_mul_of_one_le_left (by positivity) hc
  have n₁ : 0 ≤ c * (s ^ 2 * α) := by positivity
  have n₂ : 0 ≤ c * (s * α * φ) := by positivity
  have n₃ : 0 ≤ α ^ 2 * φ ^ 2 := by positivity
  rw [b₁, b₂]
  norm_num
  linarith
private lemma sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx,
    show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
private lemma sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx,
    show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
private lemma productAverageBound_sq {s α e φ η : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α) (he : 0 ≤ e) :
    productAverageBound (s ^ 2) (α ^ 2) φ (e ^ 2) η =
      s ^ 4 * α ^ 2 * η + s ^ 3 * α ^ 2 * φ * η + s ^ 2 * α ^ 2 * φ ^ 2 + s ^ 2 * (e * α) * φ +
        s ^ 2 * α ^ 3 * φ ^ 2 * η + s * α ^ 3 * φ ^ 3 * η + s * α ^ 2 * φ ^ 2 * e +
        α ^ 4 * φ ^ 4 := by
  unfold productAverageBound
  rw [sq_rpow_three_halves hs, sq_rpow_three_halves hα, sq_rpow_half hs,
    show e ^ 2 * α ^ 2 = (e * α) ^ 2 by ring, Real.sqrt_sq (mul_nonneg he hα), Real.sqrt_sq he]
  ring
private lemma averageBound_sq {s α e φ η : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α) (he : 0 ≤ e) :
    averageBound (s ^ 2) (α ^ 2) φ (e ^ 2) η =
      s ^ 2 * α * η + s * α * φ * η + s * e + α ^ 2 * φ ^ 2 := by
  unfold averageBound
  rw [sq_rpow_half hs, Real.sqrt_sq hα, Real.sqrt_sq he]
private lemma singleFormBound_sq {s α φ : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α) :
    singleFormBound (s ^ 2) (α ^ 2) φ = s ^ 2 * α + s * α * φ + α ^ 2 * φ ^ 2 := by
  unfold singleFormBound
  rw [sq_rpow_half hs, Real.sqrt_sq hα]
private lemma dot_mulVec_eq_double_sum (C : Matrix ι ι ℝ) (t : ι → ℝ) :
    t ⬝ᵥ C.mulVec t = ∑ i, ∑ j, t i * C i j * t j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma selfDot_eq_sum_sq (t : ι → ℝ) : t ⬝ᵥ t = ∑ i, t i ^ 2 :=
  Finset.sum_congr rfl fun i _ => (sq (t i)).symm
end Assembly
theorem quadraticConcentration_of_wickMoments (hW : WickMomentBound) :
    quadraticConcentrationStatement := by
  intro a ha
  obtain ⟨D₁, hD₁, m₁⟩ := hW 1 8
  obtain ⟨D₂, hD₂, m₂⟩ := hW 2 8
  obtain ⟨D₃, hD₃, m₃⟩ := hW 3 8
  obtain ⟨D₄, hD₄, m₄⟩ := hW 4 8
  obtain ⟨E₁, hE₁, n₁⟩ := hW 1 16
  obtain ⟨E₂, hE₂, n₂⟩ := hW 2 16
  obtain ⟨c, hc, hcD₁, hcD₂, hcD₃, hcD₄, hcE₁, hcE₂⟩ : ∃ c : ℝ, 1 ≤ c ∧ D₁ ≤ c ∧ D₂ ≤ c ∧ D₃ ≤ c ∧
      D₄ ≤ c ∧ E₁ ≤ c ∧ E₂ ≤ c :=
    ⟨1 + D₁ + D₂ + D₃ + D₄ + E₁ + E₂, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩
  have hc0 : 0 ≤ c := by linarith
  have hu1 : 1 ≤ a + 1 := by linarith
  refine ⟨2 ^ 13 * (c * (a + 1)), by positivity, ?_⟩
  intro ι V _ _ _ _ C μ F M M' Near lam A φ ε ρ hlam hA hφ hε hρ hCs hCpos hCle hG hF hF' hcount
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ lam = s ^ 2 :=
    ⟨Real.sqrt lam, Real.sqrt_nonneg _, (Real.sq_sqrt hlam).symm⟩
  obtain ⟨α, hα, rfl⟩ : ∃ α : ℝ, 1 ≤ α ∧ A = α ^ 2 :=
    ⟨Real.sqrt A, Real.one_le_sqrt.2 hA, (Real.sq_sqrt (by linarith)).symm⟩
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 ≤ e ∧ ε = e ^ 2 :=
    ⟨Real.sqrt ε, Real.sqrt_nonneg _, (Real.sq_sqrt hε).symm⟩
  obtain ⟨rr, hrr, rfl⟩ : ∃ rr : ℝ, 0 ≤ rr ∧ ρ = rr ^ 2 :=
    ⟨Real.sqrt ρ, Real.sqrt_nonneg _, (Real.sq_sqrt hρ).symm⟩
  have hα0 : 0 ≤ α := by linarith
  rw [Real.sqrt_sq hrr, Real.sqrt_sq he, productAverageBound_sq hs hα0 he, averageBound_sq hs hα0 he,
    singleFormBound_sq hs hα0]
  haveI hμ : IsProbabilityMeasure μ := hG.1
  have hsym : ∀ i j, C i j = C j i := fun i j => hCs.apply j i
  have hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j := fun t => by
    rw [← dot_mulVec_eq_double_sum]
    exact hCpos t
  have hle : ∀ t : ι → ℝ, ∑ i, ∑ j, t i * C i j * t j ≤ s ^ 2 * ∑ i, t i ^ 2 := fun t => by
    rw [← dot_mulVec_eq_double_sum, ← selfDot_eq_sum_sq]
    exact hCle t
  have hL : ∀ (q : ℕ) (B : (Fin q → ι) → ℝ), MemAllLp μ (wickPolynomial C B) :=
    fun q B => memAllLp_wickPolynomial hG hpos B
  have hCop : ∀ t : ι → ℝ, (C *ᵥ t) ⬝ᵥ (C *ᵥ t) ≤ (s ^ 2) ^ 2 * (t ⬝ᵥ t) :=
    covariance_mulVec_le hCs hlam hCpos hCle
  have M₁ : WickMomentHypothesis C μ (s ^ 2) c 1 8 := fun B =>
    (m₁ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcD₁ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have M₂ : WickMomentHypothesis C μ (s ^ 2) c 2 8 := fun B =>
    (m₂ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcD₂ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have M₃ : WickMomentHypothesis C μ (s ^ 2) c 3 8 := fun B =>
    (m₃ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcD₃ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have M₄ : WickMomentHypothesis C μ (s ^ 2) c 4 8 := fun B =>
    (m₄ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcD₄ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have N₁ : WickMomentHypothesis C μ (s ^ 2) c 1 16 := fun B =>
    (n₁ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcE₁ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have N₂ : WickMomentHypothesis C μ (s ^ 2) c 2 16 := fun B =>
    (n₂ ι C (s ^ 2) μ hlam hsym hpos hle hG B).trans
      (mul_le_mul_of_nonneg_right hcE₂ (pow_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) _))
  have hp : nearPairDensity Near ≤ rr ^ 2 := nearPairDensity_le Near hcount
  have hk : (2 : ℝ) ^ 3 * c ≤ 2 ^ 13 * (c * (a + 1)) := by
    have : c * 1 ≤ c * (a + 1) := mul_le_mul_of_nonneg_left hu1 hc0
    norm_num
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have G := (evenMomentBound_product_average ha hc hs hα he hrr hφ hp hCs hCop hμ hL M₁ M₂ M₃ M₄
      hF hF').2.2
    refine G.trans (le_of_eq ?_)
    congr 1
    ring
  · have G := (evenMomentBound_average_form (a := a) hc hs hα he hrr hφ hp hCs hμ hL M₁ M₂ hF).mono
      (b' := 2 ^ 13 * (c * (a + 1)) * (s ^ 2 * α * (rr + e) + s * α * φ * (rr + e) + s * e +
        α ^ 2 * φ ^ 2)) (by
        have hn : 0 ≤ s ^ 2 * α * (rr + e) + s * α * φ * (rr + e) + s * e + α ^ 2 * φ ^ 2 := by
          positivity
        calc _ = 2 ^ 3 * c * (s ^ 2 * α * (rr + e) + s * α * φ * (rr + e) + s * e +
              α ^ 2 * φ ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hn)
    exact G.2.2
  · intro v
    have G := (evenMomentBound_single_form (a := a) hc hs hα hφ hCs hμ hL N₁ N₂ hF v).mono
      (b' := 2 ^ 13 * (c * (a + 1)) * (s ^ 2 * α + s * α * φ + α ^ 2 * φ ^ 2)) (by
        have hn : 0 ≤ s ^ 2 * α + s * α * φ + α ^ 2 * φ ^ 2 := by positivity
        calc _ = 2 ^ 3 * c * (s ^ 2 * α + s * α * φ + α ^ 2 * φ ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hn)
    exact G.2.2
end QuadraticConcentration
end YangMills.Construction
end
