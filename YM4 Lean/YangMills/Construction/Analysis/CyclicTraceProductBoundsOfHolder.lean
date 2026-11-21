import YangMills.Construction.Analysis.CyclicTraceProducts
import Mathlib
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
noncomputable section
namespace YangMills.Construction.SquareSummable.CyclicTraceProducts
section OrderedProducts
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private def orderedProd (f : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | n + 1 => orderedProd f n * f n
private theorem orderedProd_zero (f : ℕ → Matrix ι ι ℂ) : orderedProd f 0 = 1 := rfl
private theorem orderedProd_succ (f : ℕ → Matrix ι ι ℂ) (n : ℕ) :
    orderedProd f (n + 1) = orderedProd f n * f n := rfl
private theorem orderedProd_congr {f g : ℕ → Matrix ι ι ℂ} {N : ℕ} (h : ∀ i < N, f i = g i) :
    orderedProd f N = orderedProd g N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [orderedProd_succ, orderedProd_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
private theorem orderedProd_add (f : ℕ → Matrix ι ι ℂ) (a b : ℕ) :
    orderedProd f (a + b) = orderedProd f a * orderedProd (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [orderedProd_zero]
  | succ n ih =>
    rw [← add_assoc, orderedProd_succ, ih, orderedProd_succ, mul_assoc]
private theorem orderedProd_succ' (f : ℕ → Matrix ι ι ℂ) (n : ℕ) :
    orderedProd f (n + 1) = f 0 * orderedProd (fun i => f (i + 1)) n := by
  rw [add_comm, orderedProd_add]
  simp only [orderedProd_succ, orderedProd_zero, one_mul, add_comm 1]
private theorem orderedProd_conjTranspose (f : ℕ → Matrix ι ι ℂ) (n : ℕ) :
    (orderedProd f n)ᴴ = orderedProd (fun i => (f (n - 1 - i))ᴴ) n := by
  induction n generalizing f with
  | zero => simp [orderedProd_zero]
  | succ n ih =>
    rw [orderedProd_succ, conjTranspose_mul, ih, orderedProd_succ']
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    apply orderedProd_congr
    intro i hi
    congr 2
    omega
private theorem orderedProd_alternating (C : Matrix ι ι ℂ) (n : ℕ) :
    orderedProd (fun i => if Even i then C else Cᴴ) (2 * n) = (C * Cᴴ) ^ n := by
  induction n with
  | zero => simp [orderedProd_zero]
  | succ n ih =>
    have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have h2 : ¬ Even (2 * n + 1) := by simp
    rw [h1, orderedProd_succ, orderedProd_succ, ih, pow_succ]
    simp [h2, mul_assoc]
private theorem orderedProd_apply (g : ℕ → Matrix ι ι ℂ) (N : ℕ) (a b : ι) :
    orderedProd g N a b = ∑ α : Fin (N + 1) → ι,
      if α 0 = a ∧ α (Fin.last N) = b then
        ∏ k : Fin N, g k (α k.castSucc) (α k.succ) else 0 := by
  induction N generalizing b with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    by_cases h : a = b
    · subst h
      simp [orderedProd_zero]
    · have : ∀ x : ι, ¬ (x = a ∧ x = b) := fun x hx => h (hx.1.symm.trans hx.2)
      simp [orderedProd_zero, h, this]
  | succ N ih =>
    have hF : ∀ (d : ι) (β : Fin (N + 1) → ι),
        (if (Fin.snoc β d : Fin (N + 2) → ι) 0 = a ∧
            (Fin.snoc β d : Fin (N + 2) → ι) (Fin.last (N + 1)) = b then
          ∏ k : Fin (N + 1), g k ((Fin.snoc β d : Fin (N + 2) → ι) k.castSucc)
            ((Fin.snoc β d : Fin (N + 2) → ι) k.succ) else 0) =
        if d = b then
          (if β 0 = a then (∏ k : Fin N, g k (β k.castSucc) (β k.succ)) * g N (β (Fin.last N)) d
            else 0) else 0 := by
      intro d β
      have h0 : (Fin.snoc β d : Fin (N + 2) → ι) 0 = β 0 := by
        rw [← Fin.castSucc_zero]
        exact Fin.snoc_castSucc (α := fun _ => ι) d β 0
      have hs : ∀ k : Fin N, (Fin.snoc β d : Fin (N + 2) → ι) k.castSucc.succ = β k.succ := by
        intro k
        rw [Fin.succ_castSucc]
        exact Fin.snoc_castSucc (α := fun _ => ι) d β k.succ
      have hl : (Fin.snoc β d : Fin (N + 2) → ι) (Fin.last N).succ = d := by
        rw [Fin.succ_last]
        exact Fin.snoc_last (α := fun _ => ι) d β
      rw [h0, Fin.snoc_last, Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, hs, hl, Fin.val_castSucc, Fin.val_last]
      by_cases h1 : d = b <;> by_cases h2 : β 0 = a <;> simp [h1, h2]
    rw [orderedProd_succ, Matrix.mul_apply]
    simp_rw [ih]
    have hsum : ∀ F : (Fin (N + 2) → ι) → ℂ, ∑ α, F α = ∑ d : ι, ∑ β : Fin (N + 1) → ι,
        F (Fin.snoc β d : Fin (N + 2) → ι) := by
      intro F
      rw [← (Fin.snocEquiv (fun _ : Fin (N + 2) => ι)).sum_comp, Fintype.sum_prod_type]
      rfl
    rw [hsum]
    simp_rw [hF, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    by_cases h2 : β 0 = a
    · simp [h2]
    · simp [h2]
end OrderedProducts
section GramTraces
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem sum_cyclic_eq_trace (g : ℕ → Matrix ι ι ℂ) (N : ℕ) :
    ∑ α : Fin (N + 1) → ι, ∏ k : Fin (N + 1), g k (α k) (α (finRotate (N + 1) k)) =
      Matrix.trace (orderedProd g (N + 1)) := by
  have hrot : ∀ k : Fin N, finRotate (N + 1) k.castSucc = k.succ := fun k => finRotate_of_lt k.2
  have hper : ∀ α : Fin (N + 1) → ι, ∏ k : Fin (N + 1), g k (α k) (α (finRotate (N + 1) k)) =
      ∑ a : ι, ∑ b : ι, if α 0 = a ∧ α (Fin.last N) = b then
        (∏ k : Fin N, g k (α k.castSucc) (α k.succ)) * g N b a else 0 := by
    intro α
    rw [Fin.prod_univ_castSucc]
    simp only [hrot, finRotate_last, Fin.val_castSucc, Fin.val_last]
    simp [ite_and]
  simp_rw [hper]
  rw [orderedProd_succ, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply]
  simp_rw [orderedProd_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
private def frobSq (X : Matrix ι ι ℂ) : ℝ := ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2
private theorem frobSq_nonneg (X : Matrix ι ι ℂ) : 0 ≤ frobSq X :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem norm_sum_mul_sq_le {κ : Type*} [Fintype κ] (x y : κ → ℂ) :
    ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ ^ 2) * ∑ k, ‖y k‖ ^ 2 := by
  calc ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ * ‖y k‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
private theorem frobSq_swap (Y : Matrix ι ι ℂ) : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = frobSq Y :=
  (Equiv.prodComm ι ι).sum_comp (fun p : ι × ι => ‖Y p.1 p.2‖ ^ 2)
private theorem norm_trace_mul_sq_le_frobSq (X Y : Matrix ι ι ℂ) :
    ‖Matrix.trace (X * Y)‖ ^ 2 ≤ frobSq X * frobSq Y := by
  have h : Matrix.trace (X * Y) = ∑ p : ι × ι, X p.1 p.2 * Y p.2 p.1 := by
    rw [Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.mul_apply]
  rw [h, ← frobSq_swap Y]
  exact norm_sum_mul_sq_le _ _
private theorem frobSq_mul_le (X Y : Matrix ι ι ℂ) : frobSq (X * Y) ≤ frobSq X * frobSq Y := by
  have h1 : frobSq X = ∑ i, ∑ k, ‖X i k‖ ^ 2 := Fintype.sum_prod_type _
  have h2 : frobSq Y = ∑ j, ∑ k, ‖Y k j‖ ^ 2 := by
    rw [← frobSq_swap Y]
    exact Fintype.sum_prod_type _
  have h3 : frobSq (X * Y) = ∑ i, ∑ j, ‖∑ k, X i k * Y k j‖ ^ 2 := by
    rw [frobSq, Fintype.sum_prod_type]
    simp [Matrix.mul_apply]
  rw [h1, h2, h3, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_sum_mul_sq_le _ _
private theorem frobSq_conjTranspose (X : Matrix ι ι ℂ) : frobSq Xᴴ = frobSq X := by
  rw [← frobSq_swap X]
  simp [frobSq, Matrix.conjTranspose_apply]
private theorem trace_mul_conjTranspose_eq_frobSq (X : Matrix ι ι ℂ) :
    Matrix.trace (X * Xᴴ) = ((frobSq X : ℝ) : ℂ) := by
  rw [frobSq, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]
private theorem eq_zero_of_frobSq_eq_zero {X : Matrix ι ι ℂ} (h : frobSq X = 0) : X = 0 := by
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by positivity)).mp h
  ext i j
  simpa using h0 (i, j) (Finset.mem_univ _)
private def gramTrace (A : Matrix ι ι ℂ) (n : ℕ) : ℝ := (Matrix.trace ((A * Aᴴ) ^ n)).re
private theorem gram_pow_conjTranspose (A : Matrix ι ι ℂ) (t : ℕ) :
    ((A * Aᴴ) ^ t)ᴴ = (A * Aᴴ) ^ t := by
  rw [conjTranspose_pow, conjTranspose_mul, conjTranspose_conjTranspose]
private theorem exists_gram_pow_eq (A : Matrix ι ι ℂ) (n : ℕ) : ∃ B, (A * Aᴴ) ^ n = B * Bᴴ := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
  · refine ⟨(A * Aᴴ) ^ t, ?_⟩
    rw [gram_pow_conjTranspose, two_mul, pow_add]
  · refine ⟨(A * Aᴴ) ^ t * A, ?_⟩
    rw [conjTranspose_mul, gram_pow_conjTranspose, show 2 * t + 1 = t + 1 + t by ring, pow_add,
      pow_succ]
    simp only [mul_assoc]
private theorem exists_gram_pow_eq_frobSq (A : Matrix ι ι ℂ) (n : ℕ) :
    ∃ B, (A * Aᴴ) ^ n = B * Bᴴ ∧ gramTrace A n = frobSq B := by
  obtain ⟨B, hB⟩ := exists_gram_pow_eq A n
  refine ⟨B, hB, ?_⟩
  rw [gramTrace, hB, trace_mul_conjTranspose_eq_frobSq, Complex.ofReal_re]
private theorem gramTrace_nonneg (A : Matrix ι ι ℂ) (n : ℕ) : 0 ≤ gramTrace A n := by
  obtain ⟨B, _, h⟩ := exists_gram_pow_eq_frobSq A n
  rw [h]
  exact frobSq_nonneg B
private theorem trace_gram_pow (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace ((A * Aᴴ) ^ n) = ((gramTrace A n : ℝ) : ℂ) := by
  obtain ⟨B, hB, h⟩ := exists_gram_pow_eq_frobSq A n
  rw [h, hB, trace_mul_conjTranspose_eq_frobSq]
private theorem gramTrace_add_le (A : Matrix ι ι ℂ) (a b : ℕ) :
    gramTrace A (a + b) ≤ gramTrace A a * gramTrace A b := by
  obtain ⟨B, hB, h⟩ := exists_gram_pow_eq_frobSq A a
  obtain ⟨C, hC, h'⟩ := exists_gram_pow_eq_frobSq A b
  have h1 : Matrix.trace ((A * Aᴴ) ^ (a + b)) = ((frobSq (Cᴴ * B) : ℝ) : ℂ) := by
    rw [← trace_mul_conjTranspose_eq_frobSq, pow_add, hB, hC, conjTranspose_mul,
      conjTranspose_conjTranspose,
      show B * Bᴴ * (C * Cᴴ) = (B * Bᴴ * C) * Cᴴ by simp only [mul_assoc], Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [gramTrace, h1, Complex.ofReal_re, h, h']
  calc frobSq (Cᴴ * B) ≤ frobSq Cᴴ * frobSq B := frobSq_mul_le _ _
    _ = frobSq B * frobSq C := by rw [frobSq_conjTranspose, mul_comm]
private theorem gramTrace_mul_le (A : Matrix ι ι ℂ) (n j : ℕ) (hj : 1 ≤ j) :
    gramTrace A (j * n) ≤ gramTrace A n ^ j := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Nat.succ_mul, pow_succ]
    exact (gramTrace_add_le A _ _).trans
      (mul_le_mul_of_nonneg_right ih (gramTrace_nonneg A n))
open scoped ComplexOrder in
private theorem eq_zero_of_hermitian_pow_eq_zero {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (n : ℕ)
    (hn : 1 ≤ n) (h : H ^ n = 0) : H = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      simpa using h
    · have hj : (n + 1) / 2 < n := by omega
      refine ih ((n + 1) / 2) hj (by omega) ?_
      have h2 : (H ^ ((n + 1) / 2))ᴴ * H ^ ((n + 1) / 2) = 0 := by
        rw [conjTranspose_pow, hH, ← pow_add]
        obtain ⟨c, hc⟩ : ∃ c, (n + 1) / 2 + (n + 1) / 2 = n + c :=
          ⟨(n + 1) / 2 + (n + 1) / 2 - n, by omega⟩
        rw [hc, pow_add, h, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
open scoped ComplexOrder in
private theorem eq_zero_of_gramTrace_eq_zero {A : Matrix ι ι ℂ} {n : ℕ} (hn : 1 ≤ n)
    (h : gramTrace A n = 0) : A = 0 := by
  obtain ⟨B, hB, h'⟩ := exists_gram_pow_eq_frobSq A n
  have hB0 : B = 0 := eq_zero_of_frobSq_eq_zero (h' ▸ h)
  have h1 : (A * Aᴴ) ^ n = 0 := by rw [hB, hB0]; simp
  have h2 : A * Aᴴ = 0 := eq_zero_of_hermitian_pow_eq_zero
    (by rw [conjTranspose_mul, conjTranspose_conjTranspose]) n hn h1
  exact Matrix.self_mul_conjTranspose_eq_zero.mp h2
private theorem gramTrace_conjTranspose (A : Matrix ι ι ℂ) {n : ℕ} (hn : 1 ≤ n) :
    gramTrace Aᴴ n = gramTrace A n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have h : ∀ t : ℕ, (Aᴴ * Aᴴᴴ) ^ (t + 1) = Aᴴ * ((A * Aᴴ) ^ t * A) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ, ih, conjTranspose_conjTranspose, pow_succ]
      simp only [mul_assoc]
  rw [gramTrace, gramTrace, h, Matrix.trace_mul_comm, pow_succ, mul_assoc]
private theorem gramTrace_smul (A : Matrix ι ι ℂ) (c : ℝ) (n : ℕ) :
    gramTrace ((c : ℂ) • A) n = c ^ (2 * n) * gramTrace A n := by
  have h : ((c : ℂ) • A) * ((c : ℂ) • A)ᴴ = ((c : ℂ) ^ 2) • (A * Aᴴ) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp [sq]
  rw [gramTrace, gramTrace, h, smul_pow, Matrix.trace_smul, ← pow_mul, ← Complex.ofReal_pow,
    smul_eq_mul, Complex.re_ofReal_mul]
end GramTraces
section Holder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem trace_orderedProd_rotate (f : ℕ → Matrix ι ι ℂ) (N : ℕ) (hN : 1 ≤ N) :
    Matrix.trace (orderedProd (fun i => if i + 1 < N then f (i + 1) else f 0) N) =
      Matrix.trace (orderedProd f N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [orderedProd_succ, orderedProd_succ' f]
  have h : orderedProd (fun i => if i + 1 < M + 1 then f (i + 1) else f 0) M =
      orderedProd (fun i => f (i + 1)) M :=
    orderedProd_congr fun i hi => by simp [hi]
  rw [h, Matrix.trace_mul_comm]
  simp
private def reflectFront (f : ℕ → Matrix ι ι ℂ) (n : ℕ) : ℕ → Matrix ι ι ℂ :=
  fun i => if i < n then f i else (f (2 * n - 1 - i))ᴴ
private def reflectBack (f : ℕ → Matrix ι ι ℂ) (n : ℕ) : ℕ → Matrix ι ι ℂ :=
  fun i => if i < n then (f (2 * n - 1 - i))ᴴ else f i
private theorem orderedProd_reflectFront (f : ℕ → Matrix ι ι ℂ) (n : ℕ) :
    orderedProd (reflectFront f n) (2 * n) = orderedProd f n * (orderedProd f n)ᴴ := by
  rw [two_mul, orderedProd_add, orderedProd_conjTranspose]
  congr 1
  · exact orderedProd_congr fun i hi => by simp [reflectFront, hi]
  · refine orderedProd_congr fun i hi => ?_
    simp only [reflectFront]
    rw [if_neg (by omega)]
    congr 2
    omega
private theorem orderedProd_reflectBack (f : ℕ → Matrix ι ι ℂ) (n : ℕ) :
    orderedProd (reflectBack f n) (2 * n) =
      (orderedProd (fun i => f (n + i)) n)ᴴ * orderedProd (fun i => f (n + i)) n := by
  rw [two_mul, orderedProd_add, orderedProd_conjTranspose]
  congr 1
  · refine orderedProd_congr fun i hi => ?_
    simp only [reflectBack, if_pos hi]
    congr 2
    omega
  · refine orderedProd_congr fun i hi => ?_
    simp [reflectBack]
private def AdjointChain (g : ℕ → Matrix ι ι ℂ) (a b : ℕ) : Prop :=
  ∀ i, a ≤ i → i + 1 < b → g (i + 1) = (g i)ᴴ
private theorem adjointChain_reflectFront {g : ℕ → Matrix ι ι ℂ} {n s : ℕ} (_hs : 1 ≤ s)
    (hsn : s ≤ n) (h : AdjointChain g (n - s) n) :
    AdjointChain (reflectFront g n) (n - s) (n + s) := by
  intro p h1 h2
  simp only [reflectFront]
  by_cases c1 : p + 1 < n
  · rw [if_pos c1, if_pos (by omega)]
    exact h p h1 c1
  · rw [if_neg c1]
    by_cases c2 : p < n
    · rw [if_pos c2]
      congr 2
      omega
    · rw [if_neg c2, conjTranspose_conjTranspose]
      have := h (2 * n - 2 - p) (by omega) (by omega)
      rw [show 2 * n - 1 - (p + 1) = 2 * n - 2 - p by omega]
      rw [show 2 * n - 1 - p = 2 * n - 2 - p + 1 by omega, this]
private theorem eq_alternating_of_adjointChain {g : ℕ → Matrix ι ι ℂ} {N : ℕ}
    (h : AdjointChain g 0 N) : ∀ i < N, g i = if Even i then g 0 else (g 0)ᴴ := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    rw [h i (Nat.zero_le _) hi, ih (by omega)]
    by_cases c : Even i
    · simp [c, Nat.even_add_one]
    · simp [c, Nat.even_add_one]
private theorem norm_trace_le_one_of_normalized {𝒜 : Set (Matrix ι ι ℂ)} (hfin : 𝒜.Finite)
    (hadj : ∀ C ∈ 𝒜, Cᴴ ∈ 𝒜) {n : ℕ} (hn : 1 ≤ n) (h1 : ∀ C ∈ 𝒜, gramTrace C n = 1)
    (f : ℕ → Matrix ι ι ℂ) (hf : ∀ i < 2 * n, f i ∈ 𝒜) :
    ‖Matrix.trace (orderedProd f (2 * n))‖ ≤ 1 := by
  classical
  have : Finite 𝒜 := hfin
  let extend : (Fin (2 * n) → 𝒜) → ℕ → Matrix ι ι ℂ :=
    fun c i => if h : i < 2 * n then (c ⟨i, h⟩ : Matrix ι ι ℂ) else 0
  have hextend : ∀ c, ∀ i < 2 * n, extend c i ∈ 𝒜 := by
    intro c i hi
    simp only [extend, dif_pos hi]
    exact (c ⟨i, hi⟩).2
  have hf0 : f 0 ∈ 𝒜 := hf 0 (by omega)
  have : Nonempty (Fin (2 * n) → 𝒜) := ⟨fun _ => ⟨f 0, hf0⟩⟩
  obtain ⟨c0, hmax⟩ := Finite.exists_max
    (fun c : Fin (2 * n) → 𝒜 => ‖Matrix.trace (orderedProd (extend c) (2 * n))‖)
  set M := ‖Matrix.trace (orderedProd (extend c0) (2 * n))‖ with hMdef
  have hle : ∀ g : ℕ → Matrix ι ι ℂ, (∀ i < 2 * n, g i ∈ 𝒜) →
      ‖Matrix.trace (orderedProd g (2 * n))‖ ≤ M := by
    intro g hg
    have := hmax (fun i => ⟨g i, hg i i.2⟩)
    have h2 : orderedProd g (2 * n) = orderedProd (extend (fun i => ⟨g i, hg i i.2⟩)) (2 * n) :=
      orderedProd_congr fun i hi => by simp [extend, hi]
    rw [h2]
    exact this
  have halt : ∀ C ∈ 𝒜,
      ‖Matrix.trace (orderedProd (fun i => if Even i then C else Cᴴ) (2 * n))‖ = 1 := by
    intro C hC
    rw [orderedProd_alternating, trace_gram_pow, h1 C hC]
    simp
  have hM1 : 1 ≤ M := by
    rw [← halt _ hf0]
    refine hle _ fun i _ => ?_
    by_cases c : Even i
    · simpa [c] using hf0
    · simpa [c] using hadj _ hf0
  have hstep : ∀ g : ℕ → Matrix ι ι ℂ, (∀ i < 2 * n, g i ∈ 𝒜) →
      ‖Matrix.trace (orderedProd g (2 * n))‖ = M →
      (∀ i < 2 * n, reflectFront g n i ∈ 𝒜) ∧
        ‖Matrix.trace (orderedProd (reflectFront g n) (2 * n))‖ = M := by
    intro g hg hgM
    have hL : ∀ i < 2 * n, reflectFront g n i ∈ 𝒜 := by
      intro i hi
      simp only [reflectFront]
      split_ifs with c
      · exact hg i hi
      · exact hadj _ (hg _ (by omega))
    have hR : ∀ i < 2 * n, reflectBack g n i ∈ 𝒜 := by
      intro i hi
      simp only [reflectBack]
      split_ifs with c
      · exact hadj _ (hg _ (by omega))
      · exact hg i hi
    refine ⟨hL, ?_⟩
    set X := orderedProd g n with hX
    set S := orderedProd (fun i => g (n + i)) n with hS
    have hXS : orderedProd g (2 * n) = X * S := by rw [two_mul, orderedProd_add]
    have eL : ‖Matrix.trace (orderedProd (reflectFront g n) (2 * n))‖ = frobSq X := by
      rw [orderedProd_reflectFront, trace_mul_conjTranspose_eq_frobSq, Complex.norm_real,
        Real.norm_of_nonneg (frobSq_nonneg X)]
    have eR : ‖Matrix.trace (orderedProd (reflectBack g n) (2 * n))‖ = frobSq S := by
      have : Sᴴ * S = Sᴴ * Sᴴᴴ := by rw [conjTranspose_conjTranspose]
      rw [orderedProd_reflectBack, ← hS, this, trace_mul_conjTranspose_eq_frobSq,
        Complex.norm_real, Real.norm_of_nonneg (frobSq_nonneg _), frobSq_conjTranspose]
    have hXM : frobSq X ≤ M := eL ▸ hle _ hL
    have hSM : frobSq S ≤ M := eR ▸ hle _ hR
    have hcs := norm_trace_mul_sq_le_frobSq X S
    rw [← hXS, hgM] at hcs
    have : M ≤ frobSq X := by
      have h3 : M ^ 2 ≤ frobSq X * M :=
        hcs.trans (mul_le_mul_of_nonneg_left hSM (frobSq_nonneg X))
      nlinarith
    rw [eL]
    exact le_antisymm hXM this
  have hchain : ∀ s, 1 ≤ s → s ≤ n → ∃ g : ℕ → Matrix ι ι ℂ, (∀ i < 2 * n, g i ∈ 𝒜) ∧
      ‖Matrix.trace (orderedProd g (2 * n))‖ = M ∧ AdjointChain g (n - s) n := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro _
      refine ⟨extend c0, hextend c0, rfl, ?_⟩
      intro i h2 h3
      omega
    | succ s hs ih =>
      intro hsn
      obtain ⟨g, hg, hgM, hc⟩ := ih (by omega)
      obtain ⟨hL, hLM⟩ := hstep g hg hgM
      have hc' := adjointChain_reflectFront hs (by omega) hc
      refine ⟨fun i => if i + 1 < 2 * n then reflectFront g n (i + 1) else reflectFront g n 0,
        ?_, ?_, ?_⟩
      · intro i hi
        simp only
        split_ifs with c
        · exact hL _ c
        · exact hL _ (by omega)
      · rw [trace_orderedProd_rotate _ _ (by omega)]
        exact hLM
      · intro i h2 h3
        simp only
        rw [if_pos (by omega), if_pos (by omega)]
        exact hc' (i + 1) (by omega) (by omega)
  obtain ⟨g, hg, hgM, hc⟩ := hchain n hn le_rfl
  obtain ⟨hL, hLM⟩ := hstep g hg hgM
  have hc' : AdjointChain (reflectFront g n) 0 (2 * n) := by
    have := adjointChain_reflectFront hn le_rfl hc
    simpa [two_mul] using this
  have hfinal : orderedProd (reflectFront g n) (2 * n) =
      orderedProd (fun i => if Even i then reflectFront g n 0 else (reflectFront g n 0)ᴴ)
        (2 * n) :=
    orderedProd_congr (eq_alternating_of_adjointChain hc')
  have hM : M = 1 := by
    rw [← hLM, hfinal]
    exact halt _ (hL 0 (by omega))
  rw [← hM]
  exact hle f hf
private theorem orderedProd_eq_zero {f : ℕ → Matrix ι ι ℂ} {k N : ℕ} (hk : k < N)
    (h : f k = 0) : orderedProd f N = 0 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [orderedProd_succ]
    by_cases c : k = N
    · rw [← c, h, mul_zero]
    · rw [ih (by omega), zero_mul]
private theorem orderedProd_smul (f : ℕ → Matrix ι ι ℂ) (c : ℕ → ℝ) (N : ℕ) :
    orderedProd (fun k => (c k : ℂ) • f k) N =
      ((∏ k ∈ Finset.range N, c k : ℝ) : ℂ) • orderedProd f N := by
  induction N with
  | zero => simp [orderedProd_zero]
  | succ N ih =>
    rw [orderedProd_succ, orderedProd_succ, ih, Finset.prod_range_succ, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    push_cast
    rfl
private theorem norm_trace_orderedProd_le_holder {n : ℕ} (hn : 1 ≤ n) (f : ℕ → Matrix ι ι ℂ) :
    ‖Matrix.trace (orderedProd f (2 * n))‖ ≤
      ∏ k ∈ Finset.range (2 * n), gramTrace (f k) n ^ (1 / ((2 * n : ℕ) : ℝ)) := by
  classical
  by_cases hz : ∃ k < 2 * n, f k = 0
  · obtain ⟨k, hk, h0⟩ := hz
    rw [orderedProd_eq_zero hk h0]
    simp only [Matrix.trace_zero, norm_zero]
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (gramTrace_nonneg _ _) _
  · push Not at hz
    have hpos : ∀ k < 2 * n, 0 < gramTrace (f k) n := fun k hk =>
      lt_of_le_of_ne (gramTrace_nonneg _ _) fun h => hz k hk (eq_zero_of_gramTrace_eq_zero hn h.symm)
    have hn0 : (((2 * n : ℕ) : ℝ)) ≠ 0 := by
      have : 2 * n ≠ 0 := by omega
      exact_mod_cast this
    let c : ℕ → ℝ := fun k => (gramTrace (f k) n ^ (1 / ((2 * n : ℕ) : ℝ)))⁻¹
    have hcpos : ∀ k < 2 * n, 0 < c k := fun k hk =>
      inv_pos.mpr (Real.rpow_pos_of_pos (hpos k hk) _)
    let g : ℕ → Matrix ι ι ℂ := fun k => (c k : ℂ) • f k
    have hg1 : ∀ k < 2 * n, gramTrace (g k) n = 1 := by
      intro k hk
      simp only [g]
      rw [gramTrace_smul]
      have : c k ^ (2 * n) = (gramTrace (f k) n)⁻¹ := by
        simp only [c]
        rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (hpos k hk).le]
        rw [one_div, inv_mul_cancel₀ hn0, Real.rpow_one]
      rw [this, inv_mul_cancel₀ (hpos k hk).ne']
    let 𝒜 : Set (Matrix ι ι ℂ) := {C | ∃ k < 2 * n, C = g k ∨ C = (g k)ᴴ}
    have hfin : 𝒜.Finite := by
      refine Set.Finite.subset (Finset.finite_toSet
        ((Finset.range (2 * n)).image g ∪ (Finset.range (2 * n)).image fun k => (g k)ᴴ)) ?_
      rintro C ⟨k, hk, rfl | rfl⟩
      · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image,
          Finset.mem_range]
        exact Or.inl ⟨k, hk, rfl⟩
      · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image,
          Finset.mem_range]
        exact Or.inr ⟨k, hk, rfl⟩
    have hadj : ∀ C ∈ 𝒜, Cᴴ ∈ 𝒜 := by
      rintro C ⟨k, hk, rfl | rfl⟩
      · exact ⟨k, hk, Or.inr rfl⟩
      · exact ⟨k, hk, Or.inl (conjTranspose_conjTranspose _)⟩
    have h1 : ∀ C ∈ 𝒜, gramTrace C n = 1 := by
      rintro C ⟨k, hk, rfl | rfl⟩
      · exact hg1 k hk
      · rw [gramTrace_conjTranspose _ hn]
        exact hg1 k hk
    have hmain := norm_trace_le_one_of_normalized hfin hadj hn h1 g
      (fun k hk => ⟨k, hk, Or.inl rfl⟩)
    simp only [g] at hmain
    rw [orderedProd_smul, Matrix.trace_smul, norm_smul, Complex.norm_real] at hmain
    have hP : 0 < ∏ k ∈ Finset.range (2 * n), c k :=
      Finset.prod_pos fun k hk => hcpos k (Finset.mem_range.mp hk)
    rw [Real.norm_of_nonneg hP.le] at hmain
    have hinv : ∏ k ∈ Finset.range (2 * n), gramTrace (f k) n ^ (1 / ((2 * n : ℕ) : ℝ)) =
        (∏ k ∈ Finset.range (2 * n), c k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by simp only [c, inv_inv]
    rw [hinv, ← one_div, le_div_iff₀ hP, mul_comm]
    exact hmain
end Holder
section FrobeniusBound
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem frobSq_orderedProd_le (f : ℕ → Matrix ι ι ℂ) (M : ℕ) :
    frobSq (orderedProd f (M + 1)) ≤ ∏ k ∈ Finset.range (M + 1), frobSq (f k) := by
  induction M with
  | zero => simp [orderedProd_succ, orderedProd_zero]
  | succ M ih =>
    rw [orderedProd_succ, Finset.prod_range_succ]
    exact (frobSq_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (frobSq_nonneg _))
private theorem norm_trace_le_prod_frobSq (f : ℕ → Matrix ι ι ℂ) (M : ℕ) :
    ‖Matrix.trace (orderedProd f (M + 2))‖ ≤
      ∏ k ∈ Finset.range (M + 2), frobSq (f k) ^ (1 / 2 : ℝ) := by
  have h1 : ‖Matrix.trace (orderedProd f (M + 2))‖ ^ 2 ≤
      ∏ k ∈ Finset.range (M + 2), frobSq (f k) := by
    rw [orderedProd_succ, Finset.prod_range_succ]
    exact (norm_trace_mul_sq_le_frobSq _ _).trans
      (mul_le_mul_of_nonneg_right (frobSq_orderedProd_le f M) (frobSq_nonneg _))
  rw [Real.finsetProd_rpow _ _ fun k _ => frobSq_nonneg _]
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    show (((2 : ℕ) : ℝ) * (1 / 2)) = 1 by norm_num, Real.rpow_one] at h2
end FrobeniusBound
section Kernels
open Filter Topology
variable {𝔸 : Type} [Countable 𝔸] [Nonempty 𝔸] [DecidableEq 𝔸]
private def restrictKernel (A : 𝔸 → 𝔸 → ℂ) (D : Finset 𝔸) : Matrix D D ℂ := fun a b => A a b
private theorem restrictKernel_adjointKernel (A : 𝔸 → 𝔸 → ℂ) (D : Finset 𝔸) :
    restrictKernel (adjointKernel A) D = (restrictKernel A D)ᴴ := by
  ext a b
  simp [restrictKernel, adjointKernel, Matrix.conjTranspose_apply]
private theorem sum_piFinset_eq_trace_restrict (Bn : ℕ → 𝔸 → 𝔸 → ℂ) {m : ℕ} (hm : 1 ≤ m)
    (D : Finset 𝔸) :
    ∑ α ∈ Fintype.piFinset (fun _ : Fin m => D), cyclicTraceTerm (fun k : Fin m => Bn k) α =
      Matrix.trace (orderedProd (fun i => restrictKernel (Bn i) D) m) := by
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  rw [← sum_cyclic_eq_trace]
  symm
  refine Finset.sum_bij (fun a _ k => ((a k : D) : 𝔸)) ?_ ?_ ?_ ?_
  · intro a _
    simp [Fintype.mem_piFinset]
  · intro a _ b _ h
    funext k
    exact Subtype.ext (congrFun h k)
  · intro α hα
    exact ⟨fun k => ⟨α k, Fintype.mem_piFinset.mp hα k⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl
private theorem tendsto_piFinset_atTop (m : ℕ) :
    Tendsto (fun D : Finset 𝔸 => Fintype.piFinset (fun _ : Fin m => D)) atTop atTop := by
  refine tendsto_atTop.mpr fun S => ?_
  filter_upwards [eventually_ge_atTop (S.biUnion fun α => Finset.univ.image α)] with D hD
  intro α hα
  refine Fintype.mem_piFinset.mpr fun k => hD ?_
  exact Finset.mem_biUnion.mpr ⟨α, hα, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
private theorem tendsto_partial_cyclicTrace {m : ℕ} {B : Fin m → 𝔸 → 𝔸 → ℂ}
    (hB : CyclicTraceConverges B) :
    Tendsto (fun D : Finset 𝔸 =>
        ∑ α ∈ Fintype.piFinset (fun _ : Fin m => D), cyclicTraceTerm B α)
      atTop (𝓝 (cyclicTrace B)) := by
  have h : HasSum (cyclicTraceTerm B) (cyclicTrace B) := (Summable.of_norm hB).hasSum
  have h' : Tendsto (fun s : Finset (Fin m → 𝔸) => ∑ α ∈ s, cyclicTraceTerm B α) atTop
      (𝓝 (cyclicTrace B)) := by
    rw [HasSum, SummationFilter.unconditional_filter] at h
    exact h
  exact h'.comp (tendsto_piFinset_atTop m)
private theorem frobSq_restrictKernel_le {A : 𝔸 → 𝔸 → ℂ} (hA : IsSqSummable A) (D : Finset 𝔸) :
    frobSq (restrictKernel (fun a b => ((‖A a b‖ : ℝ) : ℂ)) D) ≤
      ∑' p : 𝔸 × 𝔸, ‖A p.1 p.2‖ ^ 2 := by
  have hinj : Function.Injective (fun p : D × D => ((p.1 : 𝔸), (p.2 : 𝔸))) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  have := tsum_comp_le_tsum_of_inj hA (fun _ => by positivity) hinj
  rw [tsum_fintype] at this
  simpa [frobSq, restrictKernel] using this
private def extendByZero {m : ℕ} (B : Fin m → 𝔸 → 𝔸 → ℂ) : ℕ → 𝔸 → 𝔸 → ℂ :=
  fun i => if h : i < m then B ⟨i, h⟩ else 0
private theorem extendByZero_val {m : ℕ} (B : Fin m → 𝔸 → 𝔸 → ℂ) (k : Fin m) :
    extendByZero B k = B k := by
  simp [extendByZero]
private theorem extendByZero_family {m : ℕ} (B : Fin m → 𝔸 → 𝔸 → ℂ) :
    (fun k : Fin m => extendByZero B k) = B := funext (extendByZero_val B)
private theorem summable_and_tsum_abs_le {m : ℕ} (hm : 2 ≤ m) {B : Fin m → 𝔸 → 𝔸 → ℂ}
    (hB : ∀ k, IsSqSummable (B k)) :
    Summable (fun α : Fin m → 𝔸 => ∏ k : Fin m, ‖B k (α k) (α (finRotate m k))‖) ∧
      ∑' α : Fin m → 𝔸, ∏ k : Fin m, ‖B k (α k) (α (finRotate m k))‖ ≤
        ∏ k : Fin m, hsNorm (B k) := by
  set F : (Fin m → 𝔸) → ℝ := fun α => ∏ k : Fin m, ‖B k (α k) (α (finRotate m k))‖ with hF
  have hF0 : ∀ α, 0 ≤ F α := fun α => Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hD : ∀ D : Finset 𝔸, ∑ α ∈ Fintype.piFinset (fun _ : Fin m => D), F α ≤
      ∏ k : Fin m, hsNorm (B k) := by
    intro D
    let Bn : ℕ → 𝔸 → 𝔸 → ℂ := fun i a b => ((‖extendByZero B i a b‖ : ℝ) : ℂ)
    have h1 := sum_piFinset_eq_trace_restrict Bn (by omega : 1 ≤ m) D
    have h2 : ∀ α : Fin m → 𝔸, cyclicTraceTerm (fun k : Fin m => Bn k) α = ((F α : ℝ) : ℂ) := by
      intro α
      simp only [cyclicTraceTerm, Bn, extendByZero_val, hF]
      push_cast
      rfl
    simp_rw [h2] at h1
    rw [← Complex.ofReal_sum] at h1
    have h3 : ∑ α ∈ Fintype.piFinset (fun _ : Fin m => D), F α =
        ‖Matrix.trace (orderedProd (fun i => restrictKernel (Bn i) D) m)‖ := by
      rw [← h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun α _ => hF0 α)]
    rw [h3]
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
    refine (norm_trace_le_prod_frobSq _ M).trans ?_
    rw [← Fin.prod_univ_eq_prod_range
      (fun i => frobSq (restrictKernel (Bn i) D) ^ (1 / 2 : ℝ)) (M + 2)]
    refine Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (frobSq_nonneg _) _) fun k _ => ?_
    have h4 : frobSq (restrictKernel (Bn k) D) ≤ ∑' p : 𝔸 × 𝔸, ‖B k p.1 p.2‖ ^ 2 := by
      have := frobSq_restrictKernel_le (hB k) D
      simpa only [Bn, extendByZero_val] using this
    exact Real.rpow_le_rpow (frobSq_nonneg _) h4 (by norm_num)
  have hS : ∀ S : Finset (Fin m → 𝔸), ∑ α ∈ S, F α ≤ ∏ k : Fin m, hsNorm (B k) := by
    intro S
    have hev := (tendsto_piFinset_atTop (𝔸 := 𝔸) m).eventually (eventually_ge_atTop S)
    obtain ⟨D, hDS⟩ := hev.exists
    exact (Finset.sum_le_sum_of_subset_of_nonneg hDS fun α _ _ => hF0 α).trans (hD D)
  have hsum : Summable F := summable_of_sum_le hF0 hS
  exact ⟨hsum, hsum.tsum_le_of_sum_le hS⟩
private theorem cyclicTraceConverges_of_sq {m : ℕ} (hm : 2 ≤ m) {B : Fin m → 𝔸 → 𝔸 → ℂ}
    (hB : ∀ k, IsSqSummable (B k)) : CyclicTraceConverges B := by
  have h := (summable_and_tsum_abs_le hm hB).1
  refine h.congr fun α => ?_
  simp [cyclicTraceTerm, norm_prod]
private theorem norm_cyclicTrace_le {m : ℕ} (hm : 2 ≤ m) {B : Fin m → 𝔸 → 𝔸 → ℂ}
    (hB : ∀ k, IsSqSummable (B k)) : ‖cyclicTrace B‖ ≤ ∏ k : Fin m, hsNorm (B k) := by
  have hf := cyclicTraceConverges_of_sq hm hB
  refine (norm_tsum_le_tsum_norm hf).trans
    (le_trans (le_of_eq ?_) (summable_and_tsum_abs_le hm hB).2)
  refine tsum_congr fun α => ?_
  simp [cyclicTraceTerm, norm_prod]
private theorem isSqSummable_adjointKernel {A : 𝔸 → 𝔸 → ℂ} (hA : IsSqSummable A) :
    IsSqSummable (adjointKernel A) := by
  have := (Equiv.prodComm 𝔸 𝔸).summable_iff.mpr hA
  refine this.congr fun p => ?_
  simp [adjointKernel]
private theorem hsNorm_adjointKernel (A : 𝔸 → 𝔸 → ℂ) : hsNorm (adjointKernel A) = hsNorm A := by
  have := (Equiv.prodComm 𝔸 𝔸).tsum_eq (fun p : 𝔸 × 𝔸 => ‖A p.1 p.2‖ ^ 2)
  simp only [hsNorm, adjointKernel, RCLike.norm_conj]
  rw [← this]
  rfl
private theorem adjointKernel_adjointKernel (A : 𝔸 → 𝔸 → ℂ) :
    adjointKernel (adjointKernel A) = A := by
  funext a b
  simp [adjointKernel]
private theorem cyclicTrace_rotate {m : ℕ} (B : Fin m → 𝔸 → 𝔸 → ℂ) :
    cyclicTrace (fun k => B (finRotate m k)) = cyclicTrace B := by
  have h := (Equiv.arrowCongr (finRotate m) (Equiv.refl 𝔸)).tsum_eq (cyclicTraceTerm B)
  rw [cyclicTrace, cyclicTrace, ← h]
  refine tsum_congr fun α => ?_
  simp only [cyclicTraceTerm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, id]
  rw [← Equiv.prod_comp (finRotate m) (fun k => B k (α ((finRotate m).symm k))
    (α ((finRotate m).symm (finRotate m k))))]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Equiv.symm_apply_apply]
private theorem finRotate_rev_finRotate {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    finRotate m (Fin.rev (finRotate m k)) = Fin.rev k := by
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have := k.2
  apply Fin.ext
  simp only [coe_finRotate, Fin.val_rev, Fin.ext_iff, Fin.val_last]
  split_ifs <;> omega
private theorem conj_cyclicTrace {m : ℕ} (hm : 1 ≤ m) (B : Fin m → 𝔸 → 𝔸 → ℂ) :
    conj (cyclicTrace B) = cyclicTrace (fun k => adjointKernel (B (Fin.rev k))) := by
  let σ : Equiv.Perm (Fin m) := Fin.revPerm.trans (finRotate m)
  have h := (Equiv.arrowCongr σ.symm (Equiv.refl 𝔸)).tsum_eq
    (cyclicTraceTerm (fun k => adjointKernel (B (Fin.rev k))))
  rw [cyclicTrace, cyclicTrace, Complex.conj_tsum, ← h]
  refine tsum_congr fun α => ?_
  simp only [cyclicTraceTerm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, id,
    map_prod, adjointKernel, Equiv.symm_symm]
  rw [← Equiv.prod_comp Fin.revPerm (fun k => conj (B k (α k) (α (finRotate m k))))]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, σ, Equiv.trans_apply, finRotate_rev_finRotate hm]
end Kernels
section Limits
open Filter Topology
variable {𝔸 : Type} [Countable 𝔸] [Nonempty 𝔸] [DecidableEq 𝔸]
private theorem sum_piFinset_alternating (A : 𝔸 → 𝔸 → ℂ) {n : ℕ} (hn : 1 ≤ n) (D : Finset 𝔸) :
    ∑ α ∈ Fintype.piFinset (fun _ : Fin (2 * n) => D),
        cyclicTraceTerm (alternatingKernels A (2 * n)) α =
      ((gramTrace (restrictKernel A D) n : ℝ) : ℂ) := by
  refine (sum_piFinset_eq_trace_restrict (fun i => if Even i then A else adjointKernel A)
    (by omega : 1 ≤ 2 * n) D).trans ?_
  rw [← trace_gram_pow, ← orderedProd_alternating]
  congr 2
  funext i
  by_cases c : Even i
  · simp [c]
  · simp [c, restrictKernel_adjointKernel]
private theorem cyclicTraceConverges_alternating {A : 𝔸 → 𝔸 → ℂ} (hA : IsSqSummable A) {m : ℕ}
    (hm : 2 ≤ m) : CyclicTraceConverges (alternatingKernels A m) := by
  refine cyclicTraceConverges_of_sq hm fun k => ?_
  simp only [alternatingKernels]
  split_ifs
  · exact hA
  · exact isSqSummable_adjointKernel hA
private theorem exists_limit_alternating {A : 𝔸 → 𝔸 → ℂ} (hA : IsSqSummable A) {n : ℕ}
    (hn : 1 ≤ n) : ∃ x : ℝ, 0 ≤ x ∧ alternatingCyclicTrace A (2 * n) = (x : ℂ) ∧
      Tendsto (fun D : Finset 𝔸 => gramTrace (restrictKernel A D) n) atTop (𝓝 x) := by
  have ht := tendsto_partial_cyclicTrace
    (cyclicTraceConverges_alternating hA (by omega : 2 ≤ 2 * n))
  simp_rw [sum_piFinset_alternating A hn] at ht
  have hre : Tendsto (fun D : Finset 𝔸 => gramTrace (restrictKernel A D) n) atTop
      (𝓝 (alternatingCyclicTrace A (2 * n)).re) := by
    exact Tendsto.congr (fun D => by simp) ((Complex.continuous_re.tendsto _).comp ht)
  have him : Tendsto (fun _ : Finset 𝔸 => (0 : ℝ)) atTop
      (𝓝 (alternatingCyclicTrace A (2 * n)).im) := by
    exact Tendsto.congr (fun D => by simp) ((Complex.continuous_im.tendsto _).comp ht)
  refine ⟨_, ge_of_tendsto' hre fun D => gramTrace_nonneg _ _, ?_, hre⟩
  apply Complex.ext
  · simp
  · simpa using (tendsto_nhds_unique him tendsto_const_nhds)
private theorem schattenEvenNorm_eq {A : 𝔸 → 𝔸 → ℂ} {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x)
    (hx : alternatingCyclicTrace A (2 * n) = (x : ℂ)) :
    schattenEvenNorm A (2 * n) = x ^ (1 / ((2 * n : ℕ) : ℝ)) := by
  rw [schattenEvenNorm, hx, Complex.norm_real, Real.norm_of_nonneg hx0]
private theorem schattenEvenNorm_pow {A : 𝔸 → 𝔸 → ℂ} {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : alternatingCyclicTrace A (2 * n) = (x : ℂ)) :
    schattenEvenNorm A (2 * n) ^ (2 * n) = x := by
  have hn0 : (((2 * n : ℕ) : ℝ)) ≠ 0 := by
    have : 2 * n ≠ 0 := by omega
    exact_mod_cast this
  rw [schattenEvenNorm_eq hx0 hx, ← Real.rpow_natCast, ← Real.rpow_mul hx0, one_div,
    inv_mul_cancel₀ hn0, Real.rpow_one]
private theorem norm_cyclicTrace_le_schatten {n : ℕ} (hn : 1 ≤ n) {B : Fin (2 * n) → 𝔸 → 𝔸 → ℂ}
    (hB : ∀ k, IsSqSummable (B k)) :
    ‖cyclicTrace B‖ ≤ ∏ k : Fin (2 * n), schattenEvenNorm (B k) (2 * n) := by
  have hfam : ∀ D : Finset 𝔸,
      ∑ α ∈ Fintype.piFinset (fun _ : Fin (2 * n) => D), cyclicTraceTerm B α =
        Matrix.trace (orderedProd (fun i => restrictKernel (extendByZero B i) D) (2 * n)) := by
    intro D
    have := sum_piFinset_eq_trace_restrict (extendByZero B) (by omega : 1 ≤ 2 * n) D
    rwa [extendByZero_family] at this
  have hL := (tendsto_partial_cyclicTrace (cyclicTraceConverges_of_sq (by omega : 2 ≤ 2 * n) hB)).norm
  simp_rw [hfam] at hL
  have hR : Tendsto (fun D : Finset 𝔸 => ∏ k ∈ Finset.range (2 * n),
      gramTrace (restrictKernel (extendByZero B k) D) n ^ (1 / ((2 * n : ℕ) : ℝ))) atTop
      (𝓝 (∏ k ∈ Finset.range (2 * n), schattenEvenNorm (extendByZero B k) (2 * n))) := by
    refine tendsto_finsetProd _ fun k hk => ?_
    have hk' : k < 2 * n := Finset.mem_range.mp hk
    have hs : IsSqSummable (extendByZero B k) := by
      have := extendByZero_val B ⟨k, hk'⟩
      simp only at this
      rw [this]
      exact hB _
    obtain ⟨x, hx0, hx, hxt⟩ := exists_limit_alternating hs hn
    rw [schattenEvenNorm_eq hx0 hx]
    exact hxt.rpow_const (Or.inr (by positivity))
  have hfin := le_of_tendsto_of_tendsto' hL hR fun D => norm_trace_orderedProd_le_holder hn _
  rw [← Fin.prod_univ_eq_prod_range (fun i => schattenEvenNorm (extendByZero B i) (2 * n))
    (2 * n)] at hfin
  simpa only [extendByZero_val] using hfin
private theorem schattenEvenNorm_mul_pow_le {A : 𝔸 → 𝔸 → ℂ} (hA : IsSqSummable A) {n : ℕ}
    (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) :
    schattenEvenNorm A (j * (2 * n)) ^ (j * (2 * n)) ≤
      (schattenEvenNorm A (2 * n) ^ (2 * n)) ^ j := by
  have hjn : 1 ≤ j * n := Nat.mul_pos hj hn
  rw [show j * (2 * n) = 2 * (j * n) by ring]
  obtain ⟨x, hx0, hx, hxt⟩ := exists_limit_alternating hA hn
  obtain ⟨y, hy0, hy, hyt⟩ := exists_limit_alternating hA hjn
  rw [schattenEvenNorm_pow hn hx0 hx, schattenEvenNorm_pow hjn hy0 hy]
  exact le_of_tendsto_of_tendsto' hyt (hxt.pow j) fun D => gramTrace_mul_le _ n j hj
end Limits
theorem cyclicTraceProductBounds_holds : CyclicTraceProductBounds := by
  intro 𝔸 _ _ m hm A B hA hB
  classical
  refine ⟨⟨(summable_and_tsum_abs_le hm hB).1, (summable_and_tsum_abs_le hm hB).2,
      cyclicTraceConverges_of_sq hm hB, norm_cyclicTrace_le hm hB⟩,
    ⟨isSqSummable_adjointKernel hA, hsNorm_adjointKernel A, adjointKernel_adjointKernel A,
      cyclicTrace_rotate B, conj_cyclicTrace (by omega) B⟩, ?_⟩
  intro hEven
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := even_iff_exists_two_mul.mp hEven
  have hn : 1 ≤ n := by omega
  obtain ⟨x, hx0, hx, hxt⟩ := exists_limit_alternating hA hn
  obtain ⟨y, hy0, hy, hyt⟩ := exists_limit_alternating (isSqSummable_adjointKernel hA) hn
  have hxy : y = x := by
    refine tendsto_nhds_unique hyt ?_
    refine hxt.congr fun D => ?_
    rw [restrictKernel_adjointKernel, gramTrace_conjTranspose _ hn]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, norm_cyclicTrace_le_schatten hn hB,
    fun j hj => schattenEvenNorm_mul_pow_le hA hn hj⟩
  · rw [hx]
    simp
  · rw [hx]
    simpa using hx0
  · rw [schattenEvenNorm_pow hn hx0 hx, hx]
  · rw [schattenEvenNorm_eq hx0 hx, schattenEvenNorm_eq hy0 hy, hxy]
end YangMills.Construction.SquareSummable.CyclicTraceProducts
