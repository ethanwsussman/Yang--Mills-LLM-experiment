import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.Weighted.BoxPoincare
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.BoxPoincare
abbrev symmetricInterval (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) M
theorem mem_integerBox_iff {M : ℕ} {k : Fin 4 → ℤ} :
    k ∈ integerBox M ↔ ∀ ν, k ν ∈ symmetricInterval M := by
  simp only [integerBox, Fintype.mem_piFinset]
theorem card_symmetricInterval (M : ℕ) :
    ((symmetricInterval M).card : ℝ) = 2 * (M : ℝ) + 1 := by
  have hc : (symmetricInterval M).card = 2 * M + 1 := by
    simp only [symmetricInterval, Int.card_Icc]
    omega
  rw [hc]
  push_cast
  ring
theorem card_integerBox (M : ℕ) : ((integerBox M).card : ℝ) = (2 * (M : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
theorem update_mem_integerBox {M : ℕ} {μ : Fin 4} {x : Fin 4 → ℤ} {s : ℤ}
    (hx : x ∈ integerBox M) (hs : s ∈ symmetricInterval M) :
    Function.update x μ s ∈ integerBox M := by
  rw [mem_integerBox_iff] at hx ⊢
  intro ν
  by_cases hν : ν = μ
  · subst hν
    simpa using hs
  · simpa [Function.update_of_ne hν] using hx ν
theorem sum_update_involution (M : ℕ) (μ : Fin 4) (H : (Fin 4 → ℤ) → ℤ → ℝ) :
    ∑ x ∈ integerBox M, ∑ s ∈ symmetricInterval M, H (Function.update x μ s) (x μ) =
      ∑ x ∈ integerBox M, ∑ s ∈ symmetricInterval M, H x s := by
  rw [← Finset.sum_product' (integerBox M) (symmetricInterval M)
      (fun x s => H (Function.update x μ s) (x μ)),
    ← Finset.sum_product' (integerBox M) (symmetricInterval M) H]
  have hmem : ∀ p ∈ integerBox M ×ˢ symmetricInterval M,
      ((Function.update p.1 μ p.2, p.1 μ) : (Fin 4 → ℤ) × ℤ) ∈
        integerBox M ×ˢ symmetricInterval M := by
    rintro ⟨x, s⟩ hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨update_mem_integerBox hp.1 hp.2, mem_integerBox_iff.1 hp.1 μ⟩
  have hinv : ∀ p : (Fin 4 → ℤ) × ℤ,
      ((Function.update (Function.update p.1 μ p.2) μ (p.1 μ),
        Function.update p.1 μ p.2 μ) : (Fin 4 → ℤ) × ℤ) = p := by
    rintro ⟨x, s⟩
    simp
  exact Finset.sum_nbij' (fun p => (Function.update p.1 μ p.2, p.1 μ))
    (fun p => (Function.update p.1 μ p.2, p.1 μ)) hmem hmem
    (fun p _ => hinv p) (fun p _ => hinv p) (fun _ _ => rfl)
def coordSplice (j : ℕ) (k l : Fin 4 → ℤ) : Fin 4 → ℤ := fun ν => if ν.val < j then l ν else k ν
theorem coordSplice_mem_integerBox {M : ℕ} (j : ℕ) {k l : Fin 4 → ℤ} (hk : k ∈ integerBox M)
    (hl : l ∈ integerBox M) : coordSplice j k l ∈ integerBox M := by
  rw [mem_integerBox_iff] at hk hl ⊢
  intro ν
  by_cases hν : ν.val < j
  · simpa [coordSplice, hν] using hl ν
  · simpa [coordSplice, hν] using hk ν
theorem sum_coordSplice_involution (M j : ℕ) (F : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ) :
    ∑ k ∈ integerBox M, ∑ l ∈ integerBox M, F (coordSplice j k l) (coordSplice j l k) =
      ∑ k ∈ integerBox M, ∑ l ∈ integerBox M, F k l := by
  rw [← Finset.sum_product' (integerBox M) (integerBox M)
      (fun k l => F (coordSplice j k l) (coordSplice j l k)),
    ← Finset.sum_product' (integerBox M) (integerBox M) F]
  have hmem : ∀ p ∈ integerBox M ×ˢ integerBox M,
      ((coordSplice j p.1 p.2, coordSplice j p.2 p.1) : (Fin 4 → ℤ) × (Fin 4 → ℤ)) ∈
        integerBox M ×ˢ integerBox M := by
    rintro ⟨k, l⟩ hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨coordSplice_mem_integerBox j hp.1 hp.2, coordSplice_mem_integerBox j hp.2 hp.1⟩
  have hinv : ∀ p : (Fin 4 → ℤ) × (Fin 4 → ℤ),
      ((coordSplice j (coordSplice j p.1 p.2) (coordSplice j p.2 p.1),
        coordSplice j (coordSplice j p.2 p.1) (coordSplice j p.1 p.2)) :
          (Fin 4 → ℤ) × (Fin 4 → ℤ)) = p := by
    rintro ⟨k, l⟩
    refine Prod.ext (funext fun ν => ?_) (funext fun ν => ?_) <;>
      by_cases hν : ν.val < j <;> simp [coordSplice, hν]
  exact Finset.sum_nbij' (fun p => (coordSplice j p.1 p.2, coordSplice j p.2 p.1))
    (fun p => (coordSplice j p.1 p.2, coordSplice j p.2 p.1)) hmem hmem
    (fun p _ => hinv p) (fun p _ => hinv p) (fun _ _ => rfl)
theorem sum_integerBox_coord (M : ℕ) (μ : Fin 4) (ψ : ℤ → ℝ) :
    ∑ l ∈ integerBox M, ψ (l μ) =
      (2 * (M : ℝ) + 1) ^ 3 * ∑ t ∈ symmetricInterval M, ψ t := by
  have h := Finset.prod_univ_sum (fun _ : Fin 4 => symmetricInterval M)
    (fun ν s => if ν = μ then ψ s else (1 : ℝ))
  have hrhs : ∀ x : Fin 4 → ℤ, ∏ ν, (if ν = μ then ψ (x ν) else (1 : ℝ)) = ψ (x μ) := by
    intro x
    rw [Finset.prod_ite_eq' Finset.univ μ (fun ν => ψ (x ν))]
    simp
  simp only [hrhs] at h
  have hlhs : ∀ ν : Fin 4, ∑ s ∈ symmetricInterval M, (if ν = μ then ψ s else (1 : ℝ)) =
      if ν = μ then ∑ s ∈ symmetricInterval M, ψ s else 2 * (M : ℝ) + 1 := by
    intro ν
    by_cases hν : ν = μ
    · simp [hν]
    · simp only [hν, if_false, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact card_symmetricInterval M
  simp only [hlhs] at h
  change _ = ∑ l ∈ integerBox M, ψ (l μ) at h
  rw [← h]
  generalize ∑ s ∈ symmetricInterval M, ψ s = A
  generalize 2 * (M : ℝ) + 1 = N
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ), if_pos rfl,
    Finset.prod_congr rfl (g := fun _ => N) (fun ν hν => if_neg (Finset.ne_of_mem_erase hν)),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ μ), Finset.card_univ,
    Fintype.card_fin]
  show A * N ^ 3 = N ^ 3 * A
  ring
theorem two_mul_sum_sq_sub_mean (B : Finset (Fin 4 → ℤ)) (g : (Fin 4 → ℤ) → ℝ) (m n : ℝ)
    (hn : (B.card : ℝ) = n) (hn0 : 0 < n) (hm : m = n⁻¹ * ∑ k ∈ B, g k) :
    2 * n * ∑ k ∈ B, (g k - m) ^ 2 = ∑ k ∈ B, ∑ l ∈ B, (g k - g l) ^ 2 := by
  have hS : ∑ k ∈ B, g k = n * m := by
    rw [hm]
    field_simp
  have e1 : ∑ k ∈ B, (g k - m) ^ 2 = ∑ k ∈ B, g k ^ 2 - 2 * m * ∑ k ∈ B, g k + n * m ^ 2 := by
    calc ∑ k ∈ B, (g k - m) ^ 2 = ∑ k ∈ B, (g k ^ 2 - 2 * m * g k + m ^ 2) :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul, hn]
  have e2 : ∀ k, ∑ l ∈ B, (g k - g l) ^ 2 =
      n * g k ^ 2 - 2 * (∑ l ∈ B, g l) * g k + ∑ l ∈ B, g l ^ 2 := by
    intro k
    calc ∑ l ∈ B, (g k - g l) ^ 2 = ∑ l ∈ B, (g k ^ 2 - 2 * g k * g l + g l ^ 2) :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul, hn]
          ring
  simp only [e2]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hn, e1, hS]
  ring
def edgeEnergy (M : ℕ) (f : ℤ → ℝ) : ℝ :=
  ∑ u ∈ Finset.Ico (-(M : ℤ)) M, (f (u + 1) - f u) ^ 2
theorem edgeEnergy_nonneg (M : ℕ) (f : ℤ → ℝ) : 0 ≤ edgeEnergy M f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem sum_Ico_forward_diff (f : ℤ → ℝ) {s t : ℤ} (hst : s ≤ t) :
    ∑ u ∈ Finset.Ico s t, (f (u + 1) - f u) = f t - f s := by
  induction t, hst using Int.le_induction with
  | base => simp
  | succ t hst ih =>
    have hI : Finset.Ico s (t + 1) = insert t (Finset.Ico s t) := by
      ext u
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    ring
theorem sq_sub_le_mul_edgeEnergy (M : ℕ) (f : ℤ → ℝ) {s t : ℤ} (hs : s ∈ symmetricInterval M)
    (ht : t ∈ symmetricInterval M) (hst : s ≤ t) :
    (f t - f s) ^ 2 ≤ ((t - s : ℤ) : ℝ) * edgeEnergy M f := by
  rw [← sum_Ico_forward_diff f hst]
  have hs' := Finset.mem_Icc.1 hs
  have ht' := Finset.mem_Icc.1 ht
  have hcard : ((Finset.Ico s t).card : ℝ) = ((t - s : ℤ) : ℝ) := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ t - s)
  have hsub : Finset.Ico s t ⊆ Finset.Ico (-(M : ℤ)) M := by
    intro u hu
    have hu' := Finset.mem_Ico.1 hu
    exact Finset.mem_Ico.2 (by omega)
  have hE : ∑ u ∈ Finset.Ico s t, (f (u + 1) - f u) ^ 2 ≤ edgeEnergy M f :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hnn : (0 : ℝ) ≤ ((t - s : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ t - s)
  calc (∑ u ∈ Finset.Ico s t, (f (u + 1) - f u)) ^ 2
      ≤ ((Finset.Ico s t).card : ℝ) * ∑ u ∈ Finset.Ico s t, (f (u + 1) - f u) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left hE hnn
theorem sq_sub_le_abs_add_mul (M : ℕ) (f : ℤ → ℝ) {s t : ℤ} (hs : s ∈ symmetricInterval M)
    (ht : t ∈ symmetricInterval M) :
    (f s - f t) ^ 2 ≤ (|(s : ℝ)| + |(t : ℝ)|) * edgeEnergy M f := by
  have hE := edgeEnergy_nonneg M f
  have hdiff : ∀ a b : ℤ, ((a - b : ℤ) : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| := by
    intro a b
    push_cast
    have := le_abs_self (a : ℝ)
    have := neg_abs_le (b : ℝ)
    linarith
  rcases le_total s t with hst | hts
  · calc (f s - f t) ^ 2 = (f t - f s) ^ 2 := by ring
      _ ≤ ((t - s : ℤ) : ℝ) * edgeEnergy M f := sq_sub_le_mul_edgeEnergy M f hs ht hst
      _ ≤ (|(t : ℝ)| + |(s : ℝ)|) * edgeEnergy M f :=
          mul_le_mul_of_nonneg_right (hdiff t s) hE
      _ = _ := by ring
  · exact (sq_sub_le_mul_edgeEnergy M f ht hs hts).trans
      (mul_le_mul_of_nonneg_right (hdiff s t) hE)
theorem sum_abs_symmetricInterval (M : ℕ) :
    ∑ s ∈ symmetricInterval M, |(s : ℝ)| = (M : ℝ) * ((M : ℝ) + 1) := by
  induction M with
  | zero => simp [symmetricInterval]
  | succ n ih =>
    have hI : symmetricInterval (n + 1) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (symmetricInterval n)) := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : (-((n : ℤ) + 1)) ∉ symmetricInterval n := by
      simp only [Finset.mem_Icc]
      omega
    have h2 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (symmetricInterval n) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [hI, Finset.sum_insert h2, Finset.sum_insert h1, ih]
    push_cast
    rw [abs_neg, abs_of_nonneg hpos]
    ring
theorem sum_sum_sq_sub_le_edgeEnergy (M : ℕ) (f : ℤ → ℝ) :
    ∑ s ∈ symmetricInterval M, ∑ t ∈ symmetricInterval M, (f s - f t) ^ 2 ≤
      (2 * (M : ℝ) + 1) ^ 3 / 2 * edgeEnergy M f := by
  have hE := edgeEnergy_nonneg M f
  have hM : (0 : ℝ) ≤ (M : ℝ) := by positivity
  calc ∑ s ∈ symmetricInterval M, ∑ t ∈ symmetricInterval M, (f s - f t) ^ 2
      ≤ ∑ s ∈ symmetricInterval M, ∑ t ∈ symmetricInterval M,
          (|(s : ℝ)| + |(t : ℝ)|) * edgeEnergy M f :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun t ht =>
          sq_sub_le_abs_add_mul M f hs ht
    _ = 2 * (2 * (M : ℝ) + 1) * ((M : ℝ) * ((M : ℝ) + 1)) * edgeEnergy M f := by
        simp only [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum, card_symmetricInterval, sum_abs_symmetricInterval]
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hE
        nlinarith [mul_nonneg hM hM]
theorem update_add_single_one (x : Fin 4 → ℤ) (μ : Fin 4) (s : ℤ) :
    Function.update x μ s + Pi.single μ 1 = Function.update x μ (s + 1) := by
  ext ν
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [Function.update_of_ne hν, Pi.single_eq_of_ne hν]
theorem sum_edgeEnergy_lines (M : ℕ) (μ : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ x ∈ integerBox M, edgeEnergy M (fun s => g (Function.update x μ s)) =
      (2 * (M : ℝ) + 1) *
        ∑ k ∈ (integerBox M).filter (fun k => k + Pi.single μ 1 ∈ integerBox M),
          (g (k + Pi.single μ 1) - g k) ^ 2 := by
  have hfilter :
      ∑ k ∈ (integerBox M).filter (fun k => k + Pi.single μ 1 ∈ integerBox M),
          (g (k + Pi.single μ 1) - g k) ^ 2 =
        ∑ k ∈ integerBox M,
          if k μ < (M : ℤ) then (g (k + Pi.single μ 1) - g k) ^ 2 else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := mem_integerBox_iff.1 hk
    have hiff : k + Pi.single μ 1 ∈ integerBox M ↔ k μ < (M : ℤ) := by
      constructor
      · intro hmem
        have h1 := (Finset.mem_Icc.1 (mem_integerBox_iff.1 hmem μ)).2
        simp only [Pi.add_apply, Pi.single_eq_same] at h1
        omega
      · intro hlt
        refine mem_integerBox_iff.2 fun ν => ?_
        by_cases hν : ν = μ
        · subst hν
          have h1 := Finset.mem_Icc.1 (hk' ν)
          simp only [Pi.add_apply, Pi.single_eq_same]
          exact Finset.mem_Icc.2 (by omega)
        · simpa [Pi.single_eq_of_ne hν] using hk' ν
    simp only [hiff]
  have hswap := sum_update_involution M μ (fun x _ =>
    if x μ < (M : ℤ) then (g (x + Pi.single μ 1) - g x) ^ 2 else 0)
  simp only [Finset.sum_const, nsmul_eq_mul, card_symmetricInterval] at hswap
  rw [hfilter, Finset.mul_sum, ← hswap]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Function.update_self, update_add_single_one]
  have hI : (symmetricInterval M).filter (fun s => s < (M : ℤ)) = Finset.Ico (-(M : ℤ)) M := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hI]
  rfl
theorem sum_sq_sub_along_lines_le (M : ℕ) (μ : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ x ∈ integerBox M, ∑ t ∈ symmetricInterval M, (g x - g (Function.update x μ t)) ^ 2 ≤
      (2 * (M : ℝ) + 1) ^ 3 / 2 *
        ∑ k ∈ (integerBox M).filter (fun k => k + Pi.single μ 1 ∈ integerBox M),
          (g (k + Pi.single μ 1) - g k) ^ 2 := by
  have hN : 0 < 2 * (M : ℝ) + 1 := by positivity
  have hswap := sum_update_involution M μ (fun x _ =>
    ∑ t ∈ symmetricInterval M, (g x - g (Function.update x μ t)) ^ 2)
  have hconst : ∑ x ∈ integerBox M, ∑ _s ∈ symmetricInterval M,
      ∑ t ∈ symmetricInterval M, (g x - g (Function.update x μ t)) ^ 2 =
      (2 * (M : ℝ) + 1) * ∑ x ∈ integerBox M, ∑ t ∈ symmetricInterval M,
        (g x - g (Function.update x μ t)) ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, card_symmetricInterval, Finset.mul_sum]
  have hline : ∀ x : Fin 4 → ℤ, ∑ s ∈ symmetricInterval M, ∑ t ∈ symmetricInterval M,
      (g (Function.update x μ s) - g (Function.update (Function.update x μ s) μ t)) ^ 2 ≤
      (2 * (M : ℝ) + 1) ^ 3 / 2 * edgeEnergy M (fun s => g (Function.update x μ s)) := by
    intro x
    simp only [Function.update_idem]
    exact sum_sum_sq_sub_le_edgeEnergy M _
  refine le_of_mul_le_mul_left ?_ hN
  rw [← hconst, ← hswap, mul_left_comm, ← sum_edgeEnergy_lines, Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => hline x
theorem coordSplice_succ (μ : Fin 4) (k l : Fin 4 → ℤ) :
    coordSplice (μ.val + 1) k l =
      Function.update (coordSplice μ.val k l) μ (coordSplice μ.val l k μ) := by
  ext ν
  by_cases hν : ν = μ
  · subst hν
    simp [coordSplice]
  · have hv : ν.val ≠ μ.val := fun e => hν (Fin.ext e)
    have hiff : ν.val < μ.val + 1 ↔ ν.val < μ.val := by omega
    simp [coordSplice, Function.update_of_ne hν, hiff]
theorem sq_sub_le_four_mul_sum_coordSplice (g : (Fin 4 → ℤ) → ℝ) (k l : Fin 4 → ℤ) :
    (g k - g l) ^ 2 ≤
      4 * ∑ μ : Fin 4, (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2 := by
  have h0 : coordSplice 0 k l = k := by
    ext ν
    simp [coordSplice]
  have h4 : coordSplice 4 k l = l := by
    ext ν
    simp [coordSplice, ν.isLt]
  have hsum : g k - g l =
      ∑ μ : Fin 4, (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) := by
    rw [Fin.sum_univ_four]
    show g k - g l = (g (coordSplice 0 k l) - g (coordSplice 1 k l)) +
      (g (coordSplice 1 k l) - g (coordSplice 2 k l)) +
      (g (coordSplice 2 k l) - g (coordSplice 3 k l)) +
      (g (coordSplice 3 k l) - g (coordSplice 4 k l))
    rw [h0, h4]
    ring
  rw [hsum]
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4)))
    (f := fun μ : Fin 4 => g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l))
  simpa using h
theorem sum_coordSplice_step (M : ℕ) (μ : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
        (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2 =
      (2 * (M : ℝ) + 1) ^ 3 * ∑ x ∈ integerBox M, ∑ t ∈ symmetricInterval M,
        (g x - g (Function.update x μ t)) ^ 2 := by
  have h := sum_coordSplice_involution M μ.val
    (fun x y => (g x - g (Function.update x μ (y μ))) ^ 2)
  calc ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
        (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2
      = ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
          (g k - g (Function.update k μ (l μ))) ^ 2 := by
        rw [← h]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [coordSplice_succ]
    _ = ∑ k ∈ integerBox M, (2 * (M : ℝ) + 1) ^ 3 * ∑ t ∈ symmetricInterval M,
          (g k - g (Function.update k μ t)) ^ 2 :=
        Finset.sum_congr rfl fun k _ =>
          sum_integerBox_coord M μ (fun t => (g k - g (Function.update k μ t)) ^ 2)
    _ = _ := (Finset.mul_sum _ _ _).symm
theorem boxPoincareInequality_holds : BoxPoincareInequality := by
  intro M g m hm
  have hvar := two_mul_sum_sq_sub_mean (integerBox M) g m ((2 * (M : ℝ) + 1) ^ 4)
    (card_integerBox M) (by positivity) hm
  have hsteps : ∑ k ∈ integerBox M, ∑ l ∈ integerBox M, (g k - g l) ^ 2 ≤
      4 * ∑ μ : Fin 4, ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
        (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2 := by
    calc ∑ k ∈ integerBox M, ∑ l ∈ integerBox M, (g k - g l) ^ 2
        ≤ ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
            4 * ∑ μ : Fin 4, (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2 :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
            sq_sub_le_four_mul_sum_coordSplice g k l
      _ = _ := by
          simp only [← Finset.mul_sum]
          rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  have hlines : ∑ μ : Fin 4, ∑ k ∈ integerBox M, ∑ l ∈ integerBox M,
        (g (coordSplice μ.val k l) - g (coordSplice (μ.val + 1) k l)) ^ 2 ≤
      ∑ μ : Fin 4, (2 * (M : ℝ) + 1) ^ 3 * ((2 * (M : ℝ) + 1) ^ 3 / 2 *
        ∑ k ∈ (integerBox M).filter (fun k => k + Pi.single μ 1 ∈ integerBox M),
          (g (k + Pi.single μ 1) - g k) ^ 2) :=
    Finset.sum_le_sum fun μ _ => by
      rw [sum_coordSplice_step]
      exact mul_le_mul_of_nonneg_left (sum_sq_sub_along_lines_le M μ g) (by positivity)
  simp only [← Finset.mul_sum] at hlines
  refine le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 * (2 * (M : ℝ) + 1) ^ 4)
  rw [hvar]
  refine hsteps.trans ?_
  refine (mul_le_mul_of_nonneg_left hlines (by norm_num : (0 : ℝ) ≤ 4)).trans (le_of_eq ?_)
  ring
end YangMills.Construction.Weighted.BoxPoincare
