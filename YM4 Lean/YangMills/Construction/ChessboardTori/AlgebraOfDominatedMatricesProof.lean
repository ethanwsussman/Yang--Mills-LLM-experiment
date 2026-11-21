import YangMills.Construction.Analysis.CyclicTraceProducts
import YangMills.Construction.Analysis.SquareSummableKernels
import YangMills.Construction.ChessboardTori.DominatedMatricesOverTheExpansionIndex
import Mathlib
set_option autoImplicit false

section
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.SquareSummable
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def alternatingPrefix (X : T.WordMatrix) (h : ℕ) : T.WordMatrix :=
  T.foldProduct (n := h - 1) (alternatingKernels X (h - 1 + 1))
end TransferSetup
def DominatedMatrixAlgebra.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D),
    (∀ (X Y Z : T.WordMatrix) (ζ : ℂ), T.IsDominated X → T.IsDominated Y → T.IsDominated Z →
      T.IsDominated (X + Y) ∧
      T.IsDominated (ζ • X) ∧
      T.wordMul (X + Y) Z = T.wordMul X Z + T.wordMul Y Z ∧
      T.wordMul X (Y + Z) = T.wordMul X Y + T.wordMul X Z ∧
      T.wordMul (ζ • X) Y = ζ • T.wordMul X Y ∧
      T.wordMul X (ζ • Y) = ζ • T.wordMul X Y ∧
      T.wordMul (T.wordMul X Y) Z = T.wordMul X (T.wordMul Y Z) ∧
      adjointKernel (T.wordMul X Y) = T.wordMul (adjointKernel Y) (adjointKernel X) ∧
      adjointKernel (adjointKernel X) = X ∧
      adjointKernel (ζ • X) = conj ζ • adjointKernel X) ∧
    (∀ (n : ℕ) (B : Fin (n + 1) → T.WordMatrix), (∀ k, T.IsDominated (B k)) →
      CyclicTraceConverges B ∧
      T.diagonalTrace (T.foldProduct B) = ∑' a : Fin (n + 1) → T.WordIndex, cyclicTraceTerm B a) ∧
    (∀ (n : ℕ) (B : Fin (n + 2) → T.WordMatrix), (∀ k, T.IsDominated (B k)) →
      cyclicTrace B = T.diagonalTrace (T.foldProduct (n := n + 1) B) ∧
      cyclicTrace B = cyclicTrace (fun k => B (finRotate (n + 2) k)) ∧
      ∀ (j : Fin (n + 2)) (W : T.WordMatrix) (ζ : ℂ), T.IsDominated W →
        cyclicTrace (Function.update B j (B j + W)) = cyclicTrace B + cyclicTrace (Function.update B j W) ∧
        cyclicTrace (Function.update B j (ζ • B j)) = ζ * cyclicTrace B) ∧
    (∀ X Y : T.WordMatrix, T.IsDominated X → T.IsDominated Y →
      IsSqSummable X ∧
      CyclicTraceConverges ![X, adjointKernel X] ∧
      cyclicTrace ![X, adjointKernel X] =
        ((∑' p : T.WordIndex × T.WordIndex, ‖X p.1 p.2‖ ^ 2 : ℝ) : ℂ) ∧
      0 ≤ ∑' p : T.WordIndex × T.WordIndex, ‖X p.1 p.2‖ ^ 2 ∧
      CyclicTraceConverges ![X, Y] ∧
      CyclicTraceConverges ![adjointKernel Y, Y] ∧
      ‖cyclicTrace ![X, Y]‖ ^ 2 ≤
        (cyclicTrace ![X, adjointKernel X]).re * (cyclicTrace ![adjointKernel Y, Y]).re) ∧
    (∀ (X : T.WordMatrix) (ζ : ℂ), T.IsDominated X →
      (∀ h : ℕ, 1 ≤ h →
        T.matrixPower (T.wordMul X (adjointKernel X)) h =
          T.wordMul (T.alternatingPrefix X h)
            (adjointKernel (T.alternatingPrefix X h)) ∧
        CyclicTraceConverges (alternatingKernels X (2 * h)) ∧
        CyclicTraceConverges ![T.alternatingPrefix X h, adjointKernel (T.alternatingPrefix X h)] ∧
        alternatingCyclicTrace X (2 * h) =
          T.diagonalTrace (T.matrixPower (T.wordMul X (adjointKernel X)) h) ∧
        T.diagonalTrace (T.matrixPower (T.wordMul X (adjointKernel X)) h) =
          cyclicTrace ![T.alternatingPrefix X h, adjointKernel (T.alternatingPrefix X h)] ∧
        (alternatingCyclicTrace X (2 * h)).im = 0 ∧
        0 ≤ (alternatingCyclicTrace X (2 * h)).re ∧
        alternatingCyclicTrace (adjointKernel X) (2 * h) = alternatingCyclicTrace X (2 * h) ∧
        alternatingCyclicTrace (ζ • X) (2 * h) =
          ((‖ζ‖ ^ (2 * h) : ℝ) : ℂ) * alternatingCyclicTrace X (2 * h)) ∧
      ∀ m : ℕ, Even m → 2 ≤ m →
        ((schattenEvenNorm X m ^ m : ℝ) : ℂ) = alternatingCyclicTrace X m ∧
        schattenEvenNorm (adjointKernel X) m = schattenEvenNorm X m ∧
        schattenEvenNorm (ζ • X) m = ‖ζ‖ * schattenEvenNorm X m) ∧
    (∀ m : ℕ, Even m → 2 ≤ m → ∀ B : Fin m → T.WordMatrix, (∀ k, T.IsDominated (B k)) →
      CyclicTraceConverges B ∧
      ‖cyclicTrace B‖ ≤ ∏ k : Fin m, schattenEvenNorm (B k) m) ∧
    (∀ Y : T.WordMatrix, T.IsDominated Y → ∀ j : ℕ, 1 ≤ j →
      CyclicTraceConverges (alternatingKernels Y (2 * j)) ∧
      ‖alternatingCyclicTrace Y (2 * j)‖ ≤ (cyclicTrace ![Y, adjointKernel Y]).re ^ j)
end YangMills.Construction.ChessboardTori
end
end

open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ChessboardTori
open SquareSummable
namespace DominatedMatrixAlgebra
theorem summable_prod_fin {W : Type} {f : W → ℝ} (h0 : ∀ x, 0 ≤ f x) (hf : Summable f) (n : ℕ) :
    Summable fun α : Fin n → W => ∏ i, f (α i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    let e : (W × (Fin n → W)) ≃ (Fin (n + 1) → W) := Fin.consEquiv (fun _ => W)
    rw [← e.summable_iff]
    refine (hf.mul_of_nonneg ih (fun x => h0 x)
      (fun α => Finset.prod_nonneg fun i _ => h0 _)).congr fun x => ?_
    simp only [Function.comp_apply]
    rw [Fin.prod_univ_succ]
    rfl
theorem summable_prod_pi {W ι : Type} [Fintype ι] {f : W → ℝ} (h0 : ∀ x, 0 ≤ f x)
    (hf : Summable f) : Summable fun α : ι → W => ∏ i, f (α i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : (Fin (Fintype.card ι) → W) ≃ (ι → W) := e.symm.arrowCongr (Equiv.refl W)
  rw [← E.summable_iff]
  refine (summable_prod_fin h0 hf _).congr fun β => ?_
  simp only [Function.comp_apply]
  rw [← e.symm.prod_comp (fun i => f (E β i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [E, Equiv.arrowCongr]
theorem summable_poissonWeight (D : ChessboardSetup) :
    Summable fun γ : MatrixWord => poissonWeight D γ.length := by
  rw [← (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm.summable_iff]
  have hc : ∀ n, 0 ≤ poissonWeight D n := fun n => (poissonWeight_pos D n).le
  have hcomp : (fun γ : MatrixWord => poissonWeight D γ.length) ∘
      (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm =
      fun x : (Σ n, Fin n → Fin 2 × Fin 2) => poissonWeight D x.1 := by
    funext x
    obtain ⟨n, p⟩ := x
    simp [List.equivSigmaTuple]
  rw [hcomp]
  refine (summable_sigma_of_nonneg fun x => hc _).2 ⟨fun n => Summable.of_finite, ?_⟩
  have hfib : ∀ n, ∑' _ : Fin n → Fin 2 × Fin 2, poissonWeight D n =
      Real.exp (-D.β) * ((2 * D.β) ^ n / (n.factorial : ℝ)) := by
    intro n
    have h2 : (2 * D.β) = 4 * (D.β / 2) := by ring
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, h2, mul_pow]
    simp only [Fintype.card_pi, Fintype.card_prod, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ, nsmul_eq_mul, poissonWeight]
    push_cast
    ring
  simp only [hfib]
  exact (Real.summable_pow_div_factorial _).mul_left _
section Domination
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem summable_indexWeight : Summable T.indexWeight :=
  summable_prod_pi (f := fun γ : MatrixWord => poissonWeight D γ.length)
    (fun _ => (poissonWeight_pos D _).le) (summable_poissonWeight D)
def sqrtWeight (a : T.WordIndex) : ℝ := Real.sqrt (T.indexWeight a)
theorem sqrtWeight_pos (a : T.WordIndex) : 0 < sqrtWeight T a :=
  Real.sqrt_pos.2 (T.indexWeight_pos a)
theorem sqrtWeight_mul_self (a : T.WordIndex) :
    sqrtWeight T a * sqrtWeight T a = T.indexWeight a :=
  Real.mul_self_sqrt (T.indexWeight_pos a).le
theorem weightedEntry_eq (X : T.WordMatrix) (a b : T.WordIndex) :
    T.weightedEntry X (a, b) = ‖X a b‖ / (sqrtWeight T a * sqrtWeight T b) := by
  have hnn : 0 ≤ T.indexWeight a * T.indexWeight b :=
    (mul_pos (T.indexWeight_pos a) (T.indexWeight_pos b)).le
  simp only [TransferSetup.weightedEntry]
  rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, Real.sqrt_mul (T.indexWeight_pos a).le,
    div_eq_inv_mul]
  rfl
theorem exists_entry_bound {X : T.WordMatrix} (hX : T.IsDominated X) :
    ∃ C, 0 ≤ C ∧ ∀ a b, ‖X a b‖ ≤ C * (sqrtWeight T a * sqrtWeight T b) := by
  obtain ⟨C, hC⟩ := hX
  refine ⟨max C 0, le_max_right _ _, fun a b => ?_⟩
  have hp := mul_pos (sqrtWeight_pos T a) (sqrtWeight_pos T b)
  have h := hC (Set.mem_range_self (a, b))
  rw [weightedEntry_eq, div_le_iff₀ hp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
theorem isDominated_of_entry_bound {X : T.WordMatrix} {C : ℝ}
    (h : ∀ a b, ‖X a b‖ ≤ C * (sqrtWeight T a * sqrtWeight T b)) : T.IsDominated X := by
  refine ⟨C, ?_⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [weightedEntry_eq, div_le_iff₀ (mul_pos (sqrtWeight_pos T a) (sqrtWeight_pos T b))]
  exact h a b
theorem norm_entry_mul_le {X Y : T.WordMatrix} {C C' : ℝ} (hC : 0 ≤ C)
    (hX : ∀ a b, ‖X a b‖ ≤ C * (sqrtWeight T a * sqrtWeight T b))
    (hY : ∀ a b, ‖Y a b‖ ≤ C' * (sqrtWeight T a * sqrtWeight T b))
    (a m b : T.WordIndex) :
    ‖X a m * Y m b‖ ≤
      C * C' * (sqrtWeight T a * sqrtWeight T b) * T.indexWeight m := by
  have ha := (sqrtWeight_pos T a).le
  have hm := (sqrtWeight_pos T m).le
  rw [norm_mul, ← sqrtWeight_mul_self T m]
  calc ‖X a m‖ * ‖Y m b‖
      ≤ (C * (sqrtWeight T a * sqrtWeight T m)) *
          (C' * (sqrtWeight T m * sqrtWeight T b)) :=
        mul_le_mul (hX a m) (hY m b) (norm_nonneg _) (by positivity)
    _ = _ := by ring
theorem summable_entry_mul {X Y : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y)
    (a b : T.WordIndex) : Summable fun m => X a m * Y m b := by
  obtain ⟨C, hC, hX⟩ := exists_entry_bound T hX
  obtain ⟨C', hC', hY⟩ := exists_entry_bound T hY
  exact Summable.of_norm_bounded
    (g := fun m => C * C' * (sqrtWeight T a * sqrtWeight T b) * T.indexWeight m)
    ((summable_indexWeight T).mul_left _) (fun m => norm_entry_mul_le T hC hX hY a m b)
theorem isDominated_wordMul {X Y : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y) :
    T.IsDominated (T.wordMul X Y) := by
  obtain ⟨C, hC, hX⟩ := exists_entry_bound T hX
  obtain ⟨C', hC', hY⟩ := exists_entry_bound T hY
  refine isDominated_of_entry_bound T (C := C * C' * ∑' m, T.indexWeight m) fun a b => ?_
  have h := tsum_of_norm_bounded
    (((summable_indexWeight T).hasSum).mul_left
      (C * C' * (sqrtWeight T a * sqrtWeight T b)))
    (fun m => norm_entry_mul_le T hC hX hY a m b)
  calc ‖T.wordMul X Y a b‖ ≤ _ := h
    _ = _ := by ring
theorem isDominated_adjointKernel {X : T.WordMatrix} (hX : T.IsDominated X) :
    T.IsDominated (adjointKernel X) := by
  obtain ⟨C, _, hX⟩ := exists_entry_bound T hX
  refine isDominated_of_entry_bound T (C := C) fun a b => ?_
  simp only [adjointKernel, RCLike.norm_conj]
  rw [mul_comm (sqrtWeight T a)]
  exact hX b a
theorem isDominated_add {X Y : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y) :
    T.IsDominated (X + Y) := by
  obtain ⟨C, _, hX⟩ := exists_entry_bound T hX
  obtain ⟨C', _, hY⟩ := exists_entry_bound T hY
  refine isDominated_of_entry_bound T (C := C + C') fun a b => ?_
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hX a b) (hY a b))
theorem isDominated_smul (ζ : ℂ) {X : T.WordMatrix} (hX : T.IsDominated X) :
    T.IsDominated (ζ • X) := by
  obtain ⟨C, _, hX⟩ := exists_entry_bound T hX
  refine isDominated_of_entry_bound T (C := ‖ζ‖ * C) fun a b => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX a b) (norm_nonneg _)
theorem isSqSummable_of_isDominated {X : T.WordMatrix} (hX : T.IsDominated X) :
    IsSqSummable X := by
  obtain ⟨C, hC, hX⟩ := exists_entry_bound T hX
  have hs := (summable_indexWeight T).mul_of_nonneg (summable_indexWeight T)
    (fun a => (T.indexWeight_pos a).le) (fun a => (T.indexWeight_pos a).le)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) (hs.mul_left (C ^ 2))
  have h := pow_le_pow_left₀ (norm_nonneg _) (hX p.1 p.2) 2
  refine h.trans (le_of_eq ?_)
  rw [← sqrtWeight_mul_self T p.1, ← sqrtWeight_mul_self T p.2]
  ring
theorem add_wordMul {X Y Z : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y)
    (hZ : T.IsDominated Z) :
    T.wordMul (X + Y) Z = T.wordMul X Z + T.wordMul Y Z := by
  funext a b
  show ∑' m, (X + Y) a m * Z m b = (∑' m, X a m * Z m b) + ∑' m, Y a m * Z m b
  rw [← (summable_entry_mul T hX hZ a b).tsum_add (summable_entry_mul T hY hZ a b)]
  exact tsum_congr fun m => by simp [add_mul]
theorem wordMul_add {X Y Z : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y)
    (hZ : T.IsDominated Z) :
    T.wordMul X (Y + Z) = T.wordMul X Y + T.wordMul X Z := by
  funext a b
  show ∑' m, X a m * (Y + Z) m b = (∑' m, X a m * Y m b) + ∑' m, X a m * Z m b
  rw [← (summable_entry_mul T hX hY a b).tsum_add (summable_entry_mul T hX hZ a b)]
  exact tsum_congr fun m => by simp [mul_add]
theorem smul_wordMul (ζ : ℂ) (X Y : T.WordMatrix) :
    T.wordMul (ζ • X) Y = ζ • T.wordMul X Y := by
  funext a b
  show ∑' m, (ζ • X) a m * Y m b = ζ * ∑' m, X a m * Y m b
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by simp [mul_assoc]
theorem wordMul_smul (ζ : ℂ) (X Y : T.WordMatrix) :
    T.wordMul X (ζ • Y) = ζ • T.wordMul X Y := by
  funext a b
  show ∑' m, X a m * (ζ • Y) m b = ζ * ∑' m, X a m * Y m b
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by simp only [Pi.smul_apply, smul_eq_mul]; ring
theorem wordMul_assoc {X Y Z : T.WordMatrix} (hX : T.IsDominated X) (hY : T.IsDominated Y)
    (hZ : T.IsDominated Z) :
    T.wordMul (T.wordMul X Y) Z = T.wordMul X (T.wordMul Y Z) := by
  funext a d
  obtain ⟨C, hC, hX'⟩ := exists_entry_bound T hX
  obtain ⟨C', hC', hY'⟩ := exists_entry_bound T hY
  obtain ⟨C'', hC'', hZ'⟩ := exists_entry_bound T hZ
  have hsum : Summable (Function.uncurry fun (b c : T.WordIndex) =>
      X a b * Y b c * Z c d) := by
    have hs := (summable_indexWeight T).mul_of_nonneg (summable_indexWeight T)
      (fun a => (T.indexWeight_pos a).le) (fun a => (T.indexWeight_pos a).le)
    refine Summable.of_norm_bounded
      (g := fun p : T.WordIndex × T.WordIndex =>
        (C * C' * C'' * (sqrtWeight T a * sqrtWeight T d)) *
          (T.indexWeight p.1 * T.indexWeight p.2))
      (hs.mul_left _) fun p => ?_
    obtain ⟨b, c⟩ := p
    have h1 := norm_entry_mul_le T hC hX' hY' a b c
    have h2 := hZ' c d
    have ha := (sqrtWeight_pos T a).le
    have hb := (T.indexWeight_pos b).le
    have hc := (sqrtWeight_pos T c).le
    show ‖X a b * Y b c * Z c d‖ ≤ _
    rw [norm_mul, ← sqrtWeight_mul_self T c]
    calc ‖X a b * Y b c‖ * ‖Z c d‖
        ≤ (C * C' * (sqrtWeight T a * sqrtWeight T c) * T.indexWeight b) *
            (C'' * (sqrtWeight T c * sqrtWeight T d)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  show ∑' c, (∑' b, X a b * Y b c) * Z c d = ∑' b, X a b * ∑' c, Y b c * Z c d
  simp only [← tsum_mul_left, ← tsum_mul_right, ← mul_assoc]
  exact hsum.tsum_comm
theorem adjointKernel_wordMul (X Y : T.WordMatrix) :
    adjointKernel (T.wordMul X Y) = T.wordMul (adjointKernel Y) (adjointKernel X) := by
  funext a c
  show conj (∑' m, X c m * Y m a) = ∑' m, conj (Y m a) * conj (X c m)
  rw [Complex.conj_tsum]
  exact tsum_congr fun m => by rw [map_mul, mul_comm]
theorem adjointKernel_adjointKernel (X : T.WordMatrix) : adjointKernel (adjointKernel X) = X := by
  funext a b
  simp [adjointKernel]
theorem adjointKernel_smul (ζ : ℂ) (X : T.WordMatrix) :
    adjointKernel (ζ • X) = conj ζ • adjointKernel X := by
  funext a b
  simp [adjointKernel]
end Domination
section Walks
variable {D : ChessboardSetup} (T : TransferSetup D)
def pathProduct : (n : ℕ) → (Fin (n + 1) → T.WordMatrix) → T.WordIndex →
    (Fin n → T.WordIndex) → T.WordIndex → ℂ
  | 0, B, a, _, b => B 0 a b
  | n + 1, B, a, β, b =>
    pathProduct n (fun i => B i.castSucc) a (fun i => β i.castSucc) (β (Fin.last n)) *
      B (Fin.last (n + 1)) (β (Fin.last n)) b
theorem pathProduct_bound : ∀ (n : ℕ) (B : Fin (n + 1) → T.WordMatrix),
    (∀ k, T.IsDominated (B k)) →
    ∃ K, 0 ≤ K ∧ ∀ a β b, ‖pathProduct T n B a β b‖ ≤
      K * (sqrtWeight T a * sqrtWeight T b) * ∏ k, T.indexWeight (β k)
  | 0, B, hB => by
    obtain ⟨C, hC, h⟩ := exists_entry_bound T (hB 0)
    exact ⟨C, hC, fun a β b => by simpa [pathProduct] using h a b⟩
  | n + 1, B, hB => by
    obtain ⟨K, hK, h⟩ := pathProduct_bound n (fun i => B i.castSucc) (fun i => hB _)
    obtain ⟨C, hC, hl⟩ := exists_entry_bound T (hB (Fin.last (n + 1)))
    refine ⟨K * C, mul_nonneg hK hC, fun a β b => ?_⟩
    have hP : 0 ≤ ∏ i : Fin n, T.indexWeight (β i.castSucc) :=
      Finset.prod_nonneg fun i _ => (T.indexWeight_pos _).le
    have ha := (sqrtWeight_pos T a).le
    have hm := (sqrtWeight_pos T (β (Fin.last n))).le
    rw [pathProduct, norm_mul, Fin.prod_univ_castSucc, ← sqrtWeight_mul_self T (β (Fin.last n))]
    calc _ ≤ (K * (sqrtWeight T a * sqrtWeight T (β (Fin.last n))) *
            ∏ i : Fin n, T.indexWeight (β i.castSucc)) *
          (C * (sqrtWeight T (β (Fin.last n)) * sqrtWeight T b)) :=
          mul_le_mul (h a _ _) (hl _ b) (norm_nonneg _) (by positivity)
      _ = _ := by ring
theorem pathProduct_snoc (n : ℕ) (B : Fin (n + 1 + 1) → T.WordMatrix) (a : T.WordIndex)
    (β' : Fin n → T.WordIndex) (m b : T.WordIndex) :
    pathProduct T (n + 1) B a (Fin.snoc (α := fun _ => T.WordIndex) β' m) b =
      pathProduct T n (fun i => B i.castSucc) a β' m * B (Fin.last (n + 1)) m b := by
  have h : (fun i : Fin n => (Fin.snoc (α := fun _ => T.WordIndex) β' m) i.castSucc) = β' := by
    funext i
    simp
  simp only [pathProduct, Fin.snoc_last, h]
theorem hasSum_pathProduct : ∀ (n : ℕ) (B : Fin (n + 1) → T.WordMatrix),
    (∀ k, T.IsDominated (B k)) →
    ∀ a b, HasSum (fun β => pathProduct T n B a β b) (T.foldProduct B a b)
  | 0, B, _, a, b => hasSum_unique (fun β : Fin 0 → T.WordIndex => pathProduct T 0 B a β b)
  | n + 1, B, hB, a, b => by
    let e : (T.WordIndex × (Fin (n + 1 - 1) → T.WordIndex)) ≃
        (Fin (n + 1) → T.WordIndex) := Fin.snocEquiv (fun _ => T.WordIndex)
    obtain ⟨K, _, hb⟩ := pathProduct_bound T (n + 1) B hB
    have hs : Summable (fun β => pathProduct T (n + 1) B a β b) :=
      Summable.of_norm_bounded
        (g := fun β : Fin (n + 1) → T.WordIndex =>
          K * (sqrtWeight T a * sqrtWeight T b) * ∏ k, T.indexWeight (β k))
        ((summable_prod_pi (fun x => (T.indexWeight_pos x).le)
          (summable_indexWeight T)).mul_left _) (fun β => hb a β b)
    have hF := hs.hasSum
    rw [← e.hasSum_iff] at hF
    have hfib : ∀ m, HasSum (fun β' => ((fun β => pathProduct T (n + 1) B a β b) ∘ e) (m, β'))
        (T.foldProduct (fun i => B i.castSucc) a m * B (Fin.last (n + 1)) m b) := by
      intro m
      have h := (hasSum_pathProduct n (fun i => B i.castSucc) (fun i => hB _) a m).mul_right
        (B (Fin.last (n + 1)) m b)
      have hc : (fun β' => ((fun β => pathProduct T (n + 1) B a β b) ∘ e) (m, β')) =
          fun β' => pathProduct T n (fun i => B i.castSucc) a β' m * B (Fin.last (n + 1)) m b :=
        funext fun β' => pathProduct_snoc T n B a β' m b
      rw [hc]
      exact h
    have hg := (hF.prod_fiberwise hfib).tsum_eq
    have hl : T.foldProduct B a b = ∑' β, pathProduct T (n + 1) B a β b := hg
    rw [hl]
    exact hs.hasSum
theorem pathProduct_eq_prod : ∀ (n : ℕ) (B : Fin (n + 1) → T.WordMatrix) (a : T.WordIndex)
    (β : Fin n → T.WordIndex) (b : T.WordIndex),
    pathProduct T n B a β b = ∏ k : Fin (n + 1),
      B k (Fin.cons (α := fun _ => T.WordIndex) a β k)
        (Fin.snoc (α := fun _ => T.WordIndex) β b k)
  | 0, B, a, β, b => by simp [pathProduct, Fin.snoc]
  | n + 1, B, a, β, b => by
    have h1 : (Fin.cons (α := fun _ => T.WordIndex) a β) =
        Fin.snoc (α := fun _ => T.WordIndex)
          (Fin.cons (α := fun _ => T.WordIndex) a fun i : Fin n => β i.castSucc)
          (β (Fin.last n)) := by
      rw [← Fin.cons_snoc_eq_snoc_cons]
      congr 1
      exact (Fin.snoc_init_self β).symm
    have hc : ∀ k : Fin (n + 1), (Fin.cons (α := fun _ => T.WordIndex) a β) k.castSucc =
        Fin.cons (α := fun _ => T.WordIndex) a (fun i : Fin n => β i.castSucc) k :=
      fun k => by rw [h1, Fin.snoc_castSucc]
    have hl : (Fin.cons (α := fun _ => T.WordIndex) a β) (Fin.last (n + 1)) =
        β (Fin.last n) := by rw [h1, Fin.snoc_last]
    have hs : ∀ k : Fin (n + 1), (Fin.snoc (α := fun _ => T.WordIndex) β b) k.castSucc =
        Fin.snoc (α := fun _ => T.WordIndex) (fun i : Fin n => β i.castSucc)
          (β (Fin.last n)) k := fun k => by
      rw [Fin.snoc_castSucc]
      exact (congrFun (Fin.snoc_init_self β) k).symm
    rw [pathProduct, Fin.prod_univ_castSucc, pathProduct_eq_prod n]
    simp only [hc, hl, hs, Fin.snoc_last]
theorem cons_apply_finRotate (n : ℕ) (a : T.WordIndex) (β : Fin n → T.WordIndex)
    (k : Fin (n + 1)) :
    (Fin.cons (α := fun _ => T.WordIndex) a β) (finRotate (n + 1) k) =
      Fin.snoc (α := fun _ => T.WordIndex) β a k := by
  induction k using Fin.lastCases with
  | last => rw [finRotate_last, Fin.snoc_last]; rfl
  | cast j => rw [finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]
theorem cyclicTraceTerm_cons (n : ℕ) (B : Fin (n + 1) → T.WordMatrix) (a : T.WordIndex)
    (β : Fin n → T.WordIndex) :
    cyclicTraceTerm B (Fin.cons (α := fun _ => T.WordIndex) a β) = pathProduct T n B a β a := by
  rw [pathProduct_eq_prod]
  unfold cyclicTraceTerm
  exact Finset.prod_congr rfl fun k _ => by rw [cons_apply_finRotate]
theorem cyclicTraceConverges_of_isDominated (n : ℕ) (B : Fin (n + 1) → T.WordMatrix)
    (hB : ∀ k, T.IsDominated (B k)) : CyclicTraceConverges B := by
  obtain ⟨K, hK, hb⟩ := pathProduct_bound T n B hB
  let e : (T.WordIndex × (Fin n → T.WordIndex)) ≃ (Fin (n + 1) → T.WordIndex) :=
    Fin.consEquiv (fun _ => T.WordIndex)
  have hs1 : Summable fun β : Fin n → T.WordIndex => ∏ k, T.indexWeight (β k) :=
    summable_prod_pi (fun x => (T.indexWeight_pos x).le) (summable_indexWeight T)
  have hs := ((summable_indexWeight T).mul_of_nonneg hs1
    (fun a => (T.indexWeight_pos a).le)
    (fun β => Finset.prod_nonneg fun i _ => (T.indexWeight_pos _).le)).mul_left K
  unfold CyclicTraceConverges
  rw [← e.summable_iff]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hs
  obtain ⟨a, β⟩ := x
  have h := hb a β a
  rw [sqrtWeight_mul_self] at h
  show ‖cyclicTraceTerm B (Fin.cons (α := fun _ => T.WordIndex) a β)‖ ≤ _
  rw [cyclicTraceTerm_cons]
  exact h.trans (le_of_eq (by ring))
theorem diagonalTrace_foldProduct (n : ℕ) (B : Fin (n + 1) → T.WordMatrix)
    (hB : ∀ k, T.IsDominated (B k)) :
    T.diagonalTrace (T.foldProduct B) = ∑' α : Fin (n + 1) → T.WordIndex, cyclicTraceTerm B α := by
  let e : (T.WordIndex × (Fin n → T.WordIndex)) ≃ (Fin (n + 1) → T.WordIndex) :=
    Fin.consEquiv (fun _ => T.WordIndex)
  have hs : Summable (cyclicTraceTerm B) :=
    Summable.of_norm (cyclicTraceConverges_of_isDominated T n B hB)
  have hF := hs.hasSum
  rw [← e.hasSum_iff] at hF
  have hfib : ∀ a, HasSum (fun β => (cyclicTraceTerm B ∘ e) (a, β)) (T.foldProduct B a a) := by
    intro a
    have hc : (fun β => (cyclicTraceTerm B ∘ e) (a, β)) = fun β => pathProduct T n B a β a :=
      funext fun β => cyclicTraceTerm_cons T n B a β
    rw [hc]
    exact hasSum_pathProduct T n B hB a a
  exact (hF.prod_fiberwise hfib).tsum_eq
theorem cyclicTraceTerm_update {m : ℕ} (B : Fin m → T.WordMatrix) (j : Fin m) (V : T.WordMatrix)
    (α : Fin m → T.WordIndex) :
    cyclicTraceTerm (Function.update B j V) α = V (α j) (α (finRotate m j)) *
      ∏ k ∈ Finset.univ \ {j}, B k (α k) (α (finRotate m k)) := by
  have h : ∀ k, Function.update B j V k (α k) (α (finRotate m k)) =
      Function.update (fun k => B k (α k) (α (finRotate m k))) j
        (V (α j) (α (finRotate m j))) k := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Function.update_of_ne hk]
  unfold cyclicTraceTerm
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_update_of_mem (Finset.mem_univ j)]
theorem cyclicTraceTerm_eq_mul_erase {m : ℕ} (B : Fin m → T.WordMatrix) (j : Fin m)
    (α : Fin m → T.WordIndex) :
    cyclicTraceTerm B α = B j (α j) (α (finRotate m j)) *
      ∏ k ∈ Finset.univ \ {j}, B k (α k) (α (finRotate m k)) := by
  have h := cyclicTraceTerm_update T B j (B j) α
  rwa [Function.update_eq_self] at h
theorem cyclicTrace_update_add (n : ℕ) (B : Fin (n + 1) → T.WordMatrix)
    (hB : ∀ k, T.IsDominated (B k)) (j : Fin (n + 1)) (W : T.WordMatrix)
    (hW : T.IsDominated W) :
    cyclicTrace (Function.update B j (B j + W)) =
      cyclicTrace B + cyclicTrace (Function.update B j W) := by
  have hu : ∀ k, T.IsDominated (Function.update B j W k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      simpa using hW
    · simpa [Function.update_of_ne hk] using hB k
  have hs1 : Summable (cyclicTraceTerm B) :=
    Summable.of_norm (cyclicTraceConverges_of_isDominated T n B hB)
  have hs2 : Summable (cyclicTraceTerm (Function.update B j W)) :=
    Summable.of_norm (cyclicTraceConverges_of_isDominated T n _ hu)
  unfold cyclicTrace
  rw [← hs1.tsum_add hs2]
  refine tsum_congr fun α => ?_
  rw [cyclicTraceTerm_update, cyclicTraceTerm_update, cyclicTraceTerm_eq_mul_erase T B j α,
    ← add_mul]
  rfl
theorem cyclicTrace_update_smul {m : ℕ} (B : Fin m → T.WordMatrix) (j : Fin m) (ζ : ℂ) :
    cyclicTrace (Function.update B j (ζ • B j)) = ζ * cyclicTrace B := by
  unfold cyclicTrace
  rw [← tsum_mul_left]
  refine tsum_congr fun α => ?_
  rw [cyclicTraceTerm_update, cyclicTraceTerm_eq_mul_erase T B j α]
  exact mul_assoc ζ _ _
end Walks
section Sequences
variable {D : ChessboardSetup} (T : TransferSetup D)
def partialProduct (G : ℕ → T.WordMatrix) : ℕ → T.WordMatrix
  | 0 => G 0
  | n + 1 => T.wordMul (partialProduct G n) (G (n + 1))
theorem foldProduct_eq_partialProduct (G : ℕ → T.WordMatrix) :
    ∀ n, T.foldProduct (n := n) (fun k => G k) = partialProduct T G n
  | 0 => rfl
  | n + 1 => by
    show T.wordMul (T.foldProduct (n := n) fun i => G i) (G (n + 1)) =
      T.wordMul (partialProduct T G n) (G (n + 1))
    rw [foldProduct_eq_partialProduct G n]
theorem partialProduct_congr {G G' : ℕ → T.WordMatrix} :
    ∀ n, (∀ i ≤ n, G i = G' i) → partialProduct T G n = partialProduct T G' n
  | 0, h => h 0 le_rfl
  | n + 1, h => by
    simp only [partialProduct]
    rw [partialProduct_congr n (fun i hi => h i (by omega)), h (n + 1) le_rfl]
theorem isDominated_partialProduct {G : ℕ → T.WordMatrix} (hG : ∀ i, T.IsDominated (G i)) :
    ∀ n, T.IsDominated (partialProduct T G n)
  | 0 => hG 0
  | n + 1 => isDominated_wordMul T (isDominated_partialProduct hG n) (hG _)
theorem partialProduct_split {G : ℕ → T.WordMatrix} (hG : ∀ i, T.IsDominated (G i)) (p : ℕ) :
    ∀ q, partialProduct T G (p + q + 1) =
      T.wordMul (partialProduct T G p) (partialProduct T (fun i => G (p + 1 + i)) q)
  | 0 => rfl
  | q + 1 => by
    have hG' : ∀ i, T.IsDominated ((fun i => G (p + 1 + i)) i) := fun i => hG _
    show T.wordMul (partialProduct T G (p + q + 1)) (G (p + q + 1 + 1)) =
      T.wordMul (partialProduct T G p)
        (T.wordMul (partialProduct T (fun i => G (p + 1 + i)) q) (G (p + 1 + (q + 1))))
    rw [partialProduct_split hG p q,
      wordMul_assoc T (isDominated_partialProduct T hG p) (isDominated_partialProduct T hG' q)
        (hG _)]
    have e : p + 1 + (q + 1) = p + q + 1 + 1 := by omega
    rw [e]
theorem adjointKernel_partialProduct {G : ℕ → T.WordMatrix} (hG : ∀ i, T.IsDominated (G i)) :
    ∀ n, adjointKernel (partialProduct T G n) =
      partialProduct T (fun i => adjointKernel (G (n - i))) n
  | 0 => rfl
  | n + 1 => by
    have hG' : ∀ i, T.IsDominated ((fun i => adjointKernel (G (n + 1 - i))) i) :=
      fun i => isDominated_adjointKernel T (hG _)
    have hsplit := partialProduct_split T hG' 0 n
    have e : 0 + n + 1 = n + 1 := by omega
    rw [e] at hsplit
    rw [hsplit]
    show adjointKernel (T.wordMul (partialProduct T G n) (G (n + 1))) =
      T.wordMul (adjointKernel (G (n + 1))) _
    rw [adjointKernel_wordMul, adjointKernel_partialProduct hG n]
    refine congrArg (T.wordMul _) (partialProduct_congr T n fun i _ => ?_)
    show adjointKernel (G (n - i)) = adjointKernel (G (n + 1 - (0 + 1 + i)))
    have e' : n + 1 - (0 + 1 + i) = n - i := by omega
    rw [e']
def altFactor (X : T.WordMatrix) (i : ℕ) : T.WordMatrix :=
  if Even i then X else adjointKernel X
theorem altFactor_of_even {X : T.WordMatrix} {i : ℕ} (h : Even i) : altFactor T X i = X :=
  if_pos h
theorem altFactor_of_not_even {X : T.WordMatrix} {i : ℕ} (h : ¬Even i) :
    altFactor T X i = adjointKernel X := if_neg h
theorem isDominated_altFactor {X : T.WordMatrix} (hX : T.IsDominated X) (i : ℕ) :
    T.IsDominated (altFactor T X i) := by
  by_cases h : Even i
  · rwa [altFactor_of_even T h]
  · rw [altFactor_of_not_even T h]
    exact isDominated_adjointKernel T hX
theorem altFactor_of_odd_add (X : T.WordMatrix) {s t : ℕ} (h : Odd (s + t)) :
    altFactor T X s = adjointKernel (altFactor T X t) := by
  by_cases ht : Even t
  · by_cases hs : Even s
    · exact absurd (hs.add ht) (Nat.not_even_iff_odd.2 h)
    · rw [altFactor_of_not_even T hs, altFactor_of_even T ht]
  · by_cases hs : Even s
    · rw [altFactor_of_even T hs, altFactor_of_not_even T ht, adjointKernel_adjointKernel]
    · exact absurd ((Nat.not_even_iff_odd.1 hs).add_odd (Nat.not_even_iff_odd.1 ht))
        (Nat.not_even_iff_odd.2 h)
theorem alternatingPrefix_eq (X : T.WordMatrix) (k : ℕ) :
    T.alternatingPrefix X (k + 1) = partialProduct T (altFactor T X) k :=
  foldProduct_eq_partialProduct T (altFactor T X) k
theorem matrixPower_eq_partialProduct (Z : T.WordMatrix) (k : ℕ) :
    T.matrixPower Z (k + 1) = partialProduct T (fun _ => Z) k :=
  foldProduct_eq_partialProduct T (fun _ => Z) k
theorem partialProduct_const_eq {X : T.WordMatrix} (hX : T.IsDominated X) :
    ∀ k, partialProduct T (fun _ => T.wordMul X (adjointKernel X)) k =
      partialProduct T (altFactor T X) (2 * k + 1)
  | 0 => by
    show T.wordMul X (adjointKernel X) = T.wordMul (altFactor T X 0) (altFactor T X 1)
    rw [altFactor_of_even T (by decide), altFactor_of_not_even T (by decide)]
  | k + 1 => by
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    have h1 : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
    have h2 : ¬Even (2 * k + 1 + 1 + 1) := Nat.not_even_iff_odd.2 ⟨k + 1, by ring⟩
    rw [e]
    show T.wordMul (partialProduct T (fun _ => T.wordMul X (adjointKernel X)) k)
        (T.wordMul X (adjointKernel X)) =
      T.wordMul (T.wordMul (partialProduct T (altFactor T X) (2 * k + 1))
        (altFactor T X (2 * k + 1 + 1))) (altFactor T X (2 * k + 1 + 1 + 1))
    rw [partialProduct_const_eq hX k, altFactor_of_even T h1, altFactor_of_not_even T h2,
      wordMul_assoc T (isDominated_partialProduct T (isDominated_altFactor T hX) _) hX
        (isDominated_adjointKernel T hX)]
theorem matrixPower_mul_adjoint {X : T.WordMatrix} (hX : T.IsDominated X) (k : ℕ) :
    T.matrixPower (T.wordMul X (adjointKernel X)) (k + 1) =
      T.wordMul (T.alternatingPrefix X (k + 1))
        (adjointKernel (T.alternatingPrefix X (k + 1))) := by
  have hG := isDominated_altFactor T hX
  have e : 2 * k + 1 = k + k + 1 := by ring
  rw [matrixPower_eq_partialProduct, partialProduct_const_eq T hX, alternatingPrefix_eq,
    adjointKernel_partialProduct T hG, e, partialProduct_split T hG]
  refine congrArg (T.wordMul _) (partialProduct_congr T k fun i hi => ?_)
  exact altFactor_of_odd_add T X ⟨k, by omega⟩
theorem alternatingCyclicTrace_eq_diagonalTrace {X : T.WordMatrix} (hX : T.IsDominated X)
    (n : ℕ) :
    alternatingCyclicTrace X (n + 2) =
      T.diagonalTrace (partialProduct T (altFactor T X) (n + 1)) := by
  have h := diagonalTrace_foldProduct T (n + 1) (alternatingKernels X (n + 2))
    (fun k => isDominated_altFactor T hX k)
  rw [← foldProduct_eq_partialProduct T (altFactor T X) (n + 1)]
  exact h.symm
theorem alternatingCyclicTrace_eq_diagonalTrace_pow {X : T.WordMatrix} (hX : T.IsDominated X)
    (k : ℕ) :
    alternatingCyclicTrace X (2 * (k + 1)) =
      T.diagonalTrace (T.matrixPower (T.wordMul X (adjointKernel X)) (k + 1)) := by
  have e : 2 * (k + 1) = 2 * k + 2 := by ring
  rw [e, alternatingCyclicTrace_eq_diagonalTrace T hX, matrixPower_eq_partialProduct,
    partialProduct_const_eq T hX]
theorem diagonalTrace_wordMul {X Y : T.WordMatrix} (hX : T.IsDominated X)
    (hY : T.IsDominated Y) : T.diagonalTrace (T.wordMul X Y) = cyclicTrace ![X, Y] :=
  diagonalTrace_foldProduct T 1 ![X, Y] (Fin.forall_fin_two.2 ⟨hX, hY⟩)
theorem alternatingKernels_two (X : T.WordMatrix) :
    alternatingKernels X 2 = ![X, adjointKernel X] := by
  funext k
  fin_cases k <;> simp [alternatingKernels]
theorem alternatingKernels_rotate (X : T.WordMatrix) {n : ℕ} (hn : ¬Even n) :
    (fun k => alternatingKernels X (n + 1) (finRotate (n + 1) k)) =
      alternatingKernels (adjointKernel X) (n + 1) := by
  funext k
  show altFactor T X (finRotate (n + 1) k) = altFactor T (adjointKernel X) k
  induction k using Fin.lastCases with
  | last =>
    rw [finRotate_last]
    show altFactor T X 0 = altFactor T (adjointKernel X) n
    rw [altFactor_of_even T (by decide), altFactor_of_not_even T hn, adjointKernel_adjointKernel]
  | cast j =>
    rw [finRotate_apply, Fin.coeSucc_eq_succ]
    show altFactor T X (j + 1) = altFactor T (adjointKernel X) j
    by_cases hj : Even (j : ℕ)
    · rw [altFactor_of_not_even T (by simpa [Nat.even_add_one] using hj), altFactor_of_even T hj]
    · rw [altFactor_of_even T (by simpa [Nat.even_add_one] using hj), altFactor_of_not_even T hj,
        adjointKernel_adjointKernel]
theorem cyclicTraceTerm_smul {m : ℕ} (w : Fin m → ℂ) (B : Fin m → T.WordMatrix)
    (α : Fin m → T.WordIndex) :
    cyclicTraceTerm (fun k => w k • B k) α = (∏ k, w k) * cyclicTraceTerm B α := by
  simp only [cyclicTraceTerm, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
theorem prod_alternating_conj (ζ : ℂ) (h : ℕ) :
    ∏ k : Fin (2 * h), (if Even (k : ℕ) then ζ else conj ζ) = ((‖ζ‖ ^ (2 * h) : ℝ) : ℂ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if Even i then ζ else conj ζ)]
  induction h with
  | zero => simp
  | succ h ih =>
    have e : 2 * (h + 1) = 2 * h + 1 + 1 := by ring
    have h1 : Even (2 * h) := ⟨h, by ring⟩
    have h2 : ¬Even (2 * h + 1) := Nat.not_even_iff_odd.2 ⟨h, rfl⟩
    rw [e, Finset.prod_range_succ, Finset.prod_range_succ, ih, if_pos h1, if_neg h2, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
theorem alternatingCyclicTrace_smul (ζ : ℂ) (X : T.WordMatrix) (h : ℕ) :
    alternatingCyclicTrace (ζ • X) (2 * h) =
      ((‖ζ‖ ^ (2 * h) : ℝ) : ℂ) * alternatingCyclicTrace X (2 * h) := by
  have hf : alternatingKernels (ζ • X) (2 * h) =
      fun k : Fin (2 * h) =>
        (if Even (k : ℕ) then ζ else conj ζ) • alternatingKernels X (2 * h) k := by
    funext k
    by_cases hk : Even (k : ℕ)
    · simp [alternatingKernels, hk]
    · simp only [alternatingKernels, hk, if_false]
      exact adjointKernel_smul T ζ X
  unfold alternatingCyclicTrace cyclicTrace
  rw [hf, ← prod_alternating_conj, ← tsum_mul_left]
  exact tsum_congr fun α => cyclicTraceTerm_smul T _ _ α
theorem schattenEvenNorm_pow (X : T.WordMatrix) {m : ℕ} (hm : m ≠ 0) :
    schattenEvenNorm X m ^ m = ‖alternatingCyclicTrace X m‖ := by
  unfold schattenEvenNorm
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (norm_nonneg _) hm
theorem schattenEvenNorm_smul (ζ : ℂ) (X : T.WordMatrix) {h : ℕ} (hh : 2 * h ≠ 0) :
    schattenEvenNorm (ζ • X) (2 * h) = ‖ζ‖ * schattenEvenNorm X (2 * h) := by
  unfold schattenEvenNorm
  rw [alternatingCyclicTrace_smul, norm_mul, Complex.norm_real, norm_pow, norm_norm, one_div,
    Real.mul_rpow (by positivity) (norm_nonneg _), Real.pow_rpow_inv_natCast (norm_nonneg _) hh]
end Sequences
section Assertions
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem cyclicTrace_rotate (hT : CyclicTraceProductBounds) {m : ℕ} (hm : 2 ≤ m)
    {B : Fin m → T.WordMatrix} (hB : ∀ k, T.IsDominated (B k)) :
    cyclicTrace (fun k => B (finRotate m k)) = cyclicTrace B :=
  (hT T.WordIndex m hm (B ⟨0, by omega⟩) B (isSqSummable_of_isDominated T (hB _))
    (fun k => isSqSummable_of_isDominated T (hB k))).2.1.2.2.2.1
theorem norm_cyclicTrace_le_prod (hT : CyclicTraceProductBounds) {m : ℕ} (hm : 2 ≤ m)
    (hE : Even m) {B : Fin m → T.WordMatrix} (hB : ∀ k, T.IsDominated (B k)) :
    ‖cyclicTrace B‖ ≤ ∏ k : Fin m, schattenEvenNorm (B k) m :=
  ((hT T.WordIndex m hm (B ⟨0, by omega⟩) B (isSqSummable_of_isDominated T (hB _))
    (fun k => isSqSummable_of_isDominated T (hB k))).2.2 hE).2.1
theorem alternatingCyclicTrace_properties (hT : CyclicTraceProductBounds) {m : ℕ} (hm : 2 ≤ m)
    (hE : Even m) {X : T.WordMatrix} (hX : T.IsDominated X) :
    (alternatingCyclicTrace X m).im = 0 ∧ 0 ≤ (alternatingCyclicTrace X m).re ∧
      alternatingCyclicTrace X m = ((schattenEvenNorm X m ^ m : ℝ) : ℂ) ∧
      schattenEvenNorm (adjointKernel X) m = schattenEvenNorm X m :=
  ((hT T.WordIndex m hm X (fun _ => X) (isSqSummable_of_isDominated T hX)
    (fun _ => isSqSummable_of_isDominated T hX)).2.2 hE).1
theorem schattenEvenNorm_pow_le (hT : CyclicTraceProductBounds) {X : T.WordMatrix}
    (hX : T.IsDominated X) {j : ℕ} (hj : 1 ≤ j) :
    schattenEvenNorm X (j * 2) ^ (j * 2) ≤ (schattenEvenNorm X 2 ^ 2) ^ j :=
  ((hT T.WordIndex 2 le_rfl X (fun _ => X) (isSqSummable_of_isDominated T hX)
    (fun _ => isSqSummable_of_isDominated T hX)).2.2 even_two).2.2 j hj
theorem cyclicTraceConverges_alternating {X : T.WordMatrix} (hX : T.IsDominated X) {m : ℕ}
    (hm : m ≠ 0) : CyclicTraceConverges (alternatingKernels X m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact cyclicTraceConverges_of_isDominated T n _ fun k => isDominated_altFactor T hX k
theorem alternatingCyclicTrace_adjointKernel (hT : CyclicTraceProductBounds) {X : T.WordMatrix}
    (hX : T.IsDominated X) {m : ℕ} (hm : 2 ≤ m) (hE : Even m) :
    alternatingCyclicTrace (adjointKernel X) m = alternatingCyclicTrace X m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : ¬Even n := by simpa [Nat.even_add_one] using hE
  have h := cyclicTrace_rotate T hT hm (B := alternatingKernels X (n + 1))
    (fun k => isDominated_altFactor T hX k)
  rw [alternatingKernels_rotate T X hn] at h
  exact h
theorem cyclicTrace_pair_adjoint_eq_tsum (X : T.WordMatrix) :
    cyclicTrace ![X, adjointKernel X] =
      ((∑' p : T.WordIndex × T.WordIndex, ‖X p.1 p.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold cyclicTrace
  rw [← (finTwoArrowEquiv T.WordIndex).symm.tsum_eq]
  refine tsum_congr fun p => ?_
  have h0 : finRotate 2 0 = 1 := rfl
  have h1 : finRotate 2 1 = 0 := rfl
  simp only [cyclicTraceTerm, Fin.prod_univ_two, h0, h1, finTwoArrowEquiv,
    Matrix.cons_val_zero, Matrix.cons_val_one, adjointKernel]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl
theorem cyclicTrace_pair_adjoint (hT : CyclicTraceProductBounds) {X : T.WordMatrix}
    (hX : T.IsDominated X) :
    cyclicTrace ![X, adjointKernel X] = ((schattenEvenNorm X 2 ^ 2 : ℝ) : ℂ) := by
  have h := (alternatingCyclicTrace_properties T hT (le_refl 2) even_two hX).2.2.1
  unfold alternatingCyclicTrace at h
  rwa [alternatingKernels_two] at h
theorem cyclicTrace_swap (hT : CyclicTraceProductBounds) {X : T.WordMatrix}
    (hX : T.IsDominated X) :
    cyclicTrace ![adjointKernel X, X] = cyclicTrace ![X, adjointKernel X] := by
  have h := cyclicTrace_rotate T hT (le_refl 2) (B := ![X, adjointKernel X])
    (Fin.forall_fin_two.2 ⟨hX, isDominated_adjointKernel T hX⟩)
  have e : (fun k => (![X, adjointKernel X] : Fin 2 → T.WordMatrix) (finRotate 2 k)) =
      ![adjointKernel X, X] := by
    funext k
    fin_cases k <;> rfl
  rwa [e] at h
theorem cyclicTrace_cauchy_schwarz (hT : CyclicTraceProductBounds) {X Y : T.WordMatrix}
    (hX : T.IsDominated X) (hY : T.IsDominated Y) :
    ‖cyclicTrace ![X, Y]‖ ^ 2 ≤
      (cyclicTrace ![X, adjointKernel X]).re * (cyclicTrace ![adjointKernel Y, Y]).re := by
  have hd := norm_cyclicTrace_le_prod T hT (le_refl 2) even_two (B := ![X, Y])
    (Fin.forall_fin_two.2 ⟨hX, hY⟩)
  rw [Fin.prod_univ_two] at hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  rw [cyclicTrace_swap T hT hY, cyclicTrace_pair_adjoint T hT hX, cyclicTrace_pair_adjoint T hT hY,
    Complex.ofReal_re, Complex.ofReal_re, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hd 2
theorem norm_alternatingCyclicTrace_le (hT : CyclicTraceProductBounds) {Y : T.WordMatrix}
    (hY : T.IsDominated Y) {j : ℕ} (hj : 1 ≤ j) :
    ‖alternatingCyclicTrace Y (2 * j)‖ ≤ (cyclicTrace ![Y, adjointKernel Y]).re ^ j := by
  have h := schattenEvenNorm_pow_le T hT hY hj
  rw [mul_comm j 2, schattenEvenNorm_pow T Y (by omega)] at h
  rw [cyclicTrace_pair_adjoint T hT hY, Complex.ofReal_re]
  exact h
end Assertions
theorem statement_holds (hT : CyclicTraceProductBounds) : Statement := by
  intro D T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y Z ζ hX hY hZ
    exact ⟨isDominated_add T hX hY, isDominated_smul T ζ hX, add_wordMul T hX hY hZ,
      wordMul_add T hX hY hZ, smul_wordMul T ζ X Y, wordMul_smul T ζ X Y,
      wordMul_assoc T hX hY hZ, adjointKernel_wordMul T X Y, adjointKernel_adjointKernel T X,
      adjointKernel_smul T ζ X⟩
  · intro n B hB
    exact ⟨cyclicTraceConverges_of_isDominated T n B hB, diagonalTrace_foldProduct T n B hB⟩
  · intro n B hB
    refine ⟨(diagonalTrace_foldProduct T (n + 1) B hB).symm,
      (cyclicTrace_rotate T hT (by omega) hB).symm, fun j W ζ hW => ?_⟩
    exact ⟨cyclicTrace_update_add T (n + 1) B hB j W hW, cyclicTrace_update_smul T B j ζ⟩
  · intro X Y hX hY
    have hXa := isDominated_adjointKernel T hX
    have hYa := isDominated_adjointKernel T hY
    exact ⟨isSqSummable_of_isDominated T hX,
      cyclicTraceConverges_of_isDominated T 1 _ (Fin.forall_fin_two.2 ⟨hX, hXa⟩),
      cyclicTrace_pair_adjoint_eq_tsum T X, tsum_nonneg fun _ => sq_nonneg _,
      cyclicTraceConverges_of_isDominated T 1 _ (Fin.forall_fin_two.2 ⟨hX, hY⟩),
      cyclicTraceConverges_of_isDominated T 1 _ (Fin.forall_fin_two.2 ⟨hYa, hY⟩),
      cyclicTrace_cauchy_schwarz T hT hX hY⟩
  · intro X ζ hX
    refine ⟨fun h hh => ?_, fun m hE hm => ?_⟩
    · obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      have hm : 2 ≤ 2 * (k + 1) := by omega
      have hE : Even (2 * (k + 1)) := even_two_mul _
      have hc := alternatingCyclicTrace_properties T hT hm hE hX
      have hY : T.IsDominated (T.alternatingPrefix X (k + 1)) := by
        rw [alternatingPrefix_eq]
        exact isDominated_partialProduct T (isDominated_altFactor T hX) k
      have hYa := isDominated_adjointKernel T hY
      have hp := matrixPower_mul_adjoint T hX k
      refine ⟨hp, cyclicTraceConverges_alternating T hX (by omega),
        cyclicTraceConverges_of_isDominated T 1 _ (Fin.forall_fin_two.2 ⟨hY, hYa⟩),
        alternatingCyclicTrace_eq_diagonalTrace_pow T hX k, ?_, hc.1, hc.2.1,
        alternatingCyclicTrace_adjointKernel T hT hX hm hE, alternatingCyclicTrace_smul T ζ X _⟩
      rw [hp]
      exact diagonalTrace_wordMul T hY hYa
    · have hc := alternatingCyclicTrace_properties T hT hm hE hX
      obtain ⟨h, rfl⟩ := hE.two_dvd
      exact ⟨hc.2.2.1.symm, hc.2.2.2, schattenEvenNorm_smul T ζ X (by omega)⟩
  · intro m hE hm B hB
    have hd := norm_cyclicTrace_le_prod T hT hm hE hB
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact ⟨cyclicTraceConverges_of_isDominated T n B hB, hd⟩
  · intro Y hY j hj
    exact ⟨cyclicTraceConverges_alternating T hY (by omega), norm_alternatingCyclicTrace_le T hT hY hj⟩
end DominatedMatrixAlgebra
end YangMills.Construction.ChessboardTori
end
