import YangMills.Construction.ChessboardTori.AlgebraOfDominatedMatricesProof
import YangMills.Construction.ChessboardTori.ThreeConsequencesOfTheTraceFormula
import YangMills.Construction.ChessboardTori.TraceFormulaOverDominatedMatrices
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SquareSummable
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori.TraceFormulaConsequences
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem weightedEntry_eq_div_sqrt (X : T.WordMatrix) (a b : T.WordIndex) :
    T.weightedEntry X (a, b) =
      ‖X a b‖ / (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b)) := by apply _root_.YangMills.Construction.ChessboardTori.DominatedMatrixAlgebra.weightedEntry_eq <;> assumption
theorem norm_entry_le_of_weightedEntry_le {X : T.WordMatrix} {C : ℝ}
    (hC : ∀ p, T.weightedEntry X p ≤ C) (a b : T.WordIndex) :
    ‖X a b‖ ≤ C * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b)) := by
  have hpos : 0 < Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b) :=
    mul_pos (Real.sqrt_pos.2 (T.indexWeight_pos a)) (Real.sqrt_pos.2 (T.indexWeight_pos b))
  have := hC (a, b)
  rw [weightedEntry_eq_div_sqrt, div_le_iff₀ hpos] at this
  exact this
theorem summable_indexWeight (hA : DominatedMatrixAlgebra.Statement) :
    Summable T.indexWeight := by
  obtain ⟨-, -, -, hc, -⟩ := hA D T
  let X : T.WordMatrix := fun a b =>
    ((Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b) : ℝ) : ℂ)
  have hnorm : ∀ a b, ‖X a b‖ =
      Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b) := by
    intro a b
    simp only [X, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hX : T.IsDominated X := by
    refine ⟨1, ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [weightedEntry_eq_div_sqrt, hnorm]
    exact div_self_le_one _
  have hsq : Summable fun p : T.WordIndex × T.WordIndex => ‖X p.1 p.2‖ ^ 2 :=
    (hc X X hX hX).1
  let e : T.WordIndex := fun _ => []
  have h1 : Summable fun a : T.WordIndex => ‖X a e‖ ^ 2 :=
    hsq.comp_injective (i := fun a => (a, e)) fun u v huv => (Prod.ext_iff.1 huv).1
  have h2 : (fun a : T.WordIndex => ‖X a e‖ ^ 2) =
      fun a => T.indexWeight a * T.indexWeight e := by
    funext a
    rw [hnorm, mul_pow, Real.sq_sqrt (T.indexWeight_pos a).le,
      Real.sq_sqrt (T.indexWeight_pos e).le]
  rw [h2] at h1
  exact (summable_mul_right_iff (T.indexWeight_pos e).ne').1 h1
theorem isDominated_adjointKernel {X : T.WordMatrix} (hX : T.IsDominated X) :
    T.IsDominated (adjointKernel X) := by apply _root_.YangMills.Construction.ChessboardTori.DominatedMatrixAlgebra.isDominated_adjointKernel <;> assumption
theorem isDominated_wordMul (hs : Summable T.indexWeight) {X Y : T.WordMatrix}
    (hX : T.IsDominated X) (hY : T.IsDominated Y) : T.IsDominated (T.wordMul X Y) := by
  obtain ⟨C, hC⟩ := hX
  obtain ⟨E, hE⟩ := hY
  have hC' : ∀ p, T.weightedEntry X p ≤ C := fun p => hC ⟨p, rfl⟩
  have hE' : ∀ p, T.weightedEntry Y p ≤ E := fun p => hE ⟨p, rfl⟩
  let e : T.WordIndex := fun _ => []
  have sq : ∀ a, 0 < Real.sqrt (T.indexWeight a) := fun a =>
    Real.sqrt_pos.2 (T.indexWeight_pos a)
  have hC0 : 0 ≤ C := by
    refine le_trans ?_ (hC' (e, e))
    rw [weightedEntry_eq_div_sqrt]
    have := sq e
    positivity
  refine ⟨C * E * ∑' a, T.indexWeight a, ?_⟩
  rintro _ ⟨⟨a, c⟩, rfl⟩
  have hterm : ∀ b, ‖X a b * Y b c‖ ≤
      C * E * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight c)) *
        T.indexWeight b := by
    intro b
    rw [norm_mul]
    calc ‖X a b‖ * ‖Y b c‖
        ≤ (C * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight b))) *
            (E * (Real.sqrt (T.indexWeight b) * Real.sqrt (T.indexWeight c))) :=
          mul_le_mul (norm_entry_le_of_weightedEntry_le T hC' _ _)
            (norm_entry_le_of_weightedEntry_le T hE' _ _) (norm_nonneg _)
            (mul_nonneg hC0 (mul_pos (sq _) (sq _)).le)
      _ = C * E * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight c)) *
            (Real.sqrt (T.indexWeight b) * Real.sqrt (T.indexWeight b)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (T.indexWeight_pos b).le]
  have hmaj : Summable fun b =>
      C * E * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight c)) *
        T.indexWeight b := hs.mul_left _
  have hsum : Summable fun b => ‖X a b * Y b c‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have hbound : ‖T.wordMul X Y a c‖ ≤
      C * E * (Real.sqrt (T.indexWeight a) * Real.sqrt (T.indexWeight c)) *
        ∑' b, T.indexWeight b := by
    rw [← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hterm hmaj)
  rw [weightedEntry_eq_div_sqrt, div_le_iff₀ (mul_pos (sq _) (sq _))]
  calc ‖T.wordMul X Y a c‖ ≤ _ := hbound
    _ = _ := by ring
theorem isDominated_foldProduct (hs : Summable T.indexWeight) :
    ∀ (n : ℕ) (B : Fin (n + 1) → T.WordMatrix), (∀ k, T.IsDominated (B k)) →
      T.IsDominated (T.foldProduct B)
  | 0, _, hB => hB 0
  | n + 1, B, hB => isDominated_wordMul T hs
      (isDominated_foldProduct hs n (fun i => B i.castSucc) fun _ => hB _) (hB _)
theorem isDominated_matrixPower (hs : Summable T.indexWeight) {X : T.WordMatrix}
    (hX : T.IsDominated X) (j : ℕ) : T.IsDominated (T.matrixPower X j) :=
  isDominated_foldProduct T hs _ _ fun _ => hX
theorem isDominated_alternatingPrefix (hs : Summable T.indexWeight)
    {X : T.WordMatrix} (hX : T.IsDominated X) (h : ℕ) :
    T.IsDominated (T.alternatingPrefix X h) := by
  refine isDominated_foldProduct T hs _ _ fun k => ?_
  unfold alternatingKernels
  split_ifs
  · exact hX
  · exact isDominated_adjointKernel T hX
theorem matrixPower_one_eq (X : T.WordMatrix) : T.matrixPower X 1 = X := rfl
theorem matrixPower_succ_succ (X : T.WordMatrix) (n : ℕ) :
    T.matrixPower X (n + 2) = T.wordMul (T.matrixPower X (n + 1)) X := rfl
theorem matrixPower_add_eq (hA : DominatedMatrixAlgebra.Statement)
    (hs : Summable T.indexWeight) {X : T.WordMatrix} (hX : T.IsDominated X) (s t : ℕ) :
    T.matrixPower X (s + 1 + (t + 1)) =
      T.wordMul (T.matrixPower X (s + 1)) (T.matrixPower X (t + 1)) := by
  induction t with
  | zero => exact matrixPower_succ_succ T X s
  | succ t ih =>
    have hassoc := ((hA D T).1 (T.matrixPower X (s + 1)) (T.matrixPower X (t + 1)) X 0
      (isDominated_matrixPower T hs hX _) (isDominated_matrixPower T hs hX _) hX).2.2.2.2.2.2.1
    rw [show s + 1 + (t + 1 + 1) = (s + 1 + t) + 2 by ring, matrixPower_succ_succ,
      show s + 1 + t + 1 = s + 1 + (t + 1) by ring, ih, hassoc, ← matrixPower_succ_succ]
theorem matrixPower_matrixPower (hA : DominatedMatrixAlgebra.Statement)
    (hs : Summable T.indexWeight) {X : T.WordMatrix} (hX : T.IsDominated X) (h j : ℕ) :
    T.matrixPower (T.matrixPower X (h + 1)) (j + 1) = T.matrixPower X ((j + 1) * (h + 1)) := by
  induction j with
  | zero => simp [matrixPower_one_eq]
  | succ j ih =>
    have hpos : ∃ n, (j + 1) * (h + 1) = n + 1 := ⟨j * (h + 1) + h, by ring⟩
    obtain ⟨n, hn⟩ := hpos
    rw [matrixPower_succ_succ, ih, hn, ← matrixPower_add_eq T hA hs hX n h]
    congr 1
    rw [← hn]
    ring
theorem bijective_natCast_fin (m : SlabCount) :
    Function.Bijective fun k : Fin (m : ℕ) => (((k : ℕ) : ZMod (m : ℕ))) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp [ZMod.card]⟩
  intro a b hab
  have := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) (m : ℕ)).1 hab
  rw [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at this
  exact Fin.ext this
theorem holds (hTF : CyclicTraceFormula.Statement) (hA : DominatedMatrixAlgebra.Statement)
    (hD : DominatedTraceFormula.Statement) :
    TraceFormulaConsequences.Statement := by
  intro D T m hm
  have hs : Summable T.indexWeight := summable_indexWeight T hA
  obtain ⟨-, -, hTF3⟩ := hTF D T
  obtain ⟨hD1, hD2⟩ := hD D T
  obtain ⟨-, -, -, -, hd, he, hf⟩ := hA D T
  have hm2 : 2 ≤ (m : ℕ) := m.2
  have hone : ∀ (M : SlabCount) (hM : Even (M : ℕ)) (Φ : T.SlabConfig → ℂ),
      T.IsBoundedMeasurable Φ → 0 ≤ T.alternatingSlabIntegral M hM Φ := by
    intro M hM Φ hΦ
    obtain ⟨-, -, e2, e3, -⟩ := (hTF3 M hM).1 Φ hΦ
    rw [e2]
    exact Complex.zero_le_real.2 e3
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ hΦ j hj => ?_⟩
  · obtain ⟨-, e1, e2, -, e4⟩ := (hTF3 m hm).1 Φ hΦ
    exact ⟨e1, e1.symm.trans e2, hone m hm Φ hΦ, e4⟩
  · have hB : ∀ k, T.IsDominated (T.slabKernels m Φ k) := fun k => (hD1 _ (hΦ _)).1
    have hbound := (he m hm hm2 (T.slabKernels m Φ) hB).2
    rw [← (hD2 m Φ hΦ).2] at hbound
    have hprod : ∏ k : Fin (m : ℕ), schattenEvenNorm (T.slabKernels m Φ k) (m : ℕ) =
        ∏ k : ZMod (m : ℕ), schattenEvenNorm (T.slabKernelMatrix (Φ k)) (m : ℕ) :=
      (bijective_natCast_fin m).prod_comp fun k =>
        schattenEvenNorm (T.slabKernelMatrix (Φ k)) (m : ℕ)
    refine ⟨hprod ▸ hbound, Finset.prod_congr rfl fun k _ => ?_⟩
    obtain ⟨-, -, e2, -, -⟩ := (hTF3 m hm).1 (Φ k) (hΦ k)
    have hnn : 0 ≤ schattenEvenNorm (T.slabKernelMatrix (Φ k)) (m : ℕ) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hm0 : (m : ℕ) ≠ 0 := by omega
    rw [e2, Complex.ofReal_re, one_div]
    exact (Real.pow_rpow_inv_natCast hnn hm0).symm
  · set X := T.slabKernelMatrix Φ with hXdef
    have hX : T.IsDominated X := (hD1 Φ hΦ).1
    have hXX : T.IsDominated (T.wordMul X (adjointKernel X)) :=
      isDominated_wordMul T hs hX (isDominated_adjointKernel T hX)
    obtain ⟨h, hh⟩ : ∃ h, (m : ℕ) / 2 = h + 1 := ⟨(m : ℕ) / 2 - 1, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h2m : 2 * (h + 1) = (m : ℕ) := by
      obtain ⟨c, hc⟩ := hm
      omega
    have hT : T.gramPower (m : ℕ) Φ =
        T.matrixPower (T.wordMul X (adjointKernel X)) (h + 1) := by
      unfold TransferSetup.gramPower
      rw [hh]
    rw [hT]
    set Y := T.alternatingPrefix X (h + 1) with hYdef
    have hY : T.IsDominated Y := isDominated_alternatingPrefix T hs hX _
    obtain ⟨hfac, -, -, htr, hdt, -, -, -, -⟩ := (hd X 1 hX).1 (h + 1) (by omega)
    obtain ⟨-, -, -, htr', -, -, -, -, -⟩ := (hd X 1 hX).1 ((i + 1) * (h + 1)) (by
      have : 0 < (i + 1) * (h + 1) := by positivity
      omega)
    obtain ⟨-, -, -, htrY, -, -, -, -, -⟩ := (hd Y 1 hY).1 (i + 1) (by omega)
    have hfY := (hf Y hY (i + 1) (by omega)).2
    obtain ⟨-, e1, -, -, -⟩ := (hTF3 m hm).1 Φ hΦ
    have hIm : T.alternatingSlabIntegral m hm Φ =
        T.diagonalTrace (T.matrixPower (T.wordMul X (adjointKernel X)) (h + 1)) := by
      rw [e1, ← htr, h2m]
    set M := SlabCount.scale (i + 1) hj m with hMdef
    have hM : Even (M : ℕ) := SlabCount.even_scale (i + 1) hj hm
    have hMcoe : (M : ℕ) = 2 * ((i + 1) * (h + 1)) := by
      have : (M : ℕ) = (i + 1) * (m : ℕ) := rfl
      rw [this, ← h2m]
      ring
    obtain ⟨-, e1M, -, -, -⟩ := (hTF3 M (SlabCount.even_scale (i + 1) hj hm)).1 Φ hΦ
    have hpow : T.matrixPower (T.matrixPower (T.wordMul X (adjointKernel X)) (h + 1)) (i + 1) =
        T.matrixPower (T.wordMul X (adjointKernel X)) ((i + 1) * (h + 1)) :=
      matrixPower_matrixPower T hA hs hXX h i
    have hIM : T.alternatingSlabIntegral M (SlabCount.even_scale (i + 1) hj hm) Φ =
        T.diagonalTrace
          (T.matrixPower (T.matrixPower (T.wordMul X (adjointKernel X)) (h + 1)) (i + 1)) := by
      rw [e1M, hMcoe, htr', hpow]
    have hMnn := hone M (SlabCount.even_scale (i + 1) hj hm) Φ hΦ
    have hmnn := hone m hm Φ hΦ
    refine ⟨isDominated_matrixPower T hs hXX _, hMnn, hIM, ?_, by rw [hIm]⟩
    rw [← hIM, ← hIm]
    have hIY : T.alternatingSlabIntegral m hm Φ = cyclicTrace ![Y, adjointKernel Y] :=
      hIm.trans hdt
    have hre : (T.alternatingSlabIntegral m hm Φ).im = 0 := (Complex.nonneg_iff.1 hmnn).2.symm
    have hreal : T.alternatingSlabIntegral m hm Φ =
        ((T.alternatingSlabIntegral m hm Φ).re : ℂ) :=
      Complex.ext (by simp) (by simp [hre])
    have hYM : T.alternatingSlabIntegral M (SlabCount.even_scale (i + 1) hj hm) Φ =
        alternatingCyclicTrace Y (2 * (i + 1)) := by
      rw [hIM, hfac, htrY]
    have hle : (T.alternatingSlabIntegral M (SlabCount.even_scale (i + 1) hj hm) Φ).re ≤
        (T.alternatingSlabIntegral m hm Φ).re ^ (i + 1) := by
      calc _ ≤ ‖T.alternatingSlabIntegral M (SlabCount.even_scale (i + 1) hj hm) Φ‖ :=
            Complex.re_le_norm _
        _ = ‖alternatingCyclicTrace Y (2 * (i + 1))‖ := by rw [hYM]
        _ ≤ (cyclicTrace ![Y, adjointKernel Y]).re ^ (i + 1) := hfY
        _ = _ := by rw [hIY]
    have hpw : T.alternatingSlabIntegral m hm Φ ^ (i + 1) =
        (((T.alternatingSlabIntegral m hm Φ).re ^ (i + 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact congrArg (· ^ (i + 1)) hreal
    rw [hpw, Complex.le_def, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hle, (Complex.nonneg_iff.1 hMnn).2.symm⟩
end YangMills.Construction.ChessboardTori.TraceFormulaConsequences
end
