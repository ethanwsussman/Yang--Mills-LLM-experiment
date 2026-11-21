import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.ElementaryMatrixInequalities
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace GaugeOrbitTangentInLeftChart
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.ComplexMatrix2
private theorem inv_matExp (Z : ComplexMatrix2) : (matExp Z)⁻¹ = matExp (-Z) := (Matrix.exp_neg Z).symm
abbrev _root_.YangMills.SharedProofs.p3399 := @inv_matExp
private theorem isUnit_of_det_eq_one {U : ComplexMatrix2} (hU : U.det = 1) : IsUnit U := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
private theorem conjugateBy_smul (U : ComplexMatrix2) (s : ℂ) (Z : ComplexMatrix2) :
    conjugateBy U (s • Z) = s • conjugateBy U Z := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
private theorem fullTrace_conjugateBy {U : ComplexMatrix2} (hU : U.det = 1) (c : ComplexMatrix2) :
    fullTrace (conjugateBy U c) = fullTrace c := by
  have h : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (by rw [hU]; exact isUnit_one)
  simp only [conjugateBy, fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, h, one_mul]
abbrev _root_.YangMills.DeltaSharedProofs.p68910 := @fullTrace_conjugateBy
private theorem mem_traceless_iff (c : ComplexMatrix2) : c ∈ traceless ↔ fullTrace c = 0 := Iff.rfl
private theorem mul_matExp_neg {U : ComplexMatrix2} (hU : U.det = 1) (Z : ComplexMatrix2) :
    U * matExp (-Z) = matExp (-conjugateBy U Z) * U := by
  have hu := isUnit_of_det_eq_one hU
  have h : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (by rw [hU]; exact isUnit_one)
  have e : -conjugateBy U Z = U * (-Z) * U⁻¹ := by simp [conjugateBy]
  have h₂ : matExp (U * (-Z) * U⁻¹) = U * matExp (-Z) * U⁻¹ := Matrix.exp_conj U (-Z) hu
  rw [e, h₂, mul_assoc, h, mul_one]
private theorem edge_value_expansion (explog : ExpLogEstimates)
    (ineq : ElementaryInequalitiesStatement) {U a c : ComplexMatrix2} (hU : U.det = 1)
    (ha : a ∈ traceless) (hc : c ∈ traceless) :
    ∃ C r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      ∃ X ∈ traceless, operatorNorm X ≤ C * ‖t‖ ^ 2 ∧
        matExp (Complex.I • (t • a)) * U * (matExp (Complex.I • (t • c)))⁻¹ =
          matExp (Complex.I • (-(t • (conjugateBy U c - a)) + X)) * U := by
  obtain ⟨-, -, -, hE, -, hdet, hlog, -⟩ := explog
  obtain ⟨hprod, -⟩ := ineq
  set c' := conjugateBy U c with hc'
  have hc'sl : c' ∈ traceless := by
    rw [mem_traceless_iff, hc', fullTrace_conjugateBy hU]
    exact hc
  set M : ℝ := ‖a‖ + ‖c'‖ with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨4 * M ^ 2, 1 / (4 * (M + 1)), by positivity, fun t ht => ?_⟩
  set Y₁ : ComplexMatrix2 := Complex.I • (t • a) with hY₁
  set Y₂ : ComplexMatrix2 := -(Complex.I • (t • c')) with hY₂
  set s : ℝ := ‖t‖ * M with hs
  have hn₁ : ‖Y₁‖ = ‖t‖ * ‖a‖ := by
    rw [hY₁, norm_smul, norm_smul, Complex.norm_I, one_mul]
  have hn₂ : ‖Y₂‖ = ‖t‖ * ‖c'‖ := by
    rw [hY₂, norm_neg, norm_smul, norm_smul, Complex.norm_I, one_mul]
  have hs0 : 0 ≤ s := by positivity
  have hs4 : s ≤ 1 / 4 := by
    have h1 : ‖t‖ * (4 * (M + 1)) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at ht
    have h2 : 0 ≤ ‖t‖ := norm_nonneg t
    rw [hs]
    nlinarith
  have hsum : ∑ i, operatorNorm ((![Y₁, Y₂] : Fin 2 → ComplexMatrix2) i) = s := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, operatorNorm]
    rw [hn₁, hn₂, hs, hM]
    ring
  have hsumY : ∑ i, (![Y₁, Y₂] : Fin 2 → ComplexMatrix2) i = Y₁ + Y₂ := by
    simp [Fin.sum_univ_two]
  have hP : expListProduct (![Y₁, Y₂] : Fin 2 → ComplexMatrix2) = matExp Y₁ * matExp Y₂ := by
    simp [expListProduct, List.ofFn_succ]
  obtain ⟨h1, h2⟩ := hprod 2 (by norm_num) ![Y₁, Y₂]
  rw [hsum, hsumY, hP] at h1 h2
  have hb1 := (h1 (by linarith)).1
  have hb2 := h2 hs4
  set P : ComplexMatrix2 := matExp Y₁ * matExp Y₂ with hPdef
  have hYs : operatorNorm (Y₁ + Y₂) ≤ s := by
    have := norm_add_le Y₁ Y₂
    rw [hn₁, hn₂] at this
    simpa [operatorNorm, hs, hM, mul_add] using this
  have hP1 : operatorNorm (P - 1) ≤ 9 / 10 := by
    have e : P - 1 = (P - 1 - (Y₁ + Y₂)) + (Y₁ + Y₂) := by abel
    have := norm_add_le (P - 1 - (Y₁ + Y₂)) (Y₁ + Y₂)
    rw [← e] at this
    simp only [operatorNorm] at hb1 hYs ⊢
    nlinarith
  have htr₁ : fullTrace Y₁ = 0 := by
    have : Y₁ ∈ traceless := traceless.smul_mem _ (traceless.smul_mem _ ha)
    exact this
  have htr₂ : fullTrace Y₂ = 0 := by
    have : Y₂ ∈ traceless := traceless.neg_mem (traceless.smul_mem _ (traceless.smul_mem _ hc'sl))
    exact this
  have hPdet : P.det = 1 := by
    rw [hPdef, Matrix.det_mul, hdet, hdet, htr₁, htr₂]
    simp
  have hlogmem : logSeries P ∈ traceless := (hlog P hPdet hP1).2
  have hexplog : matExp (logSeries P) = P := by
    have h := (hE (P - 1) (by
      have : operatorNorm (P - 1) < 1 := by linarith
      exact this)).2.2.2.2
    simpa using h
  refine ⟨Complex.I⁻¹ • logSeries P + t • (c' - a), ?_, ?_, ?_⟩
  · exact traceless.add_mem (traceless.smul_mem _ hlogmem)
      (traceless.smul_mem _ (traceless.sub_mem hc'sl ha))
  · have e : Complex.I⁻¹ • logSeries P + t • (c' - a) =
        Complex.I⁻¹ • (logSeries P - (Y₁ + Y₂)) := by
      have hY : Y₁ + Y₂ = Complex.I • (t • a - t • c') := by
        rw [hY₁, hY₂, smul_sub, sub_eq_add_neg]
      rw [hY, smul_sub Complex.I⁻¹ (logSeries P), smul_smul, inv_mul_cancel₀ Complex.I_ne_zero,
        one_smul, smul_sub t c' a]
      abel
    have hnI : ‖Complex.I⁻¹‖ = 1 := by simp
    simp only [operatorNorm] at hb2 ⊢
    rw [e, norm_smul, hnI, one_mul]
    calc ‖logSeries P - (Y₁ + Y₂)‖ ≤ 4 * s ^ 2 := hb2
      _ = 4 * M ^ 2 * ‖t‖ ^ 2 := by rw [hs]; ring
  · have e : Complex.I • (-(t • (c' - a)) + (Complex.I⁻¹ • logSeries P + t • (c' - a))) =
        logSeries P := by
      rw [neg_add_cancel_comm_assoc, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    have hmove : U * matExp (-(Complex.I • (t • c))) = matExp Y₂ * U := by
      have h := mul_matExp_neg hU (Complex.I • (t • c))
      rw [conjugateBy_smul, conjugateBy_smul] at h
      exact h
    rw [e, hexplog, hPdef, inv_matExp, mul_assoc, hmove, mul_assoc]
private theorem curve_hasDerivAt_zero (a c U : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * U *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) ((Complex.I • a) * U - U * (Complex.I • c)) 0 := by
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • a) (0 : ℂ)
  have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-(Complex.I • c)) (0 : ℂ)
  have h := (h₁.mul_const U).mul h₂
  have hr : HasDerivAt (fun t : ℝ => ((t : ℂ))) (1 : ℂ) 0 := Complex.ofRealCLM.hasDerivAt
  have hg : HasDerivAt
      (fun z : ℂ => matExp (z • (Complex.I • a)) * U * matExp (z • (-(Complex.I • c))))
      ((Complex.I • a) * U - U * (Complex.I • c)) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    refine HasDerivAt.congr_deriv h ?_
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]
    abel
  have h' := HasDerivAt.scomp (0 : ℝ) (h := fun t : ℝ => ((t : ℂ))) hg hr
  rw [one_smul] at h'
  have e : (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * U *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) =
      (fun z : ℂ => matExp (z • (Complex.I • a)) * U * matExp (z • (-(Complex.I • c)))) ∘
        fun t : ℝ => (t : ℂ) := by
    funext t
    simp only [Function.comp]
    rw [inv_matExp, smul_comm Complex.I (t : ℂ) a, smul_comm Complex.I (t : ℂ) c, smul_neg]
  rw [e]
  exact h'
private theorem curve_tangent_at_zero {U : ComplexMatrix2} (hU : U.det = 1) (a c : ComplexMatrix2) :
    Complex.I⁻¹ • (deriv (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * U *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) 0 *
        (matExp (Complex.I • (((0 : ℝ) : ℂ) • a)) * U *
          (matExp (Complex.I • (((0 : ℝ) : ℂ) • c)))⁻¹)⁻¹) = -(conjugateBy U c - a) := by
  have h : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (by rw [hU]; exact isUnit_one)
  rw [(curve_hasDerivAt_zero a c U).deriv]
  simp only [Complex.ofReal_zero, zero_smul, smul_zero, NormedSpace.exp_zero, inv_one, one_mul,
    mul_one, conjugateBy]
  rw [sub_mul, Matrix.smul_mul, Matrix.smul_mul, mul_assoc, h, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul,
    one_smul]
  abel
private theorem periodic_case (explog : ExpLogEstimates)
    (ineq : ElementaryInequalitiesStatement) (L n k j : ℕ) (hL : 0 < L) :
    LeftChartFacts.GaugeOrbitTangent L n k j := by
  have hξ : ((meshAt L k j : ℝ) : ℂ) ≠ 0 := by
    have : meshAt L k j ≠ 0 := zpow_ne_zero _ (by positivity)
    exact_mod_cast this
  refine ⟨fun U hU l hl => ?_, fun l => ?_⟩
  · have hUb : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ b)
    have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
        covDiff U l b = conjugateBy (U b) (l b.target) - l b.source := fun b hb => if_pos hb
    refine ⟨fun b hb => ?_, fun b _ => (curve_hasDerivAt_zero _ _ _).differentiableAt, ?_,
      fun x μ hb => ?_⟩
    · obtain ⟨C, r, hr, h⟩ := edge_value_expansion explog ineq (hUb b) (hl b.source) (hl b.target)
      refine ⟨C, r, hr, fun t ht => ?_⟩
      rw [hpos b hb]
      exact h t ht
    · funext b
      have e : (-covDiff U l) b = extendOddly (fun b : Edge L n k j =>
          -(conjugateBy (U b) (l b.target) - l b.source)) b := by
        simp only [covDiff, extendOddly, Pi.neg_apply]
        split_ifs <;> simp
      rw [e]
      simp only [curveTangent, extendOddly]
      split_ifs
      · exact curve_tangent_at_zero (hUb b) _ _
      · exact congrArg Neg.neg (curve_tangent_at_zero (hUb b.opposite) _ _)
    · rw [hpos _ hb]
      simp only [PeriodicLattice.covDeriv]
      rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hξ, one_smul]
      rfl
  · funext b
    simp only [covDiff, extendOddly, vertexCoboundary, conjugateBy]
    split_ifs
    · simp
    · simp [PeriodicLattice.Bond.opposite]
private theorem fullSpace_case (explog : ExpLogEstimates)
    (ineq : ElementaryInequalitiesStatement) (L k j : ℕ) (hL : 0 < L) :
    FullSpace.LeftChartFacts.GaugeOrbitTangent L k j := by
  have hξ : ((meshAt L k j : ℝ) : ℂ) ≠ 0 := by
    have : meshAt L k j ≠ 0 := zpow_ne_zero _ (by positivity)
    exact_mod_cast this
  refine ⟨fun U hU l hl => ?_, fun l => ?_⟩
  · have hUb : ∀ b, (U b).det = 1 := hU.1
    have hpos : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
        FullSpace.covDiff U l b = conjugateBy (U b) (l b.terminal) - l b.initial :=
      fun b hb => if_pos hb
    refine ⟨fun b hb => ?_, fun b _ => (curve_hasDerivAt_zero _ _ _).differentiableAt, ?_,
      fun x μ hb => ?_⟩
    · obtain ⟨C, r, hr, h⟩ :=
        edge_value_expansion explog ineq (hUb b) (hl b.initial) (hl b.terminal)
      refine ⟨C, r, hr, fun t ht => ?_⟩
      rw [hpos b hb]
      exact h t ht
    · funext b
      have e : (-FullSpace.covDiff U l) b = FullSpace.extendOddly
          (fun b : FullSpace.Edge L k j => -(conjugateBy (U b) (l b.terminal) - l b.initial)) b := by
        simp only [FullSpace.covDiff, FullSpace.extendOddly, Pi.neg_apply]
        split_ifs <;> simp
      rw [e]
      simp only [FullSpace.curveTangent, FullSpace.extendOddly]
      split_ifs
      · exact curve_tangent_at_zero (hUb b) _ _
      · exact congrArg Neg.neg (curve_tangent_at_zero (hUb b.opposite) _ _)
    · rw [hpos _ hb, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hξ, one_smul]
      rfl
  · funext b
    simp only [FullSpace.covDiff, FullSpace.extendOddly, FullSpace.vertexCoboundary, conjugateBy]
    split_ifs
    · simp
    · simp [InfiniteLattice.Link.opposite]
end GaugeOrbitTangentInLeftChart
theorem GaugeOrbitTangentInLeftChart.holds
    (explog : Matrices.ComplexMatrix2.ExpLogEstimates)
    (ineq : Matrices.ComplexMatrix2.ElementaryInequalitiesStatement) :
    GaugeOrbitTangentInLeftChart.Statement := by
  intro L k j hL _
  have hL0 : 0 < L := by have := hL.2; omega
  exact ⟨fun n _ => GaugeOrbitTangentInLeftChart.periodic_case explog ineq L n k j hL0,
    GaugeOrbitTangentInLeftChart.fullSpace_case explog ineq L k j hL0⟩
end YangMills.Construction.Tower
end
