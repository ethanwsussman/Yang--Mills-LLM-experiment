import YangMills.Construction.Matrices.ExpLogSeriesConvergence
import YangMills.Construction.RunningCouplingSlope.LinearAverageIsTheMeanOverTheContours
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfAnExponential
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanOfExp
open Tower Matrices
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem norm_apply_le_norm (A : ComplexMatrix2) (a b : Fin 2) : ‖A a b‖ ≤ ‖A‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
theorem cpow_half_near_one (z : ℂ) (h : ‖z - 1‖ ≤ 1 / 10) :
    z ^ (1 / 2 : ℂ) ≠ 0 ∧ (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ ‖z ^ (1 / 2 : ℂ) - 1‖ ≤ ‖z - 1‖ ∧
      z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.sqrt_near_one <;> assumption
theorem norm_prod_matExp_sub (hc : ComplexMatrix2.ExpLogSeriesConvergence)
    (a : ℝ) (ha : 0 ≤ a) (l : List ComplexMatrix2) (h : ∀ X ∈ l, ‖X‖ ≤ a) :
    ‖(l.map fun X => ComplexMatrix2.matExp (Complex.I • X)).prod - 1 - Complex.I • l.sum‖ ≤
        Real.exp (l.length * a) - 1 - l.length * a ∧
      ‖(l.map fun X => ComplexMatrix2.matExp (Complex.I • X)).prod - 1‖ ≤
        Real.exp (l.length * a) - 1 ∧
      ‖(l.map fun X => ComplexMatrix2.matExp (Complex.I • X)).prod‖ ≤
        Real.exp (l.length * a) := by
  induction l with
  | nil =>
    have h1 : ‖(1 : ComplexMatrix2)‖ = 1 := norm_one
    simp [h1]
  | cons X l ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    have hX := h X (List.mem_cons_self ..)
    obtain ⟨-, -, -, -, -, -, e1, e2, e3⟩ := hc.1 (Complex.I • X)
    have hnorm : ComplexMatrix2.operatorNorm (Complex.I • X) = ‖X‖ := by
      simp [ComplexMatrix2.operatorNorm, norm_smul]
    rw [hnorm] at e1 e2 e3
    have hmono : Real.exp ‖X‖ - 1 - ‖X‖ ≤ Real.exp a - 1 - a := by
      have h4 := Real.add_one_le_exp (a - ‖X‖)
      have h5 : Real.exp a = Real.exp ‖X‖ * Real.exp (a - ‖X‖) := by
        rw [← Real.exp_add]; congr 1; ring
      have h6 : 1 ≤ Real.exp ‖X‖ := Real.one_le_exp (norm_nonneg _)
      nlinarith
    have hexp : Real.exp ‖X‖ ≤ Real.exp a := Real.exp_le_exp.mpr hX
    set E := ComplexMatrix2.matExp (Complex.I • X) with hE
    set Pr := (l.map fun X => ComplexMatrix2.matExp (Complex.I • X)).prod with hPr
    set m : ℝ := (l.length : ℝ) with hm
    set T := Real.exp (m * a) with hT
    have hT1 : 1 ≤ T := Real.one_le_exp (by positivity)
    have hnE : ‖E - 1 - Complex.I • X‖ ≤ Real.exp a - 1 - a := le_trans e2 hmono
    have hnE1 : ‖E - 1‖ ≤ Real.exp a - 1 := by
      have : ComplexMatrix2.operatorNorm (E - 1) ≤ Real.exp ‖X‖ - 1 := e1
      linarith [this]
    have hnE2 : ‖E‖ ≤ Real.exp a := le_trans e3 hexp
    have hpos : 0 ≤ Real.exp a - 1 - a := by linarith [Real.add_one_le_exp a]
    have hpos1 : 0 ≤ Real.exp a - 1 := by linarith [Real.one_le_exp ha]
    have hlen : Real.exp ((m + 1) * a) = Real.exp a * T := by
      rw [hT, ← Real.exp_add]
      congr 1
      ring
    have hlenR : ((((X :: l).length : ℕ) : ℝ)) = m + 1 := by
      simp [hm]
    simp only [List.map_cons, List.prod_cons, List.sum_cons, hlenR, hlen, smul_add, ← hE, ← hPr]
    refine ⟨?_, ?_, ?_⟩
    · have e : E * Pr - 1 - (Complex.I • X + Complex.I • l.sum) =
          (E - 1 - Complex.I • X) * Pr + (Complex.I • X) * (Pr - 1) +
            (Pr - 1 - Complex.I • l.sum) := by noncomm_ring
      rw [e]
      have n1 : ‖(E - 1 - Complex.I • X) * Pr‖ ≤ (Real.exp a - 1 - a) * T :=
        (norm_mul_le _ _).trans (mul_le_mul hnE h3 (norm_nonneg _) hpos)
      have n2 : ‖(Complex.I • X) * (Pr - 1)‖ ≤ a * (T - 1) := by
        refine (norm_mul_le _ _).trans (mul_le_mul ?_ h2 (norm_nonneg _) ha)
        simpa [norm_smul] using hX
      calc ‖(E - 1 - Complex.I • X) * Pr + (Complex.I • X) * (Pr - 1) +
            (Pr - 1 - Complex.I • l.sum)‖
          ≤ ‖(E - 1 - Complex.I • X) * Pr‖ + ‖(Complex.I • X) * (Pr - 1)‖ +
              ‖Pr - 1 - Complex.I • l.sum‖ := norm_add₃_le
        _ ≤ (Real.exp a - 1 - a) * T + a * (T - 1) + (T - 1 - m * a) := by gcongr
        _ = Real.exp a * T - 1 - (m + 1) * a := by ring
    · have e : E * Pr - 1 = (E - 1) * Pr + (Pr - 1) := by noncomm_ring
      rw [e]
      have n1 : ‖(E - 1) * Pr‖ ≤ (Real.exp a - 1) * T :=
        (norm_mul_le _ _).trans (mul_le_mul hnE1 h3 (norm_nonneg _) hpos1)
      calc ‖(E - 1) * Pr + (Pr - 1)‖ ≤ ‖(E - 1) * Pr‖ + ‖Pr - 1‖ := norm_add_le _ _
        _ ≤ (Real.exp a - 1) * T + (T - 1) := by gcongr
        _ = Real.exp a * T - 1 := by ring
    · exact (norm_mul_le _ _).trans (mul_le_mul hnE2 h3 (norm_nonneg _) (Real.exp_pos _).le)
section
variable {L n k j : ℕ}
theorem bondFormSumAlong_reversePath (A : Edge L n k j → ComplexMatrix2)
    (hA : ∀ b, A b.opposite = -A b) (l : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong A (PeriodicLattice.reversePath l) =
      -PeriodicLattice.bondFormSumAlong A l := by
  induction l with
  | nil => simp [PeriodicLattice.bondFormSumAlong, PeriodicLattice.reversePath]
  | cons b l ih =>
    have e : PeriodicLattice.reversePath (b :: l) =
        PeriodicLattice.reversePath l ++ [b.opposite] := by
      simp [PeriodicLattice.reversePath]
    rw [e]
    simp only [PeriodicLattice.bondFormSumAlong, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil, add_zero, hA] at ih ⊢
    rw [ih]
    abel
theorem norm_list_map_sum_le {ι : Type*} (f : ι → ComplexMatrix2) (a : ℝ) (h : ∀ b, ‖f b‖ ≤ a)
    (l : List ι) : ‖(l.map f).sum‖ ≤ l.length * a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc ‖f b + (l.map f).sum‖ ≤ ‖f b‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ a + l.length * a := add_le_add (h b) ih
      _ = (l.length + 1) * a := by ring
theorem inv_pathHolonomy (V : Edge L n k j → ComplexMatrix2) (hV : ∀ b, V b.opposite = (V b)⁻¹)
    (hd : ∀ b, Matrix.det (V b) = 1) (l : List (Edge L n k j)) :
    (PeriodicLattice.pathHolonomy V l)⁻¹ =
      PeriodicLattice.pathHolonomy V (PeriodicLattice.reversePath l) := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.inv_pathHolonomy_eq <;> assumption
theorem length_stepsThroughAxes {a : ℤ} (d : Fin 4 → ℤ) (x : PeriodicLattice.Site L n a)
    (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes d x l).length = (l.map fun μ => (d μ).natAbs).sum := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.length_stepsThroughAxes <;> assumption
end
theorem unimodular_part_eq_matExp (hel : ComplexMatrix2.ExpLogEstimates)
    (hc : ComplexMatrix2.ExpLogSeriesConvergence)
    (W M : ComplexMatrix2) (x₀ : ℝ) (hx0 : 0 ≤ x₀) (hx1 : x₀ ≤ 1 / 100)
    (htrM : ComplexMatrix2.fullTrace M = 0)
    (hMn : ‖M‖ ≤ 5 * x₀) (hEn : ‖W - 1 - Complex.I • M‖ ≤ 25 * x₀ ^ 2) :
    ‖(Matrix.det W) ^ (1 / 2 : ℂ) - 1‖ ≤ 122 * x₀ ^ 2 ∧
      ∃ N ∈ ComplexMatrix2.traceless, ‖N‖ ≤ 472 * x₀ ^ 2 ∧
        ((Matrix.det W) ^ (1 / 2 : ℂ))⁻¹ • W = ComplexMatrix2.matExp (Complex.I • (M + N)) := by
  set E := W - 1 - Complex.I • M with hE
  set Z := Complex.I • M + E with hZ
  have hWZ : W = 1 + Z := by
    rw [hZ, hE]
    abel
  have hIM : ‖Complex.I • M‖ ≤ 5 * x₀ := by
    have : ‖Complex.I • M‖ = ‖M‖ := by simp [norm_smul]
    rw [this]; exact hMn
  have hx2 : x₀ ^ 2 ≤ x₀ / 100 := by nlinarith
  have hZn : ‖Z‖ ≤ 6 * x₀ := by
    have : ‖Z‖ ≤ ‖Complex.I • M‖ + ‖E‖ := norm_add_le _ _
    nlinarith
  have hentryE : ∀ p q, ‖E p q‖ ≤ 25 * x₀ ^ 2 := fun p q => (norm_apply_le_norm E p q).trans hEn
  have hentryZ : ∀ p q, ‖Z p q‖ ≤ 6 * x₀ := fun p q => (norm_apply_le_norm Z p q).trans hZn
  have htrZ : Z 0 0 + Z 1 1 = E 0 0 + E 1 1 := by
    have h1 : (Complex.I • M) 0 0 + (Complex.I • M) 1 1 = 0 := by
      have := htrM
      simp only [ComplexMatrix2.fullTrace, Matrix.trace, Matrix.diag, Fin.sum_univ_two] at this
      simp only [Matrix.smul_apply, smul_eq_mul, ← mul_add, this, mul_zero]
    simp only [hZ, Matrix.add_apply]
    linear_combination h1
  have hdet : ‖Matrix.det W - 1‖ ≤ 122 * x₀ ^ 2 := by
    have e00 : W 0 0 = 1 + Z 0 0 := by simp [hWZ]
    have e11 : W 1 1 = 1 + Z 1 1 := by simp [hWZ]
    have e01 : W 0 1 = Z 0 1 := by simp [hWZ]
    have e10 : W 1 0 = Z 1 0 := by simp [hWZ]
    have e : Matrix.det W - 1 = (E 0 0 + E 1 1) + Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 := by
      rw [Matrix.det_fin_two, e00, e11, e01, e10, ← htrZ]
      ring
    rw [e]
    have m1 : ‖Z 0 0 * Z 1 1‖ ≤ 6 * x₀ * (6 * x₀) := by
      rw [norm_mul]; exact mul_le_mul (hentryZ _ _) (hentryZ _ _) (norm_nonneg _) (by positivity)
    have m2 : ‖Z 0 1 * Z 1 0‖ ≤ 6 * x₀ * (6 * x₀) := by
      rw [norm_mul]; exact mul_le_mul (hentryZ _ _) (hentryZ _ _) (norm_nonneg _) (by positivity)
    have a1 := hentryE 0 0
    have a2 := hentryE 1 1
    calc ‖(E 0 0 + E 1 1) + Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0‖
        ≤ ‖(E 0 0 + E 1 1) + Z 0 0 * Z 1 1‖ + ‖Z 0 1 * Z 1 0‖ := norm_sub_le _ _
      _ ≤ ‖E 0 0‖ + ‖E 1 1‖ + ‖Z 0 0 * Z 1 1‖ + ‖Z 0 1 * Z 1 0‖ := by
          gcongr; exact norm_add₃_le
      _ ≤ 122 * x₀ ^ 2 := by nlinarith
  have hd10 : ‖Matrix.det W - 1‖ ≤ 1 / 10 := by nlinarith
  obtain ⟨hr0, hrsq, hrnear, hslit⟩ := cpow_half_near_one (Matrix.det W) hd10
  set r := (Matrix.det W) ^ (1 / 2 : ℂ) with hr
  have hrclose : ‖r - 1‖ ≤ 122 * x₀ ^ 2 := hrnear.trans hdet
  have hrnorm : 1 / 2 ≤ ‖r‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖r‖ + ‖r - 1‖ := by
      have := norm_sub_le r (r - 1)
      simpa using this
    simp only [norm_one] at h1
    nlinarith
  have hrinv : ‖r⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  set u := r⁻¹ • W with hu
  have hav : u = r⁻¹ • W := rfl
  have hWn : ‖W‖ ≤ 3 / 2 := by
    have h1 : ‖W‖ ≤ ‖(1 : ComplexMatrix2)‖ + ‖Z‖ := by rw [hWZ]; exact norm_add_le _ _
    rw [norm_one] at h1
    nlinarith
  have hun : ‖u‖ ≤ 3 := by
    rw [hav]
    calc ‖r⁻¹ • W‖ ≤ ‖r⁻¹‖ * ‖W‖ := norm_smul_le _ _
      _ ≤ 2 * (3 / 2) := by gcongr
      _ = 3 := by norm_num
  have hru : r • u = W := by
    rw [hav, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  set G := u - 1 - Complex.I • M with hG
  have hGn : ‖G‖ ≤ 391 * x₀ ^ 2 := by
    have e : G = E - (r - 1) • u := by
      have h1 : (r - 1) • u = W - u := by rw [sub_smul, one_smul, hru]
      rw [h1, hG, hE]
      abel
    rw [e]
    calc ‖E - (r - 1) • u‖ ≤ ‖E‖ + ‖(r - 1) • u‖ := norm_sub_le _ _
      _ ≤ ‖E‖ + ‖r - 1‖ * ‖u‖ := by gcongr; exact norm_smul_le _ _
      _ ≤ 25 * x₀ ^ 2 + 122 * x₀ ^ 2 * 3 := by gcongr
      _ = 391 * x₀ ^ 2 := by ring
  have hXn : ‖u - 1‖ ≤ 9 * x₀ := by
    have e : u - 1 = G + Complex.I • M := by rw [hG]; abel
    rw [e]
    have : ‖G + Complex.I • M‖ ≤ ‖G‖ + ‖Complex.I • M‖ := norm_add_le _ _
    nlinarith
  have hdetu : Matrix.det u = 1 := by
    rw [hav, Matrix.det_smul, Fintype.card_fin, inv_pow, hrsq, inv_mul_cancel₀]
    intro h0
    exact hr0 (by rw [hr, h0]; simp)
  have ht1 : ComplexMatrix2.operatorNorm (u - 1) < 1 := by
    have : ComplexMatrix2.operatorNorm (u - 1) = ‖u - 1‖ := rfl
    rw [this]; linarith
  obtain ⟨-, -, -, -, -, -, hlog1, -⟩ := hc.2.1 u _ rfl ht1
  have hlogn : ‖ComplexMatrix2.logSeries u - (u - 1)‖ ≤ 81 * x₀ ^ 2 := by
    refine le_trans hlog1 ?_
    have h0 : ComplexMatrix2.operatorNorm (u - 1) = ‖u - 1‖ := rfl
    rw [h0]
    set t := ‖u - 1‖ with ht
    rw [div_le_iff₀ (by linarith)]
    have h2 : t ^ 2 ≤ (9 * x₀) ^ 2 := by gcongr
    nlinarith
  have hexpu : ComplexMatrix2.matExp (ComplexMatrix2.logSeries u) = u := by
    have := ((hel.2.2.2.1 (u - 1) ht1).2.2.2.2)
    simpa using this
  have hlogsl : ComplexMatrix2.logSeries u ∈ ComplexMatrix2.traceless :=
    (hel.2.2.2.2.2.2.1 u hdetu (by
      have : ComplexMatrix2.operatorNorm (u - 1) = ‖u - 1‖ := rfl
      rw [this]; linarith)).2
  set N := Complex.I⁻¹ • ComplexMatrix2.logSeries u - M with hN
  have hIN : Complex.I • (M + N) = ComplexMatrix2.logSeries u := by
    rw [hN, add_sub_cancel, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  refine ⟨hrclose, N, ?_, ?_, ?_⟩
  · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hlogsl) ?_
    exact htrM
  · have e0 : (ComplexMatrix2.logSeries u - (u - 1)) + G =
        ComplexMatrix2.logSeries u - Complex.I • M := by
      rw [hG]; abel
    have e : N = Complex.I⁻¹ • ((ComplexMatrix2.logSeries u - (u - 1)) + G) := by
      rw [e0, hN, smul_sub, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    rw [e]
    have h1 : ‖Complex.I⁻¹ • ((ComplexMatrix2.logSeries u - (u - 1)) + G)‖ =
        ‖(ComplexMatrix2.logSeries u - (u - 1)) + G‖ := by
      rw [norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
    rw [h1]
    have h2 : ‖(ComplexMatrix2.logSeries u - (u - 1)) + G‖ ≤ 81 * x₀ ^ 2 + 391 * x₀ ^ 2 :=
      (norm_add_le _ _).trans (add_le_add hlogn hGn)
    linarith
  · rw [hIN, hexpu]
theorem normalizedMeanOfExp_holds (hlin : RunningCouplingSlope.LinearSmoothingContourFormula)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hc : ComplexMatrix2.ExpLogSeriesConvergence)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    RunningCouplingSlope.NormalizedMeanOfExp := by
  intro L hL
  have hLpos : 0 < L := by have := hL.2; omega
  refine ⟨1 / (100 * L), 600 * (L : ℝ) ^ 2, by positivity, by positivity, ?_⟩
  intro n k j hn hj A hA a ha haρ hAa c hcp
  have hK : 0 < k := by omega
  set x₀ : ℝ := L * a with hx₀
  have hx0 : 0 ≤ x₀ := by positivity
  have hx1 : x₀ ≤ 1 / 100 := by
    have : (L : ℝ) * a ≤ L * (1 / (100 * L)) := by gcongr
    calc x₀ ≤ L * (1 / (100 * L)) := this
      _ = 1 / 100 := by field_simp
  have hform : ∀ b, A b.opposite = -A b := hA.2
  have hAtr : ∀ b, ComplexMatrix2.fullTrace (A b) = 0 := by
    intro b
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact hA.1 b ⟨μ, h⟩
    · have hp : (PeriodicLattice.Bond.opposite b).IsPositivelyOriented :=
        ⟨μ, by change b.source - b.target = _; rw [← neg_sub, h, neg_neg]⟩
      have h1 := hA.1 _ hp
      have h2 : ComplexMatrix2.fullTrace (A b.opposite) = 0 := h1
      rw [hform, ComplexMatrix2.fullTrace, Matrix.trace_neg, neg_eq_zero] at h2
      exact h2
  have hcard := ((hb L hL n k hn).1 j hj c hcp).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hcp
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    have h1 : S.card = (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [h1, ← Nat.card_coe_set_eq, hcard]
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  set V : Edge L n k j → ComplexMatrix2 := PeriodicLattice.expTwist A (fun _ => 1) with hVdef
  have hV : ∀ b, V b = ComplexMatrix2.matExp (Complex.I • A b) := by
    intro b
    simp only [hVdef, PeriodicLattice.expTwist, mul_one]
    split_ifs with h
    · rfl
    · rw [matExp_inv, hform]
      congr 1
      simp
  have hrevV : ∀ b, V b.opposite = (V b)⁻¹ := by
    intro b
    rw [hV, hV, matExp_inv, hform]
    congr 1
    simp
  have hdetV : ∀ b, Matrix.det (V b) = 1 := by
    intro b
    rw [hV, (hel.2.2.2.2.2.1 _)]
    have : ComplexMatrix2.fullTrace (Complex.I • A b) = 0 := by
      have := hAtr b
      simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at this ⊢
      simp [this]
    rw [this]
    simp
  have hmean : contourMean V c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hMdef : linearSmoothing L n k j A c = w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
      (PeriodicLattice.bondFormSumAlong A (contourLeg c.source x π) +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.bondFormSumAlong A
          (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)) := by
    rw [hlin L hL n k j hn hj A c hcp, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hlegLen : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        ∀ π, (contourLeg y x π).length ≤ 2 * L := by
    intro y x hx π
    obtain ⟨d, hd1, -⟩ := (hcf L n k hL hn j hj y x hx).1
    have hspec : PeriodicLattice.IsBlockOffset y x (PeriodicLattice.blockOffset y x) :=
      Classical.epsilon_spec ⟨d, hd1⟩
    rw [contourLeg, length_stepsThroughAxes]
    have hb1 : ∀ μ, ((PeriodicLattice.blockOffset y x) μ).natAbs ≤ L / 2 := by
      intro μ
      have h3 := hspec.2 μ
      have h4 : (((PeriodicLattice.blockOffset y x) μ).natAbs : ℤ) =
          |(PeriodicLattice.blockOffset y x) μ| := Int.natCast_natAbs _
      omega
    have h2 := List.sum_le_card_nsmul (((List.finRange 4).map π).map fun μ =>
      ((PeriodicLattice.blockOffset y x) μ).natAbs) (L / 2) (by
        intro a ha
        obtain ⟨μ, -, rfl⟩ := List.mem_map.mp ha
        exact hb1 μ)
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at h2
    omega
  let Mx : Vertex L n k j → Equiv.Perm (Fin 4) → ComplexMatrix2 := fun x π =>
    PeriodicLattice.bondFormSumAlong A (contourLeg c.source x π) +
      PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
      PeriodicLattice.bondFormSumAlong A (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
  have hmapV : ∀ l : List (Edge L n k j), l.map V =
      (l.map A).map fun X => ComplexMatrix2.matExp (Complex.I • X) := by
    intro l
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun b _ => hV b
  have hcv : ∀ x ∈ S, ∀ π,
      ‖contourHolonomy V c x π - 1 - Complex.I • Mx x π‖ ≤ 25 * x₀ ^ 2 ∧
        ‖Mx x π‖ ≤ 5 * x₀ := by
    intro x hx π
    have hx1 : x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) := by simpa [hSdef] using hx
    have hx2 := hcross.1.mapsTo hx1
    have hlen1 := hlegLen c.source x hx1 π
    have hlen2 := hlegLen c.target (PeriodicLattice.shiftAcross c x) hx2 π
    have hlen3 := (hcross.2 x hx1).2.1
    set Γ := contourLeg c.source x π ++ PeriodicLattice.crossingPath c x ++
      PeriodicLattice.reversePath
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) π) with hΓ
    have e1 : contourHolonomy V c x π =
        ((Γ.map A).map fun X => ComplexMatrix2.matExp (Complex.I • X)).prod := by
      rw [← hmapV, contourHolonomy, inv_pathHolonomy V hrevV hdetV, hΓ]
      simp [PeriodicLattice.pathHolonomy, List.map_append, List.prod_append, mul_assoc]
    have e2 : (Γ.map A).sum = Mx x π := by
      have : (Γ.map A).sum = PeriodicLattice.bondFormSumAlong A (contourLeg c.source x π) +
          PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) +
          PeriodicLattice.bondFormSumAlong A (PeriodicLattice.reversePath
            (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)) := by
        simp [hΓ, PeriodicLattice.bondFormSumAlong, List.map_append, List.sum_append, add_assoc]
      rw [this, bondFormSumAlong_reversePath A hform]
      simp only [Mx]
      abel
    have hlen : Γ.length ≤ 5 * L := by
      simp only [hΓ, List.length_append, PeriodicLattice.reversePath, List.length_reverse,
        List.length_map]
      omega
    have hlenR : (Γ.length : ℝ) ≤ 5 * L := by exact_mod_cast hlen
    have hma : (Γ.length : ℝ) * a ≤ 5 * x₀ := by
      calc (Γ.length : ℝ) * a ≤ 5 * L * a := by gcongr
        _ = 5 * x₀ := by rw [hx₀]; ring
    have hma0 : 0 ≤ (Γ.length : ℝ) * a := by positivity
    obtain ⟨h1, -, -⟩ := norm_prod_matExp_sub hc a ha (Γ.map A) (by
      intro X hX
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hX
      exact hAa b)
    simp only [List.length_map] at h1
    rw [e2, ← e1] at h1
    constructor
    · refine h1.trans ?_
      have h2 : |Real.exp ((Γ.length : ℝ) * a) - 1 - (Γ.length : ℝ) * a| ≤
          ((Γ.length : ℝ) * a) ^ 2 :=
        Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hma0]; linarith)
      have h3 := (abs_le.mp h2).2
      have h4 : ((Γ.length : ℝ) * a) ^ 2 ≤ (5 * x₀) ^ 2 := by gcongr
      nlinarith
    · rw [← e2]
      exact (norm_list_map_sum_le A a hAa Γ).trans hma
  have hwval : w = (((1 / (24 * (L : ℝ) ^ 4) : ℝ)) : ℂ) := by
    rw [hw, PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    rw [zpow_neg]
    field_simp
  have hwnorm : ‖w‖ = 1 / (24 * (L : ℝ) ^ 4) := by
    rw [hwval, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcount : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2) =
      (((24 * (L : ℝ) ^ 4 : ℝ)) : ℂ) • (1 : ComplexMatrix2) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    norm_num [Nat.factorial]
    ring
  have hone : w • ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2) = 1 := by
    rw [hcount, smul_smul, hwval, ← Complex.ofReal_mul]
    have : 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4) = 1 := by field_simp
    rw [this]
    simp
  have hmb : ∀ (f : Vertex L n k j → Equiv.Perm (Fin 4) → ComplexMatrix2) (B : ℝ),
      (∀ x ∈ S, ∀ π, ‖f x π‖ ≤ B) → ‖w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), f x π‖ ≤ B := by
    intro f B hf
    have h1 : ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), f x π‖ ≤
        ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), B := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hf x hx π)
    have h2 : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), B = (24 * (L : ℝ) ^ 4) * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard,
        nsmul_eq_mul]
      push_cast
      norm_num [Nat.factorial]
      ring
    rw [h2] at h1
    calc ‖w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), f x π‖
        ≤ ‖w‖ * ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), f x π‖ := norm_smul_le _ _
      _ ≤ ‖w‖ * ((24 * (L : ℝ) ^ 4) * B) := by gcongr
      _ = B := by rw [hwnorm]; field_simp
  set M := linearSmoothing L n k j A c with hM
  have hMn : ‖M‖ ≤ 5 * x₀ := by
    rw [hMdef]
    exact hmb _ _ fun x hx π => (hcv x hx π).2
  set E := contourMean V c - 1 - Complex.I • M with hE
  have hEn : ‖E‖ ≤ 25 * x₀ ^ 2 := by
    have e : E = w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
        (contourHolonomy V c x π - 1 - Complex.I • Mx x π) := by
      have h0 : w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4),
          (contourHolonomy V c x π - 1 - Complex.I • Mx x π) =
          w • (∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π) -
            w • (∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2)) -
            Complex.I • (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), Mx x π) := by
        simp only [Finset.sum_sub_distrib, smul_sub, ← Finset.smul_sum]
        rw [smul_comm Complex.I w]
      rw [h0, hone, ← hmean, hE, hMdef]
    rw [e]
    exact hmb _ _ fun x hx π => (hcv x hx π).1
  have htrΓ : ∀ Γ : List (Edge L n k j),
      ComplexMatrix2.fullTrace (PeriodicLattice.bondFormSumAlong A Γ) = 0 := by
    intro Γ
    induction Γ with
    | nil => simp [PeriodicLattice.bondFormSumAlong, ComplexMatrix2.fullTrace]
    | cons b l ih =>
      have := hAtr b
      simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons,
        ComplexMatrix2.fullTrace, Matrix.trace_add] at ih this ⊢
      rw [ih, this, add_zero]
  have htrM : ComplexMatrix2.fullTrace M = 0 := by
    rw [hMdef]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_add,
      Matrix.trace_sub]
    have h1 := htrΓ
    simp only [ComplexMatrix2.fullTrace] at h1
    simp [h1]
  obtain ⟨h1, N, hN, hNn, hNe⟩ :=
    unimodular_part_eq_matExp hel hc (contourMean V c) M x₀ hx0 hx1 htrM hMn hEn
  have hbig : ∀ y : ℝ, y ≤ 472 * x₀ ^ 2 → y ≤ 600 * (L : ℝ) ^ 2 * a ^ 2 := by
    intro y hy
    have : 472 * x₀ ^ 2 ≤ 600 * (L : ℝ) ^ 2 * a ^ 2 := by
      rw [hx₀, mul_pow]; nlinarith [sq_nonneg ((L : ℝ) * a)]
    linarith
  have h1' : ‖meanRadius V c - 1‖ ≤ 122 * x₀ ^ 2 := h1
  refine ⟨hbig _ (by nlinarith [sq_nonneg x₀]), N, hN, hbig _ hNn, hNe⟩
end YangMills.Construction.RunningCouplingSlope.MeanOfExp
end
