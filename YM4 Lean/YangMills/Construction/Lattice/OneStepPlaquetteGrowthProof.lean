import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquette
import YangMills.Construction.Lattice.FirstDerivativeOfTheAverageLogarithm
import YangMills.Construction.Lattice.FirstDerivativeOfTheContourVariables
import YangMills.Construction.Lattice.LinearAveragesRoundACoarsePlaquette
import YangMills.Construction.Lattice.OneStepPlaquetteGrowth
import YangMills.Construction.Lattice.SecondOrderBoundOfTheAverageLogarithm
import YangMills.Construction.Lattice.SumOfARealBondFunctionRoundAPlaquette
import YangMills.Construction.Matrices.RestatedElementaryInequalities
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace StepCurvatureGrowth
theorem expLoop_sub_one_le (hE : Matrices.ComplexMatrix2.ElementaryInequalitiesStatement)
    (A₁ A₂ A₃ A₄ : Matrices.ComplexMatrix2) (hA : ‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖ ≤ 1) :
    ‖Matrices.ComplexMatrix2.matExp (Complex.I • A₁) * Matrices.ComplexMatrix2.matExp (Complex.I • A₂) *
        (Matrices.ComplexMatrix2.matExp (Complex.I • A₃))⁻¹ *
        (Matrices.ComplexMatrix2.matExp (Complex.I • A₄))⁻¹ - 1‖ ≤
      ‖A₁ + A₂ - A₃ - A₄‖ + (‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖) ^ 2 := by
  have hI : ∀ B : Matrices.ComplexMatrix2, ‖Complex.I • B‖ = ‖B‖ := fun B => by
    rw [norm_smul, Complex.norm_I, one_mul]
  have key := ((hE.1 4 le_rfl ![Complex.I • A₁, Complex.I • A₂, -(Complex.I • A₃),
    -(Complex.I • A₄)]).1 (by
      simpa [Fin.sum_univ_four, hI, add_assoc] using hA)).1
  have hprod : Matrices.ComplexMatrix2.expListProduct ![Complex.I • A₁, Complex.I • A₂,
      -(Complex.I • A₃), -(Complex.I • A₄)] =
      Matrices.ComplexMatrix2.matExp (Complex.I • A₁) * Matrices.ComplexMatrix2.matExp (Complex.I • A₂) *
        (Matrices.ComplexMatrix2.matExp (Complex.I • A₃))⁻¹ *
        (Matrices.ComplexMatrix2.matExp (Complex.I • A₄))⁻¹ := by
    simp [Matrices.ComplexMatrix2.expListProduct, List.ofFn_succ, Matrix.exp_neg, mul_assoc]
  have hsum : ∑ j, (![Complex.I • A₁, Complex.I • A₂, -(Complex.I • A₃),
      -(Complex.I • A₄)] : Fin 4 → Matrices.ComplexMatrix2) j =
      Complex.I • (A₁ + A₂ - A₃ - A₄) := by
    simp [Fin.sum_univ_four, smul_add, sub_eq_add_neg]
  have hnorms : ∑ j, Matrices.ComplexMatrix2.operatorNorm ((![Complex.I • A₁, Complex.I • A₂,
      -(Complex.I • A₃), -(Complex.I • A₄)] : Fin 4 → Matrices.ComplexMatrix2) j) =
      ‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖ := by
    simp [Fin.sum_univ_four, hI]
  rw [hprod, hsum, hnorms] at key
  set P := Matrices.ComplexMatrix2.matExp (Complex.I • A₁) *
    Matrices.ComplexMatrix2.matExp (Complex.I • A₂) *
    (Matrices.ComplexMatrix2.matExp (Complex.I • A₃))⁻¹ *
    (Matrices.ComplexMatrix2.matExp (Complex.I • A₄))⁻¹ with hP
  have htri : ‖P - 1‖ ≤ ‖P - 1 - Complex.I • (A₁ + A₂ - A₃ - A₄)‖ +
      ‖Complex.I • (A₁ + A₂ - A₃ - A₄)‖ := by
    simpa using norm_add_le (P - 1 - Complex.I • (A₁ + A₂ - A₃ - A₄))
      (Complex.I • (A₁ + A₂ - A₃ - A₄))
  rw [hI] at htri
  linarith
theorem constant_arith {ℓ ϖ ρ X N : ℝ} (hρ : 0 ≤ ρ)
    (hN : N ≤ ℓ ^ 2 * (ϖ + 35 * (3 * Real.pi * ℓ * ϖ) ^ 2))
    (hX : X ≤ N + 8 * ((3 * Real.pi * ℓ * ϖ) ^ 2 * ρ) + 16 * ((3 * Real.pi * ℓ * ϖ) ^ 2 * ρ)) :
    X ≤ ℓ ^ 2 * ϖ + (3 * Real.pi * ℓ) ^ 2 * (35 * ℓ ^ 2 + 40 * ρ) * ϖ ^ 2 := by
  have hnn : 0 ≤ (3 * Real.pi * ℓ * ϖ) ^ 2 * ρ := by positivity
  nlinarith [hnn]
end StepCurvatureGrowth
theorem stepCurvatureGrowth_holds
    (hLoop : ContourHolonomyDerivative.Statement)
    (hDeriv : HasDerivBlockAverageLogAtZero)
    (hSecondOrder : BlockAverageLogSecondOrderBound)
    (hLin : CoarsePlaquetteLinearAverageBound.Statement)
    (hBondSum : RealBondSumAroundPlaquetteBound)
    (hGauge : CoarsePlaquetteCombGauge)
    (hCov : stepCovarianceDomainsStatement)
    (hIneq : Matrices.ComplexMatrix2.RestatedElementaryInequalitiesStatement) :
    StepCurvatureGrowth := by
  intro L hL
  have hE : Matrices.ComplexMatrix2.ElementaryInequalitiesStatement := hIneq
  have hR : IsStepRadius L (stepRadius L) := (hCov L hL).2.1
  have hr : 0 < stepRadius L := hR.pos
  have hr16 : stepRadius L ≤ 1 / 16 := hR.le
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hκ : 0 < Averaging.SingleStep.loopVariableConstant L := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have h1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
    unfold Averaging.SingleStep.loopVariableConstant Averaging.SingleStep.loopAngleConstant
    positivity
  have hbound : 0 < stepCurvatureBound L := by
    unfold stepCurvatureBound
    refine lt_min (by positivity) (lt_min (by positivity) ?_)
    positivity
  set r := stepRadius L with hrdef
  set ϖ' : ℝ := min (stepCurvatureBound L) (r / (12 * Real.pi * L)) with hϖ'
  set C : ℝ := (3 * Real.pi * L) ^ 2 * (35 * (L : ℝ) ^ 2 + 40 * (r ^ 2)⁻¹) with hC
  have hpair : IsCurvatureGrowthPair L C ϖ' := by
    refine ⟨?_, lt_min hbound (by positivity), min_le_left _ _, ?_⟩
    · have h1 : (1 : ℝ) ≤ (3 * Real.pi * L) ^ 2 := by
        have h0 : (1 : ℝ) ≤ 3 * Real.pi * L := by nlinarith
        exact one_le_pow₀ h0
      have h2 : (1 : ℝ) ≤ 35 * (L : ℝ) ^ 2 + 40 * (r ^ 2)⁻¹ := by
        have : 0 ≤ (r ^ 2)⁻¹ := by positivity
        nlinarith
      exact one_le_mul_of_one_le_of_one_le h1 h2
    · intro m K n hm hn s p W hW hϖ
      set ϖ := maxPlaquetteDeviation (plaquetteCornerBlockSites p) W with hϖdef
      have hϖ0 : 0 ≤ ϖ := by
        refine Real.sSup_nonneg ?_
        rintro _ ⟨q, -, rfl⟩
        exact norm_nonneg _
      obtain ⟨a, hreal, hsup, hedges, hface, heq⟩ :=
        hGauge L hL m K n hm hn s p W hW (hϖ.trans (min_le_left _ _))
      change supOperatorNorm a ≤ 3 * Real.pi * L * ϖ at hsup
      change ∀ c ∈ ({firstEdge p, secondEdge p, thirdEdge p,
          fourthEdge p} : Set (BondAtLevel L m K (n + 1))),
        supOperatorNorm (LieBondField.restrictToDoubleBlock c a) ≤ 3 * Real.pi * L * ϖ at hedges
      change ∀ q : PlaquetteAtLevel L m K n, q.LiesIn (fourCornerBlockSites p) →
        Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (expTwist (LieBondField.matrixValues a) trivialGaugeField) q
          - 1) ≤ ϖ at hface
      set σ : ℝ := 3 * Real.pi * L * ϖ with hσ
      have hσr : σ ≤ r / 4 := by
        have h12 : ϖ ≤ r / (12 * Real.pi * L) := hϖ.trans (min_le_right _ _)
        have hpos : 0 < 12 * Real.pi * L := by positivity
        rw [le_div_iff₀ hpos] at h12
        rw [hσ]
        nlinarith
      have hsup0 : 0 ≤ supOperatorNorm a := Real.iSup_nonneg fun _ => norm_nonneg _
      have hquarter : supOperatorNorm a ≤ 1 / 4 := by linarith
      have hD : ∀ q : PlaquetteAtLevel L m K n, q.LiesIn (fourCornerBlockSites p) →
          Matrices.ComplexMatrix2.operatorNorm
            (bondFormSumAlong (LieBondField.matrixValues a) q.boundaryBonds) ≤ ϖ + 35 * σ ^ 2 := by
        intro q hq
        have h := hBondSum L hL m K n hm hn.le (fourCornerBlockSites p) a hreal hquarter q hq
        have hsq : supOperatorNorm a ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hsup0 hsup 2
        have := hface q hq
        linarith
      have hlin := hLin L hL m K n hm hn s p a (ϖ + 35 * σ ^ 2) hD
      have hedge : ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
          c ∈ ({firstEdge p, secondEdge p, thirdEdge p,
            fourthEdge p} : Set (BondAtLevel L m K (n + 1))) →
          Matrices.ComplexMatrix2.matExp
              (Complex.I • blockAverageLog s c (LieBondField.restrictToDoubleBlock c a)) =
              restrictedSchemeAverage s a c ∧
            ‖blockAverageLog s c (LieBondField.restrictToDoubleBlock c a)‖ ≤ σ * r⁻¹ ∧
            ‖blockAverageLog s c (LieBondField.restrictToDoubleBlock c a) - linearSchemeAverage s
              (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock c a)) c‖ ≤
              2 * (σ ^ 2 * (r ^ 2)⁻¹) := by
        intro c hc hmem
        have hc0 : 0 ≤ supOperatorNorm (LieBondField.restrictToDoubleBlock c a) :=
          Real.iSup_nonneg fun _ => norm_nonneg _
        have hcσ := hedges c hmem
        obtain ⟨h1, h2, h3⟩ := hSecondOrder L hL m K n hm hn s c hc
          (LieBondField.restrictToDoubleBlock c a) (hcσ.trans hσr)
        refine ⟨h1, ?_, ?_⟩
        · refine h2.trans ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hcσ (by positivity)
        · refine h3.trans ?_
          have hsq := pow_le_pow_left₀ hc0 hcσ 2
          rw [div_eq_mul_inv, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsq (by positivity)) (by norm_num)
      have hfwd : ∀ (x : SiteAtLevel L m K (n + 1)) (μ : Fin 4),
          (Bond.forwardFrom x μ).IsPositivelyOriented :=
        fun x μ => ⟨μ, by simp [Bond.forwardFrom]⟩
      obtain ⟨e₁, n₁, d₁⟩ := hedge (firstEdge p) (hfwd _ _) (by simp)
      obtain ⟨e₂, n₂, d₂⟩ := hedge (secondEdge p) (hfwd _ _) (by simp)
      obtain ⟨e₃, n₃, d₃⟩ := hedge (thirdEdge p) (hfwd _ _) (by simp)
      obtain ⟨e₄, n₄, d₄⟩ := hedge (fourthEdge p) (hfwd _ _) (by simp)
      set A₁ := blockAverageLog s (firstEdge p)
        (LieBondField.restrictToDoubleBlock (firstEdge p) a)
      set A₂ := blockAverageLog s (secondEdge p)
        (LieBondField.restrictToDoubleBlock (secondEdge p) a)
      set A₃ := blockAverageLog s (thirdEdge p)
        (LieBondField.restrictToDoubleBlock (thirdEdge p) a)
      set A₄ := blockAverageLog s (fourthEdge p)
        (LieBondField.restrictToDoubleBlock (fourthEdge p) a)
      have hρ : σ * r⁻¹ ≤ 1 / 4 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hr]
        linarith
      have hs4 : ‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖ ≤ 4 * (σ * r⁻¹) := by linarith
      have hs0 : 0 ≤ ‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖ := by positivity
      have hloop := StepCurvatureGrowth.expLoop_sub_one_le hE A₁ A₂ A₃ A₄ (by linarith)
      rw [e₁, e₂, e₃, e₄] at hloop
      have hsq : (‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖) ^ 2 ≤ 16 * (σ ^ 2 * (r ^ 2)⁻¹) := by
        have := pow_le_pow_left₀ hs0 hs4 2
        have he : (4 * (σ * r⁻¹)) ^ 2 = 16 * (σ ^ 2 * (r ^ 2)⁻¹) := by
          simp only [mul_pow, inv_pow]; ring
        linarith
      have hdiff : ‖A₁ + A₂ - A₃ - A₄‖ ≤ ‖plaquetteLinearAverage s a p‖ +
          8 * (σ ^ 2 * (r ^ 2)⁻¹) := by
        unfold plaquetteLinearAverage
        set B₁ := linearSchemeAverage s
          (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (firstEdge p) a))
          (firstEdge p)
        set B₂ := linearSchemeAverage s
          (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (secondEdge p) a))
          (secondEdge p)
        set B₃ := linearSchemeAverage s
          (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (thirdEdge p) a))
          (thirdEdge p)
        set B₄ := linearSchemeAverage s
          (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (fourthEdge p) a))
          (fourthEdge p)
        have hsplit : A₁ + A₂ - A₃ - A₄ = (B₁ + B₂ - B₃ - B₄) + (A₁ - B₁) + (A₂ - B₂) -
            (A₃ - B₃) - (A₄ - B₄) := by abel
        rw [hsplit]
        have t1 := norm_sub_le ((B₁ + B₂ - B₃ - B₄) + (A₁ - B₁) + (A₂ - B₂) - (A₃ - B₃))
          (A₄ - B₄)
        have t2 := norm_sub_le ((B₁ + B₂ - B₃ - B₄) + (A₁ - B₁) + (A₂ - B₂)) (A₃ - B₃)
        have t3 := norm_add_le ((B₁ + B₂ - B₃ - B₄) + (A₁ - B₁)) (A₂ - B₂)
        have t4 := norm_add_le (B₁ + B₂ - B₃ - B₄) (A₁ - B₁)
        linarith
      have hfinal : ‖plaquetteAverageHolonomy s a p - 1‖ ≤
          ‖plaquetteLinearAverage s a p‖ + 8 * (σ ^ 2 * (r ^ 2)⁻¹) +
            16 * (σ ^ 2 * (r ^ 2)⁻¹) := by
        have : plaquetteAverageHolonomy s a p = restrictedSchemeAverage s a (firstEdge p) *
            restrictedSchemeAverage s a (secondEdge p) *
            (restrictedSchemeAverage s a (thirdEdge p))⁻¹ *
            (restrictedSchemeAverage s a (fourthEdge p))⁻¹ := rfl
        rw [this]
        linarith
      rw [show Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy (schemeBlockAverage s W) p - 1) =
        ‖plaquetteAverageHolonomy s a p - 1‖ from heq]
      exact StepCurvatureGrowth.constant_arith (by positivity) hlin hfinal
  have hspec : IsCurvatureGrowthPair L (curvatureGrowthConst L) (curvatureGrowthRadius L) :=
    Classical.epsilon_spec (p := fun q : ℝ × ℝ => IsCurvatureGrowthPair L q.1 q.2)
      ⟨(C, ϖ'), hpair⟩
  refine ⟨hspec, ?_⟩
  intro m K n hm hn s c hc a
  exact ⟨hDeriv L hL m K n hm hn s c hc a, rfl,
    fun y hy x hx => hLoop L hL m K n hm hn s c hc a y hy x hx⟩
end YangMills.Construction.PeriodicLattice
