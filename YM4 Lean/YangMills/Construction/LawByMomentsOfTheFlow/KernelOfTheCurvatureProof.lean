import YangMills.Construction.FreeKernel.SecondDifferencesOfTheGreenFunctionOfTheTorusProof
import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvatureOnATorus
import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvatureOnTheLattice
import YangMills.Construction.LawByMomentsOfTheFlow.SecondDifferencesOnATorusNearTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.CyclicFormula (OrderedDirectionPair exteriorSquareMap inversionMatrix)
open YangMills.Construction.FourDimKernel (intVecNorm mixedSecondDiff mixedSecondPartial)
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint (continuumGreenFunction forwardDiff backwardDiff)
open YangMills.Construction.PeriodicLattice.VectorClasses (greenOnVectors)
open YangMills.Construction.TestFunctions (EuclideanFourSpace)
open YangMills.Construction.WeightedResponses (OrientedPlaquette)
private def greenHessian (x : Fin 4 → ℝ) (r : ℝ) (i j : Fin 4) : ℝ :=
  -(1 / (2 * Real.pi ^ 2 * r ^ 4)) * ((if i = j then 1 else 0) - 4 * x i * x j / r ^ 2)
private theorem planePairEntry_sub_le {D D' : Fin 4 → Fin 4 → ℝ} {ε : ℝ} (h : ∀ i j, |D i j - D' i j| ≤ ε)
    (p q : OrderedDirectionPair) : |planePairEntry D p q - planePairEntry D' p q| ≤ 4 * ε := by
  have h0 : 0 ≤ ε := (abs_nonneg _).trans (h 0 0)
  have h1 := abs_le.1 (h p.1.1 q.1.1)
  have h2 := abs_le.1 (h p.1.1 q.1.2)
  have h3 := abs_le.1 (h p.1.2 q.1.1)
  have h4 := abs_le.1 (h p.1.2 q.1.2)
  simp only [planePairEntry]
  rw [abs_le]
  split_ifs <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
private theorem planePairEntry_greenHessian (v : EuclideanFourSpace) (hv : v ≠ 0) (p q : OrderedDirectionPair) :
    (Real.pi ^ 2 * ‖v‖ ^ 4)⁻¹ * exteriorSquareMap (inversionMatrix v) p q =
      planePairEntry (greenHessian (fun a => v a) ‖v‖) p q := by
  have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [planePairEntry, greenHessian, exteriorSquareMap, inversionMatrix, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  split_ifs <;> field_simp <;> ring
private theorem abs_pow_succ_sub_pow_succ_le {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAσ : A ≤ σ) (hBσ : B ≤ σ)
    (k : ℕ) : |A ^ (k + 1) - B ^ (k + 1)| ≤ ((k : ℝ) + 1) * σ ^ k * |A - B| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : A ^ (k + 1 + 1) - B ^ (k + 1 + 1) = A * (A ^ (k + 1) - B ^ (k + 1)) + B ^ (k + 1) * (A - B) := by
      ring
    have hσ : 0 ≤ σ := hA.trans hAσ
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg (pow_nonneg hB _)]
    have h1 : A * |A ^ (k + 1) - B ^ (k + 1)| ≤ σ * (((k : ℝ) + 1) * σ ^ k * |A - B|) :=
      mul_le_mul hAσ ih (abs_nonneg _) hσ
    have h2 : B ^ (k + 1) * |A - B| ≤ σ ^ (k + 1) * |A - B| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hBσ _) (abs_nonneg _)
    push_cast
    have e2 : ((k : ℝ) + 1 + 1) * σ ^ (k + 1) * |A - B| =
        σ * (((k : ℝ) + 1) * σ ^ k * |A - B|) + σ ^ (k + 1) * |A - B| := by ring
    rw [e2]
    linarith
private theorem greenHessian_lipschitz (x y : Fin 4 → ℝ) {a b ρ d : ℝ} (hρ : 1 ≤ ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (hab : |a - b| ≤ 1) (hxa : ∀ μ, |x μ| ≤ a) (hyb : ∀ μ, |y μ| ≤ b) (hxy : ∀ μ, |x μ - y μ| ≤ 1)
    (hd : |d| ≤ 1) (i j : Fin 4) :
    |1 / a ^ 4 * (d - 4 * x i * x j / a ^ 2) - 1 / b ^ 4 * (d - 4 * y i * y j / b ^ 2)| ≤
      64 * (ρ ^ 5)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hρ0 : 0 < ρ := by linarith
  set A : ℝ := a⁻¹ with hA
  set B : ℝ := b⁻¹ with hB
  set σ : ℝ := ρ⁻¹ with hσ
  have hA0 : 0 < A := inv_pos.2 ha0
  have hB0 : 0 < B := inv_pos.2 hb0
  have hσ0 : 0 < σ := inv_pos.2 hρ0
  have hAσ : A ≤ σ := inv_anti₀ hρ0 ha
  have hBσ : B ≤ σ := inv_anti₀ hρ0 hb
  have haA : a * A = 1 := mul_inv_cancel₀ ha0.ne'
  have hbB : b * B = 1 := mul_inv_cancel₀ hb0.ne'
  have e : 1 / a ^ 4 * (d - 4 * x i * x j / a ^ 2) - 1 / b ^ 4 * (d - 4 * y i * y j / b ^ 2) =
      d * (A ^ 4 - B ^ 4) - 4 * ((x i * x j - y i * y j) * A ^ 6 + y i * y j * (A ^ 6 - B ^ 6)) := by
    simp only [hA, hB]
    field_simp
    ring
  rw [e]
  have hAB : |A - B| ≤ A * B := by
    have e1 : A - B = (b - a) * (A * B) := by
      have : (b - a) * (A * B) = (b * B) * A - (a * A) * B := by ring
      rw [this, hbB, haA]
      ring
    rw [e1, abs_mul, abs_of_pos (by positivity : 0 < A * B), abs_sub_comm]
    nlinarith [abs_nonneg (a - b), mul_pos hA0 hB0]
  have hABσ : A * B ≤ σ ^ 2 := by
    rw [sq]
    exact mul_le_mul hAσ hBσ hB0.le hσ0.le
  have h4 : |A ^ 4 - B ^ 4| ≤ 4 * σ ^ 5 := by
    have h := abs_pow_succ_sub_pow_succ_le hA0.le hB0.le hAσ hBσ 3
    have h2 : |A - B| ≤ σ ^ 2 := hAB.trans hABσ
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (((3 : ℕ) : ℝ) + 1) * σ ^ 3)
    norm_num at h h3 ⊢
    nlinarith
  have hba : b * A ≤ 2 := by
    have h1 : b ≤ 2 * a := by
      have := (abs_le.1 hab).1
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hA0.le
    nlinarith
  have hyy : |y i * y j| ≤ b ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (hyb i) (hyb j) (abs_nonneg _) hb0.le
  have h6 : |y i * y j * (A ^ 6 - B ^ 6)| ≤ 12 * σ ^ 5 := by
    have h := abs_pow_succ_sub_pow_succ_le hA0.le hB0.le hAσ hBσ 5
    have h2 : |A ^ 6 - B ^ 6| ≤ 6 * σ ^ 5 * (A * B) := by
      have h3 := mul_le_mul_of_nonneg_left hAB (by positivity : 0 ≤ (((5 : ℕ) : ℝ) + 1) * σ ^ 5)
      norm_num at h h3 ⊢
      linarith
    rw [abs_mul]
    calc |y i * y j| * |A ^ 6 - B ^ 6| ≤ b ^ 2 * (6 * σ ^ 5 * (A * B)) :=
          mul_le_mul hyy h2 (abs_nonneg _) (by positivity)
      _ = 6 * σ ^ 5 * ((b * B) * (b * A)) := by ring
      _ = 6 * σ ^ 5 * (b * A) := by rw [hbB, one_mul]
      _ ≤ 6 * σ ^ 5 * 2 := mul_le_mul_of_nonneg_left hba (by positivity)
      _ = 12 * σ ^ 5 := by ring
  have h7 : |(x i * x j - y i * y j) * A ^ 6| ≤ 3 * σ ^ 5 := by
    have e1 : x i * x j - y i * y j = (x i - y i) * x j + y i * (x j - y j) := by ring
    have h1 : |x i * x j - y i * y j| ≤ a + b := by
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have t1 : |x i - y i| * |x j| ≤ 1 * a := mul_le_mul (hxy i) (hxa j) (abs_nonneg _) zero_le_one
      have t2 : |y i| * |x j - y j| ≤ b * 1 := mul_le_mul (hyb i) (hxy j) (abs_nonneg _) hb0.le
      linarith
    have h2 : a + b ≤ 3 * a := by
      have := (abs_le.1 hab).1
      linarith
    rw [abs_mul, abs_of_pos (by positivity : 0 < A ^ 6)]
    calc |x i * x j - y i * y j| * A ^ 6 ≤ (3 * a) * A ^ 6 :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      _ = 3 * (a * A) * A ^ 5 := by ring
      _ = 3 * A ^ 5 := by rw [haA]; ring
      _ ≤ 3 * σ ^ 5 := by
          have := pow_le_pow_left₀ hA0.le hAσ 5
          linarith
  have h8 : |d * (A ^ 4 - B ^ 4)| ≤ 4 * σ ^ 5 := by
    rw [abs_mul]
    calc |d| * |A ^ 4 - B ^ 4| ≤ 1 * (4 * σ ^ 5) := mul_le_mul hd h4 (abs_nonneg _) zero_le_one
      _ = 4 * σ ^ 5 := one_mul _
  have e5 : 64 * (ρ ^ 5)⁻¹ = 64 * σ ^ 5 := by
    rw [hσ, inv_pow]
  rw [e5]
  have t := abs_sub (d * (A ^ 4 - B ^ 4)) (4 * ((x i * x j - y i * y j) * A ^ 6 + y i * y j * (A ^ 6 - B ^ 6)))
  have t2 : |4 * ((x i * x j - y i * y j) * A ^ 6 + y i * y j * (A ^ 6 - B ^ 6))| ≤ 4 * (15 * σ ^ 5) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have := abs_add_le ((x i * x j - y i * y j) * A ^ 6) (y i * y j * (A ^ 6 - B ^ 6))
    linarith
  linarith
private theorem intVecNorm_sq (x : Fin 4 → ℤ) : intVecNorm x ^ 2 = ∑ μ, (x μ : ℝ) ^ 2 := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.intVecNorm_sq <;> assumption
private theorem abs_apply_le_intVecNorm (x : Fin 4 → ℤ) (μ : Fin 4) :
    |(x μ : ℝ)| ≤ intVecNorm x := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.abs_coord_le_intVecNorm <;> assumption
private theorem latticeGreen_near_greenHessian (hS : torusSecondDiffNearLatticeStatement)
    (hB : YangMills.Construction.FreeKernel.TorusGreenSecondDiffBound)
    (hM : YangMills.Construction.PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 4 → ℤ, 1 ≤ intVecNorm z → ∀ i j : Fin 4,
      |secondDiffMatrix latticeGreen z i j -
        greenHessian (fun μ => (z μ : ℝ)) (intVecNorm z) i j| ≤
        C * (intVecNorm z ^ 5)⁻¹ := by
  obtain ⟨C₃, h3⟩ := hS
  obtain ⟨-, hB2⟩ := hB
  set Cp := YangMills.Construction.Constants.HeatKernel.fieldConstant.toReal with hCp
  have hCp0 : 0 ≤ Cp := ENNReal.toReal_nonneg
  refine ⟨2 * Cp + |C₃|, by positivity, fun z hz i j => ?_⟩
  set R := intVecNorm z with hR
  have hR0 : 0 < R := by linarith
  set n : ℕ := 3 * ⌈R⌉₊ ^ 2 + 2 with hn
  have hn2 : 2 ≤ n := by omega
  have hceil : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hnR : 3 * R ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    push_cast
    have : R ^ 2 ≤ (⌈R⌉₊ : ℝ) ^ 2 := pow_le_pow_left₀ hR0.le hceil 2
    linarith
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hz' : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2 := fun μ => (abs_apply_le_intVecNorm z μ).trans (by linarith)
  have a1 := h3 n hn2 i j z hz'
  have a2 := hB2 n hn2 i j (1 / 3) (by norm_num) (by norm_num) z hz (by linarith)
  obtain ⟨-, -, -, -, hSD⟩ := hM 2 le_rfl
  have hzv : (fun μ => (z μ : ℝ)) ≠ 0 := by
    intro h
    have h0 : R ^ 2 = 0 := by
      rw [hR, intVecNorm_sq]
      refine Finset.sum_eq_zero fun μ _ => ?_
      have := congrFun h μ
      simp only [Pi.zero_apply] at this
      rw [this]
      norm_num
    have : R ≠ 0 := hR0.ne'
    exact this (pow_eq_zero_iff (by norm_num) |>.1 h0)
  have a3 := (hSD i j (fun μ => (z μ : ℝ)) hzv).2.2
  have a4 : mixedSecondPartial i j continuumGreenFunction (fun μ => (z μ : ℝ)) =
      greenHessian (fun μ => (z μ : ℝ)) R i j := by
    have hE : YangMills.Construction.FourVector.euclidNorm (fun μ => (z μ : ℝ)) = R := rfl
    show YangMills.Construction.FourVector.coordPartialDeriv i
      (YangMills.Construction.FourVector.coordPartialDeriv j continuumGreenFunction) _ = _
    rw [a3, hE]
    simp only [greenHessian, YangMills.Construction.FourVector.kronecker,
      YangMills.Construction.FourVector.propIndicator]
    congr
  rw [a4] at a2
  set T := greenHessian (fun μ => (z μ : ℝ)) R i j
  set X := mixedSecondDiff i j (greenOnVectors n) z
  have hre : secondDiffMatrix (fun w => (greenOnVectors n w).re) z i j = X.re := by
    simp only [X, secondDiffMatrix, mixedSecondDiff, forwardDiff, backwardDiff, Complex.sub_re]
  rw [hre] at a1
  have b1 : |X.re - T| ≤ ‖X - (T : ℂ)‖ := by
    have := Complex.abs_re_le_norm (X - (T : ℂ))
    simpa using this
  have hinv : ((n : ℝ) ^ 4)⁻¹ ≤ (R ^ 5)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    have h1 : R ^ 2 ≤ (n : ℝ) := by nlinarith
    calc R ^ 5 ≤ R ^ 8 := pow_le_pow_right₀ hz (by norm_num)
      _ = (R ^ 2) ^ 4 := by ring
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  have e5 : R ^ (-5 : ℤ) = (R ^ 5)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have e4 : (n : ℝ) ^ (-4 : ℤ) = ((n : ℝ) ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [e5, e4] at a2
  have c1 : C₃ * ((n : ℝ) ^ 4)⁻¹ ≤ |C₃| * (R ^ 5)⁻¹ := by
    have hp : 0 ≤ ((n : ℝ) ^ 4)⁻¹ := by positivity
    calc C₃ * ((n : ℝ) ^ 4)⁻¹ ≤ |C₃| * ((n : ℝ) ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hp
      _ ≤ |C₃| * (R ^ 5)⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
  have c2 : Cp * ((R ^ 5)⁻¹ + ((n : ℝ) ^ 4)⁻¹) ≤ 2 * Cp * (R ^ 5)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hinv hCp0
    linarith
  have c3 : |secondDiffMatrix latticeGreen z i j - T| ≤
      |X.re - secondDiffMatrix latticeGreen z i j| + |X.re - T| := by
    have := abs_sub_le (secondDiffMatrix latticeGreen z i j) X.re T
    rw [abs_sub_comm (secondDiffMatrix latticeGreen z i j) X.re] at this
    exact this
  calc _ ≤ _ := c3
    _ ≤ |C₃| * (R ^ 5)⁻¹ + 2 * Cp * (R ^ 5)⁻¹ := by linarith
    _ = (2 * Cp + |C₃|) * (R ^ 5)⁻¹ := by ring
private theorem intBarycenter_eq_add (P : IntPlaquette) (a : Fin 4) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧ intBarycenter P a = (P.1 a : ℝ) + s := by
  refine ⟨(if a = P.2.1.1 then 1 / 2 else 0) + (if a = P.2.1.2 then 1 / 2 else 0), ?_, ?_, ?_⟩
  · split_ifs <;> norm_num
  · have h := P.2.2
    split_ifs with h1 h2
    · exact absurd (h1 ▸ h2 ▸ h) (lt_irrefl _)
    all_goals norm_num
  · simp [intBarycenter, add_assoc]
private theorem abs_intBarycenter_sub_sub_le (P P' : IntPlaquette) (a : Fin 4) :
    |(intBarycenter P - intBarycenter P') a - (((P.1 - P'.1) a : ℤ) : ℝ)| ≤ 1 / 2 := by
  obtain ⟨s, h0, h1, e⟩ := intBarycenter_eq_add P a
  obtain ⟨s', h0', h1', e'⟩ := intBarycenter_eq_add P' a
  have e2 : (intBarycenter P - intBarycenter P') a = intBarycenter P a - intBarycenter P' a := rfl
  rw [e2, e, e']
  push_cast
  rw [Pi.sub_apply]
  push_cast
  rw [abs_le]
  constructor <;> linarith
private theorem planePairEntry_near_continuum (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hnear : ∀ z : Fin 4 → ℤ, 1 ≤ intVecNorm z → ∀ i j : Fin 4,
      |secondDiffMatrix latticeGreen z i j -
        greenHessian (fun μ => (z μ : ℝ)) (intVecNorm z) i j| ≤
        C₂ * (intVecNorm z ^ 5)⁻¹)
    (P P' : IntPlaquette) (hR : 2 ≤ ‖intBarycenter P - intBarycenter P'‖) :
    |planePairEntry (secondDiffMatrix latticeGreen (P.1 - P'.1)) P.2 P'.2 -
        (Real.pi ^ 2 * ‖intBarycenter P - intBarycenter P'‖ ^ 4)⁻¹ *
          exteriorSquareMap (inversionMatrix (intBarycenter P - intBarycenter P')) P.2 P'.2| ≤
      128 * (C₂ + 64) * (‖intBarycenter P - intBarycenter P'‖ ^ 5)⁻¹ := by
  set u : EuclideanFourSpace := intBarycenter P - intBarycenter P' with hu
  set w : Fin 4 → ℤ := P.1 - P'.1 with hw
  set R := ‖u‖ with hRd
  have hu0 : u ≠ 0 := fun h => by
    have : R = 0 := by rw [hRd, h, norm_zero]
    linarith
  set wv : EuclideanFourSpace := WithLp.toLp 2 (fun a => (w a : ℝ)) with hwv
  have hnorm : ‖wv‖ = intVecNorm w := by
    have h1 : ‖wv‖ ^ 2 = intVecNorm w ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, intVecNorm_sq]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hwv]
    have h2 : 0 ≤ intVecNorm w := Real.sqrt_nonneg _
    exact (sq_eq_sq₀ (norm_nonneg _) h2).1 h1
  have hclose : ‖u - wv‖ ≤ 1 := by
    have h1 : ‖u - wv‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have h2 : ∀ a : Fin 4, ‖(u - wv) a‖ ^ 2 ≤ 1 / 4 := fun a => by
        have h3 := abs_intBarycenter_sub_sub_le P P' a
        have e : (u - wv) a = u a - (w a : ℝ) := by simp [hwv]
        rw [e, Real.norm_eq_abs, sq_abs, ← sq_abs]
        have : |u a - (w a : ℝ)| ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        linarith [this, (by norm_num : ((1 : ℝ) / 2) ^ 2 = 1 / 4)]
      calc ∑ a, ‖(u - wv) a‖ ^ 2 ≤ ∑ _a : Fin 4, (1 / 4 : ℝ) := Finset.sum_le_sum fun a _ => h2 a
        _ = 1 := by norm_num
    nlinarith [norm_nonneg (u - wv)]
  set Rw := intVecNorm w with hRw
  have hdiff : |R - Rw| ≤ 1 := by
    rw [← hnorm]
    exact (abs_norm_sub_norm_le u wv).trans hclose
  have hRw1 : 1 ≤ Rw := by
    have := (abs_le.1 hdiff).2
    linarith
  have hρ : R / 2 ≤ Rw := by
    have := (abs_le.1 hdiff).2
    linarith
  have hpi1 : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hinv5 : (Rw ^ 5)⁻¹ ≤ 32 * (R ^ 5)⁻¹ := by
    have h1 : (R / 2) ^ 5 ≤ Rw ^ 5 := pow_le_pow_left₀ (by positivity) hρ 5
    have h2 : (Rw ^ 5)⁻¹ ≤ ((R / 2) ^ 5)⁻¹ := inv_anti₀ (by positivity) h1
    have e : ((R / 2) ^ 5)⁻¹ = 32 * (R ^ 5)⁻¹ := by
      field_simp
      norm_num
    linarith
  have key : ∀ i j : Fin 4, |secondDiffMatrix latticeGreen w i j -
      greenHessian (fun a => u a) R i j| ≤ 32 * (C₂ + 64) * (R ^ 5)⁻¹ := by
    intro i j
    have h1 := hnear w hRw1 i j
    have h2 : |greenHessian (fun μ => (w μ : ℝ)) Rw i j - greenHessian (fun a => u a) R i j| ≤
        64 * ((R / 2) ^ 5)⁻¹ := by
      have t := greenHessian_lipschitz (fun μ => (w μ : ℝ)) (fun a => u a) (a := Rw) (b := R) (ρ := R / 2)
        (d := if i = j then 1 else 0) (by linarith) hρ (by linarith)
        (by rw [abs_sub_comm]; exact hdiff) (fun μ => abs_apply_le_intVecNorm w μ)
        (fun μ => by simpa using PiLp.norm_apply_le u μ)
        (fun μ => by
          have := abs_intBarycenter_sub_sub_le P P' μ
          rw [abs_sub_comm]
          linarith)
        (by split_ifs <;> norm_num) i j
      have e : greenHessian (fun μ => (w μ : ℝ)) Rw i j - greenHessian (fun a => u a) R i j =
          -(1 / (2 * Real.pi ^ 2)) * (1 / Rw ^ 4 * ((if i = j then 1 else 0) - 4 * (w i : ℝ) * (w j : ℝ) / Rw ^ 2) -
            1 / R ^ 4 * ((if i = j then 1 else 0) - 4 * u i * u j / R ^ 2)) := by
        simp only [greenHessian]
        have : Rw ≠ 0 := by linarith
        field_simp
        ring
      rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi ^ 2))]
      have hc : 1 / (2 * Real.pi ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have e6 : 64 * ((R / 2) ^ 5)⁻¹ = 1 * (64 * ((R / 2) ^ 5)⁻¹) := (one_mul _).symm
      rw [e6]
      exact mul_le_mul hc t (abs_nonneg _) zero_le_one
    have e3 : ((R / 2) ^ 5)⁻¹ = 32 * (R ^ 5)⁻¹ := by
      field_simp
      norm_num
    rw [e3] at h2
    have h3 := abs_sub_le (secondDiffMatrix latticeGreen w i j)
      (greenHessian (fun μ => (w μ : ℝ)) Rw i j) (greenHessian (fun a => u a) R i j)
    have h4 := mul_le_mul_of_nonneg_left hinv5 hC₂
    linarith [h1, h2, h3, h4]
  rw [planePairEntry_greenHessian u hu0]
  have := planePairEntry_sub_le key P.2 P'.2
  calc _ ≤ _ := this
    _ = 128 * (C₂ + 64) * (R ^ 5)⁻¹ := by ring
private theorem abs_inversionMatrix_le (v : EuclideanFourSpace) (hv : v ≠ 0) (a b : Fin 4) :
    |inversionMatrix v a b| ≤ 3 := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ha : |v a| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v a
  have hb : |v b| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v b
  simp only [inversionMatrix, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  have h1 : |(2 / ‖v‖ ^ 2) * (v a * v b)| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / ‖v‖ ^ 2), abs_mul]
    have h2 : |v a| * |v b| ≤ ‖v‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul ha hb (abs_nonneg _) hr.le
    calc 2 / ‖v‖ ^ 2 * (|v a| * |v b|) ≤ 2 / ‖v‖ ^ 2 * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 := by field_simp
  have h3 := abs_sub (if a = b then (1 : ℝ) else 0) ((2 / ‖v‖ ^ 2) * (v a * v b))
  have h4 : |if a = b then (1 : ℝ) else 0| ≤ 1 := by
    split_ifs <;> norm_num
  linarith
private theorem abs_exteriorSquareMap_inversionMatrix_le (v : EuclideanFourSpace) (hv : v ≠ 0)
    (p q : OrderedDirectionPair) : |exteriorSquareMap (inversionMatrix v) p q| ≤ 18 := by
  unfold exteriorSquareMap
  have h1 := abs_inversionMatrix_le v hv p.1.1 q.1.1
  have h2 := abs_inversionMatrix_le v hv p.1.2 q.1.2
  have h3 := abs_inversionMatrix_le v hv p.1.1 q.1.2
  have h4 := abs_inversionMatrix_le v hv p.1.2 q.1.1
  have t := abs_sub (inversionMatrix v p.1.1 q.1.1 * inversionMatrix v p.1.2 q.1.2)
    (inversionMatrix v p.1.1 q.1.2 * inversionMatrix v p.1.2 q.1.1)
  rw [abs_mul, abs_mul] at t
  have t1 : |inversionMatrix v p.1.1 q.1.1| * |inversionMatrix v p.1.2 q.1.2| ≤ 3 * 3 :=
    mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  have t2 : |inversionMatrix v p.1.1 q.1.2| * |inversionMatrix v p.1.2 q.1.1| ≤ 3 * 3 :=
    mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
  linarith
private theorem abs_torusCurvatureProjection_le_one {m : ℕ} [NeZero m] (p p' : OrientedPlaquette m) :
    |torusCurvatureProjection p p'| ≤ 1 := by
  unfold torusCurvatureProjection
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := Submodule.norm_starProjection_apply_le (curvatureSubspace m) (EuclideanSpace.single p' (1 : ℝ))
  rw [EuclideanSpace.norm_single] at h1 ⊢
  simpa using h1
private theorem abs_intCurvatureProjection_le_one (P P' : IntPlaquette) : |intCurvatureProjection P P'| ≤ 1 := by
  unfold intCurvatureProjection
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := Submodule.norm_starProjection_apply_le intCurvatures (lp.single 2 P' (1 : ℝ))
  rw [lp.norm_single (by norm_num)] at h1 ⊢
  simpa using h1
theorem curvatureKernelBoundsStatement_holds (h1 : torusCurvatureProjectionGreenStatement)
    (h2 : curvatureProjectionGreenStatement)
    (h3 : torusSecondDiffNearLatticeStatement)
    (hB : YangMills.Construction.FreeKernel.TorusGreenSecondDiffBound)
    (hM : YangMills.Construction.PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement) :
    curvatureKernelBoundsStatement := by
  obtain ⟨C₂, hC₂, hnear⟩ := latticeGreen_near_greenHessian h3 hB hM
  obtain ⟨C₃, h3'⟩ := h3
  set C₁ := 128 * (C₂ + 64) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hc : ∀ P P' : IntPlaquette, 2 ≤ ‖intBarycenter P - intBarycenter P'‖ →
      |intCurvatureProjection P P' - (Real.pi ^ 2 * ‖intBarycenter P - intBarycenter P'‖ ^ 4)⁻¹ *
          exteriorSquareMap (inversionMatrix (intBarycenter P - intBarycenter P')) P.2 P'.2| ≤
        C₁ * (‖intBarycenter P - intBarycenter P'‖ ^ 5)⁻¹ := fun P P' hR => by
    rw [h2 P P']
    exact planePairEntry_near_continuum C₂ hC₂ hnear P P' hR
  have hA0 : 0 ≤ 4 * |C₃| + 2 := by positivity
  refine ⟨4 * |C₃| + 2 + 18 + C₁, fun m _ => ⟨abs_torusCurvatureProjection_le_one,
    abs_intCurvatureProjection_le_one, ?_, ?_⟩⟩
  · intro p p' P P' hP hP' hu
    have hm0 : m ≠ 0 := NeZero.ne m
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm0
    have hX : |torusCurvatureProjection p p' - intCurvatureProjection P P'| ≤
        (4 * |C₃| + 2) * ((m : ℝ) ^ 4)⁻¹ := by
      by_cases hm : 2 ≤ m
      · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
        rw [h1 m hm p p' P P' hP hP', h2 P P']
        have hw : ∀ μ, |(((P.1 - P'.1) μ : ℤ) : ℝ)| ≤ (m : ℝ) / 2 := fun μ => by
          have a1 := abs_intBarycenter_sub_sub_le P P' μ
          have a2 : |(intBarycenter P - intBarycenter P') μ| ≤ (m : ℝ) / 4 := hu μ
          have a3 := abs_sub_abs_le_abs_sub (((P.1 - P'.1) μ : ℤ) : ℝ)
            ((intBarycenter P - intBarycenter P') μ)
          rw [abs_sub_comm (((P.1 - P'.1) μ : ℤ) : ℝ)] at a3
          linarith
        have hp : 0 ≤ ((m : ℝ) ^ 4)⁻¹ := by positivity
        have := planePairEntry_sub_le (D := secondDiffMatrix (fun w => (greenOnVectors m w).re) (P.1 - P'.1))
          (D' := secondDiffMatrix latticeGreen (P.1 - P'.1)) (ε := |C₃| * ((m : ℝ) ^ 4)⁻¹)
          (fun i j => (h3' m hm i j _ hw).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) hp)) P.2 P'.2
        nlinarith
      · have hm' : m = 1 := by omega
        subst hm'
        have t1 := abs_torusCurvatureProjection_le_one p p'
        have t2 := abs_intCurvatureProjection_le_one P P'
        have t3 := abs_sub (torusCurvatureProjection p p') (intCurvatureProjection P P')
        have : 0 ≤ |C₃| := abs_nonneg _
        norm_num
        linarith
    have hp4 : 0 ≤ ((m : ℝ) ^ 4)⁻¹ := by positivity
    refine ⟨hX.trans (mul_le_mul_of_nonneg_right (by linarith) hp4), fun hR => ?_⟩
    set u : EuclideanFourSpace := intBarycenter P - intBarycenter P' with hud
    set R := ‖u‖ with hRd
    have hR0 : 0 < R := by linarith
    have hu0 : u ≠ 0 := fun h => by
      have : R = 0 := by rw [hRd, h, norm_zero]
      linarith
    have hRm : R ≤ m := by
      have a1 : R ^ 2 ≤ (m : ℝ) ^ 2 := by
        rw [hRd, EuclideanSpace.norm_sq_eq]
        have a2 : ∀ a : Fin 4, ‖u a‖ ^ 2 ≤ ((m : ℝ) / 4) ^ 2 := fun a =>
          pow_le_pow_left₀ (norm_nonneg _) (hu a) 2
        calc ∑ a, ‖u a‖ ^ 2 ≤ ∑ _a : Fin 4, ((m : ℝ) / 4) ^ 2 := Finset.sum_le_sum fun a _ => a2 a
          _ = (m : ℝ) ^ 2 / 4 := by
              simp
              ring
          _ ≤ (m : ℝ) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
      exact abs_le_of_sq_le_sq' a1 (by linarith) |>.2
    have hinv : ((m : ℝ) ^ 4)⁻¹ ≤ (R ^ 4)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hR0.le hRm 4)
    have hinv5 : (R ^ 5)⁻¹ ≤ (R ^ 4)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
    have hY : 0 ≤ (R ^ 4)⁻¹ := by positivity
    have hpi1 : 1 ≤ Real.pi ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have hmain : |(Real.pi ^ 2 * R ^ 4)⁻¹ * exteriorSquareMap (inversionMatrix u) P.2 P'.2| ≤
        18 * (R ^ 4)⁻¹ := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < (Real.pi ^ 2 * R ^ 4)⁻¹)]
      have a1 : (Real.pi ^ 2 * R ^ 4)⁻¹ ≤ (R ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) (by nlinarith [pow_pos hR0 4])
      have a2 := abs_exteriorSquareMap_inversionMatrix_le u hu0 P.2 P'.2
      calc _ ≤ (R ^ 4)⁻¹ * 18 := mul_le_mul a1 a2 (abs_nonneg _) hY
        _ = 18 * (R ^ 4)⁻¹ := by ring
    have hcl := hc P P' hR
    have hl : |intCurvatureProjection P P'| ≤ 18 * (R ^ 4)⁻¹ + C₁ * (R ^ 4)⁻¹ := by
      have a1 := abs_sub_abs_le_abs_sub (intCurvatureProjection P P')
        ((Real.pi ^ 2 * R ^ 4)⁻¹ * exteriorSquareMap (inversionMatrix u) P.2 P'.2)
      have a2 := mul_le_mul_of_nonneg_left hinv5 hC₁0
      linarith
    have ht : |torusCurvatureProjection p p'| ≤
        |torusCurvatureProjection p p' - intCurvatureProjection P P'| + |intCurvatureProjection P P'| := by
      have := abs_add_le (torusCurvatureProjection p p' - intCurvatureProjection P P') (intCurvatureProjection P P')
      simpa using this
    have hX' := mul_le_mul_of_nonneg_left hinv hA0
    calc _ ≤ _ := ht
      _ ≤ (4 * |C₃| + 2) * (R ^ 4)⁻¹ + (18 * (R ^ 4)⁻¹ + C₁ * (R ^ 4)⁻¹) := by linarith
      _ = (4 * |C₃| + 2 + 18 + C₁) * (R ^ 4)⁻¹ := by ring
  · intro P P' hR
    refine (hc P P' hR).trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    have : 0 ≤ ‖intBarycenter P - intBarycenter P'‖ := norm_nonneg _
    positivity
end YangMills.Construction.MomentLaw
end
