import YangMills.Construction.Towers.BackgroundsCutToBondsNearAPoint
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LocalizedBackgrounds
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds (fineFieldNorm)
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.ResponseProperties (ResponseBound)
open YangMills.Construction.Tower.FullSpace.BackgroundProperties (PointProperties edgeFormOf)
theorem norm_exp_phase_le {δ r : ℝ} {q : Fin 4 → ℂ} (hq : ∀ μ, ‖q μ‖ ≤ δ)
    {v : InfiniteLattice.AmbientSpace} (hv : ∀ ν, |v ν| ≤ r) :
    ‖Complex.exp (Complex.I * bilinDot q (toComplexVec v))‖ ≤ Real.exp (4 * δ * r) := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hq 0)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * bilinDot q (toComplexVec v)).re ≤ ‖Complex.I * bilinDot q (toComplexVec v)‖ :=
    Complex.re_le_norm _
  refine hre.trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  unfold bilinDot toComplexVec
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), ‖q μ * ((v μ : ℝ) : ℂ)‖ ≤ δ * r := by
    intro μ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hq μ) (hv μ) (abs_nonneg _) hδ
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  linarith
theorem norm_ofPauliCoeffs_indicator_le {L k : ℕ} {q : Fin 4 → ℂ} {μ : Fin 4} {y : InfiniteLattice.AmbientSpace}
    {r C : ℝ} (hq : q ∈ momentumPolydisc stripHalfWidth) {P : Set (PeriodicOperators.PosEdge L k 0)}
    (hP : ∀ κ ∈ edgeFibre L k P, ∀ ν, |(remainderIndex L k).pos κ ν - y ν| ≤ r)
    (hη : 0 ≤ finestMesh L k) (hC : 0 ≤ C)
    (hα : ∀ b, Matrices.ComplexMatrix2.operatorNorm (edgeFormOf L k (responseAmplitude L k q μ) b) ≤ C)
    (b : PeriodicOperators.PosEdge L k 0) :
    ‖ofPauliCoeffs ((edgeFibre L k P).indicator
        (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)) b‖ ≤
      finestMesh L k * (Real.exp (4 * stripHalfWidth * r) * C) := by
  by_cases hb : b ∈ P
  · set w : ℂ := Complex.exp (Complex.I * bilinDot q (toComplexVec (b.1.initial - y))) with hw
    have hval : ofPauliCoeffs ((edgeFibre L k P).indicator
          (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)) b =
        (w * ((finestMesh L k : ℝ) : ℂ)) •
          edgeFormOf L k (responseAmplitude L k q μ) b := by
      unfold ofPauliCoeffs edgeFormOf ofPauliCoeffs
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hmem : ((c, b) : (remainderIndex L k).Carrier) ∈ edgeFibre L k P := hb
      have hz : (edgeFibre L k P).indicator
            (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)
            ((c, b) : (remainderIndex L k).Carrier) =
          (w * ((finestMesh L k : ℝ) : ℂ)) *
            liftQuotFn (colourEdges L k 0) (responseAmplitude L k q μ) (c, b) :=
        (Set.indicator_of_mem hmem _).trans (mul_assoc _ _ _).symm
      refine (congrArg (fun z : ℂ => z • Matrices.ComplexMatrix2.pauliFamily c) hz).trans ?_
      rw [smul_smul]
    have hphase : ‖w‖ ≤ Real.exp (4 * stripHalfWidth * r) := by
      refine norm_exp_phase_le hq fun ν => ?_
      exact hP ((0 : Fin 3), b) hb ν
    rw [hval, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη]
    calc ‖w‖ * finestMesh L k * ‖edgeFormOf L k (responseAmplitude L k q μ) b‖
        ≤ Real.exp (4 * stripHalfWidth * r) * finestMesh L k * C := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hphase hη) (hα b) (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le hη)
      _ = finestMesh L k * (Real.exp (4 * stripHalfWidth * r) * C) := by ring
  · have hval : ofPauliCoeffs ((edgeFibre L k P).indicator
          (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)) b = 0 := by
      unfold ofPauliCoeffs
      refine Finset.sum_eq_zero fun c _ => ?_
      have hmem : ((c, b) : (remainderIndex L k).Carrier) ∉ edgeFibre L k P := hb
      have hz : (edgeFibre L k P).indicator
            (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)
            ((c, b) : (remainderIndex L k).Carrier) = 0 :=
        Set.indicator_of_notMem hmem _
      exact (congrArg (fun z : ℂ => z • Matrices.ComplexMatrix2.pauliFamily c) hz).trans (zero_smul _ _)
    rw [hval, norm_zero]
    exact mul_nonneg hη (mul_nonneg (Real.exp_pos _).le hC)
theorem norm_edgeCoefficient_le_of_positive {L k : ℕ} (ζ : (remainderIndex L k).Carrier → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ b : PeriodicOperators.PosEdge L k 0, ‖ofPauliCoeffs ζ b‖ ≤ M)
    (b : Edge L k 0) : ‖(edgePauliCoordinates L k 0).ofCoeffs ζ b‖ ≤ M := by
  classical
  show ‖extendOddly (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs ζ ⟨b, h⟩ else 0) b‖ ≤ M
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb, dif_pos hb]
    exact h ⟨b, hb⟩
  · simp only [if_neg hb, norm_neg]
    by_cases hb' : b.opposite.IsPositivelyOriented
    · simp only [dif_pos hb']
      exact h ⟨b.opposite, hb'⟩
    · simp only [dif_neg hb', norm_zero]
      exact hM
theorem localizedBackgroundBound_of_backgroundProperties
    (h : BackgroundProperties.BackgroundPropertiesHold) : LocalizedBackgroundBound := by
  intro L hL k hk q hq μ y r hr P hP C hC
  have hat : PointProperties L k q μ := ((h L hL k hk).on_polydisc q hq μ μ).1
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos hL0 _
  have hbound := hat.le_bound C hC
  have hf : 0 ≤ PeriodicLattice.supOfOperatorNorms
      (BackgroundProperties.faceFunctionOf L k (responseCurvature L k q μ)) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hsup : ∀ b, Matrices.ComplexMatrix2.operatorNorm (edgeFormOf L k (responseAmplitude L k q μ) b) ≤ C := fun b =>
    (le_ciSup hat.amplitude_bddAbove b).trans (by unfold PeriodicLattice.supOfOperatorNorms at hbound hf; linarith)
  have hC0 : 0 ≤ C :=
    (norm_nonneg _).trans (hsup (Classical.arbitrary _))
  have hM : 0 ≤ finestMesh L k * (Real.exp (4 * stripHalfWidth * r) * C) :=
    mul_nonneg hη.le (mul_nonneg (Real.exp_pos _).le hC0)
  have hall := norm_edgeCoefficient_le_of_positive _ hM
    (norm_ofPauliCoeffs_indicator_le (q := q) (μ := μ) (y := y) (r := r) (C := C) hq hP hη.le hC0 hsup)
  unfold fineFieldNorm
  have hsupNorm : maxOperatorNorm ((edgePauliCoordinates L k 0).ofCoeffs ((edgeFibre L k P).indicator
        (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y))) ≤
      ENNReal.ofReal (finestMesh L k * (Real.exp (4 * stripHalfWidth * r) * C)) :=
    iSup_le fun b => ENNReal.ofReal_le_ofReal (hall b)
  calc ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm ((edgePauliCoordinates L k 0).ofCoeffs
          ((edgeFibre L k P).indicator
            (phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y)))
      ≤ ENNReal.ofReal (finestMesh L k)⁻¹ *
          ENNReal.ofReal (finestMesh L k * (Real.exp (4 * stripHalfWidth * r) * C)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (4 * stripHalfWidth * r) * C) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hη.le), inv_mul_cancel_left₀ hη.ne']
end YangMills.Construction.Tower.FullSpace.LocalizedBackgrounds
end
