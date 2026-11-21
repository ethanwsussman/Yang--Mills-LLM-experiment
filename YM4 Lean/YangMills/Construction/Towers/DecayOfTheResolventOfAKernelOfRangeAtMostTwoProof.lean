import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.DecayOfTheResolventOfAKernelOfRangeAtMostTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2 OneLoopNotation
namespace Tower
namespace ResolventDecay
theorem euclidNormVec_zero : TorusMetric.euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (u + v) ≤
      TorusMetric.euclidNormVec u + TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem abs_exp_sub_one_le (s : ℝ) : |Real.exp s - 1| ≤ Real.exp |s| - 1 := by
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp s])]
  · have h1 : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr h
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]
    linarith [Real.add_one_le_exp s, Real.add_one_le_exp (-s)]
theorem resolventDecayRate_pos (z C : ℝ) (hz : 0 < z) (hC : 0 < C) :
    0 < resolventDecayRate z C := by
  have h : 0 < z / (4 * 12 * 5 ^ 4 * C) := by positivity
  have : 0 < Real.log (1 + z / (4 * 12 * 5 ^ 4 * C)) := Real.log_pos (by linarith)
  unfold resolventDecayRate
  linarith
theorem mul_exp_two_resolventDecayRate (z C : ℝ) (hz : 0 < z) (hC : 0 < C) :
    12 * 5 ^ 4 * C * (Real.exp (2 * resolventDecayRate z C) - 1) = z / 4 := by
  have h : 0 < z / (4 * 12 * 5 ^ 4 * C) := by positivity
  have h1 : 2 * resolventDecayRate z C = Real.log (1 + z / (4 * 12 * 5 ^ 4 * C)) := by
    unfold resolventDecayRate
    ring
  rw [h1, Real.exp_log (by linarith)]
  field_simp
  ring
theorem abs_euclidNormVec_sub_le (a b e : Fin 4 → ℝ) :
    |TorusMetric.euclidNormVec (a - e) - TorusMetric.euclidNormVec (b - e)| ≤
      TorusMetric.euclidNormVec (a - b) := by
  have h1 : TorusMetric.euclidNormVec (a - e) ≤
      TorusMetric.euclidNormVec (a - b) + TorusMetric.euclidNormVec (b - e) := by
    have := euclidNormVec_add_le (a - b) (b - e)
    rwa [sub_add_sub_cancel] at this
  have h2 : TorusMetric.euclidNormVec (b - e) ≤
      TorusMetric.euclidNormVec (a - b) + TorusMetric.euclidNormVec (a - e) := by
    have := euclidNormVec_add_le (b - a) (a - e)
    rw [sub_add_sub_cancel, ← neg_sub a b, euclidNormVec_neg] at this
    exact this
  rw [abs_le]
  constructor <;> linarith
variable {J : Type}
theorem basisVec_apply_of_ne {κ κ' : J} (h : κ' ≠ κ) : basisVec κ κ' = 0 := by
  classical
  simp [basisVec, lp.single_apply, h]
theorem exists_diagonal_multiplier {pos : J → InfiniteLattice.AmbientSpace}
    (hK : BoundedKernelOperator pos) (φ : J → ℝ) (B : ℝ)
    (hB : ∀ κ, Real.exp (φ κ) ≤ B) (hB0 : 0 ≤ B) :
    ∃ E : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2,
      ∀ (f : lp (fun _ : J => ℂ) 2) (κ : J), E f κ = (Real.exp (φ κ) : ℂ) * f κ := by
  classical
  obtain ⟨E, hE, -, -⟩ := hK B (fun κ' κ => if κ' = κ then (Real.exp (φ κ') : ℂ) else 0)
    (fun κ' κ => by
      by_cases h : κ' = κ
      · simp only [h, if_true, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact hB κ
      · simpa [h] using hB0)
    (fun κ' κ h => by
      have : κ' ≠ κ := by
        rintro rfl
        apply h
        simp [euclidNormVec_zero]
      simp [this])
  refine ⟨E, fun f κ => ?_⟩
  rw [(hE f κ).2.2, tsum_eq_single κ]
  · simp
  · intro κ' h
    simp [Ne.symm h]
theorem matrixEntry_conj_diagonal
    (E Ei S : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2) (φ : J → ℝ)
    (hE : ∀ (f : lp (fun _ : J => ℂ) 2) (κ : J), E f κ = (Real.exp (φ κ) : ℂ) * f κ)
    (hEi : ∀ (f : lp (fun _ : J => ℂ) 2) (κ : J), Ei f κ = (Real.exp (-φ κ) : ℂ) * f κ)
    (κ' κ : J) :
    matrixEntry (E * S * Ei) κ' κ = (Real.exp (φ κ' - φ κ) : ℂ) * matrixEntry S κ' κ := by
  have hunit : Ei (basisVec κ) = (Real.exp (-φ κ) : ℂ) • basisVec κ := by
    ext κ''
    rw [hEi, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : κ'' = κ
    · rw [h]
    · simp [basisVec_apply_of_ne h]
  have hexp : (Real.exp (φ κ' - φ κ) : ℂ) = (Real.exp (φ κ') : ℂ) * (Real.exp (-φ κ) : ℂ) := by
    rw [sub_eq_add_neg, Real.exp_add]
    push_cast
    rfl
  simp only [matrixEntry, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hunit,
    map_smul, hE, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hexp]
  ring
theorem resolventKernelDecays_of_parts {pos : J → InfiniteLattice.AmbientSpace}
    (hEntries : MatrixEntryProperties J) (hK : BoundedKernelOperator pos)
    (hSum : AddScalarClaim (lp (fun _ : J => ℂ) 2))
    (hNeumann : NeumannClaim (lp (fun _ : J => ℂ) 2))
    (hLog : OperatorCalculus.LogExists (lp (fun _ : J => ℂ) 2))
    (z C : ℝ) (hz : 0 < z) (hC : 0 < C) : ResolventKernelDecays pos z C := by
  intro T hT hge hCT hRange w hw ι' ι
  have hc : 0 < resolventDecayRate z C := resolventDecayRate_pos z C hz hC
  have hexp2 : 12 * 5 ^ 4 * C * (Real.exp (2 * resolventDecayRate z C) - 1) = z / 4 :=
    mul_exp_two_resolventDecayRate z C hz hC
  set c := resolventDecayRate z C with hcdef
  set m : ℝ := c * TorusMetric.euclidNormVec (pos ι' - pos ι) with hm
  have hm0 : 0 ≤ m := mul_nonneg hc.le (euclidNormVec_nonneg _)
  let φ : J → ℝ := fun κ => min (c * TorusMetric.euclidNormVec (pos κ - pos ι)) m
  have hφ0 : ∀ κ, 0 ≤ φ κ := fun κ =>
    le_min (mul_nonneg hc.le (euclidNormVec_nonneg _)) hm0
  have hφm : ∀ κ, φ κ ≤ m := fun κ => min_le_right _ _
  have hφι : φ ι = 0 := by
    have : TorusMetric.euclidNormVec (pos ι - pos ι) = 0 := by
      rw [sub_self]
      exact euclidNormVec_zero
    simp only [φ, this, mul_zero]
    exact min_eq_left hm0
  have hφι' : φ ι' = m := min_self m
  have hLip : ∀ κ' κ, |φ κ' - φ κ| ≤
      c * TorusMetric.euclidNormVec (pos κ' - pos κ) := by
    intro κ' κ
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp only [sub_self, abs_zero]
    refine max_le ?_ (mul_nonneg hc.le (euclidNormVec_nonneg _))
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    exact abs_euclidNormVec_sub_le _ _ _
  obtain ⟨E, hE⟩ := exists_diagonal_multiplier hK φ (Real.exp m)
    (fun κ => Real.exp_le_exp.mpr (hφm κ)) (Real.exp_pos _).le
  obtain ⟨Ei, hEi⟩ := exists_diagonal_multiplier hK (fun κ => -φ κ) (Real.exp m)
    (fun κ => Real.exp_le_exp.mpr (by linarith [hφ0 κ])) (Real.exp_pos _).le
  have hEEi : E * Ei = 1 := by
    ext1 f
    ext κ
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hE, hEi, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hEiE : Ei * E = 1 := by
    ext1 f
    ext κ
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hEi, hE, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hconj := matrixEntry_conj_diagonal E Ei
  set D := E * T * Ei - T with hD
  have hentryD : ∀ κ' κ, matrixEntry D κ' κ =
      ((Real.exp (φ κ' - φ κ) - 1 : ℝ) : ℂ) * matrixEntry T κ' κ := by
    intro κ' κ
    have h1 : matrixEntry D κ' κ = matrixEntry (E * T * Ei) κ' κ - matrixEntry T κ' κ := by
      simp [matrixEntry, hD]
    rw [h1, hconj T φ hE hEi]
    push_cast
    ring
  have hDbound : ∀ κ' κ, ‖matrixEntry D κ' κ‖ ≤ (Real.exp (2 * c) - 1) * C := by
    intro κ' κ
    have h2 : 0 ≤ Real.exp (2 * c) - 1 := by
      have := Real.add_one_le_exp (2 * c)
      linarith
    by_cases hd : TorusMetric.euclidNormVec (pos κ' - pos κ) ≤ 2
    · rw [hentryD, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul ?_ (hCT κ' κ) (norm_nonneg _) h2
      refine (abs_exp_sub_one_le _).trans ?_
      have : |φ κ' - φ κ| ≤ 2 * c := by
        refine (hLip κ' κ).trans ?_
        nlinarith [hc]
      linarith [Real.exp_le_exp.mpr this]
    · rw [hentryD, hRange κ' κ hd]
      simpa using mul_nonneg h2 hC.le
  have hDrange : ∀ κ' κ, ¬ TorusMetric.euclidNormVec (pos κ' - pos κ) ≤ 2 →
      matrixEntry D κ' κ = 0 := by
    intro κ' κ hd
    rw [hentryD, hRange κ' κ hd, mul_zero]
  have hDnorm : ‖D‖ ≤ z / 4 := by
    obtain ⟨D', hD', hnorm, -⟩ := hK _ (matrixEntry D) hDbound hDrange
    have hDD' : D' = D := by
      ext1 f
      ext κ
      rw [(hD' f κ).2.2, ((hEntries D).2 f κ).2]
    rw [hDD'] at hnorm
    refine hnorm.trans (le_of_eq ?_)
    rw [← hexp2]
    ring
  have hSa : IsSelfAdjointOp (addScalar T z) := (hSum T hT z 0).1
  obtain ⟨hInv, hRnorm⟩ := (hLog (addScalar T z) (z / 2) hSa (by positivity) hge).1 w hw
  set X := addScalar (addScalar T z) w with hX
  set R := inverseOp X with hR
  have hpos : 0 < z / 2 + w := by positivity
  have hq : (z / 4) * (z / 2 + w)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    linarith
  have hA : ‖-(R * D)‖ ≤ (z / 4) * (z / 2 + w)⁻¹ := by
    rw [norm_neg, mul_comm (z / 4)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hRnorm hDnorm (norm_nonneg _) (inv_nonneg.mpr hpos.le))
  obtain ⟨B, -, hB, hBnorm⟩ := hNeumann (-(R * D)) _ hA hq
  rw [sub_neg_eq_add] at hB
  have hnum : ∀ a : ℂ, E * scalarOp a * Ei = scalarOp a := by
    intro a
    have : E * scalarOp a = scalarOp a * E := by
      ext1 f
      simp [scalarOp]
    rw [this, mul_assoc, hEEi, mul_one]
  have hconjX : E * X * Ei = X + D := by
    simp only [hX, addScalar, hD, add_mul, mul_add, hnum]
    abel
  have hfactor : E * X * Ei = X * (1 + R * D) := by
    rw [hconjX, mul_add, mul_one, ← mul_assoc, hInv.1, one_mul]
  have hleft : (E * R * Ei) * (E * X * Ei) = 1 := by
    calc (E * R * Ei) * (E * X * Ei) = E * R * (Ei * E) * X * Ei := by
          simp only [mul_assoc]
      _ = E * (R * X) * Ei := by
          rw [hEiE]
          simp only [mul_assoc, mul_one]
      _ = 1 := by rw [hInv.2, mul_one, hEEi]
  have hright : (X * (1 + R * D)) * (B * R) = 1 := by
    calc (X * (1 + R * D)) * (B * R) = X * ((1 + R * D) * B) * R := by
          simp only [mul_assoc]
      _ = 1 := by rw [hB.1, mul_one, hInv.1]
  have hconjR : E * R * Ei = B * R := by
    calc E * R * Ei = (E * R * Ei) * ((X * (1 + R * D)) * (B * R)) := by rw [hright, mul_one]
      _ = ((E * R * Ei) * (E * X * Ei)) * (B * R) := by
          rw [hfactor]
          exact (mul_assoc _ _ _).symm
      _ = B * R := by rw [hleft, one_mul]
  have hnormConj : ‖E * R * Ei‖ ≤ (z / 4 + w)⁻¹ := by
    rw [hconjR]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hq' : 0 < 1 - (z / 4) * (z / 2 + w)⁻¹ := by linarith
    refine (mul_le_mul hBnorm hRnorm (norm_nonneg _) (inv_nonneg.mpr hq'.le)).trans (le_of_eq ?_)
    have : 1 - (z / 4) * (z / 2 + w)⁻¹ = (z / 4 + w) * (z / 2 + w)⁻¹ := by
      field_simp
      ring
    rw [this, mul_inv, inv_inv]
    field_simp
  have hentry := ((hEntries (E * R * Ei)).1 ι' ι).2
  rw [hconj R φ hE hEi, hφι, hφι', sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hentry
  have hfinal : Real.exp m * ‖matrixEntry R ι' ι‖ ≤ (z / 4 + w)⁻¹ := hentry.trans hnormConj
  rw [show -(c * TorusMetric.euclidNormVec (pos ι' - pos ι)) = -m from rfl,
    Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact hfinal
end ResolventDecay
open ResolventDecay in
theorem rangeTwoResolventDecay_proof
    (hSpaces : UnitLatticeL2Statement)
    (hCalculus : OperatorCalculus.Calculus.Statement) :
    RangeTwoResolventDecay := by
  intro z C hz hC
  refine ⟨resolventDecayRate_pos z C hz hC, fun L => ?_⟩
  obtain ⟨-, hL⟩ := hSpaces
  obtain ⟨-, ⟨-, -, -, -, hEs, hKs⟩, ⟨-, -, -, -, hEb, hKb⟩⟩ := hL L
  obtain ⟨hSs, -, -, hNs, -, -, hLs⟩ := hCalculus (lp (fun _ : VertexIndex L => ℂ) 2)
    (lp (fun _ : VertexIndex L => ℂ) 2)
  obtain ⟨hSb, -, -, hNb, -, -, hLb⟩ := hCalculus (lp (fun _ : EdgeIndex L => ℂ) 2)
    (lp (fun _ : EdgeIndex L => ℂ) 2)
  exact ⟨resolventKernelDecays_of_parts hEs hKs hSs hNs hLs z C hz hC,
    resolventKernelDecays_of_parts hEb hKb hSb hNb hLb z C hz hC⟩
end Tower
end YangMills.Construction
end
