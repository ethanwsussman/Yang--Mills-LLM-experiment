import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.NormAndPairingInPauliCoordinates
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.PauliNormPairing
open ComplexMatrix2 PeriodicLattice
private theorem pauliCombination_entries (x : Fin 3 → ℂ) :
    pauliCombination x = !![x 2, x 0 - Complex.I * x 1; x 0 + Complex.I * x 1, -x 2] := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_eq_matrix <;> assumption
private theorem pauliCombination_mem_traceless (x : Fin 3 → ℂ) :
    pauliCombination x ∈ traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
private theorem halfTracePairing_pauliCombination (x y : Fin 3 → ℂ) :
    halfTracePairing (pauliCombination x) (pauliCombination y) = ∑ a, x a * y a := by apply _root_.YangMills.Construction.LieInnerProductProof.halfTracePairing_pauliCombination <;> assumption
private noncomputable def sumSqEntries (M : ComplexMatrix2) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2
private theorem norm_sub_sq_add_norm_add_sq (a b : ℂ) :
    ‖a - Complex.I * b‖ ^ 2 + ‖a + Complex.I * b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring
private theorem sumSqEntries_pauliCombination (x : Fin 3 → ℂ) :
    sumSqEntries (pauliCombination x) = 2 * ∑ a, ‖x a‖ ^ 2 := by
  have hpar := norm_sub_sq_add_norm_add_sq (x 0) (x 1)
  rw [pauliCombination_entries, sumSqEntries, Fin.sum_univ_three]
  simp
  nlinarith [hpar]
private theorem norm_toEuclideanCLM_apply_le (M : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M v‖ ≤ ‖M‖ * ‖v‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  exact ContinuousLinearMap.le_opNorm _ _
private theorem norm_toEuclideanCLM_apply_sq (M : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M v‖ ^ 2 =
      ‖M 0 0 * v 0 + M 0 1 * v 1‖ ^ 2 + ‖M 1 0 * v 0 + M 1 1 * v 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
private theorem norm_two_term_sq_le (a b u w : ℂ) :
    ‖a * u + b * w‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
  have htri : ‖a * u + b * w‖ ≤ ‖a‖ * ‖u‖ + ‖b‖ * ‖w‖ := by
    simpa using norm_add_le (a * u) (b * w)
  have hsq : ‖a * u + b * w‖ ^ 2 ≤ (‖a‖ * ‖u‖ + ‖b‖ * ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [sq_nonneg (‖a‖ * ‖w‖ - ‖b‖ * ‖u‖)]
private theorem norm_sq_le_sumSqEntries (M : ComplexMatrix2) : ‖M‖ ^ 2 ≤ sumSqEntries M := by
  have hS : 0 ≤ sumSqEntries M := by unfold sumSqEntries; positivity
  have hle : ‖M‖ ≤ Real.sqrt (sumSqEntries M) := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt hS, norm_toEuclideanCLM_apply_sq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two]
    have hrow0 := norm_two_term_sq_le (M 0 0) (M 0 1) (v 0) (v 1)
    have hrow1 := norm_two_term_sq_le (M 1 0) (M 1 1) (v 0) (v 1)
    unfold sumSqEntries
    nlinarith [hrow0, hrow1]
  calc ‖M‖ ^ 2 ≤ Real.sqrt (sumSqEntries M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = sumSqEntries M := Real.sq_sqrt hS
private theorem column_sq_le_norm_sq (M : ComplexMatrix2) (j : Fin 2) :
    ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have hle := norm_toEuclideanCLM_apply_le M (EuclideanSpace.single j 1)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [norm_toEuclideanCLM_apply_sq] at hsq
  fin_cases j <;> simpa using hsq
private theorem sumSqEntries_le_two_mul_norm_sq (M : ComplexMatrix2) :
    sumSqEntries M ≤ 2 * ‖M‖ ^ 2 := by
  have hc0 := column_sq_le_norm_sq M 0
  have hc1 := column_sq_le_norm_sq M 1
  unfold sumSqEntries
  linarith
private theorem hermitianNormFin3_nonneg' (x : Fin 3 → ℂ) : 0 ≤ hermitianNormFin3 x :=
  Real.sqrt_nonneg _
private theorem sum_norm_sq_nonneg (x : Fin 3 → ℂ) : 0 ≤ ∑ a, ‖x a‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem hermitianNormFin3_le_operatorNorm (x : Fin 3 → ℂ) :
    hermitianNormFin3 x ≤ operatorNorm (pauliCombination x) := by
  refine Real.sqrt_le_iff.mpr ⟨norm_nonneg _, ?_⟩
  have hle := sumSqEntries_le_two_mul_norm_sq (pauliCombination x)
  rw [sumSqEntries_pauliCombination] at hle
  linarith
private theorem operatorNorm_le_sqrt_two_mul (x : Fin 3 → ℂ) :
    operatorNorm (pauliCombination x) ≤ Real.sqrt 2 * hermitianNormFin3 x := by
  have hle := norm_sq_le_sumSqEntries (pauliCombination x)
  rw [sumSqEntries_pauliCombination] at hle
  rw [hermitianNormFin3, ← Real.sqrt_mul (by norm_num)]
  exact Real.le_sqrt_of_sq_le hle
private theorem norm_sum_mul_le (x y : Fin 3 → ℂ) :
    ‖∑ a, x a * y a‖ ≤ hermitianNormFin3 x * hermitianNormFin3 y := by
  calc ‖∑ a, x a * y a‖ ≤ ∑ a, ‖x a‖ * ‖y a‖ := by
        simpa using norm_sum_le Finset.univ fun a => x a * y a
    _ ≤ hermitianNormFin3 x * hermitianNormFin3 y :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖x a‖) fun a => ‖y a‖
private theorem hermitianNormFin3_mul_le (x y : Fin 3 → ℂ) :
    hermitianNormFin3 x * hermitianNormFin3 y ≤
      operatorNorm (pauliCombination x) * operatorNorm (pauliCombination y) :=
  mul_le_mul (hermitianNormFin3_le_operatorNorm x) (hermitianNormFin3_le_operatorNorm y)
    (hermitianNormFin3_nonneg' y) (norm_nonneg _)
private theorem pairingNormCoords_holds : PairingNormCoords := fun x y =>
  ⟨halfTracePairing_pauliCombination x y, hermitianNormFin3_le_operatorNorm x,
    operatorNorm_le_sqrt_two_mul x⟩
private theorem operatorNorm_le_two_mul_sSup (x : Fin 3 → ℂ) :
    operatorNorm (pauliCombination x) ≤
      2 * sSup ((fun e : ↥traceless =>
          ‖halfTracePairing (e : ComplexMatrix2) (pauliCombination x)‖) ''
        {e | operatorNorm (e : ComplexMatrix2) ≤ 1}) := by
  set S := (fun e : ↥traceless =>
      ‖halfTracePairing (e : ComplexMatrix2) (pauliCombination x)‖) ''
    {e | operatorNorm (e : ComplexMatrix2) ≤ 1} with hS
  have hbdd : BddAbove S := by
    refine ⟨operatorNorm (pauliCombination x), ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have hpair := halfTracePairing_pauliCombination (pauliCoords e) x
    rw [pauliCombination_pauliCoords] at hpair
    have hcs := norm_sum_mul_le (pauliCoords e) x
    have hmul := hermitianNormFin3_mul_le (pauliCoords e) x
    rw [pauliCombination_pauliCoords] at hmul
    have he' : ‖(e : ComplexMatrix2)‖ ≤ 1 := he
    change ‖halfTracePairing (e : ComplexMatrix2) (pauliCombination x)‖ ≤ ‖pauliCombination x‖
    rw [hpair]
    have hone : ‖(e : ComplexMatrix2)‖ * ‖pauliCombination x‖ ≤ 1 * ‖pauliCombination x‖ :=
      mul_le_mul_of_nonneg_right he' (norm_nonneg _)
    linarith
  have hnn : 0 ≤ sSup S := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨e, _, rfl⟩
    exact norm_nonneg _
  set t := hermitianNormFin3 x with ht
  by_cases h0 : t = 0
  · have hle := operatorNorm_le_sqrt_two_mul x
    rw [← ht, h0, mul_zero] at hle
    linarith
  have tpos : 0 < t := lt_of_le_of_ne (hermitianNormFin3_nonneg' x) (Ne.symm h0)
  have s2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set r : ℝ := (Real.sqrt 2 * t)⁻¹ with hr
  have rpos : 0 < r := by positivity
  set y : Fin 3 → ℂ := fun a => (r : ℂ) * (starRingEnd ℂ) (x a) with hy
  have hty : hermitianNormFin3 y = r * t := by
    have hsum : ∑ a, ‖y a‖ ^ 2 = r ^ 2 * ∑ a, ‖x a‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hy, mul_pow, abs_of_pos rpos]
    rw [hermitianNormFin3, hsum, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq rpos.le]
    rfl
  have hle : operatorNorm (pauliCombination y) ≤ 1 := by
    have hy1 := operatorNorm_le_sqrt_two_mul y
    rw [hty] at hy1
    have hone : Real.sqrt 2 * (r * t) = 1 := by
      rw [hr]
      field_simp
    linarith
  have tsq : t ^ 2 = ∑ a, ‖x a‖ ^ 2 := Real.sq_sqrt (sum_norm_sq_nonneg x)
  have hpair : halfTracePairing (pauliCombination y) (pauliCombination x) =
      ((r * t ^ 2 : ℝ) : ℂ) := by
    rw [halfTracePairing_pauliCombination, tsq]
    simp only [hy, mul_assoc, ← Finset.mul_sum, Complex.conj_mul']
    push_cast
    rfl
  have hmem : ‖halfTracePairing (pauliCombination y) (pauliCombination x)‖ ∈ S :=
    ⟨⟨pauliCombination y, pauliCombination_mem_traceless y⟩, hle, rfl⟩
  have hval : r * t ^ 2 ≤ sSup S := by
    have hc := le_csSup hbdd hmem
    rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hc
    exact hc
  have hfin : Real.sqrt 2 * t = 2 * (r * t ^ 2) := by
    rw [hr]
    field_simp
    nlinarith [s2sq]
  have hx := operatorNorm_le_sqrt_two_mul x
  rw [← ht, hfin] at hx
  linarith
private theorem pairingBounds_holds : PairingBounds :=
  ⟨fun x y => ⟨by rw [halfTracePairing_pauliCombination]; exact norm_sum_mul_le x y,
    hermitianNormFin3_mul_le x y⟩, operatorNorm_le_two_mul_sSup⟩
private theorem apply_le_opNormWrt (N : ↥traceless → ℝ) (T : ↥traceless →ₗ[ℂ] ↥traceless)
    (hnn : ∀ X, 0 ≤ N X) (hsm : ∀ (c : ℂ) X, N (c • X) = ‖c‖ * N X) (K : ℝ)
    (hK : ∀ X, N (T X) ≤ K * N X) (X : ↥traceless) :
    N (T X) ≤ opNormWrt N T * N X := by
  have hb : BddAbove ((fun X => N (T X)) '' {X | N X ≤ 1}) := by
    refine ⟨max K 0, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    have hY' : N Y ≤ 1 := hY
    calc N (T Y) ≤ K * N Y := hK Y
      _ ≤ max K 0 * N Y := mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn Y)
      _ ≤ max K 0 * 1 := mul_le_mul_of_nonneg_left hY' (le_max_right _ _)
      _ = max K 0 := mul_one _
  by_cases h : N X = 0
  · have hKX := hK X
    rw [h, mul_zero] at hKX
    rw [h, mul_zero]
    exact hKX
  have hp : 0 < N X := lt_of_le_of_ne (hnn X) (Ne.symm h)
  have hc : ‖(((N X)⁻¹ : ℝ) : ℂ)‖ = (N X)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have hunit : N ((((N X)⁻¹ : ℝ) : ℂ) • X) = 1 := by
    rw [hsm, hc]
    exact inv_mul_cancel₀ h
  have hsup : N (T ((((N X)⁻¹ : ℝ) : ℂ) • X)) ≤ opNormWrt N T :=
    le_csSup hb ⟨_, hunit.le, rfl⟩
  rw [map_smul, hsm, hc] at hsup
  calc N (T X) = (N X)⁻¹ * N (T X) * N X := by field_simp
    _ ≤ opNormWrt N T * N X := mul_le_mul_of_nonneg_right hsup hp.le
private theorem opNormWrt_le (N : ↥traceless → ℝ) (T : ↥traceless →ₗ[ℂ] ↥traceless) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ X, N (T X) ≤ C * N X) : opNormWrt N T ≤ C := by
  refine Real.sSup_le ?_ hC
  rintro _ ⟨X, hX, rfl⟩
  have hX' : N X ≤ 1 := hX
  calc N (T X) ≤ C * N X := h X
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hX' hC
    _ = C := mul_one _
private theorem opNormWrt_nonneg (N : ↥traceless → ℝ) (T : ↥traceless →ₗ[ℂ] ↥traceless)
    (hnn : ∀ X, 0 ≤ N X) : 0 ≤ opNormWrt N T := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨X, _, rfl⟩
  exact hnn _
private theorem pauliCoordNorm_le_operatorNorm (X : ↥traceless) :
    pauliCoordNorm X ≤ operatorNorm (X : ComplexMatrix2) := by
  have h := hermitianNormFin3_le_operatorNorm (pauliCoords X)
  rwa [pauliCombination_pauliCoords] at h
private theorem operatorNorm_le_sqrt_two_mul_pauliCoordNorm (X : ↥traceless) :
    operatorNorm (X : ComplexMatrix2) ≤ Real.sqrt 2 * pauliCoordNorm X := by
  have h := operatorNorm_le_sqrt_two_mul (pauliCoords X)
  rwa [pauliCombination_pauliCoords] at h
private theorem pauliCoordNorm_nonneg' (X : ↥traceless) : 0 ≤ pauliCoordNorm X :=
  hermitianNormFin3_nonneg' _
private theorem operatorNorm_coe_smul (c : ℂ) (X : ↥traceless) :
    operatorNorm ((c • X : ↥traceless) : ComplexMatrix2) = ‖c‖ * operatorNorm (X : ComplexMatrix2) := by
  rw [Submodule.coe_smul]
  exact norm_smul c (X : ComplexMatrix2)
private theorem pauliCoordNorm_smul (c : ℂ) (X : ↥traceless) :
    pauliCoordNorm (c • X) = ‖c‖ * pauliCoordNorm X := by
  have hcoord : ∀ a, pauliCoords (c • X) a = c * pauliCoords X a := by
    intro a
    simp only [pauliCoords, halfTracePairing, halfTrace, fullTrace, Submodule.coe_smul,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    ring
  have hsum : ∑ a, ‖pauliCoords (c • X) a‖ ^ 2 = ‖c‖ ^ 2 * ∑ a, ‖pauliCoords X a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcoord, norm_mul, mul_pow]
  rw [pauliCoordNorm, pauliCoordNorm, hermitianNormFin3, hermitianNormFin3, hsum,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
private theorem norm_apply_le_hermitianNormFin3 (x : Fin 3 → ℂ) (a : Fin 3) :
    ‖x a‖ ≤ hermitianNormFin3 x := by
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun a => ‖x a‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ a)
private theorem operatorNorm_apply_le_sum_mul (T : ↥traceless →ₗ[ℂ] ↥traceless) (X : ↥traceless) :
    operatorNorm ((T X : ↥traceless) : ComplexMatrix2) ≤
      (∑ a, operatorNorm ((T (pauliTraceless a) : ↥traceless) : ComplexMatrix2)) *
        pauliCoordNorm X := by
  have hX : X = ∑ a, pauliCoords X a • pauliTraceless a := by
    apply Subtype.ext
    rw [← pauliCombination_pauliCoords X]
    simp [pauliCombination, pauliTraceless]
  have hTX : ((T X : ↥traceless) : ComplexMatrix2) =
      ∑ a, pauliCoords X a • ((T (pauliTraceless a) : ↥traceless) : ComplexMatrix2) := by
    conv_lhs => rw [hX]
    simp [map_sum]
  rw [hTX, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_apply_le_hermitianNormFin3 _ a) (norm_nonneg _)
private theorem sum_operatorNorm_image_nonneg (T : ↥traceless →ₗ[ℂ] ↥traceless) :
    0 ≤ ∑ a, operatorNorm ((T (pauliTraceless a) : ↥traceless) : ComplexMatrix2) :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
private theorem operatorNorm_apply_le_linOpNorm (T : ↥traceless →ₗ[ℂ] ↥traceless) (X : ↥traceless) :
    operatorNorm ((T X : ↥traceless) : ComplexMatrix2) ≤
      linOpNorm T * operatorNorm (X : ComplexMatrix2) :=
  apply_le_opNormWrt (fun X => operatorNorm (X : ComplexMatrix2)) T (fun _ => norm_nonneg _)
    operatorNorm_coe_smul
    (∑ a, operatorNorm ((T (pauliTraceless a) : ↥traceless) : ComplexMatrix2))
    (fun X => (operatorNorm_apply_le_sum_mul T X).trans
      (mul_le_mul_of_nonneg_left (pauliCoordNorm_le_operatorNorm X)
        (sum_operatorNorm_image_nonneg T))) X
private theorem pauliCoordNorm_apply_le_linOpPauliNorm (T : ↥traceless →ₗ[ℂ] ↥traceless)
    (X : ↥traceless) : pauliCoordNorm (T X) ≤ linOpPauliNorm T * pauliCoordNorm X :=
  apply_le_opNormWrt pauliCoordNorm T pauliCoordNorm_nonneg' pauliCoordNorm_smul
    (∑ a, operatorNorm ((T (pauliTraceless a) : ↥traceless) : ComplexMatrix2))
    (fun X => (pauliCoordNorm_le_operatorNorm (T X)).trans (operatorNorm_apply_le_sum_mul T X)) X
private theorem opNormsComparable_holds : OpNormsComparable := by
  intro T
  have s2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have n1 : 0 ≤ linOpNorm T := opNormWrt_nonneg _ T fun _ => norm_nonneg _
  have n2 : 0 ≤ linOpPauliNorm T := opNormWrt_nonneg _ T pauliCoordNorm_nonneg'
  refine ⟨opNormWrt_le _ T _ (mul_nonneg s2 n1) fun X => ?_,
    opNormWrt_le _ T _ (mul_nonneg s2 n2) fun X => ?_⟩
  · calc pauliCoordNorm (T X) ≤ operatorNorm ((T X : ↥traceless) : ComplexMatrix2) :=
          pauliCoordNorm_le_operatorNorm _
      _ ≤ linOpNorm T * operatorNorm (X : ComplexMatrix2) := operatorNorm_apply_le_linOpNorm T X
      _ ≤ linOpNorm T * (Real.sqrt 2 * pauliCoordNorm X) :=
          mul_le_mul_of_nonneg_left (operatorNorm_le_sqrt_two_mul_pauliCoordNorm X) n1
      _ = Real.sqrt 2 * linOpNorm T * pauliCoordNorm X := by ring
  · calc operatorNorm ((T X : ↥traceless) : ComplexMatrix2) ≤
          Real.sqrt 2 * pauliCoordNorm (T X) :=
          operatorNorm_le_sqrt_two_mul_pauliCoordNorm _
      _ ≤ Real.sqrt 2 * (linOpPauliNorm T * pauliCoordNorm X) :=
          mul_le_mul_of_nonneg_left (pauliCoordNorm_apply_le_linOpPauliNorm T X) s2
      _ ≤ Real.sqrt 2 * (linOpPauliNorm T * operatorNorm (X : ComplexMatrix2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pauliCoordNorm_le_operatorNorm X) n2) s2
      _ = Real.sqrt 2 * linOpPauliNorm T * operatorNorm (X : ComplexMatrix2) := by ring
theorem statement_holds : Statement :=
  ⟨pairingNormCoords_holds, pairingBounds_holds, opNormsComparable_holds⟩
end YangMills.Construction.Matrices.PauliNormPairing
