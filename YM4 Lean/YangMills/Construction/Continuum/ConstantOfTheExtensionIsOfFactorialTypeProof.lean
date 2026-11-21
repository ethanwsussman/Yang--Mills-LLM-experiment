import YangMills.Construction.Continuum.ConstantOfTheExtensionIsOfFactorialType
import YangMills.Construction.Continuum.ThreeElementaryInequalitiesInTheCoordinateNorms
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExtensionConstants
open YangMills.Construction.DiagonalShells YangMills.Construction.Bumps YangMills.Construction.PieceSystems YangMills.Construction.ConfigSpace YangMills.Construction.PieceScales YangMills.Construction.ShellPieces
theorem sideConstant_pos : 0 < sideConstant := isSideConstant_sideConstant.1
theorem sideConstant_le_one : sideConstant ≤ 1 :=
  isSideConstant_sideConstant.2.trans (by norm_num)
theorem one_le_inv_sideConstant : 1 ≤ sideConstant⁻¹ :=
  (one_le_inv₀ sideConstant_pos).2 sideConstant_le_one
theorem one_le_normalizerBound : 1 ≤ normalizerBound := le_max_left _ _
theorem one_le_derivConst : 1 ≤ derivConst := by
  have h := one_le_inv_sideConstant
  have h1 : 2 * twiceGevreyConst * sideConstant⁻¹ ≤
      max tupleCutoffConst (2 * twiceGevreyConst * sideConstant⁻¹) := le_max_right _ _
  have h2 : (36 : ℝ) * sideConstant⁻¹ = 2 * twiceGevreyConst * sideConstant⁻¹ := by
    unfold twiceGevreyConst gevreyConst
    ring
  unfold derivConst
  linarith
theorem two_le_factorialConst : 2 ≤ factorialConst := by
  have h : 2 * Real.exp 34 * weightConst ^ 5 ≤ factorialConst := le_max_left _ _
  have h1 : (1 : ℝ) ≤ Real.exp 34 := Real.one_le_exp (by norm_num)
  have h2 : (2 : ℝ) ≤ 2 * Real.exp 34 * weightConst ^ 5 := by
    unfold weightConst
    nlinarith
  linarith
theorem whitneyConst_le_factorialConst : whitneyConst ≤ factorialConst :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem leibnizBase_le_factorialConst :
    2 ^ 7 * 36 * 5 ^ 10 * Real.exp 15 * (2 * normalizerBound ^ 4) * derivConst ^ 6 ≤
      factorialConst :=
  (le_max_right _ _).trans (le_max_right _ _)
theorem one_le_localConst (hBump : GevreyBumpBounds) : 1 ≤ localConst := by
  have he := hBump.2.2.2.2.1
  have hbd : BddAbove (Set.range fun y : Fin 4 → ℝ => ‖((cubeBump y : ℝ) : ℂ)‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := he.2.2.1 y
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [this.1], this.2⟩
  have h0 : cubeBump 0 = 1 := he.2.2.2.1 0 (fun c => by norm_num)
  have hs : (1 : ℝ) ≤ TestFunctions.uniformNorm fun y : Fin 4 → ℝ => ((cubeBump y : ℝ) : ℂ) := by
    have := le_ciSup hbd 0
    unfold TestFunctions.uniformNorm
    simpa [h0] using this
  have hm : 2 * (TestFunctions.uniformNorm fun y : Fin 4 → ℝ => ((cubeBump y : ℝ) : ℂ)) ≤
      modeConst := le_max_left _ _
  unfold localConst
  linarith
theorem two_le_extBase (hBump : GevreyBumpBounds) : 2 ≤ extBase := by
  have hl := one_le_localConst hBump
  have hf := two_le_factorialConst
  have hr := one_le_inv_sideConstant
  have hcube : (2 : ℝ) ≤ factorialConst ^ 3 := by nlinarith [mul_self_nonneg factorialConst]
  have h1 : (2 : ℝ) ≤ localConst * factorialConst ^ 3 := by nlinarith
  unfold extBase
  rw [div_eq_mul_inv]
  nlinarith
theorem natPow_self_le_exp_mul_factorial (hElem : CoordNormBounds.inequalitiesClaim) (n : ℕ) :
    (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := by
  have h := hElem.2.1 n (n : ℝ) (Nat.cast_nonneg n)
  linarith [mul_comm (Real.exp n) (n.factorial : ℝ)]
theorem natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
theorem five_mul_add_one_le_six_pow (n : ℕ) : 5 * n + 1 ≤ 6 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : 1 ≤ 6 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega
theorem exp_natCast_pow_comm (a : ℕ) (n : ℕ) : Real.exp a ^ n = Real.exp n ^ a := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_comm]
theorem sqrt_natCast_pow_two_mul (n k : ℕ) : Real.sqrt (n : ℝ) ^ (2 * k) = (n : ℝ) ^ k := by
  rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
theorem taylorConst_le (hElem : CoordNormBounds.inequalitiesClaim) {n : ℕ} (hn : 2 ≤ n) :
    taylorConst n ≤ (2 * Real.exp 34 * weightConst ^ 5) ^ n * (n.factorial : ℝ) ^ 2 := by
  set X := Real.exp n with hX
  set f : ℝ := (n.factorial : ℝ) with hf
  have hpow : ((n : ℝ) ^ n) ^ 2 ≤ (X * f) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (natPow_self_le_exp_mul_factorial hElem n) 2
  have h10 : (10 : ℝ) ^ (4 * n + 2) ≤ 10 ^ (5 * n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (n : ℝ) ≤ 2 ^ n := natCast_le_two_pow n
  have h32 : Real.exp (32 * n) = X ^ 32 := by
    rw [hX, ← Real.exp_nat_mul]
    norm_num
  have h34 : Real.exp 34 ^ n = X ^ 34 := by
    have := exp_natCast_pow_comm 34 n
    simpa using this
  have hsq : Real.sqrt (n : ℝ) ^ (4 * n + 2) = (n : ℝ) * ((n : ℝ) ^ n) ^ 2 := by
    have : 4 * n + 2 = 2 * (2 * n + 1) := by ring
    rw [this, sqrt_natCast_pow_two_mul]
    ring
  have hmain : (n : ℝ) * ((n : ℝ) ^ n) ^ 2 ≤ 2 ^ n * (X * f) ^ 2 :=
    mul_le_mul h2 hpow (by positivity) (by positivity)
  calc taylorConst n
      = X ^ 32 * ((10 : ℝ) ^ (4 * n + 2) * ((n : ℝ) * ((n : ℝ) ^ n) ^ 2)) := by
        unfold taylorConst weightConst
        rw [mul_pow, hsq, h32]
    _ ≤ X ^ 32 * ((10 : ℝ) ^ (5 * n) * (2 ^ n * (X * f) ^ 2)) := by
        gcongr
    _ = (2 * Real.exp 34 * weightConst ^ 5) ^ n * f ^ 2 := by
        have e : (2 * Real.exp 34 * (10 : ℝ) ^ 5) ^ n = 2 ^ n * X ^ 34 * 10 ^ (5 * n) := by
          rw [mul_pow, mul_pow, h34, ← pow_mul]
        unfold weightConst
        rw [e]
        ring
theorem unitBallVol_nonneg : ∀ D : ℕ, 0 ≤ unitBallVol D
  | 0 => by simp [unitBallVol]
  | D + 1 => ENNReal.toReal_nonneg
theorem unitBallVol_le_two_pow (hElem : CoordNormBounds.inequalitiesClaim) :
    ∀ D : ℕ, unitBallVol D ≤ 2 ^ D
  | 0 => by simp [unitBallVol]
  | D + 1 => by
    have hsub : {x : Fin (D + 1) → ℝ | EuclideanCoords.sqrtSumSq x ≤ 1} ⊆
        Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) := by
      intro x hx
      have hm := (hElem.1 (D + 1) (by omega) x).1
      have hi : ∀ i, |x i| ≤ 1 := fun i =>
        ((le_ciSup (f := fun ι => |x ι|) (Set.finite_range _).bddAbove i).trans hm).trans hx
      exact ⟨fun i => (abs_le.1 (hi i)).1, fun i => (abs_le.1 (hi i)).2⟩
    have hcube : MeasureTheory.volume (Set.Icc (fun _ : Fin (D + 1) => (-1 : ℝ)) (fun _ => 1)) =
        2 ^ (D + 1) := by
      rw [Real.volume_Icc_pi]
      norm_num
    have hle : lebesgueOn (D + 1) {x | EuclideanCoords.sqrtSumSq x ≤ 1} ≤ 2 ^ (D + 1) :=
      hcube ▸ MeasureTheory.measure_mono hsub
    have := ENNReal.toReal_mono (by simp) hle
    simpa [unitBallVol] using this
theorem countConst_le (hElem : CoordNormBounds.inequalitiesClaim) {n : ℕ} (hn : 2 ≤ n) :
    countConst n ≤ whitneyConst ^ n * (n.factorial : ℝ) ^ 2 := by
  set X := Real.exp n with hX
  set f : ℝ := (n.factorial : ℝ) with hf
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCv : 0 ≤ volumeCountConst := by
    unfold volumeCountConst
    positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.2 hn1
  have hball : (1 + Real.sqrt (n : ℝ)) ^ (4 * n) ≤ 16 ^ n * ((n : ℝ) ^ n) ^ 2 := by
    calc (1 + Real.sqrt (n : ℝ)) ^ (4 * n) ≤ (2 * Real.sqrt (n : ℝ)) ^ (4 * n) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 16 ^ n * ((n : ℝ) ^ n) ^ 2 := by
          have h1 : Real.sqrt (n : ℝ) ^ (4 * n) = ((n : ℝ) ^ n) ^ 2 := by
            rw [show 4 * n = 2 * (n * 2) by ring, sqrt_natCast_pow_two_mul, pow_mul]
          have h2 : (2 : ℝ) ^ (4 * n) = 16 ^ n := by
            rw [pow_mul]
            norm_num
          rw [mul_pow, h1, h2]
  have hpow : ((n : ℝ) ^ n) ^ 2 ≤ (X * f) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (natPow_self_le_exp_mul_factorial hElem n) 2
  have hn2 : (n : ℝ) ^ 2 ≤ 4 ^ n := by
    have := pow_le_pow_left₀ hnn (natCast_le_two_pow n) 2
    calc (n : ℝ) ^ 2 ≤ (2 ^ n) ^ 2 := this
      _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hv1 : unitBallVol (4 * n) ≤ 16 ^ n := by
    calc unitBallVol (4 * n) ≤ 2 ^ (4 * n) := unitBallVol_le_two_pow hElem _
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have hv2 : unitBallVol (4 * n - 4) ≤ 16 ^ n := by
    calc unitBallVol (4 * n - 4) ≤ 2 ^ (4 * n - 4) := unitBallVol_le_two_pow hElem _
      _ ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have h16 : (0 : ℝ) < 16 ^ n := by positivity
  have hpair : halfPairs n ≤ (n : ℝ) ^ 2 := by
    unfold halfPairs
    nlinarith
  have hmax : max (halfPairs n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n)) ≤
      4 ^ n * 16 ^ n := by
    refine max_le ?_ ?_
    · exact mul_le_mul (hpair.trans hn2) hv2 (unitBallVol_nonneg _) (by positivity)
    · have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
  have hmax0 : 0 ≤ max (halfPairs n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n)) :=
    (unitBallVol_nonneg _).trans (le_max_right _ _)
  have hexp2 : Real.exp 2 ^ n = X ^ 2 := by
    have := exp_natCast_pow_comm 2 n
    simpa using this
  have hbase : 1024 * Real.exp 2 * volumeCountConst ≤ whitneyConst :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))
  calc countConst n
      ≤ volumeCountConst ^ n * (16 ^ n * (X * f) ^ 2) * (4 ^ n * 16 ^ n) := by
        unfold countConst
        have h1 : (1 + Real.sqrt (n : ℝ)) ^ (4 * n) ≤ 16 ^ n * (X * f) ^ 2 :=
          hball.trans (mul_le_mul_of_nonneg_left hpow h16.le)
        gcongr
    _ = (1024 * Real.exp 2 * volumeCountConst) ^ n * f ^ 2 := by
        have h1024 : (1024 : ℝ) ^ n = 16 ^ n * 4 ^ n * 16 ^ n := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        have e : (1024 * Real.exp 2 * volumeCountConst) ^ n =
            16 ^ n * 4 ^ n * 16 ^ n * X ^ 2 * volumeCountConst ^ n := by
          rw [mul_pow, mul_pow, hexp2, h1024]
        rw [e]
        ring
    _ ≤ whitneyConst ^ n * f ^ 2 := by
        have : 0 ≤ 1024 * Real.exp 2 * volumeCountConst := by positivity
        gcongr
theorem leibnizConst_le (hElem : CoordNormBounds.inequalitiesClaim) {n : ℕ} (hn : 2 ≤ n) :
    leibnizConst n ≤
      (2 ^ 7 * 36 * 5 ^ 10 * Real.exp 15 * (2 * normalizerBound ^ 4) *
        derivConst ^ 6) ^ n * (n.factorial : ℝ) ^ 15 := by
  set X := Real.exp n with hX
  set f : ℝ := (n.factorial : ℝ) with hf
  set A := normalizerBound with hA
  set U := derivConst with hU
  have hA1 : 1 ≤ A := one_le_normalizerBound
  have hU1 : 1 ≤ U := one_le_derivConst
  have hself := natPow_self_le_exp_mul_factorial hElem n
  have hpow5 : ((n : ℝ) ^ n) ^ 5 ≤ (X * f) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hself 5
  have a1 : (2 : ℝ) ^ (5 * n + 1) ≤ 2 ^ (6 * n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have a2 : 2 * A ^ (4 * n) ≤ 2 ^ n * A ^ (4 * n) := by
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  have a3 : U ^ (5 * n + 1) ≤ U ^ (6 * n) := pow_le_pow_right₀ hU1 (by omega)
  have a4 : (n : ℝ) ^ (5 * n + 1) ≤ 2 ^ n * (X * f) ^ 5 := by
    have : (n : ℝ) ^ (5 * n + 1) = (n : ℝ) * ((n : ℝ) ^ n) ^ 5 := by
      rw [pow_succ, mul_comm 5 n, pow_mul]
      ring
    rw [this]
    exact mul_le_mul (natCast_le_two_pow n) hpow5 (by positivity) (by positivity)
  have a5 : (((5 * n + 1).factorial : ℕ) : ℝ) ≤ 6 ^ n * (5 ^ (5 * n) * (X * f) ^ 5) := by
    have h1 : (((5 * n).factorial : ℕ) : ℝ) ≤ ((5 * n : ℕ) : ℝ) ^ (5 * n) := by
      exact_mod_cast Nat.factorial_le_pow (5 * n)
    have h2 : ((5 * n : ℕ) : ℝ) ^ (5 * n) = 5 ^ (5 * n) * ((n : ℝ) ^ n) ^ 5 := by
      push_cast
      rw [mul_pow, mul_comm 5 n, pow_mul (n : ℝ) n 5]
    have h3 : (((5 * n + 1 : ℕ)) : ℝ) ≤ 6 ^ n := by
      exact_mod_cast five_mul_add_one_le_six_pow n
    rw [Nat.factorial_succ, Nat.cast_mul]
    refine mul_le_mul h3 ?_ (by positivity) (by positivity)
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hpow5 (by positivity))
  have a6 : (((5 * n + 1).factorial : ℕ) : ℝ) ^ 2 ≤
      (6 ^ n * (5 ^ (5 * n) * (X * f) ^ 5)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) a5 2
  have h15 : Real.exp 15 ^ n = X ^ 15 := by
    have := exp_natCast_pow_comm 15 n
    simpa using this
  have hsplit : (U * (n : ℝ)) ^ (5 * n + 1) ≤ U ^ (6 * n) * (2 ^ n * (X * f) ^ 5) := by
    rw [mul_pow]
    exact mul_le_mul a3 a4 (by positivity) (by positivity)
  calc leibnizConst n
      = 2 ^ (5 * n + 1) * (2 * A ^ (4 * n) * (U * (n : ℝ)) ^ (5 * n + 1) *
          (((5 * n + 1).factorial : ℕ) : ℝ) ^ 2) := leibnizConst_eq n
    _ ≤ 2 ^ (6 * n) * (2 ^ n * A ^ (4 * n) * (U ^ (6 * n) * (2 ^ n * (X * f) ^ 5)) *
          (6 ^ n * (5 ^ (5 * n) * (X * f) ^ 5)) ^ 2) := by
        gcongr
    _ = (2 ^ 7 * 36 * 5 ^ 10 * Real.exp 15 * (2 * A ^ 4) * U ^ 6) ^ n * f ^ 15 := by
        have e36 : (36 : ℝ) ^ n = (6 ^ n) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        simp only [mul_pow, h15, e36, ← pow_mul]
        rw [mul_comm 7 n, mul_comm 10 n, mul_comm 4 n, mul_comm 6 n]
        ring
theorem factorialTypeBounds_holds (hElem : CoordNormBounds.inequalitiesClaim)
    (hBump : GevreyBumpBounds) : FactorialTypeBounds := by
  have hF2 := two_le_factorialConst
  have hT : ∀ n : ℕ, 2 ≤ n →
      taylorConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 2 := by
    intro n hn
    refine (taylorConst_le hElem hn).trans ?_
    have h : 2 * Real.exp 34 * weightConst ^ 5 ≤ factorialConst := le_max_left _ _
    have h0 : 0 ≤ 2 * Real.exp 34 * weightConst ^ 5 := by
      unfold weightConst
      positivity
    gcongr
  have hC : ∀ n : ℕ, 2 ≤ n →
      countConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 2 := by
    intro n hn
    refine (countConst_le hElem hn).trans ?_
    have h0 : 0 ≤ whitneyConst := by
      have : (48 : ℝ) ≤ whitneyConst := le_max_left _ _
      linarith
    have := whitneyConst_le_factorialConst
    gcongr
  have hL : ∀ n : ℕ, 2 ≤ n →
      leibnizConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 15 := by
    intro n hn
    refine (leibnizConst_le hElem hn).trans ?_
    have h0 : 0 ≤ 2 ^ 7 * 36 * 5 ^ 10 * Real.exp 15 * (2 * normalizerBound ^ 4) *
        derivConst ^ 6 := by
      have := one_le_normalizerBound
      have := one_le_derivConst
      positivity
    have := leibnizBase_le_factorialConst
    gcongr
  refine ⟨by linarith, ?_, two_le_extBase hBump, ?_, fun n hn => ⟨hT n hn, hC n hn, hL n hn⟩⟩
  · unfold extFactor
    norm_num
  · intro n a hn
    have hB := two_le_extBase hBump
    have hlf : 0 ≤ localConst / sideConstant := by
      have := one_le_localConst hBump
      have := sideConstant_pos
      positivity
    have hTn := hT n hn
    have hCn := hC n hn
    have hLn := hL n hn
    set f : ℝ := (n.factorial : ℝ) with hf
    have hT0 : 0 ≤ taylorConst n := by
      unfold taylorConst weightConst
      positivity
    have hC0 : 0 ≤ countConst n := by
      unfold countConst
      have h1 : 0 ≤ volumeCountConst := by
        unfold volumeCountConst
        positivity
      have h2 := (unitBallVol_nonneg (4 * n)).trans
        (le_max_right (halfPairs n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n)))
      positivity
    have h2a : (2 : ℝ) ^ a ≤ extBase ^ a := pow_le_pow_left₀ (by norm_num) hB a
    have hbase : (localConst / sideConstant) * factorialConst ^ 3 = extBase := by
      unfold extBase
      ring
    calc extConst n a
        = 2 ^ (a + 2) * (localConst / sideConstant) ^ n * leibnizConst n * taylorConst n *
            countConst n := rfl
      _ ≤ 2 ^ (a + 2) * (localConst / sideConstant) ^ n *
            (factorialConst ^ n * f ^ 15) * (factorialConst ^ n * f ^ 2) *
            (factorialConst ^ n * f ^ 2) := by
          gcongr
      _ = 4 * 2 ^ a * ((localConst / sideConstant) * factorialConst ^ 3) ^ n * f ^ 19 := by
          rw [mul_pow, ← pow_mul, mul_comm 3 n, pow_mul]
          ring
      _ = 4 * 2 ^ a * extBase ^ n * f ^ 19 := by rw [hbase]
      _ ≤ 4 * extBase ^ a * extBase ^ n * f ^ 19 := by
          have : 0 ≤ extBase := by linarith
          gcongr
      _ = extFactor * extBase ^ (n + a) * f ^ 19 := by
          unfold extFactor
          rw [pow_add]
          ring
end YangMills.Construction.ExtensionConstants
