import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.LawInAState.AxialFormsOnTheLattice
import YangMills.Construction.LawInAState.TheMarkOfAFunctionOfTheField
import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.LawInAState.TheAxialLogIsTheCirculation
import YangMills.Construction.ResponseInTheExpansion.MomentsOfAStepOfTheCurvatureProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.AxialLogarithm
open AxialForms LatticeSums TorusLumps LumpContours
open BlockAverages hiding unitStep
open TorusFields hiding supDist_add_siteOfInt_le
namespace TreeGaugeEstimates
private def prodUp (F : ℤ → UnitQuaternion) : ℕ → UnitQuaternion
  | 0 => 1
  | k + 1 => prodUp F k * F k
private def prodDown (F : ℤ → UnitQuaternion) : ℕ → UnitQuaternion
  | 0 => 1
  | k + 1 => prodDown F k * (F (-(k : ℤ) - 1))⁻¹
private def lineProd (F : ℤ → UnitQuaternion) : ℤ → UnitQuaternion
  | Int.ofNat k => prodUp F k
  | Int.negSucc k => prodDown F (k + 1)
private theorem lineProd_zero (F : ℤ → UnitQuaternion) : lineProd F 0 = 1 := rfl
private theorem lineProd_succ (F : ℤ → UnitQuaternion) (m : ℤ) : lineProd F (m + 1) = lineProd F m * F m := by
  cases m with
  | ofNat k => rfl
  | negSucc k =>
    cases k with
    | zero =>
      have e : (Int.negSucc 0 + 1 : ℤ) = 0 := rfl
      rw [e, lineProd_zero]
      simp only [lineProd, prodDown]
      have e2 : (-((0 : ℕ) : ℤ) - 1) = Int.negSucc 0 := rfl
      rw [e2]
      simp
    | succ k =>
      have e : (Int.negSucc (k + 1) + 1 : ℤ) = Int.negSucc k := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e]
      simp only [lineProd, prodDown]
      have e2 : (-((k + 1 : ℕ) : ℤ) - 1) = Int.negSucc (k + 1) := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e2]
      simp
private theorem lineProd_pred (F : ℤ → UnitQuaternion) (j : ℤ) :
    lineProd F (j - 1) = lineProd F j * (F (j - 1))⁻¹ := by
  have h := lineProd_succ F (j - 1)
  rw [sub_add_cancel] at h
  rw [h]
  simp
private theorem int_induction_from_zero {p : ℤ → Prop} (m : ℤ) (h0 : p 0)
    (hup : ∀ j, 0 ≤ j → j < m → p j → p (j + 1))
    (hdn : ∀ j, j ≤ 0 → m < j → p j → p (j - 1)) : p m := by
  rcases le_total 0 m with hm | hm
  · have key : ∀ k : ℕ, (k : ℤ) ≤ m → p k := by
      intro k
      induction k with
      | zero => simpa using fun _ => h0
      | succ k ih =>
        intro hk
        push_cast at hk ⊢
        exact hup k (by omega) (by omega) (ih (by omega))
    have := key m.toNat (by omega)
    rwa [Int.toNat_of_nonneg hm] at this
  · have key : ∀ k : ℕ, m ≤ -(k : ℤ) → p (-(k : ℤ)) := by
      intro k
      induction k with
      | zero => simpa using fun _ => h0
      | succ k ih =>
        intro hk
        push_cast at hk ⊢
        have := hdn (-(k : ℤ)) (by omega) (by omega) (ih (by omega))
        have e : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by ring
        rwa [e] at this
    have := key (-m).toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at this
private theorem coe_unit_mul (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
private theorem norm_unit_mul_sub_one_le (a b : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem coe_unit_inv_mul_self (a : UnitQuaternion) : ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (a : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
private theorem coe_unit_mul_inv_self (a : UnitQuaternion) : (a : ℍ[ℝ]) * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
private theorem norm_unit_inv_sub_one_eq (a : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_unit_conj_sub_one_eq (g p : UnitQuaternion) :
    ‖((g * p * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(p : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
private theorem norm_mul_sub_expUnit_add_le {g g' : UnitQuaternion} {x y : imaginaryQuaternions} {ε ε' : ℝ}
    (hg : ‖(g : ℍ[ℝ]) - (expUnit x : UnitQuaternion)‖ ≤ ε)
    (hg' : ‖(g' : ℍ[ℝ]) - (expUnit y : UnitQuaternion)‖ ≤ ε') (hx : ‖(x : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hy : ‖(y : ℍ[ℝ])‖ ≤ 1 / 4000) :
    ‖((g * g' : UnitQuaternion) : ℍ[ℝ]) - (expUnit (x + y) : UnitQuaternion)‖ ≤
      ε + ε' + 8257 * ‖(x : ℍ[ℝ])‖ * ‖(y : ℍ[ℝ])‖ := by
  have e : ((g * g' : UnitQuaternion) : ℍ[ℝ]) - (expUnit (x + y) : UnitQuaternion) =
      ((g : ℍ[ℝ]) - (expUnit x : UnitQuaternion)) * (g' : ℍ[ℝ]) +
        ((expUnit x : UnitQuaternion) : ℍ[ℝ]) * ((g' : ℍ[ℝ]) - (expUnit y : UnitQuaternion)) +
        (((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1) * (((expUnit y : UnitQuaternion) : ℍ[ℝ]) - 1) -
          (((expUnit (x + y) : UnitQuaternion) : ℍ[ℝ]) - (expUnit x : UnitQuaternion) -
            (expUnit y : UnitQuaternion) + 1) := by
    rw [coe_unit_mul]
    noncomm_ring
  have h1 : ‖((g : ℍ[ℝ]) - (expUnit x : UnitQuaternion)) * (g' : ℍ[ℝ])‖ ≤ ε := by
    rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, mul_one]
    exact hg
  have h2 : ‖((expUnit x : UnitQuaternion) : ℍ[ℝ]) * ((g' : ℍ[ℝ]) - (expUnit y : UnitQuaternion))‖ ≤ ε' := by
    rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, one_mul]
    exact hg'
  have h3 : ‖(((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1) * (((expUnit y : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      ‖(x : ℍ[ℝ])‖ * ‖(y : ℍ[ℝ])‖ := by
    rw [norm_mul]
    exact mul_le_mul (norm_exp_sub_one_le x.2) (norm_exp_sub_one_le y.2) (norm_nonneg _) (norm_nonneg _)
  have h4 := PlaquetteSecondDifference.norm_expUnit_second_diff_le hx hy
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add₃_le (a := ((g : ℍ[ℝ]) - (expUnit x : UnitQuaternion)) * (g' : ℍ[ℝ]))
    (b := ((expUnit x : UnitQuaternion) : ℍ[ℝ]) * ((g' : ℍ[ℝ]) - (expUnit y : UnitQuaternion)))
    (c := (((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1) * (((expUnit y : UnitQuaternion) : ℍ[ℝ]) - 1))
  nlinarith
private theorem norm_inv_sub_expUnit_neg {g : UnitQuaternion} {x : imaginaryQuaternions} :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (expUnit (-x) : UnitQuaternion)‖ =
      ‖(g : ℍ[ℝ]) - (expUnit x : UnitQuaternion)‖ := by
  rw [PlaquetteSecondDifference.expUnit_neg_eq_inv]
  have e : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (((expUnit x)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((expUnit x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])) *
        (((expUnit x)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [mul_sub, sub_mul, coe_unit_inv_mul_self, one_mul, mul_assoc, coe_unit_mul_inv_self, mul_one]
  rw [e, norm_mul, norm_mul, BlockAverages.norm_coe_unitQuaternion, BlockAverages.norm_coe_unitQuaternion,
    one_mul, mul_one, norm_sub_rev]
private abbrev LatticePoint : Type := Fin 4 → ℤ
private theorem trunc_shift_of_le {a : LatticePoint} {μ ν : Fin 4} (h : ν ≤ μ) (j : ℤ) :
    truncate (a + Pi.single μ 1) ν j = truncate a ν j := by apply _root_.YangMills.DeltaSharedProofs.p502521 <;> assumption
private theorem trunc_succ (a : LatticePoint) (ν : Fin 4) (j : ℤ) :
    truncate a ν j + Pi.single ν 1 = truncate a ν (j + 1) := by apply _root_.YangMills.DeltaSharedProofs.p501433 <;> assumption
private theorem trunc_self {a : LatticePoint} {ν : Fin 4} (h : ∀ l, ν < l → a l = 0) :
    truncate a ν (a ν) = a := by
  funext i
  simp only [truncate]
  by_cases hi : i < ν
  · simp [hi]
  · by_cases h2 : i = ν
    · subst h2
      simp
    · have : ν < i := lt_of_le_of_ne (not_lt.1 hi) (Ne.symm h2)
      simp [hi, h2, h i this]
private theorem trunc_eq_zero_above (a : LatticePoint) (ν : Fin 4) (j : ℤ) (l : Fin 4) (h : ν < l) :
    truncate a ν j l = 0 := by
  have h1 : ¬ l < ν := not_lt.2 h.le
  have h2 : l ≠ ν := ne_of_gt h
  simp [truncate, h1, h2]
private theorem trunc_chain (a : LatticePoint) : truncate a 1 0 = truncate a 0 (a 0) ∧
    truncate a 2 0 = truncate a 1 (a 1) ∧ truncate a 3 0 = truncate a 2 (a 2) ∧ truncate a 3 (a 3) = a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [truncate]
variable (U : LatticePoint → Fin 4 → UnitQuaternion)
private def axisProd (a : LatticePoint) (ν : Fin 4) : UnitQuaternion :=
  lineProd (fun j => U (truncate a ν j) ν) (a ν)
private def treeProd (a : LatticePoint) : UnitQuaternion :=
  axisProd U a 0 * axisProd U a 1 * axisProd U a 2 * axisProd U a 3
private def axialGaugeField (a : LatticePoint) (μ : Fin 4) : UnitQuaternion :=
  treeProd U a * U a μ * (treeProd U (a + Pi.single μ 1))⁻¹
private def plaqHolonomy (a : LatticePoint) (μ ν : Fin 4) : UnitQuaternion :=
  U a μ * U (a + Pi.single μ 1) ν * (U (a + Pi.single ν 1) μ)⁻¹ * (U a ν)⁻¹
private theorem axisProd_shift_of_lt {a : LatticePoint} {μ ν : Fin 4} (h : ν < μ) :
    axisProd U (a + Pi.single μ 1) ν = axisProd U a ν := by
  have e : (a + Pi.single μ 1 : LatticePoint) ν = a ν := by simp [ne_of_lt h]
  simp only [axisProd, e, trunc_shift_of_le h.le]
private theorem axisProd_shift_self {a : LatticePoint} {μ : Fin 4} (hz : ∀ l, μ < l → a l = 0) :
    axisProd U (a + Pi.single μ 1) μ = axisProd U a μ * U a μ := by
  have e : (a + Pi.single μ 1 : LatticePoint) μ = a μ + 1 := by simp
  simp only [axisProd, e, trunc_shift_of_le le_rfl, lineProd_succ, trunc_self hz]
private theorem axisProd_eq_one_of_lt {a : LatticePoint} {μ ν : Fin 4} (h : μ < ν) (hz : ∀ l, μ < l → a l = 0) :
    axisProd U (a + Pi.single μ 1) ν = 1 ∧ axisProd U a ν = 1 := by
  have e1 : (a + Pi.single μ 1 : LatticePoint) ν = 0 := by simp [ne_of_gt h, hz ν h]
  have e2 := hz ν h
  simp only [axisProd, e1, e2]
  exact ⟨rfl, rfl⟩
private theorem treeProd_shift {a : LatticePoint} {μ : Fin 4} (hz : ∀ l, μ < l → a l = 0) :
    treeProd U (a + Pi.single μ 1) = treeProd U a * U a μ := by
  have hμ : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by omega
  unfold treeProd
  rcases hμ with rfl | rfl | rfl | rfl
  · rw [axisProd_shift_self U hz, (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 1) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 2) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 3) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 1) hz).2,
      (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 2) hz).2,
      (axisProd_eq_one_of_lt U (by decide : (0 : Fin 4) < 3) hz).2]
    simp
  · rw [axisProd_shift_of_lt U (by decide : (0 : Fin 4) < 1), axisProd_shift_self U hz,
      (axisProd_eq_one_of_lt U (by decide : (1 : Fin 4) < 2) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (1 : Fin 4) < 3) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (1 : Fin 4) < 2) hz).2,
      (axisProd_eq_one_of_lt U (by decide : (1 : Fin 4) < 3) hz).2]
    simp [mul_assoc]
  · rw [axisProd_shift_of_lt U (by decide : (0 : Fin 4) < 2), axisProd_shift_of_lt U (by decide : (1 : Fin 4) < 2),
      axisProd_shift_self U hz, (axisProd_eq_one_of_lt U (by decide : (2 : Fin 4) < 3) hz).1,
      (axisProd_eq_one_of_lt U (by decide : (2 : Fin 4) < 3) hz).2]
    simp [mul_assoc]
  · rw [axisProd_shift_of_lt U (by decide : (0 : Fin 4) < 3), axisProd_shift_of_lt U (by decide : (1 : Fin 4) < 3),
      axisProd_shift_of_lt U (by decide : (2 : Fin 4) < 3), axisProd_shift_self U hz]
    simp [mul_assoc]
private theorem axialGaugeField_eq_one {a : LatticePoint} {μ : Fin 4} (hz : ∀ l, μ < l → a l = 0) :
    axialGaugeField U a μ = 1 := by
  unfold axialGaugeField
  rw [treeProd_shift U hz]
  simp
private theorem plaqHolonomy_axialGaugeField (a : LatticePoint) (μ ν : Fin 4) :
    axialGaugeField U a μ * axialGaugeField U (a + Pi.single μ 1) ν * (axialGaugeField U (a + Pi.single ν 1) μ)⁻¹ *
        (axialGaugeField U a ν)⁻¹ =
      treeProd U a * plaqHolonomy U a μ ν * (treeProd U a)⁻¹ := by
  unfold axialGaugeField plaqHolonomy
  rw [add_right_comm a (Pi.single μ 1) (Pi.single ν 1)]
  group
private theorem axialGaugeField_shift {a : LatticePoint} {μ ν : Fin 4} (h : μ < ν) (hz : ∀ l, ν < l → a l = 0) :
    axialGaugeField U (a + Pi.single ν 1) μ =
      (treeProd U a * plaqHolonomy U a μ ν * (treeProd U a)⁻¹)⁻¹ * axialGaugeField U a μ := by
  have h1 : axialGaugeField U a ν = 1 := axialGaugeField_eq_one U hz
  have h2 : axialGaugeField U (a + Pi.single μ 1) ν = 1 := axialGaugeField_eq_one U fun l hl => by
    have : l ≠ μ := ne_of_gt (h.trans hl)
    simp [this, hz l hl]
  have h3 := plaqHolonomy_axialGaugeField U a μ ν
  rw [h1, h2] at h3
  rw [← h3]
  group
private theorem norm_axialGaugeField_line_le {a : LatticePoint} {μ ν : Fin 4} (h : μ < ν) {t : ℝ}
    (hpl : ∀ j, |j| ≤ |a ν| → ‖((plaqHolonomy U (truncate a ν j) μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t) :
    ‖((axialGaugeField U (truncate a ν (a ν)) μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((axialGaugeField U (truncate a ν 0) μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ + |(a ν : ℝ)| * t := by
  refine int_induction_from_zero (p := fun j => ‖((axialGaugeField U (truncate a ν j) μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((axialGaugeField U (truncate a ν 0) μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ + |(j : ℝ)| * t) (a ν) (by simp) ?_ ?_
  · intro j hj hm ih
    have hb : |j| ≤ |a ν| := by
      rw [abs_of_nonneg hj, abs_of_pos (by omega)]
      omega
    have e := axialGaugeField_shift U h (a := truncate a ν j) (trunc_eq_zero_above a ν j)
    rw [trunc_succ] at e
    rw [e]
    have h1 := norm_unit_mul_sub_one_le
      (treeProd U (truncate a ν j) * plaqHolonomy U (truncate a ν j) μ ν * (treeProd U (truncate a ν j))⁻¹)⁻¹
      (axialGaugeField U (truncate a ν j) μ)
    rw [norm_unit_inv_sub_one_eq, norm_unit_conj_sub_one_eq] at h1
    have h2 := hpl j hb
    have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
    have e2 : |((j + 1 : ℤ) : ℝ)| = |(j : ℝ)| + 1 := by
      push_cast
      rw [abs_of_nonneg hj', abs_of_nonneg (by linarith)]
    rw [e2]
    linarith
  · intro j hj hm ih
    have hb : |j - 1| ≤ |a ν| := by
      rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]
      omega
    have e := axialGaugeField_shift U h (a := truncate a ν (j - 1)) (trunc_eq_zero_above a ν (j - 1))
    rw [trunc_succ, sub_add_cancel] at e
    have e3 : axialGaugeField U (truncate a ν (j - 1)) μ =
        (treeProd U (truncate a ν (j - 1)) * plaqHolonomy U (truncate a ν (j - 1)) μ ν *
          (treeProd U (truncate a ν (j - 1)))⁻¹) * axialGaugeField U (truncate a ν j) μ := by
      rw [e]
      group
    rw [e3]
    have h1 := norm_unit_mul_sub_one_le
      (treeProd U (truncate a ν (j - 1)) * plaqHolonomy U (truncate a ν (j - 1)) μ ν *
        (treeProd U (truncate a ν (j - 1)))⁻¹)
      (axialGaugeField U (truncate a ν j) μ)
    rw [norm_unit_conj_sub_one_eq] at h1
    have h2 := hpl (j - 1) hb
    have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have e2 : |((j - 1 : ℤ) : ℝ)| = |(j : ℝ)| + 1 := by
      push_cast
      rw [abs_of_nonpos hj', abs_of_nonpos (by linarith)]
      ring
    rw [e2]
    linarith
private theorem norm_axialGaugeField_sub_one_le {a : LatticePoint} {μ : Fin 4} {t d : ℝ} (ht : 0 ≤ t)
    (hd : ∀ ν, |(a ν : ℝ)| ≤ d)
    (hpl : ∀ ν, μ < ν → ∀ j, |j| ≤ |a ν| →
      ‖((plaqHolonomy U (truncate a ν j) μ ν : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t) :
    ‖((axialGaugeField U a μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * d * t := by
  obtain ⟨t0, t1, t2, t3⟩ := trunc_chain a
  have hμ : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by omega
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have one : ∀ {ν : Fin 4}, μ < ν → ∀ b : LatticePoint, (∀ l, μ < l → b l = 0) →
      ‖((axialGaugeField U b μ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0 := by
    intro ν _ b hb
    rw [axialGaugeField_eq_one U hb]
    simp
  have dt : ∀ ν, |(a ν : ℝ)| * t ≤ d * t := fun ν => mul_le_mul_of_nonneg_right (hd ν) ht
  have p : 0 ≤ d * t := by positivity
  rcases hμ with rfl | rfl | rfl | rfl
  · have l3 := norm_axialGaugeField_line_le U (by decide : (0 : Fin 4) < 3) (hpl 3 (by decide))
    have l2 := norm_axialGaugeField_line_le U (by decide : (0 : Fin 4) < 2) (hpl 2 (by decide))
    have l1 := norm_axialGaugeField_line_le U (by decide : (0 : Fin 4) < 1) (hpl 1 (by decide))
    rw [t3, t2] at l3
    rw [t1] at l2
    have z1 := one (by decide : (0 : Fin 4) < 1) (truncate a 1 0) (fun l hl => by
      have : (1 : Fin 4) ≤ l := by omega
      rcases this.lt_or_eq with h | h
      · exact trunc_eq_zero_above a 1 0 l h
      · subst h
        simp [truncate])
    rw [z1] at l1
    have := dt 1
    have := dt 2
    have := dt 3
    linarith
  · have l3 := norm_axialGaugeField_line_le U (by decide : (1 : Fin 4) < 3) (hpl 3 (by decide))
    have l2 := norm_axialGaugeField_line_le U (by decide : (1 : Fin 4) < 2) (hpl 2 (by decide))
    rw [t3, t2] at l3
    have z2 := one (by decide : (1 : Fin 4) < 2) (truncate a 2 0) (fun l hl => by
      have : (2 : Fin 4) ≤ l := by omega
      rcases this.lt_or_eq with h | h
      · exact trunc_eq_zero_above a 2 0 l h
      · subst h
        simp [truncate])
    rw [z2] at l2
    have := dt 2
    have := dt 3
    linarith
  · have l3 := norm_axialGaugeField_line_le U (by decide : (2 : Fin 4) < 3) (hpl 3 (by decide))
    rw [t3] at l3
    have z3 := one (by decide : (2 : Fin 4) < 3) (truncate a 3 0) (fun l hl => by
      have h3 : l = 3 := by omega
      subst h3
      simp [truncate])
    rw [z3] at l3
    have := dt 3
    linarith
  · have h0 : axialGaugeField U a 3 = 1 := axialGaugeField_eq_one U fun l hl => absurd hl (by omega)
    rw [h0]
    simp
    positivity
private def imagJ : imaginaryQuaternions := ⟨⟨0, 0, 1, 0⟩, rfl⟩
private def imagK : imaginaryQuaternions := ⟨⟨0, 0, 0, 1⟩, rfl⟩
private def imagBasis : Fin 3 → imaginaryQuaternions := ![FlatHessian.quaternionI, imagJ, imagK]
private theorem imagBasis_coords (e : Fin 3) : ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).re = 0 ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imI = (if e = 0 then 1 else 0) ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imJ = (if e = 1 then 1 else 0) ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imK = (if e = 2 then 1 else 0) := by
  fin_cases e <;> refine ⟨rfl, ?_, ?_, ?_⟩ <;> rfl
private theorem eq_sum_imagBasis (w : imaginaryQuaternions) : w = ∑ e, imaginaryComponent e w • imagBasis e := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have c0 := imagBasis_coords 0
  have c1 := imagBasis_coords 1
  have c2 := imagBasis_coords 2
  simp only [Fin.sum_univ_three, Submodule.coe_add, Submodule.coe_smul]
  ext
  · simp [imaginaryComponent, c0.1, c1.1, c2.1, hw]
  · simp [imaginaryComponent, c0.2.1, c1.2.1, c2.2.1]
  · simp [imaginaryComponent, c0.2.2.1, c1.2.2.1, c2.2.2.1]
  · simp [imaginaryComponent, c0.2.2.2, c1.2.2.2, c2.2.2.2]
private theorem imComp_imagBasis (e f : Fin 3) : imaginaryComponent e (imagBasis f) = if f = e then 1 else 0 := by
  fin_cases e <;> fin_cases f <;> simp [imaginaryComponent, imagBasis, FlatHessian.quaternionI, imagJ, imagK]
private def imCompHom (e : Fin 3) : imaginaryQuaternions →+ ℝ :=
  AddMonoidHom.mk' (imaginaryComponent e) (fun a b => by fin_cases e <;> simp [imaginaryComponent])
private theorem imComp_add (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a + b) = imaginaryComponent e a + imaginaryComponent e b :=
  (imCompHom e).map_add a b
private theorem imComp_neg (e : Fin 3) (a : imaginaryQuaternions) :
    imaginaryComponent e (-a) = -imaginaryComponent e a := (imCompHom e).map_neg a
private theorem imComp_smul (e : Fin 3) (τ : ℝ) (v : imaginaryQuaternions) :
    imaginaryComponent e (τ • v) = τ * imaginaryComponent e v := by
  fin_cases e <;> simp [imaginaryComponent]
private def imagLineSum (f : ℤ → imaginaryQuaternions) (m : ℤ) : imaginaryQuaternions :=
  ∑ e, AxialForms.intervalSum m (fun j => imaginaryComponent e (f j)) • imagBasis e
private theorem imComp_imagLineSum (f : ℤ → imaginaryQuaternions) (m : ℤ) (e : Fin 3) :
    imaginaryComponent e (imagLineSum f m) = AxialForms.intervalSum m (fun j => imaginaryComponent e (f j)) := by
  have h := map_sum (imCompHom e)
    (fun e' => AxialForms.intervalSum m (fun j => imaginaryComponent e' (f j)) • imagBasis e') Finset.univ
  have h2 : imCompHom e (imagLineSum f m) = imaginaryComponent e (imagLineSum f m) := rfl
  rw [← h2]
  unfold imagLineSum
  rw [h]
  have h3 : ∀ e', imCompHom e (AxialForms.intervalSum m (fun j => imaginaryComponent e' (f j)) • imagBasis e') =
      AxialForms.intervalSum m (fun j => imaginaryComponent e' (f j)) * (if e' = e then 1 else 0) := fun e' => by
    change imaginaryComponent e _ = _
    rw [imComp_smul, imComp_imagBasis]
  simp only [h3]
  simp
private theorem imagLineSum_zero (f : ℤ → imaginaryQuaternions) : imagLineSum f 0 = 0 := by
  simp [imagLineSum, AxialForms.intervalSum_zero]
private theorem imagLineSum_succ (f : ℤ → imaginaryQuaternions) (m : ℤ) :
    imagLineSum f (m + 1) = imagLineSum f m + f m := by
  conv_rhs => rw [eq_sum_imagBasis (f m)]
  simp only [imagLineSum, AxialForms.intervalSum_succ, add_smul, Finset.sum_add_distrib]
private theorem imagLineSum_pred (f : ℤ → imaginaryQuaternions) (j : ℤ) :
    imagLineSum f (j - 1) = imagLineSum f j + -f (j - 1) := by
  have h := imagLineSum_succ f (j - 1)
  rw [sub_add_cancel] at h
  rw [h]
  abel
private theorem lineProd_near_exp {F : ℤ → UnitQuaternion} {f : ℤ → imaginaryQuaternions} {m : ℤ} {s ε D : ℝ}
    (hs : 0 ≤ s) (hε : 0 ≤ ε) (hD : |(m : ℝ)| ≤ D) (hsm : (D + 1) * s ≤ 1 / 4000)
    (hf : ∀ j : ℤ, |j| ≤ |m| → ‖(f j : ℍ[ℝ])‖ ≤ s ∧ ‖(F j : ℍ[ℝ]) - (expUnit (f j) : UnitQuaternion)‖ ≤ ε) :
    ‖(lineProd F m : ℍ[ℝ]) - (expUnit (imagLineSum f m) : UnitQuaternion)‖ ≤ |(m : ℝ)| * (ε + 8257 * D * s ^ 2) ∧
      ‖(imagLineSum f m : ℍ[ℝ])‖ ≤ |(m : ℝ)| * s := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hs1 : s ≤ 1 / 4000 := by nlinarith
  have hDs : D * s ≤ 1 / 4000 := by nlinarith
  refine int_induction_from_zero (p := fun j =>
      ‖(lineProd F j : ℍ[ℝ]) - (expUnit (imagLineSum f j) : UnitQuaternion)‖ ≤ |(j : ℝ)| * (ε + 8257 * D * s ^ 2) ∧
      ‖(imagLineSum f j : ℍ[ℝ])‖ ≤ |(j : ℝ)| * s) m ?_ ?_ ?_
  · have e1 : ((expUnit (0 : imaginaryQuaternions) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      change NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 1
      simp
    simp [lineProd_zero, imagLineSum_zero, e1]
  · intro j hj hm ih
    have hb : |j| ≤ |m| := by
      rw [abs_of_nonneg hj, abs_of_pos (by omega)]
      omega
    have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
    have hjm : (j : ℝ) ≤ D := by
      have h1 : (j : ℝ) ≤ m := by exact_mod_cast hm.le
      exact h1.trans ((le_abs_self _).trans hD)
    have e2 : |((j + 1 : ℤ) : ℝ)| = (j : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by linarith)]
    obtain ⟨i1, i2⟩ := ih
    obtain ⟨f1, f2⟩ := hf j hb
    rw [abs_of_nonneg hj'] at i1 i2
    have hx : ‖(imagLineSum f j : ℍ[ℝ])‖ ≤ 1 / 4000 :=
      i2.trans ((mul_le_mul_of_nonneg_right hjm hs).trans hDs)
    have tm := norm_mul_sub_expUnit_add_le i1 f2 hx (f1.trans hs1)
    rw [lineProd_succ, imagLineSum_succ, e2]
    constructor
    · refine tm.trans ?_
      have p1 : ‖(imagLineSum f j : ℍ[ℝ])‖ * ‖(f j : ℍ[ℝ])‖ ≤ (j * s) * s :=
        mul_le_mul i2 f1 (norm_nonneg _) (by positivity)
      have p2 : (j : ℝ) * s * s ≤ D * s ^ 2 := by nlinarith [mul_nonneg hs hs]
      nlinarith
    · have : ‖((imagLineSum f j + f j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          ‖(imagLineSum f j : ℍ[ℝ])‖ + ‖(f j : ℍ[ℝ])‖ := norm_add_le _ _
      nlinarith
  · intro j hj hm ih
    have hb : |j - 1| ≤ |m| := by
      rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]
      omega
    have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have hjm : -(j : ℝ) ≤ D := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm.le
      have h2 := neg_abs_le (m : ℝ)
      linarith
    have e2 : |((j - 1 : ℤ) : ℝ)| = -(j : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
    obtain ⟨i1, i2⟩ := ih
    obtain ⟨f1, f2⟩ := hf (j - 1) hb
    rw [abs_of_nonpos hj'] at i1 i2
    have hx : ‖(imagLineSum f j : ℍ[ℝ])‖ ≤ 1 / 4000 :=
      i2.trans ((mul_le_mul_of_nonneg_right hjm hs).trans hDs)
    have f2' : ‖(((F (j - 1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (expUnit (-f (j - 1)) : UnitQuaternion)‖ ≤ ε := by
      rw [norm_inv_sub_expUnit_neg]
      exact f2
    have f1' : ‖((-f (j - 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ s := by
      rw [Submodule.coe_neg, norm_neg]
      exact f1
    have tm := norm_mul_sub_expUnit_add_le i1 f2' hx (f1'.trans hs1)
    rw [lineProd_pred, imagLineSum_pred, e2]
    constructor
    · refine tm.trans ?_
      have p1 : ‖(imagLineSum f j : ℍ[ℝ])‖ * ‖((-f (j - 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ (-(j : ℝ) * s) * s :=
        mul_le_mul i2 f1' (norm_nonneg _) (by nlinarith)
      have p2 : -(j : ℝ) * s * s ≤ D * s ^ 2 := by nlinarith [mul_nonneg hs hs]
      nlinarith
    · have : ‖((imagLineSum f j + -f (j - 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          ‖(imagLineSum f j : ℍ[ℝ])‖ + ‖((-f (j - 1) : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_add_le _ _
      nlinarith
variable (v : LatticePoint → Fin 4 → imaginaryQuaternions)
private def axisSum (a : LatticePoint) (ν : Fin 4) : imaginaryQuaternions :=
  imagLineSum (fun j => v (truncate a ν j) ν) (a ν)
private def treeLog (a : LatticePoint) : imaginaryQuaternions :=
  axisSum v a 0 + axisSum v a 1 + axisSum v a 2 + axisSum v a 3
private theorem imComp_treeLog (a : LatticePoint) (e : Fin 3) :
    imaginaryComponent e (treeLog v a) = axialPathSum (fun b μ => imaginaryComponent e (v b μ)) a := by
  simp only [treeLog, imComp_add, axisSum, imComp_imagLineSum, axialPathSum, Fin.sum_univ_four]
private theorem treeProd_near_exp {a : LatticePoint} {s ε D : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hD : ∀ ν, |(a ν : ℝ)| ≤ D) (hsm : 4 * (D + 1) * s ≤ 1 / 4000)
    (hf : ∀ ν (j : ℤ), |j| ≤ |a ν| → ‖(v (truncate a ν j) ν : ℍ[ℝ])‖ ≤ s ∧
      ‖(U (truncate a ν j) ν : ℍ[ℝ]) - (expUnit (v (truncate a ν j) ν) : UnitQuaternion)‖ ≤ ε) :
    ‖(treeProd U a : ℍ[ℝ]) - (expUnit (treeLog v a) : UnitQuaternion)‖ ≤
        4 * D * (ε + 8257 * D * s ^ 2) + 8257 * 6 * (D * s) ^ 2 ∧
      ‖(treeLog v a : ℍ[ℝ])‖ ≤ 4 * (D * s) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hDs0 : 0 ≤ D * s := by positivity
  have hsm1 : (D + 1) * s ≤ 1 / 4000 := by nlinarith
  have hA : 0 ≤ ε + 8257 * D * s ^ 2 := by positivity
  have line : ∀ ν, ‖(axisProd U a ν : ℍ[ℝ]) - (expUnit (axisSum v a ν) : UnitQuaternion)‖ ≤
      D * (ε + 8257 * D * s ^ 2) ∧ ‖(axisSum v a ν : ℍ[ℝ])‖ ≤ D * s := by
    intro ν
    obtain ⟨h1, h2⟩ := lineProd_near_exp (F := fun j => U (truncate a ν j) ν) (f := fun j => v (truncate a ν j) ν)
      hs hε (hD ν) hsm1 (hf ν)
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (hD ν) hA), h2.trans (mul_le_mul_of_nonneg_right (hD ν) hs)⟩
  obtain ⟨a0, b0⟩ := line 0
  obtain ⟨a1, b1⟩ := line 1
  obtain ⟨a2, b2⟩ := line 2
  obtain ⟨a3, b3⟩ := line 3
  have n2 : ‖((axisSum v a 0 + axisSum v a 1 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * (D * s) :=
    (norm_add_le _ _).trans (by linarith)
  have n3 : ‖((axisSum v a 0 + axisSum v a 1 + axisSum v a 2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 3 * (D * s) :=
    (norm_add_le _ _).trans (by linarith)
  have n4 : ‖((treeLog v a : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 4 * (D * s) := (norm_add_le _ _).trans (by linarith)
  refine ⟨?_, n4⟩
  have t1 := norm_mul_sub_expUnit_add_le a0 a1 (by linarith) (by linarith)
  have t2 := norm_mul_sub_expUnit_add_le t1 a2 (by linarith) (by linarith)
  have t3 := norm_mul_sub_expUnit_add_le t2 a3 (by linarith) (by linarith)
  refine t3.trans ?_
  have p1 : ‖(axisSum v a 0 : ℍ[ℝ])‖ * ‖(axisSum v a 1 : ℍ[ℝ])‖ ≤ (D * s) * (D * s) :=
    mul_le_mul b0 b1 (norm_nonneg _) hDs0
  have p2 : ‖((axisSum v a 0 + axisSum v a 1 : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖(axisSum v a 2 : ℍ[ℝ])‖ ≤
      (2 * (D * s)) * (D * s) :=
    mul_le_mul n2 b2 (norm_nonneg _) (by positivity)
  have p3 : ‖((axisSum v a 0 + axisSum v a 1 + axisSum v a 2 : imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖(axisSum v a 3 : ℍ[ℝ])‖ ≤ (3 * (D * s)) * (D * s) :=
    mul_le_mul n3 b3 (norm_nonneg _) (by positivity)
  nlinarith
private theorem axialGaugeField_near_exp {a : LatticePoint} {μ : Fin 4} {s ε D : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hD1 : 1 ≤ D) (hD : ∀ ν, |(a ν : ℝ)| ≤ D) (hD' : ∀ ν, |((a + Pi.single μ 1 : LatticePoint) ν : ℝ)| ≤ D)
    (hsm : 10 * D * s ≤ 1 / 4000)
    (hf : ∀ ν (j : ℤ), |j| ≤ |a ν| → ‖(v (truncate a ν j) ν : ℍ[ℝ])‖ ≤ s ∧
      ‖(U (truncate a ν j) ν : ℍ[ℝ]) - (expUnit (v (truncate a ν j) ν) : UnitQuaternion)‖ ≤ ε)
    (hf' : ∀ ν (j : ℤ), |j| ≤ |(a + Pi.single μ 1 : LatticePoint) ν| →
      ‖(v (truncate (a + Pi.single μ 1) ν j) ν : ℍ[ℝ])‖ ≤ s ∧
      ‖(U (truncate (a + Pi.single μ 1) ν j) ν : ℍ[ℝ]) -
        (expUnit (v (truncate (a + Pi.single μ 1) ν j) ν) : UnitQuaternion)‖ ≤ ε)
    (h0 : ‖(v a μ : ℍ[ℝ])‖ ≤ s ∧ ‖(U a μ : ℍ[ℝ]) - (expUnit (v a μ) : UnitQuaternion)‖ ≤ ε) :
    ‖(axialGaugeField U a μ : ℍ[ℝ]) -
        (expUnit (treeLog v a + v a μ + -treeLog v (a + Pi.single μ 1)) : UnitQuaternion)‖ ≤
        9 * D * ε + 400000 * D ^ 2 * s ^ 2 ∧
      ‖((treeLog v a + v a μ + -treeLog v (a + Pi.single μ 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 9 * (D * s) := by
  have hDs0 : 0 ≤ D * s := by positivity
  have hsm4 : 4 * (D + 1) * s ≤ 1 / 4000 := by nlinarith
  obtain ⟨g1, n1⟩ := treeProd_near_exp U v hs hε hD hsm4 hf
  obtain ⟨g2, n2⟩ := treeProd_near_exp U v (a := a + Pi.single μ 1) hs hε hD' hsm4 hf'
  have sD : s ≤ D * s := by nlinarith
  have nv : ‖((treeLog v a + v a μ : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 5 * (D * s) :=
    (norm_add_le _ _).trans (by linarith [h0.1])
  have nneg : ‖((-treeLog v (a + Pi.single μ 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 4 * (D * s) := by
    rw [Submodule.coe_neg, norm_neg]
    exact n2
  have g2' : ‖(((treeProd U (a + Pi.single μ 1))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      (expUnit (-treeLog v (a + Pi.single μ 1)) : UnitQuaternion)‖ ≤
      4 * D * (ε + 8257 * D * s ^ 2) + 8257 * 6 * (D * s) ^ 2 := by
    rw [norm_inv_sub_expUnit_neg]
    exact g2
  have t1 := norm_mul_sub_expUnit_add_le g1 h0.2 (by linarith) (by linarith [h0.1])
  have t2 := norm_mul_sub_expUnit_add_le t1 g2' (by linarith) (by linarith)
  have hn : ‖((treeLog v a + v a μ + -treeLog v (a + Pi.single μ 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      9 * (D * s) :=
    (norm_add_le _ _).trans (by linarith)
  refine ⟨?_, hn⟩
  unfold axialGaugeField
  refine t2.trans ?_
  have p1 : ‖(treeLog v a : ℍ[ℝ])‖ * ‖(v a μ : ℍ[ℝ])‖ ≤ (4 * (D * s)) * (D * s) :=
    mul_le_mul n1 (h0.1.trans sD) (norm_nonneg _) (by positivity)
  have p2 : ‖((treeLog v a + v a μ : imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖((-treeLog v (a + Pi.single μ 1) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ (5 * (D * s)) * (4 * (D * s)) :=
    mul_le_mul nv nneg (norm_nonneg _) (by positivity)
  have hDε : ε ≤ D * ε := by nlinarith
  nlinarith
private theorem offsetSupNorm_truncate_le' (a : LatticePoint) (ν : Fin 4) {j : ℤ} (hj : |j| ≤ |a ν|) :
    offsetSupNorm (truncate a ν j) ≤ offsetSupNorm a := by apply _root_.YangMills.Construction.CurvatureKernel.offsetSupNorm_truncate_le <;> assumption
private theorem offsetSupNorm_add_single_le' (a : LatticePoint) (μ : Fin 4) :
    offsetSupNorm (a + Pi.single μ 1) ≤ offsetSupNorm a + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
private theorem abs_imComp_le (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryComponent e w| ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.SharedProofs.p13926 <;> assumption
variable {n : ℕ} [NeZero n]
private def localField (g : TorusSite n → UnitQuaternion) (W : TorusField n) (z : TorusSite n) :
    LatticePoint → Fin 4 → UnitQuaternion :=
  fun a μ => ResponseInTheExpansion.gaugeTransform g W (z + siteOfInt a, μ)
private def localForm (v : TorusBond n → imaginaryQuaternions) (z : TorusSite n) :
    LatticePoint → Fin 4 → imaginaryQuaternions := fun a μ => v (z + siteOfInt a, μ)
private def treeGauge (g : TorusSite n → UnitQuaternion) (W : TorusField n) (z : TorusSite n) :
    TorusSite n → UnitQuaternion :=
  fun x => treeProd (localField g W z) (fun i => (x i - z i).valMinAbs) * g x
private theorem centeredCoords_eq (z : TorusSite n) {b : LatticePoint} (h : 2 * offsetSupNorm b < n) :
    (fun i => ((z + siteOfInt b : TorusSite n) i - z i).valMinAbs) = b := by
  funext i
  have e : (z + siteOfInt b : TorusSite n) i - z i = (b i : ZMod n) := by simp [siteOfInt]
  rw [e]
  exact intCast_valMinAbs_eq (by have := natAbs_le_offsetSupNorm b i; omega)
private theorem gaugeTransform_treeGauge_eq (g : TorusSite n → UnitQuaternion) (W : TorusField n) (z : TorusSite n)
    {c : LatticeBond} (h : 2 * (offsetSupNorm c.1 + 1) < n) :
    ResponseInTheExpansion.gaugeTransform (treeGauge g W z) W (bondFrom z c) = axialGaugeField (localField g W z) c.1 c.2 := by
  have h1 := centeredCoords_eq z (b := c.1) (by omega)
  have h2 := centeredCoords_eq z (b := c.1 + Pi.single c.2 1)
    (by have := offsetSupNorm_add_single_le' c.1 c.2; omega)
  have e : z + siteOfInt (c.1 + Pi.single c.2 1) = z + siteOfInt c.1 + unitStep n c.2 := by
    rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
  rw [e] at h2
  simp only [ResponseInTheExpansion.gaugeTransform, treeGauge, bondFrom, axialGaugeField, localField]
  rw [h1, h2]
  group
omit [NeZero n] in
private theorem plaqHolonomy_localField (g : TorusSite n → UnitQuaternion) (W : TorusField n) (z : TorusSite n)
    (b : LatticePoint) (μ ν : Fin 4) :
    plaqHolonomy (localField g W z) b μ ν = holonomy (gaugeTransform g W) (z + siteOfInt b) μ ν := by
  have e1 : z + siteOfInt (b + Pi.single μ 1) = z + siteOfInt b + unitStep n μ := by
    rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
  have e2 : z + siteOfInt (b + Pi.single ν 1) = z + siteOfInt b + unitStep n ν := by
    rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
  simp only [plaqHolonomy, holonomy, localField, e1, e2]
  rfl
omit [NeZero n] in
private theorem circulation_eq_imComp (v : TorusBond n → imaginaryQuaternions) (z : TorusSite n) (e : Fin 3)
    (c : LatticeBond) :
    circulation z v e c = imaginaryComponent e (treeLog (localForm v z) c.1 + localForm v z c.1 c.2 +
      -treeLog (localForm v z) (c.1 + Pi.single c.2 1)) := by
  have h := eq_pathSum_sub_add_axialForm (fun b μ => imaginaryComponent e (localForm v z b μ)) c.1 c.2
  have hc : (fun a μ ν => imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v (z + siteOfInt a, μ, ν))) =
      latticeCurl (fun b μ => imaginaryComponent e (localForm v z b μ)) := by
    funext a μ ν
    have e1 : z + siteOfInt (a + Pi.single μ 1) = z + siteOfInt a + unitStep n μ := by
      rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
    have e2 : z + siteOfInt (a + Pi.single ν 1) = z + siteOfInt a + unitStep n ν := by
      rw [siteOfInt_add_eq, siteOfInt_single, add_assoc]
    simp only [latticeCurl, localForm, ResponseInTheExpansion.lieFormCurl, e1, e2]
    have hs : ∀ x y : imaginaryQuaternions,
        imaginaryComponent e (x - y) = imaginaryComponent e x - imaginaryComponent e y :=
      fun x y => (imCompHom e).map_sub x y
    rw [hs, hs, imComp_add]
  unfold circulation
  rw [hc, imComp_add, imComp_add, imComp_neg, imComp_treeLog, imComp_treeLog]
  have hp : (c.1, c.2) = c := rfl
  rw [hp] at h
  linarith
private theorem mem_supBall_of_le (z : TorusSite n) {ρ : ℝ} {b : LatticePoint} (h : (offsetSupNorm b : ℝ) ≤ ρ) :
    z + siteOfInt b ∈ ResponseInTheExpansion.supBall z ρ := by
  simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (supDist (z + siteOfInt b) z : ℝ) ≤ offsetSupNorm b := by
    exact_mod_cast supDist_add_siteOfInt_le z b
  linarith
private theorem mem_plaquettesIn_supBall (z : TorusSite n) {ρ : ℝ} {c : LatticeBond}
    (h : (offsetSupNorm c.1 : ℝ) + 2 ≤ ρ) {ν : Fin 4} (hν : c.2 < ν) {j : ℤ} (hj : |j| ≤ |c.1 ν|) :
    ((z + siteOfInt (truncate c.1 ν j), c.2, ν) : TorusPlaquette n) ∈
      plaquettesIn (ResponseInTheExpansion.supBall z ρ) := by
  have hs := offsetSupNorm_truncate_le' c.1 ν hj
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hν, fun y hy => ?_⟩
  set x : TorusSite n := z + siteOfInt (truncate c.1 ν j) with hx
  have hd : supDist x z ≤ offsetSupNorm c.1 := (supDist_add_siteOfInt_le z _).trans hs
  have step : ∀ (a : TorusSite n) (i : Fin 4), supDist (a + unitStep n i) z ≤ supDist a z + 1 := fun a i =>
    (supDist_triangle _ a _).trans (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; have := supDist_add_unitStep_le a i; omega)
  have hy2 : supDist y z ≤ offsetSupNorm c.1 + 2 := by
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · omega
    · have := step x c.2
      omega
    · have := step x ν
      omega
    · have h1 := step x c.2
      have h2 := step (x + unitStep n c.2) ν
      omega
  simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (supDist y z : ℝ) ≤ (offsetSupNorm c.1 : ℝ) + 2 := by exact_mod_cast hy2
  linarith
private theorem abs_circulation_le {z : TorusSite n} {W : TorusField n} {g : TorusSite n → UnitQuaternion}
    {v : TorusBond n → imaginaryQuaternions} {ρ s t : ℝ}
    (hbox : IsSmallOnBall W g v z ρ s t) (ht : 0 ≤ t) {c : LatticeBond} (h : (offsetSupNorm c.1 : ℝ) + 2 ≤ ρ)
    (e : Fin 3) :
    |circulation z v e c| ≤ 4 * offsetSupNorm c.1 * t := by
  unfold circulation axialForm
  rw [abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin 4, (offsetSupNorm c.1 : ℝ) * t := Finset.sum_le_sum fun l _ => by
        split_ifs with hl
        · refine (abs_intervalSum_le _ _ t fun j hj => ?_).trans ?_
          · exact (abs_imComp_le e _).trans (hbox.curl_le _ (mem_plaquettesIn_supBall z h hl hj))
          · have := abs_le_offsetSupNorm c.1 l
            gcongr
        · simp only [abs_zero]
          positivity
    _ = _ := by
      simp
      ring
private theorem bound_at_bond {z : TorusSite n} {W : TorusField n} {g : TorusSite n → UnitQuaternion}
    {v : TorusBond n → imaginaryQuaternions} {ρ s t : ℝ} (hρn : 4 * ρ + 4 ≤ n)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hbox : IsSmallOnBall W g v z ρ s t) {c : LatticeBond}
    (hc : (offsetSupNorm c.1 : ℝ) + 2 ≤ ρ) (hKt : (10 : ℝ) ^ 8 * (1 + offsetSupNorm c.1) * t ≤ 1) :
    ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (treeGauge g W z) W (bondFrom z c)) : ℍ[ℝ])‖ ≤
        (10 : ℝ) ^ 8 * (1 + offsetSupNorm c.1) * t ∧
      ∀ e : Fin 3, |imaginaryComponent e (minimalLog (ResponseInTheExpansion.gaugeTransform (treeGauge g W z) W (bondFrom z c))) -
        circulation z v e c| ≤ (10 : ℝ) ^ 8 * (1 + offsetSupNorm c.1) ^ 2 * s ^ 2 := by
  obtain ⟨d, hd⟩ : ∃ d, d = offsetSupNorm c.1 := ⟨_, rfl⟩
  rw [← hd] at hc hKt ⊢
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = 1 + d := ⟨_, rfl⟩
  rw [← hDd] at hKt ⊢
  have hD1 : 1 ≤ D := by linarith
  have hdn : 4 * d + 12 ≤ n := by
    have : 4 * (d : ℝ) + 12 ≤ n := by linarith
    exact_mod_cast this
  have h2 : 2 * (offsetSupNorm c.1 + 1) < n := by omega
  rw [gaugeTransform_treeGauge_eq g W z h2]
  set U := localField g W z with hU
  set v' := localForm v z with hv'
  set A := axialGaugeField U c.1 c.2 with hA
  have hcoord : ∀ ν, |(c.1 ν : ℝ)| ≤ D := fun ν => by
    have h1 := abs_le_offsetSupNorm c.1 ν
    rw [← hd] at h1
    linarith
  have hnear : ‖(A : ℍ[ℝ]) - 1‖ ≤ 3 * D * t := by
    refine norm_axialGaugeField_sub_one_le U ht0 hcoord fun ν _ j hj => ?_
    rw [hU, plaqHolonomy_localField]
    change curvature (gaugeTransform g W) _ _ _ ≤ t
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
    refine hbox.curvature_le _ (mem_supBall_of_le z ?_) _ _
    have h1 : (offsetSupNorm (truncate c.1 ν j) : ℝ) ≤ offsetSupNorm c.1 := by
      exact_mod_cast offsetSupNorm_truncate_le' c.1 ν hj
    rw [← hd] at h1
    linarith
  have hlog : ‖(minimalLog A : ℍ[ℝ])‖ ≤ 6 * (D * t) := by
    have := GaugeFixing.norm_minimalLog_le A
    linarith
  have hDt0 : 0 ≤ D * t := by positivity
  refine ⟨by nlinarith, fun e => ?_⟩
  by_cases hsm : 10 * D * s ≤ 1 / 4000
  · have hs1 : s ≤ 1 / 40000 := by nlinarith
    have hε : 0 ≤ 2 * s ^ 2 := by positivity
    have hH : ∀ b : LatticePoint, (offsetSupNorm b : ℝ) ≤ d + 1 → ∀ ν, ‖(v' b ν : ℍ[ℝ])‖ ≤ s ∧
        ‖(U b ν : ℍ[ℝ]) - (expUnit (v' b ν) : UnitQuaternion)‖ ≤ 2 * s ^ 2 := by
      intro b hb ν
      obtain ⟨f1, f2⟩ := hbox.form_small (z + siteOfInt b, ν) (mem_supBall_of_le z (by linarith))
      refine ⟨f1, ?_⟩
      have hw : (U b ν : ℍ[ℝ]) = NormedSpace.exp (minimalLog (U b ν) : ℍ[ℝ]) := by
        have := GaugeFixing.expUnit_minimalLog (U b ν)
        exact (congrArg (fun q : UnitQuaternion => (q : ℍ[ℝ])) this).symm
      have hs2 : s ^ 2 ≤ s := by nlinarith
      have n1 : ‖(minimalLog (U b ν) : ℍ[ℝ])‖ ≤ 1 / 4 := by
        have h3 : ‖(minimalLog (U b ν) : ℍ[ℝ])‖ ≤ ‖(v' b ν : ℍ[ℝ])‖ +
            ‖(v' b ν : ℍ[ℝ]) - (minimalLog (U b ν) : ℍ[ℝ])‖ := by
          have := norm_sub_le (v' b ν : ℍ[ℝ]) ((v' b ν : ℍ[ℝ]) - (minimalLog (U b ν) : ℍ[ℝ]))
          simpa using this
        have f2' : ‖(v' b ν : ℍ[ℝ]) - (minimalLog (U b ν) : ℍ[ℝ])‖ ≤ s ^ 2 := f2
        have f1' : ‖(v' b ν : ℍ[ℝ])‖ ≤ s := f1
        linarith
      have n2 : ‖(v' b ν : ℍ[ℝ])‖ ≤ 1 / 4 := by
        have f1' : ‖(v' b ν : ℍ[ℝ])‖ ≤ s := f1
        linarith
      rw [hw, GaugeFixing.coe_expUnit]
      refine (GaugeFixing.norm_exp_sub_exp_le _ _ n1 n2).trans ?_
      rw [norm_sub_rev]
      have f2' : ‖(v' b ν : ℍ[ℝ]) - (minimalLog (U b ν) : ℍ[ℝ])‖ ≤ s ^ 2 := f2
      linarith
    have hsz : (offsetSupNorm (c.1 + Pi.single c.2 1) : ℝ) ≤ d + 1 := by
      have := offsetSupNorm_add_single_le' c.1 c.2
      rw [← hd] at this
      exact_mod_cast this
    have hD' : ∀ ν, |((c.1 + Pi.single c.2 1 : LatticePoint) ν : ℝ)| ≤ D := fun ν => by
      have h1 := abs_le_offsetSupNorm (c.1 + Pi.single c.2 1) ν
      linarith
    obtain ⟨tA, tN⟩ := axialGaugeField_near_exp U v' (a := c.1) (μ := c.2) hs0 hε hD1 hcoord hD' hsm
      (fun ν j hj => hH _ (by
        have h1 : (offsetSupNorm (truncate c.1 ν j) : ℝ) ≤ offsetSupNorm c.1 := by
          exact_mod_cast offsetSupNorm_truncate_le' c.1 ν hj
        rw [← hd] at h1
        linarith) ν)
      (fun ν j hj => hH _ (by
        have h1 : (offsetSupNorm (truncate (c.1 + Pi.single c.2 1) ν j) : ℝ) ≤
            offsetSupNorm (c.1 + Pi.single c.2 1) := by
          exact_mod_cast offsetSupNorm_truncate_le' _ ν hj
        linarith) ν)
      (hH _ (by
        rw [hd]
        linarith) c.2)
    obtain ⟨α, hα⟩ : ∃ α, α = treeLog v' c.1 + v' c.1 c.2 + -treeLog v' (c.1 + Pi.single c.2 1) := ⟨_, rfl⟩
    rw [← hα] at tA tN
    rw [circulation_eq_imComp, ← hv', ← hα]
    have hDs : D * s ≤ 1 / 40000 := by nlinarith
    have hA1 : ‖(A : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have : 3 * D * t ≤ 1 / 8 := by nlinarith
      linarith
    have hA2 : ‖((expUnit α : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have := norm_exp_sub_one_le α.2
      have h3 : ‖((expUnit α : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(α : ℍ[ℝ])‖ := this
      nlinarith
    have hlg := GaugeFixing.norm_minimalLog_sub_minimalLog_le A (expUnit α) hA1 hA2
    rw [GaugeFixing.minimalLog_expUnit α (by
      have := Real.pi_gt_three
      nlinarith)] at hlg
    have hsub : imaginaryComponent e (minimalLog A) - imaginaryComponent e α =
        imaginaryComponent e (minimalLog A - α) := ((imCompHom e).map_sub _ _).symm
    rw [hsub]
    refine (abs_imComp_le e _).trans ?_
    rw [Submodule.coe_sub]
    refine hlg.trans ?_
    have hDD : D ≤ D ^ 2 := by nlinarith
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hq : D * s ^ 2 ≤ D ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_right hDD hs2
    have hq0 : 0 ≤ D ^ 2 * s ^ 2 := by positivity
    nlinarith
  · have hsm' : 1 / 4000 < 10 * D * s := not_le.1 hsm
    have hDs : 1 / 40000 < D * s := by linarith
    have hc2 := abs_circulation_le hbox ht0 (c := c) (by rw [← hd]; exact hc) e
    rw [← hd] at hc2
    have hcomp := abs_imComp_le e (minimalLog A)
    have h5 : (4 : ℝ) * d * t ≤ 4 * (D * t) := by
      have : (d : ℝ) ≤ D := by linarith
      nlinarith
    have e1 : |imaginaryComponent e (minimalLog A) - circulation z v e c| ≤ 10 * (D * t) := by
      refine (abs_sub _ _).trans ?_
      linarith
    refine e1.trans ?_
    have hq : (1 / 40000 : ℝ) ^ 2 ≤ (D * s) ^ 2 := pow_le_pow_left₀ (by norm_num) hDs.le 2
    have e2 : (10 : ℝ) ^ 8 * D ^ 2 * s ^ 2 = 10 ^ 8 * (D * s) ^ 2 := by ring
    rw [e2]
    nlinarith
end TreeGaugeEstimates
theorem axialLogEqCirculationStatement_holds : axialLogEqCirculationStatement := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro n _ z W g v ρ s t _ hρn hs0 _ ht0 _ hbox
  exact ⟨TreeGaugeEstimates.treeGauge g W z, fun c hc hKt =>
    TreeGaugeEstimates.bound_at_bond hρn hs0 ht0 hbox hc hKt⟩
end YangMills.Construction.AxialLogarithm
end
