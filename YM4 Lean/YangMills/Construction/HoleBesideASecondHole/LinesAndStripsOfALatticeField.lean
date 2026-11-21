import YangMills.Construction.ColdChainAtEveryLevel.ShareOfTheCriticalChainProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LatticeGauge
open YangMills.Construction.BlockAverages
def unitVec (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
def plaquetteHolonomy (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (x : Fin 4 → ℤ) (μ ν : Fin 4) :
    UnitQuaternion :=
  U x μ * U (x + unitVec μ) ν * (U (x + unitVec ν) μ)⁻¹ * (U x ν)⁻¹
def box (lo hi : Fin 4 → ℤ) : Set (Fin 4 → ℤ) := {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i}
def boxBoundary (lo hi : Fin 4 → ℤ) : Set (Fin 4 → ℤ) :=
  {x | x ∈ box lo hi ∧ ∃ i, x i = lo i ∨ x i = hi i}
def quatDist (g h : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖
theorem quatDist_self (g : UnitQuaternion) : quatDist g g = 0 := by simp [quatDist]
theorem quatDist_comm (g h : UnitQuaternion) : quatDist g h = quatDist h g := by
  simp only [quatDist]
  rw [norm_sub_rev]
theorem quatDist_triangle (g h k : UnitQuaternion) : quatDist g k ≤ quatDist g h + quatDist h k := by
  simp only [quatDist]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem quatDist_mul_left (a g h : UnitQuaternion) : quatDist (a * g) (a * h) = quatDist g h := by
  simp only [quatDist]
  have : ((a * g : UnitQuaternion) : ℍ[ℝ]) - ((a * h : UnitQuaternion) : ℍ[ℝ]) =
      (a : ℍ[ℝ]) * ((g : ℍ[ℝ]) - (h : ℍ[ℝ])) := by
    rw [mul_sub]
    rfl
  rw [this, norm_mul, norm_coe_unitQuaternion, one_mul]
theorem quatDist_mul_right (a g h : UnitQuaternion) : quatDist (g * a) (h * a) = quatDist g h := by
  simp only [quatDist]
  have : ((g * a : UnitQuaternion) : ℍ[ℝ]) - ((h * a : UnitQuaternion) : ℍ[ℝ]) =
      ((g : ℍ[ℝ]) - (h : ℍ[ℝ])) * (a : ℍ[ℝ]) := by
    rw [sub_mul]
    rfl
  rw [this, norm_mul, norm_coe_unitQuaternion, mul_one]
theorem quatDist_inv (g h : UnitQuaternion) : quatDist g⁻¹ h⁻¹ = quatDist g h := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem quatDist_mul_mul (a b c d : UnitQuaternion) :
    quatDist (a * b) (c * d) ≤ quatDist a c + quatDist b d := by apply _root_.YangMills.Construction.BlockAverages.CriticalShare.norm_coe_mul_sub_coe_mul_le <;> assumption
theorem quatDist_mul_inv_one (a b : UnitQuaternion) : quatDist (a * b⁻¹) 1 = quatDist a b := by
  have h := quatDist_mul_right b (a * b⁻¹) 1
  rw [← h]
  simp
def plaquetteDefect (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (x : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  quatDist (plaquetteHolonomy U x μ ν) 1
theorem quatDist_plaquette_halves (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (x : Fin 4 → ℤ) (μ ν : Fin 4) :
    quatDist (U x μ * U (x + unitVec μ) ν) (U x ν * U (x + unitVec ν) μ) =
      plaquetteDefect U x μ ν := by
  rw [plaquetteDefect, plaquetteHolonomy, ← quatDist_mul_inv_one]
  congr 1
  group
def lineHolonomy (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (x : Fin 4 → ℤ) (i : Fin 4) : ℕ → UnitQuaternion
  | 0 => 1
  | n + 1 => lineHolonomy U x i n * U (x + (n : ℤ) • unitVec i) i
theorem quatDist_strip_le (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (a : Fin 4 → ℤ) (i j : Fin 4) (k : ℕ) :
    quatDist (lineHolonomy U a i k * U (a + (k : ℤ) • unitVec i) j)
        (U a j * lineHolonomy U (a + unitVec j) i k) ≤
      ∑ r ∈ Finset.range k, plaquetteDefect U (a + (r : ℤ) • unitVec i) i j := by
  induction k with
  | zero => simp [lineHolonomy, quatDist_self]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    set b := a + (k : ℤ) • unitVec i with hb
    have e1 : a + ((k + 1 : ℕ) : ℤ) • unitVec i = b + unitVec i := by
      rw [hb]
      push_cast
      rw [add_smul, one_smul, add_assoc]
    have e2 : a + unitVec j + (k : ℤ) • unitVec i = b + unitVec j := by
      rw [hb]
      abel
    have h1 := quatDist_plaquette_halves U b i j
    have h2 := quatDist_mul_left (lineHolonomy U a i k) (U b i * U (b + unitVec i) j)
      (U b j * U (b + unitVec j) i)
    have h3 := quatDist_mul_right (U (b + unitVec j) i) (lineHolonomy U a i k * U b j)
      (U a j * lineHolonomy U (a + unitVec j) i k)
    have h4 := quatDist_triangle (lineHolonomy U a i k * (U b i * U (b + unitVec i) j))
      (lineHolonomy U a i k * (U b j * U (b + unitVec j) i))
      (U a j * lineHolonomy U (a + unitVec j) i k * U (b + unitVec j) i)
    have e3 : lineHolonomy U a i (k + 1) * U (a + ((k + 1 : ℕ) : ℤ) • unitVec i) j =
        lineHolonomy U a i k * (U b i * U (b + unitVec i) j) := by
      rw [e1, lineHolonomy, mul_assoc]
    have e4 : U a j * lineHolonomy U (a + unitVec j) i (k + 1) =
        U a j * lineHolonomy U (a + unitVec j) i k * U (b + unitVec j) i := by
      rw [lineHolonomy, e2, mul_assoc]
    have e5 : lineHolonomy U a i k * (U b j * U (b + unitVec j) i) =
        lineHolonomy U a i k * U b j * U (b + unitVec j) i := by
      rw [mul_assoc]
    rw [e3, e4]
    rw [e5] at h2 h4
    linarith [h1, h2, h3, h4, ih]
def gaugeDefect (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (γ : (Fin 4 → ℤ) → UnitQuaternion) (x : Fin 4 → ℤ)
    (j : Fin 4) : ℝ :=
  quatDist (γ x * U x j) (γ (x + unitVec j))
def transportedGauge (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (γ : (Fin 4 → ℤ) → UnitQuaternion) (i : Fin 4)
    (c : ℤ) (x : Fin 4 → ℤ) : UnitQuaternion :=
  γ (Function.update x i c) * lineHolonomy U (Function.update x i c) i (x i - c).toNat
theorem update_add_unitVec_self (x : Fin 4 → ℤ) (i : Fin 4) (c : ℤ) :
    Function.update (x + unitVec i) i c = Function.update x i c := by
  funext l
  by_cases h : l = i
  · subst h
    simp
  · simp [Function.update_of_ne h, unitVec, Pi.single_apply, h]
theorem update_add_unitVec_of_ne (x : Fin 4 → ℤ) {i j : Fin 4} (hj : j ≠ i) (c : ℤ) :
    Function.update (x + unitVec j) i c = Function.update x i c + unitVec j := by
  funext l
  by_cases h : l = i
  · subst h
    simp [unitVec, Pi.single_apply, hj.symm]
  · simp [Function.update_of_ne h, unitVec]
theorem update_add_smul_unitVec (x : Fin 4 → ℤ) (i : Fin 4) (c : ℤ) (hx : c ≤ x i) :
    Function.update x i c + ((x i - c).toNat : ℤ) • unitVec i = x := by
  funext l
  by_cases h : l = i
  · subst h
    simp [unitVec]
    omega
  · simp [Function.update_of_ne h, unitVec, Pi.single_apply, h]
theorem gaugeDefect_transportedGauge_along (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion)
    (γ : (Fin 4 → ℤ) → UnitQuaternion) (i : Fin 4) (c : ℤ) (x : Fin 4 → ℤ) (hx : c ≤ x i) :
    gaugeDefect U (transportedGauge U γ i c) x i = 0 := by
  have hk : ((x + unitVec i) i - c).toNat = (x i - c).toNat + 1 := by
    simp [unitVec]
    omega
  have hl := update_add_smul_unitVec x i c hx
  rw [gaugeDefect, transportedGauge, transportedGauge, update_add_unitVec_self, hk, lineHolonomy, hl, mul_assoc,
    quatDist_self]
theorem gaugeDefect_transportedGauge_side (U : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion)
    (γ : (Fin 4 → ℤ) → UnitQuaternion) {i j : Fin 4} (hj : j ≠ i) (c : ℤ) (x : Fin 4 → ℤ) (hx : c ≤ x i) :
    gaugeDefect U (transportedGauge U γ i c) x j ≤ gaugeDefect U γ (Function.update x i c) j +
      ∑ r ∈ Finset.range (x i - c).toNat,
        plaquetteDefect U (Function.update x i c + (r : ℤ) • unitVec i) i j := by
  set a := Function.update x i c with ha
  set k := (x i - c).toNat with hk
  have hl : a + (k : ℤ) • unitVec i = x := update_add_smul_unitVec x i c hx
  have hk' : ((x + unitVec j) i - c).toNat = k := by
    have : (x + unitVec j) i = x i := by simp [unitVec, Pi.single_apply, hj.symm]
    rw [this]
  have hs := quatDist_strip_le U a i j k
  rw [hl] at hs
  rw [gaugeDefect, transportedGauge, transportedGauge, update_add_unitVec_of_ne x hj, hk', ← ha]
  have h1 := quatDist_mul_left (γ a) (lineHolonomy U a i k * U x j) (U a j * lineHolonomy U (a + unitVec j) i k)
  have h2 := quatDist_mul_right (lineHolonomy U (a + unitVec j) i k) (γ a * U a j) (γ (a + unitVec j))
  have h3 := quatDist_triangle (γ a * (lineHolonomy U a i k * U x j))
    (γ a * (U a j * lineHolonomy U (a + unitVec j) i k))
    (γ (a + unitVec j) * lineHolonomy U (a + unitVec j) i k)
  have e1 : γ a * lineHolonomy U a i k * U x j = γ a * (lineHolonomy U a i k * U x j) := by rw [mul_assoc]
  have e2 : γ a * (U a j * lineHolonomy U (a + unitVec j) i k) =
      γ a * U a j * lineHolonomy U (a + unitVec j) i k := by rw [mul_assoc]
  rw [e1]
  rw [e2] at h1 h3
  rw [gaugeDefect]
  linarith
theorem quatDist_walk_le (f : (Fin 4 → ℤ) → UnitQuaternion) (a : Fin 4 → ℤ) (j : Fin 4) (d : ℝ) (n : ℕ)
    (H : ∀ r < n, quatDist (f (a + (r : ℤ) • unitVec j)) (f (a + ((r + 1 : ℕ) : ℤ) • unitVec j)) ≤ d) :
    quatDist (f a) (f (a + (n : ℤ) • unitVec j)) ≤ n * d := by
  induction n with
  | zero => simp [quatDist_self]
  | succ n ih =>
    have h1 := ih fun r hr => H r (by omega)
    have h2 := H n (by omega)
    have h3 := quatDist_triangle (f a) (f (a + (n : ℤ) • unitVec j))
      (f (a + ((n + 1 : ℕ) : ℤ) • unitVec j))
    push_cast at h3 h2 ⊢
    linarith
end YangMills.Construction.LatticeGauge
end
