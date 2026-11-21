import YangMills.Construction.Torus.StandardPartitionsLayersBlocksAndBallsProof
import YangMills.Construction.Weighted.BlockBumpFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.BlockBumps
open TorusMetric
def symWindow (r : ℕ) : Finset ℤ := Finset.Icc (-(r : ℤ)) r
theorem mem_symWindow {r : ℕ} {m : ℤ} : m ∈ symWindow r ↔ -(r : ℤ) ≤ m ∧ m ≤ r := Finset.mem_Icc
theorem sum_symWindow_eq_sum_range (r : ℕ) (h : ℤ → ℝ) :
    ∑ m ∈ symWindow r, h m = ∑ j ∈ Finset.range (2 * r + 1), h ((j : ℤ) - r) := by
  refine Finset.sum_nbij' (fun m => (m + r).toNat) (fun j => (j : ℤ) - r) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have := mem_symWindow.1 hm
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact mem_symWindow.2 (by omega)
  · intro m hm
    have := mem_symWindow.1 hm
    omega
  · intro j _
    omega
  · intro m hm
    have := mem_symWindow.1 hm
    have h' : (((m + r).toNat : ℤ) - r) = m := by omega
    simp only [h']
structure IsBumpProfile (r : ℕ) (f : ℤ → ℝ) : Prop where
  eq_zero_of_not_mem : ∀ m, m ∉ symWindow r → f m = 0
  nonneg : ∀ m, 0 ≤ f m
  le_two : ∀ m, f m ≤ 2
  sum_eq : ∑ m ∈ symWindow r, f m = 2 * r + 1
  abs_secondDiff_le : ∀ m, |f (m + 1) + f (m - 1) - 2 * f m| ≤ 4 * Real.pi ^ 2 / (2 * r + 1) ^ 2
theorem isBumpProfile_delta : IsBumpProfile 0 (fun m => if m = 0 then 1 else 0) where
  eq_zero_of_not_mem := by
    intro m hm
    have : m ≠ 0 := fun h => hm (mem_symWindow.2 (by simp [h]))
    simp [this]
  nonneg := by
    intro m
    split_ifs <;> norm_num
  le_two := by
    intro m
    split_ifs <;> norm_num
  sum_eq := by
    rw [sum_symWindow_eq_sum_range]
    simp
  abs_secondDiff_le := by
    intro m
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h : (2 : ℝ) ≤ 4 * Real.pi ^ 2 / (2 * ((0 : ℕ) : ℝ) + 1) ^ 2 := by
      norm_num
      nlinarith
    refine le_trans ?_ h
    split_ifs <;> norm_num
def cosBump (r : ℕ) (m : ℤ) : ℝ :=
  if m ∈ symWindow r then 1 + Real.cos ((m : ℝ) * (2 * Real.pi / (2 * r + 1))) else 0
theorem cosBump_neg (r : ℕ) (m : ℤ) : cosBump r (-m) = cosBump r m := by
  have h : -m ∈ symWindow r ↔ m ∈ symWindow r := by
    rw [mem_symWindow, mem_symWindow]
    omega
  unfold cosBump
  simp only [h, Int.cast_neg, neg_mul, Real.cos_neg]
theorem isBumpProfile_cosBump {r : ℕ} (hr : 1 ≤ r) : IsBumpProfile r (cosBump r) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 2 * Real.pi / (2 * r + 1) := ⟨_, rfl⟩
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hrθ : (r : ℝ) * θ + θ / 2 = Real.pi := by
    rw [hθ]
    field_simp
  have hθsq : θ ^ 2 = 4 * Real.pi ^ 2 / (2 * r + 1) ^ 2 := by
    rw [hθ, div_pow]
    ring
  have hhalf : θ / 2 ≤ Real.pi / 2 := by nlinarith
  have hκ0 : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hhalf
  have hκ1 := Real.cos_le_one (θ / 2)
  have hs : Real.sin (θ / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hin : ∀ m ∈ symWindow r, cosBump r m = 1 + Real.cos ((m : ℝ) * θ) := by
    intro m hm
    rw [hθ]
    exact if_pos hm
  have hout : ∀ m, m ∉ symWindow r → cosBump r m = 0 := fun m hm => if_neg hm
  have hA0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hA : 2 * (1 - Real.cos θ) ≤ θ ^ 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hB : 1 - Real.cos (θ / 2) ≤ θ ^ 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ / 2)
    nlinarith [sq_nonneg θ]
  have hcosr : Real.cos ((r : ℝ) * θ) = -Real.cos (θ / 2) := by
    rw [show (r : ℝ) * θ = Real.pi - θ / 2 by linarith, Real.cos_pi_sub]
  have hcosr1 : Real.cos (((r : ℝ) + 1) * θ) = -Real.cos (θ / 2) := by
    rw [show ((r : ℝ) + 1) * θ = θ / 2 + Real.pi by linarith, Real.cos_add_pi]
  have sdG : ∀ t : ℝ, Real.cos ((t + 1) * θ) + Real.cos ((t - 1) * θ) - 2 * Real.cos (t * θ) =
      2 * Real.cos (t * θ) * (Real.cos θ - 1) := by
    intro t
    rw [add_mul, sub_mul, one_mul, Real.cos_add, Real.cos_sub]
    ring
  have key : ∀ m : ℤ, 0 ≤ m → |cosBump r (m + 1) + cosBump r (m - 1) - 2 * cosBump r m| ≤ θ ^ 2 := by
    intro m hm
    rcases lt_or_ge m r with hlt | hge
    · rw [hin (m + 1) (mem_symWindow.2 (by omega)), hin (m - 1) (mem_symWindow.2 (by omega)),
        hin m (mem_symWindow.2 (by omega))]
      have h := sdG (m : ℝ)
      have ht1 := Real.cos_le_one ((m : ℝ) * θ)
      have ht2 := Real.neg_one_le_cos ((m : ℝ) * θ)
      push_cast
      rw [abs_le]
      constructor <;>
        nlinarith [mul_nonneg hA0 (sub_nonneg.2 ht1), mul_nonneg hA0 (by linarith : 0 ≤ 1 + Real.cos ((m : ℝ) * θ))]
    · rcases eq_or_lt_of_le hge with heq | hgt
      · subst heq
        rw [hout ((r : ℤ) + 1) (fun h => by have := mem_symWindow.1 h; omega),
          hin ((r : ℤ) - 1) (mem_symWindow.2 (by omega)), hin (r : ℤ) (mem_symWindow.2 (by omega))]
        have h := sdG (r : ℝ)
        rw [hcosr1, hcosr] at h
        push_cast
        rw [hcosr]
        have h1 : Real.cos (θ / 2) * (1 - Real.cos θ) ≤ 1 - Real.cos θ := by nlinarith
        have h0 : 0 ≤ Real.cos (θ / 2) * (1 - Real.cos θ) := mul_nonneg hκ0 hA0
        rw [abs_le]
        constructor <;> nlinarith
      · rcases eq_or_lt_of_le (show (r : ℤ) + 1 ≤ m by omega) with heq | hgt'
        · subst heq
          rw [hout ((r : ℤ) + 1 + 1) (fun h => by have := mem_symWindow.1 h; omega),
            hout ((r : ℤ) + 1) (fun h => by have := mem_symWindow.1 h; omega),
            show (r : ℤ) + 1 - 1 = r by ring, hin (r : ℤ) (mem_symWindow.2 (by omega))]
          push_cast
          rw [hcosr, abs_le]
          constructor <;> nlinarith [sq_nonneg θ]
        · rw [hout (m + 1) (fun h => by have := mem_symWindow.1 h; omega),
            hout (m - 1) (fun h => by have := mem_symWindow.1 h; omega),
            hout m (fun h => by have := mem_symWindow.1 h; omega)]
          simpa using sq_nonneg θ
  refine ⟨hout, ?_, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m ∈ symWindow r
    · rw [hin m hm]
      linarith [Real.neg_one_le_cos ((m : ℝ) * θ)]
    · rw [hout m hm]
  · intro m
    by_cases hm : m ∈ symWindow r
    · rw [hin m hm]
      linarith [Real.cos_le_one ((m : ℝ) * θ)]
    · rw [hout m hm]
      norm_num
  · rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib]
    have hone : ∑ m ∈ symWindow r, (1 : ℝ) = 2 * r + 1 := by
      rw [sum_symWindow_eq_sum_range]
      simp
    have hcos : ∑ m ∈ symWindow r, Real.cos ((m : ℝ) * θ) = 0 := by
      rw [sum_symWindow_eq_sum_range]
      have hterm : ∀ j ∈ Finset.range (2 * r + 1),
          2 * Real.sin (θ / 2) * Real.cos ((((j : ℤ) - r : ℤ) : ℝ) * θ) =
            Real.sin ((((j + 1 : ℕ) : ℝ) - r) * θ - θ / 2) -
              Real.sin (((j : ℝ) - r) * θ - θ / 2) := by
        intro j _
        push_cast
        rw [show ((j : ℝ) + 1 - r) * θ - θ / 2 = ((j : ℝ) - r) * θ + θ / 2 by ring, Real.sin_add,
          Real.sin_sub]
        ring
      have htel := Finset.sum_range_sub (fun j : ℕ => Real.sin (((j : ℝ) - r) * θ - θ / 2))
        (2 * r + 1)
      rw [← Finset.sum_congr rfl hterm, ← Finset.mul_sum] at htel
      have e1 : (((2 * r + 1 : ℕ) : ℝ) - r) * θ - θ / 2 = Real.pi := by
        push_cast
        linarith
      have e2 : (((0 : ℕ) : ℝ) - r) * θ - θ / 2 = -Real.pi := by
        push_cast
        linarith
      rw [e1, e2, Real.sin_pi, Real.sin_neg, Real.sin_pi] at htel
      have h2 : 2 * Real.sin (θ / 2) ≠ 0 := mul_ne_zero two_ne_zero hs
      have h3 := htel
      simp only [sub_self, neg_zero] at h3
      exact (mul_eq_zero.1 h3).resolve_left h2
    rw [hone, hcos, add_zero]
  · intro m
    rw [← hθsq]
    rcases le_or_gt 0 m with hm | hm
    · exact key m hm
    · have h := key (-m) (by omega)
      rw [show -m + 1 = -(m - 1) by ring, show -m - 1 = -(m + 1) by ring, cosBump_neg, cosBump_neg,
        cosBump_neg, add_comm (cosBump r (m - 1))] at h
      exact h
theorem exists_isBumpProfile (r : ℕ) : ∃ f, IsBumpProfile r f := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨_, isBumpProfile_delta⟩
  · exact ⟨_, isBumpProfile_cosBump hr⟩
section Circle
variable {S c : ℝ} {P r : ℕ} {f : ℤ → ℝ}
open scoped Classical in
def circleLift (S c : ℝ) (r : ℕ) (f : ℤ → ℝ) (u : AddCircle S) : ℝ :=
  ∑ w ∈ symWindow r, if u = ((c * (w : ℝ) : ℝ) : AddCircle S) then f w else 0
theorem int_eq_of_coe_mul_eq (hc : 0 < c) (hS : S = P * c) {a b : ℤ}
    (h : ((c * (a : ℝ) : ℝ) : AddCircle S) = ((c * (b : ℝ) : ℝ) : AddCircle S))
    (hab : |a - b| < P) : a = b := by
  have h0 : ((c * ((a - b : ℤ) : ℝ) : ℝ) : AddCircle S) = 0 := by
    push_cast
    rw [mul_sub, AddCircle.coe_sub, h, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  have h1 : c * ((n * P : ℤ) : ℝ) = c * ((a - b : ℤ) : ℝ) := by
    rw [← hn, hS]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have h2 : n * P = a - b := by exact_mod_cast mul_left_cancel₀ hc.ne' h1
  have h3 : n = 0 := by
    by_contra hne
    have h4 : 1 ≤ |n| := Int.one_le_abs hne
    rw [← h2, abs_mul, Nat.abs_cast] at hab
    nlinarith [(Nat.cast_nonneg P : (0 : ℤ) ≤ P)]
  rw [h3, zero_mul] at h2
  omega
theorem circleLift_coe (hc : 0 < c) (hS : S = P * c) (hf : ∀ m, m ∉ symWindow r → f m = 0) {m : ℤ}
    (h1 : (r : ℤ) - P < m) (h2 : m < P - r) :
    circleLift S c r f ((c * (m : ℝ) : ℝ) : AddCircle S) = f m := by
  unfold circleLift
  have hne : ∀ w ∈ symWindow r, w ≠ m →
      ((c * (m : ℝ) : ℝ) : AddCircle S) ≠ ((c * (w : ℝ) : ℝ) : AddCircle S) := by
    intro w hw hwm h
    have := mem_symWindow.1 hw
    exact hwm (int_eq_of_coe_mul_eq hc hS h (abs_lt.2 ⟨by omega, by omega⟩)).symm
  by_cases hw : m ∈ symWindow r
  · rw [Finset.sum_eq_single m (fun w hw' hwm => if_neg (hne w hw' hwm))
      (fun h => absurd hw h), if_pos rfl]
  · rw [hf m hw]
    exact Finset.sum_eq_zero fun w hw' => if_neg (hne w hw' fun h => hw (h ▸ hw'))
theorem exists_coe_eq_balanced (hS : S = P * c) (hP : 0 < P) (m : ℤ) :
    ∃ m' : ℤ, ((c * (m : ℝ) : ℝ) : AddCircle S) = ((c * (m' : ℝ) : ℝ) : AddCircle S) ∧
      -((P : ℤ) / 2) ≤ m' ∧ m' < ((P : ℤ) + 1) / 2 := by
  refine ⟨m.bmod P, ?_, Int.le_bmod hP, Int.bmod_lt hP⟩
  have hmod : m.bmod P ≡ m [ZMOD P] := Int.bmod_emod
  obtain ⟨j, hj⟩ := hmod.dvd
  have h0 : ((c * (m : ℝ) - c * ((m.bmod P : ℤ) : ℝ) : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨j, ?_⟩
    have h' : (m : ℝ) - ((m.bmod P : ℤ) : ℝ) = P * j := by exact_mod_cast hj
    rw [zsmul_eq_mul, hS, ← mul_sub, h']
    ring
  rw [AddCircle.coe_sub] at h0
  exact sub_eq_zero.1 h0
theorem abs_circleLift_secondDiff_le (hc : 0 < c) (hS : S = P * c) (hP : 6 ≤ P) (hPr : 4 * r + 2 ≤ P)
    (hf : ∀ m, m ∉ symWindow r → f m = 0) {K : ℝ}
    (hK : ∀ m, |f (m + 1) + f (m - 1) - 2 * f m| ≤ K) (m : ℤ) :
    |circleLift S c r f (((c * (m : ℝ) : ℝ) : AddCircle S) + (c : AddCircle S)) +
        circleLift S c r f (((c * (m : ℝ) : ℝ) : AddCircle S) - (c : AddCircle S)) -
        2 * circleLift S c r f ((c * (m : ℝ) : ℝ) : AddCircle S)| ≤ K := by
  obtain ⟨m', hm, h1, h2⟩ := exists_coe_eq_balanced (c := c) hS (by omega) m
  have hplus : ((c * (m' : ℝ) : ℝ) : AddCircle S) + (c : AddCircle S) =
      ((c * ((m' + 1 : ℤ) : ℝ) : ℝ) : AddCircle S) := by
    rw [← AddCircle.coe_add]
    congr 1
    push_cast
    ring
  have hminus : ((c * (m' : ℝ) : ℝ) : AddCircle S) - (c : AddCircle S) =
      ((c * ((m' - 1 : ℤ) : ℝ) : ℝ) : AddCircle S) := by
    rw [← AddCircle.coe_sub]
    congr 1
    push_cast
    ring
  rw [hm, hplus, hminus, circleLift_coe hc hS hf (by omega) (by omega),
    circleLift_coe hc hS hf (by omega) (by omega), circleLift_coe hc hS hf (by omega) (by omega)]
  exact hK m'
theorem circleLift_bounds (hc : 0 < c) (hS : S = P * c) (hP : 6 ≤ P) (hPr : 4 * r + 2 ≤ P)
    (hf : IsBumpProfile r f) (m : ℤ) :
    0 ≤ circleLift S c r f ((c * (m : ℝ) : ℝ) : AddCircle S) ∧
      circleLift S c r f ((c * (m : ℝ) : ℝ) : AddCircle S) ≤ 2 := by
  obtain ⟨m', hm, h1, h2⟩ := exists_coe_eq_balanced (c := c) hS (by omega) m
  rw [hm, circleLift_coe hc hS hf.eq_zero_of_not_mem (by omega) (by omega)]
  exact ⟨hf.nonneg m', hf.le_two m'⟩
theorem exists_mem_of_circleLift_ne_zero {u : AddCircle S} (h : circleLift S c r f u ≠ 0) :
    ∃ w ∈ symWindow r, u = ((c * (w : ℝ) : ℝ) : AddCircle S) := by
  by_contra hh
  exact h (Finset.sum_eq_zero fun w hw => if_neg fun hu => hh ⟨w, hw, hu⟩)
end Circle
section Lattice
variable {D : TorusData}
theorem scale_zero_pos (D : TorusData) : 0 < D.scale 0 := by
  simpa [TorusData.scale] using D.bareSpacing_pos
theorem exists_side_eq_mul (D : TorusData) {n : ℕ} (hn : n ≤ D.top) :
    ∃ P : ℕ, D.side = P * D.scale 0 ∧ 6 ≤ P ∧ 2 * D.L ^ n ≤ P := by
  obtain ⟨k, hk, hs⟩ := D.side_multiple
  have hL := D.blocking.three_le_factor
  have hM := D.le_blockNumber
  have h1 : 1 ≤ D.L ^ D.top := Nat.one_le_pow _ _ (by omega)
  have h2 : D.L ^ n ≤ D.L ^ D.top := Nat.pow_le_pow_right (by omega) hn
  have h3 : 3 ≤ D.blockNumber * D.L ^ D.top := by nlinarith
  have h4 : D.L ^ n ≤ D.blockNumber * D.L ^ D.top := by nlinarith
  refine ⟨2 * k * (D.blockNumber * D.L ^ D.top), ?_, ?_, ?_⟩
  · rw [hs]
    simp only [TorusData.scale]
    push_cast
    ring
  · nlinarith
  · nlinarith
theorem mem_latticeAt_zero_of_mem {n : ℕ} {y : D.Space} (hy : y ∈ D.latticeAt (D.scale n)) :
    y ∈ D.latticeAt (D.scale 0) := by
  obtain ⟨k, rfl⟩ := hy
  refine ⟨fun μ => (D.L : ℤ) ^ n * k μ, ?_⟩
  congr 1
  funext μ
  simp only [TorusData.scale]
  push_cast
  ring
theorem add_mem_latticeAt {σ : ℝ} {a b : D.Space} (ha : a ∈ D.latticeAt σ)
    (hb : b ∈ D.latticeAt σ) : a + b ∈ D.latticeAt σ := by apply _root_.YangMills.Construction.Weighted.CubeGeometry.Cube.add_mem_latticeAt <;> assumption
theorem neg_mem_latticeAt {σ : ℝ} {a : D.Space} (ha : a ∈ D.latticeAt σ) :
    -a ∈ D.latticeAt σ := by
  obtain ⟨k, rfl⟩ := ha
  refine ⟨-k, ?_⟩
  funext μ
  simp only [torusProj, Pi.neg_apply]
  rw [← AddCircle.coe_neg]
  congr 1
  push_cast
  ring
theorem unitStep_apply_self (μ : Fin 4) : D.unitStep μ μ = ((D.scale 0 : ℝ) : AddCircle D.side) := by
  simp [TorusData.unitStep, torusProj]
theorem unitStep_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) : D.unitStep μ ν = 0 := by
  simp [TorusData.unitStep, torusProj, Pi.single_eq_of_ne h]
theorem unitStep_mem (μ : Fin 4) : D.unitStep μ ∈ D.latticeAt (D.scale 0) := by
  refine ⟨Pi.single μ 1, ?_⟩
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [unitStep_apply_self, torusProj]
  · simp [unitStep_apply_of_ne h, torusProj, Pi.single_eq_of_ne h]
theorem unitStep_injective {P : ℕ} (hS : D.side = P * D.scale 0) (hP : 6 ≤ P) :
    Function.Injective D.unitStep := by
  intro μ ν h
  by_contra hne
  have h1 := congrFun h μ
  rw [unitStep_apply_self, unitStep_apply_of_ne hne] at h1
  have h2 : ((D.scale 0 * ((1 : ℤ) : ℝ) : ℝ) : AddCircle D.side) =
      ((D.scale 0 * ((0 : ℤ) : ℝ) : ℝ) : AddCircle D.side) := by
    simpa using h1
  have h3 := int_eq_of_coe_mul_eq (scale_zero_pos D) hS h2
    (by simp only [sub_zero, abs_one]; omega)
  omega
def stepUp (x : D.BareSite) (μ : Fin 4) : D.BareSite :=
  ⟨x.1 + D.unitStep μ, add_mem_latticeAt x.2 (unitStep_mem μ)⟩
def stepDown (x : D.BareSite) (μ : Fin 4) : D.BareSite :=
  ⟨x.1 + -D.unitStep μ, add_mem_latticeAt x.2 (neg_mem_latticeAt (unitStep_mem μ))⟩
def bondInto (x : D.BareSite) (μ : Fin 4) : D.Bond :=
  ⟨stepDown x μ, x, μ, by simp [stepDown]⟩
def bondFrom (x : D.BareSite) (μ : Fin 4) : D.Bond :=
  ⟨x, stepUp x μ, μ, by simp [stepUp]⟩
theorem finsum_target_eq (hinj : Function.Injective D.unitStep) (g : D.Bond → ℝ) (x : D.BareSite) :
    ∑ᶠ b ∈ {b : D.Bond | b.target = x}, g b = ∑ μ, g (bondInto x μ) := by
  have hset : {b : D.Bond | b.target = x} = Set.range (bondInto x) := by
    ext b
    constructor
    · intro hb
      have hb' : b.target = x := hb
      obtain ⟨μ, hμ⟩ := b.isPositive
      refine ⟨μ, TorusData.Bond.ext ?_ hb'.symm⟩
      apply Subtype.ext
      change x.1 + -D.unitStep μ = b.source.1
      rw [← hμ, hb']
      abel
    · rintro ⟨μ, rfl⟩
      rfl
  have hi : Function.Injective (bondInto x) := by
    intro μ ν h
    have h1 : (x.1 + -D.unitStep μ) = (x.1 + -D.unitStep ν) :=
      congrArg (fun b : D.Bond => (b.source : D.Space)) h
    exact hinj (neg_injective (add_left_cancel h1))
  rw [hset, finsum_mem_range hi, finsum_eq_sum_of_fintype]
theorem finsum_source_eq (hinj : Function.Injective D.unitStep) (g : D.Bond → ℝ) (x : D.BareSite) :
    ∑ᶠ b ∈ {b : D.Bond | b.source = x}, g b = ∑ μ, g (bondFrom x μ) := by
  have hset : {b : D.Bond | b.source = x} = Set.range (bondFrom x) := by
    ext b
    constructor
    · intro hb
      have hb' : b.source = x := hb
      obtain ⟨μ, hμ⟩ := b.isPositive
      refine ⟨μ, TorusData.Bond.ext hb'.symm ?_⟩
      apply Subtype.ext
      change x.1 + D.unitStep μ = b.target.1
      rw [← hμ, hb']
      abel
    · rintro ⟨μ, rfl⟩
      rfl
  have hi : Function.Injective (bondFrom x) := by
    intro μ ν h
    have h1 : (x.1 + D.unitStep μ) = (x.1 + D.unitStep ν) :=
      congrArg (fun b : D.Bond => (b.target : D.Space)) h
    exact hinj (add_left_cancel h1)
  rw [hset, finsum_mem_range hi, finsum_eq_sum_of_fintype]
theorem bareLaplacian_eq_sum (hinj : Function.Injective D.unitStep) (φ : D.BareSite → ℝ) (x : D.BareSite) :
    TorusData.bareLaplacian φ x =
      ((D.scale 0)⁻¹) ^ 2 * ∑ μ, (2 * φ x - φ (stepUp x μ) - φ (stepDown x μ)) := by
  unfold TorusData.bareLaplacian
  rw [finsum_target_eq hinj, finsum_source_eq hinj]
  simp only [TorusData.bondGrad, TorusData.bondDiff, bondInto, bondFrom]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib, sq, mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun μ _ => by ring
end Lattice
section Test
variable {D : TorusData}
def blockBump (D : TorusData) (r : ℕ) (f : ℤ → ℝ) (y : D.Space) (x : D.BareSite) : ℝ :=
  ∏ ν, circleLift D.side (D.scale 0) r f (((x : D.Space) - y) ν)
theorem exists_sub_eq_coe {x y : D.Space} (hx : x ∈ D.latticeAt (D.scale 0))
    (hy : y ∈ D.latticeAt (D.scale 0)) :
    ∃ m : Fin 4 → ℤ, ∀ ν, (x - y) ν = ((D.scale 0 * (m ν : ℝ) : ℝ) : AddCircle D.side) := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  refine ⟨k - l, fun ν => ?_⟩
  simp only [torusProj, Pi.sub_apply]
  rw [← AddCircle.coe_sub]
  congr 1
  push_cast
  ring
theorem prod_add_single (F : AddCircle D.side → ℝ) (u h : D.Space) (μ : Fin 4)
    {t : AddCircle D.side} (h1 : h μ = t) (h2 : ∀ ν, ν ≠ μ → h ν = 0) :
    ∏ ν, F ((u + h) ν) = F (u μ + t) * ∏ ν ∈ Finset.univ.erase μ, F (u ν) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
  congr 1
  · simp [h1]
  · refine Finset.prod_congr rfl fun ν hν => ?_
    simp [h2 ν (Finset.ne_of_mem_erase hν)]
theorem abs_blockBump_secondDiff_le {P r : ℕ} {f : ℤ → ℝ} (hS : D.side = P * D.scale 0) (hP : 6 ≤ P)
    (hPr : 4 * r + 2 ≤ P) (hf : IsBumpProfile r f) {y : D.Space}
    (hy : y ∈ D.latticeAt (D.scale 0)) (x : D.BareSite) (μ : Fin 4) :
    |2 * blockBump D r f y x - blockBump D r f y (stepUp x μ) -
        blockBump D r f y (stepDown x μ)| ≤ 8 * (4 * Real.pi ^ 2 / (2 * r + 1) ^ 2) := by
  have hc := scale_zero_pos D
  obtain ⟨m, hm⟩ := exists_sub_eq_coe x.2 hy
  obtain ⟨F, hF⟩ : ∃ F, F = circleLift D.side (D.scale 0) r f := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ∏ ν ∈ Finset.univ.erase μ, F (((x : D.Space) - y) ν) := ⟨_, rfl⟩
  have hx : blockBump D r f y x = F (((x : D.Space) - y) μ) * R := by
    rw [hR, Finset.mul_prod_erase Finset.univ (fun ν => F (((x : D.Space) - y) ν))
      (Finset.mem_univ μ), hF]
    rfl
  have hu : blockBump D r f y (stepUp x μ) =
      F (((x : D.Space) - y) μ + ((D.scale 0 : ℝ) : AddCircle D.side)) * R := by
    rw [hR, ← prod_add_single F _ (D.unitStep μ) μ (unitStep_apply_self μ) fun ν h => unitStep_apply_of_ne h, hF]
    refine Finset.prod_congr rfl fun ν _ => ?_
    congr 1
    change (x.1 + D.unitStep μ - y) ν = _
    rw [add_sub_right_comm]
  have hd : blockBump D r f y (stepDown x μ) =
      F (((x : D.Space) - y) μ - ((D.scale 0 : ℝ) : AddCircle D.side)) * R := by
    rw [hR, sub_eq_add_neg (((x : D.Space) - y) μ),
      ← prod_add_single F _ (-D.unitStep μ) μ (by simp [unitStep_apply_self])
        (fun ν h => by simp [unitStep_apply_of_ne h]), hF]
    refine Finset.prod_congr rfl fun ν _ => ?_
    congr 1
    change (x.1 + -D.unitStep μ - y) ν = _
    rw [add_sub_right_comm]
  have hb : ∀ ν, 0 ≤ F (((x : D.Space) - y) ν) ∧ F (((x : D.Space) - y) ν) ≤ 2 := by
    intro ν
    rw [hm ν, hF]
    exact circleLift_bounds hc hS hP hPr hf (m ν)
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact Finset.prod_nonneg fun ν _ => (hb ν).1
  have hR8 : R ≤ 8 := by
    rw [hR]
    calc ∏ ν ∈ Finset.univ.erase μ, F (((x : D.Space) - y) ν)
        ≤ ∏ _ν ∈ Finset.univ.erase μ, (2 : ℝ) :=
          Finset.prod_le_prod (fun ν _ => (hb ν).1) fun ν _ => (hb ν).2
      _ = 8 := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ μ)]
          norm_num
  have hsd := abs_circleLift_secondDiff_le hc hS hP hPr hf.eq_zero_of_not_mem hf.abs_secondDiff_le (m μ)
  rw [← hm μ, ← hF] at hsd
  rw [hx, hu, hd, show ∀ a b e : ℝ, 2 * (a * R) - b * R - e * R = -(R * (b + e - 2 * a)) by
    intro a b e
    ring, abs_neg, abs_mul, abs_of_nonneg hR0]
  exact mul_le_mul hR8 hsd (abs_nonneg _) (by norm_num)
theorem exists_blockBump (D : TorusData) {y : D.Space} {n : ℕ} (hn : n ≤ D.top)
    (hy : y ∈ D.latticeAt (D.scale n)) :
    ∃ φ : D.BareSite → ℝ,
      (∀ x, x ∉ D.bareSites (D.cubeAround (D.scale n) y) → φ x = 0) ∧
      ∑ᶠ x ∈ D.bareSites (D.cubeAround (D.scale n) y), φ x = (D.L : ℝ) ^ (n * 4) ∧
      ∀ x, |TorusData.bareLaplacian φ x| ≤ testLaplacianConst 4 * (D.scale n ^ 2)⁻¹ := by
  obtain ⟨P, hS, hP, hPN⟩ := exists_side_eq_mul D hn
  obtain ⟨r, hr⟩ : Odd (D.L ^ n) := D.blocking.factor_odd.pow
  obtain ⟨f, hf⟩ := exists_isBumpProfile r
  have hc := scale_zero_pos D
  have hPr : 4 * r + 2 ≤ P := by omega
  have hLr : (D.L : ℝ) ^ n = 2 * r + 1 := by exact_mod_cast hr
  have hξ : D.scale n = (2 * r + 1) * D.scale 0 := by
    simp only [TorusData.scale]
    rw [hLr]
    simp
  have hy0 := mem_latticeAt_zero_of_mem hy
  have hinj := unitStep_injective hS hP
  have hemem : ∀ k : Fin 4 → ℤ, y + torusProj D.side (fun μ => D.scale 0 * (k μ : ℝ)) ∈
      D.latticeAt (D.scale 0) := fun k => add_mem_latticeAt hy0 ⟨k, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin 4 → ℤ) → D.BareSite, ∀ k, (e k : D.Space) =
      y + torusProj D.side (fun μ => D.scale 0 * (k μ : ℝ)) := ⟨fun k => ⟨_, hemem k⟩, fun _ => rfl⟩
  have hmem : ∀ x, blockBump D r f y x ≠ 0 →
      x ∈ D.bareSites (D.cubeAround (D.scale n) y) ∧
        ∃ k ∈ Fintype.piFinset fun _ : Fin 4 => symWindow r, e k = x := by
    intro x hx
    have hne := Finset.prod_ne_zero_iff.1 hx
    choose w hw hw' using fun ν => exists_mem_of_circleLift_ne_zero (hne ν (Finset.mem_univ ν))
    have hcov : torusProj D.side (fun ν => D.scale 0 * (w ν : ℝ)) = (x : D.Space) - y :=
      funext fun ν => (hw' ν).symm
    constructor
    · change torusSupNorm ((x : D.Space) - y) ≤ D.scale n / 2
      refine le_trans (csInf_le ⟨0, ?_⟩ ⟨_, hcov, rfl⟩) ?_
      · rintro _ ⟨v, -, rfl⟩
        exact le_trans (abs_nonneg (v 0)) (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
      · refine Finset.sup'_le _ _ fun ν _ => ?_
        have h1 := mem_symWindow.1 (hw ν)
        have h2 : |(w ν : ℝ)| ≤ r := by
          refine abs_le.2 ⟨?_, ?_⟩
          · exact_mod_cast h1.1
          · exact_mod_cast h1.2
        rw [abs_mul, abs_of_pos hc, hξ]
        nlinarith
    · refine ⟨w, Fintype.mem_piFinset.2 hw, Subtype.ext ?_⟩
      rw [he, hcov]
      abel
  have hwin : ∀ k ∈ Fintype.piFinset (fun _ : Fin 4 => symWindow r), ∀ ν,
      -(r : ℤ) ≤ k ν ∧ k ν ≤ r := fun k hk ν => mem_symWindow.1 (Fintype.mem_piFinset.1 hk ν)
  have heval : ∀ k ∈ Fintype.piFinset (fun _ : Fin 4 => symWindow r),
      blockBump D r f y (e k) = ∏ ν, f (k ν) := by
    intro k hk
    refine Finset.prod_congr rfl fun ν _ => ?_
    have h1 := hwin k hk ν
    rw [he, add_sub_cancel_left]
    exact circleLift_coe hc hS hf.eq_zero_of_not_mem (by omega) (by omega)
  have hinjOn : Set.InjOn e (Fintype.piFinset fun _ : Fin 4 => symWindow r :
      Finset (Fin 4 → ℤ)) := by
    intro k hk k' hk' h
    have h1 := congrArg (fun z : D.BareSite => (z : D.Space)) h
    simp only [he] at h1
    have h2 := add_left_cancel h1
    funext ν
    have h3 := hwin k hk ν
    have h4 := hwin k' hk' ν
    exact int_eq_of_coe_mul_eq hc hS (congrFun h2 ν) (abs_lt.2 ⟨by omega, by omega⟩)
  refine ⟨blockBump D r f y, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hne
    exact hx (hmem x hne).1
  · have hs : D.bareSites (D.cubeAround (D.scale n) y) ∩
        Function.support (blockBump D r f y) =
        (e '' ((Fintype.piFinset fun _ : Fin 4 => symWindow r : Finset (Fin 4 → ℤ)) :
          Set (Fin 4 → ℤ))) ∩ Function.support (blockBump D r f y) := by
      ext x
      constructor
      · rintro ⟨-, hx⟩
        obtain ⟨-, k, hk, rfl⟩ := hmem x hx
        exact ⟨⟨k, hk, rfl⟩, hx⟩
      · rintro ⟨-, hx⟩
        exact ⟨(hmem x hx).1, hx⟩
    rw [finsum_mem_inter_support_eq _ _ _ hs, finsum_mem_image hinjOn, finsum_mem_coe_finset,
      Finset.sum_congr rfl heval,
      ← Finset.prod_univ_sum (fun _ : Fin 4 => symWindow r) (fun _ m => f m)]
    simp only [hf.sum_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, hLr]
  · intro x
    rw [bareLaplacian_eq_sum hinj, abs_mul, abs_of_nonneg (by positivity)]
    have hsum : |∑ μ, (2 * blockBump D r f y x - blockBump D r f y (stepUp x μ) -
        blockBump D r f y (stepDown x μ))| ≤ 4 * (8 * (4 * Real.pi ^ 2 / (2 * r + 1) ^ 2)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun μ _ => abs_blockBump_secondDiff_le hS hP hPr hf hy0 x μ) ?_
      simp
    have hfinal : ((D.scale 0)⁻¹) ^ 2 * (4 * (8 * (4 * Real.pi ^ 2 / (2 * r + 1) ^ 2))) =
        testLaplacianConst 4 * (D.scale n ^ 2)⁻¹ := by
      rw [hξ]
      unfold testLaplacianConst
      have hN : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [← hfinal]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
end Test
theorem blockBumpsExist : BlockBumpsExist := by
  intro G y hy
  have hex : ∃ n, y ∈ G.chain.layerSites n := by
    simp only [SeparatedChain.allSites, Set.mem_iUnion] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, hn⟩
  have hl : y ∈ G.chain.layerSites (G.chain.level y) := Nat.sInf_mem hex
  have hlt : G.chain.level y ≤ G.data.top := by
    by_contra h
    have h1 : ¬ G.chain.level y < G.data.top := by omega
    have h2 : G.chain.level y ≠ G.data.top := by omega
    have h3 := hl.2
    simp [SeparatedChain.layer, h1, h2] at h3
  obtain ⟨φ, h1, h2, h3⟩ := exists_blockBump G.data hlt hl.1
  exact ⟨φ, h1, h2, h3⟩
end YangMills.Construction.Weighted.BlockBumps
end
