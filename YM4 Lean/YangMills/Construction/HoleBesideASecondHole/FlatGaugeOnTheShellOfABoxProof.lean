import YangMills.Construction.HoleBesideASecondHole.FlatGaugeOnTheShellOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace LatticeGauge
namespace BoundaryGauge
variable (X : (Fin 4 → ℤ) → Fin 4 → UnitQuaternion) (lo hi : Fin 4 → ℤ)
theorem unitVec_self (i : Fin 4) : unitVec i i = 1 := by simp [unitVec]
theorem unitVec_of_ne {i j : Fin 4} (h : j ≠ i) : unitVec i j = 0 := by simp [unitVec, h]
theorem sum_range_le_mul {k : ℕ} {M : ℕ} {e : ℝ} (he : 0 ≤ e) (hk : k ≤ M) (f : ℕ → ℝ)
    (H : ∀ r < k, f r ≤ e) : ∑ r ∈ Finset.range k, f r ≤ M * e := by
  have h1 : ∑ r ∈ Finset.range k, f r ≤ ∑ _r ∈ Finset.range k, e :=
    Finset.sum_le_sum fun r hr => H r (Finset.mem_range.mp hr)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) ≤ M := by exact_mod_cast hk
  nlinarith
theorem exists_gauge_on_slice (M : ℕ) (e : ℝ) (hM : ∀ i, hi i - lo i ≤ M) (he : 0 ≤ e) (c : ℤ)
    (H : ∀ a μ ν, μ ≠ 3 → ν ≠ 3 → μ ≠ ν → a 3 = c → a ∈ box lo hi →
      a + unitVec μ ∈ box lo hi → a + unitVec ν ∈ box lo hi →
      a + unitVec μ + unitVec ν ∈ box lo hi → plaquetteDefect X a μ ν ≤ e) :
    ∃ γ : (Fin 4 → ℤ) → UnitQuaternion, ∀ x j, j ≠ 3 → x 3 = c → x ∈ box lo hi →
      x + unitVec j ∈ box lo hi → gaugeDefect X γ x j ≤ 2 * M * e := by
  have hMe : (0 : ℝ) ≤ M * e := by positivity
  have strip : ∀ (i j : Fin 4), i ≠ 3 → j ≠ 3 → j ≠ i → ∀ x, x 3 = c → x ∈ box lo hi →
      x + unitVec j ∈ box lo hi →
      ∑ r ∈ Finset.range (x i - lo i).toNat,
        plaquetteDefect X (Function.update x i (lo i) + (r : ℤ) • unitVec i) i j ≤ M * e := by
    intro i j hi3 hj3 hji x hx3 hx hx'
    have hk : (x i - lo i).toNat ≤ M := by
      have h1 := hx i
      have h2 := hx' i
      have h3 := hM i
      omega
    refine sum_range_le_mul he hk _ fun r hr => ?_
    have hr' : (r : ℤ) + 1 ≤ x i - lo i := by omega
    have hxi := hx i
    have hxj : ∀ l, lo l ≤ (x + unitVec j) l ∧ (x + unitVec j) l ≤ hi l := hx'
    have mem : ∀ (d : ℤ) (b : Bool), 0 ≤ d → (r : ℤ) + d ≤ x i - lo i →
        (Function.update x i (lo i) + (r : ℤ) • unitVec i + d • unitVec i +
          (if b then unitVec j else 0)) ∈ box lo hi := by
      intro d b hd hd' l
      by_cases hl : l = i
      · subst hl
        cases b <;> simp [unitVec_self, unitVec_of_ne hji.symm, unitVec_of_ne hji] <;> omega
      · have := hx l
        have h2 := hxj l
        cases b <;> simp [Function.update_of_ne hl, unitVec_of_ne (Ne.symm (Ne.symm hl)), hl] <;>
          simp at h2 <;> omega
    have m0 := mem 0 false le_rfl (by omega)
    have m1 := mem 1 false (by omega) (by omega)
    have m2 := mem 0 true le_rfl (by omega)
    have m3 := mem 1 true (by omega) (by omega)
    simp only [zero_smul, one_smul, add_zero, if_true, if_false, Bool.false_eq_true] at m0 m1 m2 m3
    refine H _ i j hi3 hj3 hji.symm ?_ m0 m1 m2 m3
    have : (3 : Fin 4) ≠ i := Ne.symm hi3
    simp [Function.update_of_ne this, unitVec_of_ne hi3.symm, hx3]
  let γ1 := transportedGauge X (fun _ => 1) 0 (lo 0)
  let γ2 := transportedGauge X γ1 1 (lo 1)
  let γ3 := transportedGauge X γ2 2 (lo 2)
  refine ⟨γ3, fun x j hj hx3 hx hx' => ?_⟩
  have h2 : lo 2 ≤ x 2 := (hx 2).1
  have h1 : lo 1 ≤ x 1 := (hx 1).1
  have h0 : lo 0 ≤ x 0 := (hx 0).1
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    revert hj
    fin_cases j <;> simp
  let a := Function.update x 2 (lo 2)
  have ha0 : a 0 = x 0 := by simp [a, Function.update_of_ne (show (0 : Fin 4) ≠ 2 by decide)]
  have ha1 : a 1 = x 1 := by simp [a, Function.update_of_ne (show (1 : Fin 4) ≠ 2 by decide)]
  have ha2 : a 2 = lo 2 := by simp [a]
  have ha3 : a 3 = c := by simp [a, Function.update_of_ne (show (3 : Fin 4) ≠ 2 by decide), hx3]
  have hab : a ∈ box lo hi := by
    intro l
    by_cases hl : l = 2
    · subst hl
      have := hx 2
      have h3 := hM 2
      constructor
      · rw [ha2]
      · rw [ha2]
        omega
    · simp only [a, Function.update_of_ne hl]
      exact hx l
  rcases hj' with rfl | rfl | rfl
  · have s3 := gaugeDefect_transportedGauge_side X γ2 (show (0 : Fin 4) ≠ 2 by decide) (lo 2) x h2
    have t3 := strip 2 0 (by decide) (by decide) (by decide) x hx3 hx hx'
    have hab' : a + unitVec 0 ∈ box lo hi := by
      intro l
      have := hx' l
      by_cases hl : l = 2
      · subst hl
        have h4 := hab 2
        simp [unitVec_of_ne (show (2 : Fin 4) ≠ 0 by decide)] at this ⊢
        omega
      · simpa [a, Function.update_of_ne hl] using this
    have s2 := gaugeDefect_transportedGauge_side X γ1 (show (0 : Fin 4) ≠ 1 by decide) (lo 1) a (by rw [ha1]; exact h1)
    have t2 := strip 1 0 (by decide) (by decide) (by decide) a ha3 hab hab'
    have s1 : gaugeDefect X γ1 (Function.update a 1 (lo 1)) 0 = 0 :=
      gaugeDefect_transportedGauge_along X (fun _ => 1) 0 (lo 0) _ (by
        rw [Function.update_of_ne (show (0 : Fin 4) ≠ 1 by decide), ha0]
        exact h0)
    show gaugeDefect X (transportedGauge X γ2 2 (lo 2)) x 0 ≤ _
    have : gaugeDefect X γ2 a 0 ≤ M * e := by
      have : gaugeDefect X γ2 a 0 ≤ gaugeDefect X γ1 (Function.update a 1 (lo 1)) 0 + _ := s2
      linarith
    linarith
  · have s3 := gaugeDefect_transportedGauge_side X γ2 (show (1 : Fin 4) ≠ 2 by decide) (lo 2) x h2
    have t3 := strip 2 1 (by decide) (by decide) (by decide) x hx3 hx hx'
    have s2 : gaugeDefect X γ2 a 1 = 0 :=
      gaugeDefect_transportedGauge_along X γ1 1 (lo 1) a (by rw [ha1]; exact h1)
    show gaugeDefect X (transportedGauge X γ2 2 (lo 2)) x 1 ≤ _
    have : gaugeDefect X (transportedGauge X γ2 2 (lo 2)) x 1 ≤ gaugeDefect X γ2 a 1 + _ := s3
    linarith
  · have : gaugeDefect X γ3 x 2 = 0 := gaugeDefect_transportedGauge_along X γ2 2 (lo 2) x h2
    rw [this]
    positivity
theorem add_smul_unitVec_apply (a : Fin 4 → ℤ) (i l : Fin 4) (r : ℕ) :
    (a + (r : ℤ) • unitVec i) l = a l + if l = i then (r : ℤ) else 0 := by
  by_cases h : l = i
  · subst h
    simp [unitVec_self]
  · simp [unitVec_of_ne h, h]
def OnSideWall (x : Fin 4 → ℤ) : Prop := ∃ i, i ≠ 3 ∧ (x i = lo i ∨ x i = hi i)
def InLowerPart (x : Fin 4 → ℤ) : Prop := x ∈ box lo hi ∧ (x 3 = lo 3 ∨ OnSideWall lo hi x)
def InTopFace (x : Fin 4 → ℤ) : Prop := x ∈ box lo hi ∧ x 3 = hi 3
theorem gaugeDefect_lowerPart_le (M : ℕ) (e : ℝ) (hM : ∀ i, hi i - lo i ≤ M) (he : 0 ≤ e)
    (Hc : ∀ a μ ν, μ ≠ ν → a ∈ boxBoundary lo hi → a + unitVec μ ∈ boxBoundary lo hi →
      a + unitVec ν ∈ boxBoundary lo hi → a + unitVec μ + unitVec ν ∈ boxBoundary lo hi →
      plaquetteDefect X a μ ν ≤ e)
    (γ : (Fin 4 → ℤ) → UnitQuaternion)
    (hb : ∀ x j, j ≠ 3 → x 3 = lo 3 → x ∈ box lo hi →
      x + unitVec j ∈ box lo hi → gaugeDefect X γ x j ≤ 2 * M * e)
    (hlo : lo 3 ≤ hi 3)
    (x : Fin 4 → ℤ) (j : Fin 4) (hx : InLowerPart lo hi x) (hx' : InLowerPart lo hi (x + unitVec j)) :
    gaugeDefect X (transportedGauge X γ 3 (lo 3)) x j ≤ 3 * M * e := by
  have hMe : (0 : ℝ) ≤ M * e := by positivity
  have h3 : lo 3 ≤ x 3 := (hx.1 3).1
  by_cases hj : j = 3
  · subst hj
    rw [gaugeDefect_transportedGauge_along X γ 3 (lo 3) x h3]
    linarith
  have hs := gaugeDefect_transportedGauge_side X γ hj (lo 3) x h3
  set a := Function.update x 3 (lo 3) with ha
  have hcoord : ∀ l, l ≠ 3 → a l = x l := fun l hl => by simp [a, Function.update_of_ne hl]
  have ha3 : a 3 = lo 3 := by simp [a]
  have hab : a ∈ box lo hi := by
    intro l
    by_cases hl : l = 3
    · subst hl
      rw [ha3]
      exact ⟨le_rfl, hlo⟩
    · rw [hcoord l hl]
      exact hx.1 l
  have hab' : a + unitVec j ∈ box lo hi := by
    intro l
    by_cases hl : l = 3
    · subst hl
      simp only [Pi.add_apply, unitVec_of_ne (Ne.symm hj), add_zero]
      rw [ha3]
      exact ⟨le_rfl, hlo⟩
    · have := hx'.1 l
      simp only [Pi.add_apply] at this ⊢
      rw [hcoord l hl]
      exact this
  have h1 := hb a j hj ha3 hab hab'
  have h2 : ∑ r ∈ Finset.range (x 3 - lo 3).toNat,
      plaquetteDefect X (a + (r : ℤ) • unitVec 3) 3 j ≤ M * e := by
    by_cases h0 : x 3 = lo 3
    · have : (x 3 - lo 3).toNat = 0 := by omega
      rw [this]
      simpa using hMe
    have f1 : OnSideWall lo hi x := hx.2.resolve_left h0
    have f2 : OnSideWall lo hi (x + unitVec j) := hx'.2.resolve_left (by
      simp only [Pi.add_apply, unitVec_of_ne (Ne.symm hj), add_zero]
      exact h0)
    obtain ⟨i₁, hi₁, hf₁⟩ := f1
    obtain ⟨i₂, hi₂, hf₂⟩ := f2
    have hk : (x 3 - lo 3).toNat ≤ M := by
      have := hM 3
      have := (hx.1 3).2
      omega
    refine sum_range_le_mul he hk _ fun r hr => ?_
    have hr' : (r : ℤ) + 1 ≤ x 3 - lo 3 := by omega
    have hx3 := (hx.1 3).2
    have mem1 : ∀ d : ℕ, r + d ≤ (x 3 - lo 3).toNat →
        a + ((r + d : ℕ) : ℤ) • unitVec 3 ∈ boxBoundary lo hi := by
      intro d hd
      refine ⟨fun l => ?_, i₁, ?_⟩
      · rw [add_smul_unitVec_apply]
        by_cases hl : l = 3
        · subst hl
          rw [ha3, if_pos rfl]
          push_cast
          omega
        · rw [if_neg hl, add_zero, hcoord l hl]
          exact hx.1 l
      · rw [add_smul_unitVec_apply, if_neg hi₁, add_zero, hcoord i₁ hi₁]
        exact hf₁
    have mem2 : ∀ d : ℕ, r + d ≤ (x 3 - lo 3).toNat →
        a + ((r + d : ℕ) : ℤ) • unitVec 3 + unitVec j ∈ boxBoundary lo hi := by
      intro d hd
      have key : ∀ l, l ≠ 3 → (a + ((r + d : ℕ) : ℤ) • unitVec 3 + unitVec j) l =
          (x + unitVec j) l := by
        intro l hl
        simp only [Pi.add_apply]
        have := add_smul_unitVec_apply a 3 l (r + d)
        simp only [Pi.add_apply] at this
        rw [this, if_neg hl, add_zero, hcoord l hl]
      refine ⟨fun l => ?_, i₂, ?_⟩
      · by_cases hl : l = 3
        · subst hl
          simp only [Pi.add_apply, unitVec_of_ne (Ne.symm hj), add_zero]
          have := add_smul_unitVec_apply a 3 3 (r + d)
          simp only [Pi.add_apply] at this
          rw [this, ha3, if_pos trivial]
          push_cast
          omega
        · rw [key l hl]
          exact hx'.1 l
      · rw [key i₂ hi₂]
        exact hf₂
    have m0 := mem1 0 (by omega)
    have m1 := mem1 1 (by omega)
    have m2 := mem2 0 (by omega)
    have m3 := mem2 1 (by omega)
    have e1 : a + ((r + 1 : ℕ) : ℤ) • unitVec 3 = a + (r : ℤ) • unitVec 3 + unitVec 3 := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    simp only [add_zero] at m0 m2
    rw [e1] at m1 m3
    exact Hc _ 3 j (Ne.symm hj) m0 m1 m2 m3
  linarith
theorem quatDist_along_wall_le (f : (Fin 4 → ℤ) → UnitQuaternion) (d : ℝ)
    (hstep : ∀ x j, j ≠ 3 → InTopFace lo hi x → InTopFace lo hi (x + unitVec j) → OnSideWall lo hi x →
      OnSideWall lo hi (x + unitVec j) → quatDist (f x) (f (x + unitVec j)) ≤ d)
    (a : Fin 4 → ℤ) (j l : Fin 4) (hj : j ≠ 3) (hl : l ≠ 3) (hlj : l ≠ j) (n : ℕ)
    (hlid : ∀ r ≤ n, InTopFace lo hi (a + (r : ℤ) • unitVec j)) (hface : a l = lo l ∨ a l = hi l) :
    quatDist (f a) (f (a + (n : ℤ) • unitVec j)) ≤ n * d := by
  refine quatDist_walk_le f a j d n fun r hr => ?_
  have e1 : a + ((r + 1 : ℕ) : ℤ) • unitVec j = a + (r : ℤ) • unitVec j + unitVec j := by
    push_cast
    rw [add_smul, one_smul, add_assoc]
  have face : ∀ r : ℕ, OnSideWall lo hi (a + (r : ℤ) • unitVec j) := fun r =>
    ⟨l, hl, by rw [add_smul_unitVec_apply, if_neg hlj, add_zero]; exact hface⟩
  have h1 := hlid r hr.le
  have h2 := hlid (r + 1) hr
  have h3 := face (r + 1)
  rw [e1] at h2 h3 ⊢
  exact hstep _ j hj h1 h2 (face r) h3
theorem quatDist_corner_le (M : ℕ) (hM : ∀ i, hi i - lo i ≤ M) (hle : ∀ i, lo i ≤ hi i) (f : (Fin 4 → ℤ) → UnitQuaternion) (d : ℝ)
    (hd : 0 ≤ d)
    (hstep : ∀ x j, j ≠ 3 → InTopFace lo hi x → InTopFace lo hi (x + unitVec j) → OnSideWall lo hi x →
      OnSideWall lo hi (x + unitVec j) → quatDist (f x) (f (x + unitVec j)) ≤ d)
    (i j k : Fin 4) (hi3 : i ≠ 3) (hj3 : j ≠ 3) (hk3 : k ≠ 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l, l = i ∨ l = j ∨ l = k ∨ l = 3) (x : Fin 4 → ℤ) (hx : InTopFace lo hi x)
    (hface : x i = lo i ∨ x i = hi i) :
    quatDist (f (Function.update lo 3 (hi 3))) (f x) ≤ 3 * M * d := by
  set q := Function.update lo 3 (hi 3) with hq
  have q3 : q 3 = hi 3 := by simp [q]
  have ql : ∀ l, l ≠ 3 → q l = lo l := fun l hl => by simp [q, Function.update_of_ne hl]
  have hxl := hx.1
  have hx3 := hx.2
  set n₁ := (x i - lo i).toNat with hn₁
  set n₂ := (x j - lo j).toNat with hn₂
  set n₃ := (x k - lo k).toNat with hn₃
  have c₁ : (n₁ : ℤ) = x i - lo i := Int.toNat_of_nonneg (by have := (hxl i).1; omega)
  have c₂ : (n₂ : ℤ) = x j - lo j := Int.toNat_of_nonneg (by have := (hxl j).1; omega)
  have c₃ : (n₃ : ℤ) = x k - lo k := Int.toNat_of_nonneg (by have := (hxl k).1; omega)
  set p₁ := q + (n₁ : ℤ) • unitVec i with hp₁
  set p₂ := p₁ + (n₂ : ℤ) • unitVec j with hp₂
  set p₃ := p₂ + (n₃ : ℤ) • unitVec k with hp₃
  have a1 : ∀ l, p₁ l = q l + if l = i then (n₁ : ℤ) else 0 := fun l => add_smul_unitVec_apply q i l n₁
  have a2 : ∀ l, p₂ l = p₁ l + if l = j then (n₂ : ℤ) else 0 := fun l => add_smul_unitVec_apply p₁ j l n₂
  have a3 : ∀ l, p₃ l = p₂ l + if l = k then (n₃ : ℤ) else 0 := fun l => add_smul_unitVec_apply p₂ k l n₃
  have hlast : p₃ = x := by
    funext l
    rcases hcover l with rfl | rfl | rfl | rfl
    · rw [a3, a2, a1, ql _ hi3]
      simp only [if_true, hij, hik, if_false]
      omega
    · rw [a3, a2, a1, ql _ hj3]
      simp only [if_true, hij.symm, hjk, if_false]
      omega
    · rw [a3, a2, a1, ql _ hk3]
      simp only [if_true, hik.symm, hjk.symm, if_false]
      omega
    · rw [a3, a2, a1, q3, if_neg hk3.symm, if_neg hj3.symm, if_neg hi3.symm]
      omega
  have w₁ : quatDist (f q) (f p₁) ≤ n₁ * d := by
    refine quatDist_along_wall_le lo hi f d hstep q i j hi3 hj3 hij.symm n₁ (fun r hr => ⟨fun l => ?_, ?_⟩)
      (Or.inl (ql j hj3))
    · rw [add_smul_unitVec_apply]
      have hr' : (r : ℤ) ≤ n₁ := by exact_mod_cast hr
      by_cases hl3 : l = 3
      · subst hl3
        rw [q3, if_neg hi3.symm]
        have := hle 3
        omega
      · rw [ql l hl3]
        by_cases hli : l = i
        · subst hli
          rw [if_pos rfl]
          have := hxl l
          omega
        · rw [if_neg hli]
          have := hle l
          omega
    · rw [add_smul_unitVec_apply, if_neg hi3.symm, q3]
      omega
  have w₂ : quatDist (f p₁) (f p₂) ≤ n₂ * d := by
    have b1 : p₁ i = x i := by
      rw [a1, ql i hi3, if_pos rfl]
      omega
    refine quatDist_along_wall_le lo hi f d hstep p₁ j i hj3 hi3 hij n₂ (fun r hr => ⟨fun l => ?_, ?_⟩)
      (by rw [b1]; exact hface)
    · rw [add_smul_unitVec_apply]
      have hr' : (r : ℤ) ≤ n₂ := by exact_mod_cast hr
      rcases hcover l with rfl | rfl | rfl | rfl
      · rw [b1, if_neg hij, add_zero]
        exact hxl _
      · rw [a1, ql _ hj3, if_neg hij.symm, if_pos rfl]
        have := hxl l
        omega
      · rw [a1, ql _ hk3, if_neg hik.symm, if_neg hjk.symm]
        have := hle l
        omega
      · rw [a1, q3, if_neg hi3.symm, if_neg hj3.symm]
        have := hle 3
        omega
    · rw [add_smul_unitVec_apply, if_neg hj3.symm, a1, q3, if_neg hi3.symm]
      omega
  have w₃ : quatDist (f p₂) (f p₃) ≤ n₃ * d := by
    have b1 : p₂ i = x i := by
      rw [a2, a1, ql i hi3, if_pos rfl, if_neg hij]
      omega
    refine quatDist_along_wall_le lo hi f d hstep p₂ k i hk3 hi3 hik n₃ (fun r hr => ⟨fun l => ?_, ?_⟩)
      (by rw [b1]; exact hface)
    · rw [add_smul_unitVec_apply]
      have hr' : (r : ℤ) ≤ n₃ := by exact_mod_cast hr
      rcases hcover l with rfl | rfl | rfl | rfl
      · rw [b1, if_neg hik, add_zero]
        exact hxl _
      · rw [a2, a1, ql _ hj3, if_neg hij.symm, if_pos rfl, if_neg hjk]
        have := hxl l
        omega
      · rw [a2, a1, ql _ hk3, if_neg hik.symm, if_neg hjk.symm, if_pos rfl]
        have := hxl l
        omega
      · rw [a2, a1, q3, if_neg hi3.symm, if_neg hj3.symm, if_neg hk3.symm]
        have := hle 3
        omega
    · rw [add_smul_unitVec_apply, if_neg hk3.symm, a2, a1, q3, if_neg hi3.symm, if_neg hj3.symm]
      omega
  have hb₁ : (n₁ : ℝ) ≤ M := by
    have : n₁ ≤ M := by
      have := hM i
      have := (hxl i).2
      omega
    exact_mod_cast this
  have hb₂ : (n₂ : ℝ) ≤ M := by
    have : n₂ ≤ M := by
      have := hM j
      have := (hxl j).2
      omega
    exact_mod_cast this
  have hb₃ : (n₃ : ℝ) ≤ M := by
    have : n₃ ≤ M := by
      have := hM k
      have := (hxl k).2
      omega
    exact_mod_cast this
  have t1 := quatDist_triangle (f q) (f p₁) (f x)
  have t2 := quatDist_triangle (f p₁) (f p₂) (f x)
  rw [← hlast] at t1 t2 ⊢
  nlinarith
theorem boundary_edge_cases (hb : ∀ i, lo i + 2 ≤ hi i) (a : Fin 4 → ℤ) (i : Fin 4) (ha : a ∈ boxBoundary lo hi)
    (ha' : a + unitVec i ∈ boxBoundary lo hi) :
    (InLowerPart lo hi a ∧ InLowerPart lo hi (a + unitVec i)) ∨
      (InTopFace lo hi a ∧ InTopFace lo hi (a + unitVec i) ∧ i ≠ 3) := by
  obtain ⟨hab, l, hl⟩ := ha
  obtain ⟨hab', l', hl'⟩ := ha'
  by_cases hi3 : i = 3
  · subst hi3
    left
    have e3 : (a + unitVec 3) 3 = a 3 + 1 := by simp [unitVec_self]
    have elt : ∀ m, m ≠ 3 → (a + unitVec 3) m = a m := fun m hm => by simp [unitVec_of_ne hm]
    have hlt : a 3 + 1 ≤ hi 3 := by
      have := (hab' 3).2
      rwa [e3] at this
    have hge : lo 3 ≤ a 3 := (hab 3).1
    have hb3 := hb 3
    have cupa : a 3 = lo 3 ∨ OnSideWall lo hi a := by
      by_cases hl3 : l = 3
      · subst hl3
        left
        omega
      · exact Or.inr ⟨l, hl3, hl⟩
    refine ⟨⟨hab, cupa⟩, hab', Or.inr ?_⟩
    by_cases hl3 : l' = 3
    · subst hl3
      rw [e3] at hl'
      have hh : a 3 + 1 = hi 3 := by omega
      rcases cupa with h0 | ⟨m, hm, hf⟩
      · omega
      · exact ⟨m, hm, by rw [elt m hm]; exact hf⟩
    · exact ⟨l', hl3, hl'⟩
  · have e3 : (a + unitVec i) 3 = a 3 := by simp [unitVec_of_ne (Ne.symm hi3)]
    by_cases hh : a 3 = hi 3
    · right
      exact ⟨⟨hab, hh⟩, ⟨hab', by rw [e3]; exact hh⟩, hi3⟩
    · left
      have c1 : InLowerPart lo hi a := by
        refine ⟨hab, ?_⟩
        by_cases hl3 : l = 3
        · subst hl3
          left
          tauto
        · exact Or.inr ⟨l, hl3, hl⟩
      have c2 : InLowerPart lo hi (a + unitVec i) := by
        refine ⟨hab', ?_⟩
        by_cases hl3 : l' = 3
        · subst hl3
          left
          rw [e3] at hl' ⊢
          tauto
        · exact Or.inr ⟨l', hl3, hl'⟩
      exact ⟨c1, c2⟩
end BoundaryGauge
open BoundaryGauge in
theorem flatGaugeOnBoxBoundary_holds : FlatGaugeOnBoxBoundary := by
  classical
  intro X lo hi M e hb he H
  have hM : ∀ i, hi i - lo i ≤ M := fun i => (hb i).2
  have hb2 : ∀ i, lo i + 2 ≤ hi i := fun i => (hb i).1
  have hle : ∀ i, lo i ≤ hi i := fun i => by have := hb2 i; omega
  have hM2 : (2 : ℝ) ≤ M := by
    have h1 := hb 0
    have : (2 : ℤ) ≤ M := by omega
    exact_mod_cast this
  have hMe : (0 : ℝ) ≤ M * e := by positivity
  have Hc : ∀ a μ ν, μ ≠ ν → a ∈ boxBoundary lo hi → a + unitVec μ ∈ boxBoundary lo hi →
      a + unitVec ν ∈ boxBoundary lo hi → a + unitVec μ + unitVec ν ∈ boxBoundary lo hi →
      plaquetteDefect X a μ ν ≤ e := fun a μ ν h h1 h2 h3 h4 => H a μ ν h h1 h2 h3 h4
  have faceH : ∀ c, (c = lo 3 ∨ c = hi 3) → ∀ a μ ν, μ ≠ 3 → ν ≠ 3 → μ ≠ ν → a 3 = c → a ∈ box lo hi →
      a + unitVec μ ∈ box lo hi → a + unitVec ν ∈ box lo hi →
      a + unitVec μ + unitVec ν ∈ box lo hi → plaquetteDefect X a μ ν ≤ e := by
    intro c hc a μ ν hμ hν hμν ha h1 h2 h3 h4
    have wall : ∀ b : Fin 4 → ℤ, b 3 = c → b ∈ box lo hi → b ∈ boxBoundary lo hi := fun b hb' hbb =>
      ⟨hbb, 3, by rw [hb']; exact hc⟩
    refine Hc a μ ν hμν (wall a ha h1) (wall _ ?_ h2) (wall _ ?_ h3) (wall _ ?_ h4)
    · simp [unitVec_of_ne (Ne.symm hμ), ha]
    · simp [unitVec_of_ne (Ne.symm hν), ha]
    · simp [unitVec_of_ne (Ne.symm hμ), unitVec_of_ne (Ne.symm hν), ha]
  obtain ⟨γb, hγb⟩ := exists_gauge_on_slice X lo hi M e hM he (lo 3) (faceH _ (Or.inl rfl))
  obtain ⟨γl, hγl⟩ := exists_gauge_on_slice X lo hi M e hM he (hi 3) (faceH _ (Or.inr rfl))
  set γc := transportedGauge X γb 3 (lo 3) with hγc
  have hcup := gaugeDefect_lowerPart_le X lo hi M e hM he Hc γb hγb (hle 3)
  let t : (Fin 4 → ℤ) → UnitQuaternion := fun x => γc x * (γl x)⁻¹
  have hstep : ∀ x j, j ≠ 3 → InTopFace lo hi x → InTopFace lo hi (x + unitVec j) → OnSideWall lo hi x →
      OnSideWall lo hi (x + unitVec j) → quatDist (t x) (t (x + unitVec j)) ≤ 5 * M * e := by
    intro x j hj l1 l2 f1 f2
    have h1 := hcup x j ⟨l1.1, Or.inr f1⟩ ⟨l2.1, Or.inr f2⟩
    have h2 := hγl x j hj l1.2 l1.1 l2.1
    have h3 := quatDist_mul_mul (γc x * X x j) (γl x * X x j)⁻¹ (γc (x + unitVec j))
      (γl (x + unitVec j))⁻¹
    rw [quatDist_inv] at h3
    have e1 : γc x * X x j * (γl x * X x j)⁻¹ = t x := by
      simp only [t]
      group
    rw [e1] at h3
    simp only [gaugeDefect] at h1 h2
    show quatDist (t x) (γc (x + unitVec j) * (γl (x + unitVec j))⁻¹) ≤ _
    linarith
  have hrim : ∀ x, InTopFace lo hi x → OnSideWall lo hi x →
      quatDist (t (Function.update lo 3 (hi 3))) (t x) ≤ 3 * M * (5 * M * e) := by
    intro x hx ⟨i, hi3, hf⟩
    have hd : (0 : ℝ) ≤ 5 * M * e := by positivity
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
      revert hi3
      fin_cases i <;> simp
    rcases hi' with rfl | rfl | rfl
    · exact quatDist_corner_le lo hi M hM hle t _ hd hstep 0 1 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x hx hf
    · exact quatDist_corner_le lo hi M hM hle t _ hd hstep 1 0 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x hx hf
    · exact quatDist_corner_le lo hi M hM hle t _ hd hstep 2 0 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x hx hf
  set c := t (Function.update lo 3 (hi 3)) with hc
  let γ : (Fin 4 → ℤ) → UnitQuaternion := fun x => if InLowerPart lo hi x then γc x else c * γl x
  have hbig : (M : ℝ) * e * 2 ≤ (M : ℝ) ^ 2 * e := by nlinarith
  have hcupγ : ∀ x, InLowerPart lo hi x → γ x = t x * γl x := by
    intro x hx
    simp only [γ, if_pos hx, t]
    group
  refine ⟨γ, fun a i ha ha' => ?_⟩
  have goal : gaugeDefect X γ a i ≤ 40 * (M : ℝ) ^ 2 * e := by
    have hcl := boundary_edge_cases lo hi hb2 a i ha ha'
    by_cases c1 : InLowerPart lo hi a
    · by_cases c2 : InLowerPart lo hi (a + unitVec i)
      · have h1 := hcup a i c1 c2
        simp only [gaugeDefect] at h1 ⊢
        simp only [γ, if_pos c1, if_pos c2]
        nlinarith
      · obtain ⟨l1, l2, hi3⟩ := hcl.resolve_left fun h => c2 h.2
        have hf : OnSideWall lo hi a := by
          rcases c1.2 with h0 | h0
          · have := hb2 3
            have := l1.2
            omega
          · exact h0
        have h1 := hrim a l1 hf
        have h2 := hγl a i hi3 l1.2 l1.1 l2.1
        simp only [gaugeDefect] at h2 ⊢
        have e1 : γ a * X a i = t a * (γl a * X a i) := by rw [hcupγ a c1, mul_assoc]
        have e2 : γ (a + unitVec i) = c * γl (a + unitVec i) := by simp only [γ, if_neg c2]
        rw [e1, e2]
        have h3 := quatDist_mul_mul (t a) (γl a * X a i) c (γl (a + unitVec i))
        rw [quatDist_comm] at h1
        nlinarith
    · by_cases c2 : InLowerPart lo hi (a + unitVec i)
      · obtain ⟨l1, l2, hi3⟩ := hcl.resolve_left fun h => c1 h.1
        have hf : OnSideWall lo hi (a + unitVec i) := by
          rcases c2.2 with h0 | h0
          · have := hb2 3
            have := l2.2
            omega
          · exact h0
        have h1 := hrim _ l2 hf
        have h2 := hγl a i hi3 l1.2 l1.1 l2.1
        simp only [gaugeDefect] at h2 ⊢
        have e1 : γ a * X a i = c * (γl a * X a i) := by simp only [γ, if_neg c1, mul_assoc]
        rw [e1, hcupγ _ c2]
        have h3 := quatDist_mul_mul c (γl a * X a i) (t (a + unitVec i)) (γl (a + unitVec i))
        nlinarith
      · obtain ⟨l1, l2, hi3⟩ := hcl.resolve_left fun h => c1 h.1
        have h2 := hγl a i hi3 l1.2 l1.1 l2.1
        simp only [gaugeDefect] at h2 ⊢
        have e1 : γ a * X a i = c * (γl a * X a i) := by simp only [γ, if_neg c1, mul_assoc]
        have e2 : γ (a + unitVec i) = c * γl (a + unitVec i) := by simp only [γ, if_neg c2]
        rw [e1, e2, quatDist_mul_left]
        nlinarith
  have e3 : ‖((γ a * X a i * (γ (a + unitVec i))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      quatDist (γ a * X a i * (γ (a + unitVec i))⁻¹) 1 := rfl
  rw [e3, quatDist_mul_inv_one]
  exact goal
end LatticeGauge
end YangMills.Construction
end
