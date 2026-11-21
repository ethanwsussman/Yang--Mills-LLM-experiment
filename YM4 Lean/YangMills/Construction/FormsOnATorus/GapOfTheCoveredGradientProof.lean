import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.LawOnABoxOfTheFlow.GapOfTheCoveredGradient
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion ColdStepAtMirrorFrames
open BlockAverages hiding unitStep adjointAction
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
private theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
private theorem spectralGap_along {X : Type} [Fintype X] [AddCommGroup X] (e : X) (f φ : X → ℝ) (B : Finset X)
    (lam : ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) (hpos : ∀ x ∈ B, 0 < φ x)
    (hup : ∀ x ∈ B, 0 ≤ φ (x + e)) (hdn : ∀ x ∈ B, 0 ≤ φ (x - e))
    (hsum : ∀ x ∈ B, φ (x + e) + φ (x - e) ≤ (2 - lam) * φ x) :
    lam * ∑ x, f x ^ 2 ≤ ∑ x, (f x - f (x + e)) ^ 2 := by
  classical
  set ρ : X → ℝ := fun x => if x ∈ B then φ (x + e) / φ x else 0 with hρdef
  set σ : X → ℝ := fun x => if x ∈ B then φ (x - e) / φ x else 0 with hσdef
  have hρ : ∀ x, 0 ≤ ρ x := by
    intro x
    by_cases hx : x ∈ B
    · simp only [hρdef, if_pos hx]
      exact div_nonneg (hup x hx) (hpos x hx).le
    · simp [hρdef, if_neg hx]
  have hσ : ∀ x, 0 ≤ σ x := by
    intro x
    by_cases hx : x ∈ B
    · simp only [hσdef, if_pos hx]
      exact div_nonneg (hdn x hx) (hpos x hx).le
    · simp [hσdef, if_neg hx]
  have edge : ∀ x, 2 * (f x * f (x + e)) ≤ f x ^ 2 * ρ x + f (x + e) ^ 2 * σ (x + e) := by
    intro x
    by_cases hx : x ∈ B
    · by_cases hy : x + e ∈ B
      · simp only [hρdef, hσdef, if_pos hx, if_pos hy, add_sub_cancel_right]
        have h1 := hpos x hx
        have h2 := hpos _ hy
        have h3 : f x ^ 2 * (φ (x + e) / φ x) + f (x + e) ^ 2 * (φ x / φ (x + e)) - 2 * (f x * f (x + e))
            = (f x * φ (x + e) - f (x + e) * φ x) ^ 2 / (φ x * φ (x + e)) := by
          field_simp
          ring
        have h4 : 0 ≤ (f x * φ (x + e) - f (x + e) * φ x) ^ 2 / (φ x * φ (x + e)) := by positivity
        linarith
      · rw [hf _ hy]
        have := mul_nonneg (sq_nonneg (f x)) (hρ x)
        have := hσ (x + e)
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
        linarith
    · rw [hf _ hx]
      have := mul_nonneg (sq_nonneg (f (x + e))) (hσ (x + e))
      have := hρ x
      simp only [zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
      linarith
  have shiftσ : ∑ x, f (x + e) ^ 2 * σ (x + e) = ∑ x, f x ^ 2 * σ x :=
    Equiv.sum_comp (Equiv.addRight e) (fun x => f x ^ 2 * σ x)
  have shiftf : ∑ x, f (x + e) ^ 2 = ∑ x, f x ^ 2 :=
    Equiv.sum_comp (Equiv.addRight e) (fun x => f x ^ 2)
  have pt : ∀ x, f x ^ 2 * ρ x + f x ^ 2 * σ x ≤ (2 - lam) * f x ^ 2 := by
    intro x
    by_cases hx : x ∈ B
    · simp only [hρdef, hσdef, if_pos hx]
      have h1 := hpos x hx
      have h2 : φ (x + e) / φ x + φ (x - e) / φ x ≤ 2 - lam := by
        rw [← add_div, div_le_iff₀ h1]
        exact hsum x hx
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (f x))
      linarith
    · rw [hf _ hx]
      simp
  have key : ∑ x, 2 * (f x * f (x + e)) ≤ (2 - lam) * ∑ x, f x ^ 2 := by
    calc ∑ x, 2 * (f x * f (x + e))
        ≤ ∑ x, (f x ^ 2 * ρ x + f (x + e) ^ 2 * σ (x + e)) := Finset.sum_le_sum fun x _ => edge x
      _ = ∑ x, (f x ^ 2 * ρ x + f x ^ 2 * σ x) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, shiftσ]
      _ ≤ ∑ x, (2 - lam) * f x ^ 2 := Finset.sum_le_sum fun x _ => pt x
      _ = (2 - lam) * ∑ x, f x ^ 2 := by rw [Finset.mul_sum]
  have expand : ∑ x, (f x - f (x + e)) ^ 2
      = ∑ x, f x ^ 2 + ∑ x, f (x + e) ^ 2 - ∑ x, 2 * (f x * f (x + e)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [expand, shiftf]
  linarith
private theorem maximumPrinciple {X : Type} [Finite X] [Nonempty X] (B : Finset X) (f u c : X → ℝ)
    (s s' : Fin 4 → X → X)
    (hf : ∀ x, x ∉ B → f x = 0) (hu : ∀ x, 0 ≤ u x)
    (sub : ∀ w ∈ B, 8 * f w ≤ c w + ∑ i, (f (s i w) + f (s' i w)))
    (sup : ∀ w ∈ B, c w + ∑ i, (u (s i w) + u (s' i w)) < 8 * u w) :
    ∀ w, f w ≤ u w := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (fun x => f x - u x)
  by_cases h0 : f w₀ - u w₀ ≤ 0
  · intro w
    have := hw₀ w
    linarith
  · exfalso
    have hB : w₀ ∈ B := by
      by_contra hB
      apply h0
      rw [hf _ hB]
      linarith [hu w₀]
    have h1 := sub w₀ hB
    have h2 := sup w₀ hB
    have h3 : ∑ i, ((f (s i w₀) - u (s i w₀)) + (f (s' i w₀) - u (s' i w₀))) ≤ 8 * (f w₀ - u w₀) := by
      simp only [Fin.sum_univ_four]
      have a0 := hw₀ (s 0 w₀)
      have a1 := hw₀ (s 1 w₀)
      have a2 := hw₀ (s 2 w₀)
      have a3 := hw₀ (s 3 w₀)
      have b0 := hw₀ (s' 0 w₀)
      have b1 := hw₀ (s' 1 w₀)
      have b2 := hw₀ (s' 2 w₀)
      have b3 := hw₀ (s' 3 w₀)
      linarith
    simp only [Fin.sum_univ_four] at h1 h2 h3
    linarith
private theorem inv_pair_le (E t P : ℝ) (hE : 0 < E) (hp : 0 < E + 2 * t) (hm : 0 < E - 2 * t) (hP : 0 < P)
    (hPQ : P ≤ E ^ 2 - 4 * t ^ 2) :
    1 / (E + 2 * t) + 1 / (E - 2 * t) ≤ 2 / E + 8 * t ^ 2 / (E * P) := by
  have h1 : 1 / (E + 2 * t) + 1 / (E - 2 * t) = 2 / E + 8 * t ^ 2 / (E * ((E + 2 * t) * (E - 2 * t))) := by
    field_simp
    ring
  rw [h1]
  have h2 : P ≤ (E + 2 * t) * (E - 2 * t) := by nlinarith
  have h3 : 8 * t ^ 2 / (E * ((E + 2 * t) * (E - 2 * t))) ≤ 8 * t ^ 2 / (E * P) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left h2 hE.le)
  linarith
private theorem inverseQuadratic_superharmonic (t : Fin 4 → ℝ) :
    ∑ i, (1 / (3 + ∑ j, t j ^ 2 + 1 + 2 * t i) + 1 / (3 + ∑ j, t j ^ 2 + 1 - 2 * t i))
      < 8 / (3 + ∑ j, t j ^ 2) := by
  set S : ℝ := ∑ j, t j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : ∀ i, t i ^ 2 ≤ S := fun i =>
    Finset.single_le_sum (f := fun j => t j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  set D : ℝ := 3 + S with hD
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < D + 1 := by linarith
  set P : ℝ := (D + 1) ^ 2 - 4 * S with hPdef
  have hP0 : 0 < P := by
    have : P = (S + 2) ^ 2 + 12 := by
      rw [hPdef, hD]
      ring
    rw [this]
    positivity
  have term : ∀ i, 1 / (D + 1 + 2 * t i) + 1 / (D + 1 - 2 * t i)
      ≤ 2 / (D + 1) + 8 * t i ^ 2 / ((D + 1) * P) := by
    intro i
    have hi := hle i
    refine inv_pair_le (D + 1) (t i) P hE0 ?_ ?_ hP0 ?_
    · nlinarith [sq_nonneg (t i + 1)]
    · nlinarith [sq_nonneg (t i - 1)]
    · rw [hPdef]
      linarith
  have hsum : ∑ i, (1 / (D + 1 + 2 * t i) + 1 / (D + 1 - 2 * t i))
      ≤ 8 / (D + 1) + 8 * S / ((D + 1) * P) := by
    calc ∑ i, (1 / (D + 1 + 2 * t i) + 1 / (D + 1 - 2 * t i))
        ≤ ∑ i, (2 / (D + 1) + 8 * t i ^ 2 / ((D + 1) * P)) := Finset.sum_le_sum fun i _ => term i
      _ = 8 / (D + 1) + 8 * S / ((D + 1) * P) := by
          rw [hS]
          simp only [Fin.sum_univ_four]
          ring
  have hgap : 8 / D - (8 / (D + 1) + 8 * S / ((D + 1) * P)) = 8 * (D + 13) / (D * (D + 1) * P) := by
    have hSD : S = D - 3 := by rw [hD]; ring
    have hPD : P = (D + 1) ^ 2 - 4 * (D - 3) := by rw [hPdef, hSD]
    rw [hSD]
    field_simp
    rw [hPD]
    ring
  have hpos : 0 < 8 * (D + 13) / (D * (D + 1) * P) := by positivity
  linarith
variable {n : ℕ} [NeZero n]
private def offsetCoord (c x : TorusSite n) (i : Fin 4) : ℤ := ((x - c) i).valMinAbs
private theorem valMinAbs_add_one (x : ZMod n) (m : ℤ) (hx : |x.valMinAbs| ≤ m) (hn : 2 * (m + 1) < n) :
    (x + 1).valMinAbs = x.valMinAbs + 1 := by
  rw [ZMod.valMinAbs_spec]
  have h := abs_le.1 hx
  refine ⟨by simp, Set.mem_Ioc.2 ⟨by omega, by omega⟩⟩
private theorem valMinAbs_sub_one (x : ZMod n) (m : ℤ) (hx : |x.valMinAbs| ≤ m) (hn : 2 * (m + 1) < n) :
    (x - 1).valMinAbs = x.valMinAbs - 1 := by
  rw [ZMod.valMinAbs_spec]
  have h := abs_le.1 hx
  refine ⟨by simp, Set.mem_Ioc.2 ⟨by omega, by omega⟩⟩
private theorem offsetCoord_add (c x : TorusSite n) (j i : Fin 4) (m : ℤ) (h : |offsetCoord c x i| ≤ m)
    (hn : 2 * (m + 1) < n) :
    offsetCoord c (x + unitStep n j) i = offsetCoord c x i + if i = j then 1 else 0 := by
  unfold offsetCoord at *
  by_cases hij : i = j
  · subst hij
    have h1 : (x + unitStep n i - c) i = (x - c) i + 1 := by
      simp [unitStep]
      ring
    rw [h1, if_pos rfl]
    exact valMinAbs_add_one _ m h hn
  · have h1 : (x + unitStep n j - c) i = (x - c) i := by
      simp [unitStep, Pi.single_eq_of_ne hij]
    rw [h1, if_neg hij, add_zero]
private theorem offsetCoord_sub (c x : TorusSite n) (j i : Fin 4) (m : ℤ) (h : |offsetCoord c x i| ≤ m)
    (hn : 2 * (m + 1) < n) :
    offsetCoord c (x - unitStep n j) i = offsetCoord c x i - if i = j then 1 else 0 := by
  unfold offsetCoord at *
  by_cases hij : i = j
  · subst hij
    have h1 : (x - unitStep n i - c) i = (x - c) i - 1 := by
      simp [unitStep]
      ring
    rw [h1, if_pos rfl]
    exact valMinAbs_sub_one _ m h hn
  · have h1 : (x - unitStep n j - c) i = (x - c) i := by
      simp [unitStep, Pi.single_eq_of_ne hij]
    rw [h1, if_neg hij, sub_zero]
private theorem mem_supBall_iff (o z : TorusSite n) (R : ℕ) :
    z ∈ supBall o (R : ℝ) ↔ ∀ i, |offsetCoord o z i| ≤ (R : ℤ) := by
  unfold supBall
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_le]
  unfold supDist
  rw [Finset.sup_le_iff]
  constructor
  · intro h i
    have := h i (Finset.mem_univ i)
    unfold offsetCoord
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  · intro h i _
    have := h i
    unfold offsetCoord at this
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
private theorem abs_offsetCoord_le_of_mem (o z w : TorusSite n) (R : ℕ) (hz : z ∈ supBall o (R : ℝ))
    (hw : w ∈ supBall o (R : ℝ)) (j : Fin 4) : |offsetCoord z w j| ≤ 2 * (R : ℤ) := by
  have h1 := (mem_supBall_iff o z R).1 hz j
  have h2 := (mem_supBall_iff o w R).1 hw j
  unfold offsetCoord at *
  have e : (w - z) j = (w - o) j + -((z - o) j) := by
    simp
  rw [Int.abs_eq_natAbs] at h1 h2 ⊢
  rw [e]
  have h3 := ZMod.natAbs_valMinAbs_add_le ((w - o) j) (-((z - o) j))
  have h4 := Int.natAbs_add_le ((w - o) j).valMinAbs (-((z - o) j)).valMinAbs
  rw [ZMod.natAbs_valMinAbs_neg ((z - o) j)] at h4
  omega
private def quadraticWeight (z w : TorusSite n) : ℝ := 3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2
private theorem quadraticWeight_add (z w : TorusSite n) (i : Fin 4) (m : ℤ) (h : ∀ j, |offsetCoord z w j| ≤ m)
    (hn : 2 * (m + 1) < n) :
    quadraticWeight z (w + unitStep n i)
      = 3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2 + 1 + 2 * (offsetCoord z w i : ℝ) := by
  unfold quadraticWeight
  have h1 : ∀ j, (offsetCoord z (w + unitStep n i) j : ℝ) ^ 2
      = (offsetCoord z w j : ℝ) ^ 2 + if j = i then 1 + 2 * (offsetCoord z w i : ℝ) else 0 := by
    intro j
    rw [offsetCoord_add z w i j m (h j) hn]
    split_ifs with hij
    · subst hij
      push_cast
      ring
    · simp
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private theorem quadraticWeight_sub (z w : TorusSite n) (i : Fin 4) (m : ℤ) (h : ∀ j, |offsetCoord z w j| ≤ m)
    (hn : 2 * (m + 1) < n) :
    quadraticWeight z (w - unitStep n i)
      = 3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2 + 1 - 2 * (offsetCoord z w i : ℝ) := by
  unfold quadraticWeight
  have h1 : ∀ j, (offsetCoord z (w - unitStep n i) j : ℝ) ^ 2
      = (offsetCoord z w j : ℝ) ^ 2 + if j = i then 1 - 2 * (offsetCoord z w i : ℝ) else 0 := by
    intro j
    rw [offsetCoord_sub z w i j m (h j) hn]
    split_ifs with hij
    · subst hij
      push_cast
      ring
    · simp
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
omit [NeZero n] in
private theorem three_le_quadraticWeight (z w : TorusSite n) : 3 ≤ quadraticWeight z w := by
  unfold quadraticWeight
  have : 0 ≤ ∑ j, (offsetCoord z w j : ℝ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith
private theorem covariantGrad_gap_along (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 8 * R < n)
    (A : TorusBond n → imaginaryQuaternions)
    (χ : TorusSite n → imaginaryQuaternions) (hχ : ∀ z, z ∉ supBall o (R : ℝ) → χ z = 0) (i : Fin 4) :
    ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ x, ‖χ x‖ ^ 2 ≤ ∑ x, ‖covariantGrad A χ (x, i)‖ ^ 2 := by
  have hn' : 2 * ((R : ℤ) + 1) < (n : ℤ) := by omega
  have hlam : ((R : ℝ) + 1)⁻¹ ^ 2 * ((R : ℝ) + 1) ^ 2 = 1 := by
    field_simp
  have hlam0 : 0 ≤ ((R : ℝ) + 1)⁻¹ ^ 2 := sq_nonneg _
  have bounds : ∀ x ∈ supBall o (R : ℝ), -(R : ℝ) ≤ (offsetCoord o x i : ℝ) ∧ (offsetCoord o x i : ℝ) ≤ R := by
    intro x hx
    have h := abs_le.1 ((mem_supBall_iff o x R).1 hx i)
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have up : ∀ x ∈ supBall o (R : ℝ),
      (offsetCoord o (x + unitStep n i) i : ℝ) = (offsetCoord o x i : ℝ) + 1 := by
    intro x hx
    rw [offsetCoord_add o x i i R ((mem_supBall_iff o x R).1 hx i) hn', if_pos rfl]
    push_cast
    ring
  have dn : ∀ x ∈ supBall o (R : ℝ),
      (offsetCoord o (x - unitStep n i) i : ℝ) = (offsetCoord o x i : ℝ) - 1 := by
    intro x hx
    rw [offsetCoord_sub o x i i R ((mem_supBall_iff o x R).1 hx i) hn', if_pos rfl]
    push_cast
    ring
  have h1 := spectralGap_along (unitStep n i) (fun x => ‖χ x‖)
    (fun x => ((R : ℝ) + 1) ^ 2 - (offsetCoord o x i : ℝ) ^ 2)
    (supBall o (R : ℝ)) (((R : ℝ) + 1)⁻¹ ^ 2)
    (fun x hx => by simp [hχ x hx])
    (fun x hx => by
      obtain ⟨b1, b2⟩ := bounds x hx
      have : ((R : ℝ) + 1) ^ 2 - (offsetCoord o x i : ℝ) ^ 2
          = ((R : ℝ) + 1 - offsetCoord o x i) * ((R : ℝ) + 1 + offsetCoord o x i) := by ring
      simp only [this]
      exact mul_pos (by linarith) (by linarith))
    (fun x hx => by
      obtain ⟨b1, b2⟩ := bounds x hx
      simp only [up x hx]
      have : ((R : ℝ) + 1) ^ 2 - ((offsetCoord o x i : ℝ) + 1) ^ 2
          = ((R : ℝ) - offsetCoord o x i) * ((R : ℝ) + 2 + offsetCoord o x i) := by ring
      rw [this]
      exact mul_nonneg (by linarith) (by linarith))
    (fun x hx => by
      obtain ⟨b1, b2⟩ := bounds x hx
      simp only [dn x hx]
      have : ((R : ℝ) + 1) ^ 2 - ((offsetCoord o x i : ℝ) - 1) ^ 2
          = ((R : ℝ) + offsetCoord o x i) * ((R : ℝ) + 2 - offsetCoord o x i) := by ring
      rw [this]
      exact mul_nonneg (by linarith) (by linarith))
    (fun x hx => by
      simp only [up x hx, dn x hx]
      have h2 : ((R : ℝ) + 1)⁻¹ ^ 2 * (((R : ℝ) + 1) ^ 2 - (offsetCoord o x i : ℝ) ^ 2) ≤ 2 := by
        have := mul_nonneg hlam0 (sq_nonneg (offsetCoord o x i : ℝ))
        rw [mul_sub, hlam]
        linarith
      nlinarith)
  refine h1.trans (Finset.sum_le_sum fun x _ => ?_)
  have h2 := abs_norm_sub_norm_le (χ x) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (x, i))) (χ (x + unitStep n i)))
  rw [norm_adjointAction] at h2
  have h3 : |‖χ x‖ - ‖χ (x + unitStep n i)‖| ≤ |‖covariantGrad A χ (x, i)‖| := by
    rw [abs_norm]
    exact h2
  exact sq_le_sq.2 h3
private theorem covariantGrad_weak_form_at (A : TorusBond n → imaginaryQuaternions)
    (χ : TorusSite n → imaginaryQuaternions) (w : TorusSite n) (Y : imaginaryQuaternions) :
    ∑ b : TorusBond n, inner ℝ (covariantGrad A χ b) (covariantGrad A (fun x => if x = w then Y else 0) b)
      = ∑ i : Fin 4, (inner ℝ (covariantGrad A χ (w, i)) Y -
          inner ℝ (covariantGrad A χ (w - unitStep n i, i))
            (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) Y)) := by
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ x : TorusSite n,
      inner ℝ (covariantGrad A χ (x, i)) (covariantGrad A (fun x => if x = w then Y else 0) (x, i))
        = (if x = w then inner ℝ (covariantGrad A χ (x, i)) Y else 0) -
          (if x = w - unitStep n i then
            inner ℝ (covariantGrad A χ (x, i)) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (x, i))) Y) else 0) := by
    intro x
    show inner ℝ (covariantGrad A χ (x, i))
      ((if x = w then Y else 0) - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (x, i))) (if x + unitStep n i = w then Y else 0)) = _
    rw [inner_sub_right]
    congr 1
    · split_ifs <;> simp
    · have hiff : x + unitStep n i = w ↔ x = w - unitStep n i := eq_sub_iff_add_eq.symm
      by_cases h : x = w - unitStep n i
      · rw [if_pos h, if_pos (hiff.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.1 h')), adjointAction_zero, inner_zero_right]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
private theorem norm_isSubsolution (A : TorusBond n → imaginaryQuaternions)
    (χ : TorusSite n → imaginaryQuaternions) (z : TorusSite n) (X : imaginaryQuaternions)
    (B : Finset (TorusSite n))
    (H : ∀ ψ : TorusSite n → imaginaryQuaternions, (∀ z', z' ∉ B → ψ z' = 0) →
      ∑ b : TorusBond n, inner ℝ (covariantGrad A χ b) (covariantGrad A ψ b) = inner ℝ X (ψ z)) :
    ∀ w ∈ B, 8 * ‖χ w‖ ≤ (if w = z then ‖X‖ else 0) + ∑ i, (‖χ (w + unitStep n i)‖ + ‖χ (w - unitStep n i)‖) := by
  intro w hw
  have eq0 := H (fun x => if x = w then χ w else 0) (fun z' hz' => if_neg (by rintro rfl; exact hz' hw))
  rw [covariantGrad_weak_form_at] at eq0
  have eq1 : ∑ i : Fin 4, (inner ℝ (covariantGrad A χ (w, i)) (χ w) -
      inner ℝ (covariantGrad A χ (w - unitStep n i, i))
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w)))
      = inner ℝ X (if z = w then χ w else 0) := eq0
  have term : ∀ i : Fin 4, 2 * ‖χ w‖ ^ 2 - ‖χ w‖ * (‖χ (w + unitStep n i)‖ + ‖χ (w - unitStep n i)‖)
      ≤ inner ℝ (covariantGrad A χ (w, i)) (χ w) -
        inner ℝ (covariantGrad A χ (w - unitStep n i, i))
          (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w)) := by
    intro i
    have a1 : inner ℝ (covariantGrad A χ (w, i)) (χ w)
        = ‖χ w‖ ^ 2 - inner ℝ (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w, i))) (χ (w + unitStep n i))) (χ w) := by
      show inner ℝ (χ w - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w, i))) (χ (w + unitStep n i))) (χ w) = _
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have a2 : inner ℝ (covariantGrad A χ (w - unitStep n i, i))
          (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w))
        = inner ℝ (χ (w - unitStep n i)) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w))
          - ‖χ w‖ ^ 2 := by
      show inner ℝ (χ (w - unitStep n i) - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i)))
          (χ (w - unitStep n i + unitStep n i)))
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w)) = _
      rw [sub_add_cancel, inner_sub_left, real_inner_self_eq_norm_sq, norm_adjointAction]
    have a3 := real_inner_le_norm (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w, i))) (χ (w + unitStep n i))) (χ w)
    rw [norm_adjointAction] at a3
    have a4 := real_inner_le_norm (χ (w - unitStep n i))
      (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A (w - unitStep n i, i))) (χ w))
    rw [norm_adjointAction] at a4
    rw [a1, a2]
    nlinarith [a3, a4]
  have hsum : 8 * ‖χ w‖ ^ 2 - ‖χ w‖ * ∑ i, (‖χ (w + unitStep n i)‖ + ‖χ (w - unitStep n i)‖)
      ≤ inner ℝ X (if z = w then χ w else 0) := by
    rw [← eq1]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => term i)
    simp only [Fin.sum_univ_four] at h ⊢
    linarith
  have hrhs : inner ℝ X (if z = w then χ w else 0) ≤ (if w = z then ‖X‖ else 0) * ‖χ w‖ := by
    by_cases hwz : w = z
    · rw [if_pos hwz.symm, if_pos hwz]
      exact real_inner_le_norm _ _
    · rw [if_neg (Ne.symm hwz), if_neg hwz, inner_zero_right, zero_mul]
  have hnn : 0 ≤ (if w = z then ‖X‖ else 0) + ∑ i, (‖χ (w + unitStep n i)‖ + ‖χ (w - unitStep n i)‖) := by
    refine add_nonneg ?_ (Finset.sum_nonneg fun i _ => by positivity)
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  by_cases h0 : ‖χ w‖ = 0
  · rw [h0]
    simpa using hnn
  · have hpos : 0 < ‖χ w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [hsum, hrhs]
private theorem norm_le_of_pointSource (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 8 * R < n)
    (A : TorusBond n → imaginaryQuaternions)
    (χ : TorusSite n → imaginaryQuaternions) (z : TorusSite n) (X : imaginaryQuaternions)
    (hχ : ∀ z', z' ∉ supBall o (R : ℝ) → χ z' = 0)
    (hz : z ∈ supBall o (R : ℝ))
    (H : ∀ ψ : TorusSite n → imaginaryQuaternions, (∀ z', z' ∉ supBall o (R : ℝ) → ψ z' = 0) →
      ∑ b : TorusBond n, inner ℝ (covariantGrad A χ b) (covariantGrad A ψ b) = inner ℝ X (ψ z))
    (z' : TorusSite n) : ‖χ z'‖ ≤ ‖X‖ := by
  have hn' : 2 * (2 * (R : ℤ) + 1) < (n : ℤ) := by omega
  have sub := norm_isSubsolution A χ z X (supBall o (R : ℝ)) H
  apply le_of_forall_pos_le_add
  intro ε hε
  set K : ℝ := 3 / 2 * (‖X‖ + ε) with hKdef
  have hK : 0 < K := by
    have := norm_nonneg X
    rw [hKdef]
    positivity
  have hden : ∀ w, 0 < quadraticWeight z w := fun w => by linarith [three_le_quadraticWeight z w]
  have sup : ∀ w ∈ supBall o (R : ℝ),
      (if w = z then ‖X‖ else 0) +
        ∑ i, (K * (1 / quadraticWeight z (w + unitStep n i)) + K * (1 / quadraticWeight z (w - unitStep n i)))
        < 8 * (K * (1 / quadraticWeight z w)) := by
    intro w hw
    have hb : ∀ j, |offsetCoord z w j| ≤ 2 * (R : ℤ) := abs_offsetCoord_le_of_mem o z w R hz hw
    have eS : ∑ i, (K * (1 / quadraticWeight z (w + unitStep n i)) +
          K * (1 / quadraticWeight z (w - unitStep n i)))
        = K * ∑ i, (1 / (3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2 + 1 + 2 * (offsetCoord z w i : ℝ)) +
            1 / (3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2 + 1 - 2 * (offsetCoord z w i : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [quadraticWeight_add z w i _ hb hn', quadraticWeight_sub z w i _ hb hn']
      ring
    rw [eS]
    by_cases hwz : w = z
    · subst hwz
      have h0 : ∀ j, (offsetCoord w w j : ℝ) = 0 := by
        intro j
        simp [offsetCoord]
      have hd : quadraticWeight w w = 3 := by
        simp [quadraticWeight, h0]
      have hs : ∑ i, (1 / (3 + ∑ j, (offsetCoord w w j : ℝ) ^ 2 + 1 + 2 * (offsetCoord w w i : ℝ)) +
          1 / (3 + ∑ j, (offsetCoord w w j : ℝ) ^ 2 + 1 - 2 * (offsetCoord w w i : ℝ))) = 2 := by
        simp only [h0]
        norm_num [Fin.sum_univ_four]
      rw [if_pos rfl, hd, hs]
      linarith
    · rw [if_neg hwz, zero_add]
      have hs := inverseQuadratic_superharmonic (fun j => (offsetCoord z w j : ℝ))
      have e8 : 8 * (K * (1 / quadraticWeight z w)) = K * (8 / (3 + ∑ j, (offsetCoord z w j : ℝ) ^ 2)) := by
        unfold quadraticWeight
        ring
      rw [e8]
      exact mul_lt_mul_of_pos_left hs hK
  have hbnd := maximumPrinciple (X := TorusSite n) (supBall o (R : ℝ)) (fun w => ‖χ w‖)
    (fun w => K * (1 / quadraticWeight z w))
    (fun w => if w = z then ‖X‖ else 0) (fun i w => w + unitStep n i) (fun i w => w - unitStep n i)
    (fun x hx => by simp [hχ x hx])
    (fun x => by have := hden x; positivity) sub sup
  have h1 : ‖χ z'‖ ≤ K * (1 / quadraticWeight z z') := hbnd z'
  have h2 : 1 / quadraticWeight z z' ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (three_le_quadraticWeight z z')
  have h3 : K * (1 / quadraticWeight z z') ≤ K * (1 / 3) := mul_le_mul_of_nonneg_left h2 hK.le
  linarith
theorem covariantGradientGap : covariantGradientGapStatement := by
  intro n _ o R hR hn A
  refine ⟨fun χ hχ => ?_, fun χ z X hχ hz H z' => norm_le_of_pointSource o R hR hn A χ z X hχ hz H z'⟩
  rw [Fintype.sum_prod_type_right]
  calc 4 * ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusSite n, ‖χ z‖ ^ 2
      = ∑ _i : Fin 4, ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusSite n, ‖χ z‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ i : Fin 4, ∑ x : TorusSite n, ‖covariantGrad A χ (x, i)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => covariantGrad_gap_along o R hR hn A χ hχ i
end YangMills.Construction.BoxGaussian
end
