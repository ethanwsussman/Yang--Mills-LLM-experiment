import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Finset
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
structure EdgeGrid (G J : Type) [AddCommGroup G] where
  dir : J → G
  mark : J → G → ℝ
  mark_cases : ∀ j k, mark j k = 0 ∨ mark j k = 1
  mark_add_dir : ∀ i j k, i ≠ j → mark i (k + dir j) = mark i k
variable {G J : Type} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
namespace EdgeGrid
variable (L : EdgeGrid G J) (V : G → ℝ)
def siteMass (k : G) : ℝ := Real.exp (- V k)
def edgeWeight (j : J) (k : G) : ℝ := Real.exp (-(V k + V (k + L.dir j)) / 2)
def diff (u : G → ℝ) (j : J) (k : G) : ℝ := u (k + L.dir j) - u k
def fwd (u : G → ℝ) (j : J) (k : G) : ℝ := L.mark j k * L.diff u j k
def bwd (u : G → ℝ) (j : J) (k : G) : ℝ := L.fwd u j (k - L.dir j)
def flux (u : G → ℝ) (j : J) (k : G) : ℝ :=
  L.edgeWeight V j (k - L.dir j) * L.bwd u j k - L.edgeWeight V j k * L.fwd u j k
omit [Fintype J] [DecidableEq J] in
theorem sum_add_const_eq {M : Type} [AddCommMonoid M] (F : G → M) (c : G) :
    ∑ k, F (k + c) = ∑ k, F k :=
  Equiv.sum_comp (Equiv.addRight c) F
omit [Fintype G] [Fintype J] [DecidableEq J] in
theorem siteMass_pos (k : G) : 0 < siteMass V k := Real.exp_pos _
omit [Fintype G] [Fintype J] [DecidableEq J] in
theorem edgeWeight_pos (j : J) (k : G) : 0 < L.edgeWeight V j k := Real.exp_pos _
omit [Fintype G] [Fintype J] [DecidableEq J] in
theorem edgeWeight_sq (j : J) (k : G) : L.edgeWeight V j k ^ 2 = siteMass V k * siteMass V (k + L.dir j) := by
  unfold edgeWeight siteMass
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring
omit [Fintype G] [Fintype J] [DecidableEq J] in
theorem edgeWeight_le (j : J) (k : G) : L.edgeWeight V j k ≤ (siteMass V k + siteMass V (k + L.dir j)) / 2 := by
  have h := L.edgeWeight_sq V j k
  have h1 := L.edgeWeight_pos V j k
  have h2 := siteMass_pos V k
  have h3 := siteMass_pos V (k + L.dir j)
  nlinarith [sq_nonneg (siteMass V k - siteMass V (k + L.dir j)), sq_nonneg (L.edgeWeight V j k - (siteMass V k + siteMass V (k + L.dir j)) / 2)]
theorem sum_flux_mul (u v : G → ℝ) (j : J) :
    ∑ k, L.flux V u j k * v k = ∑ k, L.edgeWeight V j k * L.fwd u j k * L.diff v j k := by
  have h1 : ∑ k, L.edgeWeight V j (k - L.dir j) * L.bwd u j k * v k
      = ∑ k, L.edgeWeight V j k * L.fwd u j k * v (k + L.dir j) := by
    rw [← sum_add_const_eq (fun k => L.edgeWeight V j (k - L.dir j) * L.bwd u j k * v k) (L.dir j)]
    simp [bwd]
  calc ∑ k, L.flux V u j k * v k
      = ∑ k, L.edgeWeight V j (k - L.dir j) * L.bwd u j k * v k - ∑ k, L.edgeWeight V j k * L.fwd u j k * v k := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by unfold flux; ring
    _ = _ := by
        rw [h1, ← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by unfold diff; ring
def diagWeight (j : J) (x : G) : ℝ := Real.exp (-(V (x + L.dir j) + V (x - L.dir j)) / 2)
omit [Fintype G] [Fintype J] [DecidableEq J] in
theorem diagWeight_pos (j : J) (x : G) : 0 < L.diagWeight V j x := Real.exp_pos _
theorem sum_flux_sq_div (u : G → ℝ) (j : J) :
    ∑ x, L.flux V u j x ^ 2 / siteMass V x = ∑ x, (siteMass V x * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2)
      - 2 * L.diagWeight V j x * (L.fwd u j x * L.bwd u j x)) := by
  have key : ∀ x, L.flux V u j x ^ 2 / siteMass V x = siteMass V (x - L.dir j) * L.bwd u j x ^ 2
      + siteMass V (x + L.dir j) * L.fwd u j x ^ 2 - 2 * L.diagWeight V j x * (L.fwd u j x * L.bwd u j x) := by
    intro x
    have hp := (siteMass_pos V x).ne'
    have h1 := L.edgeWeight_sq V j x
    have h2 := L.edgeWeight_sq V j (x - L.dir j)
    rw [sub_add_cancel] at h2
    have h3 : L.edgeWeight V j (x - L.dir j) * L.edgeWeight V j x = L.diagWeight V j x * siteMass V x := by
      unfold edgeWeight diagWeight siteMass
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [sub_add_cancel]
      ring
    unfold flux
    rw [div_eq_iff hp]
    have : (L.edgeWeight V j (x - L.dir j) * L.bwd u j x - L.edgeWeight V j x * L.fwd u j x) ^ 2
        = L.edgeWeight V j (x - L.dir j) ^ 2 * L.bwd u j x ^ 2 + L.edgeWeight V j x ^ 2 * L.fwd u j x ^ 2
          - 2 * (L.edgeWeight V j (x - L.dir j) * L.edgeWeight V j x) * (L.fwd u j x * L.bwd u j x) := by ring
    rw [this, h1, h2, h3]
    ring
  have s1 : ∑ x, siteMass V (x + L.dir j) * L.fwd u j x ^ 2 = ∑ x, siteMass V x * L.bwd u j x ^ 2 := by
    rw [← sum_add_const_eq (fun x => siteMass V x * L.bwd u j x ^ 2) (L.dir j)]
    simp [bwd]
  have s2 : ∑ x, siteMass V (x - L.dir j) * L.bwd u j x ^ 2 = ∑ x, siteMass V x * L.fwd u j x ^ 2 := by
    rw [← sum_add_const_eq (fun x => siteMass V (x - L.dir j) * L.bwd u j x ^ 2) (L.dir j)]
    simp [bwd]
  simp only [key]
  rw [sum_sub_distrib, sum_add_distrib, s1, s2, sum_sub_distrib, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun x _ => by ring
def plaqWeightA (i j : J) (k : G) : ℝ := Real.exp (-(V (k + L.dir i) + V (k + L.dir j)) / 2)
def plaqWeightB (i j : J) (k : G) : ℝ := Real.exp (-(V k + V (k + L.dir i + L.dir j)) / 2)
def plaqHalfDiff (i j : J) (k : G) : ℝ := (L.plaqWeightA V i j k - L.plaqWeightB V i j k) / 2
theorem sum_flux_mul_flux_div (u : G → ℝ) (i j : J) :
    ∑ x, L.flux V u i x * L.flux V u j x / siteMass V x = ∑ k,
      (L.plaqWeightA V i j k * (L.fwd u i k * L.fwd u j k + L.fwd u i (k + L.dir j) * L.fwd u j (k + L.dir i))
        - L.plaqWeightB V i j k * (L.fwd u i k * L.fwd u j (k + L.dir i) + L.fwd u i (k + L.dir j) * L.fwd u j k)) := by
  have h00 : ∀ k, L.edgeWeight V i k * L.edgeWeight V j k / siteMass V k = L.plaqWeightA V i j k := by
    intro k
    unfold edgeWeight siteMass plaqWeightA
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have h11 : ∀ k, L.edgeWeight V i (k + L.dir j) * L.edgeWeight V j (k + L.dir i) / siteMass V (k + L.dir i + L.dir j)
      = L.plaqWeightA V i j k := by
    intro k
    unfold edgeWeight siteMass plaqWeightA
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [add_right_comm k (L.dir j) (L.dir i)]
    ring
  have h10 : ∀ k, L.edgeWeight V i k * L.edgeWeight V j (k + L.dir i) / siteMass V (k + L.dir i) = L.plaqWeightB V i j k := by
    intro k
    unfold edgeWeight siteMass plaqWeightB
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have h01 : ∀ k, L.edgeWeight V i (k + L.dir j) * L.edgeWeight V j k / siteMass V (k + L.dir j) = L.plaqWeightB V i j k := by
    intro k
    unfold edgeWeight siteMass plaqWeightB
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [add_right_comm k (L.dir j) (L.dir i)]
    ring
  have t1 : ∑ x, L.edgeWeight V i (x - L.dir i) * L.bwd u i x * (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x
      = ∑ k, L.plaqWeightA V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j (k + L.dir i)) := by
    rw [← sum_add_const_eq (fun x => L.edgeWeight V i (x - L.dir i) * L.bwd u i x *
      (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x) (L.dir i + L.dir j)]
    refine sum_congr rfl fun k _ => ?_
    have a1 : k + (L.dir i + L.dir j) - L.dir i = k + L.dir j := by abel
    have a2 : k + (L.dir i + L.dir j) - L.dir j = k + L.dir i := by abel
    unfold bwd
    rw [a1, a2, ← h11 k, ← add_assoc]
    ring
  have t2 : ∑ x, L.edgeWeight V i (x - L.dir i) * L.bwd u i x * (L.edgeWeight V j x * L.fwd u j x) / siteMass V x
      = ∑ k, L.plaqWeightB V i j k * (L.fwd u i k * L.fwd u j (k + L.dir i)) := by
    rw [← sum_add_const_eq (fun x => L.edgeWeight V i (x - L.dir i) * L.bwd u i x *
      (L.edgeWeight V j x * L.fwd u j x) / siteMass V x) (L.dir i)]
    refine sum_congr rfl fun k _ => ?_
    unfold bwd
    rw [add_sub_cancel_right, ← h10 k]
    ring
  have t3 : ∑ x, L.edgeWeight V i x * L.fwd u i x * (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x
      = ∑ k, L.plaqWeightB V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j k) := by
    rw [← sum_add_const_eq (fun x => L.edgeWeight V i x * L.fwd u i x *
      (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x) (L.dir j)]
    refine sum_congr rfl fun k _ => ?_
    unfold bwd
    rw [add_sub_cancel_right, ← h01 k]
    ring
  have t4 : ∑ x, L.edgeWeight V i x * L.fwd u i x * (L.edgeWeight V j x * L.fwd u j x) / siteMass V x
      = ∑ k, L.plaqWeightA V i j k * (L.fwd u i k * L.fwd u j k) := by
    refine sum_congr rfl fun k _ => ?_
    rw [← h00 k]
    ring
  have split : ∀ x, L.flux V u i x * L.flux V u j x / siteMass V x =
      L.edgeWeight V i (x - L.dir i) * L.bwd u i x * (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x
      - L.edgeWeight V i (x - L.dir i) * L.bwd u i x * (L.edgeWeight V j x * L.fwd u j x) / siteMass V x
      - L.edgeWeight V i x * L.fwd u i x * (L.edgeWeight V j (x - L.dir j) * L.bwd u j x) / siteMass V x
      + L.edgeWeight V i x * L.fwd u i x * (L.edgeWeight V j x * L.fwd u j x) / siteMass V x := by
    intro x
    unfold flux
    ring
  simp only [split]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, t1, t2, t3, t4, ← sum_sub_distrib,
    ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring
end EdgeGrid
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Finset
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {G J : Type} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
namespace EdgeGrid
variable (L : EdgeGrid G J) (V : G → ℝ)
theorem fwd_add_dir (u : G → ℝ) {i j : J} (h : i ≠ j) (k : G) :
    L.fwd u i (k + L.dir j) = L.mark i k * L.diff u i (k + L.dir j) := by
  unfold fwd
  rw [L.mark_add_dir i j k h]
theorem plaq_le_cross (u : G → ℝ) {i j : J} (h : i ≠ j) :
    ∑ k, L.plaqHalfDiff V i j k * ((L.fwd u i k + L.fwd u i (k + L.dir j)) * (L.fwd u j k + L.fwd u j (k + L.dir i)))
      ≤ ∑ x, L.flux V u i x * L.flux V u j x / siteMass V x := by
  rw [L.sum_flux_mul_flux_div V u i j]
  refine sum_le_sum fun k _ => ?_
  have hs : 0 ≤ (L.plaqWeightA V i j k + L.plaqWeightB V i j k) / 2 := by
    have := Real.exp_pos (-(V (k + L.dir i) + V (k + L.dir j)) / 2)
    have := Real.exp_pos (-(V k + V (k + L.dir i + L.dir j)) / 2)
    unfold plaqWeightA plaqWeightB
    linarith
  have hsq : 0 ≤ (L.fwd u i k - L.fwd u i (k + L.dir j)) * (L.fwd u j k - L.fwd u j (k + L.dir i)) := by
    rw [L.fwd_add_dir u h k, L.fwd_add_dir u h.symm k]
    unfold fwd
    rcases L.mark_cases i k with hi | hi
    · simp [hi]
    rcases L.mark_cases j k with hj | hj
    · simp [hj]
    rw [hi, hj]
    have : (1 * L.diff u i k - 1 * L.diff u i (k + L.dir j)) = (1 * L.diff u j k - 1 * L.diff u j (k + L.dir i)) := by
      unfold diff
      rw [add_right_comm k (L.dir j) (L.dir i)]
      ring
    rw [this]
    exact mul_self_nonneg _
  have id1 : L.plaqWeightA V i j k * (L.fwd u i k * L.fwd u j k + L.fwd u i (k + L.dir j) * L.fwd u j (k + L.dir i))
        - L.plaqWeightB V i j k * (L.fwd u i k * L.fwd u j (k + L.dir i) + L.fwd u i (k + L.dir j) * L.fwd u j k)
      = (L.plaqWeightA V i j k + L.plaqWeightB V i j k) / 2 * ((L.fwd u i k - L.fwd u i (k + L.dir j)) * (L.fwd u j k - L.fwd u j (k + L.dir i)))
        + L.plaqHalfDiff V i j k * ((L.fwd u i k + L.fwd u i (k + L.dir j)) * (L.fwd u j k + L.fwd u j (k + L.dir i))) := by
    unfold plaqHalfDiff
    ring
  rw [id1]
  linarith [mul_nonneg hs hsq]
theorem mul_sub_abs_le {c a b P : ℝ} (h : P ≠ 0 → |c - a| ≤ b) : a * P - b * |P| ≤ c * P := by
  by_cases hP : P = 0
  · simp [hP]
  have h1 := h hP
  have h2 : |(c - a) * P| ≤ b * |P| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have h3 := neg_abs_le ((c - a) * P)
  nlinarith
theorem mark_eq_one_of_fwd {u : G → ℝ} {j : J} {k : G} (h : L.fwd u j k ≠ 0) : L.mark j k = 1 := by
  rcases L.mark_cases j k with h0 | h0
  · exact absurd (by unfold fwd; rw [h0, zero_mul]) h
  · exact h0
variable (H : G → J → J → ℝ) (s ε : ℝ)
def PlaquetteHessBound : Prop :=
  ∀ i j, i ≠ j → ∀ k, L.mark i k = 1 → L.mark j k = 1 → ∀ x,
    (x = k ∨ x = k + L.dir i ∨ x = k + L.dir j ∨ x = k + L.dir i + L.dir j) →
      |L.plaqHalfDiff V i j k - s ^ 2 / 4 * siteMass V x * H x i j| ≤ s ^ 2 / 4 * siteMass V x * ε
theorem cross_hessian_le (hc : L.PlaquetteHessBound V H s ε) (u : G → ℝ) {i j : J} (h : i ≠ j) :
    ∑ x, s ^ 2 / 4 * siteMass V x * (H x i j * ((L.fwd u i x + L.bwd u i x) * (L.fwd u j x + L.bwd u j x))
        - ε * ((|L.fwd u i x| + |L.bwd u i x|) * (|L.fwd u j x| + |L.bwd u j x|)))
      ≤ ∑ x, L.flux V u i x * L.flux V u j x / siteMass V x := by
  refine le_trans ?_ (L.plaq_le_cross V u h)
  set a : G → ℝ := fun x => s ^ 2 / 4 * siteMass V x * H x i j with ha
  set b : G → ℝ := fun x => s ^ 2 / 4 * siteMass V x * ε with hb
  have hA : ∑ x, (a x * (L.fwd u i x * L.fwd u j x) - b x * |L.fwd u i x * L.fwd u j x|)
      ≤ ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i k * L.fwd u j k) := by
    refine sum_le_sum fun k _ => mul_sub_abs_le fun hP => ?_
    have h1 : L.fwd u i k ≠ 0 := left_ne_zero_of_mul hP
    have h2 : L.fwd u j k ≠ 0 := right_ne_zero_of_mul hP
    exact hc i j h k (L.mark_eq_one_of_fwd h1) (L.mark_eq_one_of_fwd h2) k (Or.inl rfl)
  have hB : ∑ x, (a x * (L.bwd u i x * L.fwd u j x) - b x * |L.bwd u i x * L.fwd u j x|)
      ≤ ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i k * L.fwd u j (k + L.dir i)) := by
    rw [← sum_add_const_eq (fun x => a x * (L.bwd u i x * L.fwd u j x) - b x * |L.bwd u i x * L.fwd u j x|) (L.dir i)]
    refine sum_le_sum fun k _ => ?_
    simp only [bwd, add_sub_cancel_right]
    refine mul_sub_abs_le fun hP => ?_
    have h1 : L.fwd u i k ≠ 0 := left_ne_zero_of_mul hP
    have h2 : L.fwd u j (k + L.dir i) ≠ 0 := right_ne_zero_of_mul hP
    have h3 := L.mark_eq_one_of_fwd h2
    rw [L.mark_add_dir j i k h.symm] at h3
    exact hc i j h k (L.mark_eq_one_of_fwd h1) h3 _ (Or.inr (Or.inl rfl))
  have hC : ∑ x, (a x * (L.fwd u i x * L.bwd u j x) - b x * |L.fwd u i x * L.bwd u j x|)
      ≤ ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j k) := by
    rw [← sum_add_const_eq (fun x => a x * (L.fwd u i x * L.bwd u j x) - b x * |L.fwd u i x * L.bwd u j x|) (L.dir j)]
    refine sum_le_sum fun k _ => ?_
    simp only [bwd, add_sub_cancel_right]
    refine mul_sub_abs_le fun hP => ?_
    have h1 : L.fwd u i (k + L.dir j) ≠ 0 := left_ne_zero_of_mul hP
    have h2 : L.fwd u j k ≠ 0 := right_ne_zero_of_mul hP
    have h3 := L.mark_eq_one_of_fwd h1
    rw [L.mark_add_dir i j k h] at h3
    exact hc i j h k h3 (L.mark_eq_one_of_fwd h2) _ (Or.inr (Or.inr (Or.inl rfl)))
  have hD : ∑ x, (a x * (L.bwd u i x * L.bwd u j x) - b x * |L.bwd u i x * L.bwd u j x|)
      ≤ ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j (k + L.dir i)) := by
    rw [← sum_add_const_eq (fun x => a x * (L.bwd u i x * L.bwd u j x) - b x * |L.bwd u i x * L.bwd u j x|) (L.dir i + L.dir j)]
    refine sum_le_sum fun k _ => ?_
    have a1 : k + (L.dir i + L.dir j) - L.dir i = k + L.dir j := by abel
    have a2 : k + (L.dir i + L.dir j) - L.dir j = k + L.dir i := by abel
    simp only [bwd, a1, a2]
    refine mul_sub_abs_le fun hP => ?_
    have h1 : L.fwd u i (k + L.dir j) ≠ 0 := left_ne_zero_of_mul hP
    have h2 : L.fwd u j (k + L.dir i) ≠ 0 := right_ne_zero_of_mul hP
    have h3 := L.mark_eq_one_of_fwd h1
    have h4 := L.mark_eq_one_of_fwd h2
    rw [L.mark_add_dir i j k h] at h3
    rw [L.mark_add_dir j i k h.symm] at h4
    have := hc i j h k h3 h4 (k + (L.dir i + L.dir j)) (Or.inr (Or.inr (Or.inr (by rw [add_assoc]))))
    exact this
  have hsum : ∑ k, L.plaqHalfDiff V i j k * ((L.fwd u i k + L.fwd u i (k + L.dir j)) * (L.fwd u j k + L.fwd u j (k + L.dir i)))
      = ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i k * L.fwd u j k) + ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i k * L.fwd u j (k + L.dir i))
        + ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j k)
        + ∑ k, L.plaqHalfDiff V i j k * (L.fwd u i (k + L.dir j) * L.fwd u j (k + L.dir i)) := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsum]
  have hle : ∑ x, s ^ 2 / 4 * siteMass V x * (H x i j * ((L.fwd u i x + L.bwd u i x) * (L.fwd u j x + L.bwd u j x))
        - ε * ((|L.fwd u i x| + |L.bwd u i x|) * (|L.fwd u j x| + |L.bwd u j x|)))
      = ∑ x, (a x * (L.fwd u i x * L.fwd u j x) - b x * |L.fwd u i x * L.fwd u j x|)
        + ∑ x, (a x * (L.bwd u i x * L.fwd u j x) - b x * |L.bwd u i x * L.fwd u j x|)
        + ∑ x, (a x * (L.fwd u i x * L.bwd u j x) - b x * |L.fwd u i x * L.bwd u j x|)
        + ∑ x, (a x * (L.bwd u i x * L.bwd u j x) - b x * |L.bwd u i x * L.bwd u j x|) := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [ha, hb, abs_mul]
    ring
  rw [hle]
  linarith
def LineHessBound : Prop :=
  ∀ j x, s ^ 2 / 2 * (H x j j - ε) ≤ 1 ∧
    (L.mark j x = 1 → L.mark j (x - L.dir j) = 1 →
      L.diagWeight V j x ≤ siteMass V x * (1 - s ^ 2 / 2 * (H x j j - ε)))
theorem diag_hessian_le (hl : L.LineHessBound V H s ε) (u : G → ℝ) (j : J) :
    ∑ x, siteMass V x * (s ^ 2 / 2 * (H x j j - ε)) * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2)
      ≤ ∑ x, L.flux V u j x * L.flux V u j x / siteMass V x := by
  have e1 : ∑ x, L.flux V u j x * L.flux V u j x / siteMass V x = ∑ x, L.flux V u j x ^ 2 / siteMass V x :=
    sum_congr rfl fun x _ => by rw [sq]
  rw [e1, L.sum_flux_sq_div V u j]
  refine sum_le_sum fun x _ => ?_
  obtain ⟨h1, h2⟩ := hl j x
  have hp := siteMass_pos V x
  have hm := L.diagWeight_pos V j x
  set θ := s ^ 2 / 2 * (H x j j - ε)
  set p := L.fwd u j x with hpdef
  set q := L.bwd u j x with hqdef
  have hz : 0 ≤ p ^ 2 + q ^ 2 := by positivity
  rcases L.mark_cases j x with h0 | h0
  · have : p = 0 := by rw [hpdef]; unfold fwd; rw [h0, zero_mul]
    rw [this]
    have : 0 ≤ siteMass V x * (1 - θ) * q ^ 2 := mul_nonneg (mul_nonneg hp.le (by linarith)) (sq_nonneg _)
    nlinarith
  rcases L.mark_cases j (x - L.dir j) with h3 | h3
  · have : q = 0 := by rw [hqdef]; unfold bwd fwd; rw [h3, zero_mul]
    rw [this]
    have : 0 ≤ siteMass V x * (1 - θ) * p ^ 2 := mul_nonneg (mul_nonneg hp.le (by linarith)) (sq_nonneg _)
    nlinarith
  have h4 := h2 h0 h3
  have h5 : 0 ≤ (siteMass V x * (1 - θ) - L.diagWeight V j x) * (p ^ 2 + q ^ 2) :=
    mul_nonneg (by linarith) hz
  have h6 : 0 ≤ L.diagWeight V j x * (p - q) ^ 2 := mul_nonneg hm.le (sq_nonneg _)
  nlinarith
theorem site_form_le (w : J → ℝ) (hw : ∀ j, 0 < w j) (Wr : ℝ) (hWr : ∀ i j, w j ≤ Wr * w i)
    (Hx : J → J → ℝ) (m : ℝ) (hε : 0 ≤ ε)
    (hform : ∀ ξ : J → ℝ, m * ∑ j, w j * ξ j ^ 2 ≤ ∑ j, ∑ i, w j * Hx j i * ξ j * ξ i)
    (p q : J → ℝ) :
    (m - ε * ((Fintype.card J : ℝ) * (1 + Wr))) * ∑ j, w j * (p j ^ 2 + q j ^ 2) / 2
      ≤ ∑ j, w j * ∑ i, if i = j then (Hx j j - ε) * (p j ^ 2 + q j ^ 2) / 2 else
          (Hx j i * ((p j + q j) * (p i + q i))
            - ε * ((|p j| + |q j|) * (|p i| + |q i|))) / 4 := by
  classical
  set ξ : J → ℝ := fun j => (p j + q j) / 2 with hξ
  set ζ : J → ℝ := fun j => (p j - q j) / 2 with hζ
  set A : J → ℝ := fun j => p j ^ 2 + q j ^ 2 with hA
  have hA0 : ∀ j, 0 ≤ A j := fun j => by positivity
  have hdiag : ∀ j, m ≤ Hx j j := by
    intro j
    have := hform (Pi.single j 1)
    simp only [Pi.single_apply, ite_pow, one_pow, mul_ite, mul_one, mul_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    simp only [sum_ite_eq', mem_univ, if_true] at this
    have h2 : ∑ j_1, ∑ i, (if j_1 = j then (if i = j then w j_1 * Hx j_1 i else 0) else 0)
        = w j * Hx j j := by
      rw [sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have h3 : ∑ j_1, ∑ i, (if i = j then (if j_1 = j then w j_1 * Hx j_1 i else 0) else 0)
        = w j * Hx j j := by
      rw [sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have h4 : m * w j ≤ w j * Hx j j := by
      first
        | simpa [h2] using this
        | simpa [h3] using this
        | (convert this using 1; simp [sum_ite_eq', sum_ite_eq])
    nlinarith [hw j]
  have hterm : ∀ j i, Hx j i * ξ j * ξ i + (if i = j then Hx j j * ζ j ^ 2 else 0)
        - ε * ((A i + A j) / 2)
      ≤ if i = j then (Hx j j - ε) * (p j ^ 2 + q j ^ 2) / 2 else
          (Hx j i * ((p j + q j) * (p i + q i))
            - ε * ((|p j| + |q j|) * (|p i| + |q i|))) / 4 := by
    intro j i
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hξ, hζ, hA]
      have : 0 ≤ ε * (p i ^ 2 + q i ^ 2) := mul_nonneg hε (by positivity)
      nlinarith
    · simp only [if_neg hij, hξ, hA]
      have h1 : (|p j| + |q j|) * (|p i| + |q i|) ≤ (p i ^ 2 + q i ^ 2) + (p j ^ 2 + q j ^ 2) := by
        have a1 := sq_abs (p j)
        have a2 := sq_abs (q j)
        have a3 := sq_abs (p i)
        have a4 := sq_abs (q i)
        nlinarith [sq_nonneg (|p j| + |q j| - |p i| - |q i|), sq_nonneg (|p j| - |q j|), sq_nonneg (|p i| - |q i|)]
      have h2 := mul_le_mul_of_nonneg_left h1 hε
      nlinarith
  have hsum : ∑ j, w j * ∑ i, (Hx j i * ξ j * ξ i + (if i = j then Hx j j * ζ j ^ 2 else 0)
        - ε * ((A i + A j) / 2))
      ≤ ∑ j, w j * ∑ i, if i = j then (Hx j j - ε) * (p j ^ 2 + q j ^ 2) / 2 else
          (Hx j i * ((p j + q j) * (p i + q i))
            - ε * ((|p j| + |q j|) * (|p i| + |q i|))) / 4 :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hterm j i) (hw j).le
  refine le_trans ?_ hsum
  have e1 : ∑ j, w j * ∑ i, (Hx j i * ξ j * ξ i + (if i = j then Hx j j * ζ j ^ 2 else 0)
        - ε * ((A i + A j) / 2))
      = ∑ j, ∑ i, w j * Hx j i * ξ j * ξ i + ∑ j, w j * (Hx j j * ζ j ^ 2)
        - ε * ∑ j, ∑ i, w j * ((A i + A j) / 2) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_sub_distrib, sum_add_distrib, mul_sub, mul_add, mul_sum, mul_sum, mul_sum, mul_sum]
    simp only [sum_ite_eq', mem_univ, if_true, mul_ite, mul_zero]
    congr 1
    · congr 1
      exact sum_congr rfl fun i _ => by ring
    · exact sum_congr rfl fun i _ => by ring
  rw [e1]
  have f1 := hform ξ
  have f2 : m * ∑ j, w j * ζ j ^ 2 ≤ ∑ j, w j * (Hx j j * ζ j ^ 2) := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_right (hdiag j) (mul_nonneg (hw j).le (sq_nonneg (ζ j)))
    nlinarith
  have f3 : ∑ j, ∑ i, w j * ((A i + A j) / 2)
      ≤ (Fintype.card J : ℝ) * (1 + Wr) * ∑ j, w j * A j / 2 := by
    have g1 : ∑ j, ∑ i, w j * (A i / 2) ≤ (Fintype.card J : ℝ) * Wr * ∑ i, w i * A i / 2 := by
      rw [sum_comm, mul_sum]
      refine sum_le_sum fun i _ => ?_
      have : ∑ j, w j * (A i / 2) ≤ ∑ _j : J, Wr * (w i * A i / 2) :=
        sum_le_sum fun j _ => by
          have := mul_le_mul_of_nonneg_right (hWr i j) (div_nonneg (hA0 i) (by norm_num : (0:ℝ) ≤ 2))
          nlinarith
      refine le_trans this ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
    have g2 : ∑ j, ∑ i : J, w j * (A j / 2) = (Fintype.card J : ℝ) * ∑ j, w j * A j / 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring
    have g3 : ∑ j, ∑ i, w j * ((A i + A j) / 2)
        = ∑ j, ∑ i, w j * (A i / 2) + ∑ j, ∑ i : J, w j * (A j / 2) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [g3, g2]
    have : (Fintype.card J : ℝ) * (1 + Wr) * ∑ j, w j * A j / 2
        = (Fintype.card J : ℝ) * Wr * ∑ j, w j * A j / 2 + (Fintype.card J : ℝ) * ∑ j, w j * A j / 2 := by
      ring
    rw [this]
    linarith
  have f4 : ∑ j, w j * (p j ^ 2 + q j ^ 2) / 2 = ∑ j, w j * ξ j ^ 2 + ∑ j, w j * ζ j ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by simp only [hξ, hζ]; ring
  have f5 := mul_le_mul_of_nonneg_left f3 hε
  have f6 : ∑ j, w j * A j / 2 = ∑ j, w j * (p j ^ 2 + q j ^ 2) / 2 := rfl
  rw [f6] at f5
  have f7 : m * ∑ j, w j * (p j ^ 2 + q j ^ 2) / 2 ≤
      ∑ j, ∑ i, w j * Hx j i * ξ j * ξ i + ∑ j, w j * (Hx j j * ζ j ^ 2) := by
    rw [f4, mul_add]
    linarith
  nlinarith
end EdgeGrid
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Finset
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {G J : Type} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
namespace EdgeGrid
variable (L : EdgeGrid G J) (V : G → ℝ)
def siteEnergy (w : J → ℝ) (u : G → ℝ) : ℝ :=
  ∑ x, siteMass V x * ∑ j, w j * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2
def edgeForm (w : J → ℝ) (u g : G → ℝ) : ℝ :=
  ∑ j, w j * ∑ k, L.edgeWeight V j k * L.fwd u j k * L.fwd g j k
variable (H : G → J → J → ℝ) (s ε : ℝ)
theorem discrete_bochner (hc : L.PlaquetteHessBound V H s ε) (hl : L.LineHessBound V H s ε)
    (w : J → ℝ) (hw : ∀ j, 0 < w j) (Wr : ℝ) (hWr : ∀ i j, w j ≤ Wr * w i) (m : ℝ) (hε : 0 ≤ ε)
    (hform : ∀ x, ∀ ξ : J → ℝ, m * ∑ j, w j * ξ j ^ 2 ≤ ∑ j, ∑ i, w j * H x j i * ξ j * ξ i)
    (u : G → ℝ) :
    s ^ 2 * (m - ε * ((Fintype.card J : ℝ) * (1 + Wr))) * L.siteEnergy V w u
      ≤ ∑ x, (∑ j, w j * L.flux V u j x) * (∑ i, L.flux V u i x) / siteMass V x := by
  have e1 : ∑ x, (∑ j, w j * L.flux V u j x) * (∑ i, L.flux V u i x) / siteMass V x
      = ∑ j, w j * ∑ i, ∑ x, L.flux V u j x * L.flux V u i x / siteMass V x := by
    have h : ∀ x, (∑ j, w j * L.flux V u j x) * (∑ i, L.flux V u i x) / siteMass V x
        = ∑ j, w j * ∑ i, L.flux V u j x * L.flux V u i x / siteMass V x := by
      intro x
      rw [sum_mul, sum_div]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc, mul_div_assoc, mul_sum, sum_div]
    simp only [h]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sum, sum_comm]
  rw [e1]
  set LB : J → J → G → ℝ := fun j i x => s ^ 2 * siteMass V x *
    (if i = j then (H x j j - ε) * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2 else
      (H x j i * ((L.fwd u j x + L.bwd u j x) * (L.fwd u i x + L.bwd u i x))
        - ε * ((|L.fwd u j x| + |L.bwd u j x|) * (|L.fwd u i x| + |L.bwd u i x|))) / 4) with hLB
  have h1 : ∀ j i, ∑ x, LB j i x ≤ ∑ x, L.flux V u j x * L.flux V u i x / siteMass V x := by
    intro j i
    by_cases hij : i = j
    · subst hij
      refine le_trans (le_of_eq ?_) (L.diag_hessian_le V H s ε hl u i)
      refine sum_congr rfl fun x _ => ?_
      simp only [hLB, if_true]
      ring
    · refine le_trans (le_of_eq ?_) (L.cross_hessian_le V H s ε hc u (Ne.symm hij))
      refine sum_congr rfl fun x _ => ?_
      simp only [hLB, if_neg hij]
      ring
  have h2 : ∑ j, w j * ∑ i, ∑ x, LB j i x
      ≤ ∑ j, w j * ∑ i, ∑ x, L.flux V u j x * L.flux V u i x / siteMass V x :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => h1 j i) (hw j).le
  refine le_trans ?_ h2
  have e2 : ∑ j, w j * ∑ i, ∑ x, LB j i x = ∑ x, s ^ 2 * siteMass V x * ∑ j, w j * ∑ i,
      (if i = j then (H x j j - ε) * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2 else
      (H x j i * ((L.fwd u j x + L.bwd u j x) * (L.fwd u i x + L.bwd u i x))
        - ε * ((|L.fwd u j x| + |L.bwd u j x|) * (|L.fwd u i x| + |L.bwd u i x|))) / 4) := by
    have h : ∀ j, w j * ∑ i, ∑ x, LB j i x = ∑ x, s ^ 2 * siteMass V x * (w j * ∑ i,
      (if i = j then (H x j j - ε) * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2 else
      (H x j i * ((L.fwd u j x + L.bwd u j x) * (L.fwd u i x + L.bwd u i x))
        - ε * ((|L.fwd u j x| + |L.bwd u j x|) * (|L.fwd u i x| + |L.bwd u i x|))) / 4)) := by
      intro j
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      simp only [hLB]
      rw [← mul_sum]
      ring
    simp only [h]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
  rw [e2]
  unfold siteEnergy
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have h3 := site_form_le ε w hw Wr hWr (H x) m hε (hform x)
    (fun j => L.fwd u j x) (fun j => L.bwd u j x)
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (sq_nonneg s) (siteMass_pos V x).le)
  refine le_trans (le_of_eq ?_) h4
  ring
theorem fwd_mul_diff (u g : G → ℝ) (j : J) (k : G) :
    L.fwd u j k * L.diff g j k = L.fwd u j k * L.fwd g j k := by
  unfold fwd
  rcases L.mark_cases j k with h | h <;> simp [h]
theorem edgeForm_self_nonneg (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (u : G → ℝ) : 0 ≤ L.edgeForm V w u u := by
  refine sum_nonneg fun j _ => mul_nonneg (hw j) (sum_nonneg fun k _ => ?_)
  have h1 := (L.edgeWeight_pos V j k).le
  rw [mul_assoc]
  exact mul_nonneg h1 (mul_self_nonneg _)
theorem edgeForm_le_siteEnergy (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (u : G → ℝ) : L.edgeForm V w u u ≤ L.siteEnergy V w u := by
  have h1 : ∀ j, ∑ k, L.edgeWeight V j k * L.fwd u j k * L.fwd u j k
      ≤ ∑ x, siteMass V x * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2 := by
    intro j
    have s1 : ∑ x, siteMass V x * L.bwd u j x ^ 2 = ∑ k, siteMass V (k + L.dir j) * L.fwd u j k ^ 2 := by
      rw [← sum_add_const_eq (fun x => siteMass V x * L.bwd u j x ^ 2) (L.dir j)]
      simp [bwd]
    have s2 : ∑ x, siteMass V x * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2
        = ∑ x, siteMass V x * L.fwd u j x ^ 2 / 2 + (∑ x, siteMass V x * L.bwd u j x ^ 2) / 2 := by
      rw [sum_div, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [s2, s1, sum_div, ← sum_add_distrib]
    refine sum_le_sum fun k _ => ?_
    have := mul_le_mul_of_nonneg_right (L.edgeWeight_le V j k) (sq_nonneg (L.fwd u j k))
    nlinarith
  have h2 : L.siteEnergy V w u = ∑ j, w j * ∑ x, siteMass V x * (L.fwd u j x ^ 2 + L.bwd u j x ^ 2) / 2 := by
    unfold siteEnergy
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun x _ => by ring
  rw [h2]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hw j)
theorem edgeForm_sq_le (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (u g : G → ℝ) :
    L.edgeForm V w u g ^ 2 ≤ L.edgeForm V w u u * L.edgeForm V w g g := by
  set c : J × G → ℝ := fun a => Real.sqrt (w a.1 * L.edgeWeight V a.1 a.2) with hc
  have hc2 : ∀ a : J × G, c a * c a = w a.1 * L.edgeWeight V a.1 a.2 := fun a =>
    Real.mul_self_sqrt (mul_nonneg (hw _) (L.edgeWeight_pos V _ _).le)
  have hform : ∀ u g : G → ℝ, L.edgeForm V w u g
      = ∑ a : J × G, (c a * L.fwd u a.1 a.2) * (c a * L.fwd g a.1 a.2) := by
    intro u g
    rw [Fintype.sum_prod_type]
    unfold edgeForm
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have := hc2 (j, k)
    simp only at this
    calc w j * (L.edgeWeight V j k * L.fwd u j k * L.fwd g j k)
        = (w j * L.edgeWeight V j k) * (L.fwd u j k * L.fwd g j k) := by ring
      _ = _ := by rw [← this]; ring
  have := sum_mul_sq_le_sq_mul_sq (univ : Finset (J × G))
    (fun a => c a * L.fwd u a.1 a.2) (fun a => c a * L.fwd g a.1 a.2)
  rw [hform u g, hform u u, hform g g]
  simpa only [sq] using this
variable {L V H s ε}
theorem energy_contraction (hs : 0 < s) (hc : L.PlaquetteHessBound V H s ε) (hl : L.LineHessBound V H s ε)
    (w : J → ℝ) (hw : ∀ j, 0 < w j) (Wr : ℝ) (hWr : ∀ i j, w j ≤ Wr * w i) (m : ℝ) (hε : 0 ≤ ε)
    (hform : ∀ x, ∀ ξ : J → ℝ, m * ∑ j, w j * ξ j ^ 2 ≤ ∑ j, ∑ i, w j * H x j i * ξ j * ξ i)
    (hm : 0 < m - ε * ((Fintype.card J : ℝ) * (1 + Wr)))
    (u g : G → ℝ) (cst : ℝ) (hsol : ∀ x, ∑ i, L.flux V u i x = s ^ 2 * siteMass V x * (g x - cst)) :
    (m - ε * ((Fintype.card J : ℝ) * (1 + Wr))) ^ 2 * L.edgeForm V w u u ≤ L.edgeForm V w g g := by
  set mh := m - ε * ((Fintype.card J : ℝ) * (1 + Wr)) with hmh
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).le
  have hB := L.discrete_bochner V H s ε hc hl w hw Wr hWr m hε hform u
  have e1 : ∑ x, (∑ j, w j * L.flux V u j x) * (∑ i, L.flux V u i x) / siteMass V x
      = s ^ 2 * L.edgeForm V w u g := by
    have h1 : ∀ x, (∑ j, w j * L.flux V u j x) * (∑ i, L.flux V u i x) / siteMass V x
        = s ^ 2 * ∑ j, w j * (L.flux V u j x * (g x - cst)) := by
      intro x
      have hp := (siteMass_pos V x).ne'
      have h5 : (∑ j, w j * L.flux V u j x) * (s ^ 2 * siteMass V x * (g x - cst)) / siteMass V x
          = s ^ 2 * ((∑ j, w j * L.flux V u j x) * (g x - cst)) := by
        field_simp
      rw [hsol x, h5, sum_mul]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    simp only [h1]
    rw [← mul_sum, sum_comm]
    congr 1
    unfold edgeForm
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sum, L.sum_flux_mul V u (fun x => g x - cst) j]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have : L.diff (fun x => g x - cst) j k = L.diff g j k := by unfold diff; ring
    rw [this, mul_assoc, L.fwd_mul_diff, mul_assoc]
  rw [e1] at hB
  have hs2 : 0 < s ^ 2 := by positivity
  have h2 : mh * L.siteEnergy V w u ≤ L.edgeForm V w u g := by
    have : s ^ 2 * (mh * L.siteEnergy V w u) ≤ s ^ 2 * L.edgeForm V w u g := by
      rw [← mul_assoc]; exact hB
    exact le_of_mul_le_mul_left this hs2
  have hN0 : 0 ≤ L.siteEnergy V w u := le_trans (L.edgeForm_self_nonneg V w hw0 u) (L.edgeForm_le_siteEnergy V w hw0 u)
  have hQu := L.edgeForm_le_siteEnergy V w hw0 u
  have hQu0 := L.edgeForm_self_nonneg V w hw0 u
  have hQg0 := L.edgeForm_self_nonneg V w hw0 g
  have hcs := L.edgeForm_sq_le V w hw0 u g
  have h3 : (mh * L.siteEnergy V w u) ^ 2 ≤ L.siteEnergy V w u * L.edgeForm V w g g := by
    have h4 : (mh * L.siteEnergy V w u) ^ 2 ≤ L.edgeForm V w u g ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hm.le hN0) h2 2
    exact le_trans h4 (le_trans hcs (mul_le_mul_of_nonneg_right hQu hQg0))
  rcases hN0.eq_or_lt with h0 | hpos
  · have : L.edgeForm V w u u ≤ 0 := by rw [← h0] at hQu; exact hQu
    have : L.edgeForm V w u u = 0 := le_antisymm this hQu0
    rw [this, mul_zero]
    exact hQg0
  · have h5 : mh ^ 2 * L.siteEnergy V w u ≤ L.edgeForm V w g g := by
      have : L.siteEnergy V w u * (mh ^ 2 * L.siteEnergy V w u) ≤ L.siteEnergy V w u * L.edgeForm V w g g := by
        calc L.siteEnergy V w u * (mh ^ 2 * L.siteEnergy V w u) = (mh * L.siteEnergy V w u) ^ 2 := by ring
          _ ≤ _ := h3
      exact le_of_mul_le_mul_left this hpos
    exact le_trans (mul_le_mul_of_nonneg_left hQu (sq_nonneg mh)) h5
variable (L V)
theorem flux_add (u v : G → ℝ) (j : J) (k : G) :
    L.flux V (u + v) j k = L.flux V u j k + L.flux V v j k := by
  simp only [flux, bwd, fwd, diff, Pi.add_apply]
  ring
theorem flux_smul (c : ℝ) (u : G → ℝ) (j : J) (k : G) :
    L.flux V (c • u) j k = c * L.flux V u j k := by
  simp only [flux, bwd, fwd, diff, Pi.smul_apply, smul_eq_mul]
  ring
def fluxPlusSum : (G → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun u x := ∑ i, L.flux V u i x + ∑ y, u y
  map_add' u v := by
    funext x
    simp only [L.flux_add V, sum_add_distrib, Pi.add_apply]
    ring
  map_smul' c u := by
    funext x
    simp only [L.flux_smul V, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, mul_sum]
theorem sum_flux (u : G → ℝ) (j : J) : ∑ k, L.flux V u j k = 0 := by
  have := L.sum_flux_mul V u (fun _ => 1) j
  simpa [diff] using this
theorem sum_flux_mul_self (u : G → ℝ) (j : J) :
    ∑ k, L.flux V u j k * u k = ∑ k, L.edgeWeight V j k * (L.fwd u j k * L.fwd u j k) := by
  rw [L.sum_flux_mul V u u j]
  exact sum_congr rfl fun k _ => by rw [mul_assoc, L.fwd_mul_diff]
theorem exists_flux_solution
    (hconn : ∀ u : G → ℝ, (∀ j k, L.mark j k = 1 → L.diff u j k = 0) → ∀ k k', u k = u k')
    (r : G → ℝ) (hr : ∑ x, r x = 0) : ∃ u : G → ℝ, ∀ x, ∑ i, L.flux V u i x = r x := by
  have hinj : Function.Injective (L.fluxPlusSum V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ x, ∑ i, L.flux V u i x + ∑ y, u y = 0 := fun x => congrFun hu x
    have h1 : ∑ x, (∑ i, L.flux V u i x + ∑ y, u y) * u x = 0 := by
      simp only [h0, zero_mul, sum_const_zero]
    have h2 : ∑ x, (∑ i, L.flux V u i x + ∑ y, u y) * u x
        = ∑ i, ∑ k, L.edgeWeight V i k * (L.fwd u i k * L.fwd u i k) + (∑ y, u y) ^ 2 := by
      simp only [add_mul, sum_add_distrib, sum_mul]
      rw [sum_comm]
      congr 1
      · exact sum_congr rfl fun i _ => L.sum_flux_mul_self V u i
      · rw [sq, sum_mul_sum, sum_comm]
    rw [h2] at h1
    have h3 : ∀ i k, 0 ≤ L.edgeWeight V i k * (L.fwd u i k * L.fwd u i k) := fun i k =>
      mul_nonneg (L.edgeWeight_pos V i k).le (mul_self_nonneg _)
    have h4 : 0 ≤ ∑ i, ∑ k, L.edgeWeight V i k * (L.fwd u i k * L.fwd u i k) :=
      sum_nonneg fun i _ => sum_nonneg fun k _ => h3 i k
    have h5 : ∑ i, ∑ k, L.edgeWeight V i k * (L.fwd u i k * L.fwd u i k) = 0 := by
      nlinarith [sq_nonneg (∑ y, u y)]
    have h6 : (∑ y, u y) ^ 2 = 0 := by linarith
    have h7 : ∑ y, u y = 0 := by simpa using h6
    have h8 : ∀ j k, L.mark j k = 1 → L.diff u j k = 0 := by
      intro j k hjk
      have a1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun k _ => h3 i k)).mp h5 j (mem_univ j)
      have a2 := (sum_eq_zero_iff_of_nonneg (fun k _ => h3 j k)).mp a1 k (mem_univ k)
      have a3 : L.fwd u j k * L.fwd u j k = 0 := by
        rcases mul_eq_zero.mp a2 with h | h
        · exact absurd h (L.edgeWeight_pos V j k).ne'
        · exact h
      have a4 : L.fwd u j k = 0 := by simpa using a3
      unfold fwd at a4
      rw [hjk, one_mul] at a4
      exact a4
    have h9 := hconn u h8
    have h10 : ∀ k, u k = u 0 := fun k => h9 k 0
    have h11 : (Fintype.card G : ℝ) * u 0 = 0 := by
      have : ∑ y, u y = ∑ _y : G, u 0 := sum_congr rfl fun y _ => h10 y
      rw [this, sum_const, card_univ, nsmul_eq_mul] at h7
      exact h7
    have h12 : (Fintype.card G : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have h13 : u 0 = 0 := by
      rcases mul_eq_zero.mp h11 with h | h
      · exact absurd h h12
      · exact h
    funext k
    rw [h10 k, h13]
    rfl
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsurj r
  have h0 : ∀ x, ∑ i, L.flux V u i x + ∑ y, u y = r x := fun x => congrFun hu x
  have h1 : ∑ x, (∑ i, L.flux V u i x + ∑ y, u y) = 0 := by
    simp only [h0]; exact hr
  rw [sum_add_distrib, sum_comm] at h1
  simp only [L.sum_flux V u, sum_const_zero, zero_add] at h1
  rw [sum_const, card_univ, nsmul_eq_mul] at h1
  have h12 : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h2 : ∑ y, u y = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h h12
    · exact h
  refine ⟨u, fun x => ?_⟩
  have := h0 x
  rw [h2, add_zero] at this
  exact this
end EdgeGrid
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Finset
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {G J : Type} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
namespace EdgeGrid
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (L : EdgeGrid G J) (V : G → ℝ)
def bondEnergy (β : J → ι) (f : G → ℝ) (b : ι) : ℝ :=
  L.edgeForm V (fun j => if β j = b then 1 else 0) f f
theorem edgeForm_mono {w w' : J → ℝ} (hww : ∀ j, w j ≤ w' j) (u : G → ℝ) :
    L.edgeForm V w u u ≤ L.edgeForm V w' u u := by
  refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hww j) (sum_nonneg fun k _ => ?_)
  rw [mul_assoc]
  exact mul_nonneg (L.edgeWeight_pos V j k).le (mul_self_nonneg _)
theorem bondEnergy_nonneg (β : J → ι) (f : G → ℝ) (b : ι) : 0 ≤ L.bondEnergy V β f b :=
  L.edgeForm_self_nonneg V _ (fun j => by split_ifs <;> norm_num) f
theorem edgeForm_fiber (β : J → ι) (w : ι → ℝ) (f g : G → ℝ) :
    L.edgeForm V (fun j => w (β j)) f g
      = ∑ b, w b * L.edgeForm V (fun j => if β j = b then 1 else 0) f g := by
  unfold edgeForm
  calc ∑ j, w (β j) * ∑ k, L.edgeWeight V j k * L.fwd f j k * L.fwd g j k
      = ∑ j, ∑ b, w b * ((if β j = b then 1 else 0) * ∑ k, L.edgeWeight V j k * L.fwd f j k * L.fwd g j k) := by
        refine sum_congr rfl fun j _ => ?_
        simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
    _ = ∑ b, ∑ j, w b * ((if β j = b then 1 else 0) * ∑ k, L.edgeWeight V j k * L.fwd f j k * L.fwd g j k) :=
        sum_comm
    _ = _ := by
        refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]
theorem sum_sq_le_sq_of_nonneg {α : Type} [Fintype α] (a : α → ℝ) (ha : ∀ x, 0 ≤ a x) :
    ∑ x, a x ^ 2 ≤ (∑ x, a x) ^ 2 := by
  rw [sq (∑ x, a x), sum_mul]
  refine sum_le_sum fun x _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := a) (fun y _ => ha y) (mem_univ x)) (ha x)
variable {L V}
variable {H : G → J → J → ℝ} {s ε : ℝ}
theorem discrete_covariance (hs : 0 < s) (hc : L.PlaquetteHessBound V H s ε) (hl : L.LineHessBound V H s ε)
    (β : J → ι) (Dk : ι → ι → ℝ) (hD0 : ∀ b b', 0 < Dk b b') (hD1 : ∀ b, Dk b b = 1)
    (Wr m : ℝ) (hε : 0 ≤ ε)
    (hWr : ∀ b i j, Dk b (β j) ^ 2 ≤ Wr * Dk b (β i) ^ 2)
    (hform : ∀ b x, ∀ ξ : J → ℝ, m * ∑ j, Dk b (β j) ^ 2 * ξ j ^ 2
      ≤ ∑ j, ∑ i, Dk b (β j) ^ 2 * H x j i * ξ j * ξ i)
    (hm : 0 < m - ε * ((Fintype.card J : ℝ) * (1 + Wr)))
    (hconn : ∀ u : G → ℝ, (∀ j k, L.mark j k = 1 → L.diff u j k = 0) → ∀ k k', u k = u k')
    (f g : G → ℝ) :
    s ^ 2 * |∑ x, siteMass V x * f x * (g x - (∑ y, siteMass V y * g y) / ∑ y, siteMass V y)|
      ≤ (m - ε * ((Fintype.card J : ℝ) * (1 + Wr)))⁻¹ *
        ∑ b, ∑ b', Real.sqrt (L.bondEnergy V β f b) * Dk b b' * Real.sqrt (L.bondEnergy V β g b') := by
  set mh := m - ε * ((Fintype.card J : ℝ) * (1 + Wr)) with hmh
  set Z := ∑ y, siteMass V y with hZ
  have hZpos : 0 < Z := sum_pos (fun y _ => siteMass_pos V y) ⟨0, mem_univ _⟩
  set c := (∑ y, siteMass V y * g y) / Z with hcdef
  have hr : ∑ x, s ^ 2 * siteMass V x * (g x - c) = 0 := by
    have e : ∀ x, s ^ 2 * siteMass V x * (g x - c) = s ^ 2 * (siteMass V x * g x) - s ^ 2 * c * siteMass V x :=
      fun x => by ring
    have hcZ : c * Z = ∑ y, siteMass V y * g y := div_mul_cancel₀ _ hZpos.ne'
    simp only [e]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, ← hZ, mul_assoc, hcZ]
    ring
  obtain ⟨u, hu⟩ := L.exists_flux_solution V hconn _ hr
  have key : s ^ 2 * ∑ x, siteMass V x * f x * (g x - c) = ∑ b, L.edgeForm V (fun j => if β j = b then 1 else 0) u f := by
    have h1 : s ^ 2 * ∑ x, siteMass V x * f x * (g x - c) = ∑ x, (∑ i, L.flux V u i x) * f x := by
      rw [mul_sum]
      exact sum_congr rfl fun x _ => by rw [hu x]; ring
    have h2 : L.edgeForm V (fun _ => (1 : ℝ)) u f = ∑ x, (∑ i, L.flux V u i x) * f x := by
      have e : ∑ x, (∑ i, L.flux V u i x) * f x = ∑ i, ∑ x, L.flux V u i x * f x := by
        simp only [sum_mul]
        exact sum_comm
      rw [e]
      unfold edgeForm
      refine sum_congr rfl fun j _ => ?_
      rw [L.sum_flux_mul V u f j, one_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_assoc (L.edgeWeight V j k) _ (L.diff f j k), L.fwd_mul_diff, mul_assoc]
    have h3 : L.edgeForm V (fun _ => (1 : ℝ)) u f = ∑ b, L.edgeForm V (fun j => if β j = b then 1 else 0) u f := by
      simpa using L.edgeForm_fiber V β (fun _ => 1) u f
    rw [h1, ← h2, h3]
  have habs : s ^ 2 * |∑ x, siteMass V x * f x * (g x - c)| = |s ^ 2 * ∑ x, siteMass V x * f x * (g x - c)| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < s ^ 2)]
  rw [habs, key]
  have hb : ∀ b, |L.edgeForm V (fun j => if β j = b then 1 else 0) u f|
      ≤ mh⁻¹ * ∑ b', Real.sqrt (L.bondEnergy V β f b) * Dk b b' * Real.sqrt (L.bondEnergy V β g b') := by
    intro b
    have h0 : ∀ j, (0 : ℝ) ≤ if β j = b then 1 else 0 := fun j => by split_ifs <;> norm_num
    have h1 := L.edgeForm_sq_le V _ h0 u f
    have h2 : |L.edgeForm V (fun j => if β j = b then 1 else 0) u f|
        ≤ Real.sqrt (L.bondEnergy V β u b) * Real.sqrt (L.bondEnergy V β f b) := by
      rw [← Real.sqrt_mul (L.bondEnergy_nonneg V β u b)]
      exact Real.abs_le_sqrt h1
    set a : ι → ℝ := fun b' => Dk b b' * Real.sqrt (L.bondEnergy V β g b') with ha
    have ha0 : ∀ b', 0 ≤ a b' := fun b' => mul_nonneg (hD0 b b').le (Real.sqrt_nonneg _)
    have h3 : Real.sqrt (L.bondEnergy V β u b) ≤ mh⁻¹ * ∑ b', a b' := by
      have w0 : ∀ j, 0 < Dk b (β j) ^ 2 := fun j => by have := hD0 b (β j); positivity
      have h4 := energy_contraction hs hc hl (fun j => Dk b (β j) ^ 2) w0 Wr (hWr b) m hε (hform b) hm u g c
        (fun x => by rw [hu x])
      have h5 : L.bondEnergy V β u b ≤ L.edgeForm V (fun j => Dk b (β j) ^ 2) u u := by
        refine L.edgeForm_mono V (fun j => ?_) u
        split_ifs with h
        · rw [h, hD1]; norm_num
        · exact (w0 j).le
      have h6 : L.edgeForm V (fun j => Dk b (β j) ^ 2) g g = ∑ b', a b' ^ 2 := by
        rw [L.edgeForm_fiber V β (fun b' => Dk b b' ^ 2)]
        refine sum_congr rfl fun b' _ => ?_
        simp only [ha, mul_pow]
        rw [Real.sq_sqrt (L.bondEnergy_nonneg V β g b')]
        rfl
      have h7 := sum_sq_le_sq_of_nonneg a ha0
      have h8 : mh ^ 2 * L.bondEnergy V β u b ≤ (∑ b', a b') ^ 2 := by
        calc mh ^ 2 * L.bondEnergy V β u b ≤ mh ^ 2 * L.edgeForm V (fun j => Dk b (β j) ^ 2) u u :=
              mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
          _ ≤ L.edgeForm V (fun j => Dk b (β j) ^ 2) g g := h4
          _ = ∑ b', a b' ^ 2 := h6
          _ ≤ _ := h7
      have h9 : 0 ≤ ∑ b', a b' := sum_nonneg fun b' _ => ha0 b'
      have h10 : L.bondEnergy V β u b ≤ (mh⁻¹ * ∑ b', a b') ^ 2 := by
        rw [mul_pow, inv_pow]
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith
      exact Real.sqrt_le_iff.mpr ⟨by positivity, h10⟩
    refine le_trans h2 ?_
    calc Real.sqrt (L.bondEnergy V β u b) * Real.sqrt (L.bondEnergy V β f b)
        ≤ (mh⁻¹ * ∑ b', a b') * Real.sqrt (L.bondEnergy V β f b) :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = _ := by
          rw [mul_assoc, sum_mul, mul_sum]
          congr 1
          simp only [mul_sum]
          exact sum_congr rfl fun b' _ => by simp only [ha]; ring
  calc |∑ b, L.edgeForm V (fun j => if β j = b then 1 else 0) u f|
      ≤ ∑ b, |L.edgeForm V (fun j => if β j = b then 1 else 0) u f| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, mh⁻¹ * ∑ b', Real.sqrt (L.bondEnergy V β f b) * Dk b b' * Real.sqrt (L.bondEnergy V β g b') :=
        sum_le_sum fun b _ => hb b
    _ = _ := by rw [mul_sum]
end EdgeGrid
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
def secondDeriv (Φ : X → ℝ) (η u v : X) : ℝ := fderiv ℝ (fun ζ => fderiv ℝ Φ ζ u) η v
theorem hasDerivAt_line_at {Φ : X → ℝ} {p a : X} {t : ℝ} (h : DifferentiableAt ℝ Φ (p + t • a)) :
    HasDerivAt (fun t : ℝ => Φ (p + t • a)) (fderiv ℝ Φ (p + t • a) a) t := by
  have h0 : HasDerivAt (fun t : ℝ => p + t • a) a t := by
    have := ((hasDerivAt_id t).smul_const a).const_add p
    simpa using this
  exact h.hasFDerivAt.comp_hasDerivAt t h0
theorem differentiableAt_fderiv_apply_of_contDiffAt {Φ : X → ℝ} {p : X} (h : ContDiffAt ℝ 2 Φ p) (a : X) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ Φ ζ a) p := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) p := h.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun ζ => fderiv ℝ Φ ζ a) p := h1.clm_apply contDiffAt_const
  exact h2.differentiableAt (by norm_num)
theorem mixed_difference_eq (Φ : X → ℝ) (y a b : X) {s : ℝ} (hs : 0 < s)
    (hΦ : ∀ t ∈ Icc 0 s, ∀ t' ∈ Icc 0 s, ContDiffAt ℝ 2 Φ (y + t • a + t' • b)) :
    ∃ t ∈ Icc 0 s, ∃ t' ∈ Icc 0 s,
      Φ (y + s • a + s • b) + Φ y - Φ (y + s • a) - Φ (y + s • b)
        = s ^ 2 * secondDeriv Φ (y + t • a + t' • b) a b := by
  have hd : ∀ t ∈ Icc 0 s, ∀ t' ∈ Icc 0 s, DifferentiableAt ℝ Φ (y + t • a + t' • b) :=
    fun t ht t' ht' => (hΦ t ht t' ht').differentiableAt (by norm_num)
  have h0 : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl, hs.le⟩
  have h1 : s ∈ Icc 0 s := ⟨hs.le, le_rfl⟩
  set h : ℝ → ℝ := fun t => Φ (y + s • b + t • a) - Φ (y + t • a) with hh
  have comm : ∀ t t' : ℝ, y + t' • b + t • a = y + t • a + t' • b := fun t t' => by abel
  have hder : ∀ t ∈ Icc 0 s, HasDerivAt h
      (fderiv ℝ Φ (y + s • b + t • a) a - fderiv ℝ Φ (y + t • a) a) t := by
    intro t ht
    have e1 : DifferentiableAt ℝ Φ (y + s • b + t • a) := by
      rw [comm]; exact hd t ht s h1
    have e2 : DifferentiableAt ℝ Φ (y + t • a) := by
      have := hd t ht 0 h0
      simpa using this
    exact (hasDerivAt_line_at e1).sub (hasDerivAt_line_at e2)
  obtain ⟨c, hc, hc2⟩ := exists_hasDerivAt_eq_slope h
    (fun t => fderiv ℝ Φ (y + s • b + t • a) a - fderiv ℝ Φ (y + t • a) a) hs
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t (Ioo_subset_Icc_self ht))
  have hcI : c ∈ Icc 0 s := Ioo_subset_Icc_self hc
  set k : ℝ → ℝ := fun t' => fderiv ℝ Φ (y + c • a + t' • b) a with hk
  have kder : ∀ t' ∈ Icc 0 s, HasDerivAt k (secondDeriv Φ (y + c • a + t' • b) a b) t' := by
    intro t' ht'
    have e1 := differentiableAt_fderiv_apply_of_contDiffAt (hΦ c hcI t' ht') a
    exact hasDerivAt_line_at e1
  obtain ⟨c', hc', hc2'⟩ := exists_hasDerivAt_eq_slope k
    (fun t' => secondDeriv Φ (y + c • a + t' • b) a b) hs
    (fun t ht => (kder t ht).continuousAt.continuousWithinAt)
    (fun t ht => kder t (Ioo_subset_Icc_self ht))
  refine ⟨c, hcI, c', Ioo_subset_Icc_self hc', ?_⟩
  have hs0 : s ≠ 0 := hs.ne'
  have e3 : fderiv ℝ Φ (y + s • b + c • a) a - fderiv ℝ Φ (y + c • a) a = k s - k 0 := by
    simp only [hk, zero_smul, add_zero]
    rw [comm]
  have e4 : k s - k 0 = s * secondDeriv Φ (y + c • a + c' • b) a b := by
    rw [hc2']
    field_simp
    ring
  have e5 : h s - h 0 = s * (s * secondDeriv Φ (y + c • a + c' • b) a b) := by
    have : h s - h 0 = s * (fderiv ℝ Φ (y + s • b + c • a) a - fderiv ℝ Φ (y + c • a) a) := by
      rw [hc2]
      field_simp
      ring
    rw [this, e3, e4]
  have e6 : h s - h 0 = Φ (y + s • a + s • b) + Φ y - Φ (y + s • a) - Φ (y + s • b) := by
    simp only [hh, zero_smul, add_zero]
    rw [comm s s]
    ring
  rw [← e6, e5]
  ring
theorem plaquette_weight_estimate {v00 v10 v01 v11 vx Hx s ε₀ θ Hb : ℝ} (hε0 : 0 ≤ ε₀)
    (hD : |(v11 + v00 - v10 - v01) - s ^ 2 * Hx| ≤ ε₀ * s ^ 2) (hH : |Hx| + ε₀ ≤ Hb)
    (hβ : |vx - (v00 + v11) / 2| ≤ θ) (hθ : θ ≤ 1) (hs2 : s ^ 2 * Hb ≤ 1)
    (hbig : 3 / 2 * s ^ 2 * Hb ^ 2 + 2 * θ * Hb ≤ ε₀) :
    |(Real.exp (-(v10 + v01) / 2) - Real.exp (-(v00 + v11) / 2)) / 2 - s ^ 2 / 4 * Real.exp (-vx) * Hx|
      ≤ s ^ 2 / 4 * Real.exp (-vx) * (2 * ε₀) := by
  set D := v11 + v00 - v10 - v01 with hDdef
  set β := vx - (v00 + v11) / 2 with hβdef
  set t := D / 2 with ht
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hθ0 : 0 ≤ θ := le_trans (abs_nonneg _) hβ
  have hDabs : |D| ≤ s ^ 2 * Hb := by
    have h1 : |D| ≤ |D - s ^ 2 * Hx| + |s ^ 2 * Hx| := by
      have := abs_add_le (D - s ^ 2 * Hx) (s ^ 2 * Hx)
      simpa using this
    rw [abs_mul, abs_of_nonneg hs0] at h1
    nlinarith
  have ht1 : |t| ≤ 1 := by
    rw [ht, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have e1 := Real.abs_exp_sub_one_sub_id_le ht1
  have hβ1 : |β| ≤ 1 := le_trans hβ hθ
  have e2 := Real.abs_exp_sub_one_le hβ1
  have hexpb : Real.exp β ≤ 3 := by
    have := abs_le.mp e2
    linarith [this.2, hβ1]
  have main : |2 * (Real.exp (β + t) - Real.exp β) - s ^ 2 * Hx| ≤ 2 * ε₀ * s ^ 2 := by
    have id1 : 2 * (Real.exp (β + t) - Real.exp β) - s ^ 2 * Hx
        = 2 * Real.exp β * (Real.exp t - 1 - t) + (Real.exp β - 1) * D + (D - s ^ 2 * Hx) := by
      rw [Real.exp_add, ht]
      ring
    rw [id1]
    have b1 : |2 * Real.exp β * (Real.exp t - 1 - t)| ≤ 6 * t ^ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.exp β)]
      have : 2 * Real.exp β * |Real.exp t - 1 - t| ≤ 6 * |Real.exp t - 1 - t| := by
        have := abs_nonneg (Real.exp t - 1 - t)
        nlinarith
      nlinarith
    have b2 : |(Real.exp β - 1) * D| ≤ 2 * θ * (s ^ 2 * Hb) := by
      rw [abs_mul]
      have h3 : |Real.exp β - 1| ≤ 2 * θ := by linarith
      exact mul_le_mul h3 hDabs (abs_nonneg _) (by linarith)
    have b3 : t ^ 2 ≤ (s ^ 2 * Hb) ^ 2 / 4 := by
      have : t ^ 2 = D ^ 2 / 4 := by rw [ht]; ring
      rw [this]
      have : D ^ 2 ≤ (s ^ 2 * Hb) ^ 2 := by
        rw [← sq_abs D]
        exact pow_le_pow_left₀ (abs_nonneg _) hDabs 2
      linarith
    have hsum := abs_add_three (2 * Real.exp β * (Real.exp t - 1 - t)) ((Real.exp β - 1) * D) (D - s ^ 2 * Hx)
    have b4 : s ^ 2 * (3 / 2 * s ^ 2 * Hb ^ 2 + 2 * θ * Hb) ≤ s ^ 2 * ε₀ :=
      mul_le_mul_of_nonneg_left hbig hs0
    nlinarith
  have hα : Real.exp (-(v10 + v01) / 2) = Real.exp (-vx) * Real.exp (β + t) := by
    rw [← Real.exp_add]
    congr 1
    rw [hβdef, ht, hDdef]
    ring
  have hβe : Real.exp (-(v00 + v11) / 2) = Real.exp (-vx) * Real.exp β := by
    rw [← Real.exp_add]
    congr 1
    rw [hβdef]
    ring
  rw [hα, hβe]
  have id2 : (Real.exp (-vx) * Real.exp (β + t) - Real.exp (-vx) * Real.exp β) / 2
        - s ^ 2 / 4 * Real.exp (-vx) * Hx
      = Real.exp (-vx) / 4 * (2 * (Real.exp (β + t) - Real.exp β) - s ^ 2 * Hx) := by ring
  rw [id2, abs_mul, abs_of_pos (by positivity : 0 < Real.exp (-vx) / 4)]
  have := mul_le_mul_of_nonneg_left main (by positivity : 0 ≤ Real.exp (-vx) / 4)
  linarith
theorem line_weight_estimate {v0 v1 v2 Hx s ε₀ Hb : ℝ}
    (hD : |(v1 + v2 - 2 * v0) - s ^ 2 * Hx| ≤ ε₀ * s ^ 2) (hH : |Hx| + ε₀ ≤ Hb)
    (hs2 : s ^ 2 * Hb ≤ 1) (hbig : 3 / 2 * s ^ 2 * Hb ^ 2 ≤ ε₀) :
    s ^ 2 / 2 * (Hx - 2 * ε₀) ≤ 1 ∧
    Real.exp (-(v1 + v2) / 2) ≤ Real.exp (-v0) * (1 - s ^ 2 / 2 * (Hx - 2 * ε₀)) := by
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hε0 : 0 ≤ ε₀ := le_trans (by positivity) hbig
  set D := v1 + v2 - 2 * v0 with hDdef
  set θ₀ := s ^ 2 / 2 * (Hx - ε₀) with hθ₀
  have hHabs := abs_le.mp (le_trans (le_add_of_nonneg_right hε0) hH : |Hx| ≤ Hb)
  constructor
  · nlinarith
  have h1 : -D / 2 ≤ -θ₀ := by
    have := (abs_le.mp hD).1
    rw [hθ₀]
    nlinarith
  have h2 : |(-θ₀)| ≤ 1 := by
    rw [abs_neg, hθ₀, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 2 / 2)]
    have : |Hx - ε₀| ≤ Hb := by
      have := abs_sub Hx ε₀
      rw [abs_of_nonneg hε0] at this
      linarith
    nlinarith
  have h3 := Real.abs_exp_sub_one_sub_id_le h2
  have h4 : Real.exp (-θ₀) ≤ 1 + (-θ₀) + (-θ₀) ^ 2 := by
    have := (abs_le.mp h3).2
    linarith
  have h5 : (-θ₀) ^ 2 ≤ s ^ 2 / 2 * ε₀ := by
    have a1 : |θ₀| ≤ s ^ 2 / 2 * Hb := by
      rw [hθ₀, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 2 / 2)]
      have : |Hx - ε₀| ≤ Hb := by
        have := abs_sub Hx ε₀
        rw [abs_of_nonneg hε0] at this
        linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have a2 : (-θ₀) ^ 2 ≤ (s ^ 2 / 2 * Hb) ^ 2 := by
      rw [neg_sq, ← sq_abs θ₀]
      exact pow_le_pow_left₀ (abs_nonneg _) a1 2
    have a3 : s ^ 2 * (3 / 2 * s ^ 2 * Hb ^ 2) ≤ s ^ 2 * ε₀ := mul_le_mul_of_nonneg_left hbig hs0
    nlinarith
  have h6 : Real.exp (-(v1 + v2) / 2) = Real.exp (-v0) * Real.exp (-D / 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hDdef]
    ring
  rw [h6]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc Real.exp (-D / 2) ≤ Real.exp (-θ₀) := Real.exp_le_exp.mpr h1
    _ ≤ 1 + (-θ₀) + (-θ₀) ^ 2 := h4
    _ ≤ _ := by rw [hθ₀] at h5 ⊢; nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem contDiff_fderiv_apply_one {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (u : X) :
    ContDiff ℝ 1 (fun ζ => fderiv ℝ Φ ζ u) :=
  (hΦ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
theorem continuous_secondDeriv {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (u v : X) :
    Continuous fun η => secondDeriv Φ η u v :=
  ((contDiff_fderiv_apply_one hΦ u).continuous_fderiv (by norm_num)).clm_apply continuous_const
theorem mem_of_parallelogram {B : Set X} (hB : Convex ℝ B) {y a b : X} {s : ℝ} (hs : 0 < s)
    (h00 : y ∈ B) (h10 : y + s • a ∈ B) (h01 : y + s • b ∈ B) (h11 : y + s • a + s • b ∈ B)
    {t t' : ℝ} (ht : t ∈ Icc 0 s) (ht' : t' ∈ Icc 0 s) : y + t • a + t' • b ∈ B := by
  have hq : ∀ {t : ℝ}, t ∈ Icc 0 s → t / s ∈ Icc (0 : ℝ) 1 := fun {t} ht =>
    ⟨div_nonneg ht.1 hs.le, (div_le_one hs).mpr ht.2⟩
  have hsc : ∀ (t : ℝ) (v : X), t • v = (t / s) • (s • v) := fun t v => by
    rw [smul_smul, div_mul_cancel₀ _ hs.ne']
  have hP : y + t • a ∈ B := by
    rw [hsc t a]
    exact hB.add_smul_mem h00 h10 (hq ht)
  have hQ : y + t • a + s • b ∈ B := by
    have e : y + t • a + s • b = (y + s • b) + t • a := by abel
    rw [e, hsc t a]
    refine hB.add_smul_mem h01 ?_ (hq ht)
    have e2 : y + s • b + s • a = y + s • a + s • b := by abel
    rw [e2]
    exact h11
  rw [hsc t' b]
  exact hB.add_smul_mem hP hQ (hq ht')
theorem mixed_difference_close {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) {B : Set X} (hB : Convex ℝ B)
    {y a b : X} {s ε₀ : ℝ} (hs : 0 < s)
    (h00 : y ∈ B) (h10 : y + s • a ∈ B) (h01 : y + s • b ∈ B) (h11 : y + s • a + s • b ∈ B)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Icc 0 s) (hc₂ : c₂ ∈ Icc 0 s)
    (hU : ∀ ζ ∈ B, ∀ ζ' ∈ B, ‖ζ - ζ'‖ ≤ s * (‖a‖ + ‖b‖) → |secondDeriv Φ ζ a b - secondDeriv Φ ζ' a b| ≤ ε₀) :
    |(Φ (y + s • a + s • b) + Φ y - Φ (y + s • a) - Φ (y + s • b))
      - s ^ 2 * secondDeriv Φ (y + c₁ • a + c₂ • b) a b| ≤ ε₀ * s ^ 2 := by
  obtain ⟨t, ht, t', ht', e⟩ := mixed_difference_eq Φ y a b hs (fun _ _ _ _ => hΦ.contDiffAt)
  rw [e, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg s), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg s)
  refine hU _ (mem_of_parallelogram hB hs h00 h10 h01 h11 ht ht') _
    (mem_of_parallelogram hB hs h00 h10 h01 h11 hc₁ hc₂) ?_
  have e1 : y + t • a + t' • b - (y + c₁ • a + c₂ • b) = (t - c₁) • a + (t' - c₂) • b := by
    simp only [sub_smul]
    abel
  rw [e1]
  have n1 : |t - c₁| ≤ s := abs_le.mpr ⟨by linarith [ht.1, hc₁.2], by linarith [ht.2, hc₁.1]⟩
  have n2 : |t' - c₂| ≤ s := abs_le.mpr ⟨by linarith [ht'.1, hc₂.2], by linarith [ht'.2, hc₂.1]⟩
  calc ‖(t - c₁) • a + (t' - c₂) • b‖ ≤ ‖(t - c₁) • a‖ + ‖(t' - c₂) • b‖ := norm_add_le _ _
    _ = |t - c₁| * ‖a‖ + |t' - c₂| * ‖b‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ s * ‖a‖ + s * ‖b‖ := add_le_add (mul_le_mul_of_nonneg_right n1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))
    _ = _ := by ring
variable {J : Type} [Fintype J] [DecidableEq J]
theorem exists_small_step {η₀ ε₀ Dm Lp Hb : ℝ} (hη : 0 < η₀) (hε : 0 < ε₀) (hD : 0 ≤ Dm)
    (hL : 0 ≤ Lp) (hH : 0 ≤ Hb) : ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      s * (2 * Dm) < η₀ ∧ 2 * s * Dm * Lp ≤ 1 ∧ s ^ 2 * Hb ≤ 1 ∧
      3 / 2 * s ^ 2 * Hb ^ 2 + 2 * (2 * s * Dm * Lp) * Hb ≤ ε₀ := by
  have p1 : 0 ≤ Dm * Lp := mul_nonneg hD hL
  have p2 : 0 ≤ Dm * Lp * Hb := mul_nonneg p1 hH
  have p3 : 0 ≤ Hb ^ 2 := sq_nonneg _
  obtain ⟨A, hA, a1, a2, a3, a4⟩ : ∃ A : ℝ, 0 < A ∧ 2 * Dm ≤ A ∧ 2 * (Dm * Lp) ≤ A ∧ Hb ≤ A ∧
      3 / 2 * Hb ^ 2 + 4 * (Dm * Lp * Hb) ≤ A :=
    ⟨1 + 2 * Dm + 2 * (Dm * Lp) + Hb + (3 / 2 * Hb ^ 2 + 4 * (Dm * Lp * Hb)),
      by positivity, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨c, hc, c1, c2, c3⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ η₀ ∧ c ≤ ε₀ ∧ c ≤ 1 :=
    ⟨min η₀ (min ε₀ 1), lt_min hη (lt_min hε one_pos), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _), le_trans (min_le_right _ _) (min_le_right _ _)⟩
  refine ⟨min 1 (c / A), lt_min one_pos (div_pos hc hA), fun s hs hs₀ => ?_⟩
  have hs1 : s < 1 := lt_of_lt_of_le hs₀ (min_le_left _ _)
  have hsA : s * A < c := by
    have := lt_of_lt_of_le hs₀ (min_le_right _ _)
    rwa [lt_div_iff₀ hA] at this
  have hss : s ^ 2 ≤ s := by nlinarith
  have b1 := mul_le_mul_of_nonneg_left a1 hs.le
  have b2 := mul_le_mul_of_nonneg_left a2 hs.le
  have b3 := mul_le_mul_of_nonneg_left a3 hs.le
  have b4 := mul_le_mul_of_nonneg_left a4 hs.le
  have b5 := mul_le_mul_of_nonneg_right hss hH
  have b6 := mul_le_mul_of_nonneg_right hss p3
  refine ⟨by linarith, ?_, by linarith, ?_⟩
  · have : 2 * s * Dm * Lp = s * (2 * (Dm * Lp)) := by ring
    rw [this]
    linarith
  · have : 3 / 2 * s ^ 2 * Hb ^ 2 + 2 * (2 * s * Dm * Lp) * Hb
        = 3 / 2 * (s ^ 2 * Hb ^ 2) + s * (4 * (Dm * Lp * Hb)) := by ring
    rw [this]
    have e : s * (3 / 2 * Hb ^ 2 + 4 * (Dm * Lp * Hb))
        = 3 / 2 * (s * Hb ^ 2) + s * (4 * (Dm * Lp * Hb)) := by ring
    rw [e] at b4
    linarith
set_option maxHeartbeats 1000000 in
theorem hessian_grid_bounds {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (d : J → X) {B : Set X}
    (hBc : IsCompact B) (hBv : Convex ℝ B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → ∀ (G : Type) [AddCommGroup G] [Fintype G]
      (L : EdgeGrid G J) (x : G → X), (∀ k, x k ∈ B) →
      (∀ j k, L.mark j k = 1 → x (k + L.dir j) = x k + s • d j) →
      L.PlaquetteHessBound (fun k => Φ (x k)) (fun k i j => secondDeriv Φ (x k) (d i) (d j)) s δ ∧
      L.LineHessBound (fun k => Φ (x k)) (fun k i j => secondDeriv Φ (x k) (d i) (d j)) s δ := by
  set ε₀ := δ / 2 with hε₀
  have hε₀p : 0 < ε₀ := by positivity
  have hδ2 : 2 * ε₀ = δ := by rw [hε₀]; ring
  set F : X → J → J → ℝ := fun ζ i j => secondDeriv Φ ζ (d i) (d j) with hF
  have hFc : Continuous F := continuous_pi fun i => continuous_pi fun j => continuous_secondDeriv hΦ _ _
  obtain ⟨η₀, hη₀, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (hBc.uniformContinuousOn_of_continuous hFc.continuousOn) ε₀ hε₀p
  obtain ⟨C, hC⟩ := hBc.exists_bound_of_continuousOn hFc.continuousOn
  have hfd : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
  obtain ⟨C', hC'⟩ := hBc.exists_bound_of_continuousOn hfd.continuousOn
  set Dm : ℝ := ∑ j, ‖d j‖ with hDm
  have hDm0 : 0 ≤ Dm := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hdj : ∀ j, ‖d j‖ ≤ Dm := fun j =>
    Finset.single_le_sum (f := fun j => ‖d j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  set Hb := |C| + ε₀ with hHb
  have hHb0 : 0 ≤ Hb := by positivity
  set Lp := |C'| with hLp
  have hLp0 : 0 ≤ Lp := abs_nonneg _
  obtain ⟨s₀, hs₀p, hs₀⟩ := exists_small_step hη₀ hε₀p hDm0 hLp0 hHb0
  refine ⟨s₀, hs₀p, fun s hs hs₀' G _ _ L x hxB hstep => ?_⟩
  obtain ⟨f1, f2, f3, f4⟩ := hs₀ s hs hs₀'
  set θ := 2 * s * Dm * Lp with hθ
  have f5 : 3 / 2 * s ^ 2 * Hb ^ 2 ≤ ε₀ := by
    have : 0 ≤ 2 * θ * Hb := by rw [hθ]; positivity
    linarith
  have hent : ∀ ζ ∈ B, ∀ i j, |F ζ i j| ≤ |C| := by
    intro ζ hζ i j
    have h1 : ‖F ζ i j‖ ≤ ‖F ζ i‖ := norm_le_pi_norm (F ζ i) j
    have h2 : ‖F ζ i‖ ≤ ‖F ζ‖ := norm_le_pi_norm (F ζ) i
    have h3 := hC ζ hζ
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self C]
  have hUU : ∀ i j, ∀ ζ ∈ B, ∀ ζ' ∈ B, ‖ζ - ζ'‖ ≤ s * (‖d i‖ + ‖d j‖) →
      |secondDeriv Φ ζ (d i) (d j) - secondDeriv Φ ζ' (d i) (d j)| ≤ ε₀ := by
    intro i j ζ hζ ζ' hζ' hn
    have h1 : dist ζ ζ' < η₀ := by
      rw [dist_eq_norm]
      have : s * (‖d i‖ + ‖d j‖) ≤ s * (2 * Dm) :=
        mul_le_mul_of_nonneg_left (by linarith [hdj i, hdj j]) hs.le
      linarith
    have h2 := hU ζ hζ ζ' hζ' h1
    have h3 : dist (F ζ i j) (F ζ' i j) ≤ dist (F ζ) (F ζ') :=
      le_trans (dist_le_pi_dist (F ζ i) (F ζ' i) j) (dist_le_pi_dist (F ζ) (F ζ') i)
    rw [Real.dist_eq] at h3
    exact le_trans h3 h2.le
  have hLip : ∀ p ∈ B, ∀ q ∈ B, ‖p - q‖ ≤ s * (2 * Dm) → |Φ p - Φ q| ≤ θ := by
    intro p hp q hq hn
    have h1 := hBv.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hΦ.differentiable (by norm_num)) z) (fun z hz => le_trans (hC' z hz) (le_abs_self C')) hq hp
    rw [Real.norm_eq_abs] at h1
    have h2 : |C'| * ‖p - q‖ ≤ |C'| * (s * (2 * Dm)) := mul_le_mul_of_nonneg_left hn hLp0
    rw [hθ]
    nlinarith
  have h00s : ∀ {t : ℝ}, t ∈ ({0, s} : Set ℝ) → t ∈ Icc 0 s := by
    intro t ht
    rcases ht with rfl | rfl
    · exact ⟨le_rfl, hs.le⟩
    · exact ⟨hs.le, le_rfl⟩
  have hcorner : ∀ i j, i ≠ j → ∀ k, L.mark i k = 1 → L.mark j k = 1 → ∀ c₁ c₂ : ℝ,
      c₁ ∈ ({0, s} : Set ℝ) → c₂ ∈ ({0, s} : Set ℝ) → ∀ z, x z = x k + c₁ • d i + c₂ • d j →
      |L.plaqHalfDiff (fun k => Φ (x k)) i j k - s ^ 2 / 4 * EdgeGrid.siteMass (fun k => Φ (x k)) z * secondDeriv Φ (x z) (d i) (d j)|
        ≤ s ^ 2 / 4 * EdgeGrid.siteMass (fun k => Φ (x k)) z * δ := by
    intro i j hij k hi hj c₁ c₂ hc₁ hc₂ z hz
    have e10 : x (k + L.dir i) = x k + s • d i := hstep i k hi
    have e01 : x (k + L.dir j) = x k + s • d j := hstep j k hj
    have e11 : x (k + L.dir i + L.dir j) = x k + s • d i + s • d j := by
      rw [hstep j (k + L.dir i) (by rw [L.mark_add_dir j i k hij.symm]; exact hj), e10]
    have m00 := hxB k
    have m10 := hxB (k + L.dir i)
    have m01 := hxB (k + L.dir j)
    have m11 := hxB (k + L.dir i + L.dir j)
    rw [e10] at m10
    rw [e01] at m01
    rw [e11] at m11
    have hD := mixed_difference_close hΦ hBv hs m00 m10 m01 m11 (h00s hc₁) (h00s hc₂) (hUU i j)
    rw [← hz, ← e11, ← e10, ← e01] at hD
    have hnear : ∀ c₃ c₄ : ℝ, c₃ ∈ ({0, s} : Set ℝ) → c₄ ∈ ({0, s} : Set ℝ) →
        ‖x z - (x k + c₃ • d i + c₄ • d j)‖ ≤ s * (2 * Dm) := by
      intro c₃ c₄ h3 h4
      have h5 := h00s hc₁
      have h6 := h00s hc₂
      have h7 := h00s h3
      have h8 := h00s h4
      have e : x z - (x k + c₃ • d i + c₄ • d j) = (c₁ - c₃) • d i + (c₂ - c₄) • d j := by
        rw [hz]
        simp only [sub_smul]
        abel
      rw [e]
      have n1 : |c₁ - c₃| ≤ s := abs_le.mpr ⟨by linarith [h5.1, h7.2], by linarith [h5.2, h7.1]⟩
      have n2 : |c₂ - c₄| ≤ s := abs_le.mpr ⟨by linarith [h6.1, h8.2], by linarith [h6.2, h8.1]⟩
      calc ‖(c₁ - c₃) • d i + (c₂ - c₄) • d j‖ ≤ ‖(c₁ - c₃) • d i‖ + ‖(c₂ - c₄) • d j‖ := norm_add_le _ _
        _ = |c₁ - c₃| * ‖d i‖ + |c₂ - c₄| * ‖d j‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ s * Dm + s * Dm := add_le_add
            (mul_le_mul n1 (hdj i) (norm_nonneg _) hs.le) (mul_le_mul n2 (hdj j) (norm_nonneg _) hs.le)
        _ = _ := by ring
    have hβ : |Φ (x z) - (Φ (x k) + Φ (x (k + L.dir i + L.dir j))) / 2| ≤ θ := by
      have g1 := hLip _ (hxB z) _ (hxB k) (by
        have := hnear 0 0 (by simp) (by simp)
        simpa using this)
      have g2 := hLip _ (hxB z) _ (hxB (k + L.dir i + L.dir j)) (by
        have := hnear s s (by simp) (by simp)
        rw [e11]
        exact this)
      have a1 := abs_le.mp g1
      have a2 := abs_le.mp g2
      exact abs_le.mpr ⟨by linarith [a1.1, a2.1], by linarith [a1.2, a2.2]⟩
    have hHx : |secondDeriv Φ (x z) (d i) (d j)| + ε₀ ≤ Hb := by
      have := hent (x z) (hxB z) i j
      simp only [hF] at this
      rw [hHb]
      linarith
    have res := plaquette_weight_estimate hε₀p.le hD hHx hβ f2 f3 f4
    rw [hδ2] at res
    exact res
  constructor
  · intro i j hij k hi hj z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hcorner i j hij z hi hj 0 0 (by simp) (by simp) z (by simp)
    · exact hcorner i j hij k hi hj s 0 (by simp) (by simp) _ (by simp [hstep i k hi])
    · exact hcorner i j hij k hi hj 0 s (by simp) (by simp) _ (by simp [hstep j k hj])
    · refine hcorner i j hij k hi hj s s (by simp) (by simp) _ ?_
      rw [hstep j (k + L.dir i) (by rw [L.mark_add_dir j i k hij.symm]; exact hj), hstep i k hi]
  · intro j z
    have hH := hent (x z) (hxB z) j j
    simp only [hF] at hH
    refine ⟨?_, fun h1 h2 => ?_⟩
    · have a1 := (abs_le.mp (le_trans hH (le_refl _))).2
      have a2 : 0 ≤ s ^ 2 := sq_nonneg s
      have a3 : secondDeriv Φ (x z) (d j) (d j) - δ ≤ Hb := by rw [hHb]; linarith [hδ]
      have a4 := mul_le_mul_of_nonneg_left a3 a2
      nlinarith
    · have e0 : x z = x (z - L.dir j) + s • d j := by
        have := hstep j (z - L.dir j) h2
        rwa [sub_add_cancel] at this
      have e1 : x (z + L.dir j) = x z + s • d j := hstep j z h1
      have m0 := hxB (z - L.dir j)
      have m1 := hxB z
      have m2 := hxB (z + L.dir j)
      have m1' : x (z - L.dir j) + s • d j ∈ B := by rw [← e0]; exact m1
      have m2' : x (z - L.dir j) + s • d j + s • d j ∈ B := by rw [← e0, ← e1]; exact m2
      have hD := mixed_difference_close hΦ hBv hs m0 m1' m1' m2' (c₁ := s) (c₂ := 0)
        ⟨hs.le, le_rfl⟩ ⟨le_rfl, hs.le⟩ (hUU j j)
      rw [zero_smul, add_zero, ← e0, ← e1] at hD
      have hD' : |(Φ (x (z + L.dir j)) + Φ (x (z - L.dir j)) - 2 * Φ (x z))
          - s ^ 2 * secondDeriv Φ (x z) (d j) (d j)| ≤ ε₀ * s ^ 2 := by
        have e2 : Φ (x (z + L.dir j)) + Φ (x (z - L.dir j)) - 2 * Φ (x z)
            = Φ (x (z + L.dir j)) + Φ (x (z - L.dir j)) - Φ (x z) - Φ (x z) := by ring
        rw [e2]
        exact hD
      have hHx : |secondDeriv Φ (x z) (d j) (d j)| + ε₀ ≤ Hb := by rw [hHb]; linarith
      have res := (line_weight_estimate hD' hHx f3 f5).2
      rw [hδ2] at res
      exact res
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set MeasureTheory Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {J : Type} [Fintype J] [DecidableEq J]
def boxEdgeGrid (J : Type) [DecidableEq J] (n : ℕ) : EdgeGrid (J → ZMod n) J where
  dir j := Pi.single j 1
  mark j k := if k j = -1 then 0 else 1
  mark_cases j k := by
    by_cases h : k j = -1 <;> simp [h]
  mark_add_dir i j k h := by
    simp [Pi.single_eq_of_ne h]
theorem boxEdgeGrid_mark_eq_one {n : ℕ} {j : J} {k : J → ZMod n} :
    (boxEdgeGrid J n).mark j k = 1 ↔ k j ≠ -1 := by
  simp only [boxEdgeGrid]
  by_cases h : k j = -1 <;> simp [h]
theorem zmod_val_add_one_of_ne {n : ℕ} [NeZero n] {a : ZMod n} (h : a ≠ -1) : (a + 1).val = a.val + 1 := by
  have hlt := ZMod.val_lt a
  have hne : a.val + 1 ≠ n := by
    intro he
    apply h
    have h1 : ((a.val + 1 : ℕ) : ZMod n) = 0 := by rw [he]; simp
    have h2 : a + 1 = 0 := by
      have := h1
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    exact eq_neg_of_add_eq_zero_left h2
  have hlt2 : a.val + 1 < n := by omega
  have h1 : (1 : ZMod n).val = 1 := by
    have : 1 < n := by omega
    have : Fact (1 < n) := ⟨this⟩
    exact ZMod.val_one n
  rw [ZMod.val_add_of_lt (by rw [h1]; exact hlt2), h1]
theorem boxEdgeGrid_connected {n : ℕ} [NeZero n] (u : (J → ZMod n) → ℝ)
    (hu : ∀ j k, (boxEdgeGrid J n).mark j k = 1 → (boxEdgeGrid J n).diff u j k = 0) (k k' : J → ZMod n) :
    u k = u k' := by
  have hstep : ∀ j (p : J → ZMod n), p j ≠ -1 → u (p + (Pi.single j 1 : J → ZMod n)) = u p := by
    intro j p hp
    have := hu j p (boxEdgeGrid_mark_eq_one.mpr hp)
    simp only [EdgeGrid.diff, boxEdgeGrid] at this
    linarith
  have hwalk : ∀ j (p : J → ZMod n), p j = 0 → ∀ t : ℕ, t < n →
      u (p + t • (Pi.single j 1 : J → ZMod n)) = u p := by
    intro j p hp t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 : (p + t • (Pi.single j 1 : J → ZMod n)) j ≠ -1 := by
        have hv : (t • (Pi.single j 1 : J → ZMod n)) j = (t : ZMod n) := by
          rw [Pi.smul_apply, Pi.single_eq_same]
          simp
        rw [Pi.add_apply, hv, hp, zero_add]
        intro he
        have h3 : ((t + 1 : ℕ) : ZMod n) = 0 := by
          push_cast
          rw [he]
          ring
        rw [ZMod.natCast_eq_zero_iff] at h3
        exact absurd (Nat.le_of_dvd (by omega) h3) (by omega)
      have h4 := hstep j _ h2
      rw [← h1, ← h4]
      congr 1
      rw [succ_nsmul, add_assoc]
  have hall : ∀ j (p : J → ZMod n), u (p + (Pi.single j 1 : J → ZMod n)) = u p := by
    intro j p
    by_cases hp : p j = -1
    · have hq : (p + (Pi.single j 1 : J → ZMod n)) j = 0 := by simp [hp]
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      have h1 := hwalk j _ hq (n - 1) (by omega)
      have h2 : p + (Pi.single j 1 : J → ZMod n) + (n - 1) • (Pi.single j 1 : J → ZMod n) = p := by
        have h3 : n • (Pi.single j 1 : J → ZMod n) = (0 : J → ZMod n) := by
          funext i
          by_cases hi : i = j
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        have h4 : (Pi.single j 1 : J → ZMod n) + (n - 1) • (Pi.single j 1 : J → ZMod n) = (0 : J → ZMod n) := by
          rw [← h3]
          have e : (n - 1) + 1 = n := by omega
          calc (Pi.single j 1 : J → ZMod n) + (n - 1) • (Pi.single j 1 : J → ZMod n)
              = ((n - 1) + 1) • (Pi.single j 1 : J → ZMod n) := by rw [succ_nsmul, add_comm]
            _ = n • (Pi.single j 1 : J → ZMod n) := congrArg (· • (Pi.single j 1 : J → ZMod n)) e
        rw [add_assoc, h4, add_zero]
      rw [h2] at h1
      exact h1.symm
    · exact hstep j p hp
  have hmul : ∀ j (t : ℕ) (p : J → ZMod n), u (p + t • (Pi.single j 1 : J → ZMod n)) = u p := by
    intro j t
    induction t with
    | zero => intro p; simp
    | succ t ih =>
      intro p
      rw [succ_nsmul, ← add_assoc, hall]
      exact ih p
  have hsingle : ∀ j (c : ZMod n) (p : J → ZMod n), u (p + (Pi.single j c : J → ZMod n)) = u p := by
    intro j c p
    have h1 : (Pi.single j c : J → ZMod n) = c.val • (Pi.single j 1 : J → ZMod n) := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [Pi.single_eq_of_ne hi]
    rw [h1]
    exact hmul j _ p
  have hzero : ∀ p : J → ZMod n, u p = u 0 := by
    intro p
    have hs : ∀ S : Finset J, u (∑ j ∈ S, Pi.single j (p j)) = u 0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih =>
        rw [Finset.sum_insert ha, add_comm, hsingle]
        exact ih
    have := hs Finset.univ
    rwa [Finset.univ_sum_single] at this
  rw [hzero k, hzero k']
def cellSide (R : ℝ) (n : ℕ) : ℝ := 2 * R / n
def cellCorner (R : ℝ) (n : ℕ) (k : J → ZMod n) (j : J) : ℝ := -R + ((k j).val : ℝ) * cellSide R n
def cellCentreAt (R : ℝ) (n : ℕ) (k : J → ZMod n) (j : J) : ℝ := cellCorner R n k j + cellSide R n / 2
theorem cellCentreAt_step {R : ℝ} {n : ℕ} [NeZero n] {j : J} {k : J → ZMod n} (h : (boxEdgeGrid J n).mark j k = 1) :
    cellCentreAt R n (k + (boxEdgeGrid J n).dir j) = cellCentreAt R n k + cellSide R n • Pi.single j 1 := by
  have hk := boxEdgeGrid_mark_eq_one.mp h
  funext i
  by_cases hi : i = j
  · subst hi
    simp only [cellCentreAt, cellCorner, boxEdgeGrid, Pi.add_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [zmod_val_add_one_of_ne hk]
    push_cast
    ring
  · simp [cellCentreAt, cellCorner, boxEdgeGrid, Pi.single_eq_of_ne hi]
def halfOpenBox (J : Type) (R : ℝ) : Set (J → ℝ) := Set.pi univ fun _ => Ioc (-R) R
def gridCell (R : ℝ) (n : ℕ) (k : J → ZMod n) : Set (J → ℝ) :=
  Set.pi univ fun j => Ioc (cellCorner R n k j) (cellCorner R n k j + cellSide R n)
theorem measurableSet_gridCell (R : ℝ) (n : ℕ) (k : J → ZMod n) : MeasurableSet (gridCell R n k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc
theorem measurableSet_halfOpenBox (R : ℝ) : MeasurableSet (halfOpenBox J R) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc
theorem cellSide_pos {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) : 0 < cellSide R n := by
  unfold cellSide
  positivity
theorem natCast_mul_cellSide {R : ℝ} {n : ℕ} (hn : 0 < n) : (n : ℝ) * cellSide R n = 2 * R := by
  unfold cellSide
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
theorem gridCell_disjoint {R : ℝ} (hR : 0 < R) {n : ℕ} [NeZero n] {k k' : J → ZMod n} (h : k ≠ k') :
    Disjoint (gridCell R n k) (gridCell R n k') := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hs := cellSide_pos hR hn
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  rw [Set.disjoint_left]
  intro y hy hy'
  have h1 := hy j (mem_univ j)
  have h2 := hy' j (mem_univ j)
  have hv : (k j).val ≠ (k' j).val := fun e => hj (ZMod.val_injective n e)
  simp only [cellCorner] at h1 h2
  rcases Nat.lt_or_gt_of_ne hv with hl | hl
  · have : ((k j).val : ℝ) + 1 ≤ (k' j).val := by exact_mod_cast hl
    nlinarith [h1.2, h2.1]
  · have : ((k' j).val : ℝ) + 1 ≤ (k j).val := by exact_mod_cast hl
    nlinarith [h1.1, h2.2]
theorem iUnion_gridCell {R : ℝ} (hR : 0 < R) {n : ℕ} [NeZero n] :
    ⋃ k : J → ZMod n, gridCell R n k = halfOpenBox J R := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hs := cellSide_pos hR hn
  have hmul := natCast_mul_cellSide (R := R) hn
  ext y
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ j _
    have h1 := hk j (mem_univ j)
    simp only [cellCorner] at h1
    have hv : ((k j).val : ℝ) + 1 ≤ n := by exact_mod_cast ZMod.val_lt (k j)
    constructor
    · nlinarith [h1.1]
    · nlinarith [h1.2]
  · intro hy
    have key : ∀ j, ∃ t : ZMod n, y j ∈ Ioc (-R + (t.val : ℝ) * cellSide R n)
        (-R + (t.val : ℝ) * cellSide R n + cellSide R n) := by
      intro j
      have h1 := hy j (mem_univ j)
      set r := (y j + R) / cellSide R n with hr
      have hr0 : 0 < r := div_pos (by linarith [h1.1]) hs
      have hrn : r ≤ n := by
        rw [hr, div_le_iff₀ hs]
        nlinarith [h1.2]
      have hc1 : 0 < ⌈r⌉₊ := Nat.ceil_pos.mpr hr0
      have hc2 : ⌈r⌉₊ ≤ n := Nat.ceil_le.mpr hrn
      have hval : (((⌈r⌉₊ - 1 : ℕ) : ZMod n)).val = ⌈r⌉₊ - 1 :=
        ZMod.val_cast_of_lt (by omega)
      refine ⟨((⌈r⌉₊ - 1 : ℕ) : ZMod n), ?_⟩
      rw [hval]
      have e1 : (((⌈r⌉₊ - 1 : ℕ)) : ℝ) = (⌈r⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hc1]
        simp
      rw [e1]
      have g1 : (⌈r⌉₊ : ℝ) - 1 < r := by
        have := Nat.ceil_lt_add_one hr0.le
        linarith
      have g2 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
      have g3 : y j = r * cellSide R n - R := by
        rw [hr, div_mul_cancel₀ _ hs.ne']
        ring
      constructor
      · rw [g3]
        nlinarith
      · rw [g3]
        nlinarith
    choose t ht using key
    exact ⟨t, fun j _ => ht j⟩
theorem volume_gridCell {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) (k : J → ZMod n) :
    volume.real (gridCell R n k) = cellSide R n ^ Fintype.card J := by
  have hs := cellSide_pos hR hn
  unfold gridCell
  rw [measureReal_def, Real.volume_pi_Ioc (a := cellCorner R n k) (b := fun j => cellCorner R n k j + cellSide R n)]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hs.le]
theorem volume_gridCell_lt_top {R : ℝ} {n : ℕ} (k : J → ZMod n) : volume (gridCell R n k) < ⊤ := by
  unfold gridCell
  rw [Real.volume_pi_Ioc (a := cellCorner R n k) (b := fun j => cellCorner R n k j + cellSide R n)]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
theorem riemann_sum_tendsto {R : ℝ} (hR : 0 < R) {F : (J → ℝ) → ℝ} (hF : Continuous F) :
    Tendsto (fun n : ℕ => cellSide R (n + 1) ^ Fintype.card J *
        ∑ k : J → ZMod (n + 1), F (cellCentreAt R (n + 1) k)) atTop (𝓝 (∫ y in halfOpenBox J R, F y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : Set (J → ℝ) := Set.pi univ fun _ => Icc (-R) R with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  set c := Fintype.card J
  set ω := ε / (2 * ((2 * R) ^ c + 1)) with hω
  have hωp : 0 < ω := by positivity
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hF.continuousOn) ω hωp
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * R / η)
  refine ⟨n₀, fun n hn => ?_⟩
  set N := n + 1 with hN
  have hNp : 0 < N := Nat.succ_pos n
  have : NeZero N := ⟨hNp.ne'⟩
  have hs := cellSide_pos hR hNp
  have hmul := natCast_mul_cellSide (R := R) hNp
  have hsη : cellSide R N < η := by
    have h1 : 2 * R / η < N := by
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      have : (n : ℝ) < N := by rw [hN]; push_cast; linarith
      linarith
    rw [div_lt_iff₀ hη] at h1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
    rw [← hmul] at h1
    exact lt_of_mul_lt_mul_left h1 hNr.le
  have hcell : ∀ k : J → ZMod N, IntegrableOn F (gridCell R N k) := fun k => by
    have hsub : gridCell R N k ⊆ K := by
      intro y hy j _
      have h1 := hy j (mem_univ j)
      have h2 : gridCell R N k ⊆ halfOpenBox J R := by
        rw [← iUnion_gridCell (J := J) hR (n := N)]
        exact subset_iUnion (fun k => gridCell R N k) k
      have h3 := h2 hy j (mem_univ j)
      exact ⟨h3.1.le, h3.2⟩
    exact (hF.continuousOn.integrableOn_compact hKc).mono_set hsub
  have hint : ∫ y in halfOpenBox J R, F y = ∑ k : J → ZMod N, ∫ y in gridCell R N k, F y := by
    rw [← iUnion_gridCell (J := J) hR (n := N)]
    exact integral_iUnion_fintype (fun k => measurableSet_gridCell R N k)
      (fun k k' h => gridCell_disjoint hR h) hcell
  have hcenter : ∀ k : J → ZMod N, cellCentreAt R N k ∈ K := by
    intro k j _
    have hv : ((k j).val : ℝ) + 1 ≤ N := by exact_mod_cast ZMod.val_lt (k j)
    simp only [cellCentreAt, cellCorner]
    constructor <;> nlinarith
  have hone : ∀ k : J → ZMod N, |(∫ y in gridCell R N k, F y) - cellSide R N ^ c * F (cellCentreAt R N k)|
      ≤ ω * cellSide R N ^ c := by
    intro k
    have hv := volume_gridCell (J := J) hR hNp k
    have e1 : (∫ y in gridCell R N k, F y) - cellSide R N ^ c * F (cellCentreAt R N k)
        = ∫ y in gridCell R N k, (F y - F (cellCentreAt R N k)) := by
      rw [integral_sub (hcell k) (integrableOn_const (volume_gridCell_lt_top k).ne), setIntegral_const, hv]
      simp [smul_eq_mul, c]
    rw [e1, ← Real.norm_eq_abs, ← hv]
    refine norm_setIntegral_le_of_norm_le_const (volume_gridCell_lt_top k) fun y hy => ?_
    have hyK : y ∈ K := by
      intro j _
      have h2 : gridCell R N k ⊆ halfOpenBox J R := by
        rw [← iUnion_gridCell (J := J) hR (n := N)]
        exact subset_iUnion (fun k => gridCell R N k) k
      have h3 := h2 hy j (mem_univ j)
      exact ⟨h3.1.le, h3.2⟩
    have hd : dist y (cellCentreAt R N k) < η := by
      rw [dist_pi_lt_iff hη]
      intro j
      have h1 := hy j (mem_univ j)
      rw [Real.dist_eq]
      simp only [cellCentreAt]
      refine lt_of_le_of_lt (abs_le.mpr ⟨?_, ?_⟩) hsη <;> linarith [h1.1, h1.2]
    have := hU y hyK _ (hcenter k) hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  rw [Real.dist_eq, hint, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hcard : (∑ _k : J → ZMod N, ω * cellSide R N ^ c) = ω * (2 * R) ^ c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, nsmul_eq_mul, ← hmul, mul_pow]
    push_cast
    ring
  calc |∑ k : J → ZMod N, (cellSide R N ^ c * F (cellCentreAt R N k) - ∫ y in gridCell R N k, F y)|
      ≤ ∑ k : J → ZMod N, |cellSide R N ^ c * F (cellCentreAt R N k) - ∫ y in gridCell R N k, F y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : J → ZMod N, ω * cellSide R N ^ c := Finset.sum_le_sum fun k _ => by
        rw [abs_sub_comm]
        exact hone k
    _ = ω * (2 * R) ^ c := hcard
    _ < ε := by
        have hp : 0 < (2 * R) ^ c := by positivity
        rw [hω, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set MeasureTheory Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {J : Type} [Fintype J] [DecidableEq J]
theorem edge_difference_sq_le {f : X → ℝ} (hf : ContDiff ℝ 1 f) (d : J → X) {B : Set X}
    (hBc : IsCompact B) (hBv : Convex ℝ B) {δ₁ : ℝ} (hδ : 0 < δ₁) :
    ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s : ℝ, 0 < s → s < s₁ → ∀ j, ∀ y ∈ B, y + s • d j ∈ B →
      (f (y + s • d j) - f y) ^ 2 ≤ s ^ 2 * ((fderiv ℝ f y (d j)) ^ 2 + δ₁) ∧
      (f (y + s • d j) - f y) ^ 2 ≤ s ^ 2 * ((fderiv ℝ f (y + s • d j) (d j)) ^ 2 + δ₁) := by
  set F : X → J → ℝ := fun ζ j => (fderiv ℝ f ζ (d j)) ^ 2 with hF
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hFc : Continuous F := continuous_pi fun j => (hfd.clm_apply continuous_const).pow 2
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (hBc.uniformContinuousOn_of_continuous hFc.continuousOn) δ₁ hδ
  set Dm : ℝ := ∑ j, ‖d j‖ with hDm
  have hdj : ∀ j, ‖d j‖ ≤ Dm := fun j =>
    Finset.single_le_sum (f := fun j => ‖d j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  refine ⟨η / (Dm + 1), by positivity, fun s hs hs₁ j y hy hy' => ?_⟩
  have hsD : s * ‖d j‖ < η := by
    rw [lt_div_iff₀ (by positivity)] at hs₁
    have : s * ‖d j‖ ≤ s * (Dm + 1) := mul_le_mul_of_nonneg_left (by linarith [hdj j]) hs.le
    linarith
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (y + t • d j)) (fderiv ℝ f (y + t • d j) (d j)) t :=
    fun t => hasDerivAt_line_at ((hf.differentiable (by norm_num)) _)
  obtain ⟨t, ht, e⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (y + t • d j))
    (fun t => fderiv ℝ f (y + t • d j) (d j)) hs
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
  have hs0 : s ≠ 0 := hs.ne'
  simp only [zero_smul, add_zero, sub_zero] at e
  have e2 : f (y + s • d j) - f y = s * fderiv ℝ f (y + t • d j) (d j) := by
    rw [e]
    field_simp
  have hζ : y + t • d j ∈ B := by
    have h1 : t / s ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1.le hs.le, (div_le_one hs).mpr ht.2.le⟩
    have h2 := hBv.add_smul_mem hy hy' h1
    rwa [smul_smul, div_mul_cancel₀ _ hs0] at h2
  have near : ∀ z ∈ B, ‖y + t • d j - z‖ ≤ s * ‖d j‖ → F (y + t • d j) j ≤ F z j + δ₁ := by
    intro z hz hn
    have h1 : dist (y + t • d j) z < η := by
      rw [dist_eq_norm]
      linarith
    have h2 := hU _ hζ z hz h1
    have h3 : dist (F (y + t • d j) j) (F z j) ≤ dist (F (y + t • d j)) (F z) :=
      dist_le_pi_dist _ _ j
    rw [Real.dist_eq] at h3
    have := (abs_le.mp (le_trans h3 h2.le)).2
    linarith
  have n1 : ‖y + t • d j - y‖ ≤ s * ‖d j‖ := by
    have : y + t • d j - y = t • d j := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
  have n2 : ‖y + t • d j - (y + s • d j)‖ ≤ s * ‖d j‖ := by
    have : y + t • d j - (y + s • d j) = (t - s) • d j := by
      rw [sub_smul]
      abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith [ht.2])]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
  have hsq : 0 ≤ s ^ 2 := sq_nonneg s
  rw [e2, mul_pow]
  exact ⟨mul_le_mul_of_nonneg_left (near y hy n1) hsq,
    mul_le_mul_of_nonneg_left (near _ hy' n2) hsq⟩
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def coordDir (Em : (J → ℝ) →L[ℝ] X) (j : J) : X := Em (Pi.single j 1)
def bondGradSq (β : J → ι) (Em : (J → ℝ) →L[ℝ] X) (f : X → ℝ) (b : ι) (x : X) : ℝ :=
  ∑ j, if β j = b then (fderiv ℝ f x (coordDir Em j)) ^ 2 else 0
def gridMean (Em : (J → ℝ) →L[ℝ] X) (Φ : X → ℝ) (R : ℝ) (N : ℕ) [NeZero N] (h : X → ℝ) : ℝ :=
  (∑ k : J → ZMod N, Real.exp (-Φ (Em (cellCentreAt R N k))) * h (Em (cellCentreAt R N k))) /
    ∑ k : J → ZMod N, Real.exp (-Φ (Em (cellCentreAt R N k)))
def boxMean (Em : (J → ℝ) →L[ℝ] X) (Φ : X → ℝ) (R : ℝ) (h : X → ℝ) : ℝ :=
  (∫ y in halfOpenBox J R, Real.exp (-Φ (Em y)) * h (Em y)) / ∫ y in halfOpenBox J R, Real.exp (-Φ (Em y))
def closedCube (J : Type) (R : ℝ) : Set (J → ℝ) := Set.pi univ fun _ => Icc (-R) R
theorem isCompact_closedCube (R : ℝ) : IsCompact (closedCube J R) := isCompact_univ_pi fun _ => isCompact_Icc
theorem convex_closedCube (R : ℝ) : Convex ℝ (closedCube J R) := convex_pi fun _ _ => convex_Icc _ _
theorem halfOpenBox_subset_closedCube (R : ℝ) : halfOpenBox J R ⊆ closedCube J R := fun _ hy j hj =>
  ⟨(hy j hj).1.le, (hy j hj).2⟩
theorem cellCentreAt_mem_closedCube {R : ℝ} (hR : 0 < R) {N : ℕ} [NeZero N] (k : J → ZMod N) : cellCentreAt R N k ∈ closedCube J R := by
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hs := cellSide_pos hR hNp
  have hmul := natCast_mul_cellSide (R := R) hNp
  intro j _
  have hv : ((k j).val : ℝ) + 1 ≤ N := by exact_mod_cast ZMod.val_lt (k j)
  simp only [cellCentreAt, cellCorner]
  constructor <;> nlinarith
theorem integrableOn_halfOpenBox {F : (J → ℝ) → ℝ} (hF : Continuous F) (R : ℝ) : IntegrableOn F (halfOpenBox J R) :=
  (hF.continuousOn.integrableOn_compact (isCompact_closedCube R)).mono_set (halfOpenBox_subset_closedCube R)
theorem volume_halfOpenBox_pos {R : ℝ} (hR : 0 < R) : 0 < volume (halfOpenBox J R) := by
  unfold halfOpenBox
  rw [Real.volume_pi_Ioc (a := fun _ => -R) (b := fun _ => R), pos_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.mpr fun _ _ => ?_
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith
theorem boxWeight_integral_pos {Φ : X → ℝ} (hΦ : Continuous Φ) (Em : (J → ℝ) →L[ℝ] X) {R : ℝ} (hR : 0 < R) :
    0 < ∫ y in halfOpenBox J R, Real.exp (-Φ (Em y)) := by
  have hc : Continuous fun y : J → ℝ => Real.exp (-Φ (Em y)) :=
    Real.continuous_exp.comp (hΦ.comp Em.continuous).neg
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun y => (Real.exp_pos _).le) (integrableOn_halfOpenBox hc R)]
  have : Function.support (fun y : J → ℝ => Real.exp (-Φ (Em y))) = univ := by
    ext y
    simp [Real.exp_ne_zero]
  rw [this, univ_inter]
  exact volume_halfOpenBox_pos hR
theorem gridMean_tendsto {Φ h : X → ℝ} (hΦ : Continuous Φ) (hh : Continuous h)
    (Em : (J → ℝ) →L[ℝ] X) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => gridMean Em Φ R (n + 1) h) atTop (𝓝 (boxMean Em Φ R h)) := by
  have hc : Continuous fun y : J → ℝ => Real.exp (-Φ (Em y)) :=
    Real.continuous_exp.comp (hΦ.comp Em.continuous).neg
  have hc2 : Continuous fun y : J → ℝ => Real.exp (-Φ (Em y)) * h (Em y) :=
    hc.mul (hh.comp Em.continuous)
  have h1 := riemann_sum_tendsto (J := J) hR hc2
  have h2 := riemann_sum_tendsto (J := J) hR hc
  have h3 := h1.div h2 (boxWeight_integral_pos hΦ Em hR).ne'
  refine h3.congr fun n => ?_
  have hs := cellSide_pos hR (Nat.succ_pos n)
  unfold gridMean
  exact mul_div_mul_left _ _ (pow_ne_zero _ hs.ne')
theorem bondEnergy_le_of_edges {N : ℕ} [NeZero N] {f : X → ℝ} (β : J → ι) (Em : (J → ℝ) →L[ℝ] X) {R s δ₁ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hs : s = cellSide R N) (V : (J → ZMod N) → ℝ)
    (hstep : ∀ j k, (boxEdgeGrid J N).mark j k = 1 →
      Em (cellCentreAt R N (k + (boxEdgeGrid J N).dir j)) = Em (cellCentreAt R N k) + s • coordDir Em j)
    (hedge : ∀ j k, (boxEdgeGrid J N).mark j k = 1 →
      (f (Em (cellCentreAt R N k) + s • coordDir Em j) - f (Em (cellCentreAt R N k))) ^ 2
        ≤ s ^ 2 * ((fderiv ℝ f (Em (cellCentreAt R N k)) (coordDir Em j)) ^ 2 + δ₁) ∧
      (f (Em (cellCentreAt R N k) + s • coordDir Em j) - f (Em (cellCentreAt R N k))) ^ 2
        ≤ s ^ 2 * ((fderiv ℝ f (Em (cellCentreAt R N k) + s • coordDir Em j) (coordDir Em j)) ^ 2 + δ₁))
    (b : ι) :
    (boxEdgeGrid J N).bondEnergy V β (fun k => f (Em (cellCentreAt R N k))) b
      ≤ s ^ 2 * ∑ k, EdgeGrid.siteMass V k *
        (bondGradSq β Em f b (Em (cellCentreAt R N k)) + δ₁ * Fintype.card J) := by
  set L := boxEdgeGrid J N with hL
  set fh : (J → ZMod N) → ℝ := fun k => f (Em (cellCentreAt R N k)) with hfh
  have hI : ∀ j, (0 : ℝ) ≤ if β j = b then 1 else 0 := fun j => by split_ifs <;> norm_num
  refine le_trans (L.edgeForm_le_siteEnergy V _ hI fh) ?_
  unfold EdgeGrid.siteEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hp := EdgeGrid.siteMass_pos V k
  have hh : ∀ z : X, ∀ j, 0 ≤ (fderiv ℝ f z (coordDir Em j)) ^ 2 + δ₁ := fun z j => by positivity
  have hpf : ∀ j, L.fwd fh j k ^ 2 ≤ s ^ 2 * ((fderiv ℝ f (Em (cellCentreAt R N k)) (coordDir Em j)) ^ 2 + δ₁) := by
    intro j
    unfold EdgeGrid.fwd
    rcases L.mark_cases j k with h0 | h1
    · rw [h0, zero_mul]
      have := mul_nonneg (sq_nonneg s) (hh (Em (cellCentreAt R N k)) j)
      simpa using this
    · rw [h1, one_mul]
      unfold EdgeGrid.diff
      simp only [hfh]
      rw [hstep j k h1]
      exact (hedge j k h1).1
  have hqf : ∀ j, L.bwd fh j k ^ 2 ≤ s ^ 2 * ((fderiv ℝ f (Em (cellCentreAt R N k)) (coordDir Em j)) ^ 2 + δ₁) := by
    intro j
    unfold EdgeGrid.bwd EdgeGrid.fwd
    rcases L.mark_cases j (k - L.dir j) with h0 | h1
    · rw [h0, zero_mul]
      have := mul_nonneg (sq_nonneg s) (hh (Em (cellCentreAt R N k)) j)
      simpa using this
    · rw [h1, one_mul]
      unfold EdgeGrid.diff
      simp only [hfh]
      have e1 := hstep j (k - L.dir j) h1
      rw [sub_add_cancel] at e1 ⊢
      have := (hedge j (k - L.dir j) h1).2
      rw [← e1] at this
      exact this
  have hsum : ∑ j, (if β j = b then (1 : ℝ) else 0) * (L.fwd fh j k ^ 2 + L.bwd fh j k ^ 2) / 2
      ≤ s ^ 2 * (bondGradSq β Em f b (Em (cellCentreAt R N k)) + δ₁ * Fintype.card J) := by
    have e1 : s ^ 2 * bondGradSq β Em f b (Em (cellCentreAt R N k))
        = ∑ j, s ^ 2 * if β j = b then (fderiv ℝ f (Em (cellCentreAt R N k)) (coordDir Em j)) ^ 2 else 0 := by
      unfold bondGradSq
      rw [Finset.mul_sum]
    have e2 : ∑ _j : J, s ^ 2 * δ₁ = s ^ 2 * (δ₁ * Fintype.card J) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [mul_add, e1, ← e2, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have a1 := hpf j
    have a2 := hqf j
    have a3 : 0 ≤ s ^ 2 * δ₁ := by positivity
    split_ifs
    · nlinarith
    · simpa using a3
  have := mul_le_mul_of_nonneg_left hsum hp.le
  calc EdgeGrid.siteMass V k * ∑ j, (if β j = b then (1 : ℝ) else 0) * (L.fwd fh j k ^ 2 + L.bwd fh j k ^ 2) / 2
      ≤ _ := this
    _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set MeasureTheory Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {J : Type} [Fintype J] [DecidableEq J]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem exists_nat_cellSide_lt {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, cellSide R (n + 1) < c := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * R / c)
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 2 * R / c < ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  unfold cellSide
  rw [div_lt_iff₀ hc] at h2
  rw [div_lt_iff₀ (by positivity)]
  linarith
set_option maxHeartbeats 1000000 in
theorem grid_covariance {Φ f g : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {R : ℝ} (hR : 0 < R) (β : J → ι) (Em : (J → ℝ) →L[ℝ] X)
    (Dk : ι → ι → ℝ) (hD0 : ∀ b b', 0 < Dk b b') (hD1 : ∀ b, Dk b b = 1) (Wr m : ℝ)
    (hWr : ∀ b i j, Dk b (β j) ^ 2 ≤ Wr * Dk b (β i) ^ 2)
    (hform : ∀ b, ∀ x ∈ Em '' closedCube J R, ∀ ξ : J → ℝ, m * ∑ j, Dk b (β j) ^ 2 * ξ j ^ 2
      ≤ ∑ j, ∑ i, Dk b (β j) ^ 2 * secondDeriv Φ x (coordDir Em j) (coordDir Em i) * ξ j * ξ i)
    {δ : ℝ} (hδ : 0 < δ) (hm : 0 < m - δ * ((Fintype.card J : ℝ) * (1 + Wr))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |gridMean Em Φ R (n + 1) (fun x => f x * g x) - gridMean Em Φ R (n + 1) f * gridMean Em Φ R (n + 1) g|
        ≤ (m - δ * ((Fintype.card J : ℝ) * (1 + Wr)))⁻¹ *
          ∑ b, ∑ b', Real.sqrt (gridMean Em Φ R (n + 1) (bondGradSq β Em f b) + δ) * Dk b b' *
            Real.sqrt (gridMean Em Φ R (n + 1) (bondGradSq β Em g b') + δ) := by
  set B := Em '' closedCube J R with hB
  have hBc : IsCompact B := (isCompact_closedCube R).image Em.continuous
  have hBv : Convex ℝ B := (convex_closedCube R).linear_image Em.toLinearMap
  obtain ⟨s₀, hs₀, hgrid⟩ := hessian_grid_bounds hΦ (coordDir Em) hBc hBv hδ
  set δ₁ := δ / ((Fintype.card J : ℝ) + 1) with hδ₁
  have hδ₁p : 0 < δ₁ := by positivity
  have hδ₁c : δ₁ * Fintype.card J ≤ δ := by
    rw [hδ₁, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨s₁, hs₁, hef⟩ := edge_difference_sq_le hf (coordDir Em) hBc hBv hδ₁p
  obtain ⟨s₂, hs₂, heg⟩ := edge_difference_sq_le hg (coordDir Em) hBc hBv hδ₁p
  obtain ⟨n₀, hn₀⟩ := exists_nat_cellSide_lt hR (lt_min hs₀ (lt_min hs₁ hs₂))
  refine ⟨n₀, fun n hn => ?_⟩
  set N := n + 1 with hN
  have hNp : 0 < N := Nat.succ_pos n
  set s := cellSide R N with hs
  have hsp : 0 < s := cellSide_pos hR hNp
  have hlt := hn₀ n hn
  have l0 : s < s₀ := lt_of_lt_of_le hlt (min_le_left _ _)
  have l1 : s < s₁ := lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have l2 : s < s₂ := lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _))
  set L := boxEdgeGrid J N with hL
  set x : (J → ZMod N) → X := fun k => Em (cellCentreAt R N k) with hx
  have hxB : ∀ k, x k ∈ B := fun k => ⟨_, cellCentreAt_mem_closedCube hR k, rfl⟩
  have hstep : ∀ j k, L.mark j k = 1 → x (k + L.dir j) = x k + s • coordDir Em j := by
    intro j k h
    simp only [hx]
    rw [cellCentreAt_step h, map_add, map_smul]
    rfl
  obtain ⟨hc, hl⟩ := hgrid s hsp l0 (J → ZMod N) L x hxB hstep
  set V : (J → ZMod N) → ℝ := fun k => Φ (x k) with hV
  have dc := EdgeGrid.discrete_covariance hsp hc hl β Dk hD0 hD1 Wr m hδ.le hWr
    (fun b k ξ => hform b (x k) (hxB k) ξ) hm (boxEdgeGrid_connected (n := N))
    (fun k => f (x k)) (fun k => g (x k))
  set mh := m - δ * ((Fintype.card J : ℝ) * (1 + Wr)) with hmh
  set Z := ∑ k, EdgeGrid.siteMass V k with hZ
  have hZp : 0 < Z := Finset.sum_pos (fun k _ => EdgeGrid.siteMass_pos V k) ⟨0, Finset.mem_univ _⟩
  have hmean : ∀ h : X → ℝ, gridMean Em Φ R N h = (∑ k, EdgeGrid.siteMass V k * h (x k)) / Z := fun h => rfl
  have hNbf : ∀ (u : X → ℝ),
      (∀ j, ∀ y ∈ B, y + s • coordDir Em j ∈ B →
        (u (y + s • coordDir Em j) - u y) ^ 2 ≤ s ^ 2 * ((fderiv ℝ u y (coordDir Em j)) ^ 2 + δ₁) ∧
        (u (y + s • coordDir Em j) - u y) ^ 2 ≤ s ^ 2 * ((fderiv ℝ u (y + s • coordDir Em j) (coordDir Em j)) ^ 2 + δ₁)) →
      ∀ b, Real.sqrt (L.bondEnergy V β (fun k => u (x k)) b)
        ≤ s * Real.sqrt Z * Real.sqrt (gridMean Em Φ R N (bondGradSq β Em u b) + δ) := by
    intro u hu b
    have h1 := bondEnergy_le_of_edges (f := u) β Em hδ₁p.le hs V hstep (fun j k h => by
      have e1 := hstep j k h
      have m1 := hxB (k + L.dir j)
      rw [e1] at m1
      exact hu j _ (hxB k) m1) b
    have h2 : ∑ k, EdgeGrid.siteMass V k * (bondGradSq β Em u b (Em (cellCentreAt R N k)) + δ₁ * Fintype.card J)
        ≤ Z * (gridMean Em Φ R N (bondGradSq β Em u b) + δ) := by
      have e1 : ∑ k, EdgeGrid.siteMass V k * (bondGradSq β Em u b (Em (cellCentreAt R N k)) + δ₁ * Fintype.card J)
          = ∑ k, EdgeGrid.siteMass V k * bondGradSq β Em u b (x k) + δ₁ * Fintype.card J * Z := by
        rw [hZ, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [hx]; ring
      have e2 : Z * (gridMean Em Φ R N (bondGradSq β Em u b) + δ)
          = ∑ k, EdgeGrid.siteMass V k * bondGradSq β Em u b (x k) + δ * Z := by
        rw [hmean, mul_add, mul_div_cancel₀ _ hZp.ne']
        ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_right hδ₁c hZp.le
      linarith
    have h3 : L.bondEnergy V β (fun k => u (x k)) b ≤ s ^ 2 * (Z * (gridMean Em Φ R N (bondGradSq β Em u b) + δ)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg s))
    have h4 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hsp.le, Real.sqrt_mul hZp.le] at h4
    rw [mul_assoc]
    exact h4
  have hbf := hNbf f (fun j y hy hy' => hef s hsp l1 j y hy hy')
  have hbg := hNbf g (fun j y hy hy' => heg s hsp l2 j y hy hy')
  set A := gridMean Em Φ R N (fun x => f x * g x) with hA
  set a := gridMean Em Φ R N f with ha
  set c := gridMean Em Φ R N g with hc'
  have hsum : ∑ k, EdgeGrid.siteMass V k * f (x k) * (g (x k) - (∑ y, EdgeGrid.siteMass V y * g (x y)) / Z)
      = Z * (A - a * c) := by
    have e1 : (∑ y, EdgeGrid.siteMass V y * g (x y)) / Z = c := (hmean g).symm
    rw [e1]
    have e2 : ∑ k, EdgeGrid.siteMass V k * (f (x k) * g (x k)) = Z * A := by
      rw [hA, hmean, mul_div_cancel₀ _ hZp.ne']
    have e3 : ∑ k, EdgeGrid.siteMass V k * f (x k) = Z * a := by
      rw [ha, hmean, mul_div_cancel₀ _ hZp.ne']
    calc ∑ k, EdgeGrid.siteMass V k * f (x k) * (g (x k) - c)
        = ∑ k, EdgeGrid.siteMass V k * (f (x k) * g (x k)) - c * ∑ k, EdgeGrid.siteMass V k * f (x k) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [e2, e3]; ring
  rw [hsum, abs_mul, abs_of_pos hZp] at dc
  have hmh : 0 ≤ mh⁻¹ := (inv_pos.mpr hm).le
  have hZZ : Real.sqrt Z * Real.sqrt Z = Z := Real.mul_self_sqrt hZp.le
  have hbound : ∑ b, ∑ b', Real.sqrt (L.bondEnergy V β (fun k => f (x k)) b) * Dk b b' *
        Real.sqrt (L.bondEnergy V β (fun k => g (x k)) b')
      ≤ s ^ 2 * Z * ∑ b, ∑ b', Real.sqrt (gridMean Em Φ R N (bondGradSq β Em f b) + δ) * Dk b b' *
        Real.sqrt (gridMean Em Φ R N (bondGradSq β Em g b') + δ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    have h1 := hbf b
    have h2 := hbg b'
    have h3 := hD0 b b'
    calc Real.sqrt (L.bondEnergy V β (fun k => f (x k)) b) * Dk b b' * Real.sqrt (L.bondEnergy V β (fun k => g (x k)) b')
        ≤ (s * Real.sqrt Z * Real.sqrt (gridMean Em Φ R N (bondGradSq β Em f b) + δ)) * Dk b b' *
          (s * Real.sqrt Z * Real.sqrt (gridMean Em Φ R N (bondGradSq β Em g b') + δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 h3.le) h2 (Real.sqrt_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hsp.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) h3.le)
      _ = s ^ 2 * (Real.sqrt Z * Real.sqrt Z) * (Real.sqrt (gridMean Em Φ R N (bondGradSq β Em f b) + δ) * Dk b b' *
          Real.sqrt (gridMean Em Φ R N (bondGradSq β Em g b') + δ)) := by ring
      _ = _ := by rw [hZZ]
  have hfin := le_trans dc (mul_le_mul_of_nonneg_left hbound hmh)
  have hpos : 0 < s ^ 2 * Z := by positivity
  have e5 : s ^ 2 * (Z * |A - a * c|) = (s ^ 2 * Z) * |A - a * c| := by ring
  have e6 : mh⁻¹ * (s ^ 2 * Z * ∑ b, ∑ b', Real.sqrt (gridMean Em Φ R N (bondGradSq β Em f b) + δ) * Dk b b' *
        Real.sqrt (gridMean Em Φ R N (bondGradSq β Em g b') + δ))
      = (s ^ 2 * Z) * (mh⁻¹ * ∑ b, ∑ b', Real.sqrt (gridMean Em Φ R N (bondGradSq β Em f b) + δ) * Dk b b' *
        Real.sqrt (gridMean Em Φ R N (bondGradSq β Em g b') + δ)) := by ring
  rw [e5, e6] at hfin
  exact le_of_mul_le_mul_left hfin hpos
theorem box_covariance {Φ f g : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {R : ℝ} (hR : 0 < R) (β : J → ι) (Em : (J → ℝ) →L[ℝ] X)
    (Dk : ι → ι → ℝ) (hD0 : ∀ b b', 0 < Dk b b') (hD1 : ∀ b, Dk b b = 1) (Wr m : ℝ)
    (hm : 0 < m) (hWr0 : 0 ≤ Wr)
    (hWr : ∀ b i j, Dk b (β j) ^ 2 ≤ Wr * Dk b (β i) ^ 2)
    (hform : ∀ b, ∀ x ∈ Em '' closedCube J R, ∀ ξ : J → ℝ, m * ∑ j, Dk b (β j) ^ 2 * ξ j ^ 2
      ≤ ∑ j, ∑ i, Dk b (β j) ^ 2 * secondDeriv Φ x (coordDir Em j) (coordDir Em i) * ξ j * ξ i) :
    |boxMean Em Φ R (fun x => f x * g x) - boxMean Em Φ R f * boxMean Em Φ R g|
      ≤ m⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b)) * Dk b b' *
          Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b')) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hPb : ∀ (u : X → ℝ), ContDiff ℝ 1 u → ∀ b, Continuous (bondGradSq β Em u b) := by
    intro u hu b
    have hfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    refine continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact (hfd.clm_apply continuous_const).pow 2
    · exact continuous_const
  set C : ℝ := (Fintype.card J : ℝ) * (1 + Wr) with hC
  have step : ∀ δ : ℝ, 0 < δ → 0 < m - δ * C →
      |boxMean Em Φ R (fun x => f x * g x) - boxMean Em Φ R f * boxMean Em Φ R g|
        ≤ (m - δ * C)⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b) + δ) * Dk b b' *
            Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b') + δ) := by
    intro δ hδ hmδ
    obtain ⟨n₀, hn₀⟩ := grid_covariance hΦ hf hg hR β Em Dk hD0 hD1 Wr m hWr hform hδ hmδ
    have t1 := (gridMean_tendsto hΦc (hf.continuous.mul hg.continuous) Em hR).sub
      ((gridMean_tendsto hΦc hf.continuous Em hR).mul (gridMean_tendsto hΦc hg.continuous Em hR))
    have t2 := t1.abs
    have t3 : Tendsto (fun n : ℕ => (m - δ * C)⁻¹ * ∑ b, ∑ b',
        Real.sqrt (gridMean Em Φ R (n + 1) (bondGradSq β Em f b) + δ) * Dk b b' *
          Real.sqrt (gridMean Em Φ R (n + 1) (bondGradSq β Em g b') + δ)) atTop
        (𝓝 ((m - δ * C)⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b) + δ) * Dk b b' *
          Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b') + δ))) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ => ?_)
      refine Tendsto.mul (Tendsto.mul_const _ ?_) ?_
      · exact ((gridMean_tendsto hΦc (hPb f hf b) Em hR).add_const δ).sqrt
      · exact ((gridMean_tendsto hΦc (hPb g hg b') Em hR).add_const δ).sqrt
    exact le_of_tendsto_of_tendsto t2 t3 (eventually_atTop.mpr ⟨n₀, hn₀⟩)
  have hlim : Tendsto (fun δ : ℝ => (m - δ * C)⁻¹ * ∑ b, ∑ b',
      Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b) + δ) * Dk b b' *
        Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b') + δ)) (𝓝[>] 0)
      (𝓝 (m⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b)) * Dk b b' *
        Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b')))) := by
    have hcont : ContinuousAt (fun δ : ℝ => (m - δ * C)⁻¹ * ∑ b, ∑ b',
        Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b) + δ) * Dk b b' *
          Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b') + δ)) 0 := by
      refine ContinuousAt.mul (ContinuousAt.inv₀ (by fun_prop) (by simpa using hm.ne')) ?_
      refine tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ => ?_
      have hcc : Continuous fun δ : ℝ => Real.sqrt (boxMean Em Φ R (bondGradSq β Em f b) + δ) * Dk b b' *
          Real.sqrt (boxMean Em Φ R (bondGradSq β Em g b') + δ) :=
        ((continuous_const.add continuous_id).sqrt.mul continuous_const).mul
          (continuous_const.add continuous_id).sqrt
      exact hcc.tendsto 0
    have := hcont.tendsto
    simp only [zero_mul, sub_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < m - δ * C := by
    have h1 : Tendsto (fun δ : ℝ => m - δ * C) (𝓝 0) (𝓝 m) := by
      have : Continuous fun δ : ℝ => m - δ * C := by fun_prop
      simpa using this.tendsto 0
    exact (h1.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hm)
  filter_upwards [hev, self_mem_nhdsWithin] with δ h1 h2
  exact step δ h2 h1
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
def secondDerivVec (τ : E → F) (η u v : E) : F := fderiv ℝ (fun ζ => fderiv ℝ τ ζ u) η v
theorem hasFDerivAt_fderiv_of_contDiffAt {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y) :
    HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) y := h.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).hasFDerivAt
theorem hasFDerivAt_fderiv_apply_of_contDiffAt {τ : E → F} {y : E} (h : ContDiffAt ℝ 2 τ y) (u : E) :
    HasFDerivAt (fun ζ => fderiv ℝ τ ζ u) (fderiv ℝ (fun ζ => fderiv ℝ τ ζ u) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ τ) y := h.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun ζ => fderiv ℝ τ ζ u) y := h1.clm_apply contDiffAt_const
  exact (h2.differentiableAt (by norm_num)).hasFDerivAt
theorem secondDeriv_eq_fderiv_fderiv {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y) (a b : E) :
    secondDeriv Φ y a b = fderiv ℝ (fderiv ℝ Φ) y b a := by
  have h1 := (hasFDerivAt_fderiv_of_contDiffAt h).clm_apply (hasFDerivAt_const a y)
  unfold secondDeriv
  rw [h1.fderiv]
  simp
theorem secondDeriv_smul_left {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y) (c : ℝ) (a b : E) :
    secondDeriv Φ y (c • a) b = c * secondDeriv Φ y a b := by
  simp only [secondDeriv_eq_fderiv_fderiv h, map_smul, smul_eq_mul]
theorem secondDeriv_smul_right {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y) (c : ℝ) (a b : E) :
    secondDeriv Φ y a (c • b) = c * secondDeriv Φ y a b := by
  simp only [secondDeriv_eq_fderiv_fderiv h, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
theorem secondDeriv_sum_left {α : Type} (S : Finset α) {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y)
    (a : α → E) (b : E) : secondDeriv Φ y (∑ x ∈ S, a x) b = ∑ x ∈ S, secondDeriv Φ y (a x) b := by
  simp only [secondDeriv_eq_fderiv_fderiv h, map_sum]
theorem secondDeriv_sum_right {α : Type} (S : Finset α) {Φ : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y)
    (a : E) (b : α → E) : secondDeriv Φ y a (∑ x ∈ S, b x) = ∑ x ∈ S, secondDeriv Φ y a (b x) := by
  simp only [secondDeriv_eq_fderiv_fderiv h, map_sum, ContinuousLinearMap.sum_apply]
theorem secondDeriv_add {Φ Φ' : E → ℝ} {y : E} (h : ContDiffAt ℝ 2 Φ y) (h' : ContDiffAt ℝ 2 Φ' y) (a b : E) :
    secondDeriv (fun z => Φ z + Φ' z) y a b = secondDeriv Φ y a b + secondDeriv Φ' y a b := by
  have ev : (fun ζ => fderiv ℝ (fun z => Φ z + Φ' z) ζ a)
      =ᶠ[𝓝 y] fun ζ => fderiv ℝ Φ ζ a + fderiv ℝ Φ' ζ a := by
    filter_upwards [h.eventually (by norm_num), h'.eventually (by norm_num)] with ζ h1 h2
    have d1 : DifferentiableAt ℝ Φ ζ := h1.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ Φ' ζ := h2.differentiableAt (by norm_num)
    rw [fderiv_fun_add d1 d2]
    rfl
  unfold secondDeriv
  rw [ev.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv_apply_of_contDiffAt h a) (differentiableAt_fderiv_apply_of_contDiffAt h' a)]
  rfl
theorem secondDeriv_sum {α : Type} (S : Finset α) {Φ : α → E → ℝ} {y : E}
    (h : ∀ x ∈ S, ContDiffAt ℝ 2 (Φ x) y) (a b : E) :
    secondDeriv (fun z => ∑ x ∈ S, Φ x z) y a b = ∑ x ∈ S, secondDeriv (Φ x) y a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [secondDeriv]
  | insert x S hx ih =>
    have h1 : ContDiffAt ℝ 2 (fun z => ∑ x ∈ S, Φ x z) y :=
      ContDiffAt.sum fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hx]
    rw [secondDeriv_add (h x (Finset.mem_insert_self x S)) h1,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
theorem secondDeriv_comp {τ : E → F} {Φ : F → ℝ} {η : E} (hτ : ContDiffAt ℝ 2 τ η)
    (hΦ : ContDiffAt ℝ 2 Φ (τ η)) (u v : E) :
    secondDeriv (fun z => Φ (τ z)) η u v
      = secondDeriv Φ (τ η) (fderiv ℝ τ η u) (fderiv ℝ τ η v) + fderiv ℝ Φ (τ η) (secondDerivVec τ η u v) := by
  have ev : (fun ζ => fderiv ℝ (fun z => Φ (τ z)) ζ u)
      =ᶠ[𝓝 η] fun ζ => fderiv ℝ Φ (τ ζ) (fderiv ℝ τ ζ u) := by
    have e1 : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ 2 Φ (τ ζ) :=
      hτ.continuousAt.eventually (hΦ.eventually (by norm_num))
    filter_upwards [hτ.eventually (by norm_num), e1] with ζ h1 h2
    have d1 : DifferentiableAt ℝ τ ζ := h1.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ Φ (τ ζ) := h2.differentiableAt (by norm_num)
    have := (d2.hasFDerivAt.comp ζ d1.hasFDerivAt).fderiv
    have e2 : (fun z => Φ (τ z)) = Φ ∘ τ := rfl
    rw [e2, this]
    rfl
  have hA : HasFDerivAt (fun ζ => fderiv ℝ Φ (τ ζ))
      ((fderiv ℝ (fderiv ℝ Φ) (τ η)).comp (fderiv ℝ τ η)) η :=
    (hasFDerivAt_fderiv_of_contDiffAt hΦ).comp η (hτ.differentiableAt (by norm_num)).hasFDerivAt
  have hw := hasFDerivAt_fderiv_apply_of_contDiffAt hτ u
  have h1 := hA.clm_apply hw
  unfold secondDeriv
  rw [ev.fderiv_eq, h1.fderiv]
  have e3 := secondDeriv_eq_fderiv_fderiv hΦ (fderiv ℝ τ η u) (fderiv ℝ τ η v)
  unfold secondDeriv at e3
  rw [e3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, secondDerivVec]
  ring
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem fderiv_bondwise_map {τ₀ : E → E} (hτ : ContDiff ℝ 2 τ₀) (ζ u : ι → E) :
    fderiv ℝ (fun (z : ι → E) b => τ₀ (z b)) ζ u = fun b => fderiv ℝ τ₀ (ζ b) (u b) := by
  have h : HasFDerivAt (fun (z : ι → E) b => τ₀ (z b))
      (ContinuousLinearMap.pi fun b => (fderiv ℝ τ₀ (ζ b)).comp (ContinuousLinearMap.proj b)) ζ := by
    refine hasFDerivAt_pi.mpr fun b => ?_
    have h1 : HasFDerivAt τ₀ (fderiv ℝ τ₀ (ζ b)) (ζ b) :=
      ((hτ.differentiable (by norm_num)) _).hasFDerivAt
    exact h1.comp ζ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b).hasFDerivAt
  rw [h.fderiv]
  rfl
theorem secondDerivVec_bondwise_map {τ₀ : E → E} (hτ : ContDiff ℝ 2 τ₀) (η u v : ι → E) :
    secondDerivVec (fun (z : ι → E) b => τ₀ (z b)) η u v = fun b => secondDerivVec τ₀ (η b) (u b) (v b) := by
  unfold secondDerivVec
  have e : (fun ζ => fderiv ℝ (fun (z : ι → E) b => τ₀ (z b)) ζ u)
      = fun (ζ : ι → E) b => fderiv ℝ τ₀ (ζ b) (u b) := funext fun ζ => fderiv_bondwise_map hτ ζ u
  rw [e]
  have h : HasFDerivAt (fun (ζ : ι → E) b => fderiv ℝ τ₀ (ζ b) (u b))
      (ContinuousLinearMap.pi fun b => (fderiv ℝ (fun z => fderiv ℝ τ₀ z (u b)) (η b)).comp
        (ContinuousLinearMap.proj b)) η := by
    refine hasFDerivAt_pi.mpr fun b => ?_
    have h1 := hasFDerivAt_fderiv_apply_of_contDiffAt hτ.contDiffAt (y := η b) (u b)
    exact h1.comp η (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b).hasFDerivAt
  rw [h.fderiv]
  rfl
theorem secondDeriv_bondwise_map {τ₀ : E → E} (hτ : ContDiff ℝ 2 τ₀) {U : (ι → E) → ℝ} {η : ι → E}
    (hU : ContDiffAt ℝ 2 U (fun b => τ₀ (η b))) (u v : ι → E) :
    secondDeriv (fun z => U (fun b => τ₀ (z b))) η u v
      = secondDeriv U (fun b => τ₀ (η b)) (fun b => fderiv ℝ τ₀ (η b) (u b)) (fun b => fderiv ℝ τ₀ (η b) (v b))
        + fderiv ℝ U (fun b => τ₀ (η b)) (fun b => secondDerivVec τ₀ (η b) (u b) (v b)) := by
  have hτ' : ContDiff ℝ 2 (fun (z : ι → E) b => τ₀ (z b)) :=
    contDiff_pi.mpr fun b => hτ.comp (contDiff_apply ℝ E b)
  have := secondDeriv_comp (τ := fun (z : ι → E) b => τ₀ (z b)) hτ'.contDiffAt hU u v
  rw [this, fderiv_bondwise_map hτ, fderiv_bondwise_map hτ, secondDerivVec_bondwise_map hτ]
theorem secondDeriv_proj {ψ : E → ℝ} (b : ι) {η : ι → E} (hψ : ContDiffAt ℝ 2 ψ (η b)) (u v : ι → E) :
    secondDeriv (fun z : ι → E => ψ (z b)) η u v = secondDeriv ψ (η b) (u b) (v b) := by
  have hp : ContDiff ℝ 2 (fun z : ι → E => z b) := contDiff_apply ℝ E b
  have hd : ∀ ζ : ι → E, fderiv ℝ (fun z : ι → E => z b) ζ
      = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b := fun ζ =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) b).hasFDerivAt.fderiv
  have := secondDeriv_comp (τ := fun z : ι → E => z b) hp.contDiffAt hψ u v
  rw [this, hd]
  have hz : secondDerivVec (fun z : ι → E => z b) η u v = 0 := by
    unfold secondDerivVec
    simp only [hd]
    simp
  rw [hz]
  simp
theorem secondDerivVec_zero_left (τ₀ : E → E) (x v : E) : secondDerivVec τ₀ x 0 v = 0 := by
  unfold secondDerivVec
  simp
theorem secondDeriv_zero_left (ψ : E → ℝ) (x v : E) : secondDeriv ψ x 0 v = 0 := by
  unfold secondDeriv
  simp
theorem extended_form_lower {U : (ι → E) → ℝ} {τ₀ : E → E} {ψ : E → ℝ} {m r₀ r₁ Rb C₂ : ℝ} (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hτ : ContDiff ℝ 2 τ₀) (hψ : ContDiff ℝ 2 ψ)
    (hU : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ContDiffAt ℝ 2 U ζ)
    (hUform : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ∀ v : ι → E,
      m * ∑ b, w b * ‖v b‖ ^ 2 ≤ ∑ b, w b * secondDeriv U ζ (Pi.single b (v b)) v)
    (hin : ∀ x, ‖τ₀ x‖ ≤ r₁) (hid : ∀ x, ‖x‖ < r₀ → τ₀ =ᶠ[𝓝 x] id)
    (hψ0 : ∀ x v, 0 ≤ secondDeriv ψ x v v)
    (hψ1 : ∀ x v, r₀ ≤ ‖x‖ → ‖x‖ ≤ Rb → (m + C₂) * ‖v‖ ^ 2 ≤ secondDeriv ψ x v v)
    (hm : 0 ≤ m)
    (hC : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ∀ x, ‖x‖ ≤ Rb → ∀ b v,
      |fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ x v v))| ≤ C₂ * ‖v‖ ^ 2)
    (η : ι → E) (hη : ∀ b, ‖η b‖ ≤ Rb) (v : ι → E) :
    m * ∑ b, w b * ‖v b‖ ^ 2 ≤ ∑ b, w b *
      secondDeriv (fun z => U (fun b => τ₀ (z b)) + ∑ b, ψ (z b)) η (Pi.single b (v b)) v := by
  set ζ : ι → E := fun b => τ₀ (η b) with hζ
  have hζin : ∀ b, ‖ζ b‖ ≤ r₁ := fun b => hin _
  have hUζ := hU ζ hζin
  have hτ' : ContDiff ℝ 2 (fun (z : ι → E) b => τ₀ (z b)) :=
    contDiff_pi.mpr fun b => hτ.comp (contDiff_apply ℝ E b)
  have hc1 : ContDiffAt ℝ 2 (fun z : ι → E => U (fun b => τ₀ (z b))) η :=
    ContDiffAt.comp η hUζ hτ'.contDiffAt
  have hc2 : ∀ b ∈ (Finset.univ : Finset ι), ContDiffAt ℝ 2 (fun z : ι → E => ψ (z b)) η :=
    fun b _ => (hψ.comp (contDiff_apply ℝ E b)).contDiffAt
  have hc3 : ContDiffAt ℝ 2 (fun z : ι → E => ∑ b, ψ (z b)) η := ContDiffAt.sum hc2
  set y : ι → E := fun b => fderiv ℝ τ₀ (η b) (v b) with hy
  have hsplit : ∀ b, secondDeriv (fun z => U (fun b => τ₀ (z b)) + ∑ b, ψ (z b)) η (Pi.single b (v b)) v
      = secondDeriv U ζ (Pi.single b (y b)) y + fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b)))
        + secondDeriv ψ (η b) (v b) (v b) := by
    intro b
    rw [secondDeriv_add hc1 hc3, secondDeriv_bondwise_map hτ hUζ, secondDeriv_sum _ hc2]
    have e1 : (fun b' => fderiv ℝ τ₀ (η b') ((Pi.single b (v b) : ι → E) b'))
        = (Pi.single b (y b) : ι → E) := by
      funext b'
      by_cases h : b' = b
      · subst h; simp [hy]
      · simp [Pi.single_eq_of_ne h]
    have e2 : (fun b' => secondDerivVec τ₀ (η b') ((Pi.single b (v b) : ι → E) b') (v b'))
        = (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b)) : ι → E) := by
      funext b'
      by_cases h : b' = b
      · subst h; simp
      · simp [Pi.single_eq_of_ne h, secondDerivVec_zero_left]
    have e3 : ∑ b', secondDeriv (fun z : ι → E => ψ (z b')) η (Pi.single b (v b)) v = secondDeriv ψ (η b) (v b) (v b) := by
      rw [Finset.sum_eq_single b]
      · rw [secondDeriv_proj b hψ.contDiffAt]
        simp
      · intro b' _ h
        rw [secondDeriv_proj b' hψ.contDiffAt]
        simp [Pi.single_eq_of_ne h, secondDeriv_zero_left]
      · simp
    rw [e1, e2, e3]
  simp only [hsplit]
  have hf := hUform ζ hζin y
  have hbond : ∀ b, m * ‖v b‖ ^ 2 ≤ m * ‖y b‖ ^ 2
      + (fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b))) + secondDeriv ψ (η b) (v b) (v b)) := by
    intro b
    by_cases hb : ‖η b‖ < r₀
    · have h1 := hid (η b) hb
      have h2 : fderiv ℝ τ₀ (η b) = ContinuousLinearMap.id ℝ E := by
        rw [h1.fderiv_eq]
        exact fderiv_id
      have h3 : secondDerivVec τ₀ (η b) (v b) (v b) = 0 := by
        unfold secondDerivVec
        have ev : (fun ζ => fderiv ℝ τ₀ ζ (v b)) =ᶠ[𝓝 (η b)] fun _ => v b := by
          filter_upwards [h1.eventuallyEq_nhds] with z hz
          rw [hz.fderiv_eq, fderiv_id]
          rfl
        rw [ev.fderiv_eq]
        simp
      have h4 : y b = v b := by
        simp only [hy]
        rw [h2]
        rfl
      rw [h4, h3]
      have := hψ0 (η b) (v b)
      simp only [Pi.single_zero, map_zero, zero_add]
      linarith
    · have h1 := hψ1 (η b) (v b) (not_lt.mp hb) (hη b)
      have h2 := abs_le.mp (hC ζ hζin (η b) (hη b) b (v b))
      have h3 : 0 ≤ m * ‖y b‖ ^ 2 := by positivity
      nlinarith [h2.1]
  have hsum : m * ∑ b, w b * ‖v b‖ ^ 2 ≤ m * ∑ b, w b * ‖y b‖ ^ 2 + ∑ b, w b *
      (fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b))) + secondDeriv ψ (η b) (v b) (v b)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    have := mul_le_mul_of_nonneg_left (hbond b) (hw b)
    nlinarith
  have e4 : ∑ b, w b * (secondDeriv U ζ (Pi.single b (y b)) y
        + fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b))) + secondDeriv ψ (η b) (v b) (v b))
      = ∑ b, w b * secondDeriv U ζ (Pi.single b (y b)) y + ∑ b, w b *
        (fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ (η b) (v b) (v b))) + secondDeriv ψ (η b) (v b) (v b)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e4]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def pullInside (r₀ r₁ : ℝ) (x : E) : E :=
  Real.smoothTransition ((r₁ ^ 2 - ‖x‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2)) • x
theorem contDiff_pullInside (r₀ r₁ : ℝ) : ContDiff ℝ 3 (pullInside r₀ r₁ : E → E) := by
  unfold pullInside
  have h1 : ContDiff ℝ 3 (fun x : E => (r₁ ^ 2 - ‖x‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2)) :=
    (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _
  have h2 : ContDiff ℝ 3 Real.smoothTransition := by
    exact_mod_cast (Real.smoothTransition.contDiff (n := 3))
  exact (h2.comp h1).smul contDiff_id
theorem norm_pullInside_le {r₀ r₁ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < r₁) (x : E) : ‖pullInside r₀ r₁ x‖ ≤ r₁ := by
  unfold pullInside
  have hd : 0 < r₁ ^ 2 - r₀ ^ 2 := by nlinarith
  by_cases h : ‖x‖ < r₁
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have := Real.smoothTransition.le_one ((r₁ ^ 2 - ‖x‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2))
    have h2 := norm_nonneg x
    have h3 := Real.smoothTransition.nonneg ((r₁ ^ 2 - ‖x‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2))
    nlinarith
  · have h2 : (r₁ ^ 2 - ‖x‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2) ≤ 0 := by
      refine div_nonpos_of_nonpos_of_nonneg ?_ hd.le
      have := not_lt.mp h
      nlinarith
    rw [Real.smoothTransition.zero_of_nonpos h2, zero_smul, norm_zero]
    linarith
theorem pullInside_eventuallyEq_id {r₀ r₁ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < r₁) {x : E} (hx : ‖x‖ < r₀) :
    (pullInside r₀ r₁ : E → E) =ᶠ[𝓝 x] id := by
  have hd : 0 < r₁ ^ 2 - r₀ ^ 2 := by nlinarith
  have ev : ∀ᶠ ζ in 𝓝 x, ‖ζ‖ < r₀ := continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [ev] with ζ hζ
  unfold pullInside
  have h2 : 1 ≤ (r₁ ^ 2 - ‖ζ‖ ^ 2) / (r₁ ^ 2 - r₀ ^ 2) := by
    rw [one_le_div hd]
    have := norm_nonneg ζ
    nlinarith
  rw [Real.smoothTransition.one_of_one_le h2, one_smul]
  rfl
def radialPower (c : ℝ) (n : ℕ) (x : E) : ℝ := c * (‖x‖ ^ 2) ^ (n + 2)
theorem contDiff_radialPower (c : ℝ) (n : ℕ) : ContDiff ℝ 2 (radialPower c n : E → ℝ) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).pow _)
theorem fderiv_norm_sq_apply (x u : E) : fderiv ℝ (fun x : E => ‖x‖ ^ 2) x u = 2 * inner ℝ x u := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv
  rw [h]
  simp
theorem secondDerivVec_norm_sq (x u v : E) : secondDerivVec (fun x : E => ‖x‖ ^ 2) x u v = 2 * inner ℝ v u := by
  unfold secondDerivVec
  have e : (fun ζ => fderiv ℝ (fun x : E => ‖x‖ ^ 2) ζ u) = fun ζ => 2 * inner ℝ ζ u :=
    funext fun ζ => fderiv_norm_sq_apply ζ u
  rw [e]
  have h : HasFDerivAt (fun ζ : E => 2 * inner ℝ ζ u) ((2 : ℝ) • (innerSL ℝ u)) x := by
    have h1 : HasFDerivAt (fun ζ : E => inner ℝ u ζ) (innerSL ℝ u) x := (innerSL ℝ u).hasFDerivAt
    have h2 := h1.const_mul (2 : ℝ)
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
    simp [real_inner_comm]
  rw [h.fderiv]
  simp [real_inner_comm]
theorem secondDeriv_radialPower_ge {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x v : E) :
    2 * c * (n + 2) * (‖x‖ ^ 2) ^ (n + 1) * ‖v‖ ^ 2 ≤ secondDeriv (radialPower c n) x v v := by
  set y := ‖x‖ ^ 2 with hy
  set Φ : ℝ → ℝ := fun y => c * y ^ (n + 2) with hΦ
  have hΦc : ContDiff ℝ 2 Φ := contDiff_const.mul (contDiff_id.pow _)
  have hder : ∀ z a : ℝ, fderiv ℝ Φ z a = a * (c * ((n + 2 : ℕ) * z ^ (n + 1))) := by
    intro z a
    have h1 : HasDerivAt Φ (c * ((n + 2 : ℕ) * z ^ (n + 1))) z := by
      have := (hasDerivAt_pow (n + 2) z).const_mul c
      simpa [hΦ] using this
    rw [h1.hasFDerivAt.fderiv]
    simp [mul_comm]
  have hsec : ∀ z a : ℝ, secondDeriv Φ z a a
      = a * (a * (c * ((n + 2 : ℕ) * ((n + 1 : ℕ) * z ^ n)))) := by
    intro z a
    unfold secondDeriv
    have e : (fun ζ => fderiv ℝ Φ ζ a) = fun ζ => a * (c * ((n + 2 : ℕ) * ζ ^ (n + 1))) :=
      funext fun ζ => hder ζ a
    rw [e]
    have h1 : HasDerivAt (fun ζ : ℝ => a * (c * ((n + 2 : ℕ) * ζ ^ (n + 1))))
        (a * (c * ((n + 2 : ℕ) * ((n + 1 : ℕ) * z ^ n)))) z := by
      have := (((hasDerivAt_pow (n + 1) z).const_mul ((n + 2 : ℕ) : ℝ)).const_mul c).const_mul a
      simpa using this
    rw [h1.hasFDerivAt.fderiv]
    simp [mul_comm]
  have hτ : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hc2 := secondDeriv_comp (τ := fun x : E => ‖x‖ ^ 2) (η := x) hτ.contDiffAt hΦc.contDiffAt v v
  have e0 : secondDeriv (radialPower c n) x v v = secondDeriv (fun z => Φ ((fun x : E => ‖x‖ ^ 2) z)) x v v := rfl
  rw [e0, hc2, fderiv_norm_sq_apply, hsec, secondDerivVec_norm_sq, hder, real_inner_self_eq_norm_sq]
  have t1 : 0 ≤ (2 * inner ℝ x v) * ((2 * inner ℝ x v) * (c * (((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * y ^ n)))) := by
    have : (2 * inner ℝ x v) * ((2 * inner ℝ x v) * (c * (((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * y ^ n))))
        = (2 * inner ℝ x v) ^ 2 * (c * (((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * y ^ n))) := by ring
    rw [this]
    positivity
  push_cast at t1 ⊢
  nlinarith
theorem secondDeriv_radialPower_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x v : E) :
    0 ≤ secondDeriv (radialPower c n) x v v := by
  refine le_trans ?_ (secondDeriv_radialPower_ge hc n x v)
  positivity
theorem exists_barrier_power {a q₁ q₂ ε T : ℝ} (ha : 0 < a) (hq₁ : 0 ≤ q₁) (hq₁' : q₁ < 1) (hq₂ : 1 < q₂)
    (hε : 0 < ε) : ∃ n : ℕ, a / (n + 2) * q₁ ^ (n + 2) ≤ ε ∧ T ≤ a / (n + 2) * q₂ ^ (n + 2) := by
  have h1 : Tendsto (fun n : ℕ => a * q₁ ^ (n + 2)) atTop (𝓝 (a * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₁ hq₁').comp (tendsto_add_atTop_nat 2)).const_mul a
  rw [mul_zero] at h1
  have h2 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ 1 / q₂ ^ (n + 2)) atTop (𝓝 0) :=
    (tendsto_pow_const_div_const_pow_of_one_lt 1 hq₂).comp (tendsto_add_atTop_nat 2)
  have e1 := h1.eventually (gt_mem_nhds hε)
  have hc : 0 < a / (|T| + 1) := by positivity
  have e2 := h2.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  refine ⟨n, ?_, ?_⟩
  · have hq : 0 ≤ q₁ ^ (n + 2) := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : a / (n + 2) ≤ a := div_le_self ha.le (by linarith [show (0 : ℝ) ≤ n from by positivity])
    have := mul_le_mul_of_nonneg_right this hq
    linarith
  · have hq : 0 < q₂ ^ (n + 2) := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    simp only [pow_one] at hn2
    push_cast at hn2
    rw [div_lt_div_iff₀ hq (by positivity)] at hn2
    have h3 : a / (n + 2) * q₂ ^ (n + 2) = a * q₂ ^ (n + 2) / (n + 2) := by ring
    rw [h3, le_div_iff₀ hn]
    have := le_abs_self T
    nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem secondDerivVec_eq_fderiv_fderiv {τ : E → E} {y : E} (h : ContDiffAt ℝ 2 τ y) (a b : E) :
    secondDerivVec τ y a b = fderiv ℝ (fderiv ℝ τ) y b a := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ τ) y := h.fderiv_right (by norm_num)
  have h2 := (h1.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const a y)
  unfold secondDerivVec
  rw [h2.fderiv]
  simp
set_option maxHeartbeats 1000000 in
theorem exists_convex_extension {U : (ι → E) → ℝ} {ρ ρ₀ r₀ r₁ Rb m Umin ε T : ℝ}
    (h0 : 0 < ρ₀) (h1 : ρ₀ < r₀) (h2 : r₀ < r₁) (h3 : r₁ < ρ) (hm : 0 < m) (hε : 0 < ε)
    (wf : ι → ι → ℝ) (hw : ∀ b₀ b, 0 ≤ wf b₀ b)
    (hU : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ < ρ) → ContDiffAt ℝ 2 U ζ)
    (hUform : ∀ b₀, ∀ ζ : ι → E, (∀ b, ‖ζ b‖ < ρ) → ∀ v : ι → E,
      m * ∑ b, wf b₀ b * ‖v b‖ ^ 2 ≤ ∑ b, wf b₀ b * secondDeriv U ζ (Pi.single b (v b)) v)
    (hmin : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ < ρ) → Umin ≤ U ζ) :
    ∃ Φ : (ι → E) → ℝ, ContDiff ℝ 2 Φ ∧
      (∀ η : ι → E, (∀ b, ‖η b‖ ≤ ρ₀) → |Φ η - U η| ≤ ε) ∧
      (∀ η, Umin ≤ Φ η) ∧
      (∀ η : ι → E, (∃ b, ρ ≤ ‖η b‖) → T ≤ Φ η) ∧
      (∀ b₀, ∀ η : ι → E, (∀ b, ‖η b‖ ≤ Rb) → ∀ v : ι → E,
        m * ∑ b, wf b₀ b * ‖v b‖ ^ 2 ≤ ∑ b, wf b₀ b * secondDeriv Φ η (Pi.single b (v b)) v) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hr₀ : 0 < r₀ := h0.trans h1
  set τ₀ : E → E := pullInside r₀ r₁ with hτ₀
  have hτ3 : ContDiff ℝ 3 τ₀ := contDiff_pullInside r₀ r₁
  have hτ : ContDiff ℝ 2 τ₀ := hτ3.of_le (by norm_num)
  have hin : ∀ x, ‖τ₀ x‖ ≤ r₁ := norm_pullInside_le hr₀ h2
  set S : Set (ι → E) := Set.pi univ fun _ => Metric.closedBall (0 : E) r₁ with hS
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 r₁
  have hmem : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ζ ∈ S := fun ζ h b _ => by simpa using h b
  have hUr : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ContDiffAt ℝ 2 U ζ := fun ζ h =>
    hU ζ fun b => lt_of_le_of_lt (h b) h3
  have hcont : ContinuousOn (fderiv ℝ U) S := by
    intro ζ hζ
    have h4 : ∀ b, ‖ζ b‖ ≤ r₁ := fun b => by simpa using hζ b (mem_univ b)
    have h5 : ContDiffAt ℝ 1 (fderiv ℝ U) ζ := (hUr ζ h4).fderiv_right (by norm_num)
    exact h5.continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hSc.exists_bound_of_continuousOn (E := (ι → E) →L[ℝ] ℝ) hcont
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ τ₀)) :=
    (hτ3.fderiv_right (m := 2) (by norm_num)).continuous_fderiv (by norm_num)
  obtain ⟨C₃, hC₃⟩ := (isCompact_closedBall (0 : E) Rb).exists_bound_of_continuousOn
    (E := E →L[ℝ] E →L[ℝ] E) hD2.continuousOn
  set C₂ : ℝ := |C₁| * |C₃| with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hC : ∀ ζ : ι → E, (∀ b, ‖ζ b‖ ≤ r₁) → ∀ x, ‖x‖ ≤ Rb → ∀ b v,
      |fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ x v v))| ≤ C₂ * ‖v‖ ^ 2 := by
    intro ζ hζ x hx b v
    have g1 := hC₁ ζ (hmem ζ hζ)
    have g2 := hC₃ x (by simpa using hx)
    have g3 : ‖secondDerivVec τ₀ x v v‖ ≤ |C₃| * ‖v‖ ^ 2 := by
      rw [secondDerivVec_eq_fderiv_fderiv hτ.contDiffAt]
      calc ‖fderiv ℝ (fderiv ℝ τ₀) x v v‖ ≤ ‖fderiv ℝ (fderiv ℝ τ₀) x v‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fderiv ℝ τ₀) x‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (|C₃| * ‖v‖) * ‖v‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (norm_nonneg _)
            exact le_trans g2 (le_abs_self _)
        _ = _ := by ring
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ U ζ (Pi.single b (secondDerivVec τ₀ x v v))‖
        ≤ ‖fderiv ℝ U ζ‖ * ‖(Pi.single b (secondDerivVec τ₀ x v v) : ι → E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ U ζ‖ * ‖secondDerivVec τ₀ x v v‖ := by rw [Pi.norm_single]
      _ ≤ |C₁| * (|C₃| * ‖v‖ ^ 2) := mul_le_mul (le_trans g1 (le_abs_self _)) g3 (norm_nonneg _) (abs_nonneg _)
      _ = _ := by rw [hC₂]; ring
  set ε' := ε / ((Fintype.card ι : ℝ) + 1) with hε'
  have hε'p : 0 < ε' := by positivity
  have hr2 : 0 < r₀ ^ 2 := by positivity
  obtain ⟨n, hn1, hn2⟩ := exists_barrier_power (a := (m + C₂) * r₀ ^ 2 / 2) (q₁ := ρ₀ ^ 2 / r₀ ^ 2)
    (q₂ := ρ ^ 2 / r₀ ^ 2) (ε := ε') (T := T - Umin) (by positivity) (by positivity)
    (by rw [div_lt_one hr2]; nlinarith)
    (by rw [one_lt_div hr2]; nlinarith [h2, h3]) hε'p
  set c : ℝ := (m + C₂) / (2 * (n + 2) * (r₀ ^ 2) ^ (n + 1)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcq : ∀ q : ℝ, (m + C₂) * r₀ ^ 2 / 2 / (n + 2) * (q / r₀ ^ 2) ^ (n + 2) = c * q ^ (n + 2) := by
    intro q
    rw [hc, div_pow, pow_succ (r₀ ^ 2) (n + 1)]
    field_simp
  rw [hcq] at hn1 hn2
  set ψ : E → ℝ := radialPower c n with hψ
  have hψc : ContDiff ℝ 2 ψ := contDiff_radialPower c n
  have hψnn : ∀ x, 0 ≤ ψ x := fun x => by
    simp only [hψ, radialPower]
    positivity
  have hτ' : ContDiff ℝ 2 (fun (z : ι → E) b => τ₀ (z b)) :=
    contDiff_pi.mpr fun b => hτ.comp (contDiff_apply ℝ E b)
  have hinn : ∀ z : ι → E, ∀ b, ‖τ₀ (z b)‖ < ρ := fun z b => lt_of_le_of_lt (hin _) h3
  refine ⟨fun z => U (fun b => τ₀ (z b)) + ∑ b, ψ (z b), ?_, ?_, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun η => ?_
    have g1 : ContDiffAt ℝ 2 (fun z : ι → E => U (fun b => τ₀ (z b))) η :=
      ContDiffAt.comp η (hU _ (hinn η)) hτ'.contDiffAt
    have g2 : ContDiffAt ℝ 2 (fun z : ι → E => ∑ b, ψ (z b)) η :=
      ContDiffAt.sum fun b _ => (hψc.comp (contDiff_apply ℝ E b)).contDiffAt
    exact g1.add g2
  · intro η hη
    have g1 : (fun b => τ₀ (η b)) = η := by
      funext b
      exact (pullInside_eventuallyEq_id hr₀ h2 (lt_of_le_of_lt (hη b) h1)).self_of_nhds
    simp only [g1, add_sub_cancel_left]
    have g2 : ∀ b, ψ (η b) ≤ ε' := by
      intro b
      have g3 : ‖η b‖ ^ 2 ≤ ρ₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hη b) 2
      have g4 : (‖η b‖ ^ 2) ^ (n + 2) ≤ (ρ₀ ^ 2) ^ (n + 2) := pow_le_pow_left₀ (by positivity) g3 _
      have := mul_le_mul_of_nonneg_left g4 hc0
      simp only [hψ, radialPower]
      linarith
    rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => hψnn _)]
    calc ∑ b, ψ (η b) ≤ ∑ _b : ι, ε' := Finset.sum_le_sum fun b _ => g2 b
      _ = (Fintype.card ι : ℝ) * ε' := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ε := by
          rw [hε', mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  · intro η
    have g1 := hmin _ (hinn η)
    have g2 : 0 ≤ ∑ b, ψ (η b) := Finset.sum_nonneg fun b _ => hψnn _
    linarith
  · rintro η ⟨b, hb⟩
    have g1 := hmin _ (hinn η)
    have g2 : ψ (η b) ≤ ∑ b, ψ (η b) :=
      Finset.single_le_sum (f := fun b => ψ (η b)) (fun b _ => hψnn _) (Finset.mem_univ b)
    have g3 : ρ ^ 2 ≤ ‖η b‖ ^ 2 := pow_le_pow_left₀ (by linarith) hb 2
    have g4 : (ρ ^ 2) ^ (n + 2) ≤ (‖η b‖ ^ 2) ^ (n + 2) := pow_le_pow_left₀ (by positivity) g3 _
    have g5 := mul_le_mul_of_nonneg_left g4 hc0
    have g6 : c * (ρ ^ 2) ^ (n + 2) ≤ ψ (η b) := g5
    linarith
  · intro b₀ η hη v
    refine extended_form_lower (r₀ := r₀) (r₁ := r₁) (Rb := Rb) (C₂ := C₂) (wf b₀) (hw b₀) hτ hψc hUr
      (fun ζ hζ v => hUform b₀ ζ (fun b => lt_of_le_of_lt (hζ b) h3) v) hin
      (fun x hx => pullInside_eventuallyEq_id hr₀ h2 hx) (fun x v => secondDeriv_radialPower_nonneg hc0 n x v) ?_ hm.le hC η hη v
    intro x v hx _
    refine le_trans ?_ (secondDeriv_radialPower_ge hc0 n x v)
    have g1 : r₀ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hr₀.le hx 2
    have g2 : (r₀ ^ 2) ^ (n + 1) ≤ (‖x‖ ^ 2) ^ (n + 1) := pow_le_pow_left₀ hr2.le g1 _
    have g3 : m + C₂ = 2 * c * (n + 2) * (r₀ ^ 2) ^ (n + 1) := by
      rw [hc]
      field_simp
    rw [g3]
    have g4 : 0 ≤ 2 * c * ((n : ℝ) + 2) := by positivity
    have := mul_le_mul_of_nonneg_left g2 g4
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
section MidpointConvexity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem continuousAt_secondDeriv {Φ : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 Φ x) (u v : E) :
    ContinuousAt (fun ζ => secondDeriv Φ ζ u v) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) x := h.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun ζ => fderiv ℝ Φ ζ u) x := h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℝ 0 (fderiv ℝ (fun ζ => fderiv ℝ Φ ζ u)) x := h2.fderiv_right (by norm_num)
  exact h3.continuousAt.clm_apply continuousAt_const
theorem secondDeriv_nonneg_of_midpoint {Φ : E → ℝ} {S : Set E} (hS : IsOpen S) {x : E} (hx : x ∈ S)
    (hC : ∀ z ∈ S, ContDiffAt ℝ 2 Φ z)
    (hmid : ∀ y w, y - w ∈ S → y + w ∈ S → y ∈ S → 2 * Φ y ≤ Φ (y - w) + Φ (y + w)) (v : E) :
    0 ≤ secondDeriv Φ x v v := by
  by_contra hneg
  push Not at hneg
  have h1 : ∀ᶠ ζ in 𝓝 x, secondDeriv Φ ζ v v < 0 :=
    (continuousAt_secondDeriv (hC x hx) v v).eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ ζ in 𝓝 x, ζ ∈ S := hS.mem_nhds hx
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  set s := ε / (4 * (‖v‖ + 1)) with hs
  have hsp : 0 < s := by positivity
  have hsv : s * ‖v‖ < ε / 4 := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  set y := x - s • v with hy
  have hnear : ∀ t ∈ Icc 0 s, ∀ t' ∈ Icc 0 s, dist (y + t • v + t' • v) x < ε := by
    intro t ht t' ht'
    have e : y + t • v + t' • v - x = (t + t' - s) • v := by
      simp only [hy, sub_smul, add_smul]
      abel
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs]
    have h3 : |t + t' - s| ≤ s := abs_le.mpr ⟨by linarith [ht.1, ht'.1, ht.2], by linarith [ht.2, ht'.2]⟩
    have := mul_le_mul_of_nonneg_right h3 (norm_nonneg v)
    linarith
  obtain ⟨t, ht, t', ht', e⟩ := mixed_difference_eq Φ y v v hsp fun t ht t' ht' =>
    hC _ (hball (hnear t ht t' ht')).2
  have e1 : y + s • v = x := by simp [hy]
  have hz : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl, hsp.le⟩
  have hs1 : s ∈ Icc 0 s := ⟨hsp.le, le_rfl⟩
  have m1 : x - s • v ∈ S := by
    have := (hball (hnear 0 hz 0 hz)).2
    simpa [hy] using this
  have m2 : x + s • v ∈ S := by
    have := (hball (hnear s hs1 s hs1)).2
    rwa [e1] at this
  have h4 := hmid x (s • v) m1 m2 hx
  rw [e1] at e
  have h5 := (hball (hnear t ht t' ht')).1
  have h6 : 0 < s ^ 2 := by positivity
  have h7 := mul_neg_of_pos_of_neg h6 h5
  rw [← e, hy] at h7
  linarith
end MidpointConvexity
section Cutoff
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoff_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < ρ) : 0 ≤ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoff_nonneg_of_lt <;> assumption
theorem cutoff_mono (hρ : 0 < ρ) (hp : IsCutoff ρ p) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < ρ) :
    p a ≤ p b := by
  have hb0 : 0 ≤ p b := cutoff_nonneg hρ hp (ha.trans hab) hb
  by_cases h : a ≤ 5 * ρ / 8
  · rw [hp.vanish_small a ha h]
    exact hb0
  push Not at h
  have hz : (0 : ℝ) ∈ Ico 0 ρ := ⟨le_rfl, hρ⟩
  have hbm : b ∈ Ico 0 ρ := ⟨ha.trans hab, hb⟩
  have hbpos : 0 < b := by linarith [show 0 < 5 * ρ / 8 by positivity]
  set l := a / b with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := (div_le_one hbpos).mpr hab
  have h2 := hp.convex.2 hz hbm (sub_nonneg.mpr hl1) hl0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at h2
  have e : l * b = a := div_mul_cancel₀ _ hbpos.ne'
  rw [e, hp.vanish_small 0 le_rfl (by positivity)] at h2
  nlinarith
theorem contDiffAt_cutoff_norm (hρ : 0 < ρ) (hp : IsCutoff ρ p) {x : BondVector} (hx : ‖x‖ < ρ) :
    ContDiffAt ℝ 2 (fun z : BondVector => p ‖z‖) x := by
  by_cases h : ‖x‖ < 5 * ρ / 8
  · have ev : (fun z : BondVector => p ‖z‖) =ᶠ[𝓝 x] fun _ => 0 := by
      have : ∀ᶠ z in 𝓝 x, ‖z‖ < 5 * ρ / 8 := continuous_norm.continuousAt.eventually (gt_mem_nhds h)
      filter_upwards [this] with z hz
      exact hp.vanish_small _ (norm_nonneg z) hz.le
    exact contDiffAt_const.congr_of_eventuallyEq ev
  · push Not at h
    have hne : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith [show 0 < 5 * ρ / 8 by positivity]
    have hnpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have h1 : ContDiffAt ℝ 2 p ‖x‖ := by
      have h5 : ContDiffOn ℝ 2 p (Ico 0 ρ) := by
        exact_mod_cast contDiffOn_infty.mp hp.smooth 2
      exact h5.contDiffAt (Ico_mem_nhds hnpos hx)
    exact h1.comp x (contDiffAt_norm ℝ hne)
theorem secondDeriv_cutoff_norm_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {x : BondVector} (hx : ‖x‖ < ρ) (v : BondVector) :
    0 ≤ secondDeriv (fun z : BondVector => p ‖z‖) x v v := by
  refine secondDeriv_nonneg_of_midpoint (S := Metric.ball 0 ρ) Metric.isOpen_ball (by simpa using hx)
    (fun z hz => contDiffAt_cutoff_norm hρ hp (by simpa using hz)) ?_ v
  intro y w h1 h2 h3
  have n1 : ‖y - w‖ < ρ := by simpa using h1
  have n2 : ‖y + w‖ < ρ := by simpa using h2
  have m1 : ‖y - w‖ ∈ Ico 0 ρ := ⟨norm_nonneg _, n1⟩
  have m2 : ‖y + w‖ ∈ Ico 0 ρ := ⟨norm_nonneg _, n2⟩
  have hc := hp.convex.2 m1 m2 (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have ht : ‖y‖ ≤ 1 / 2 * ‖y - w‖ + 1 / 2 * ‖y + w‖ := by
    have e : y = (1 / 2 : ℝ) • (y - w) + (1 / 2 : ℝ) • (y + w) := by
      simp only [smul_sub, smul_add]
      have : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y = y := by
        rw [← add_smul]
        norm_num
      calc y = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y := this.symm
        _ = _ := by abel
    calc ‖y‖ = ‖(1 / 2 : ℝ) • (y - w) + (1 / 2 : ℝ) • (y + w)‖ := by rw [← e]
      _ ≤ ‖(1 / 2 : ℝ) • (y - w)‖ + ‖(1 / 2 : ℝ) • (y + w)‖ := norm_add_le _ _
      _ = _ := by
          have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
          rw [norm_smul, norm_smul, h2]
  have hm := cutoff_mono hρ hp (norm_nonneg y) ht
    (by have := hc; linarith)
  linarith
end Cutoff
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem pseudoMetric_nonneg {d : ι → ι → ℝ} (hd : IsPseudoMetricOnBonds d) (b b' : ι) : 0 ≤ d b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.pseudoMetric_nonneg <;> assumption
theorem abs_exp_sub_one_le_exp_two_mul {t T : ℝ} (h : |t| ≤ T) : |Real.exp t - 1| ≤ Real.exp (2 * T) - 1 := by
  have hT : 0 ≤ T := le_trans (abs_nonneg _) h
  have h1 := abs_le.mp h
  have e1 : Real.exp T ≤ Real.exp (2 * T) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp t ≤ Real.exp T := Real.exp_le_exp.mpr h1.2
  have e3 : Real.exp (-T) ≤ Real.exp t := Real.exp_le_exp.mpr h1.1
  have e4 := Real.add_one_le_exp (-T)
  have e5 := Real.add_one_le_exp T
  exact abs_le.mpr ⟨by linarith, by linarith⟩
set_option maxHeartbeats 1000000 in
theorem weighted_hessian_lower {ρ m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d) (hΨ : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (b₀ : ι) (ζ : BondField ι) (hζ : ∀ b, ‖ζ b‖ < ρ) (v : BondField ι) :
    m * ∑ b, Real.exp (-(κ * d b₀ b)) ^ 2 * ‖v b‖ ^ 2
      ≤ ∑ b, Real.exp (-(κ * d b₀ b)) ^ 2 * secondDeriv Ψ ζ (Pi.single b (v b)) v := by
  set a : ι → ℝ := fun b => Real.exp (-(κ * d b₀ b)) with ha
  have hapos : ∀ b, 0 < a b := fun b => Real.exp_pos _
  have hC : ContDiffAt ℝ 2 Ψ ζ := (hΨ.smooth.of_le (by norm_num)).contDiffAt
  set y : BondField ι := fun b => a b • v b with hy
  have hsingle : ∀ b, (Pi.single b (v b) : BondField ι) = (a b)⁻¹ • (Pi.single b (y b) : BondField ι) := by
    intro b
    rw [← Pi.single_smul, hy]
    simp only
    rw [smul_smul, inv_mul_cancel₀ (hapos b).ne', one_smul]
  have hvs : v = ∑ b', (Pi.single b' (v b') : BondField ι) := (Finset.univ_sum_single v).symm
  have hys : y = ∑ b', (Pi.single b' (y b') : BondField ι) := (Finset.univ_sum_single y).symm
  set Hm : ι → ι → ℝ := fun b b' => secondDeriv Ψ ζ (Pi.single b (y b)) (Pi.single b' (y b')) with hHm
  have e1 : ∀ b, a b ^ 2 * secondDeriv Ψ ζ (Pi.single b (v b)) v = ∑ b', (a b / a b') * Hm b b' := by
    intro b
    conv_lhs => rw [hvs]
    rw [secondDeriv_sum_right _ hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    have hvb : (∑ b'', (Pi.single b'' (v b'') : BondField ι)) b = v b := by
      rw [← hvs]
    rw [hvb, hsingle b, hsingle b', secondDeriv_smul_left hC, secondDeriv_smul_right hC]
    have h1 := (hapos b).ne'
    have h2 := (hapos b').ne'
    simp only [hHm]
    field_simp
  have e2 : ∑ b, ∑ b', Hm b b' = secondDeriv Ψ ζ y y := by
    conv_rhs => rw [hys]
    rw [secondDeriv_sum_left _ hC]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [secondDeriv_sum_right _ hC]
  have hfl := hΨ.floor ζ hζ y
  have hker : ∀ b b', |Hm b b'| ≤ K b b' * ‖y b‖ * ‖y b'‖ := fun b b' => hΨ.kernel ζ hζ b b' (y b) (y b')
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    have h0 : ∀ c : ι, ‖(0 : BondField ι) c‖ < ρ := fun c => by simpa using hρ
    have h1 := hΨ.kernel 0 h0 b b' (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  set Gk : ι → ι → ℝ := fun b b' => Real.exp (2 * κ * d b b') - 1 with hGk
  have hG0 : ∀ b b', 0 ≤ Gk b b' := by
    intro b b'
    have : 0 ≤ 2 * κ * d b b' := mul_nonneg (by positivity) (pseudoMetric_nonneg hd b b')
    have := Real.add_one_le_exp (2 * κ * d b b')
    simp only [hGk]
    linarith
  have hr : ∀ b b', |a b / a b' - 1| ≤ Gk b b' := by
    intro b b'
    have e : a b / a b' = Real.exp (κ * (d b₀ b' - d b₀ b)) := by
      simp only [ha]
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [e]
    have hT : |κ * (d b₀ b' - d b₀ b)| ≤ κ * d b b' := by
      rw [abs_mul, abs_of_nonneg hκ]
      refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) hκ
      · have := hd.triangle b₀ b' b
        rw [hd.symm b' b] at this
        linarith
      · have := hd.triangle b₀ b b'
        linarith
    have := abs_exp_sub_one_le_exp_two_mul hT
    have e3 : 2 * (κ * d b b') = 2 * κ * d b b' := by ring
    rw [e3] at this
    exact this
  have hterm : ∀ b b', Hm b b' - Gk b b' * K b b' * (‖y b‖ ^ 2 + ‖y b'‖ ^ 2) / 2
      ≤ (a b / a b') * Hm b b' := by
    intro b b'
    have h1 : |(a b / a b' - 1) * Hm b b'| ≤ Gk b b' * (K b b' * ‖y b‖ * ‖y b'‖) := by
      rw [abs_mul]
      exact mul_le_mul (hr b b') (hker b b') (abs_nonneg _) (hG0 b b')
    have h2 : K b b' * ‖y b‖ * ‖y b'‖ ≤ K b b' * (‖y b‖ ^ 2 + ‖y b'‖ ^ 2) / 2 := by
      have := mul_nonneg (hK0 b b') (sq_nonneg (‖y b‖ - ‖y b'‖))
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (hG0 b b')
    have h4 := (abs_le.mp h1).1
    nlinarith
  have hrow : ∀ b, ∑ b', K b b' * Gk b b' ≤ m := hΨ.standingConstraints
  have hrow' : ∀ b', ∑ b, K b b' * Gk b b' ≤ m := by
    intro b'
    have : ∑ b, K b b' * Gk b b' = ∑ b, K b' b * Gk b' b :=
      Finset.sum_congr rfl fun b _ => by
        simp only [hGk]
        rw [hΨ.symm b b', hd.symm b b']
    rw [this]
    exact hrow b'
  have hN0 : ∀ b, 0 ≤ ‖y b‖ ^ 2 := fun b => by positivity
  set Y := ∑ b, ‖y b‖ ^ 2 with hY
  have hsum1 : ∑ b, ∑ b', Gk b b' * K b b' * ‖y b‖ ^ 2 ≤ m * Y := by
    rw [hY, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have e : ∑ b', Gk b b' * K b b' * ‖y b‖ ^ 2 = (∑ b', K b b' * Gk b b') * ‖y b‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b' _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (hrow b) (hN0 b)
  have hsum2 : ∑ b, ∑ b', Gk b b' * K b b' * ‖y b'‖ ^ 2 ≤ m * Y := by
    rw [Finset.sum_comm, hY, Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    have e : ∑ b, Gk b b' * K b b' * ‖y b'‖ ^ 2 = (∑ b, K b b' * Gk b b') * ‖y b'‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (hrow' b') (hN0 b')
  have hmain : ∑ b, ∑ b', Hm b b'
      - (∑ b, ∑ b', Gk b b' * K b b' * ‖y b‖ ^ 2 + ∑ b, ∑ b', Gk b b' * K b b' * ‖y b'‖ ^ 2) / 2
      ≤ ∑ b, ∑ b', (a b / a b') * Hm b b' := by
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b' _ => ?_
    have := hterm b b'
    calc Hm b b' - (Gk b b' * K b b' * ‖y b‖ ^ 2 + Gk b b' * K b b' * ‖y b'‖ ^ 2) / 2
        = Hm b b' - Gk b b' * K b b' * (‖y b‖ ^ 2 + ‖y b'‖ ^ 2) / 2 := by ring
      _ ≤ _ := this
  have hya : ∑ b, a b ^ 2 * ‖v b‖ ^ 2 = Y := by
    rw [hY]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hy]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hapos b)]
    ring
  have hfin : ∑ b, a b ^ 2 * secondDeriv Ψ ζ (Pi.single b (v b)) v = ∑ b, ∑ b', (a b / a b') * Hm b b' :=
    Finset.sum_congr rfl fun b _ => e1 b
  rw [hfin, hya]
  rw [e2] at hmain
  have : 2 * m * Y ≤ secondDeriv Ψ ζ y y := hfl
  linarith
def ballPotential (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  (∑ b, p ‖η b‖) + Ψ η
theorem contDiffAt_ballPotential {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : ContDiff ℝ 3 Ψ) (ζ : BondField ι) (hζ : ∀ b, ‖ζ b‖ < ρ) :
    ContDiffAt ℝ 2 (ballPotential ρ p Ψ) ζ := by
  refine ContDiffAt.add (ContDiffAt.sum fun b _ => ?_) (hΨ.of_le (by norm_num)).contDiffAt
  exact ContDiffAt.comp (g := fun z : BondVector => p ‖z‖) ζ (contDiffAt_cutoff_norm hρ hp (hζ b))
    (contDiff_apply ℝ BondVector b).contDiffAt
theorem ballPotential_form_lower {ρ m κ : ℝ} {p : ℝ → ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hp : IsCutoff ρ p) (hd : IsPseudoMetricOnBonds d) (hΨ : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (b₀ : ι) (ζ : BondField ι) (hζ : ∀ b, ‖ζ b‖ < ρ) (v : BondField ι) :
    m * ∑ b, Real.exp (-(κ * d b₀ b)) ^ 2 * ‖v b‖ ^ 2
      ≤ ∑ b, Real.exp (-(κ * d b₀ b)) ^ 2 * secondDeriv (ballPotential ρ p Ψ) ζ (Pi.single b (v b)) v := by
  refine le_trans (weighted_hessian_lower hρ hκ hd hΨ b₀ ζ hζ v) (Finset.sum_le_sum fun b _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc : ∀ b' ∈ (Finset.univ : Finset ι), ContDiffAt ℝ 2 (fun z : BondField ι => p ‖z b'‖) ζ := fun b' _ =>
    ContDiffAt.comp (g := fun z : BondVector => p ‖z‖) ζ (contDiffAt_cutoff_norm hρ hp (hζ b'))
      (contDiff_apply ℝ BondVector b').contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun z : BondField ι => ∑ b', p ‖z b'‖) ζ := ContDiffAt.sum hc
  have hC : ContDiffAt ℝ 2 Ψ ζ := (hΨ.smooth.of_le (by norm_num)).contDiffAt
  have e : secondDeriv (ballPotential ρ p Ψ) ζ (Pi.single b (v b)) v
      = secondDeriv (fun z : BondField ι => ∑ b', p ‖z b'‖) ζ (Pi.single b (v b)) v
        + secondDeriv Ψ ζ (Pi.single b (v b)) v := secondDeriv_add hc2 hC _ _
  rw [e, secondDeriv_sum _ hc]
  have e3 : ∑ b', secondDeriv (fun z : BondField ι => p ‖z b'‖) ζ (Pi.single b (v b)) v
      = secondDeriv (fun z : BondVector => p ‖z‖) (ζ b) (v b) (v b) := by
    rw [Finset.sum_eq_single b]
    · rw [secondDeriv_proj (ψ := fun z : BondVector => p ‖z‖) b (contDiffAt_cutoff_norm hρ hp (hζ b))]
      simp
    · intro b' _ h
      rw [secondDeriv_proj (ψ := fun z : BondVector => p ‖z‖) b' (contDiffAt_cutoff_norm hρ hp (hζ b'))]
      simp [Pi.single_eq_of_ne h, secondDeriv_zero_left]
    · simp
  rw [e3]
  have := secondDeriv_cutoff_norm_nonneg hρ hp (hζ b) (v b)
  linarith
theorem exists_ballPotential_lower {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : ∃ Umin : ℝ, ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → Umin ≤ ballPotential ρ p Ψ ζ := by
  have hS : IsCompact (Set.pi univ fun _ : ι => Metric.closedBall (0 : BondVector) ρ) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 ρ
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hΨ.continuousOn
  refine ⟨-C, fun ζ hζ => ?_⟩
  have h1 := hC ζ fun b _ => by simpa using (hζ b).le
  have h2 : 0 ≤ ∑ b, p ‖ζ b‖ := Finset.sum_nonneg fun b _ => cutoff_nonneg hρ hp (norm_nonneg _) (hζ b)
  have h3 := (abs_le.mp (by simpa using h1 : |Ψ ζ| ≤ C)).1
  unfold ballPotential
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def coordEquiv (ι : Type) [Fintype ι] [DecidableEq ι] : (ι × Fin 3 → ℝ) ≃ₗ[ℝ] BondField ι where
  toFun y b := WithLp.toLp 2 fun i => y (b, i)
  invFun η j := η j.1 j.2
  map_add' y y' := by
    funext b
    ext i
    simp
  map_smul' c y := by
    funext b
    ext i
    simp
  left_inv y := by
    funext j
    simp
  right_inv η := by
    funext b
    ext i
    simp
def coordCLE (ι : Type) [Fintype ι] [DecidableEq ι] : (ι × Fin 3 → ℝ) ≃L[ℝ] BondField ι :=
  (coordEquiv ι).toContinuousLinearEquiv
def coordMap (ι : Type) [Fintype ι] [DecidableEq ι] : (ι × Fin 3 → ℝ) →L[ℝ] BondField ι :=
  (coordCLE ι : (ι × Fin 3 → ℝ) →L[ℝ] BondField ι)
theorem coordMap_apply (y : ι × Fin 3 → ℝ) (b : ι) (i : Fin 3) : (coordMap ι y b) i = y (b, i) := rfl
theorem norm_sq_coordMap (y : ι × Fin 3 → ℝ) (b : ι) : ‖coordMap ι y b‖ ^ 2 = ∑ i, y (b, i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl
theorem exists_haar_scale : ∃ c : ℝ, 0 < c ∧ ∀ G : BondField ι → ℝ,
    ∫ y, G (coordMap ι y) = c * ∫ x, G x := by
  set μ : Measure (BondField ι) := (volume : Measure (ι × Fin 3 → ℝ)).map (coordCLE ι) with hμ
  have : μ.IsAddHaarMeasure := (coordCLE ι).isAddHaarMeasure_map volume
  have h : μ = Measure.addHaarScalarFactor μ volume • volume :=
    Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨(Measure.addHaarScalarFactor μ volume : ℝ), ?_, fun G => ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  · have e1 : ∫ x, G x ∂μ = ∫ y, G (coordMap ι y) :=
      (coordCLE ι).toHomeomorph.measurableEmbedding.integral_map G
    rw [← e1]
    conv_lhs => rw [h]
    rw [integral_smul_nnreal_measure]
    rfl
theorem norm_sq_linearForm (A : BondVector →L[ℝ] ℝ) :
    ‖A‖ ^ 2 = ∑ i, (A (EuclideanSpace.single i 1)) ^ 2 := by
  set a : BondVector := WithLp.toLp 2 fun i => A (EuclideanSpace.single i 1) with ha
  have hv : ∀ v : BondVector, A v = ∑ i, v i * A (EuclideanSpace.single i 1) := by
    intro v
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [map_sum]
  have hA : A = innerSL ℝ a := by
    ext v
    rw [hv]
    simp [PiLp.inner_apply, ha, mul_comm]
  rw [hA, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hA]
theorem coordDir_coordMap (b : ι) (i : Fin 3) :
    coordDir (coordMap ι) (b, i) = Pi.single b (EuclideanSpace.single i 1) := by
  unfold coordDir
  funext b'
  ext i'
  rw [coordMap_apply]
  by_cases h : b' = b
  · subst h
    by_cases h2 : i' = i
    · subst h2; simp
    · simp [Pi.single_apply, h2]
  · simp [Pi.single_apply, h]
theorem bondGradSq_eq (f : BondField ι → ℝ) (b : ι) (x : BondField ι) :
    bondGradSq Prod.fst (coordMap ι) f b x = bondGradNorm f b x ^ 2 := by
  unfold bondGradSq bondGradNorm
  rw [norm_sq_linearForm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [if_true]
    rw [coordDir_coordMap]
    rfl
  · intro b' _ h
    simp [h]
  · simp
theorem form_in_coords {Φ : BondField ι → ℝ} {x : BondField ι} (hC : ContDiffAt ℝ 2 Φ x)
    (w : ι → ℝ) {m : ℝ}
    (hform : ∀ v : BondField ι, m * ∑ b, w b * ‖v b‖ ^ 2 ≤ ∑ b, w b * secondDeriv Φ x (Pi.single b (v b)) v)
    (ξ : ι × Fin 3 → ℝ) :
    m * ∑ j, w j.1 * ξ j ^ 2 ≤ ∑ j, ∑ i, w j.1 * secondDeriv Φ x (coordDir (coordMap ι) j) (coordDir (coordMap ι) i) * ξ j * ξ i := by
  set v : BondField ι := coordMap ι ξ with hv
  have hsum : ∀ η : ι × Fin 3 → ℝ, coordMap ι η = ∑ j, η j • coordDir (coordMap ι) j := by
    intro η
    unfold coordDir
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    conv_lhs => rw [← Finset.univ_sum_single η]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul]
    simp
  have hsingle : ∀ b, (Pi.single b (v b) : BondField ι)
      = coordMap ι (fun j => if j.1 = b then ξ j else 0) := by
    intro b
    funext b'
    ext i
    rw [coordMap_apply]
    by_cases h : b' = b
    · subst h
      simp [hv, coordMap_apply]
    · simp [Pi.single_apply, h]
  have e1 : ∀ b, secondDeriv Φ x (Pi.single b (v b)) v
      = ∑ j, ∑ i, (if j.1 = b then ξ j else 0) * ξ i * secondDeriv Φ x (coordDir (coordMap ι) j) (coordDir (coordMap ι) i) := by
    intro b
    rw [hsingle b]
    conv_lhs => rw [hv, hsum ξ, hsum (fun j => if j.1 = b then ξ j else 0)]
    rw [secondDeriv_sum_left _ hC]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [secondDeriv_smul_left hC, secondDeriv_sum_right _ hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [secondDeriv_smul_right hC]
    ring
  have e2 : ∑ b, w b * secondDeriv Φ x (Pi.single b (v b)) v
      = ∑ j, ∑ i, w j.1 * secondDeriv Φ x (coordDir (coordMap ι) j) (coordDir (coordMap ι) i) * ξ j * ξ i := by
    simp only [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j.1]
    · simp only [if_true]
      ring
    · intro b _ h
      simp [Ne.symm h]
    · simp
  have e3 : ∑ b, w b * ‖v b‖ ^ 2 = ∑ j, w j.1 * ξ j ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hv, norm_sq_coordMap, Finset.mul_sum]
  have := hform v
  rw [e2, e3] at this
  exact this
theorem exists_weight_ratio {J : Type} [Fintype J] (Dk : ι → J → ℝ) (hD : ∀ b j, 0 < Dk b j) :
    ∃ Wr : ℝ, 0 ≤ Wr ∧ ∀ b i j, Dk b j ^ 2 ≤ Wr * Dk b i ^ 2 := by
  set q : ι × J × J → ℝ := fun a => Dk a.1 a.2.2 ^ 2 / Dk a.1 a.2.1 ^ 2 with hq
  have hq0 : ∀ a, 0 ≤ q a := fun a => by positivity
  refine ⟨∑ a, q a, Finset.sum_nonneg fun a _ => hq0 a, fun b i j => ?_⟩
  have h1 : q (b, i, j) ≤ ∑ a, q a :=
    Finset.single_le_sum (fun a _ => hq0 a) (Finset.mem_univ _)
  have h2 : 0 < Dk b i ^ 2 := by have := hD b i; positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2.le
  have h4 : q (b, i, j) * Dk b i ^ 2 = Dk b j ^ 2 := by
    simp only [hq]
    exact div_mul_cancel₀ _ h2.ne'
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
noncomputable section
open Set Filter Topology MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem ballDensity_eq_exp {ρ : ℝ} {p : ℝ → ℝ} {Ψ η : _} (hη : ∀ b : ι, ‖η b‖ < ρ) :
    ballDensity (cutoffFactor ρ p) Ψ η = Real.exp (-ballPotential ρ p Ψ η) := by
  unfold ballDensity radialWeightProd ballPotential
  have e : ∏ b, cutoffFactor ρ p ‖η b‖ = Real.exp (∑ b, -p ‖η b‖) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun b _ => by simp [cutoffFactor, hη b]
  rw [e, ← Real.exp_add]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
theorem ballDensity_eq_zero {ρ : ℝ} {p : ℝ → ℝ} {Ψ η : _} (hη : ∃ b : ι, ρ ≤ ‖η b‖) :
    ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  obtain ⟨b, hb⟩ := hη
  unfold ballDensity radialWeightProd
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
theorem volume_halfOpenBox_lt_top {J : Type} [Fintype J] (R : ℝ) : volume (halfOpenBox J R) < ⊤ := by
  unfold halfOpenBox
  rw [Real.volume_pi_Ioc (a := fun _ => -R) (b := fun _ => R)]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
theorem tendsto_one_div_add_two : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 2)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun N => ?_
  simp only [Function.comp]
  push_cast
  ring_nf
theorem exists_large_of_not_mem_halfOpenBox {ρ : ℝ} {y : ι × Fin 3 → ℝ} (hy : y ∉ halfOpenBox (ι × Fin 3) ρ) :
    ∃ b, ρ ≤ ‖coordMap ι y b‖ := by
  unfold halfOpenBox at hy
  simp only [Set.mem_pi, mem_univ, forall_true_left, not_forall] at hy
  obtain ⟨j, hj⟩ := hy
  refine ⟨j.1, ?_⟩
  have h1 : ρ ≤ |y j| := by
    by_contra hc
    push Not at hc
    exact hj ⟨by linarith [(abs_lt.mp hc).1], (abs_lt.mp hc).2.le⟩
  have h2 : y j ^ 2 ≤ ‖coordMap ι y j.1‖ ^ 2 := by
    rw [norm_sq_coordMap]
    have := Finset.single_le_sum (f := fun i => y (j.1, i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j.2)
    simpa using this
  have h3 : |y j| ≤ ‖coordMap ι y j.1‖ := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  linarith
theorem norm_lt_of_mem_halfOpenBox_half {ρ : ℝ} (hρ : 0 < ρ) {y : ι × Fin 3 → ℝ} (hy : y ∈ halfOpenBox (ι × Fin 3) (ρ / 2))
    (b : ι) : ‖coordMap ι y b‖ < ρ := by
  have h1 : ‖coordMap ι y b‖ ^ 2 < ρ ^ 2 := by
    rw [norm_sq_coordMap]
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), y (b, i) ^ 2 ≤ (ρ / 2) ^ 2 := by
      intro i _
      have := hy (b, i) (mem_univ _)
      exact sq_le_sq' (by linarith [this.1]) this.2
    have h3 := Finset.sum_le_sum h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    have : (0 : ℝ) < ρ ^ 2 := by positivity
    push_cast at h3
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hρ.le h1
theorem norm_le_of_mem_image_closedCube {ρ : ℝ} (hρ : 0 < ρ) {x : BondField ι}
    (hx : x ∈ coordMap ι '' closedCube (ι × Fin 3) ρ) (b : ι) : ‖x b‖ ≤ 2 * ρ := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ‖coordMap ι y b‖ ^ 2 ≤ (2 * ρ) ^ 2 := by
    rw [norm_sq_coordMap]
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), y (b, i) ^ 2 ≤ ρ ^ 2 := by
      intro i _
      have := hy (b, i) (mem_univ _)
      exact sq_le_sq' this.1 this.2
    have h3 := Finset.sum_le_sum h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    push_cast at h3
    nlinarith [sq_nonneg ρ]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1
set_option maxHeartbeats 2000000 in
theorem ball_covariance_bound (ρ m κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ)
    (p : ℝ → ℝ) (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hp : IsCutoff ρ p) (hd : IsPseudoMetricOnBonds d)
    (hΨ : IsUniformlyConvexDecaying ρ m κ d Ψ K) (f g : BondField ι → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤ m⁻¹ * ∑ b, ∑ b',
      ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b') := by
  have hΨc : Continuous Ψ := hΨ.smooth.continuous
  obtain ⟨Umin, hUmin⟩ := exists_ballPotential_lower hρ hp hΨc
  set U := ballPotential ρ p Ψ with hU
  set wf : ι → ι → ℝ := fun b₀ b => Real.exp (-(κ * d b₀ b)) ^ 2 with hwf
  have hex : ∀ N : ℕ, ∃ Φ : BondField ι → ℝ, ContDiff ℝ 2 Φ ∧
      (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ * (1 - 1 / ((N : ℝ) + 2))) → |Φ η - U η| ≤ 1 / ((N : ℝ) + 1)) ∧
      (∀ η, Umin ≤ Φ η) ∧
      (∀ η : BondField ι, (∃ b, ρ ≤ ‖η b‖) → (N : ℝ) ≤ Φ η) ∧
      (∀ b₀, ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ 2 * ρ) → ∀ v : BondField ι,
        m * ∑ b, wf b₀ b * ‖v b‖ ^ 2 ≤ ∑ b, wf b₀ b * secondDeriv Φ η (Pi.single b (v b)) v) := by
    intro N
    set t : ℝ := 1 / ((N : ℝ) + 2) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 2 := by
      rw [ht]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [show (0 : ℝ) ≤ N from by positivity])
    exact exists_convex_extension (ρ := ρ) (ρ₀ := ρ * (1 - t)) (r₀ := ρ * (1 - t / 2)) (r₁ := ρ * (1 - t / 3))
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) hm (by positivity) wf
      (fun _ _ => by positivity) (contDiffAt_ballPotential hρ hp hΨ.smooth)
      (fun b₀ ζ hζ v => ballPotential_form_lower hρ hκ hp hd hΨ b₀ ζ hζ v) hUmin
  choose Φ hΦ2 hnear hlow hhigh hform using hex
  set D : BondField ι → ℝ := ballDensity (cutoffFactor ρ p) Ψ with hD
  have hDbd : ∀ η, D η ≤ Real.exp (-Umin) := by
    intro η
    by_cases hO : ∀ b, ‖η b‖ < ρ
    · rw [hD, ballDensity_eq_exp hO]
      exact Real.exp_le_exp.mpr (by linarith [hUmin η hO])
    · push Not at hO
      rw [hD, ballDensity_eq_zero hO]
      exact (Real.exp_pos _).le
  have hD0 : ∀ η, 0 ≤ D η := by
    intro η
    by_cases hO : ∀ b, ‖η b‖ < ρ
    · rw [hD, ballDensity_eq_exp hO]
      exact (Real.exp_pos _).le
    · push Not at hO
      rw [hD, ballDensity_eq_zero hO]
  have hpt : ∀ η, Tendsto (fun N => Real.exp (-Φ N η)) atTop (𝓝 (D η)) := by
    intro η
    by_cases hO : ∀ b, ‖η b‖ < ρ
    · rw [hD, ballDensity_eq_exp hO]
      have e1 : ∀ᶠ N : ℕ in atTop, ∀ b, ‖η b‖ ≤ ρ * (1 - 1 / ((N : ℝ) + 2)) := by
        refine eventually_all.mpr fun b => ?_
        have h1 : Tendsto (fun N : ℕ => ρ * (1 - 1 / ((N : ℝ) + 2))) atTop (𝓝 (ρ * (1 - 0))) :=
          (tendsto_const_nhds.sub tendsto_one_div_add_two).const_mul ρ
        simp only [sub_zero, mul_one] at h1
        exact (h1.eventually (lt_mem_nhds (hO b))).mono fun N h => h.le
      have e2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have e3 : Tendsto (fun N => Φ N η) atTop (𝓝 (U η)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ e2
        filter_upwards [e1] with N hN
        exact hnear N η hN
      exact (Real.continuous_exp.tendsto _).comp e3.neg
    · push Not at hO
      rw [hD, ballDensity_eq_zero hO]
      have e1 : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
      refine squeeze_zero (fun N => (Real.exp_pos _).le) (fun N => ?_) e1
      exact Real.exp_le_exp.mpr (by linarith [hhigh N η hO])
  set J := ι × Fin 3
  set μ : Measure (J → ℝ) := volume.restrict (halfOpenBox J ρ) with hμ
  have hfin : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact volume_halfOpenBox_lt_top ρ⟩
  have hEc : Continuous (coordMap ι) := (coordMap ι).continuous
  have hI : ∀ h : BondField ι → ℝ, Continuous h →
      Tendsto (fun N => ∫ y in halfOpenBox J ρ, Real.exp (-Φ N (coordMap ι y)) * h (coordMap ι y)) atTop
        (𝓝 (∫ y in halfOpenBox J ρ, D (coordMap ι y) * h (coordMap ι y))) := by
    intro h hh
    obtain ⟨C, hC⟩ := (isCompact_closedCube (J := J) ρ).exists_bound_of_continuousOn
      (hh.comp hEc).continuousOn
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (-Umin) * C) ?_
      (integrable_const _) ?_ ?_
    · intro N
      exact (((Real.continuous_exp.comp ((hΦ2 N).continuous.comp hEc).neg).mul
        (hh.comp hEc))).aestronglyMeasurable
    · intro N
      refine ae_restrict_of_forall_mem (measurableSet_halfOpenBox ρ) fun y hy => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [hlow N (coordMap ι y)]))
        (hC y (halfOpenBox_subset_closedCube ρ hy)) (norm_nonneg _) (Real.exp_pos _).le
    · refine Eventually.of_forall fun y => ?_
      exact (hpt (coordMap ι y)).mul_const _
  have hI1 : Tendsto (fun N => ∫ y in halfOpenBox J ρ, Real.exp (-Φ N (coordMap ι y))) atTop
      (𝓝 (∫ y in halfOpenBox J ρ, D (coordMap ι y))) := by
    have := hI (fun _ => 1) continuous_const
    simpa using this
  have hDm : AEStronglyMeasurable (fun y => D (coordMap ι y)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => ((Real.continuous_exp.comp ((hΦ2 N).continuous.comp hEc).neg)).aestronglyMeasurable)
      (Eventually.of_forall fun y => hpt (coordMap ι y))
  have hDi : Integrable (fun y => D (coordMap ι y)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (-Umin))) hDm (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 _)]
    exact hDbd _
  have hpos : 0 < ∫ y in halfOpenBox J ρ, D (coordMap ι y) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun y => hD0 _) hDi]
    have hsub : halfOpenBox J (ρ / 2) ⊆ Function.support (fun y => D (coordMap ι y)) ∩ halfOpenBox J ρ := by
      intro y hy
      refine ⟨?_, fun j hj => ?_⟩
      · have h1 := norm_lt_of_mem_halfOpenBox_half hρ hy
        simp only [Function.mem_support]
        rw [hD, ballDensity_eq_exp h1]
        exact (Real.exp_pos _).ne'
      · have := hy j hj
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
    exact lt_of_lt_of_le (volume_halfOpenBox_pos (by positivity)) (measure_mono hsub)
  obtain ⟨c, hc0, hc⟩ := exists_haar_scale (ι := ι)
  have hoff : ∀ h : BondField ι → ℝ, ∫ y in halfOpenBox J ρ, D (coordMap ι y) * h (coordMap ι y)
      = c * ∫ x, D x * h x := by
    intro h
    rw [← hc fun x => D x * h x]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hD, ballDensity_eq_zero (exists_large_of_not_mem_halfOpenBox hy), zero_mul]
  have hoff1 : ∫ y in halfOpenBox J ρ, D (coordMap ι y) = c * ∫ x, D x := by
    have := hoff fun _ => 1
    simpa using this
  have hMn : ∀ h : BondField ι → ℝ, Continuous h →
      Tendsto (fun N => boxMean (coordMap ι) (Φ N) ρ h) atTop (𝓝 (ballExpectation (cutoffFactor ρ p) Ψ h)) := by
    intro h hh
    have h1 := (hI h hh).div hI1 hpos.ne'
    have e : (∫ y in halfOpenBox J ρ, D (coordMap ι y) * h (coordMap ι y)) / ∫ y in halfOpenBox J ρ, D (coordMap ι y)
        = ballExpectation (cutoffFactor ρ p) Ψ h := by
      rw [hoff h, hoff1, mul_div_mul_left _ _ hc0.ne']
      unfold ballExpectation
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hD]; ring)
    rw [e] at h1
    exact h1
  set Dk : ι → ι → ℝ := fun b b' => Real.exp (-(κ * d b b')) with hDk
  have hDk0 : ∀ b b', 0 < Dk b b' := fun _ _ => Real.exp_pos _
  have hDk1 : ∀ b, Dk b b = 1 := fun b => by simp [hDk, hd.self]
  obtain ⟨Wr, hWr0, hWr⟩ := exists_weight_ratio (J := J) (fun b j => Dk b j.1) (fun b j => hDk0 b j.1)
  have hbox : ∀ N, |boxMean (coordMap ι) (Φ N) ρ (fun x => f x * g x) - boxMean (coordMap ι) (Φ N) ρ f * boxMean (coordMap ι) (Φ N) ρ g|
      ≤ m⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean (coordMap ι) (Φ N) ρ (bondGradSq Prod.fst (coordMap ι) f b)) * Dk b b' *
          Real.sqrt (boxMean (coordMap ι) (Φ N) ρ (bondGradSq Prod.fst (coordMap ι) g b')) := by
    intro N
    refine box_covariance (hΦ2 N) hf hg hρ Prod.fst (coordMap ι) Dk hDk0 hDk1 Wr m hm hWr0 hWr ?_
    intro b x hx ξ
    exact form_in_coords (hΦ2 N).contDiffAt (wf b)
      (hform N b x fun b' => norm_le_of_mem_image_closedCube hρ hx b') ξ
  have hfd : ∀ u : BondField ι → ℝ, ContDiff ℝ 1 u → ∀ b,
      Continuous (bondGradSq Prod.fst (coordMap ι) u b) := by
    intro u hu b
    have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    refine continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact (h1.clm_apply continuous_const).pow 2
    · exact continuous_const
  have t1 := ((hMn _ (hf.continuous.mul hg.continuous)).sub
    ((hMn _ hf.continuous).mul (hMn _ hg.continuous))).abs
  have t2 : Tendsto (fun N => m⁻¹ * ∑ b, ∑ b', Real.sqrt (boxMean (coordMap ι) (Φ N) ρ (bondGradSq Prod.fst (coordMap ι) f b)) * Dk b b' *
      Real.sqrt (boxMean (coordMap ι) (Φ N) ρ (bondGradSq Prod.fst (coordMap ι) g b'))) atTop
      (𝓝 (m⁻¹ * ∑ b, ∑ b', Real.sqrt (ballExpectation (cutoffFactor ρ p) Ψ (bondGradSq Prod.fst (coordMap ι) f b)) * Dk b b' *
        Real.sqrt (ballExpectation (cutoffFactor ρ p) Ψ (bondGradSq Prod.fst (coordMap ι) g b')))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun b' _ => ?_)
    exact (((hMn _ (hfd f hf b)).sqrt).mul_const _).mul (hMn _ (hfd g hg b')).sqrt
  have hfinal := le_of_tendsto_of_tendsto' t1 t2 hbox
  have e1 : ∀ (u : BondField ι → ℝ) b, Real.sqrt (ballExpectation (cutoffFactor ρ p) Ψ (bondGradSq Prod.fst (coordMap ι) u b))
      = ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm u b) := by
    intro u b
    unfold ballL2Norm
    congr 2
    funext x
    exact bondGradSq_eq u b x
  simp only [e1] at hfinal
  exact hfinal
end YangMills.Construction.ColdStepAtMirrorFrames.GridBochner
end
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem ballCovarianceBound_holds : BallCovarianceBound := by
  intro ι _ _ ρ m κ d Ψ K p hρ hm hκ hp hd hΨ f g hf hg
  exact GridBochner.ball_covariance_bound ρ m κ d Ψ K p hρ hm hκ hp hd hΨ f g hf hg
end YangMills.Construction.ColdStepAtMirrorFrames
