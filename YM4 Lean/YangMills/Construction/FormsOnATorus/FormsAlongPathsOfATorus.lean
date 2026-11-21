import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PathForms
open TorusFields TorusLumps TorusContours TorusBlocks TorusPaths WeightedResponses ResponseInTheExpansion BoxGaussian
open BlockAverages hiding unitStep
variable {m : ℕ}
def stepShift (m : ℕ) (st : PathStep) : TorusSite m := if st.2 then unitStep m st.1 else - unitStep m st.1
def stepBond (x : TorusSite m) (st : PathStep) : TorusBond m :=
  if st.2 then (x, st.1) else (x - unitStep m st.1, st.1)
def pathEnd : TorusSite m → List PathStep → TorusSite m
  | x, [] => x
  | x, st :: r => pathEnd (x + stepShift m st) r
def pathBonds : TorusSite m → List PathStep → List (TorusBond m)
  | _, [] => []
  | x, st :: r => stepBond x st :: pathBonds (x + stepShift m st) r
def stepForm {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m) (st : PathStep) : E :=
  if st.2 then f (x, st.1) else - f (x - unitStep m st.1, st.1)
def formPathSum {E : Type} [AddCommGroup E] (f : TorusBond m → E) : TorusSite m → List PathStep → E
  | _, [] => 0
  | x, st :: r => stepForm f x st + formPathSum f (x + stepShift m st) r
def stepHolonomy (W : TorusField m) (x : TorusSite m) (st : PathStep) : UnitQuaternion :=
  if st.2 then W x st.1 else (W (x - unitStep m st.1) st.1)⁻¹
def pathHolonomy (W : TorusField m) : TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r => stepHolonomy W x st * pathHolonomy W (x + stepShift m st) r
def linkDeviation (W : TorusField m) (b : TorusBond m) : ℍ[ℝ] := ((W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1
theorem pathEnd_append (x : TorusSite m) (l l' : List PathStep) :
    pathEnd x (l ++ l') = pathEnd (pathEnd x l) l' := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => simpa [pathEnd] using ih _
theorem pathBonds_append (x : TorusSite m) (l l' : List PathStep) :
    pathBonds x (l ++ l') = pathBonds x l ++ pathBonds (pathEnd x l) l' := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => simp [pathBonds, pathEnd, ih]
theorem formPathSum_append {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m)
    (l l' : List PathStep) :
    formPathSum f x (l ++ l') = formPathSum f x l + formPathSum f (pathEnd x l) l' := by
  induction l generalizing x with
  | nil => simp [formPathSum, pathEnd]
  | cons st r ih => simp [formPathSum, pathEnd, ih, add_assoc]
theorem stepShift_flip (st : PathStep) : stepShift m (st.1, !st.2) = - stepShift m st := by
  rcases st with ⟨i, b⟩
  cases b <;> simp [stepShift]
theorem pathEnd_add (x u : TorusSite m) (l : List PathStep) : pathEnd (x + u) l = pathEnd x l + u := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathEnd]
    rw [← ih]
    congr 1
    abel
theorem pathEnd_reversePath (x : TorusSite m) (l : List PathStep) :
    pathEnd (pathEnd x l) (reversePath l) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have h : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e : pathEnd x (st :: r) = pathEnd (x + stepShift m st) r := rfl
    rw [h, pathEnd_append, e, ih]
    simp [pathEnd, stepShift_flip]
theorem stepForm_flip {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m) (st : PathStep) :
    stepForm f (x + stepShift m st) (st.1, !st.2) = - stepForm f x st := by
  rcases st with ⟨i, b⟩
  cases b <;> simp [stepForm, stepShift, sub_eq_add_neg]
theorem formPathSum_reversePath {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m)
    (l : List PathStep) :
    formPathSum f (pathEnd x l) (reversePath l) = - formPathSum f x l := by
  induction l generalizing x with
  | nil => simp [formPathSum, pathEnd, reversePath]
  | cons st r ih =>
    have h : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e : pathEnd x (st :: r) = pathEnd (x + stepShift m st) r := rfl
    rw [h, formPathSum_append, e, ih, pathEnd_reversePath]
    simp only [formPathSum, add_zero]
    have e2 := stepForm_flip f x st
    rw [e2]
    abel
theorem mem_pathBonds_of_mem_reversePath (x : TorusSite m) (l : List PathStep) {b : TorusBond m}
    (hb : b ∈ pathBonds (pathEnd x l) (reversePath l)) : b ∈ pathBonds x l := by
  induction l generalizing x with
  | nil => simp [reversePath, pathBonds] at hb
  | cons st r ih =>
    have h : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e : pathEnd x (st :: r) = pathEnd (x + stepShift m st) r := rfl
    rw [h, pathBonds_append, e, pathEnd_reversePath] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_cons_of_mem _ (ih _ hb)
    · refine List.mem_cons.mpr (Or.inl ?_)
      rcases st with ⟨i, c⟩
      cases c <;> simpa [pathBonds, stepBond, stepShift, sub_eq_add_neg] using hb
theorem formPathSum_replicate {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m)
    (i : Fin 4) (t : ℕ) :
    formPathSum f x (List.replicate t (i, true)) = ∑ a ∈ Finset.range t, f (x + a • unitStep m i, i) := by
  induction t generalizing x with
  | zero => simp [formPathSum]
  | succ t ih =>
    rw [List.replicate_succ, formPathSum, ih, Finset.sum_range_succ']
    simp only [stepForm, stepShift, if_true, zero_smul, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    rw [succ_nsmul']
    abel
theorem pathEnd_replicate (x : TorusSite m) (i : Fin 4) (t : ℕ) :
    pathEnd x (List.replicate t (i, true)) = x + t • unitStep m i := by
  induction t generalizing x with
  | zero => simp [pathEnd]
  | succ t ih =>
    rw [List.replicate_succ, pathEnd, ih, succ_nsmul']
    simp only [stepShift, if_true]
    abel
theorem norm_unitQuaternion (u : UnitQuaternion) : ‖((u : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_mul_sub_one_le (u v : UnitQuaternion) :
    ‖((u * v : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((u : UnitQuaternion) : ℍ[ℝ]) - 1‖ + ‖((v : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem norm_inv_sub_one (u : UnitQuaternion) :
    ‖((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖((u : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem norm_inv_sub_one_add_sub_one_le (u : UnitQuaternion) :
    ‖((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + (((u : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      ‖((u : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by
  have hinv : ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have h : ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + (((u : UnitQuaternion) : ℍ[ℝ]) - 1) =
      ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        ((((u : UnitQuaternion) : ℍ[ℝ]) - 1) * (((u : UnitQuaternion) : ℍ[ℝ]) - 1)) := by
    have e1 : ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((((u : UnitQuaternion) : ℍ[ℝ]) - 1) * (((u : UnitQuaternion) : ℍ[ℝ]) - 1)) =
        (((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u : UnitQuaternion) : ℍ[ℝ])) * ((u : UnitQuaternion) : ℍ[ℝ]) -
          2 * (((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u : UnitQuaternion) : ℍ[ℝ])) +
          ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      noncomm_ring
    rw [e1, hinv]
    noncomm_ring
  rw [h, norm_mul, norm_unitQuaternion, one_mul, norm_mul, sq]
theorem norm_stepHolonomy_sub_one (W : TorusField m) (x : TorusSite m) (st : PathStep) :
    ‖((stepHolonomy W x st : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖linkDeviation W (stepBond x st)‖ := by
  rcases st with ⟨i, c⟩
  cases c
  · simp [stepHolonomy, stepBond, linkDeviation, norm_inv_sub_one]
  · simp [stepHolonomy, stepBond, linkDeviation]
theorem norm_stepHolonomy_sub_one_sub_stepForm_le (W : TorusField m) (x : TorusSite m) (st : PathStep) :
    ‖((stepHolonomy W x st : UnitQuaternion) : ℍ[ℝ]) - 1 - stepForm (linkDeviation W) x st‖ ≤
      ‖linkDeviation W (stepBond x st)‖ ^ 2 := by
  rcases st with ⟨i, c⟩
  cases c
  · simp only [stepHolonomy, stepBond, stepForm, linkDeviation, Bool.false_eq_true, if_false, sub_neg_eq_add]
    exact norm_inv_sub_one_add_sub_one_le _
  · simp [stepHolonomy, stepBond, stepForm, linkDeviation]
theorem norm_pathHolonomy_sub_one_le (W : TorusField m) (x : TorusSite m) (l : List PathStep) {a : ℝ}
    (ha : ∀ b ∈ pathBonds x l, ‖linkDeviation W b‖ ≤ a) :
    ‖((pathHolonomy W x l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * a := by
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    simp only [pathHolonomy, List.length_cons]
    have h1 := ha _ (List.mem_cons_self ..)
    have h2 := ih (x + stepShift m st) fun b hb => ha b (List.mem_cons_of_mem _ hb)
    refine (norm_mul_sub_one_le _ _).trans ?_
    rw [norm_stepHolonomy_sub_one]
    push_cast
    linarith
theorem norm_pathHolonomy_sub_one_sub_formPathSum_le (W : TorusField m) (x : TorusSite m) (l : List PathStep)
    {a : ℝ} (h0 : 0 ≤ a) (ha : ∀ b ∈ pathBonds x l, ‖linkDeviation W b‖ ≤ a) :
    ‖((pathHolonomy W x l : UnitQuaternion) : ℍ[ℝ]) - 1 - formPathSum (linkDeviation W) x l‖ ≤
      ((l.length : ℝ) * a) ^ 2 := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, formPathSum]
  | cons st r ih =>
    simp only [pathHolonomy, formPathSum, List.length_cons]
    have h1 := ha _ (List.mem_cons_self ..)
    have h2 := ih (x + stepShift m st) fun b hb => ha b (List.mem_cons_of_mem _ hb)
    have h3 := norm_pathHolonomy_sub_one_le W (x + stepShift m st) r fun b hb => ha b (List.mem_cons_of_mem _ hb)
    have h4 := norm_stepHolonomy_sub_one_sub_stepForm_le W x st
    have h5 : ‖((stepHolonomy W x st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a := by
      rw [norm_stepHolonomy_sub_one]; exact h1
    set q : ℍ[ℝ] := ((stepHolonomy W x st : UnitQuaternion) : ℍ[ℝ])
    set H : ℍ[ℝ] := ((pathHolonomy W (x + stepShift m st) r : UnitQuaternion) : ℍ[ℝ])
    have e : ((stepHolonomy W x st * pathHolonomy W (x + stepShift m st) r : UnitQuaternion) : ℍ[ℝ]) - 1 -
        (stepForm (linkDeviation W) x st + formPathSum (linkDeviation W) (x + stepShift m st) r) =
        (q - 1 - stepForm (linkDeviation W) x st) +
          (H - 1 - formPathSum (linkDeviation W) (x + stepShift m st) r) + (q - 1) * (H - 1) := by
      simp only [Submonoid.coe_mul, q, H]
      noncomm_ring
    rw [e]
    have h6 : ‖(q - 1) * (H - 1)‖ ≤ a * ((r.length : ℝ) * a) := by
      rw [norm_mul]
      exact mul_le_mul h5 h3 (norm_nonneg _) h0
    have h7 : ‖linkDeviation W (stepBond x st)‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc _ ≤ ‖q - 1 - stepForm (linkDeviation W) x st‖ +
          ‖H - 1 - formPathSum (linkDeviation W) (x + stepShift m st) r‖ + ‖(q - 1) * (H - 1)‖ := norm_add₃_le
      _ ≤ a ^ 2 + ((r.length : ℝ) * a) ^ 2 + a * ((r.length : ℝ) * a) := by linarith
      _ ≤ (((r.length + 1 : ℕ) : ℝ) * a) ^ 2 := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) r.length) (mul_nonneg h0 h0)]
theorem pathHolonomy_eq_wordHolonomy (W : TorusField m) (x : TorusSite m) (l : List PathStep) :
    pathHolonomy W x l = wordHolonomy W (pathToWord x l) := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    rcases st with ⟨i, c⟩
    cases c
    · simp [pathHolonomy, stepHolonomy, stepShift, pathToWord, wordHolonomy, orientedValue, ih, sub_eq_add_neg]
    · simp [pathHolonomy, stepHolonomy, stepShift, pathToWord, wordHolonomy, orientedValue, ih]
theorem supDist_add_stepShift_le [NeZero m] (x : TorusSite m) (st : PathStep) :
    supDist x (x + stepShift m st) ≤ 1 := by
  rcases st with ⟨i, c⟩
  cases c
  · simpa [stepShift, sub_eq_add_neg] using supDist_sub_unitStep_le x i
  · simpa [stepShift] using supDist_add_unitStep_le x i
theorem supDist_le_length_of_mem_pathBonds [NeZero m] (x : TorusSite m) (l : List PathStep) {b : TorusBond m}
    (hb : b ∈ pathBonds x l) :
    supDist x b.1 ≤ l.length ∧ supDist x (b.1 + unitStep m b.2) ≤ l.length := by
  induction l generalizing x with
  | nil => simp [pathBonds] at hb
  | cons st r ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · rcases st with ⟨i, c⟩
      cases c
      · simp only [stepBond, Bool.false_eq_true, if_false, List.length_cons, sub_add_cancel]
        exact ⟨(supDist_sub_unitStep_le x i).trans (by omega), by rw [supDist_self]; omega⟩
      · simp only [stepBond, if_true, List.length_cons]
        exact ⟨by rw [supDist_self]; omega, (supDist_add_unitStep_le x i).trans (by omega)⟩
    · obtain ⟨h1, h2⟩ := ih _ hb
      have h3 := supDist_add_stepShift_le x st
      simp only [List.length_cons]
      exact ⟨(supDist_triangle x (x + stepShift m st) _).trans (by omega),
        (supDist_triangle x (x + stepShift m st) _).trans (by omega)⟩
def formCurl {E : Type} [AddCommGroup E] (f : TorusBond m → E) (p : TorusPlaquette m) : E :=
  f (p.1, p.2.1) + f (p.1 + unitStep m p.2.1, p.2.2) - f (p.1 + unitStep m p.2.2, p.2.1) - f (p.1, p.2.2)
def edgeSum {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m) (i : Fin 4) (t : ℕ) : E :=
  ∑ a ∈ Finset.range t, f (x + a • unitStep m i, i)
def squareCurlSum {E : Type} [AddCommGroup E] (f : TorusBond m → E) (t : ℕ) (y : TorusSite m) (μ ν : Fin 4) : E :=
  ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, formCurl f (y + a • unitStep m μ + b • unitStep m ν, μ, ν)
theorem sum_formCurl_column {E : Type} [AddCommGroup E] (f : TorusBond m → E) (x : TorusSite m)
    (μ ν : Fin 4) (t : ℕ) :
    ∑ b ∈ Finset.range t, formCurl f (x + b • unitStep m ν, μ, ν) =
      f (x, μ) - f (x + t • unitStep m ν, μ) + edgeSum f (x + unitStep m μ) ν t - edgeSum f x ν t := by
  induction t with
  | zero => simp [edgeSum]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [edgeSum, Finset.sum_range_succ, formCurl]
    have e1 : x + t • unitStep m ν + unitStep m ν = x + (t + 1) • unitStep m ν := by
      rw [succ_nsmul]; abel
    have e2 : x + t • unitStep m ν + unitStep m μ = x + unitStep m μ + t • unitStep m ν := by abel
    rw [e1, e2]
    abel
theorem sum_formCurl_rectangle {E : Type} [AddCommGroup E] (f : TorusBond m → E) (y : TorusSite m)
    (μ ν : Fin 4) (s t : ℕ) :
    ∑ a ∈ Finset.range s, ∑ b ∈ Finset.range t, formCurl f (y + a • unitStep m μ + b • unitStep m ν, μ, ν) =
      edgeSum f y μ s + edgeSum f (y + s • unitStep m μ) ν t - edgeSum f (y + t • unitStep m ν) μ s -
        edgeSum f y ν t := by
  induction s with
  | zero => simp [edgeSum]
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, sum_formCurl_column]
    simp only [edgeSum, Finset.sum_range_succ (n := s)]
    have e1 : y + s • unitStep m μ + unitStep m μ = y + (s + 1) • unitStep m μ := by
      rw [succ_nsmul]; abel
    have e2 : y + s • unitStep m μ + t • unitStep m ν = y + t • unitStep m ν + s • unitStep m μ := by abel
    rw [e1, e2]
    abel
theorem squareCurlSum_eq_edges {E : Type} [AddCommGroup E] (f : TorusBond m → E) (t : ℕ) (y : TorusSite m)
    (μ ν : Fin 4) :
    squareCurlSum f t y μ ν =
      edgeSum f y μ t + edgeSum f (y + t • unitStep m μ) ν t - edgeSum f (y + t • unitStep m ν) μ t -
        edgeSum f y ν t :=
  sum_formCurl_rectangle f y μ ν t t
theorem supDist_add_nsmul_le [NeZero m] (x : TorusSite m) (i : Fin 4) (a : ℕ) :
    supDist x (x + a • unitStep m i) ≤ a := by
  induction a with
  | zero => simp [supDist_self]
  | succ a ih =>
    have h1 : x + (a + 1) • unitStep m i = x + a • unitStep m i + unitStep m i := by rw [succ_nsmul]; abel
    rw [h1]
    exact (supDist_triangle x (x + a • unitStep m i) _).trans
      (by have := supDist_add_unitStep_le (x + a • unitStep m i) i; omega)
theorem mem_supBall_of_supDist_le [NeZero m] {o z : TorusSite m} {r : ℕ} (h : supDist z o ≤ r) :
    z ∈ supBall o (r : ℝ) := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact_mod_cast h
theorem mem_bondsWithin_of_mem [NeZero m] {S : Finset (TorusSite m)} {b : TorusBond m} (h1 : b.1 ∈ S)
    (h2 : b.1 + unitStep m b.2 ∈ S) : b ∈ bondsWithin S := by
  simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h1, h2⟩
theorem edge_mem_bondsWithin [NeZero m] {o x : TorusSite m} {r t a : ℕ} (i : Fin 4) (ha : a < t)
    (h : supDist x o + t ≤ r) :
    ((x + a • unitStep m i, i) : TorusBond m) ∈ bondsWithin (supBall o (r : ℝ)) := by
  have h1 := supDist_add_nsmul_le x i a
  have h2 := supDist_add_nsmul_le x i (a + 1)
  have e : x + a • unitStep m i + unitStep m i = x + (a + 1) • unitStep m i := by rw [succ_nsmul]; abel
  refine mem_bondsWithin_of_mem (mem_supBall_of_supDist_le ?_) (mem_supBall_of_supDist_le ?_)
  · have := supDist_triangle (x + a • unitStep m i) x o
    rw [supDist_comm (x + a • unitStep m i) x] at this
    simp only
    omega
  · have := supDist_triangle (x + (a + 1) • unitStep m i) x o
    rw [supDist_comm (x + (a + 1) • unitStep m i) x] at this
    simp only
    rw [e]
    omega
theorem norm_edgeSum_le [NeZero m] {f : TorusBond m → ℍ[ℝ]} {o x : TorusSite m} {r t : ℕ} {a : ℝ} (i : Fin 4)
    (hf : ∀ b ∈ bondsWithin (supBall o (r : ℝ)), ‖f b‖ ≤ a) (h : supDist x o + t ≤ r) :
    ‖edgeSum f x i t‖ ≤ t * a := by
  unfold edgeSum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ b ∈ Finset.range t, ‖f (x + b • unitStep m i, i)‖ ≤ a := fun b hb =>
    hf _ (edge_mem_bondsWithin i (Finset.mem_range.mp hb) h)
  simpa using Finset.sum_le_card_nsmul _ _ _ this
theorem norm_squareCurlSum_le [NeZero m] {f : TorusBond m → ℍ[ℝ]} {o y : TorusSite m} {r t : ℕ} {a : ℝ}
    (μ ν : Fin 4) (hf : ∀ b ∈ bondsWithin (supBall o (r : ℝ)), ‖f b‖ ≤ a) (h : supDist y o + 2 * t ≤ r) :
    ‖squareCurlSum f t y μ ν‖ ≤ 4 * t * a := by
  rw [squareCurlSum_eq_edges]
  have hμ : supDist (y + t • unitStep m μ) o + t ≤ r := by
    have := supDist_triangle (y + t • unitStep m μ) y o
    have h2 := supDist_add_nsmul_le y μ t
    rw [supDist_comm (y + t • unitStep m μ) y] at this
    omega
  have hν : supDist (y + t • unitStep m ν) o + t ≤ r := by
    have := supDist_triangle (y + t • unitStep m ν) y o
    have h2 := supDist_add_nsmul_le y ν t
    rw [supDist_comm (y + t • unitStep m ν) y] at this
    omega
  have h0 : supDist y o + t ≤ r := by omega
  have a1 := norm_edgeSum_le μ hf h0
  have a2 := norm_edgeSum_le ν hf hμ
  have a3 := norm_edgeSum_le μ hf hν
  have a4 := norm_edgeSum_le ν hf h0
  calc _ ≤ ‖edgeSum f y μ t‖ + ‖edgeSum f (y + t • unitStep m μ) ν t‖ + ‖edgeSum f (y + t • unitStep m ν) μ t‖ +
        ‖edgeSum f y ν t‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * t * a := by linarith
theorem squareCurlSum_sub {E : Type} [AddCommGroup E] (f f' : TorusBond m → E) (t : ℕ) (y : TorusSite m)
    (μ ν : Fin 4) :
    squareCurlSum (f - f') t y μ ν = squareCurlSum f t y μ ν - squareCurlSum f' t y μ ν := by
  simp only [squareCurlSum, formCurl, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  abel
theorem toTorusSite_pathEndpoint {F : BlockFrame} {j : ℕ} [NeZero m] (hp : ∀ i, F.period j i = m)
    (x : F.Site j) (l : List PathStep) :
    (toTorusSite m (pathEndpoint x l) : TorusSite m) = pathEnd (toTorusSite m x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : toTorusSite m (x + stepDisplacement j st : F.Site j) =
        (toTorusSite m x + stepShift m st : TorusSite m) := by
      rw [TopLevelSites.toTorusSite_add hp]
      rcases st with ⟨i, c⟩
      cases c
      · simp only [stepDisplacement, stepShift, Bool.false_eq_true, if_false]
        rw [TopLevelSites.toTorusSite_neg hp, TopLevelSites.toTorusSite_unitStep hp]
      · simp only [stepDisplacement, stepShift, if_true]
        rw [TopLevelSites.toTorusSite_unitStep hp]
    simp only [pathEndpoint, pathEnd]
    rw [ih, e]
theorem pathEnd_axisPath [NeZero m] (x : TorusSite m) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathEnd x (axisPath h π) = x + siteOfInt h := by
  have hp : ∀ i, (stepBlockFrame 1 m).period 0 i = m := fun i => by
    rw [stepBlockFrame_period_zero, mul_one]
  have h1 := toTorusSite_pathEndpoint hp (StepCosts.torusSiteInFrame (stepBlockFrame 1 m) 0 x) (axisPath h π)
  rw [pathEndpoint_axisPath, TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_siteOfCoords hp,
    TopLevelSites.toTorusSite_torusSiteInFrame hp] at h1
  exact h1.symm
theorem sum_range_mul_eq {E : Type} [AddCommMonoid E] (G : ℕ → E) (t L : ℕ) :
    ∑ i ∈ Finset.range (t * L), G i = ∑ a ∈ Finset.range t, ∑ i ∈ Finset.range L, G (a * L + i) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
theorem squareCurlSum_mul_eq_tiles {E : Type} [AddCommGroup E] (f : TorusBond m → E) (t L : ℕ) (z : TorusSite m)
    (μ ν : Fin 4) :
    squareCurlSum f (t * L) z μ ν = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
      squareCurlSum f L (z + (a * L) • unitStep m μ + (b * L) • unitStep m ν) μ ν := by
  unfold squareCurlSum
  rw [sum_range_mul_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [sum_range_mul_eq (fun b => formCurl f (z + _ • unitStep m μ + b • unitStep m ν, μ, ν)) t L]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : z + (a * L + i) • unitStep m μ + (b * L + j) • unitStep m ν =
      z + (a * L) • unitStep m μ + (b * L) • unitStep m ν + i • unitStep m μ + j • unitStep m ν := by
    rw [add_nsmul, add_nsmul]
    abel
  rw [e]
theorem nsmul_unitStep_eq (a : ℕ) (i : Fin 4) :
    a • unitStep m i = (siteOfInt (Pi.single i (a : ℤ)) : TorusSite m) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [unitStep, siteOfInt]
  · simp [unitStep, siteOfInt, h]
section CoarseBlocks
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem blockCentre_cast_add (a : ZMod n) (z : ℤ) :
    (((L : ℤ) * ((a + (z : ZMod n)).cast : ℤ) : ℤ) : ZMod (n * L)) =
      (((L : ℤ) * (a.cast : ℤ) + (L : ℤ) * z : ℤ) : ZMod (n * L)) := by
  have h1 : ((((a + (z : ZMod n)).cast : ℤ)) : ZMod n) = (((a.cast : ℤ) + z : ℤ) : ZMod n) := by
    push_cast
    simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨c, hc⟩ := h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨c, ?_⟩
  push_cast
  linear_combination (L : ℤ) * hc
theorem blockCentreSite_add_siteOfInt (Y : TorusSite n) (e : Fin 4 → ℤ) :
    blockCentreSite L (Y + siteOfInt e) = blockCentreSite L Y + siteOfInt (fun i => (L : ℤ) * e i) := by
  funext k
  have := blockCentre_cast_add (L := L) (Y k) (e k)
  simp only [blockCentreSite, siteOfInt, Pi.add_apply]
  rw [this]
  push_cast
  ring
theorem blockCentreSite_add_unitStep (Y : TorusSite n) (i : Fin 4) :
    blockCentreSite L (Y + unitStep n i) = blockCentreSite L Y + L • unitStep (n * L) i := by
  rw [← siteOfInt_single, blockCentreSite_add_siteOfInt, nsmul_unitStep_eq]
  congr 2
  funext k
  by_cases h : k = i
  · subst h
    simp
  · simp [h]
theorem blockCentreSite_tile (y : TorusSite n) (μ ν : Fin 4) (a b : ℕ) :
    blockCentreSite L (y + a • unitStep n μ + b • unitStep n ν) =
      blockCentreSite L y + (a * L) • unitStep (n * L) μ + (b * L) • unitStep (n * L) ν := by
  have e1 : y + a • unitStep n μ + b • unitStep n ν = y + siteOfInt (Pi.single μ (a : ℤ) + Pi.single ν (b : ℤ)) := by
    rw [siteOfInt_add, ← nsmul_unitStep_eq, ← nsmul_unitStep_eq, add_assoc]
  rw [e1, blockCentreSite_add_siteOfInt, nsmul_unitStep_eq, nsmul_unitStep_eq, add_assoc, ← siteOfInt_add]
  congr 2
  funext k
  simp only [Pi.add_apply, mul_add]
  congr 1
  · by_cases h : k = μ
    · subst h
      simp [mul_comm]
    · simp [h]
  · by_cases h : k = ν
    · subst h
      simp [mul_comm]
    · simp [h]
def contourMean (L : ℕ) {n : ℕ} (f : TorusBond (n * L) → ℍ[ℝ]) (c : TorusBond n) : ℍ[ℝ] :=
  contourWeight L • ∑ e ∈ contourIndex L, formPathSum f (blockCentreSite L c.1) (bondContour L e.1 e.2 c.2)
theorem formPathSum_bondContour (f : TorusBond (n * L) → ℍ[ℝ]) (x : TorusSite (n * L)) (ξ : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    formPathSum f x (bondContour L ξ π i) =
      formPathSum f x (axisPath ξ π) + edgeSum f (x + siteOfInt ξ) i L -
        formPathSum f (x + L • unitStep (n * L) i) (axisPath ξ π) := by
  unfold bondContour
  rw [formPathSum_append, formPathSum_append, pathEnd_append, pathEnd_axisPath, pathEnd_replicate,
    formPathSum_replicate]
  have e : x + siteOfInt ξ + L • unitStep (n * L) i = pathEnd (x + L • unitStep (n * L) i) (axisPath ξ π) := by
    rw [pathEnd_axisPath]
    abel
  rw [e, formPathSum_reversePath]
  simp only [edgeSum, sub_eq_add_neg]
theorem contour_legs_cancel (f : TorusBond (n * L) → ℍ[ℝ]) (Y : TorusSite n) (ξ : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (μ ν : Fin 4) :
    formPathSum f (blockCentreSite L Y) (bondContour L ξ π μ) +
        formPathSum f (blockCentreSite L (Y + unitStep n μ)) (bondContour L ξ π ν) -
        formPathSum f (blockCentreSite L (Y + unitStep n ν)) (bondContour L ξ π μ) -
        formPathSum f (blockCentreSite L Y) (bondContour L ξ π ν) =
      squareCurlSum f L (blockCentreSite L Y + siteOfInt ξ) μ ν := by
  rw [formPathSum_bondContour, formPathSum_bondContour, formPathSum_bondContour, formPathSum_bondContour,
    squareCurlSum_eq_edges, blockCentreSite_add_unitStep, blockCentreSite_add_unitStep]
  have e1 : blockCentreSite L Y + L • unitStep (n * L) μ + L • unitStep (n * L) ν =
      blockCentreSite L Y + L • unitStep (n * L) ν + L • unitStep (n * L) μ := by abel
  have e2 : blockCentreSite L Y + L • unitStep (n * L) μ + siteOfInt ξ =
      blockCentreSite L Y + siteOfInt ξ + L • unitStep (n * L) μ := by abel
  have e3 : blockCentreSite L Y + L • unitStep (n * L) ν + siteOfInt ξ =
      blockCentreSite L Y + siteOfInt ξ + L • unitStep (n * L) ν := by abel
  rw [e1, e2, e3]
  abel
theorem formCurl_contourMean (hL : Odd L) (f : TorusBond (n * L) → ℍ[ℝ]) (Y : TorusSite n) (μ ν : Fin 4) :
    formCurl (contourMean L f) (Y, μ, ν) =
      ((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L, squareCurlSum f L (blockCentreSite L Y + siteOfInt ξ) μ ν := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  simp only [formCurl, contourMean]
  rw [← smul_add, ← smul_sub, ← smul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  have h : ∀ e ∈ contourIndex L, _ = squareCurlSum f L (blockCentreSite L Y + siteOfInt e.1) μ ν :=
    fun e _ => contour_legs_cancel f Y e.1 e.2 μ ν
  rw [Finset.sum_congr rfl h]
  unfold contourIndex contourWeight
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [this]
  field_simp
theorem squareCurlSum_contourMean (hL : Odd L) (f : TorusBond (n * L) → ℍ[ℝ]) (t : ℕ) (y : TorusSite n)
    (μ ν : Fin 4) :
    ((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L, squareCurlSum f (t * L) (blockCentreSite L y + siteOfInt ξ) μ ν =
      squareCurlSum (contourMean L f) t y μ ν := by
  have hR : squareCurlSum (contourMean L f) t y μ ν = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
      ((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L,
        squareCurlSum f L (blockCentreSite L (y + a • unitStep n μ + b • unitStep n ν) + siteOfInt ξ) μ ν :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => formCurl_contourMean hL f _ μ ν
  rw [hR]
  simp_rw [squareCurlSum_mul_eq_tiles f t L]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [blockCentreSite_tile]
  congr 1
  abel
def coarseBlockMean (L d n : ℕ) [NeZero L] [NeZero n] (y₀ : TorusSite n) (μ ν : Fin 4) (t : ℕ)
    (f : TorusBond (fineSide L d n) → ℍ[ℝ]) : ℍ[ℝ] :=
  ((L : ℝ) ^ (4 * d))⁻¹ •
    ∑ y ∈ Finset.univ.filter (fun y : TorusSite (fineSide L d n) => siteAbove L d n y = y₀),
      squareCurlSum f (t * L ^ d) y μ ν
theorem coarseBlockMean_zero (y₀ : TorusSite n) (μ ν : Fin 4) (t : ℕ) (f : TorusBond (fineSide L 0 n) → ℍ[ℝ]) :
    coarseBlockMean L 0 n y₀ μ ν t f = squareCurlSum f t y₀ μ ν := by
  unfold coarseBlockMean
  let y₁ : TorusSite (fineSide L 0 n) := y₀
  have : (Finset.univ.filter (fun y : TorusSite (fineSide L 0 n) => siteAbove L 0 n y = y₀)) =
      ({y₁} : Finset (TorusSite (fineSide L 0 n))) := by
    ext y
    constructor
    · intro h
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mp h⟩
  rw [this, Finset.sum_singleton]
  simp only [mul_zero, pow_zero, inv_one, one_smul, mul_one]
  rfl
theorem parentBlock_blockCentreSite_add_of_mem (hL : Odd L) (Y : TorusSite n) {ξ : Fin 4 → ℤ}
    (hξ : ξ ∈ centredCube L) :
    parentBlock L (blockCentreSite L Y + siteOfInt ξ) = Y := by
  rw [parentBlock_blockCentreSite_add]
  have h0 : (fun i => (ξ i + ((L : ℤ) - 1) / 2) / (L : ℤ)) = (0 : Fin 4 → ℤ) := by
    funext i
    have h := mem_centredCube_iff.mp hξ i
    obtain ⟨q, hq⟩ := hL
    have hz : ((L : ℤ) - 1) / 2 = q := by
      subst hq
      push_cast
      omega
    rw [hz] at h ⊢
    have hLz : (L : ℤ) = 2 * q + 1 := by subst hq; push_cast; ring
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [h0]
  funext i
  simp [siteOfInt]
theorem blockCentreSite_add_injOn (hL : Odd L) (Y : TorusSite n) :
    Set.InjOn (fun ξ : Fin 4 → ℤ => (blockCentreSite L Y + siteOfInt ξ : TorusSite (n * L)))
      (centredCube L : Set (Fin 4 → ℤ)) := by
  intro ξ hξ ξ' hξ' h
  have h' : (siteOfInt ξ : TorusSite (n * L)) = siteOfInt ξ' := add_left_cancel h
  funext i
  have hi : ((ξ i : ℤ) : ZMod (n * L)) = ((ξ' i : ℤ) : ZMod (n * L)) := congrFun h' i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
  have a1 := mem_centredCube_iff.mp hξ i
  have a2 := mem_centredCube_iff.mp hξ' i
  obtain ⟨q, hq⟩ := hL
  have hz : ((L : ℤ) - 1) / 2 = q := by
    subst hq
    push_cast
    omega
  rw [hz] at a1 a2
  have hLz : (L : ℤ) = 2 * q + 1 := by subst hq; push_cast; ring
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnL : (L : ℤ) ≤ ((n * L : ℕ) : ℤ) := by
    push_cast
    nlinarith
  have hlt : |ξ' i - ξ i| < ((n * L : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hi hlt)).symm
theorem mem_image_centredCube (hL : Odd L) (z : TorusSite (n * L)) :
    z ∈ (centredCube L).image
      (fun ξ : Fin 4 → ℤ => (blockCentreSite L (parentBlock L z) + siteOfInt ξ : TorusSite (n * L))) := by
  obtain ⟨o, ho, hz⟩ := exists_eq_blockCentreSite_add hL z
  refine Finset.mem_image.mpr ⟨o, ?_, hz.symm⟩
  refine mem_centredCube_iff.mpr fun i => ?_
  have h := ho i
  obtain ⟨q, hq⟩ := hL
  have hz' : ((L : ℤ) - 1) / 2 = q := by
    subst hq
    push_cast
    omega
  rw [hz'] at h ⊢
  have hLz : (L : ℤ) = 2 * q + 1 := by subst hq; push_cast; ring
  constructor <;> omega
theorem coarseBlockMean_succ (hL : Odd L) (d : ℕ) (y₀ : TorusSite n) (μ ν : Fin 4) (t : ℕ)
    (f : TorusBond (fineSide L (d + 1) n) → ℍ[ℝ]) :
    coarseBlockMean L (d + 1) n y₀ μ ν t f =
      ((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L,
        coarseBlockMean L d (n * L) (blockCentreSite L y₀ + siteOfInt ξ) μ ν (t * L) f := by
  unfold coarseBlockMean
  simp only [← Finset.smul_sum]
  rw [smul_smul]
  have hc : ((L : ℝ) ^ (4 * (d + 1)))⁻¹ = ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ (4 * d))⁻¹ := by
    rw [← mul_inv, ← pow_add]
    congr 2
    ring
  rw [hc]
  congr 1
  set S := Finset.univ.filter (fun y : TorusSite (fineSide L (d + 1) n) => siteAbove L (d + 1) n y = y₀) with hS
  set φ : (Fin 4 → ℤ) → TorusSite (n * L) := fun ξ => blockCentreSite L y₀ + siteOfInt ξ with hφ
  have hmap : ∀ y ∈ S, siteAbove L d (n * L) y ∈ (centredCube L).image φ := by
    intro y hy
    have h1 : parentBlock L (siteAbove L d (n * L) y) = y₀ := (Finset.mem_filter.mp hy).2
    have := mem_image_centredCube hL (siteAbove L d (n * L) y)
    rwa [h1] at this
  rw [← Finset.sum_fiberwise_of_maps_to hmap, Finset.sum_image (blockCentreSite_add_injOn hL y₀)]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  have hSmem : ∀ y' : TorusSite (fineSide L (d + 1) n), siteAbove L (d + 1) n y' = y₀ → y' ∈ S := fun y' h => by
    rw [hS]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hf : S.filter (fun y => siteAbove L d (n * L) y = φ ξ) =
      Finset.univ.filter (fun y : TorusSite (fineSide L d (n * L)) => siteAbove L d (n * L) y = φ ξ) := by
    ext y
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
    · intro h
      have h2 : siteAbove L d (n * L) y = φ ξ := (Finset.mem_filter.mp h).2
      have h3 : siteAbove L (d + 1) n y = y₀ := by
        show parentBlock L (siteAbove L d (n * L) y) = y₀
        rw [h2]
        exact parentBlock_blockCentreSite_add_of_mem hL y₀ hξ
      exact Finset.mem_filter.mpr ⟨hSmem y h3, h2⟩
  refine Finset.sum_congr hf fun y _ => ?_
  have e : t * L ^ (d + 1) = t * L * L ^ d := by ring
  exact congrArg (fun q => squareCurlSum f q y μ ν) e
theorem norm_cubeAverage_sub_le (hL : Odd L) {X Y : (Fin 4 → ℤ) → ℍ[ℝ]} {c : ℝ}
    (h : ∀ ξ ∈ centredCube L, ‖X ξ - Y ξ‖ ≤ c) :
    ‖((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L, X ξ - ((L : ℝ) ^ 4)⁻¹ • ∑ ξ ∈ centredCube L, Y ξ‖ ≤ c := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 4 := by
    have : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne L))
    positivity
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, norm_inv, Real.norm_of_nonneg hL0.le]
  have h2 : ‖∑ ξ ∈ centredCube L, (X ξ - Y ξ)‖ ≤ (centredCube L).card • c :=
    (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ h)
  rw [card_centredCube hL, nsmul_eq_mul] at h2
  push_cast at h2
  rw [inv_mul_le_iff₀ hL0]
  exact h2
theorem norm_coarseBlockMean_succ_sub_le (hL : Odd L) (d : ℕ) (y : TorusSite n) (μ ν : Fin 4) (t : ℕ)
    (f₀ : TorusBond (fineSide L (d + 1) n) → ℍ[ℝ]) (f : TorusBond (n * L) → ℍ[ℝ]) {c : ℝ}
    (h : ∀ ξ ∈ centredCube L, ‖coarseBlockMean L d (n * L) (blockCentreSite L y + siteOfInt ξ) μ ν (t * L) f₀ -
      squareCurlSum f (t * L) (blockCentreSite L y + siteOfInt ξ) μ ν‖ ≤ c) :
    ‖coarseBlockMean L (d + 1) n y μ ν t f₀ - squareCurlSum (contourMean L f) t y μ ν‖ ≤ c := by
  rw [coarseBlockMean_succ hL, ← squareCurlSum_contourMean hL]
  exact norm_cubeAverage_sub_le hL h
end CoarseBlocks
end YangMills.Construction.PathForms
end
