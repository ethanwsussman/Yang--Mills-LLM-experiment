import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpaceProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.FullSpace
open InfiniteLattice
namespace AxisPathReversal
variable {a : ℝ}
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℤ}
    (h : IsAxisDisplacement x x' μ n) : axisPath x x' = signedSteps x μ n := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfStepSets.axisPath_eq_signedSteps <;> assumption
theorem forwardSteps_succ (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℕ) :
    forwardSteps x μ (m + 1) =
      forwardSteps x μ m ++ [InfiniteLattice.Link.forwardFrom (x + m • axisStep a μ) μ] := by
  induction m generalizing x with
  | zero => simp [forwardSteps]
  | succ m ih =>
    have hs : x + axisStep a μ + m • axisStep a μ = x + (m + 1) • axisStep a μ := by
      rw [succ_nsmul']
      abel
    rw [forwardSteps, ih (x + axisStep a μ), forwardSteps, List.cons_append, hs]
theorem reverse_map_opposite_twice (Γ : List (InfiniteLattice.Link a)) :
    (((Γ.map InfiniteLattice.Link.opposite).reverse).map InfiniteLattice.Link.opposite).reverse = Γ := by
  have hrev : ∀ b : InfiniteLattice.Link a, b.opposite.opposite = b := fun b => rfl
  simp [List.map_reverse, Function.comp_def, hrev]
theorem backwardSteps_eq_reverse (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℕ) :
    backwardSteps (x + m • axisStep a μ) μ m =
      ((forwardSteps x μ m).map InfiniteLattice.Link.opposite).reverse := by
  induction m with
  | zero => simp [backwardSteps, forwardSteps]
  | succ m ih =>
    have hprev : x + (m + 1) • axisStep a μ - axisStep a μ = x + m • axisStep a μ := by
      rw [succ_nsmul]
      abel
    rw [backwardSteps, hprev, ih, forwardSteps_succ]
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    congr 1
    ext1
    · simp only [backwardLink, InfiniteLattice.Link.forwardFrom, InfiniteLattice.Link.opposite]
      rw [succ_nsmul]
      abel
    · simp only [backwardLink, InfiniteLattice.Link.forwardFrom, InfiniteLattice.Link.opposite, hprev]
theorem signedSteps_neg (x x' : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℤ)
    (h : x' - x = n • axisStep a μ) :
    signedSteps x' μ (-n) = ((signedSteps x μ n).map InfiniteLattice.Link.opposite).reverse := by
  rcases le_total 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hx' : x' = x + m • axisStep a μ := by
      rw [← natCast_zsmul, ← h]
      abel
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [signedSteps, forwardSteps]
    · have hneg : ¬ (0 ≤ -(m : ℤ)) := by omega
      rw [signedSteps, if_neg hneg, signedSteps, if_pos hn]
      simp only [neg_neg, Int.toNat_natCast]
      rw [hx', backwardSteps_eq_reverse]
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hn)
    have hnm : n = -(m : ℤ) := by omega
    subst hnm
    have hx : x = x' + m • axisStep a μ := by
      have : x' - x = -((m : ℤ) • axisStep a μ) := by rw [h, neg_zsmul]
      rw [natCast_zsmul] at this
      rw [← sub_eq_zero]
      have h2 : x - (x' + m • axisStep a μ) = -(x' - x + m • axisStep a μ) := by abel
      rw [h2, this]
      simp
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp [signedSteps, forwardSteps]
    · have hneg : ¬ (0 ≤ -(m : ℤ)) := by omega
      rw [signedSteps, signedSteps, if_neg hneg, neg_neg, if_pos (by omega)]
      simp only [Int.toNat_natCast]
      rw [hx, backwardSteps_eq_reverse, reverse_map_opposite_twice]
theorem sum_map_reverse_opposite {E : Type} [AddCommGroup E] (f : InfiniteLattice.Link a → E)
    (hf : ∀ b, f b.opposite = -f b) (Γ : List (InfiniteLattice.Link a)) :
    (((Γ.map InfiniteLattice.Link.opposite).reverse).map f).sum = -(Γ.map f).sum := by
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.sum_append, List.sum_cons,
      List.map_nil, List.sum_nil, ih, hf, add_zero]
    abel
end AxisPathReversal
open AxisPathReversal in
theorem AxisPathReversal.holds : AxisPathReversal.statement := by
  intro L k j hL _ x x' μ n hd
  have ha : meshAt L k j ≠ 0 := by
    have hpos : (0 : ℝ) < L := by
      have : 0 < L := by
        have := hL.2
        omega
      exact_mod_cast this
    exact (zpow_pos hpos _).ne'
  have hn : x' - x = n • axisStep (meshAt L k j) μ := hd
  have hback : IsAxisDisplacement x' x μ (-n) := by
    change x - x' = (-n) • axisStep (meshAt L k j) μ
    rw [neg_zsmul, ← hn]
    abel
  have hpath : axisPath x' x =
      ((axisPath x x').map InfiniteLattice.Link.opposite).reverse := by
    rw [axisPath_eq_signedSteps ha hback, axisPath_eq_signedSteps ha hd, signedSteps_neg x x' μ n hn]
  refine ⟨⟨(μ, -n), hback⟩, hpath, ?_⟩
  intro 𝕜 E _ _ _ f hf
  rw [hpath]
  exact sum_map_reverse_opposite f hf _
end YangMills.Construction.Tower.FullSpace
