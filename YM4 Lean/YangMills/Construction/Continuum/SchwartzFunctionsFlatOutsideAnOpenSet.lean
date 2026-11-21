import YangMills.Construction.ConfigSpace.TimeSlicesAndOpenSets
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
variable {n : ℕ}
theorem iteratedPartial_zero (φ : Config n → ℂ) : iteratedPartial (0 : MultiIndex n) φ = φ := by
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (g : Config n → ℂ),
      l.foldr (fun μ g' => (coordPartial i μ)^[(0 : MultiIndex n) i μ] g') g = g := by
    intro i l g
    induction l with
    | nil => rfl
    | cons μ l ih => simp
  have outer : ∀ l : List (Fin n), l.foldr (fun i g => (List.finRange 4).foldr
      (fun μ g' => (coordPartial i μ)^[(0 : MultiIndex n) i μ] g') g) φ = φ := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.foldr_cons, inner, ih]
  exact outer _
def IsSchwartz (φ : Config n → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ k : ℕ, 1 ≤ k → schwartzSeminorm k φ < ⊤
theorem schwartzSeminorm_zero_le_one (φ : Config n → ℂ) :
    schwartzSeminorm 0 φ ≤ schwartzSeminorm 1 φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le (hα.trans zero_le_one) ?_))
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have h : (1 : ℝ) ≤ 1 + euclidNorm x ^ 2 := by nlinarith [sq_nonneg (euclidNorm x)]
  simpa using Real.one_le_rpow h (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) / 2)
theorem isSchwartz_iff_mem_schwartzSpace {φ : Config n → ℂ} :
    IsSchwartz φ ↔ φ ∈ schwartzSpace n := by
  constructor
  · rintro ⟨hs, hk⟩
    refine ⟨hs, fun k => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact (schwartzSeminorm_zero_le_one φ).trans_lt (hk 1 le_rfl)
    · exact hk k h
  · rintro ⟨hs, hk⟩
    exact ⟨hs, fun k _ => hk k⟩
def FlatAt (φ : Config n → ℂ) (x : Config n) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ α : MultiIndex n, iteratedPartial α φ x = 0
theorem FlatAt.eq_zero {φ : Config n → ℂ} {x : Config n} (h : FlatAt φ x) : φ x = 0 := by
  have := h.2 0
  rwa [iteratedPartial_zero] at this
def FlatOn (φ : Config n → ℂ) (Z : Set (Config n)) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ x ∈ Z, FlatAt φ x
def FlatOff (φ : Config n → ℂ) (V : Set (Config n)) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsOpen V ∧ ∀ x ∈ Vᶜ, FlatAt φ x
def smoothCompactSupportIn (U : Set (Config n)) : Set (Config n → ℂ) :=
  {φ | IsOpen U ∧ ContDiff ℝ ∞ φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ U}
def c1CompactSupportIn (U : Set (Config n)) : Set (Config n → ℂ) :=
  {φ | IsOpen U ∧ ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ U}
theorem isOpen_distinctArgs : IsOpen (distinctArgs n) := by
  have h : distinctArgs n = ⋂ (i : Fin n) (j : Fin n), {x : Config n | i ≠ j → x i ≠ x j} := by
    ext x
    simp only [distinctArgs, TestFunctions.injectiveTuples, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hx i j hij e => hij (hx e), fun hx i j e => by_contra fun hij => hx i j hij e⟩
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using isOpen_ne_fun (continuous_apply i) (continuous_apply j)
theorem isOpen_posTimeSet : IsOpen (posTimeSet n) := by
  have h : posTimeSet n = distinctArgs n ∩ ⋂ i : Fin n, {x : Config n | argTime x i > 0} := by
    ext x
    simp [posTimeSet, distinctArgs]
  rw [h]
  refine isOpen_distinctArgs.inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_lt continuous_const ((continuous_apply (3 : Fin 4)).comp (continuous_apply i))
theorem isOpen_negTimeSet : IsOpen (negTimeSet n) := by
  have h : negTimeSet n = distinctArgs n ∩ ⋂ i : Fin n, {x : Config n | -argTime x i > 0} := by
    ext x
    simp [negTimeSet, distinctArgs]
  rw [h]
  refine isOpen_distinctArgs.inter (isOpen_iInter_of_finite fun i => ?_)
  have hc : Continuous fun x : Config n => argTime x i :=
    (continuous_apply (3 : Fin 4)).comp (continuous_apply i)
  exact isOpen_lt continuous_const hc.neg
def schwartzFlatOffDiagonal (n : ℕ) : Set (Config n → ℂ) :=
  {φ | IsSchwartz φ ∧ FlatOff φ (distinctArgs n)}
def schwartzFlatOffPosTime (n : ℕ) : Set (Config n → ℂ) :=
  {φ | IsSchwartz φ ∧ FlatOff φ (posTimeSet n)}
def schwartzFlatOffNegTime (n : ℕ) : Set (Config n → ℂ) :=
  {φ | IsSchwartz φ ∧ FlatOff φ (negTimeSet n)}
theorem compl_distinctArgs : (distinctArgs n)ᶜ = diagonalSet n := by
  ext x
  simp only [distinctArgs, TestFunctions.injectiveTuples, Set.mem_compl_iff, Set.mem_ofPred_eq,
    diagonalSet, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    simp only [Function.Injective, not_forall] at hx
    obtain ⟨i, j, e, hij⟩ := hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, e⟩
    · exact ⟨j, i, h, e.symm⟩
  · rintro ⟨i, j, h, e⟩ hx
    exact h.ne (hx e)
end ConfigSpace
end YangMills.Construction
end
