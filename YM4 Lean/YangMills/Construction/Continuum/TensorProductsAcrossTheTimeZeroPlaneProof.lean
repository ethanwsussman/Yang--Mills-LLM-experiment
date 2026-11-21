import YangMills.Construction.Continuum.OperationsKeepTheSpaces
import YangMills.Construction.Continuum.TensorProductsAcrossTheTimeZeroPlane
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace TensorSplit
variable {q q' : ℕ}
theorem headArgs_add_smul_castAdd (z : Config (q + q')) (i : Fin q) (v : Fin 4 → ℝ) (t : ℝ) :
    headArgs (z + t • (Pi.single (Fin.castAdd q' i) v : Config (q + q'))) =
      headArgs z + t • (Pi.single i v : Config q) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [headArgs]
  · have hne : Fin.castAdd q' j ≠ Fin.castAdd q' i := fun e => hj (Fin.castAdd_injective _ _ e)
    simp [headArgs, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hne]
theorem tailArgs_add_smul_castAdd (z : Config (q + q')) (i : Fin q) (v : Fin 4 → ℝ) (t : ℝ) :
    tailArgs (z + t • (Pi.single (Fin.castAdd q' i) v : Config (q + q'))) =
      tailArgs z := by
  funext j
  have hne : Fin.natAdd q j ≠ Fin.castAdd q' i := fun e =>
    absurd (congrArg Fin.val e) (by simp; omega)
  simp [tailArgs, Pi.single_eq_of_ne hne]
theorem tailArgs_add_smul_natAdd (z : Config (q + q')) (i : Fin q') (v : Fin 4 → ℝ) (t : ℝ) :
    tailArgs (z + t • (Pi.single (Fin.natAdd q i) v : Config (q + q'))) =
      tailArgs z + t • (Pi.single i v : Config q') := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [tailArgs]
  · have hne : Fin.natAdd q j ≠ Fin.natAdd q i := fun e => hj (Fin.natAdd_injective _ _ e)
    simp [tailArgs, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hne]
theorem headArgs_add_smul_natAdd (z : Config (q + q')) (i : Fin q') (v : Fin 4 → ℝ) (t : ℝ) :
    headArgs (z + t • (Pi.single (Fin.natAdd q i) v : Config (q + q'))) =
      headArgs z := by
  funext j
  have hne : Fin.castAdd q' j ≠ Fin.natAdd q i := fun e =>
    absurd (congrArg Fin.val e) (by simp; omega)
  simp [headArgs, Pi.single_eq_of_ne hne]
theorem coordPartial_castAdd_tensorFn (i : Fin q) (μ : Fin 4) (f : Config q → ℂ)
    (f' : Config q' → ℂ) :
    coordPartial (Fin.castAdd q' i) μ (tensorFn f f') =
      tensorFn (coordPartial i μ f) f' := by
  funext z
  simp only [coordPartial, lineDeriv, tensorFn, headArgs_add_smul_castAdd,
    tailArgs_add_smul_castAdd]
  exact deriv_mul_const_field _
theorem coordPartial_natAdd_tensorFn (i : Fin q') (μ : Fin 4) (f : Config q → ℂ)
    (f' : Config q' → ℂ) :
    coordPartial (Fin.natAdd q i) μ (tensorFn f f') =
      tensorFn f (coordPartial i μ f') := by
  funext z
  simp only [coordPartial, lineDeriv, tensorFn, headArgs_add_smul_natAdd,
    tailArgs_add_smul_natAdd]
  exact deriv_const_mul_field _
theorem iterate_coordPartial_castAdd (i : Fin q) (μ : Fin 4) (m : ℕ) (f : Config q → ℂ)
    (f' : Config q' → ℂ) :
    (coordPartial (Fin.castAdd q' i) μ)^[m] (tensorFn f f') =
      tensorFn ((coordPartial i μ)^[m] f) f' := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      coordPartial_castAdd_tensorFn, ih]
theorem iterate_coordPartial_natAdd (i : Fin q') (μ : Fin 4) (m : ℕ) (f : Config q → ℂ)
    (f' : Config q' → ℂ) :
    (coordPartial (Fin.natAdd q i) μ)^[m] (tensorFn f f') =
      tensorFn f ((coordPartial i μ)^[m] f') := by
  induction m generalizing f' with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      coordPartial_natAdd_tensorFn, ih]
def headIndex (γ : MultiIndex (q + q')) : MultiIndex q := fun i => γ (Fin.castAdd q' i)
def tailIndex (γ : MultiIndex (q + q')) : MultiIndex q' := fun i => γ (Fin.natAdd q i)
theorem order_eq_add (γ : MultiIndex (q + q')) :
    γ.order = (headIndex γ).order + (tailIndex γ).order := by
  simp only [MultiIndex.order, headIndex, tailIndex, Fin.sum_univ_add]
theorem foldr_castAdd_tensorFn (γ : MultiIndex (q + q')) (i : Fin q) (l : List (Fin 4))
    (f : Config q → ℂ) (f' : Config q' → ℂ) :
    l.foldr (fun μ h => (coordPartial (Fin.castAdd q' i) μ)^[γ (Fin.castAdd q' i) μ] h)
        (tensorFn f f') =
      tensorFn
        (l.foldr (fun μ h => (coordPartial i μ)^[headIndex γ i μ] h) f) f' := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_coordPartial_castAdd]
    rfl
theorem foldr_natAdd_tensorFn (γ : MultiIndex (q + q')) (i : Fin q') (l : List (Fin 4))
    (f : Config q → ℂ) (f' : Config q' → ℂ) :
    l.foldr (fun μ h => (coordPartial (Fin.natAdd q i) μ)^[γ (Fin.natAdd q i) μ] h)
        (tensorFn f f') =
      tensorFn f
        (l.foldr (fun μ h => (coordPartial i μ)^[tailIndex γ i μ] h) f') := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_coordPartial_natAdd]
    rfl
theorem finRange_add_eq_append (q q' : ℕ) :
    List.finRange (q + q') =
      (List.finRange q).map (Fin.castAdd q') ++ (List.finRange q').map (Fin.natAdd q) := by
  simp only [List.finRange, List.ofFn_add, List.map_ofFn]
  rfl
theorem iteratedPartial_tensorFn (γ : MultiIndex (q + q')) (f : Config q → ℂ)
    (f' : Config q' → ℂ) :
    iteratedPartial γ (tensorFn f f') =
      tensorFn (iteratedPartial (headIndex γ) f) (iteratedPartial (tailIndex γ) f') := by
  have htail : ∀ (l : List (Fin q')) (f : Config q → ℂ),
      (l.map (Fin.natAdd q)).foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordPartial i μ)^[γ i μ] h') h) (tensorFn f f') =
      tensorFn f (l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordPartial i μ)^[tailIndex γ i μ] h') h) f') := by
    intro l f
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih, foldr_natAdd_tensorFn]
  have hhead : ∀ (l : List (Fin q)) (f' : Config q' → ℂ),
      (l.map (Fin.castAdd q')).foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordPartial i μ)^[γ i μ] h') h) (tensorFn f f') =
      tensorFn (l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordPartial i μ)^[headIndex γ i μ] h') h) f) f' := by
    intro l f'
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih, foldr_castAdd_tensorFn]
  unfold iteratedPartial
  rw [finRange_add_eq_append, List.foldr_append, htail, hhead]
theorem euclidNorm_sq_eq_add (z : Config (q + q')) :
    euclidNorm z ^ 2 =
      euclidNorm (headArgs z) ^ 2 + euclidNorm (tailArgs z) ^ 2 := by
  unfold euclidNorm
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Fin.sum_univ_add]
  rfl
theorem weight_le_mul (k : ℕ) (z : Config (q + q')) :
    (1 + euclidNorm z ^ 2) ^ ((k : ℝ) / 2) ≤
      (1 + euclidNorm (headArgs z) ^ 2) ^ ((k : ℝ) / 2) *
        (1 + euclidNorm (tailArgs z) ^ 2) ^ ((k : ℝ) / 2) := by
  have hx : 0 ≤ euclidNorm (headArgs z) ^ 2 := sq_nonneg _
  have hy : 0 ≤ euclidNorm (tailArgs z) ^ 2 := sq_nonneg _
  rw [← Real.mul_rpow (by positivity) (by positivity), euclidNorm_sq_eq_add]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  nlinarith [mul_nonneg hx hy]
theorem weighted_term_le_schwartzSeminorm {n : ℕ} (k : ℕ) (f : Config n → ℂ) (x : Config n)
    (α : MultiIndex n) (hα : α.order ≤ k) :
    ENNReal.ofReal ((1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α f x‖) ≤
      schwartzSeminorm k f :=
  le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
theorem schwartzSeminorm_tensorFn_le (k : ℕ) (f : Config q → ℂ) (f' : Config q' → ℂ) :
    schwartzSeminorm k (tensorFn f f') ≤ schwartzSeminorm k f * schwartzSeminorm k f' := by
  refine iSup_le fun z => iSup_le fun γ => iSup_le fun hγ => ?_
  have h1 : (headIndex γ).order ≤ k := by
    have := order_eq_add γ
    omega
  have h2 : (tailIndex γ).order ≤ k := by
    have := order_eq_add γ
    omega
  refine le_trans ?_ (mul_le_mul' (weighted_term_le_schwartzSeminorm k f (headArgs z) _ h1)
    (weighted_term_le_schwartzSeminorm k f' (tailArgs z) _ h2))
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [iteratedPartial_tensorFn]
  simp only [tensorFn, norm_mul]
  calc _ ≤ ((1 + euclidNorm (headArgs z) ^ 2) ^ ((k : ℝ) / 2) *
          (1 + euclidNorm (tailArgs z) ^ 2) ^ ((k : ℝ) / 2)) *
        (‖iteratedPartial (headIndex γ) f (headArgs z)‖ *
          ‖iteratedPartial (tailIndex γ) f' (tailArgs z)‖) :=
        mul_le_mul_of_nonneg_right (weight_le_mul k z) (by positivity)
    _ = _ := by ring
theorem schwartzSeminorm_lt_top {n : ℕ} {φ : Config n → ℂ} (h : IsSchwartz φ) (k : ℕ) :
    schwartzSeminorm k φ < ⊤ :=
  (isSchwartz_iff_mem_schwartzSpace.1 h).2 k
theorem contDiff_tensorFn {φ : Config q → ℂ} {ψ : Config q' → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (tensorFn φ ψ) := by
  have h1 : ContDiff ℝ ∞ (headArgs : Config (q + q') → Config q) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.castAdd q' i)
  have h2 : ContDiff ℝ ∞ (tailArgs : Config (q + q') → Config q') :=
    contDiff_pi.2 fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.natAdd q i)
  exact (hφ.comp h1).mul (hψ.comp h2)
theorem isSchwartz_tensorFn {φ : Config q → ℂ} {ψ : Config q' → ℂ}
    (hφ : IsSchwartz φ) (hψ : IsSchwartz ψ) :
    IsSchwartz (tensorFn φ ψ) :=
  ⟨contDiff_tensorFn hφ.1 hψ.1, fun k _ => (schwartzSeminorm_tensorFn_le k φ ψ).trans_lt
    (ENNReal.mul_lt_top (schwartzSeminorm_lt_top hφ k) (schwartzSeminorm_lt_top hψ k))⟩
theorem mem_distinctArgs_of_neg_pos {z : Config (q + q')} (h1 : headArgs z ∈ negTimeSet q)
    (h2 : tailArgs z ∈ posTimeSet q') : z ∈ distinctArgs (q + q') := by
  have hcross : ∀ (i : Fin q) (j : Fin q'), z (Fin.castAdd q' i) ≠ z (Fin.natAdd q j) := by
    intro i j e
    have hi : -argTime (headArgs z) i > 0 := h1.2 i
    have hj : argTime (tailArgs z) j > 0 := h2.2 j
    have he : argTime (headArgs z) i = argTime (tailArgs z) j :=
      congrArg lastCoord e
    linarith
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => exact congrArg (Fin.castAdd q') (h1.1 hab)
    | right j => exact absurd hab (hcross i j)
  | right i =>
    induction b using Fin.addCases with
    | left j => exact absurd hab.symm (hcross j i)
    | right j => exact congrArg (Fin.natAdd q) (h2.1 hab)
theorem tensorFn_mem_schwartzFlatOffDiagonal {φ : Config q → ℂ} {ψ : Config q' → ℂ}
    (hφ : φ ∈ schwartzFlatOffNegTime q) (hψ : ψ ∈ schwartzFlatOffPosTime q') :
    tensorFn φ ψ ∈ schwartzFlatOffDiagonal (q + q') := by
  have hc := contDiff_tensorFn hφ.1.1 hψ.1.1
  refine ⟨isSchwartz_tensorFn hφ.1 hψ.1, hc, isOpen_distinctArgs,
    fun z hz => ⟨hc, fun γ => ?_⟩⟩
  rw [iteratedPartial_tensorFn]
  by_cases h1 : headArgs z ∈ negTimeSet q
  · by_cases h2 : tailArgs z ∈ posTimeSet q'
    · exact absurd (mem_distinctArgs_of_neg_pos h1 h2) hz
    · simp [tensorFn, (hψ.2.2.2 _ h2).2 (tailIndex γ)]
  · simp [tensorFn, (hφ.2.2.2 _ h1).2 (headIndex γ)]
end TensorSplit
open TensorSplit in
theorem tensorAcrossZeroTime_holds (hkeep : OperationsPreserveSchwartzSpaces) :
    TensorAcrossZeroTime := by
  intro q q' hq _ k φ ψ
  refine ⟨⟨isSchwartz_tensorFn φ.2 ψ.2, ?_⟩, ?_, ?_⟩
  · unfold bracketNorm
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono
      (ENNReal.mul_lt_top (schwartzSeminorm_lt_top φ.2 k) (schwartzSeminorm_lt_top ψ.2 k)).ne
      (schwartzSeminorm_tensorFn_le k φ.1 ψ.1)
  · exact tensorFn_mem_schwartzFlatOffDiagonal
  · intro h1 h2
    have hm : flipConj φ.1 ∈ schwartzFlatOffNegTime q := by
      rw [← (hkeep q hq).2.2.2.2]
      exact ⟨φ.1, h1, rfl⟩
    exact tensorFn_mem_schwartzFlatOffDiagonal hm h2
end YangMills.Construction.ConfigSpace
end
