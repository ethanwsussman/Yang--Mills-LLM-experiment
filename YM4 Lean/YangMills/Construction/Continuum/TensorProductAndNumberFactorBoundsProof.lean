import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import YangMills.Construction.Continuum.TensorProductAndNumberFactorBounds
import YangMills.Construction.Continuum.TensorProductsAcrossTheTimeZeroPlaneProof
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.TensorProductBounds
variable {q q' : ℕ}
def leftIdx (γ : MultiIdx4 (q + q')) : MultiIdx4 q := fun i => γ (Fin.castAdd q' i)
def rightIdx (γ : MultiIdx4 (q + q')) : MultiIdx4 q' := fun j => γ (Fin.natAdd q j)
theorem leftPart_add_smul_single_left (z : PointTuple (q + q')) (i : Fin q) (μ : Fin 4) (t : ℝ) :
    leftPart (z + t • (Pi.single (Fin.castAdd q' i) (Pi.single μ 1) : PointTuple (q + q'))) =
      leftPart z + t • (Pi.single i (Pi.single μ 1) : PointTuple q) := by
  funext a ν
  by_cases h : a = i
  · subst h
    simp [leftPart]
  · have h' : Fin.castAdd q' a ≠ Fin.castAdd q' i := fun e => h (Fin.castAdd_injective _ _ e)
    simp [leftPart, h, h']
theorem rightPart_add_smul_single_left (z : PointTuple (q + q')) (i : Fin q) (μ : Fin 4) (t : ℝ) :
    rightPart (z + t • (Pi.single (Fin.castAdd q' i) (Pi.single μ 1) : PointTuple (q + q'))) =
      rightPart z := by
  funext a ν
  have h' : Fin.natAdd q a ≠ Fin.castAdd q' i := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  simp [rightPart, h']
theorem leftPart_add_smul_single_right (z : PointTuple (q + q')) (j : Fin q') (μ : Fin 4) (t : ℝ) :
    leftPart (z + t • (Pi.single (Fin.natAdd q j) (Pi.single μ 1) : PointTuple (q + q'))) =
      leftPart z := by
  funext a ν
  have h' : Fin.castAdd q' a ≠ Fin.natAdd q j := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  simp [leftPart, h']
theorem rightPart_add_smul_single_right (z : PointTuple (q + q')) (j : Fin q') (μ : Fin 4) (t : ℝ) :
    rightPart (z + t • (Pi.single (Fin.natAdd q j) (Pi.single μ 1) : PointTuple (q + q'))) =
      rightPart z + t • (Pi.single j (Pi.single μ 1) : PointTuple q') := by
  funext a ν
  by_cases h : a = j
  · subst h
    simp [rightPart]
  · have h' : Fin.natAdd q a ≠ Fin.natAdd q j := fun e => h (Fin.natAdd_injective _ _ e)
    simp [rightPart, h, h']
theorem coordDeriv_tensorFun_left (i : Fin q) (μ : Fin 4) (f : PointTuple q → ℂ)
    (g : PointTuple q' → ℂ) :
    coordDeriv (Fin.castAdd q' i) μ (tensorFun f g) =
      tensorFun (coordDeriv i μ f) g := by
  funext z
  simp only [coordDeriv, tensorFun, lineDeriv, leftPart_add_smul_single_left,
    rightPart_add_smul_single_left]
  exact deriv_mul_const_field _
theorem coordDeriv_tensorFun_right (j : Fin q') (μ : Fin 4) (f : PointTuple q → ℂ)
    (g : PointTuple q' → ℂ) :
    coordDeriv (Fin.natAdd q j) μ (tensorFun f g) =
      tensorFun f (coordDeriv j μ g) := by
  funext z
  simp only [coordDeriv, tensorFun, lineDeriv, leftPart_add_smul_single_right,
    rightPart_add_smul_single_right]
  exact deriv_const_mul_field _
theorem iterate_coordDeriv_tensorFun_left (i : Fin q) (μ : Fin 4) (m : ℕ)
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    (coordDeriv (Fin.castAdd q' i) μ)^[m] (tensorFun f g) =
      tensorFun ((coordDeriv i μ)^[m] f) g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, coordDeriv_tensorFun_left]
theorem iterate_coordDeriv_tensorFun_right (j : Fin q') (μ : Fin 4) (m : ℕ)
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    (coordDeriv (Fin.natAdd q j) μ)^[m] (tensorFun f g) =
      tensorFun f ((coordDeriv j μ)^[m] g) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, coordDeriv_tensorFun_right]
theorem foldr_coords_tensorFun_left (γ : MultiIdx4 (q + q')) (i : Fin q) (l : List (Fin 4))
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    l.foldr (fun μ h' => (coordDeriv (Fin.castAdd q' i) μ)^[γ (Fin.castAdd q' i) μ] h')
        (tensorFun f g) =
      tensorFun
        (l.foldr (fun μ h' => (coordDeriv i μ)^[leftIdx γ i μ] h') f) g := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_coordDeriv_tensorFun_left]
    rfl
theorem foldr_coords_tensorFun_right (γ : MultiIdx4 (q + q')) (j : Fin q') (l : List (Fin 4))
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    l.foldr (fun μ h' => (coordDeriv (Fin.natAdd q j) μ)^[γ (Fin.natAdd q j) μ] h')
        (tensorFun f g) =
      tensorFun f
        (l.foldr (fun μ h' => (coordDeriv j μ)^[rightIdx γ j μ] h') g) := by
  induction l with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_coordDeriv_tensorFun_right]
    rfl
theorem foldr_args_tensorFun_left (γ : MultiIdx4 (q + q')) (l : List (Fin q))
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    (l.map (Fin.castAdd q')).foldr
        (fun i h => (List.finRange 4).foldr
          (fun μ h' => (coordDeriv i μ)^[γ i μ] h') h) (tensorFun f g) =
      tensorFun
        (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ h' => (coordDeriv i μ)^[leftIdx γ i μ] h') h) f) g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, foldr_coords_tensorFun_left]
theorem foldr_args_tensorFun_right (γ : MultiIdx4 (q + q')) (l : List (Fin q'))
    (f : PointTuple q → ℂ) (g : PointTuple q' → ℂ) :
    (l.map (Fin.natAdd q)).foldr
        (fun i h => (List.finRange 4).foldr
          (fun μ h' => (coordDeriv i μ)^[γ i μ] h') h) (tensorFun f g) =
      tensorFun f
        (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ h' => (coordDeriv i μ)^[rightIdx γ i μ] h') h) g) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, foldr_coords_tensorFun_right]
theorem finRange_add_eq_append (q q' : ℕ) :
    List.finRange (q + q') =
      (List.finRange q).map (Fin.castAdd q') ++ (List.finRange q').map (Fin.natAdd q) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSplit.finRange_add_eq_append <;> assumption
theorem multiDeriv_tensorFun (γ : MultiIdx4 (q + q')) (f : PointTuple q → ℂ)
    (g : PointTuple q' → ℂ) :
    multiDeriv γ (tensorFun f g) =
      tensorFun (multiDeriv (leftIdx γ) f) (multiDeriv (rightIdx γ) g) := by
  unfold multiDeriv
  rw [finRange_add_eq_append, List.foldr_append, foldr_args_tensorFun_right,
    foldr_args_tensorFun_left]
theorem idxOrder_eq_add (γ : MultiIdx4 (q + q')) :
    idxOrder γ = idxOrder (leftIdx γ) + idxOrder (rightIdx γ) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSplit.order_eq_add <;> assumption
theorem weight_le_mul (k : ℕ) (z : PointTuple (q + q')) :
    (1 + tupleNorm z ^ 2) ^ ((k : ℝ) / 2) ≤
      (1 + tupleNorm (leftPart z) ^ 2) ^ ((k : ℝ) / 2) *
        (1 + tupleNorm (rightPart z) ^ 2) ^ ((k : ℝ) / 2) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSplit.weight_le_mul <;> assumption
theorem term_le_weightedSeminorm (k : ℕ) {n : ℕ} (f : PointTuple n → ℂ) (x : PointTuple n)
    (α : MultiIdx4 n) (h : idxOrder α ≤ k) :
    ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖multiDeriv α f x‖) ≤
      weightedSeminorm k f :=
  le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le h le_rfl))
theorem weightedSeminorm_tensorFun_le (k : ℕ) (φ : PointTuple q → ℂ) (ψ : PointTuple q' → ℂ) :
    weightedSeminorm k (tensorFun φ ψ) ≤ weightedSeminorm k φ * weightedSeminorm k ψ := by
  refine iSup_le fun z => iSup_le fun γ => iSup_le fun h => ?_
  have h₁ : idxOrder (leftIdx γ) ≤ k := by
    have := idxOrder_eq_add γ
    omega
  have h₂ : idxOrder (rightIdx γ) ≤ k := by
    have := idxOrder_eq_add γ
    omega
  set a := multiDeriv (leftIdx γ) φ (leftPart z) with ha
  set b := multiDeriv (rightIdx γ) ψ (rightPart z) with hb
  have hval : multiDeriv γ (tensorFun φ ψ) z = a * b := by
    rw [multiDeriv_tensorFun]
    rfl
  calc ENNReal.ofReal ((1 + tupleNorm z ^ 2) ^ ((k : ℝ) / 2) *
          ‖multiDeriv γ (tensorFun φ ψ) z‖)
      ≤ ENNReal.ofReal (((1 + tupleNorm (leftPart z) ^ 2) ^ ((k : ℝ) / 2) * ‖a‖) *
          ((1 + tupleNorm (rightPart z) ^ 2) ^ ((k : ℝ) / 2) * ‖b‖)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hval, norm_mul]
        calc _ ≤ ((1 + tupleNorm (leftPart z) ^ 2) ^ ((k : ℝ) / 2) *
                (1 + tupleNorm (rightPart z) ^ 2) ^ ((k : ℝ) / 2)) * (‖a‖ * ‖b‖) :=
              mul_le_mul_of_nonneg_right (weight_le_mul k z) (by positivity)
          _ = _ := by ring
    _ = ENNReal.ofReal ((1 + tupleNorm (leftPart z) ^ 2) ^ ((k : ℝ) / 2) * ‖a‖) *
          ENNReal.ofReal ((1 + tupleNorm (rightPart z) ^ 2) ^ ((k : ℝ) / 2) * ‖b‖) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ weightedSeminorm k φ * weightedSeminorm k ψ :=
        mul_le_mul' (term_le_weightedSeminorm k φ _ _ h₁) (term_le_weightedSeminorm k ψ _ _ h₂)
theorem contDiff_tensorFun {φ : PointTuple q → ℂ} {ψ : PointTuple q' → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (tensorFun φ ψ) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSplit.contDiff_tensorFn <;> assumption
theorem injective_of_mem_negativeTimeLocus_of_mem_positiveTimeLocus {z : PointTuple (q + q')}
    (hx : leftPart z ∈ negativeTimeLocus q) (hy : rightPart z ∈ positiveTimeLocus q') :
    Function.Injective z := by
  have mixed : ∀ (i : Fin q) (j : Fin q'), z (Fin.castAdd q' i) ≠ z (Fin.natAdd q j) := by
    intro i j e
    have h₁ : -timeCoord (leftPart z) i > 0 := hx.2 i
    have h₂ : timeCoord (rightPart z) j > 0 := hy.2 j
    have h₃ : z (Fin.castAdd q' i) 3 = z (Fin.natAdd q j) 3 := congrFun e 3
    simp only [timeCoord, leftPart, rightPart] at h₁ h₂
    linarith
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' => exact congrArg _ (hx.1 hab)
    | right j => exact absurd hab (mixed i j)
  | right j =>
    induction b using Fin.addCases with
    | left i => exact absurd hab.symm (mixed i j)
    | right j' => exact congrArg _ (hy.1 hab)
theorem multiDeriv_tensorFun_eq_zero_of_mem_diagonalLocus {φ : PointTuple q → ℂ}
    {ψ : PointTuple q' → ℂ}
    (hφ : VanishesToInfiniteOrderOff φ (negativeTimeLocus q))
    (hψ : VanishesToInfiniteOrderOff ψ (positiveTimeLocus q'))
    (α : MultiIdx4 (q + q')) {z : PointTuple (q + q')} (hz : z ∈ diagonalLocus (q + q')) :
    multiDeriv α (tensorFun φ ψ) z = 0 := by
  rw [multiDeriv_tensorFun]
  by_cases hx : leftPart z ∈ negativeTimeLocus q
  · by_cases hy : rightPart z ∈ positiveTimeLocus q'
    · exact absurd (injective_of_mem_negativeTimeLocus_of_mem_positiveTimeLocus hx hy) hz
    · have := (hψ.2.2 _ hy).2.2 (rightIdx α)
      simp only [tensorFun, this, mul_zero]
  · have := (hφ.2.2 _ hx).2.2 (leftIdx α)
    simp only [tensorFun, this, zero_mul]
theorem tensorSeminormBounds_holds (h : DerivRules.Combined) : TensorSeminormBounds := by
  obtain ⟨-, hC, -, -⟩ := h
  refine ⟨fun q q' k _ _ _ φ hφ ψ hψ => ?_, fun q' k _ _ c ψ hψ => ?_⟩
  · have hmem : tensorFun φ ψ ∈ schwartzSet (q + q') :=
      ⟨contDiff_tensorFun hφ.1 hψ.1, fun k hk =>
        lt_of_le_of_lt (weightedSeminorm_tensorFun_le k φ ψ)
          (ENNReal.mul_lt_top (hφ.2 k hk) (hψ.2 k hk))⟩
    exact ⟨hmem, weightedSeminorm_tensorFun_le k φ ψ, fun hf hg =>
      ⟨hmem, fun α z hz => multiDeriv_tensorFun_eq_zero_of_mem_diagonalLocus hf hg α hz⟩⟩
  · obtain ⟨-, -, -, -, -, -, hconst, -⟩ := hC q' ψ hψ.1
    have key : ∀ (x : PointTuple q') (α : MultiIdx4 q'),
        ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) *
            ‖multiDeriv α (scalarTensorLeft c ψ) x‖) =
          ENNReal.ofReal ‖c‖ * ENNReal.ofReal ((1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) *
            ‖multiDeriv α ψ x‖) := by
      intro x α
      have hval : multiDeriv α (scalarTensorLeft c ψ) x = c * multiDeriv α ψ x :=
        congrFun (hconst c α) x
      rw [hval, norm_mul, ← ENNReal.ofReal_mul (norm_nonneg c)]
      congr 1
      ring
    simp only [weightedSeminorm, key, ENNReal.mul_iSup]
end YangMills.Construction.TestSpaces.TensorProductBounds
