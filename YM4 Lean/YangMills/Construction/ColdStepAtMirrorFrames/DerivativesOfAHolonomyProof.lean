import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAHolonomy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages NormedSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives
def leibnizConvolution (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i)
theorem leibnizConvolution_nonneg {a b : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    0 ≤ leibnizConvolution a b j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i)) (hb _)
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem natCast_le_smoothOrder (j : ℕ) : (j : WithTop ℕ∞) ≤ smoothOrder := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
theorem norm_iteratedFDeriv_mul_le_leibnizConvolution {k : ℕ} {u v : (Fin k → ℝ) → ℍ[ℝ]}
    {a b : ℕ → ℝ} (hu : ContDiff ℝ smoothOrder u)
    (hv : ContDiff ℝ smoothOrder v) (ha : ∀ j, ‖iteratedFDeriv ℝ j u 0‖ ≤ a j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j v 0‖ ≤ b j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun τ => u τ * v τ) 0‖ ≤ leibnizConvolution a b j := by
  have h := norm_iteratedFDeriv_mul_le (N := smoothOrder) hu hv (0 : Fin k → ℝ) (n := j)
    (natCast_le_smoothOrder j)
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := ha i
  have h2 := hb (j - i)
  have n1 := norm_nonneg (iteratedFDeriv ℝ i u 0)
  have n2 := norm_nonneg (iteratedFDeriv ℝ (j - i) v 0)
  have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 n2 (mul_nonneg hc (n1.trans h1))
def constantBound (j : ℕ) : ℝ := if j = 0 then 1 else 0
theorem constantBound_nonneg (j : ℕ) : 0 ≤ constantBound j := by
  unfold constantBound
  split_ifs <;> norm_num
theorem norm_iteratedFDeriv_const_le {k : ℕ} {g : ℍ[ℝ]} (hg : ‖g‖ = 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => g) 0‖ ≤ constantBound j := by
  by_cases hj : j = 0
  · subst hj
    simp [constantBound, hg]
  · rw [iteratedFDeriv_const_of_ne hj]
    simp [constantBound, hj]
theorem contDiff_quaternionExp : ContDiff ℝ smoothOrder (exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
def expBound (k j : ℕ) : ℝ := ‖iteratedFDeriv ℝ j (exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * (k : ℝ) ^ j
theorem expBound_nonneg (k j : ℕ) : 0 ≤ expBound k j := by
  unfold expBound
  positivity
theorem norm_iteratedFDeriv_exp_comp_le {k : ℕ} (A : (Fin k → ℝ) →L[ℝ] ℍ[ℝ]) (hA : ‖A‖ ≤ k)
    (j : ℕ) : ‖iteratedFDeriv ℝ j (fun τ => exp (A τ)) 0‖ ≤ expBound k j := by
  have h1 : iteratedFDeriv ℝ j ((exp : ℍ[ℝ] → ℍ[ℝ]) ∘ A) 0 =
      (iteratedFDeriv ℝ j (exp : ℍ[ℝ] → ℍ[ℝ]) (A 0)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right contDiff_quaternionExp 0 (natCast_le_smoothOrder j)
  have h2 : (fun τ => exp (A τ)) = (exp : ℍ[ℝ] → ℍ[ℝ]) ∘ A := rfl
  rw [h2, h1, map_zero]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  unfold expBound
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) hA j
variable {F : BlockFrame} {lev k : ℕ}
def bondVariationMap (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site lev)
    (i : Fin 4) : (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = (y, i) then (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight
    (X l : ℍ[ℝ]) else 0
theorem bondVariation_apply (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site lev) (i : Fin 4) (τ : Fin k → ℝ) :
    bondVariationMap c X y i τ = ((bondSpread c X τ y i : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondVariationMap bondSpread
  rw [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem norm_bondVariation_le (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : ∀ i, ‖X i‖ ≤ 1) (y : F.Site lev) (i : Fin 4) : ‖bondVariationMap c X y i‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg k) fun τ => ?_
  rw [bondVariation_apply]
  have h2 : ‖((bondSpread c X τ y i : imaginaryQuaternions) : ℍ[ℝ])‖ =
      ‖(bondSpread c X τ y i : imaginaryQuaternions)‖ := rfl
  rw [h2]
  unfold bondSpread
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin k)),
      ‖(if c l = (y, i) then τ l • X l else 0 : imaginaryQuaternions)‖ ≤ ‖τ‖ := by
    intro l _
    split_ifs
    · rw [norm_smul]
      have h1 : ‖τ l‖ ≤ ‖τ‖ := norm_le_pi_norm τ l
      calc ‖τ l‖ * ‖X l‖ ≤ ‖τ‖ * 1 :=
            mul_le_mul h1 (hX l) (norm_nonneg _) (norm_nonneg _)
        _ = ‖τ‖ := mul_one _
    · simp
  simpa using Finset.sum_le_sum this
theorem expUnit_inv (v : imaginaryQuaternions) : (expUnit v)⁻¹ = expUnit (-v) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
def linkBound (k j : ℕ) : ℝ :=
  leibnizConvolution (expBound k) constantBound j + leibnizConvolution constantBound (expBound k) j
theorem linkBound_nonneg (k j : ℕ) : 0 ≤ linkBound k j :=
  add_nonneg (leibnizConvolution_nonneg (expBound_nonneg k) constantBound_nonneg j)
    (leibnizConvolution_nonneg constantBound_nonneg (expBound_nonneg k) j)
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
def perturbedLink (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (x : F.Site lev) (st : PathStep) (τ : Fin k → ℝ) : ℍ[ℝ] :=
  ((linkValue (leftTranslate (bondSpread c X τ) W) x st : UnitQuaternion) : ℍ[ℝ])
theorem perturbedLink_forward (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (x : F.Site lev) (i : Fin 4) (τ : Fin k → ℝ) :
    perturbedLink W c X x (i, true) τ =
      exp (bondVariationMap c X x i τ) * ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
  simp only [perturbedLink, linkValue, leftTranslate, if_true, bondVariation_apply]
  rfl
theorem bondSpread_neg (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (y : F.Site lev) (i : Fin 4) :
    bondSpread c (fun l => -X l) τ y i = -bondSpread c X τ y i := by
  unfold bondSpread
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem perturbedLink_backward (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (x : F.Site lev) (i : Fin 4) (τ : Fin k → ℝ) :
    perturbedLink W c X x (i, false) τ =
      (((W (x - unitStep lev i) i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        exp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i τ) := by
  simp only [perturbedLink, linkValue, leftTranslate, Bool.false_eq_true, if_false, mul_inv_rev,
    expUnit_inv]
  rw [bondVariation_apply, bondSpread_neg]
  rfl
theorem contDiff_perturbedLink (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (x : F.Site lev) (st : PathStep) :
    ContDiff ℝ smoothOrder (perturbedLink W c X x st) := by
  obtain ⟨i, s⟩ := st
  cases s with
  | true =>
    have he : perturbedLink W c X x (i, true) =
        fun τ => exp (bondVariationMap c X x i τ) * ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
      funext τ
      exact perturbedLink_forward W c X x i τ
    rw [he]
    exact (contDiff_quaternionExp.comp (bondVariationMap c X x i).contDiff).mul contDiff_const
  | false =>
    have he : perturbedLink W c X x (i, false) =
        fun τ => (((W (x - unitStep lev i) i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          exp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i τ) := by
      funext τ
      exact perturbedLink_backward W c X x i τ
    rw [he]
    exact contDiff_const.mul
      (contDiff_quaternionExp.comp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i).contDiff)
theorem contDiff_perturbedHolonomy (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : List PathStep) (x : F.Site lev) :
    ContDiff ℝ smoothOrder (perturbedHolonomy W x l c X) := by
  induction l generalizing x with
  | nil =>
    have he : perturbedHolonomy W x [] c X = fun _ => (1 : ℍ[ℝ]) := by
      funext τ
      rfl
    rw [he]
    exact contDiff_const
  | cons st r ih =>
    have he : perturbedHolonomy W x (st :: r) c X =
        fun τ => perturbedLink W c X x st τ *
          perturbedHolonomy W (x + stepDisplacement lev st) r c X τ := by
      funext τ
      rfl
    rw [he]
    exact (contDiff_perturbedLink W c X x st).mul (ih _)
theorem perturbedLink_bounds (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : ∀ i, ‖X i‖ ≤ 1) (x : F.Site lev) (st : PathStep) :
    ContDiff ℝ smoothOrder (perturbedLink W c X x st) ∧
      ∀ j, ‖iteratedFDeriv ℝ j (perturbedLink W c X x st) 0‖ ≤ linkBound k j := by
  obtain ⟨i, s⟩ := st
  cases s with
  | true =>
    have he : perturbedLink W c X x (i, true) =
        fun τ => exp (bondVariationMap c X x i τ) * ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
      funext τ
      exact perturbedLink_forward W c X x i τ
    have h1 : ContDiff ℝ smoothOrder fun τ : Fin k → ℝ => exp (bondVariationMap c X x i τ) :=
      contDiff_quaternionExp.comp (bondVariationMap c X x i).contDiff
    rw [he]
    refine ⟨h1.mul contDiff_const, fun j => ?_⟩
    have := norm_iteratedFDeriv_mul_le_leibnizConvolution h1
      (contDiff_const (c := ((W x i : UnitQuaternion) : ℍ[ℝ])))
      (norm_iteratedFDeriv_exp_comp_le _ (norm_bondVariation_le c X hX x i))
      (norm_iteratedFDeriv_const_le (norm_coe_unitQuaternion _)) j
    have h2 := leibnizConvolution_nonneg constantBound_nonneg (expBound_nonneg k) j
    unfold linkBound
    linarith
  | false =>
    have he : perturbedLink W c X x (i, false) =
        fun τ => (((W (x - unitStep lev i) i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          exp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i τ) := by
      funext τ
      exact perturbedLink_backward W c X x i τ
    have h1 : ContDiff ℝ smoothOrder fun τ : Fin k → ℝ =>
        exp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i τ) :=
      contDiff_quaternionExp.comp (bondVariationMap c (fun l => -X l) (x - unitStep lev i) i).contDiff
    rw [he]
    refine ⟨contDiff_const.mul h1, fun j => ?_⟩
    have hn : ‖bondVariationMap c (fun l => -X l) (x - unitStep lev i) i‖ ≤ k :=
      norm_bondVariation_le c _ (fun l => by simpa using hX l) _ _
    have := norm_iteratedFDeriv_mul_le_leibnizConvolution
      (contDiff_const (c := (((W (x - unitStep lev i) i)⁻¹ : UnitQuaternion) : ℍ[ℝ]))) h1
      (norm_iteratedFDeriv_const_le (norm_coe_unitQuaternion _))
      (norm_iteratedFDeriv_exp_comp_le _ hn) j
    have h2 := leibnizConvolution_nonneg (expBound_nonneg k) constantBound_nonneg j
    unfold linkBound
    linarith
def holonomyBound (k : ℕ) : ℕ → ℕ → ℝ
  | 0 => constantBound
  | n + 1 => leibnizConvolution (linkBound k) (holonomyBound k n)
theorem holonomyBound_nonneg (k n j : ℕ) : 0 ≤ holonomyBound k n j := by
  induction n generalizing j with
  | zero => exact constantBound_nonneg j
  | succ n ih => exact leibnizConvolution_nonneg (linkBound_nonneg k) ih j
theorem perturbedHolonomy_cons (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (x : F.Site lev) (st : PathStep) (r : List PathStep)
    (τ : Fin k → ℝ) :
    perturbedHolonomy W x (st :: r) c X τ =
      perturbedLink W c X x st τ * perturbedHolonomy W (x + stepDisplacement lev st) r c X τ :=
  rfl
theorem perturbedHolonomy_bounds (W : F.GaugeField lev) (c : Fin k → F.Site lev × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : ∀ i, ‖X i‖ ≤ 1) (l : List PathStep)
    (x : F.Site lev) :
    ContDiff ℝ smoothOrder (perturbedHolonomy W x l c X) ∧
      ∀ j, ‖iteratedFDeriv ℝ j (perturbedHolonomy W x l c X) 0‖ ≤ holonomyBound k l.length j := by
  induction l generalizing x with
  | nil =>
    have he : perturbedHolonomy W x [] c X = fun _ => (1 : ℍ[ℝ]) := by
      funext τ
      rfl
    rw [he]
    exact ⟨contDiff_const, fun j => norm_iteratedFDeriv_const_le (by simp) j⟩
  | cons st r ih =>
    obtain ⟨h1, h2⟩ := perturbedLink_bounds W c X hX x st
    obtain ⟨h3, h4⟩ := ih (x + stepDisplacement lev st)
    have he : perturbedHolonomy W x (st :: r) c X =
        fun τ => perturbedLink W c X x st τ *
          perturbedHolonomy W (x + stepDisplacement lev st) r c X τ := by
      funext τ
      exact perturbedHolonomy_cons W c X x st r τ
    rw [he]
    exact ⟨h1.mul h3, fun j => norm_iteratedFDeriv_mul_le_leibnizConvolution h1 h3 h2 h4 j⟩
theorem bondSpread_update (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions)
    (i : Fin k) (τ : Fin k → ℝ) (s : ℝ) (y : F.Site lev) (d : Fin 4) (h : c i ≠ (y, d)) :
    bondSpread c X (Function.update τ i s) y d = bondSpread c X τ y d := by
  unfold bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = i
  · subst hl
    simp [h]
  · simp [Function.update_of_ne hl]
theorem perturbedHolonomy_update_of_not_mem (W : F.GaugeField lev)
    (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions) (i : Fin k)
    (l : List PathStep) (x : F.Site lev) (h : c i ∉ pathPositiveBonds x l) (τ : Fin k → ℝ)
    (s : ℝ) :
    perturbedHolonomy W x l c X (Function.update τ i s) = perturbedHolonomy W x l c X τ := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have h' := h
    simp only [pathPositiveBonds, List.mem_cons, not_or] at h'
    rw [perturbedHolonomy_cons, perturbedHolonomy_cons, ih _ h'.2]
    congr 1
    obtain ⟨d, b⟩ := st
    cases b with
    | true =>
      have := bondSpread_update c X i τ s x d (by simpa using h'.1)
      simp only [perturbedLink, linkValue, if_true, leftTranslate, this]
    | false =>
      have := bondSpread_update c X i τ s (x - unitStep lev d) d (by simpa using h'.1)
      simp only [perturbedLink, linkValue, Bool.false_eq_true, if_false, leftTranslate, this]
theorem holonomyDerivativeBounds : HolonomyDerivativeBounds := by
  refine ⟨holonomyBound, holonomyBound_nonneg, ?_⟩
  intro F lev W x l k c X
  exact ⟨contDiff_perturbedHolonomy W c X l x, fun hX => (perturbedHolonomy_bounds W c X hX l x).2,
    fun i hi τ s => perturbedHolonomy_update_of_not_mem W c X i l x hi τ s⟩
end YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives
end
