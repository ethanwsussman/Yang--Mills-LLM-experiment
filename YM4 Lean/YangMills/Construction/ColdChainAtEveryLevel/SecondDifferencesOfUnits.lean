import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace SecondDifferences
theorem mul_secondDifference_eq (A₁ A₂ A₃ B₁ B₂ B₃ : ℍ[ℝ]) :
    A₃ * B₃ - A₁ * B₁ - A₂ * B₂ + 1 = (A₃ - A₁ - A₂ + 1) * B₃ + (A₁ + A₂ - 1) * (B₃ - B₁ - B₂ + 1) +
      (A₁ - 1) * (B₂ - 1) + (A₂ - 1) * (B₁ - 1) := by
  noncomm_ring
structure SecondDifferenceBound (s₁ s₂ C : ℝ) (A₁ A₂ A₃ : BlockAverages.UnitQuaternion) : Prop where
  size_left : ‖(A₁ : ℍ[ℝ]) - 1‖ ≤ s₁
  size_right : ‖(A₂ : ℍ[ℝ]) - 1‖ ≤ s₂
  second_diff : ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ≤ C * s₁ * s₂
theorem SecondDifferenceBound.mul {s₁ s₂ C s₁' s₂' C' C'' : ℝ}
    {A₁ A₂ A₃ B₁ B₂ B₃ : BlockAverages.UnitQuaternion} (hA : SecondDifferenceBound s₁ s₂ C A₁ A₂ A₃)
    (hB : SecondDifferenceBound s₁' s₂' C' B₁ B₂ B₃) (hC : C ≤ C'') (hC' : 3 * C' ≤ C'') (hone : 1 ≤ C'') :
    SecondDifferenceBound (s₁ + s₁') (s₂ + s₂') C'' (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) where
  size_left := by
    have e : ((A₁ * B₁ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 = ((A₁ : ℍ[ℝ]) - 1) * B₁ + ((B₁ : ℍ[ℝ]) - 1) := by
      push_cast
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, mul_one]
    exact add_le_add hA.size_left hB.size_left
  size_right := by
    have e : ((A₂ * B₂ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 = ((A₂ : ℍ[ℝ]) - 1) * B₂ + ((B₂ : ℍ[ℝ]) - 1) := by
      push_cast
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, mul_one]
    exact add_le_add hA.size_right hB.size_right
  second_diff := by
    have hs₁ : 0 ≤ s₁ := (norm_nonneg _).trans hA.size_left
    have hs₂ : 0 ≤ s₂ := (norm_nonneg _).trans hA.size_right
    have hs₁' : 0 ≤ s₁' := (norm_nonneg _).trans hB.size_left
    have hs₂' : 0 ≤ s₂' := (norm_nonneg _).trans hB.size_right
    have e := mul_secondDifference_eq A₁ A₂ A₃ B₁ B₂ B₃
    change ‖(A₃ : ℍ[ℝ]) * B₃ - A₁ * B₁ - A₂ * B₂ + 1‖ ≤ _
    rw [e]
    have n1 : ‖((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * B₃‖ ≤ C * s₁ * s₂ := by
      rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, mul_one]
      exact hA.second_diff
    have hsum : ‖(A₁ : ℍ[ℝ]) + A₂ - 1‖ ≤ 3 := by
      refine (norm_sub_le _ _).trans ?_
      have := norm_add_le (A₁ : ℍ[ℝ]) (A₂ : ℍ[ℝ])
      rw [BlockAverages.norm_coe_unitQuaternion, BlockAverages.norm_coe_unitQuaternion] at this
      rw [norm_one]
      linarith
    have n2 : ‖((A₁ : ℍ[ℝ]) + A₂ - 1) * ((B₃ : ℍ[ℝ]) - B₁ - B₂ + 1)‖ ≤ 3 * (C' * s₁' * s₂') := by
      rw [norm_mul]
      exact mul_le_mul hsum hB.second_diff (norm_nonneg _) (by norm_num)
    have n3 : ‖((A₁ : ℍ[ℝ]) - 1) * ((B₂ : ℍ[ℝ]) - 1)‖ ≤ s₁ * s₂' := by
      rw [norm_mul]
      exact mul_le_mul hA.size_left hB.size_right (norm_nonneg _) hs₁
    have n4 : ‖((A₂ : ℍ[ℝ]) - 1) * ((B₁ : ℍ[ℝ]) - 1)‖ ≤ s₂ * s₁' := by
      rw [norm_mul]
      exact mul_le_mul hA.size_right hB.size_left (norm_nonneg _) hs₂
    calc _ ≤ C * s₁ * s₂ + 3 * (C' * s₁' * s₂') + s₁ * s₂' + s₂ * s₁' := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add n1 n2)) n3)) n4)
      _ ≤ C'' * s₁ * s₂ + C'' * s₁' * s₂' + C'' * s₁ * s₂' + C'' * s₂ * s₁' := by
          have a1 : C * s₁ * s₂ ≤ C'' * s₁ * s₂ := by
            have := mul_le_mul_of_nonneg_right hC (mul_nonneg hs₁ hs₂)
            nlinarith
          have a2 : 3 * (C' * s₁' * s₂') ≤ C'' * s₁' * s₂' := by
            have := mul_le_mul_of_nonneg_right hC' (mul_nonneg hs₁' hs₂')
            nlinarith
          have a3 : s₁ * s₂' ≤ C'' * s₁ * s₂' := by
            have := mul_le_mul_of_nonneg_right hone (mul_nonneg hs₁ hs₂')
            nlinarith
          have a4 : s₂ * s₁' ≤ C'' * s₂ * s₁' := by
            have := mul_le_mul_of_nonneg_right hone (mul_nonneg hs₂ hs₁')
            nlinarith
          linarith
      _ = C'' * (s₁ + s₁') * (s₂ + s₂') := by ring
structure FirstOrderApprox (s c : ℝ) (A : BlockAverages.UnitQuaternion) (x : ℍ[ℝ]) : Prop where
  size : ‖(A : ℍ[ℝ]) - 1‖ ≤ s
  remainder : ‖(A : ℍ[ℝ]) - 1 - x‖ ≤ c * s ^ 2
theorem FirstOrderApprox.mul {s c s' c' c'' : ℝ} {A B : BlockAverages.UnitQuaternion} {x y : ℍ[ℝ]}
    (hA : FirstOrderApprox s c A x) (hB : FirstOrderApprox s' c' B y)
    (hc : c ≤ c'') (hc' : c' ≤ c'') (hone : 1 ≤ c'') : FirstOrderApprox (s + s') c'' (A * B) (x + y) where
  size := by
    have e : ((A * B : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 = ((A : ℍ[ℝ]) - 1) * B + ((B : ℍ[ℝ]) - 1) := by
      push_cast
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, BlockAverages.norm_coe_unitQuaternion, mul_one]
    exact add_le_add hA.size hB.size
  remainder := by
    have hs : 0 ≤ s := (norm_nonneg _).trans hA.size
    have hs' : 0 ≤ s' := (norm_nonneg _).trans hB.size
    have e : ((A * B : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 - (x + y) = ((A : ℍ[ℝ]) - 1 - x) + ((B : ℍ[ℝ]) - 1 - y) +
        ((A : ℍ[ℝ]) - 1) * ((B : ℍ[ℝ]) - 1) := by
      push_cast
      noncomm_ring
    rw [e]
    have n3 : ‖((A : ℍ[ℝ]) - 1) * ((B : ℍ[ℝ]) - 1)‖ ≤ s * s' := by
      rw [norm_mul]
      exact mul_le_mul hA.size hB.size (norm_nonneg _) hs
    have b1 := hA.remainder
    have b2 := hB.remainder
    have c1 : c * s ^ 2 ≤ c'' * s ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    have c2 : c' * s' ^ 2 ≤ c'' * s' ^ 2 := mul_le_mul_of_nonneg_right hc' (sq_nonneg _)
    have c3 : s * s' ≤ c'' * (s * s') := by
      have := mul_le_mul_of_nonneg_right hone (mul_nonneg hs hs')
      linarith
    have c4 : 0 ≤ c'' * (s * s') := by positivity
    calc _ ≤ c * s ^ 2 + c' * s' ^ 2 + s * s' :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add b1 b2)) n3)
      _ ≤ c'' * (s + s') ^ 2 := by nlinarith
theorem neg_re_secondDifference_eq (A₁ A₂ A₃ : BlockAverages.UnitQuaternion) :
    -((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1).re = inner ℝ ((A₁ : ℍ[ℝ]) - 1) ((A₂ : ℍ[ℝ]) - 1) +
      inner ℝ ((A₁ : ℍ[ℝ]) - 1 + ((A₂ : ℍ[ℝ]) - 1)) ((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) +
      ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ^ 2 / 2 := by
  set u₁ := (A₁ : ℍ[ℝ]) - 1 with hu₁
  set u₂ := (A₂ : ℍ[ℝ]) - 1 with hu₂
  set δ := (A₃ : ℍ[ℝ]) - A₁ - A₂ + 1 with hδ
  have h1 := BlockAverages.norm_coe_sub_one_sq A₁
  have h2 := BlockAverages.norm_coe_sub_one_sq A₂
  have h3 := BlockAverages.norm_coe_sub_one_sq A₃
  have e3 : (A₃ : ℍ[ℝ]) - 1 = u₁ + u₂ + δ := by
    rw [hu₁, hu₂, hδ]
    abel
  rw [e3] at h3
  rw [← hu₁] at h1
  rw [← hu₂] at h2
  have n1 : ‖u₁ + u₂ + δ‖ ^ 2 = ‖u₁ + u₂‖ ^ 2 + 2 * inner ℝ (u₁ + u₂) δ + ‖δ‖ ^ 2 := norm_add_sq_real _ _
  have n2 : ‖u₁ + u₂‖ ^ 2 = ‖u₁‖ ^ 2 + 2 * inner ℝ u₁ u₂ + ‖u₂‖ ^ 2 := norm_add_sq_real _ _
  have hre : δ.re = (A₃ : ℍ[ℝ]).re - (A₁ : ℍ[ℝ]).re - (A₂ : ℍ[ℝ]).re + 1 := by
    rw [hδ]
    simp
  rw [hre]
  linarith
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem abs_neg_re_secondDifference_mul_sub_inner_le (A₁ A₂ A₃ P : BlockAverages.UnitQuaternion) (v w : ℍ[ℝ]) :
    |-(((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * P).re - inner ℝ v w| ≤
      ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ * ‖(P : ℍ[ℝ]) - 1‖ +
      (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ +
      ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ +
      ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ := by
  have h := neg_re_secondDifference_eq A₁ A₂ A₃
  set u₁ := (A₁ : ℍ[ℝ]) - 1 with hu₁
  set u₂ := (A₂ : ℍ[ℝ]) - 1 with hu₂
  set δ := (A₃ : ℍ[ℝ]) - A₁ - A₂ + 1 with hδ
  have s1 : (δ * P).re = δ.re + (δ * ((P : ℍ[ℝ]) - 1)).re := by
    have : δ * P = δ + δ * ((P : ℍ[ℝ]) - 1) := by noncomm_ring
    rw [this]
    simp
  have s2 : inner ℝ u₁ u₂ - inner ℝ v w = inner ℝ (u₁ - v) u₂ + inner ℝ v (u₂ - w) := by
    rw [inner_sub_left u₁ v u₂, inner_sub_right v u₂ w]
    ring
  have e : -(δ * P).re - inner ℝ v w = -(δ * ((P : ℍ[ℝ]) - 1)).re + inner ℝ (u₁ + u₂) δ + ‖δ‖ ^ 2 / 2 +
      inner ℝ (u₁ - v) u₂ + inner ℝ v (u₂ - w) := by
    rw [s1]
    linarith
  rw [e]
  have a1 : |-(δ * ((P : ℍ[ℝ]) - 1)).re| ≤ ‖δ‖ * ‖(P : ℍ[ℝ]) - 1‖ := by
    rw [abs_neg, ← norm_mul]
    exact abs_re_le_norm _
  have a2 : |inner ℝ (u₁ + u₂) δ| ≤ (‖u₁‖ + ‖u₂‖) * ‖δ‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _))
  have a3 : |‖δ‖ ^ 2 / 2| = ‖δ‖ ^ 2 / 2 := abs_of_nonneg (by positivity)
  have a4 : |inner ℝ (u₁ - v) u₂| ≤ ‖u₁ - v‖ * ‖u₂‖ := abs_real_inner_le_norm _ _
  have a5 : |inner ℝ v (u₂ - w)| ≤ ‖v‖ * ‖u₂ - w‖ := abs_real_inner_le_norm _ _
  calc _ ≤ |-(δ * ((P : ℍ[ℝ]) - 1)).re| + |inner ℝ (u₁ + u₂) δ| + |‖δ‖ ^ 2 / 2| + |inner ℝ (u₁ - v) u₂| +
        |inner ℝ v (u₂ - w)| := by
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        exact abs_add_le _ _
    _ ≤ _ := by
        rw [a3]
        linarith
theorem abs_weighted_secondDifference_sub_inner_le (r₀ ρ₁ ρ₂ ρ₃ : ℝ) (A₁ A₂ A₃ P : BlockAverages.UnitQuaternion)
    (v w : ℍ[ℝ]) {E : ℝ}
    (hE : ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ * ‖(P : ℍ[ℝ]) - 1‖ +
      (‖(A₁ : ℍ[ℝ]) - 1‖ + ‖(A₂ : ℍ[ℝ]) - 1‖) * ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ +
      ‖(A₃ : ℍ[ℝ]) - A₁ - A₂ + 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1 - v‖ * ‖(A₂ : ℍ[ℝ]) - 1‖ +
      ‖v‖ * ‖(A₂ : ℍ[ℝ]) - 1 - w‖ ≤ E) :
    |(r₀ + ρ₃) * (1 - ((A₃ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re) -
        (r₀ + ρ₁) * (1 - ((A₁ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re) -
        (r₀ + ρ₂) * (1 - ((A₂ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re) + r₀ * (1 - (P : ℍ[ℝ]).re) -
        inner ℝ v w| ≤
      (|r₀ - 1| + |ρ₃|) * (|inner ℝ v w| + E) + E +
        ‖(P : ℍ[ℝ]) - 1‖ ^ 2 / 2 * |ρ₃ - ρ₁ - ρ₂| +
        |ρ₃ - ρ₁| * (‖(A₁ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1‖ * ‖(P : ℍ[ℝ]) - 1‖) +
        |ρ₃ - ρ₂| * (‖(A₂ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₂ : ℍ[ℝ]) - 1‖ * ‖(P : ℍ[ℝ]) - 1‖) := by
  set f₀ := 1 - (P : ℍ[ℝ]).re with hf₀
  set f₁ := 1 - ((A₁ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re with hf₁
  set f₂ := 1 - ((A₂ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re with hf₂
  set f₃ := 1 - ((A₃ * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re with hf₃
  set p := ‖(P : ℍ[ℝ]) - 1‖ with hp
  have key := abs_neg_re_secondDifference_mul_sub_inner_le A₁ A₂ A₃ P v w
  have hΔ : f₃ - f₁ - f₂ + f₀ = -(((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * P).re := by
    have : ((A₃ : ℍ[ℝ]) - A₁ - A₂ + 1) * P = (A₃ : ℍ[ℝ]) * P - A₁ * P - A₂ * P + P := by noncomm_ring
    rw [this, hf₀, hf₁, hf₂, hf₃]
    change (1 - ((A₃ : ℍ[ℝ]) * P).re) - (1 - ((A₁ : ℍ[ℝ]) * P).re) - (1 - ((A₂ : ℍ[ℝ]) * P).re) +
      (1 - (P : ℍ[ℝ]).re) = _
    simp only [Quaternion.re_add, Quaternion.re_sub]
    ring
  set Δ := f₃ - f₁ - f₂ + f₀ with hΔd
  have hκ : |Δ - inner ℝ v w| ≤ E := by
    rw [hΔ]
    exact key.trans hE
  have hΔn : |Δ| ≤ |inner ℝ v w| + E := by
    have : Δ = inner ℝ v w + (Δ - inner ℝ v w) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (by linarith)
  have hf0 : |f₀| = p ^ 2 / 2 := by
    have h1 := BlockAverages.norm_coe_sub_one_sq P
    rw [hf₀, ← hp] at *
    rw [abs_of_nonneg (by nlinarith [sq_nonneg p])]
    linarith
  have hfk : ∀ A : BlockAverages.UnitQuaternion, |(1 - ((A * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re) - f₀| ≤
      ‖(A : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A : ℍ[ℝ]) - 1‖ * p := by
    intro A
    have h1 := BlockAverages.norm_coe_sub_one_sq A
    have e : (1 - ((A * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re) - f₀ =
        -((A : ℍ[ℝ]) - 1).re - (((A : ℍ[ℝ]) - 1) * ((P : ℍ[ℝ]) - 1)).re := by
      have e1 : ((A * P : BlockAverages.UnitQuaternion) : ℍ[ℝ]) =
          ((A : ℍ[ℝ]) - 1) * ((P : ℍ[ℝ]) - 1) + ((A : ℍ[ℝ]) - 1) + (P : ℍ[ℝ]) := by
        change (A : ℍ[ℝ]) * P = _
        noncomm_ring
      rw [e1, hf₀]
      simp only [Quaternion.re_add, Quaternion.re_sub]
      ring
    rw [e]
    have a1 : -((A : ℍ[ℝ]) - 1).re = ‖(A : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by
      simp only [Quaternion.re_sub, Quaternion.re_one]
      linarith
    have a2 : |(((A : ℍ[ℝ]) - 1) * ((P : ℍ[ℝ]) - 1)).re| ≤ ‖(A : ℍ[ℝ]) - 1‖ * p := by
      rw [hp, ← norm_mul]
      exact abs_re_le_norm _
    rw [a1]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    linarith
  have e : (r₀ + ρ₃) * f₃ - (r₀ + ρ₁) * f₁ - (r₀ + ρ₂) * f₂ + r₀ * f₀ - inner ℝ v w =
      ((r₀ - 1) + ρ₃) * Δ + (Δ - inner ℝ v w) + f₀ * (ρ₃ - ρ₁ - ρ₂) + (ρ₃ - ρ₁) * (f₁ - f₀) +
        (ρ₃ - ρ₂) * (f₂ - f₀) := by
    rw [hΔd]
    ring
  rw [e]
  have b1 : |((r₀ - 1) + ρ₃) * Δ| ≤ (|r₀ - 1| + |ρ₃|) * (|inner ℝ v w| + E) := by
    rw [abs_mul]
    exact mul_le_mul (abs_add_le _ _) hΔn (abs_nonneg _) (by positivity)
  have b3 : |f₀ * (ρ₃ - ρ₁ - ρ₂)| ≤ p ^ 2 / 2 * |ρ₃ - ρ₁ - ρ₂| := by
    rw [abs_mul, hf0]
  have b4 : |(ρ₃ - ρ₁) * (f₁ - f₀)| ≤ |ρ₃ - ρ₁| * (‖(A₁ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₁ : ℍ[ℝ]) - 1‖ * p) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfk A₁) (abs_nonneg _)
  have b5 : |(ρ₃ - ρ₂) * (f₂ - f₀)| ≤ |ρ₃ - ρ₂| * (‖(A₂ : ℍ[ℝ]) - 1‖ ^ 2 / 2 + ‖(A₂ : ℍ[ℝ]) - 1‖ * p) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfk A₂) (abs_nonneg _)
  calc _ ≤ |((r₀ - 1) + ρ₃) * Δ| + |Δ - inner ℝ v w| + |f₀ * (ρ₃ - ρ₁ - ρ₂)| + |(ρ₃ - ρ₁) * (f₁ - f₀)| +
        |(ρ₃ - ρ₂) * (f₂ - f₀)| := by
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        exact abs_add_le _ _
    _ ≤ _ := by linarith
end SecondDifferences
end YangMills.Construction
end
