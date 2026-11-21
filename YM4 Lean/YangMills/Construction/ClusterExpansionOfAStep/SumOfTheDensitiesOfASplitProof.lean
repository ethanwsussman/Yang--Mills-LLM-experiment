import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.Interpolation
theorem sumActivitiesEqLogIntegral_of_logIntegralExpInterpolation
    (hinterp : LogIntegralExpInterpolationStatement) :
    SumActivitiesEqLogIntegral := by
  intro S n _ free D t hx ht hρ hp hreg
  classical
  set B := openBallsIn S free with hB
  have hBm : MeasurableSet B := isOpen_openBallsIn.measurableSet
  set Jtot : FreeCoords free → ℝ := fun η => ∑ y : TorusSite n, D.logJacobian y η with hJ
  set Φ : FreeCoords free → ℝ := fun η => ∑ y : TorusSite n, D.density y η with hΦ
  set Q : FreeCoords free → ℝ := fun η => ∑ y : TorusSite n, gaussianPart (R := S) t y η with hQ
  set A₀ : ℝ := S.coupling * D.totalCost 0 - Jtot 0 with hA₀
  have hpot : ∀ η ∈ closedBallsIn S free, D.potential η = D.totalInteraction η + A₀ - Φ η := fun η hη =>
    potential_eq hreg hη
  set μ : Measure (FreeCoords free) := volume.restrict B with hμdef
  have hfin : volume B < ⊤ :=
    (measure_mono openBallsIn_subset_closedBallsIn).trans_lt
      (isCompact_closedBallsIn (R := S) (free := free)).measure_lt_top
  have hfm : IsFiniteMeasure μ := ⟨by simpa [hμdef] using hfin⟩
  have hμ : μ ≠ 0 := by
    intro h0
    have h1 : volume B = 0 := Measure.restrict_eq_zero.mp h0
    have h2 : 0 < volume B := isOpen_openBallsIn.measure_pos _ ⟨0, fun b => by
      rw [coordNorm_eq_norm]; simpa using hρ⟩
    exact h2.ne' h1
  have hwm := measurable_cutoffProd (R := S) (free := free) hp
  have hw : Integrable (cutoffProd (R := S) (free := free)) μ := by
    refine Integrable.of_bound hwm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProd_nonneg η)]
    exact cutoffProd_le_one hρ hp η
  have hw0 : ∀ᵐ η ∂μ, 0 < cutoffProd (R := S) η :=
    ae_restrict_of_forall_mem hBm fun η h => cutoffProd_pos h
  have hdB : ∀ y, AEBounded μ (D.density y) := aeBounded_density hreg
  have hgB : ∀ y, AEBounded μ (gaussianPart (R := S) (free := free) t y) := aeBounded_gaussianPart t
  have hiB : ∀ y, AEBounded μ (D.interaction y) := aeBounded_interaction hreg
  have hItotB : AEBounded μ D.totalInteraction := AEBounded.sum _ fun y _ => hiB y
  have hΦB : AEBounded μ Φ := AEBounded.sum _ fun y _ => hdB y
  have hQB : AEBounded μ Q := AEBounded.sum _ fun y _ => hgB y
  set f₁ : FreeCoords free → ℝ := fun η => - Q η with hf₁
  set g₁ : FreeCoords free → ℝ := fun η => Q η - D.totalInteraction η with hg₁
  set f₂ : FreeCoords free → ℝ := fun η => - D.totalInteraction η with hf₂
  have hf₁B : AEBounded μ f₁ := hQB.neg
  have hg₁B : AEBounded μ g₁ := hQB.sub hItotB
  have hf₂B : AEBounded μ f₂ := hItotB.neg
  obtain ⟨M₁, a₁, b₁⟩ := hf₁B.exists_common_bound hg₁B
  obtain ⟨M₂, a₂, b₂⟩ := hf₂B.exists_common_bound hΦB
  obtain ⟨hpos₁, hcont₁, e₁⟩ := hinterp μ cutoffProd f₁ g₁ M₁ hμ hw hw0 hf₁B.1 hg₁B.1 a₁ b₁
  obtain ⟨hpos₂, hcont₂, e₂⟩ := hinterp μ cutoffProd f₂ Φ M₂ hμ hw hw0 hf₂B.1 hΦB.1 a₂ b₂
  have hm₁ : ∀ (G : FreeCoords free → ℝ) (τ : ℝ),
      weightedMean (D.interpolatedDensity t τ) G = tiltedMean μ cutoffProd f₁ g₁ G τ := by
    intro G τ
    unfold weightedMean tiltedMean BlockDensitySplit.interpolatedDensity
    have hE : ∀ η, -(τ * D.totalInteraction η) - (1 - τ) * ∑ y : TorusSite n, gaussianPart (R := S) t y η =
        f₁ η + τ * g₁ η := by
      intro η
      simp only [hf₁, hg₁, hQ]
      ring
    simp only [hE]
    congr 1 <;> exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun η h => by rw [cutoffProd_eq_zero h]; simp)).symm
  have hm₂ : ∀ (G : FreeCoords free → ℝ) (ν : ℝ),
      weightedMean (D.perturbedDensity ν) G = tiltedMean μ cutoffProd f₂ Φ G ν := by
    intro G ν
    unfold weightedMean tiltedMean BlockDensitySplit.perturbedDensity
    congr 1 <;> exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun η h => by rw [cutoffProd_eq_zero h]; simp)).symm
  have hGauss : Real.log (∫ η, cutoffProd (R := S) η * Real.exp (f₁ η) ∂μ) =
      (Fintype.card free : ℝ) * S.gaussianLogMass t := by
    have hprod : ∀ η : FreeCoords free, cutoffProd (R := S) η * Real.exp (f₁ η) =
        ∏ b : free, gaussianCutoffFactor S t (η b) := by
      intro η
      simp only [gaussianCutoffFactor]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Real.exp_sum]
      congr 1
      simp only [hf₁, hQ, gaussianPart, ← Finset.mul_sum]
      rw [sum_freeBondsAt (fun b => ‖η b‖ ^ 2), Finset.sum_neg_distrib, Finset.mul_sum]
    have hw₁ : ∫ η, cutoffProd (R := S) η * Real.exp (f₁ η) ∂μ =
        ∫ η, cutoffProd (R := S) η * Real.exp (f₁ η) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun η h => by rw [cutoffProd_eq_zero h]; simp)
    have hint : ∫ η : FreeCoords free, ∏ b : free, gaussianCutoffFactor S t (η b) =
        ∏ _b : free, ∫ z, gaussianCutoffFactor S t z :=
      integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : free => EuclideanSpace ℝ (Fin 3))
        fun _ => gaussianCutoffFactor S t
    rw [hw₁, integral_congr_ae (Filter.Eventually.of_forall hprod), hint, Finset.prod_const, Real.log_pow]
    rfl
  have hL : ∫ η, cutoffProd (R := S) η * Real.exp (-D.potential η) =
      Real.exp (-A₀) * ∫ η, cutoffProd (R := S) η * Real.exp (f₂ η + Φ η) ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (fun η h => by rw [cutoffProd_eq_zero h]; simp),
      ← integral_const_mul]
    refine setIntegral_congr_fun hBm fun η h => ?_
    show cutoffProd (R := S) η * Real.exp (-D.potential η) =
      Real.exp (-A₀) * (cutoffProd (R := S) η * Real.exp (f₂ η + Φ η))
    rw [hpot η (openBallsIn_subset_closedBallsIn h)]
    have e : -(D.totalInteraction η + A₀ - Φ η) = -A₀ + (f₂ η + Φ η) := by
      simp only [hf₂]
      ring
    rw [e, Real.exp_add]
    ring
  have hposC : 0 < ∫ η, cutoffProd (R := S) η * Real.exp (f₂ η + Φ η) ∂μ := by
    simpa using hpos₂ 1
  have h12 : ∫ η, cutoffProd (R := S) η * Real.exp (f₁ η + g₁ η) ∂μ =
      ∫ η, cutoffProd (R := S) η * Real.exp (f₂ η) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [hf₁, hg₁, hf₂]
    congr 2
    ring
  have hdiff : ∀ y, AEBounded μ fun η => D.interaction y η - gaussianPart (R := S) t y η :=
    fun y => (hiB y).sub (hgB y)
  have hT1 : ∑ y : TorusSite n, ∫ τ in (0 : ℝ)..1, tiltedMean μ cutoffProd f₁ g₁
      (fun η => D.interaction y η - gaussianPart (R := S) t y η) τ =
      - ∫ τ in (0 : ℝ)..1, tiltedMean μ cutoffProd f₁ g₁ g₁ τ := by
    rw [← intervalIntegral.integral_finsetSum fun y _ =>
      (hcont₁ _ (hdiff y).1 (hdiff y).2).intervalIntegrable 0 1, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    have e : g₁ = fun η => - ∑ y : TorusSite n, (D.interaction y η - gaussianPart (R := S) t y η) := by
      funext η
      simp only [hg₁, hQ, BlockDensitySplit.totalInteraction, Finset.sum_sub_distrib]
      ring
    show ∑ y : TorusSite n, tiltedMean μ cutoffProd f₁ g₁
        (fun η => D.interaction y η - gaussianPart (R := S) t y η) τ =
      - tiltedMean μ cutoffProd f₁ g₁ g₁ τ
    have e2 : tiltedMean μ cutoffProd f₁ g₁ g₁ τ =
        tiltedMean μ cutoffProd f₁ g₁
          (fun η => - ∑ y : TorusSite n, (D.interaction y η - gaussianPart (R := S) t y η)) τ := by
      conv_lhs => rw [show tiltedMean μ cutoffProd f₁ g₁ g₁ = tiltedMean μ cutoffProd f₁ g₁
        (fun η => - ∑ y : TorusSite n, (D.interaction y η - gaussianPart (R := S) t y η)) from by rw [← e]]
    rw [e2, tiltedMean_neg, neg_neg, tiltedMean_finset_sum _ _ hw hf₁B.1 hg₁B.1 a₁ b₁
      (fun y _ => (hdiff y).1) (fun y _ => (hdiff y).2)]
  have hT2 : ∑ y : TorusSite n, ∫ ν in (0 : ℝ)..1, tiltedMean μ cutoffProd f₂ Φ (D.density y) ν =
      ∫ ν in (0 : ℝ)..1, tiltedMean μ cutoffProd f₂ Φ Φ ν := by
    rw [← intervalIntegral.integral_finsetSum fun y _ =>
      (hcont₂ _ (hdB y).1 (hdB y).2).intervalIntegrable 0 1]
    refine intervalIntegral.integral_congr fun ν _ => ?_
    show ∑ y : TorusSite n, tiltedMean μ cutoffProd f₂ Φ (D.density y) ν = tiltedMean μ cutoffProd f₂ Φ Φ ν
    exact (tiltedMean_finset_sum _ _ hw hf₂B.1 hΦB.1 a₂ b₂ (fun y _ => (hdB y).1)
      (fun y _ => (hdB y).2) ν).symm
  have hZ : ∑ y : TorusSite n, D.activity t y = -A₀ + (Fintype.card free : ℝ) * S.gaussianLogMass t -
      (∑ y : TorusSite n, ∫ τ in (0 : ℝ)..1, tiltedMean μ cutoffProd f₁ g₁
        (fun η => D.interaction y η - gaussianPart (R := S) t y η) τ) +
      ∑ y : TorusSite n, ∫ ν in (0 : ℝ)..1, tiltedMean μ cutoffProd f₂ Φ (D.density y) ν := by
    unfold BlockDensitySplit.activity
    simp only [hm₁, hm₂, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, sum_card_freeBondsAt]
    simp only [hA₀, hJ, BlockDensitySplit.totalCost]
    ring
  rw [hL, Real.log_mul (Real.exp_pos _).ne' hposC.ne', Real.log_exp, hZ, hT1, hT2]
  rw [h12] at e₁
  linarith
end YangMills.Construction.ClusterExpansionOfAStep
end
