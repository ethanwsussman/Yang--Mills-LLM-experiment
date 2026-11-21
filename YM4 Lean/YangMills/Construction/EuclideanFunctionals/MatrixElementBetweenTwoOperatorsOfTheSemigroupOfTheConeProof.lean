import YangMills.Construction.EuclideanFunctionals.MatrixElementBetweenTwoOperatorsOfTheSemigroupOfTheCone
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ConeSandwich
open SpectralPoint
section PowerSeriesLines
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem norm_monomial_le_of_norm_le {w w' : Fin 4 → ℂ} (hw : ∀ μ, ‖w μ‖ ≤ ‖w' μ‖)
    (γ : YangMills.Construction.PowerSeries.MultiIndex 4) :
    ‖YangMills.Construction.PowerSeries.MultiIndex.monomial w γ‖ ≤
      ‖YangMills.Construction.PowerSeries.MultiIndex.monomial w' γ‖ := by
  simp only [YangMills.Construction.PowerSeries.MultiIndex.monomial, norm_prod, norm_pow]
  exact Finset.prod_le_prod (fun μ _ => by positivity)
    (fun μ _ => pow_le_pow_left₀ (norm_nonneg _) (hw μ) _)
theorem differentiable_monomial_smul (v : Fin 4 → ℂ)
    (γ : YangMills.Construction.PowerSeries.MultiIndex 4) :
    Differentiable ℂ fun ζ : ℂ => YangMills.Construction.PowerSeries.MultiIndex.monomial (ζ • v) γ := by
  unfold YangMills.Construction.PowerSeries.MultiIndex.monomial
  simp only [Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem differentiableAt_line_zero_of_hasSum {T : (Fin 4 → ℂ) → K →L[ℂ] K} {p : Fin 4 → ℂ} {d : ℝ}
    (hd : 0 < d) {A : YangMills.Construction.PowerSeries.MultiIndex 4 → K →L[ℂ] K}
    (hA : ∀ w : Fin 4 → ℂ, ∑ μ, ‖w μ‖ < d →
      Summable (fun γ => ‖YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • A γ‖) ∧
        HasSum (fun γ => YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • A γ) (T (p + w)))
    (v : Fin 4 → ℂ) : DifferentiableAt ℂ (fun ζ : ℂ => T (p + ζ • v)) 0 := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ∑ μ, ‖v μ‖ := ⟨_, rfl⟩
  have hnonneg : 0 ≤ ∑ μ, ‖v μ‖ := Finset.sum_nonneg fun μ _ => norm_nonneg _
  have hMpos : 0 < M := by rw [hMdef]; linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = d / M := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos hd hMpos
  have hρM : ρ * M = d := by rw [hρdef]; field_simp
  have hρlt : ρ * ∑ μ, ‖v μ‖ < d := by
    rw [← hρM, hMdef]
    nlinarith
  let b : Fin 4 → ℂ := fun μ => (ρ : ℂ) * (‖v μ‖ : ℂ)
  have hb : ∀ μ, ‖b μ‖ = ρ * ‖v μ‖ := fun μ => by simp [b, abs_of_pos hρpos]
  have hbsum : ∑ μ, ‖b μ‖ < d := by
    simp only [hb, ← Finset.mul_sum]
    exact hρlt
  have hcoord : ∀ ζ : ℂ, ‖ζ‖ < ρ → ∀ μ, ‖(ζ • v) μ‖ ≤ ‖b μ‖ := fun ζ hζ μ => by
    rw [hb μ, Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_right hζ.le (norm_nonneg _)
  have hsmall : ∀ ζ : ℂ, ‖ζ‖ < ρ → ∑ μ, ‖(ζ • v) μ‖ < d := fun ζ hζ =>
    lt_of_le_of_lt (Finset.sum_le_sum fun μ _ => hcoord ζ hζ μ) hbsum
  have hon : DifferentiableOn ℂ
      (fun ζ : ℂ => ∑' γ, YangMills.Construction.PowerSeries.MultiIndex.monomial (ζ • v) γ • A γ)
      (Metric.ball 0 ρ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (hA b hbsum).1 (fun γ => ?_)
      Metric.isOpen_ball ?_
    · exact ((differentiable_monomial_smul v γ).smul_const (A γ)).differentiableOn
    · intro γ ζ hζ
      have hζ' : ‖ζ‖ < ρ := by simpa using hζ
      rw [norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_monomial_le_of_norm_le (hcoord ζ hζ') γ) (norm_nonneg _)
  have hnhds : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hρpos
  refine (hon.differentiableAt hnhds).congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with ζ hζ
  have hζ' : ‖ζ‖ < ρ := by simpa using hζ
  exact (hA _ (hsmall ζ hζ')).2.tsum_eq.symm
theorem differentiableAt_line_of_shift {T : (Fin 4 → ℂ) → K →L[ℂ] K} (p v : Fin 4 → ℂ) (ζ₀ : ℂ)
    (h : DifferentiableAt ℂ (fun ζ : ℂ => T ((p + ζ₀ • v) + ζ • v)) 0) :
    DifferentiableAt ℂ (fun ζ : ℂ => T (p + ζ • v)) ζ₀ := by
  have htrans : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ζ₀) ζ₀ := by fun_prop
  have h' : DifferentiableAt ℂ (fun ζ : ℂ => T ((p + ζ₀ • v) + ζ • v))
      ((fun ζ : ℂ => ζ - ζ₀) ζ₀) := by
    simpa using h
  have hcomp := DifferentiableAt.comp (f := fun ζ : ℂ => ζ - ζ₀) ζ₀ h' htrans
  have heq : ((fun ζ : ℂ => T ((p + ζ₀ • v) + ζ • v)) ∘ fun ζ : ℂ => ζ - ζ₀) =
      fun ζ : ℂ => T (p + ζ • v) := by
    funext ζ
    simp only [Function.comp]
    congr 1
    rw [sub_smul]
    abel
  rwa [heq] at hcomp
theorem continuousOn_inner_mul_mul_apply {X : Type*} [TopologicalSpace X] {s : Set X}
    {F G : X → K →L[ℂ] K} (B : K →L[ℂ] K) (x y : K) (hF : ContinuousOn (fun t => star (F t) x) s)
    (hG : ContinuousOn (fun t => G t y) s) :
    ContinuousOn (fun t => ⟪x, (F t * B * G t) y⟫_ℂ) s := by
  have heq : ∀ t, ⟪x, (F t * B * G t) y⟫_ℂ = ⟪star (F t) x, B (G t y)⟫_ℂ := fun t => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rfl
  simp only [heq]
  exact hF.inner (B.continuous.comp_continuousOn hG)
omit [CompleteSpace K] in
theorem differentiableAt_inner_mul_mul_apply {F G : ℂ → K →L[ℂ] K} {ζ : ℂ}
    (hF : DifferentiableAt ℂ F ζ) (hG : DifferentiableAt ℂ G ζ) (B : K →L[ℂ] K) (x y : K) :
    DifferentiableAt ℂ (fun t => ⟪x, (F t * B * G t) y⟫_ℂ) ζ := by
  have h₁ : DifferentiableAt ℂ (fun t => G t y) ζ := hG.clm_apply (differentiableAt_const y)
  have h₂ : DifferentiableAt ℂ (fun t => B (G t y)) ζ := B.differentiableAt.comp ζ h₁
  have h₃ : DifferentiableAt ℂ (fun t => F t (B (G t y))) ζ := hF.clm_apply h₂
  exact (innerSL ℂ x).differentiableAt.comp ζ h₃
omit [CompleteSpace K] in
theorem norm_inner_mul_mul_apply_le {F G : K →L[ℂ] K} (B : K →L[ℂ] K) (hF : ‖F‖ ≤ 1) (hG : ‖G‖ ≤ 1)
    (x y : K) : ‖⟪x, (F * B * G) y⟫_ℂ‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  have h₁ : ‖G y‖ ≤ ‖y‖ := by
    calc ‖G y‖ ≤ ‖G‖ * ‖y‖ := G.le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have h₂ : ‖B (G y)‖ ≤ ‖B‖ * ‖y‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
  have h₃ : ‖F (B (G y))‖ ≤ ‖B‖ * ‖y‖ := by
    calc ‖F (B (G y))‖ ≤ ‖F‖ * ‖B (G y)‖ := F.le_opNorm _
      _ ≤ 1 * ‖B (G y)‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ ≤ ‖B‖ * ‖y‖ := by rw [one_mul]; exact h₂
  calc ‖⟪x, (F * B * G) y⟫_ℂ‖ = ‖⟪x, F (B (G y))⟫_ℂ‖ := rfl
    _ ≤ ‖x‖ * ‖F (B (G y))‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖B‖ * ‖y‖) := mul_le_mul_of_nonneg_left h₃ (norm_nonneg _)
    _ = ‖B‖ * ‖x‖ * ‖y‖ := by ring
end PowerSeriesLines
section ConePoints
variable (η : ℝ) (z : Fin 4 → ℂ)
theorem timeEighthPoint_three : timeEighthPoint η 3 = ((η / 8 : ℝ) : ℂ) := by
  simp [timeEighthPoint, ofRealPoint, timeVec, YangMills.Construction.PeriodicLattice.coordVec]
theorem timeEighthPoint_castSucc (j : Fin 3) : timeEighthPoint η j.castSucc = 0 := by
  have hj : j.castSucc ≠ (3 : Fin 4) := by
    fin_cases j <;> decide
  simp [timeEighthPoint, ofRealPoint, timeVec, YangMills.Construction.PeriodicLattice.coordVec, hj]
theorem coneMargin_timeEighthPoint_add : coneMargin (timeEighthPoint η + z) =
    η / 8 + (z 3).re - ∑ j : Fin 3, |(z j.castSucc).im| := by
  simp only [coneMargin, spatialComplex, Pi.add_apply, timeEighthPoint_three,
    timeEighthPoint_castSucc, zero_add, Complex.add_re, Complex.ofReal_re]
theorem coneMargin_timeEighthPoint_sub : coneMargin (timeEighthPoint η - z) =
    η / 8 - (z 3).re - ∑ j : Fin 3, |(z j.castSucc).im| := by
  simp only [coneMargin, spatialComplex, Pi.sub_apply, timeEighthPoint_three,
    timeEighthPoint_castSucc, zero_sub, Complex.sub_re, Complex.ofReal_re, Complex.neg_im, abs_neg]
theorem continuous_complexExtensionGauge : Continuous complexExtensionGauge := by
  unfold complexExtensionGauge
  exact (continuous_abs.comp (Complex.continuous_re.comp (continuous_apply 3))).add
    (continuous_finsetSum _ fun j _ =>
      continuous_abs.comp (Complex.continuous_im.comp (continuous_apply _)))
def contractPoint (t : ℝ) : Fin 4 → ℂ := fun k =>
  if k = 3 then ((t * (z k).re : ℝ) : ℂ) + ((z k).im : ℂ) * Complex.I
  else ((z k).re : ℂ) + ((t * (z k).im : ℝ) : ℂ) * Complex.I
theorem continuous_contractPoint : Continuous (contractPoint z) := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = 3
  · simp only [contractPoint, hk, if_true]
    exact (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).add continuous_const
  · simp only [contractPoint, hk, if_false]
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)
theorem contractPoint_one : contractPoint z 1 = z := by
  funext k
  by_cases hk : k = 3 <;> simp [contractPoint, hk, Complex.re_add_im]
theorem complexExtensionGauge_contractPoint {t : ℝ} (ht : 0 ≤ t) :
    complexExtensionGauge (contractPoint z t) = t * complexExtensionGauge z := by
  have hne : ∀ j : Fin 3, j.castSucc ≠ (3 : Fin 4) := fun j => by
    fin_cases j <;> decide
  unfold complexExtensionGauge
  simp [contractPoint, hne, abs_mul, abs_of_nonneg ht, mul_add, Finset.mul_sum]
theorem complexExtensionDomain_subset_closed {η : ℝ} :
    complexExtensionDomain η ⊆ closedComplexExtensionDomain η := fun z hz =>
  show complexExtensionGauge z ≤ η / 8 from le_of_lt (show complexExtensionGauge z < η / 8 from hz)
theorem closure_complexExtensionDomain {η : ℝ} (hη : 0 < η) :
    closure (complexExtensionDomain η) = closedComplexExtensionDomain η := by
  apply Subset.antisymm
  · exact closure_minimal complexExtensionDomain_subset_closed
      (show IsClosed {z | complexExtensionGauge z ≤ η / 8} from
        isClosed_le continuous_complexExtensionGauge continuous_const)
  · intro z hz
    have hz' : complexExtensionGauge z ≤ η / 8 := hz
    have hlim : Tendsto (contractPoint z) (𝓝[<] 1) (𝓝 z) := by
      have h := (continuous_contractPoint z).tendsto 1
      rw [contractPoint_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    show complexExtensionGauge (contractPoint z t) < η / 8
    rw [complexExtensionGauge_contractPoint z ht.1.le]
    calc t * complexExtensionGauge z ≤ t * (η / 8) := mul_le_mul_of_nonneg_left hz' ht.1.le
      _ < 1 * (η / 8) := mul_lt_mul_of_pos_right ht.2 (by positivity)
      _ = η / 8 := one_mul _
theorem continuous_reflectConj : Continuous reflectConj := by
  have hlast : ∀ z : Fin 4 → ℂ, reflectConj z (Fin.last 3) = starRingEnd ℂ (z 3) := fun z =>
    Fin.snoc_last (α := fun _ => ℂ) _ _
  have hcast : ∀ (z : Fin 4 → ℂ) (j : Fin 3),
      reflectConj z j.castSucc = -starRingEnd ℂ (z j.castSucc) := fun z j =>
    Fin.snoc_castSucc (α := fun _ => ℂ) _ _ j
  refine continuous_pi fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [hlast]
    exact Complex.continuous_conj.comp (continuous_apply _)
  | cast j =>
    simp only [hcast]
    exact (Complex.continuous_conj.comp (continuous_apply _)).neg
end ConePoints
theorem holds_of_coneSemigroup (hsg : ConeSemigroup.statement) : Holds := by
  intro c S σ hcone η hη _ Z x y
  obtain ⟨hcontr, -, hadj, -, -, -, hstrong, hseries, -, -, -⟩ := hsg σ hcone
  have hopen : IsOpen (complexExtensionDomain η) :=
    isOpen_lt continuous_complexExtensionGauge continuous_const
  have hsub : complexExtensionDomain η ⊆ closedComplexExtensionDomain η :=
    complexExtensionDomain_subset_closed
  have hplus : ∀ z : Fin 4 → ℂ, η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| ≤
      coneMargin (timeEighthPoint η + z) := fun z => by
    rw [coneMargin_timeEighthPoint_add]
    linarith [neg_abs_le (z 3).re]
  have hminus : ∀ z : Fin 4 → ℂ, η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| ≤
      coneMargin (timeEighthPoint η - z) := fun z => by
    rw [coneMargin_timeEighthPoint_sub]
    linarith [le_abs_self (z 3).re]
  have hgauge : ∀ z ∈ closedComplexExtensionDomain η,
      0 ≤ η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| := fun z hz => by
    have h : complexExtensionGauge z ≤ η / 8 := hz
    unfold complexExtensionGauge at h
    linarith
  have hgauge' : ∀ z ∈ complexExtensionDomain η,
      0 < η / 8 - |(z 3).re| - ∑ j : Fin 3, |(z j.castSucc).im| := fun z hz => by
    have h : |(z 3).re| + ∑ j : Fin 3, |(z j.castSucc).im| < η / 8 := hz
    linarith
  have hinplus : ∀ z ∈ closedComplexExtensionDomain η, 0 ≤ coneMargin (timeEighthPoint η + z) :=
    fun z hz => (hgauge z hz).trans (hplus z)
  have hinminus : ∀ z ∈ closedComplexExtensionDomain η, 0 ≤ coneMargin (timeEighthPoint η - z) :=
    fun z hz => (hgauge z hz).trans (hminus z)
  have hcont : ContinuousOn (σ.coneSandwich η Z x y) (closedComplexExtensionDomain η) := by
    have h₁ : ContinuousOn (fun z => star (σ.coneOp (timeEighthPoint η + z)) x)
        (closedComplexExtensionDomain η) := by
      have h : ContinuousOn
          (fun z => σ.coneOp (reflectConj (timeEighthPoint η + z)) x)
          (closedComplexExtensionDomain η) :=
        (hstrong x).comp
          (continuous_reflectConj.comp (continuous_const.add continuous_id)).continuousOn
          (fun z hz => (hadj _ (hinplus z hz)).2.1)
      exact h.congr fun z hz => by rw [(hadj _ (hinplus z hz)).2.2]
    have h₂ : ContinuousOn (fun z => σ.coneOp (timeEighthPoint η - z) y)
        (closedComplexExtensionDomain η) :=
      (hstrong y).comp (continuous_const.sub continuous_id).continuousOn
        (fun z hz => hinminus z hz)
    exact continuousOn_inner_mul_mul_apply Z x y h₁ h₂
  have hline : ∀ (p v : Fin 4 → ℂ) (ζ₀ : ℂ), 0 < coneMargin (p + ζ₀ • v) →
      DifferentiableAt ℂ (fun ζ : ℂ => σ.coneOp (p + ζ • v)) ζ₀ := by
    intro p v ζ₀ hp
    obtain ⟨A, -, hA⟩ := hseries _ hp
    exact differentiableAt_line_of_shift p v ζ₀
      (differentiableAt_line_zero_of_hasSum hp (fun w hw => (hA w hw).2) v)
  refine ⟨⟨hopen, closure_complexExtensionDomain hη, fun r => ?_, fun r => ?_⟩,
    fun z => ⟨hplus z, hminus z⟩, fun z hz => ⟨hinplus z hz, hinminus z hz, ?_⟩, hcont,
    hopen, continuousOn_pi.2 fun _ => hcont.mono hsub, fun a ha j => ?_⟩
  · simp [complexExtensionDomain, ofRealPoint]
  · simp [closedComplexExtensionDomain, complexExtensionGauge, ofRealPoint]
  · exact norm_inner_mul_mul_apply_le Z (hcontr _ (hinplus z hz)) (hcontr _ (hinminus z hz)) x y
  · have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ),
        a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j ∈
          complexExtensionDomain η := by
      have hca : ContinuousAt
          (fun ζ : ℂ => a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j)
          0 := by fun_prop
      exact hca.eventually_mem (hopen.mem_nhds (by simpa using ha))
    filter_upwards [hev] with ζ hζ
    refine differentiableAt_pi.2 fun _ => ?_
    have e₁ : (fun ζ' : ℂ => σ.coneOp (timeEighthPoint η +
          (a + ζ' • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j))) =
        fun ζ' : ℂ => σ.coneOp ((timeEighthPoint η + a) +
          ζ' • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j) := by
      funext ζ'
      rw [add_assoc]
    have e₂ : (fun ζ' : ℂ => σ.coneOp (timeEighthPoint η -
          (a + ζ' • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j))) =
        fun ζ' : ℂ => σ.coneOp ((timeEighthPoint η - a) +
          ζ' • (-YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j)) := by
      funext ζ'
      rw [smul_neg, sub_add_eq_sub_sub, sub_eq_add_neg (timeEighthPoint η - a)]
    have hp₁ : 0 < coneMargin (timeEighthPoint η +
        (a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j)) :=
      lt_of_lt_of_le (hgauge' _ hζ) (hplus _)
    have hp₂ : 0 < coneMargin (timeEighthPoint η -
        (a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j)) :=
      lt_of_lt_of_le (hgauge' _ hζ) (hminus _)
    have d₁ : DifferentiableAt ℂ (fun ζ' : ℂ => σ.coneOp (timeEighthPoint η +
        (a + ζ' • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j))) ζ := by
      rw [e₁]
      refine hline _ _ _ ?_
      rwa [← add_assoc] at hp₁
    have d₂ : DifferentiableAt ℂ (fun ζ' : ℂ => σ.coneOp (timeEighthPoint η -
        (a + ζ' • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j))) ζ := by
      rw [e₂]
      refine hline _ _ _ ?_
      rw [smul_neg, ← sub_eq_add_neg, sub_sub]
      exact hp₂
    exact differentiableAt_inner_mul_mul_apply d₁ d₂ Z x y
end YangMills.Construction.EuclideanFunctionals.ConeSandwich
