import YangMills.Construction.OneLoopLaw.DecayOfTheKernelsOfASymbolProof
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.OneLoopLaw.KernelsOfATemperingChoice
import YangMills.Construction.OneLoopLaw.PeriodicityAndGaugeRelationOfASymbol
import YangMills.Construction.OneLoopLaw.PolarisationOfAMember
import YangMills.Construction.OneLoopLaw.PolarisationOfBondFormsOnATorus
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TemperedKernels
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.InfiniteLattice (AmbientSpace)
private def phaseAt (u : Fin 4 → ℤ) (κ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (Complex.I * bilinDot κ (toComplexVec (castVec u)))
private theorem continuous_phaseAt (u : Fin 4 → ℤ) : Continuous (phaseAt u) := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolKernelDecay.continuous_planeWave <;> assumption
private theorem differentiable_phaseAt_line (u : Fin 4 → ℤ) (a v : Fin 4 → ℂ) :
    Differentiable ℂ fun ζ : ℂ => phaseAt u (a + ζ • v) := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolKernelDecay.differentiable_planeWave_affine <;> assumption
private theorem norm_phaseAt_real (u : Fin 4 → ℤ) (p : AmbientSpace) :
    ‖phaseAt u (toComplexVec p)‖ = 1 := by
  have h : Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec u)) =
      ((∑ μ, p μ * (u μ : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp only [bilinDot, toComplexVec, castVec]
    push_cast
    rw [mul_comm]
  rw [phaseAt, h, Complex.norm_exp_ofReal_mul_I]
private theorem norm_phaseAt_le (u : Fin 4 → ℤ) {σ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip σ) :
    ‖phaseAt u κ‖ ≤ Real.exp (σ * ∑ μ, |(u μ : ℝ)|) := by
  rw [phaseAt, Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h : (Complex.I * bilinDot κ (toComplexVec (castVec u))).re =
      -∑ μ, (κ μ).im * (u μ : ℝ) := by
    simp [bilinDot, toComplexVec, castVec, Complex.mul_re, Complex.mul_im]
  rw [h]
  calc -∑ μ, (κ μ).im * (u μ : ℝ) ≤ |∑ μ, (κ μ).im * (u μ : ℝ)| := neg_le_abs _
    _ ≤ ∑ μ, |(κ μ).im * (u μ : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ μ, σ * |(u μ : ℝ)| := Finset.sum_le_sum fun μ _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hκ μ) (abs_nonneg _)
    _ = σ * ∑ μ, |(u μ : ℝ)| := (Finset.mul_sum _ _ _).symm
private theorem phaseAt_add_period (u : Fin 4 → ℤ) (κ : Fin 4 → ℂ) {p : AmbientSpace}
    (hp : p ∈ periodLattice) :
    phaseAt u (κ + toComplexVec p) = phaseAt u κ := by
  obtain ⟨t, ht⟩ := hp
  have h : Complex.I * bilinDot (κ + toComplexVec p) (toComplexVec (castVec u)) =
      Complex.I * bilinDot κ (toComplexVec (castVec u)) +
        ((∑ μ, t μ * u μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [bilinDot, toComplexVec, castVec, Pi.add_apply, ht, Fin.sum_univ_four]
    push_cast
    ring
  rw [phaseAt, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rfl
private theorem eventually_atTop_of_sides {L : ℕ} (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) : ∀ᶠ n in atTop, P n := by
  obtain ⟨s₀, ⟨m, hm, rfl⟩, hs⟩ := h
  refine eventually_atTop.2 ⟨m, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le hm hn
  refine hs (PeriodicLattice.torusSide L n) ⟨n, hn0, rfl⟩ ?_ n hn0 rfl
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h2 := pow_le_pow_right₀ h1 hn
  unfold PeriodicLattice.torusSide
  linarith
abbrev _root_.YangMills.SharedProofs.p110886 := @eventually_atTop_of_sides
private theorem riemannError_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun s : ℕ => (1 + 2 * (Real.exp (σ * s) - 1)⁻¹) ^ 4 - 1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℕ => Real.exp (σ * s) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1)
      (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hσ))
  have h2 := ((tendsto_inv_atTop_zero.comp h1).const_mul 2).const_add 1
  have h3 := (h2.pow 4).sub_const 1
  simpa using h3
private theorem twoMulPow_tendsto_atTop {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (fun n : ℕ => 2 * L ^ n) atTop atTop :=
  tendsto_atTop_mono (fun n => by
    have : n < L ^ n := Nat.lt_pow_self (by omega)
    show n ≤ 2 * L ^ n
    omega) tendsto_id
private theorem normalizedClassSum_tendsto (hR : Claim) {L : ℕ}
    (hL : 2 ≤ L) {σ : ℝ} (hσ : 0 < σ) {g : (Fin 4 → ℂ) → ℂ} (h₁ : HolomorphicNearStrip σ g)
    (h₂ : PeriodicOnStrip σ g) (h₃ : BoundedOnStrip σ g) :
    Tendsto (fun n : ℕ => (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ * classSum (2 * L ^ n) g)
      atTop (𝓝 (torusAverage fun κ => g (toComplexVec κ))) := by
  have hr := (riemannError_tendsto_zero hσ).comp (twoMulPow_tendsto_atTop hL)
  have hb := hr.const_mul (stripSup σ g)
  rw [mul_zero] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hb
  have hpos : 0 < 2 * L ^ n := Nat.mul_pos two_pos (pow_pos (by omega) n)
  exact (hR (2 * L ^ n) σ g hpos hσ h₁ h₂ h₃).1
private theorem torusAverage_one : (torusAverage fun _ => (1 : ℂ)) = 1 := by
  unfold torusAverage
  rw [MeasureTheory.setIntegral_const]
  have hv : (MeasureTheory.volume.real (Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi))) =
      (2 * Real.pi) ^ 4 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [hv]
  have h0 : ((2 * Real.pi) ^ 4 : ℝ) ≠ 0 := by positivity
  simp only [Complex.real_smul, mul_one]
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ h0, Complex.ofReal_one]
private theorem holomorphicNearStrip_one (σ : ℝ) : HolomorphicNearStrip σ fun _ => (1 : ℂ) :=
  ⟨univ, subset_univ _, isOpen_univ, continuousOn_const, fun _ _ _ =>
    Eventually.of_forall fun _ => differentiableAt_const _⟩
private theorem phased_hypotheses {σ : ℝ} {g : (Fin 4 → ℂ) → ℂ} (u : Fin 4 → ℤ)
    (hO : ∃ O : Set (Fin 4 → ℂ), imStrip σ ⊆ O ∧
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O (fun κ _ => g κ) ∧
        ∃ C : ℝ, ∀ κ ∈ O, ‖g κ‖ ≤ C)
    (hper : PeriodicOnStrip σ g) :
    HolomorphicNearStrip σ (fun κ => g κ * phaseAt u κ) ∧
      PeriodicOnStrip σ (fun κ => g κ * phaseAt u κ) ∧
        BoundedOnStrip σ (fun κ => g κ * phaseAt u κ) := by
  obtain ⟨O, hsub, hol, C, hC⟩ := hO
  refine ⟨⟨O, hsub, hol.1, ?_, ?_⟩, ?_, ?_⟩
  · have hc : ContinuousOn g O := (continuous_apply (0 : Fin 1)).comp_continuousOn hol.2.1
    exact continuousOn_pi.2 fun _ => hc.mul (continuous_phaseAt u).continuousOn
  · intro a ha j
    filter_upwards [hol.2.2 a ha j] with ζ h
    refine differentiableAt_pi.2 fun _ => ?_
    exact (differentiableAt_pi.1 h 0).mul (differentiable_phaseAt_line u a _ ζ)
  · intro κ hκ p hp
    simp only
    rw [hper κ hκ p hp, phaseAt_add_period u κ hp]
  · refine ⟨C * Real.exp (σ * ∑ μ, |(u μ : ℝ)|), fun κ hκ => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC κ (hsub hκ)) (norm_phaseAt_le u hκ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (hsub hκ)))
private theorem norm_sub_weighted_sums_le {ι : Type*} [Finite ι] (c₀ : ℂ) (ph V T : ι → ℂ)
    {ε : ℝ} (hph : ∀ i, ‖ph i‖ = 1) (h : ∀ i, ‖V i - T i‖ ≤ ε) :
    ‖c₀ * ∑ᶠ i, ph i * V i - c₀ * ∑ᶠ i, ph i * T i‖ ≤ ‖c₀ * ∑ᶠ _ : ι, (1 : ℂ)‖ * ε := by
  have : Fintype ι := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← mul_sub,
    ← Finset.sum_sub_distrib, norm_mul, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hcard : ‖∑ _ : ι, (1 : ℂ)‖ = Fintype.card ι := by simp
  rw [hcard]
  calc ‖∑ i, (ph i * V i - ph i * T i)‖ ≤ ∑ i, ‖ph i * V i - ph i * T i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, ε := Finset.sum_le_sum fun i _ => by
        rw [← mul_sub, norm_mul, hph, one_mul]
        exact h i
    _ = Fintype.card ι * ε := by simp
private theorem kernelsTendTo_of_witness (hPer : SymbolPeriodicity.PeriodicityAndWardClaim)
    (hBonds : BondFormHessianOnTorus.PlaneWaveExpansion)
    (hR : Claim) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L} {δ : ℝ} {π : SymbolArray}
    {e : ℕ → ℝ} (hF : IsLatticeFunctional L F) (c : IsTemperedWitness L F δ π e) :
    KernelsTendTo L F π := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  intro x y a a'
  obtain ⟨G₁, G₂, G₃⟩ : _ ∧ _ ∧ _ := phased_hypotheses (y.1 - x.1)
    (by
      obtain ⟨O, hO, hh⟩ := c.analytic
      exact ⟨O, hO, (hh x.2 y.2).1, (hh x.2 y.2).2⟩)
    ((hPer L hL F δ π e hF c).1 x.2 y.2)
  have lim := normalizedClassSum_tendsto hR hL2 c.delta_pos G₁ G₂ G₃
  have one := normalizedClassSum_tendsto hR hL2 c.delta_pos (holomorphicNearStrip_one δ)
    (fun _ _ _ _ => rfl) ⟨1, fun _ _ => by simp⟩
  rw [torusAverage_one] at one
  set A : ℕ → ℂ := fun n => (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ *
    classSum (2 * L ^ n) fun _ => 1 with hA
  set R : ℕ → ℂ := fun n => if a = a' then (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ *
    classSum (2 * L ^ n) (fun κ => π x.2 y.2 κ * phaseAt (y.1 - x.1) κ) else 0 with hRdef
  have hAe : Tendsto (fun n => ‖A n‖ * e n) atTop (𝓝 0) := by
    simpa using one.norm.mul c.err_tendsto
  have ev : ∀ᶠ n in atTop,
      ‖complexHessian F n (FunctionalStiffness.liftedPauliForm L n a x)
        (FunctionalStiffness.liftedPauliForm L n a' y) - R n‖ ≤ ‖A n‖ * e n := by
    filter_upwards [eventually_atTop_of_sides hL2 hF, eventually_atTop_of_sides hL2 c.approx,
      eventually_gt_atTop 0, one.eventually_ne one_ne_zero] with n hmem hbd hn hAne
    have hfin : Finite (DualClasses (2 * L ^ n)) := by
      by_contra hinf
      rw [not_finite_iff_infinite] at hinf
      apply hAne
      simp only [hA, classSum]
      rw [finsum_of_infinite_support (by simpa [Function.support_const] using Set.infinite_univ),
        mul_zero]
    have hc₀ : (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) =
        (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ := by
      simp only [PeriodicLattice.torusSide]
      push_cast
      rw [inv_pow]
    have hb := (hBonds L n hL hn F hmem).2 x y a a'
    have key := norm_sub_weighted_sums_le (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ)
      (fun k : DualClasses (2 * L ^ n) =>
        phaseAt (y.1 - x.1) (toComplexVec (Quotient.out k : dualLattice (2 * L ^ n))))
      (fun k => (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
        complexHessian F n (fourierModeForm L n a (Quotient.out k : dualLattice (2 * L ^ n)) x.2)
          (fourierModeForm L n a' (-(Quotient.out k : dualLattice (2 * L ^ n)) : AmbientSpace) y.2))
      (fun k => if a = a' then
        π x.2 y.2 (toComplexVec (Quotient.out k : dualLattice (2 * L ^ n))) else 0)
      (fun k => norm_phaseAt_real _ _)
      (fun k => hbd _ (Quotient.out k : dualLattice (2 * L ^ n)).2 a a' x.2 y.2)
    have hRn : R n = (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
        ∑ᶠ k : DualClasses (2 * L ^ n),
          phaseAt (y.1 - x.1) (toComplexVec (Quotient.out k : dualLattice (2 * L ^ n))) *
            (if a = a' then
              π x.2 y.2 (toComplexVec (Quotient.out k : dualLattice (2 * L ^ n))) else 0) := by
      by_cases haa : a = a'
      · simp only [hRdef, if_pos haa, hc₀, classSum]
        congr 1
        exact finsum_congr fun k => mul_comm _ _
      · simp [hRdef, if_neg haa]
    have hAn : A n = (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
        ∑ᶠ _ : DualClasses (2 * L ^ n), (1 : ℂ) := by
      simp only [hA, hc₀, classSum]
    rw [hb, hRn, hAn]
    exact key
  have hdiff := squeeze_zero_norm' ev hAe
  have hRlim : Tendsto R atTop
      (𝓝 (if a = a' then symbolKernel (π x.2 y.2) (y.1 - x.1) else 0)) := by
    by_cases haa : a = a'
    · simp only [hRdef, if_pos haa]
      exact lim
    · simp only [hRdef, if_neg haa]
      exact tendsto_const_nhds
  have hsum := hdiff.add hRlim
  simpa using hsum
private theorem liftedPauliForm_mem {L n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (a : Fin 3) (q : EffectiveAction.IntBond) :
    FunctionalStiffness.liftedPauliForm L n a q ∈ edgeFormSpace L n 0 0 := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hx : ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by show -(n : ℤ) < (0 : ℤ) - (0 : ℤ); omega) b
  classical
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [FunctionalStiffness.liftedPauliForm, FunctionalStiffness.pauliEdgeForm,
      extendOddly, if_pos hb]
    split_ifs
    · exact Matrices.PowerExpCharts.pauliFamily_mem_hermitianTraceless a
    · exact zero_mem _
  · simp only [FunctionalStiffness.liftedPauliForm, FunctionalStiffness.pauliEdgeForm,
      extendOddly]
    rcases hx b with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · rw [if_neg hr, if_pos hb, show b.opposite.opposite = b from rfl]
    · rw [if_pos hr, if_neg hb, neg_neg]
theorem kernelLimitAndReality_proof (hPer : SymbolPeriodicity.PeriodicityAndWardClaim)
    (hMember : ComplexHessianOfMember.Statement)
    (hBonds : BondFormHessianOnTorus.PlaneWaveExpansion)
    (hR : Claim) : KernelLimitAndReality := by
  intro L hL F δ π e hF c
  have conv := kernelsTendTo_of_witness hPer hBonds hR hL hF c
  refine ⟨conv, fun μ ν u => ?_⟩
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have h := conv (0, μ) (u, ν) 0 0
  simp only [if_true, sub_zero] at h
  have him := (Complex.continuous_im.tendsto _).comp h
  refine tendsto_nhds_unique him (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_atTop_of_sides hL2 hF, eventually_gt_atTop 0] with n hmem hn
  have facts := hMember L n hL hn F hmem
  simp only [Function.comp]
  rw [facts.ofReal _ (liftedPauliForm_mem hL hn 0 _) _ (liftedPauliForm_mem hL hn 0 _),
    Complex.ofReal_im]
end YangMills.Construction.OneLoopLaw.TemperedKernels
end
