import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import YangMills.Construction.ReflectionPositivity.FormOfTransferPowerInAPicture
import YangMills.Construction.ReflectionPositivity.ReflectionsCarrierAndZeroEnergyOfTheLinkPicture
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.HilbertSpace (SesqForm)
open YangMills.Construction.JointSpectrum (CommutingFamily)
open YangMills.Construction.FormHilbert (IsPosSesqForm StrongTendsto formClass inner_formClass)
open YangMills.Construction.ReflectionPositivity.EnergyMomentum
namespace PowerOffGround
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem tendsto_apply_of_strongTendsto {A : ℕ → H →L[ℂ] H} {B : H →L[ℂ] H}
    (h : StrongTendsto A B) (v : H) : Tendsto (fun k => A k v) atTop (𝓝 (B v)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (h v)
omit [CompleteSpace H] in
theorem mul_eq_of_strongTendsto_pow {T P : H →L[ℂ] H} (h : StrongTendsto (fun k => T ^ k) P) :
    T * P = P := by
  ext v
  have h₁ := tendsto_apply_of_strongTendsto h v
  have h₂ : Tendsto (fun k => T ((T ^ k) v)) atTop (𝓝 (T (P v))) :=
    (T.continuous.tendsto _).comp h₁
  have h₃ : Tendsto (fun k => T ((T ^ k) v)) atTop (𝓝 (P v)) := by
    have h₄ := (tendsto_add_atTop_iff_nat (f := fun k => (T ^ k) v) 1).mpr h₁
    refine h₄.congr fun k => ?_
    rw [pow_succ']
    rfl
  exact tendsto_nhds_unique h₂ h₃
omit [CompleteSpace H] in
theorem pow_mul_eq_of_strongTendsto_pow {T P : H →L[ℂ] H}
    (h : StrongTendsto (fun k => T ^ k) P) (n : ℕ) : T ^ n * P = P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, mul_eq_of_strongTendsto_pow h, ih]
theorem mul_unitaryMonomial_eq {J : Type*} [Fintype J] [Nonempty J] (S : CommutingFamily H J)
    (P : H →L[ℂ] H) (h : ∀ j, P * (S.B j : H →L[ℂ] H) = P) (y : J → ℤ) :
    P * S.unitaryMonomial y = P := by
  let G : Subgroup (unitary (H →L[ℂ] H)) :=
    { carrier := {u | P * (u : H →L[ℂ] H) = P}
      mul_mem' := fun {a b} ha hb => by
        change P * ((a : H →L[ℂ] H) * (b : H →L[ℂ] H)) = P
        rw [← mul_assoc, show P * (a : H →L[ℂ] H) = P from ha, show P * (b : H →L[ℂ] H) = P from hb]
      one_mem' := mul_one P
      inv_mem' := fun {a} ha => by
        have ha' : P * (a : H →L[ℂ] H) = P := ha
        change P * ((a⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = P
        have e : (a : H →L[ℂ] H) * ((a⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 := by
          rw [← Submonoid.coe_mul, mul_inv_cancel]
          rfl
        calc P * ((a⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
            = (P * (a : H →L[ℂ] H)) * ((a⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by rw [ha']
          _ = P := by rw [mul_assoc, e, mul_one] }
  exact show Finset.univ.noncommProd (fun j => S.B j ^ y j)
      (fun j _ j' _ _ => S.commute_zpow_unitary y j j') ∈ G from
    G.toSubmonoid.noncommProd_mem _ _ _ fun j _ => G.zpow_mem (h j) (y j)
theorem unitaryMonomial_zero {J : Type*} [Fintype J] [Nonempty J] (S : CommutingFamily H J) :
    S.unitaryMonomial (fun _ => 0) = 1 := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.unitaryMonomial_zero <;> assumption
omit [CompleteSpace H] in
theorem inner_apply_add_add_inner_apply_sub (A : H →L[ℂ] H) (v w : H) :
    inner ℂ (v + w) (A (v + w)) + inner ℂ (v - w) (A (v - w)) =
      2 * inner ℂ v (A v) + 2 * inner ℂ w (A w) := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring
end Operators
theorem norm_le_sqrt_mul_sqrt_of_isPosSesqForm {V : Type*} [AddCommGroup V] [Module ℂ V]
    {b : SesqForm V} (h : IsPosSesqForm b) (F F' : V) :
    ‖b F F'‖ ≤ √(b F F).re * √(b F' F').re := by
  have e : ∀ G : V, ‖formClass b G‖ = √(b G G).re := fun G => by
    rw [@norm_eq_sqrt_re_inner ℂ, inner_formClass h]
    rfl
  calc ‖b F F'‖ = ‖inner ℂ (formClass b F) (formClass b F')‖ := by rw [inner_formClass h]
    _ ≤ ‖formClass b F‖ * ‖formClass b F'‖ := norm_inner_le_norm _ _
    _ = √(b F F).re * √(b F' F').re := by rw [e, e]
theorem expNegNatMulEnergy_at_zero (n : ℕ) : expNegNatMulEnergy n 0 = 1 := by
  simp [expNegNatMulEnergy, expNegEnergy]
theorem zero_le_expNegNatMulEnergy (n : ℕ) (E : ℝ≥0∞) : 0 ≤ expNegNatMulEnergy n E :=
  pow_nonneg (expNegEnergy E).2.1 n
theorem expNegNatMulEnergy_le_one' (n : ℕ) (E : ℝ≥0∞) : expNegNatMulEnergy n E ≤ 1 :=
  pow_le_one₀ (expNegEnergy E).2.1 (expNegEnergy E).2.2
theorem tendsto_expNegNatMulEnergy (E : ℝ≥0∞) :
    Tendsto (fun k => expNegNatMulEnergy k E) atTop (𝓝 (if E = 0 then 1 else 0)) := by
  by_cases h0 : E = 0
  · subst h0
    simp only [if_true, expNegNatMulEnergy_at_zero]
    exact tendsto_const_nhds
  · rw [if_neg h0]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (expNegEnergy E).2.1 ?_
    by_cases ht : E = ⊤
    · subst ht
      simp [expNegEnergy]
    · have hp : 0 < E.toReal := ENNReal.toReal_pos h0 ht
      have hv : ((expNegEnergy E : unitInterval) : ℝ) = Real.exp (-E.toReal) := by
        simp [expNegEnergy, ht]
      rw [hv]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
section Pair
variable (p : ReflectionPair) (c : unitPositiveClass) (μ : Fin 4)
theorem shiftMonomial_zero :
    p.shiftMonomial c μ ((0 : orthLattice μ) : Fin 4 → ℤ) = 1 :=
  unitaryMonomial_zero (p.opFamily c μ)
variable {p c μ}
theorem inner_transferOp_pow (hE : SpectralMeasures.UniqueSpectralMeasure p c μ)
    (ψ : p.Hilb c μ) (k : ℕ) :
    inner ℂ ψ ((p.transferOp c μ ^ k) ψ) =
      ((∫ x, expNegNatMulEnergy k (SpectralSpace.energy x)
        ∂p.spectralMeasure c μ ψ : ℝ) : ℂ) := by
  have h := ((hE ψ).2.1).2 k 0
  rw [shiftMonomial_zero, mul_one] at h
  rw [h, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [energyMomentumMonomial, angleDot]
theorem measurable_expNegNatMulEnergy
    (ht : Measurable fun x : SpectralSpace μ => ((expNegEnergy x.energy : unitInterval) : ℝ))
    (k : ℕ) :
    Measurable fun x : SpectralSpace μ => expNegNatMulEnergy k x.energy :=
  ht.pow_const k
theorem integrable_expNegNatMulEnergy
    (ht : Measurable fun x : SpectralSpace μ => ((expNegEnergy x.energy : unitInterval) : ℝ))
    (σ : Measure (SpectralSpace μ)) [IsFiniteMeasure σ] (k : ℕ) :
    Integrable (fun x : SpectralSpace μ => expNegNatMulEnergy k x.energy) σ :=
  Integrable.of_bound (measurable_expNegNatMulEnergy ht k).aestronglyMeasurable 1
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_expNegNatMulEnergy _ _)]
      exact expNegNatMulEnergy_le_one' _ _)
theorem inner_groundProjection (hE : SpectralMeasures.UniqueSpectralMeasure p c μ)
    (hs : StrongTendsto (fun k => p.transferOp c μ ^ k) (groundProjection μ p c))
    (ht : Measurable fun x : SpectralSpace μ => ((expNegEnergy x.energy : unitInterval) : ℝ))
    (hZ : MeasurableSet (groundSet μ)) (ψ : p.Hilb c μ) :
    inner ℂ ψ (groundProjection μ p c ψ) =
      (((p.spectralMeasure c μ ψ).real (groundSet μ) : ℝ) : ℂ) := by
  have h₁ : Tendsto (fun k => inner ℂ ψ ((p.transferOp c μ ^ k) ψ)) atTop
      (𝓝 (inner ℂ ψ (groundProjection μ p c ψ))) :=
    Tendsto.inner tendsto_const_nhds (tendsto_apply_of_strongTendsto hs ψ)
  have h₂ : Tendsto (fun k => ∫ x, expNegNatMulEnergy k (SpectralSpace.energy x)
        ∂p.spectralMeasure c μ ψ) atTop
      (𝓝 (∫ x, (groundSet μ).indicator 1 x ∂p.spectralMeasure c μ ψ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun k => (measurable_expNegNatMulEnergy ht k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_expNegNatMulEnergy _ _)]
      exact expNegNatMulEnergy_le_one' _ _
    · have h := tendsto_expNegNatMulEnergy (SpectralSpace.energy x)
      by_cases h0 : SpectralSpace.energy x = 0
      · have hx : x ∈ groundSet μ := h0
        simpa [hx, h0] using h
      · have hx : x ∉ groundSet μ := h0
        simpa [hx, h0] using h
  rw [integral_indicator_one hZ] at h₂
  have h₃ := (Complex.continuous_ofReal.tendsto _).comp h₂
  refine tendsto_nhds_unique h₁ (h₃.congr fun k => ?_)
  exact (inner_transferOp_pow hE ψ k).symm
theorem powerOffGroundForm_diag (hE : SpectralMeasures.UniqueSpectralMeasure p c μ)
    (hs : StrongTendsto (fun k => p.transferOp c μ ^ k) (groundProjection μ p c))
    (ht : Measurable fun x : SpectralSpace μ => ((expNegEnergy x.energy : unitInterval) : ℝ))
    (hZ : MeasurableSet (groundSet μ)) {n : ℕ} (hn : 1 ≤ n) (ψ : p.Hilb c μ) :
    p.powerOffGroundForm c μ n ψ ψ =
      ((∫ x, (excitedSet μ).indicator
          (fun y : SpectralSpace μ => expNegNatMulEnergy n y.energy) x
          ∂p.spectralMeasure c μ ψ : ℝ) : ℂ) := by
  have e : p.powerOffGroundForm c μ n ψ ψ =
      inner ℂ ψ ((p.transferOp c μ ^ n) ψ) - inner ℂ ψ (groundProjection μ p c ψ) := by
    unfold ReflectionPair.powerOffGroundForm
    rw [mul_sub, mul_one, pow_mul_eq_of_strongTendsto_pow hs n, sub_apply, inner_sub_right]
  have hi₂ : Integrable ((groundSet μ).indicator (1 : SpectralSpace μ → ℝ))
      (p.spectralMeasure c μ ψ) :=
    (integrable_const (1 : ℝ)).indicator hZ
  rw [e, inner_transferOp_pow hE, inner_groundProjection hE hs ht hZ, ← Complex.ofReal_sub,
    ← integral_indicator_one hZ, ← integral_sub (integrable_expNegNatMulEnergy ht _ n) hi₂]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases h0 : SpectralSpace.energy x = 0
  · have hx : x ∈ groundSet μ := h0
    have hx' : x ∉ excitedSet μ := fun h => h.1.ne' h0
    simp [hx, hx', h0, expNegNatMulEnergy_at_zero]
  · have hx : x ∉ groundSet μ := h0
    by_cases h1 : SpectralSpace.energy x = ⊤
    · have hx' : x ∉ excitedSet μ := fun h => h.2.ne h1
      simp [hx, hx', h1, expNegNatMulEnergy_top hn]
    · have hx' : x ∈ excitedSet μ :=
        ⟨pos_iff_ne_zero.mpr h0, lt_top_iff_ne_top.mpr h1⟩
      simp [hx, hx']
end Pair
theorem holds_of_spectral (p : ReflectionPair) (c : unitPositiveClass) (μ : Fin 4) (n : ℕ)
    (hn : 1 ≤ n) (hV : SpectralMeasures.SpectralSpaceProps μ)
    (hE : SpectralMeasures.UniqueSpectralMeasure p c μ)
    (hI : SpectralMeasures.TranslationInvariance p c μ)
    (hs : StrongTendsto (fun k => p.transferOp c μ ^ k) (groundProjection μ p c))
    (hU : ∀ l, groundProjection μ p c * p.shiftOp c μ l = groundProjection μ p c) :
    GroundAndDiagonal p c μ n ∧ GroundSplits p c μ n ∧
      IsPosConjSymmForm p c μ n ∧ TransverseInvariance p c μ n := by
  obtain ⟨-, -, -, -, -, -, -, -, ht, hen, -⟩ := hV
  have hZ : MeasurableSet (groundSet μ) := hen (measurableSet_singleton 0)
  have hP : MeasurableSet (excitedSet μ) :=
    hen (measurableSet_Ioo (a := (0 : ℝ≥0∞)) (b := ⊤))
  have hdiag := fun ψ : p.Hilb c μ => powerOffGroundForm_diag hE hs ht hZ hn ψ
  have hpos : (p.powerOffGroundForm c μ n).IsNonnegDiag := fun ψ => by
    rw [hdiag ψ]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact integral_nonneg fun x => indicator_nonneg (fun y _ => zero_le_expNegNatMulEnergy _ _) x
  have hform : IsPosSesqForm (p.powerOffGroundForm c μ n) :=
    { sesq :=
        { add_left := fun _ _ _ => inner_add_left _ _ _
          smul_left := fun _ _ _ => inner_smul_left _ _ _
          add_right := fun F F₁ F₂ => by
            unfold ReflectionPair.powerOffGroundForm
            rw [map_add, inner_add_right]
          smul_right := fun a F F' => by
            unfold ReflectionPair.powerOffGroundForm
            rw [map_smul, inner_smul_right] }
      nonneg := hpos }
  refine ⟨⟨fun a b ψ ψ' => by simp only [map_add, map_smul],
      fun ψ => ⟨inner_groundProjection hE hs ht hZ ψ, hdiag ψ⟩⟩,
    ⟨pow_mul_eq_of_strongTendsto_pow hs n, ?_, fun w => ?_⟩,
    ⟨hform, hform.isConjSymm, fun ψ ψ' => ⟨norm_le_sqrt_mul_sqrt_of_isPosSesqForm hform ψ ψ', ?_⟩⟩,
    fun w ψ => ?_⟩
  · rw [mul_sub, mul_one, pow_mul_eq_of_strongTendsto_pow hs n, add_sub_cancel]
  · exact mul_unitaryMonomial_eq (p.opFamily c μ) _ hU _
  · have e := inner_apply_add_add_inner_apply_sub
      (p.transferOp c μ ^ n * (1 - groundProjection μ p c)) ψ ψ'
    have e' := congrArg Complex.re e
    have h₀ := (hpos (ψ - ψ')).2
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero] at e'
    unfold ReflectionPair.powerOffGroundForm at h₀ ⊢
    linarith
  · rw [hdiag, hdiag, hI ψ w]
end PowerOffGround
theorem powerOffGround_holds (hM : SpectralMeasuresTheorem)
    (hS : SiteReflectionPair.Conclusion)
    (hL : LinkPictureReflectionsConeGround) :
    PowerOffGround.Holds := by
  intro c μ n hn
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun p => ?_⟩
  obtain ⟨hV, -, hp⟩ := hM μ
  obtain ⟨-, hE, -, -, -, -, -, -, hI⟩ := hp c p
  cases p with
  | link =>
    obtain ⟨-, -, -, hs, hU⟩ := hL c μ
    exact PowerOffGround.holds_of_spectral _ c μ n hn hV hE hI hs
      fun l => (hU l).2
  | site =>
    obtain ⟨-, hC, -⟩ := hS c μ 1
    obtain ⟨-, -, hU, -, hs⟩ := hC
    exact PowerOffGround.holds_of_spectral _ c μ n hn hV hE hI hs
      fun l => (hU l).2
end YangMills.Construction.ReflectionPositivity.DirectionPictures
