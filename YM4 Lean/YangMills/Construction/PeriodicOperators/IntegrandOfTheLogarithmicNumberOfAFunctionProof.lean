import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumberProof
import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunction
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStripProof
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDensityBounds
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Coordinates (ComplexCoordinates)
open YangMills.Construction.Coordinates.ComplexCoordinates (stdBasisVector)
open YangMills.Construction.PeriodicOperators.JetQuad (logDensity)
section CoordLines
variable {N : ℕ}
def coordLine (O : Set (ComplexCoordinates N)) (a : ComplexCoordinates N) (j : Fin N) : Set ℂ :=
  {ζ | a + ζ • stdBasisVector j ∈ O}
theorem isOpen_coordLine {O : Set (ComplexCoordinates N)} (hO : IsOpen O) (a : ComplexCoordinates N)
    (j : Fin N) : IsOpen (coordLine O a j) :=
  hO.preimage (by fun_prop)
theorem differentiableOn_coordLine {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z) (a : ComplexCoordinates N)
    (j : Fin N) : DifferentiableOn ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) (coordLine O a j) := by
  intro ζ₀ hζ₀
  have h0 := (h.2.2 _ hζ₀ j).self_of_nhds
  have h1 : DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ₀ • stdBasisVector j + ζ • stdBasisVector j)) 0 :=
    differentiableAt_pi.1 h0 0
  have h2 : DifferentiableAt ℂ
      ((fun ζ : ℂ => g (a + ζ₀ • stdBasisVector j + ζ • stdBasisVector j)) ∘ fun ζ : ℂ => ζ - ζ₀) ζ₀ := by
    refine DifferentiableAt.comp ζ₀ (by simpa using h1) (by fun_prop)
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)).differentiableWithinAt
  simp only [Function.comp]
  congr 1
  rw [add_assoc, ← add_smul]
  simp
theorem isHolomorphicIn_of_coordLine {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ}
    (hO : IsOpen O) (hc : ContinuousOn g O)
    (hl : ∀ a j, DifferentiableOn ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) (coordLine O a j)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by
  refine ⟨hO, continuousOn_pi.2 fun _ => hc, fun a ha j => ?_⟩
  have hmem : coordLine O a j ∈ 𝓝 (0 : ℂ) :=
    (isOpen_coordLine hO a j).mem_nhds (by simpa [coordLine] using ha)
  have := (isOpen_coordLine hO a j).eventually_mem (x := 0) (by simpa [coordLine] using ha)
  filter_upwards [eventually_eventually_nhds.2 (Filter.mem_of_superset hmem fun _ h => h)] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) ζ :=
    (hl a j).differentiableAt hζ
  exact differentiableAt_pi.2 fun _ => hd
end CoordLines
section SetIntegrals
variable {N : ℕ}
theorem norm_stdBasisVector (j : Fin N) : ‖(stdBasisVector j : ComplexCoordinates N)‖ = 1 := by
  classical
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
  · by_cases h : i = j
    · subst h; simp [stdBasisVector]
    · simp [stdBasisVector, Pi.single_eq_of_ne h]
  · have := norm_le_pi_norm (stdBasisVector j : ComplexCoordinates N) j
    simpa [stdBasisVector] using this
variable {C : Set AmbientSpace} {O : Set (ComplexCoordinates N)} {Φ : AmbientSpace → ComplexCoordinates N → ℂ}
theorem exists_bound_near (hC : IsCompact C) (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    {p₀ : ComplexCoordinates N} (hp₀ : p₀ ∈ O) :
    ∃ r M : ℝ, 0 < r ∧ Metric.closedBall p₀ (2 * r) ⊆ O ∧
      ∀ x ∈ C, ∀ p ∈ Metric.closedBall p₀ (2 * r), ‖Φ x p‖ ≤ M := by
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hp₀)
  have hK : IsCompact (C ×ˢ Metric.closedBall p₀ ε) := hC.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono_right hball))
  refine ⟨ε / 2, M, by positivity, ?_, fun x hx p hp => hM (x, p) ⟨hx, ?_⟩⟩
  · rwa [mul_div_cancel₀ _ (two_ne_zero)]
  · rwa [mul_div_cancel₀ _ (two_ne_zero)] at hp
theorem aestronglyMeasurable_slice (hCm : MeasurableSet C)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    {p : ComplexCoordinates N} (hp : p ∈ O) :
    AEStronglyMeasurable (fun x => Φ x p) (volume.restrict C) := by
  have : ContinuousOn (fun x => Φ x p) C :=
    hc.comp (f := fun x => (x, p)) (by fun_prop) fun x hx => ⟨hx, hp⟩
  exact this.aestronglyMeasurable hCm
theorem integrableOn_slice (hC : IsCompact C)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    {p : ComplexCoordinates N} (hp : p ∈ O) :
    IntegrableOn (fun x => Φ x p) C volume := by
  have : ContinuousOn (fun x => Φ x p) C :=
    hc.comp (f := fun x => (x, p)) (by fun_prop) fun x hx => ⟨hx, hp⟩
  exact this.integrableOn_compact hC
theorem continuousOn_setIntegral_slice (hC : IsCompact C) (hCm : MeasurableSet C) (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O)) :
    ContinuousOn (fun p => ∫ x in C, Φ x p) O := by
  intro p₀ hp₀
  obtain ⟨r, M, hr, hsub, hM⟩ := exists_bound_near hC hO hc hp₀
  have hnear : Metric.closedBall p₀ (2 * r) ∈ 𝓝 p₀ :=
    Metric.closedBall_mem_nhds _ (by positivity)
  have hfin : IsFiniteMeasure (volume.restrict C) :=
    ⟨by simpa using hC.measure_lt_top⟩
  refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_)
  · filter_upwards [hnear] with p hp using aestronglyMeasurable_slice hCm hc (hsub hp)
  · filter_upwards [hnear] with p hp
    exact (ae_restrict_iff' hCm).2 (Eventually.of_forall fun x hx => hM x hx p hp)
  · exact integrable_const _
  · refine (ae_restrict_iff' hCm).2 (Eventually.of_forall fun x hx => ?_)
    have : ContinuousOn (fun p => Φ x p) O :=
      hc.comp (f := fun p => (x, p)) (by fun_prop) fun p hp => ⟨hx, hp⟩
    exact this.continuousAt (hO.mem_nhds hp₀)
theorem differentiableAt_setIntegral_coordLine (hC : IsCompact C) (hCm : MeasurableSet C)
    (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    (hl : ∀ x ∈ C, ∀ a j,
      DifferentiableOn ℂ (fun ζ : ℂ => Φ x (a + ζ • stdBasisVector j)) (coordLine O a j))
    {p₁ : ComplexCoordinates N} (hp₁ : p₁ ∈ O) (j : Fin N) :
    DifferentiableAt ℂ (fun ζ : ℂ => ∫ x in C, Φ x (p₁ + ζ • stdBasisVector j)) 0 := by
  obtain ⟨r, M, hr, hsub, hM⟩ := exists_bound_near hC hO hc hp₁
  have hfin : IsFiniteMeasure (volume.restrict C) :=
    ⟨by simpa using hC.measure_lt_top⟩
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * r → p₁ + ζ • stdBasisVector j ∈ Metric.closedBall p₁ (2 * r) := by
    intro ζ hζ
    simpa [dist_eq_norm, norm_smul, norm_stdBasisVector] using hζ
  have hline : ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * r → ζ ∈ coordLine O p₁ j := fun ζ hζ => hsub (hin ζ hζ)
  have hdiff : ∀ x ∈ C, ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * r →
      DifferentiableAt ℂ (fun ζ : ℂ => Φ x (p₁ + ζ • stdBasisVector j)) ζ := fun x hx ζ hζ =>
    (hl x hx p₁ j).differentiableAt ((isOpen_coordLine hO p₁ j).mem_nhds (hline ζ hζ))
  have hbound : ∀ x ∈ C, ∀ ζ ∈ Metric.ball (0 : ℂ) r,
      ‖deriv (fun ζ : ℂ => Φ x (p₁ + ζ • stdBasisVector j)) ζ‖ ≤ M / r := by
    intro x hx ζ hζ
    have hζ' : ‖ζ‖ < r := by simpa using hζ
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · have hD : DifferentiableOn ℂ (fun ζ : ℂ => Φ x (p₁ + ζ • stdBasisVector j))
          (Metric.closedBall ζ r) := by
        intro w hw
        refine (hdiff x hx w ?_).differentiableWithinAt
        have : ‖w - ζ‖ ≤ r := by simpa [dist_eq_norm] using hw
        calc ‖w‖ = ‖(w - ζ) + ζ‖ := by simp
          _ ≤ ‖w - ζ‖ + ‖ζ‖ := norm_add_le _ _
          _ ≤ 2 * r := by linarith
      exact hD.diffContOnCl_ball subset_rfl
    · intro w hw
      refine hM x hx _ (hin w ?_)
      have : ‖w - ζ‖ = r := by simpa [dist_eq_norm] using hw
      calc ‖w‖ = ‖(w - ζ) + ζ‖ := by simp
        _ ≤ ‖w - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ ≤ 2 * r := by linarith
  have hmeas : AEStronglyMeasurable
      (fun x => deriv (fun ζ : ℂ => Φ x (p₁ + ζ • stdBasisVector j)) 0) (volume.restrict C) := by
    let t : ℕ → ℂ := fun n => ((r / (n + 2) : ℝ) : ℂ)
    have ht0 : ∀ n, t n ≠ 0 := fun n => by
      have : (r / ((n : ℝ) + 2)) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.2 this
    have htn : ∀ n, ‖t n‖ ≤ 2 * r := fun n => by
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have : r / ((n : ℝ) + 2) ≤ r := div_le_self hr.le (by linarith)
      simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr h2)]
      linarith
    have ht : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall ht0⟩
      have h1 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [t, Function.comp_def] using h2
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) x => (t n)⁻¹ • (Φ x (p₁ + t n • stdBasisVector j) -
        Φ x (p₁ + (0 : ℂ) • stdBasisVector j)))
      (fun n => ?_) ?_
    · exact ((aestronglyMeasurable_slice hCm hc (hsub (hin _ (htn n)))).sub
        (aestronglyMeasurable_slice hCm hc (hsub (hin 0 (by simp; positivity))))).fun_const_smul _
    · refine (ae_restrict_iff' hCm).2 (Eventually.of_forall fun x hx => ?_)
      have hd := (hdiff x hx 0 (by simp; positivity)).hasDerivAt
      have := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp ht
      simpa [Function.comp_def] using this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict C) (𝕜 := ℂ) (x₀ := (0 : ℂ)) (s := Metric.ball (0 : ℂ) r)
    (F := fun ζ x => Φ x (p₁ + ζ • stdBasisVector j))
    (F' := fun ζ x => deriv (fun ζ : ℂ => Φ x (p₁ + ζ • stdBasisVector j)) ζ)
    (bound := fun _ => M / r)
    (Metric.ball_mem_nhds _ hr) ?_ ?_ hmeas ?_ (integrable_const _) ?_
  · exact key.2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with ζ hζ
    have : ‖ζ‖ < r := by simpa using hζ
    exact aestronglyMeasurable_slice hCm hc (hsub (hin ζ (by linarith)))
  · exact integrableOn_slice hC hc (hsub (hin 0 (by simp; positivity)))
  · exact (ae_restrict_iff' hCm).2 (Eventually.of_forall fun x hx ζ hζ => hbound x hx ζ hζ)
  · refine (ae_restrict_iff' hCm).2 (Eventually.of_forall fun x hx ζ hζ => ?_)
    have : ‖ζ‖ < r := by simpa using hζ
    exact (hdiff x hx ζ (by linarith)).hasDerivAt
theorem differentiableOn_setIntegral_coordLine (hC : IsCompact C) (hCm : MeasurableSet C)
    (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    (hl : ∀ x ∈ C, ∀ a j,
      DifferentiableOn ℂ (fun ζ : ℂ => Φ x (a + ζ • stdBasisVector j)) (coordLine O a j))
    (a : ComplexCoordinates N) (j : Fin N) :
    DifferentiableOn ℂ (fun ζ : ℂ => ∫ x in C, Φ x (a + ζ • stdBasisVector j)) (coordLine O a j) := by
  intro ζ₀ hζ₀
  have h1 := differentiableAt_setIntegral_coordLine hC hCm hO hc hl hζ₀ j
  have h2 : DifferentiableAt ℂ
      ((fun ζ : ℂ => ∫ x in C, Φ x (a + ζ₀ • stdBasisVector j + ζ • stdBasisVector j)) ∘
        fun ζ : ℂ => ζ - ζ₀) ζ₀ :=
    DifferentiableAt.comp ζ₀ (by simpa using h1) (by fun_prop)
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)).differentiableWithinAt
  simp only [Function.comp]
  congr 2
  funext x
  congr 1
  rw [add_assoc, ← add_smul]
  simp
end SetIntegrals
section MatrixEntries
variable {J J' J'' : Type}
theorem linearMapEntry_eq_apply [DecidableEq J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (c' : J') (c : J) :
    linearMapEntry M c' c = M (Pi.single c 1) c' := by
  unfold linearMapEntry
  congr!
theorem linearMap_ext_entry [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : ∀ c' c, linearMapEntry M c' c = linearMapEntry M' c' c) : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.linearMap_ext_of_entry <;> assumption
open Classical in
def stdUnit (c : J) : J → ℂ := Pi.single c 1
theorem eq_sum_stdUnit [Fintype J] (ε : J → ℂ) : ε = ∑ c, ε c • stdUnit c := by
  classical
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [stdUnit]
  · intro c _ hc
    simp [stdUnit, Pi.single_eq_of_ne hc.symm]
  · simp
theorem linearMap_apply_eq_sum [Fintype J] (L : (J → ℂ) →ₗ[ℂ] ℂ) (ε : J → ℂ) :
    L ε = ∑ c, ε c * L (stdUnit c) := by
  conv_lhs => rw [eq_sum_stdUnit ε]
  simp [map_sum]
theorem linearMapEntry_sum_smul {K : Type} (s : Finset K) (a : K → ℂ)
    (M : K → (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (c' : J') (c : J) :
    linearMapEntry (∑ k ∈ s, a k • M k) c' c = ∑ k ∈ s, a k * linearMapEntry (M k) c' c := by
  simp [linearMapEntry, LinearMap.sum_apply, Finset.sum_apply]
theorem linearMapEntry_comp [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (N : (J'' → ℂ) →ₗ[ℂ] (J → ℂ))
    (c' : J') (c : J'') :
    linearMapEntry (M.comp N) c' c = ∑ k, linearMapEntry M c' k * linearMapEntry N k c := by
  classical
  simp only [linearMapEntry_eq_apply, LinearMap.comp_apply]
  have h : N (Pi.single c 1) = ∑ k, (N (Pi.single c 1) k) • (Pi.single k (1 : ℂ) : J → ℂ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  simp [map_sum, Finset.sum_apply, mul_comm]
theorem trace_eq_sum_linearMapEntry [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) M = ∑ i, linearMapEntry M i i := by apply _root_.YangMills.SharedProofs.p9894 <;> assumption
def densityTrace (b x y b' z : Module.End ℂ (J → ℂ)) : ℂ :=
  LinearMap.trace ℂ (J → ℂ) (b * x - b * (y * (b' * z)))
theorem densityTrace_eq_sum [Fintype J] (b x y b' z : Module.End ℂ (J → ℂ)) :
    densityTrace b x y b' z = ∑ i, ((∑ k, linearMapEntry b i k * linearMapEntry x k i) -
      ∑ k, linearMapEntry b i k * ∑ l, linearMapEntry y k l *
        ∑ m, linearMapEntry b' l m * linearMapEntry z m i) := by
  unfold densityTrace
  rw [trace_eq_sum_linearMapEntry]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : ∀ M N : Module.End ℂ (J → ℂ), linearMapEntry (M - N) i i =
      linearMapEntry M i i - linearMapEntry N i i := fun M N => by simp [linearMapEntry]
  rw [hsub]
  congr 1
  · exact linearMapEntry_comp b x i i
  · refine (linearMapEntry_comp b _ i i).trans (Finset.sum_congr rfl fun k _ => ?_)
    congr 1
    refine (linearMapEntry_comp y _ k i).trans (Finset.sum_congr rfl fun l _ => ?_)
    congr 1
    exact linearMapEntry_comp b' z l i
theorem densityTrace_conj [Fintype J] {u u' : Module.End ℂ (J → ℂ)} (h₁ : u * u' = 1)
    (b x y b' z : Module.End ℂ (J → ℂ)) :
    densityTrace (u' * b * u) (u' * x * u) (u' * y * u) (u' * b' * u) (u' * z * u) =
      densityTrace b x y b' z := by
  have hc : ∀ w, u * (u' * w) = w := fun w => by rw [← mul_assoc, h₁, one_mul]
  unfold densityTrace
  have e : u' * b * u * (u' * x * u) - u' * b * u * (u' * y * u * (u' * b' * u * (u' * z * u))) =
      u' * ((b * x - b * (y * (b' * z))) * u) := by
    simp only [mul_assoc, hc, mul_sub, sub_mul]
  rw [e, LinearMap.trace_mul_comm, mul_assoc, h₁, mul_one]
theorem ring_inverse_conj {R : Type} [Ring R] {u u' : R} (h₁ : u * u' = 1) (h₂ : u' * u = 1)
    (a : R) : Ring.inverse (u' * a * u) = u' * Ring.inverse a * u := by
  have hc : ∀ w, u * (u' * w) = w := fun w => by rw [← mul_assoc, h₁, one_mul]
  by_cases ha : IsUnit a
  · obtain ⟨a, rfl⟩ := ha
    rw [Ring.inverse_unit]
    let v : Rˣ := ⟨u' * a * u, u' * ↑a⁻¹ * u, by simp [mul_assoc, hc, h₂],
      by simp [mul_assoc, hc, h₂]⟩
    exact Ring.inverse_unit v
  · have hn : ¬ IsUnit (u' * a * u) := fun h => ha (by
      have hu : IsUnit u := ⟨⟨u, u', h₁, h₂⟩, rfl⟩
      have hu' : IsUnit u' := ⟨⟨u', u, h₂, h₁⟩, rfl⟩
      have : a = u * (u' * a * u) * u' := by simp [mul_assoc, hc, h₁]
      rw [this]
      exact (hu.mul h).mul hu')
    rw [Ring.inverse_non_unit _ hn, Ring.inverse_non_unit _ ha]
    simp
theorem densityTrace_sum_smul {K K' : Type} [Fintype K] [Fintype K'] (s : K → ℂ) (t : K' → ℂ)
    (b b' : Module.End ℂ (J → ℂ)) (X : K → K' → Module.End ℂ (J → ℂ))
    (Y : K → Module.End ℂ (J → ℂ)) (Z : K' → Module.End ℂ (J → ℂ)) :
    densityTrace b (∑ c, ∑ c', (s c * t c') • X c c') (∑ c, s c • Y c) b' (∑ c', t c' • Z c') =
      ∑ c, ∑ c', s c * t c' * densityTrace b (X c c') (Y c) b' (Z c') := by
  unfold densityTrace
  have e₁ : b * ∑ c, ∑ c', (s c * t c') • X c c' = ∑ c, ∑ c', (s c * t c') • (b * X c c') := by
    simp only [Finset.mul_sum, mul_smul_comm]
  have e₂ : b * ((∑ c, s c • Y c) * (b' * ∑ c', t c' • Z c')) =
      ∑ c, ∑ c', (s c * t c') • (b * (Y c * (b' * Z c'))) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [smul_comm]
  rw [e₁, e₂, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  have e₃ : (s c * t c') • (b * X c c') - (s c * t c') • (b * (Y c * (b' * Z c'))) =
      (s c * t c') • (b * X c c' - b * (Y c * (b' * Z c'))) := (smul_sub _ _ _).symm
  rw [e₃, map_smul, smul_eq_mul]
end MatrixEntries
section Phases
variable {I : PeriodicData}
def carrierPhase (I : PeriodicData) (e : Fin 4 → ℤ) (ι : I.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)))
theorem carrierPhase_translate (hI : IsPeriodic I) (e n : Fin 4 → ℤ) (ι : I.Carrier) :
    carrierPhase I e (I.translate n ι) = carrierPhase I e ι := by
  unfold carrierPhase
  rw [hI.pos_translate]
  have h : bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι + castVec n)) =
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)) +
        ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp [bilinDot, toComplexVec, castVec, mul_add, Finset.sum_add_distrib]
  rw [h, mul_add, Complex.exp_add]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((∑ μ, e μ * n μ : ℤ) : ℂ)) = 1 := by
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, mul_one]
theorem phaseOn_mkQuot (hI : IsPeriodic I) (e : Fin 4 → ℤ) (ι : I.Carrier) :
    phaseOn I e (I.mkQuot 1 ι) = carrierPhase I e ι := by
  let ph : I.UnitQuot → ℂ := Quot.lift (carrierPhase I e) (by
    rintro a _ ⟨n, rfl⟩
    exact (carrierPhase_translate hI e _ a).symm)
  have hex : ∃ z, ∀ ι', I.mkQuot 1 ι' = I.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι'))) = z :=
    ⟨ph (I.mkQuot 1 ι), fun ι' h => by rw [← h]; rfl⟩
  exact (Classical.epsilon_spec hex ι rfl).symm
theorem blochWave_addTwoPiInt (hI : IsPeriodic I) (q : Fin 4 → ℂ) (e : Fin 4 → ℤ)
    (φ : I.UnitQuot → ℂ) :
    blochWave I (addTwoPiInt q e) φ = blochWave I q (phaseMul I e φ) := by apply _root_.YangMills.SharedProofs.p35841 <;> assumption
theorem phaseOn_neg_mul (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    phaseOn I (-e) c * phaseOn I e c = 1 := by
  induction c using Quot.ind with
  | mk ι =>
    have h := phaseOn_mkQuot hI
    change phaseOn I (-e) (I.mkQuot 1 ι) * phaseOn I e (I.mkQuot 1 ι) = 1
    rw [h, h, carrierPhase, carrierPhase, ← Complex.exp_add]
    have : bilinDot (toComplexVec (castVec (-e))) (toComplexVec (I.pos ι)) =
        - bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)) := by
      simp [bilinDot, toComplexVec, castVec]
    rw [this]
    simp
theorem norm_phaseOn (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    ‖phaseOn I e c‖ = 1 := by apply _root_.YangMills.SharedProofs.p4911 <;> assumption
theorem phaseMul_neg_mul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (phaseMul I (-e) * phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) = 1 := by
  refine LinearMap.ext fun f => ?_
  funext c
  simp only [Module.End.mul_apply, phaseMul, LinearMap.coe_mk, AddHom.coe_mk,
    Module.End.one_apply]
  rw [← mul_assoc, phaseOn_neg_mul hI, one_mul]
theorem phaseMul_mul_neg (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (phaseMul I e * phaseMul I (-e) : Module.End ℂ (I.UnitQuot → ℂ)) = 1 := by
  simpa using phaseMul_neg_mul hI (-e)
theorem quotHomInverse_phaseMul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    quotHomInverse (phaseMul I e) = phaseMul I (-e) := by
  unfold quotHomInverse
  let v : (Module.End ℂ (I.UnitQuot → ℂ))ˣ :=
    ⟨phaseMul I e, phaseMul I (-e), phaseMul_mul_neg hI e, phaseMul_neg_mul hI e⟩
  exact Ring.inverse_unit v
theorem quotWeight_pos (hI : IsPeriodic I) (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
theorem wNorm_phaseMul (hI : IsPeriodic I) (e : Fin 4 → ℤ) (ε : I.UnitQuot → ℂ) :
    wNorm (I.quotWeight 1) (phaseMul I e ε) = wNorm (I.quotWeight 1) ε := by
  simp only [wNorm, phaseMul, LinearMap.coe_mk, AddHom.coe_mk, norm_mul,
    norm_phaseOn hI, one_mul]
theorem norm_apply_le_wNorm [Fintype I.UnitQuot] (hI : IsPeriodic I) (ε : I.UnitQuot → ℂ)
    (c : I.UnitQuot) :
    ‖ε c‖ ≤ (Real.sqrt (I.quotWeight 1 c))⁻¹ * wNorm (I.quotWeight 1) ε := by
  have hw := quotWeight_pos hI c
  have hs : 0 < Real.sqrt (I.quotWeight 1 c) := Real.sqrt_pos.2 hw
  rw [inv_mul_eq_div, le_div_iff₀ hs, wNorm, tsum_fintype]
  have h1 : I.quotWeight 1 c * ‖ε c‖ ^ 2 ≤ ∑ i, I.quotWeight 1 i * ‖ε i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => I.quotWeight 1 i * ‖ε i‖ ^ 2)
      (fun i _ => mul_nonneg (quotWeight_pos hI i).le (by positivity)) (Finset.mem_univ c)
  calc ‖ε c‖ * Real.sqrt (I.quotWeight 1 c)
      = Real.sqrt (I.quotWeight 1 c * ‖ε c‖ ^ 2) := by
        rw [Real.sqrt_mul hw.le, Real.sqrt_sq (norm_nonneg _), mul_comm]
    _ ≤ _ := Real.sqrt_le_sqrt h1
end Phases
section LatticePeriods
variable {F I : PeriodicData}
open JetDomains
theorem logDensity_eq_densityTrace (p : Fin 4 → ℂ) (T : JetQuad I I) (κ : Fin 4 → ℂ) :
    logDensity p T κ = densityTrace (quotHomInverse (T.f00 κ)) (T.f11 κ) (T.f10 (κ - p))
      (quotHomInverse (T.f00 (κ - p))) (T.f01 κ) := rfl
theorem addTwoPiInt_sub (κ p : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    addTwoPiInt κ e - p = addTwoPiInt (κ - p) e := by
  funext μ
  simp [addTwoPiInt]
  ring
theorem sub_addTwoPiInt (κ p : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    κ - addTwoPiInt p e = addTwoPiInt (κ - p) (-e) := by
  funext μ
  simp [addTwoPiInt]
  ring
theorem logDensity_addTwoPiInt [Fintype I.UnitQuot] (hI : IsPeriodic I) {p : Fin 4 → ℂ}
    {T : JetQuad I I} (h00 : IsQuasiPeriodic univ T.f00) (h10 : IsQuasiPeriodic univ T.f10)
    (h01 : IsQuasiPeriodic univ T.f01) (h11 : IsQuasiPeriodic univ T.f11) (e : Fin 4 → ℤ)
    (κ : Fin 4 → ℂ) :
    logDensity p T (addTwoPiInt κ e) = logDensity p T κ := by
  have hu₁ := phaseMul_mul_neg hI e
  have hu₂ := phaseMul_neg_mul hI e
  have hq : ∀ {A : (Fin 4 → ℂ) → QuotHom I I}, IsQuasiPeriodic univ A → ∀ κ,
      A (addTwoPiInt κ e) = (phaseMul I (-e) * A κ * phaseMul I e :
        Module.End ℂ (I.UnitQuot → ℂ)) := fun h κ => by
    rw [h e κ (mem_univ _), quotHomInverse_phaseMul hI, mul_assoc]
    rfl
  have hinv : ∀ κ, quotHomInverse (T.f00 (addTwoPiInt κ e)) =
      (phaseMul I (-e) * quotHomInverse (T.f00 κ) * phaseMul I e :
        Module.End ℂ (I.UnitQuot → ℂ)) := fun κ => by
    rw [hq h00 κ]
    exact ring_inverse_conj hu₁ hu₂ _
  rw [logDensity_eq_densityTrace, logDensity_eq_densityTrace, addTwoPiInt_sub,
    hinv, hinv, hq h11, hq h10, hq h01]
  exact densityTrace_conj hu₁ _ _ _ _ _
theorem jetAlong_addTwoPiInt [Finite I.UnitQuot] (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (h : OpFunJetProperties F I I T)
    (p : Fin 4 → ℂ) (e : Fin 4 → ℤ) (εPlus εMinus : F.UnitQuot → ℂ) (κ : Fin 4 → ℂ) :
    (jetAlong F I I T (addTwoPiInt p e) εPlus εMinus).f10 κ =
        (phaseMul I (-e) * (jetAlong F I I T p (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus)).f10 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      (jetAlong F I I T (addTwoPiInt p e) εPlus εMinus).f01 κ =
        (phaseMul I e * (jetAlong F I I T p (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus)).f01 κ : Module.End ℂ (I.UnitQuot → ℂ)) ∧
      (jetAlong F I I T (addTwoPiInt p e) εPlus εMinus).f11 κ =
        (jetAlong F I I T p (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus)).f11 κ := by
  set ε₁ := phaseMul F e εPlus
  set ε₂ := phaseMul F (-e) εMinus
  have hA := Classical.epsilon_spec (h.triple_unique p ε₁ ε₂).exists
  set A := Classical.epsilon (IsActionTriple F I I T p ε₁ ε₂) with hAdef
  have hwp : blochWave F (addTwoPiInt p e) εPlus = blochWave F p ε₁ :=
    blochWave_addTwoPiInt hF p e εPlus
  have hwm : blochWave F (-addTwoPiInt p e) εMinus = blochWave F (-p) ε₂ := by
    have : -addTwoPiInt p e = addTwoPiInt (-p) (-e) := by
      funext μ
      simp [addTwoPiInt]
      ring
    rw [this]
    exact blochWave_addTwoPiInt hF (-p) (-e) εMinus
  have hA' : IsActionTriple F I I T (addTwoPiInt p e) εPlus εMinus
      (fun κ => (phaseMul I (-e) * A.1 κ : Module.End ℂ (I.UnitQuot → ℂ)),
        fun κ => (phaseMul I e * A.2.1 κ : Module.End ℂ (I.UnitQuot → ℂ)), A.2.2) := by
    intro κ φ ι'
    obtain ⟨h1, h2, h3⟩ := hA κ φ ι'
    refine ⟨?_, ?_, ?_⟩
    · rw [hwp, h1]
      have : κ + addTwoPiInt p e = addTwoPiInt (κ + p) e := by
        funext μ
        simp [addTwoPiInt]
        ring
      rw [this, blochWave_addTwoPiInt hI]
      have hc : phaseMul I e ((phaseMul I (-e) * A.1 κ :
          Module.End ℂ (I.UnitQuot → ℂ)) φ) = A.1 κ φ := by
        have := congrArg (fun M : Module.End ℂ (I.UnitQuot → ℂ) => M (A.1 κ φ))
          (phaseMul_mul_neg hI e)
        simpa using this
      rw [hc]
    · rw [hwm, h2, sub_eq_add_neg κ (addTwoPiInt p e)]
      have : κ + -addTwoPiInt p e = addTwoPiInt (κ - p) (-e) := by
        rw [← sub_eq_add_neg, sub_addTwoPiInt]
      rw [this, blochWave_addTwoPiInt hI]
      have hc : phaseMul I (-e) ((phaseMul I e * A.2.1 κ :
          Module.End ℂ (I.UnitQuot → ℂ)) φ) = A.2.1 κ φ := by
        have := congrArg (fun M : Module.End ℂ (I.UnitQuot → ℂ) => M (A.2.1 κ φ))
          (phaseMul_neg_mul hI e)
        simpa using this
      rw [hc]
    · rw [hwp, hwm]
      exact h3
  have hu := (h.triple_unique (addTwoPiInt p e) εPlus εMinus).unique
    (Classical.epsilon_spec (h.triple_unique (addTwoPiInt p e) εPlus εMinus).exists) hA'
  refine ⟨?_, ?_, ?_⟩
  · exact congrFun (congrArg Prod.fst hu) κ
  · exact congrFun (congrArg (fun x => x.2.1) hu) κ
  · exact congrFun (congrArg (fun x => x.2.2) hu) κ
theorem logDensity_jetAlong_addTwoPiInt [Fintype I.UnitQuot] (hF : IsPeriodic F)
    (hI : IsPeriodic I) {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    (h : OpFunJetProperties F I I T) (p : Fin 4 → ℂ) (e : Fin 4 → ℤ)
    (εPlus εMinus : F.UnitQuot → ℂ) (κ : Fin 4 → ℂ) :
    logDensity (addTwoPiInt p e) (jetAlong F I I T (addTwoPiInt p e) εPlus εMinus) κ =
      logDensity p (jetAlong F I I T p (phaseMul F e εPlus)
        (phaseMul F (-e) εMinus)) κ := by
  set J := jetAlong F I I T p (phaseMul F e εPlus) (phaseMul F (-e) εMinus)
    with hJ
  have hq := h.quasiPeriodic p (phaseMul F e εPlus) (phaseMul F (-e) εMinus)
  have hu₁ := phaseMul_mul_neg hI e
  have hu₂ := phaseMul_neg_mul hI e
  have h00 : (jetAlong F I I T (addTwoPiInt p e) εPlus εMinus).f00 = J.f00 := rfl
  obtain ⟨-, -, h11⟩ := jetAlong_addTwoPiInt hF hI h p e εPlus εMinus κ
  obtain ⟨-, h01, -⟩ := jetAlong_addTwoPiInt hF hI h p e εPlus εMinus κ
  obtain ⟨h10, -, -⟩ := jetAlong_addTwoPiInt hF hI h p e εPlus εMinus (κ - addTwoPiInt p e)
  rw [logDensity_eq_densityTrace, logDensity_eq_densityTrace, h00, h10, h01, h11]
  have hA : J.f00 (κ - addTwoPiInt p e) =
      (phaseMul I e * J.f00 (κ - p) * phaseMul I (-e) :
        Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [sub_addTwoPiInt, hq.1 (-e) _ (mem_univ _), quotHomInverse_phaseMul hI, neg_neg,
      mul_assoc]
    rfl
  have hB : quotHomInverse (J.f00 (κ - addTwoPiInt p e)) =
      (phaseMul I e * quotHomInverse (J.f00 (κ - p)) * phaseMul I (-e) :
        Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [hA]
    exact ring_inverse_conj hu₂ hu₁ _
  have hY : J.f10 (κ - addTwoPiInt p e) =
      (phaseMul I e * J.f10 (κ - p) * phaseMul I (-e) :
        Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [sub_addTwoPiInt, hq.2.1 (-e) _ (mem_univ _), quotHomInverse_phaseMul hI, neg_neg,
      mul_assoc]
    rfl
  rw [hB, hY]
  unfold densityTrace
  congr 2
  generalize (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) = u at *
  generalize (phaseMul I (-e) : Module.End ℂ (I.UnitQuot → ℂ)) = u' at *
  have hc : ∀ w, u' * (u * w) = w := fun w => by rw [← mul_assoc, hu₂, one_mul]
  simp only [mul_assoc, hc]
  rfl
end LatticePeriods
section BilinearExpansion
variable {F I : PeriodicData} [Fintype F.UnitQuot] [Finite I.UnitQuot]
  {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
open JetDomains
theorem f10_jetAlong_eq_sum (h : OpFunJetProperties F I I T) (p κ : Fin 4 → ℂ)
    (ε ε' ε'' : F.UnitQuot → ℂ) :
    (jetAlong F I I T p ε ε').f10 κ = ∑ c, ε c • (jetAlong F I I T p (stdUnit c) ε'').f10 κ := by
  refine linearMap_ext_entry fun i k => ?_
  rw [linearMapEntry_sum_smul]
  obtain ⟨n, f, a, ha⟩ := h.entries_f10 i k
  simp only [ha, expSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [linearMap_apply_eq_sum (a j) ε, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
theorem f01_jetAlong_eq_sum (h : OpFunJetProperties F I I T) (p κ : Fin 4 → ℂ)
    (ε ε' ε'' : F.UnitQuot → ℂ) :
    (jetAlong F I I T p ε ε').f01 κ = ∑ c, ε' c • (jetAlong F I I T p ε'' (stdUnit c)).f01 κ := by
  refine linearMap_ext_entry fun i k => ?_
  rw [linearMapEntry_sum_smul]
  obtain ⟨n, f, a, ha⟩ := h.entries_f01 i k
  simp only [ha, expSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [linearMap_apply_eq_sum (a j) ε', Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
omit [Fintype F.UnitQuot] in
theorem f10_jetAlong_indep (h : OpFunJetProperties F I I T) (p κ : Fin 4 → ℂ)
    (ε ε' ε'' : F.UnitQuot → ℂ) :
    (jetAlong F I I T p ε ε').f10 κ = (jetAlong F I I T p ε ε'').f10 κ := by
  refine linearMap_ext_entry fun i k => ?_
  obtain ⟨n, f, a, ha⟩ := h.entries_f10 i k
  rw [ha, ha]
omit [Fintype F.UnitQuot] in
theorem f01_jetAlong_indep (h : OpFunJetProperties F I I T) (p κ : Fin 4 → ℂ)
    (ε ε' ε'' : F.UnitQuot → ℂ) :
    (jetAlong F I I T p ε' ε).f01 κ = (jetAlong F I I T p ε'' ε).f01 κ := by
  refine linearMap_ext_entry fun i k => ?_
  obtain ⟨n, f, a, ha⟩ := h.entries_f01 i k
  rw [ha, ha]
theorem bilin_apply_eq_sum {J : Type} [Fintype J] (a : (J → ℂ) →ₗ[ℂ] (J → ℂ) →ₗ[ℂ] ℂ)
    (ε ε' : J → ℂ) :
    a ε ε' = ∑ c, ∑ c', ε c * ε' c' * a (stdUnit c) (stdUnit c') := by
  calc a ε ε' = ∑ c', ε' c' * a ε (stdUnit c') := linearMap_apply_eq_sum _ _
    _ = ∑ c', ε' c' * ∑ c, ε c * a (stdUnit c) (stdUnit c') := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        congr 1
        exact linearMap_apply_eq_sum (a.flip (stdUnit c')) ε
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
        ring
theorem f11_jetAlong_eq_sum (h : OpFunJetProperties F I I T) (p κ : Fin 4 → ℂ)
    (ε ε' : F.UnitQuot → ℂ) :
    (jetAlong F I I T p ε ε').f11 κ = ∑ c, ∑ c', (ε c * ε' c') •
      (jetAlong F I I T p (stdUnit c) (stdUnit c')).f11 κ := by
  refine linearMap_ext_entry fun i k => ?_
  have hd : linearMapEntry (∑ c, ∑ c', (ε c * ε' c') •
        (jetAlong F I I T p (stdUnit c) (stdUnit c')).f11 κ) i k =
      ∑ c, ∑ c', (ε c * ε' c') *
        linearMapEntry ((jetAlong F I I T p (stdUnit c) (stdUnit c')).f11 κ) i k := by
    simp [linearMapEntry, LinearMap.sum_apply, Finset.sum_apply]
  rw [hd]
  obtain ⟨n, f, a, ha⟩ := h.entries_f11 i k
  simp only [ha, expSum]
  simp only [bilin_apply_eq_sum (a _) ε ε', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => ?_
  ring
def basisDensity (F I : PeriodicData) (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (c c' : F.UnitQuot) (κ p : Fin 4 → ℂ) : ℂ :=
  logDensity p (jetAlong F I I T p (stdUnit c) (stdUnit c')) κ
theorem logDensity_eq_sum_basisDensity [Fintype I.UnitQuot] (h : OpFunJetProperties F I I T)
    (p κ : Fin 4 → ℂ) (ε ε' : F.UnitQuot → ℂ) :
    logDensity p (jetAlong F I I T p ε ε') κ =
      ∑ c, ∑ c', ε c * ε' c' * basisDensity F I T c c' κ p := by
  rw [logDensity_eq_densityTrace, f11_jetAlong_eq_sum h p κ ε ε',
    f10_jetAlong_eq_sum h p (κ - p) ε ε' 0, f01_jetAlong_eq_sum h p κ ε ε' 0]
  refine (densityTrace_sum_smul ε ε' _ _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  congr 1
  rw [basisDensity, logDensity_eq_densityTrace,
    f10_jetAlong_indep h p (κ - p) (stdUnit c) 0 (stdUnit c'),
    f01_jetAlong_indep h p κ (stdUnit c') 0 (stdUnit c)]
  rfl
end BilinearExpansion
section SeparateHolomorphy
abbrev MomPair : Type := (Fin 4 → ℂ) × (Fin 4 → ℂ)
structure SepHolo (U : Set MomPair) (h : MomPair → ℂ) : Prop where
  contOn : ContinuousOn h U
  diff_fst : ∀ (x : MomPair) (j : Fin 4),
    DifferentiableOn ℂ (fun ζ : ℂ => h (x.1 + ζ • stdBasisVector j, x.2))
      {ζ : ℂ | (x.1 + ζ • stdBasisVector j, x.2) ∈ U}
  diff_snd : ∀ (x : MomPair) (j : Fin 4),
    DifferentiableOn ℂ (fun ζ : ℂ => h (x.1, x.2 + ζ • stdBasisVector j))
      {ζ : ℂ | (x.1, x.2 + ζ • stdBasisVector j) ∈ U}
variable {U : Set MomPair} {h h' : MomPair → ℂ}
theorem SepHolo.sub (a : SepHolo U h) (b : SepHolo U h') : SepHolo U fun x => h x - h' x :=
  ⟨a.contOn.sub b.contOn, fun x j => (a.diff_fst x j).sub (b.diff_fst x j),
    fun x j => (a.diff_snd x j).sub (b.diff_snd x j)⟩
theorem SepHolo.mul (a : SepHolo U h) (b : SepHolo U h') : SepHolo U fun x => h x * h' x :=
  ⟨a.contOn.mul b.contOn, fun x j => (a.diff_fst x j).mul (b.diff_fst x j),
    fun x j => (a.diff_snd x j).mul (b.diff_snd x j)⟩
theorem SepHolo.const (z : ℂ) : SepHolo U fun _ => z :=
  ⟨continuousOn_const, fun _ _ => differentiableOn_const _, fun _ _ => differentiableOn_const _⟩
theorem SepHolo.add (a : SepHolo U h) (b : SepHolo U h') : SepHolo U fun x => h x + h' x :=
  ⟨a.contOn.add b.contOn, fun x j => (a.diff_fst x j).add (b.diff_fst x j),
    fun x j => (a.diff_snd x j).add (b.diff_snd x j)⟩
theorem SepHolo.sum {K : Type} (s : Finset K) {g : K → MomPair → ℂ}
    (hg : ∀ k, SepHolo U (g k)) : SepHolo U fun x => ∑ k ∈ s, g k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SepHolo.const (U := U) 0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hg k).add ih
theorem SepHolo.of_differentiable (hd : Differentiable ℂ h) : SepHolo U h :=
  ⟨hd.continuous.continuousOn,
    fun x j => (hd.comp (f := fun ζ : ℂ => ((x.1 + ζ • stdBasisVector j, x.2) : MomPair))
      (by fun_prop)).differentiableOn,
    fun x j => (hd.comp (f := fun ζ : ℂ => ((x.1, x.2 + ζ • stdBasisVector j) : MomPair))
      (by fun_prop)).differentiableOn⟩
theorem SepHolo.isHolomorphicIn_slice (hU : IsOpen U) (a : SepHolo U h) (p : Fin 4 → ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) {κ : ComplexCoordinates 4 | (κ, p) ∈ U}
      fun κ _ => h (κ, p) :=
  isHolomorphicIn_of_coordLine (g := fun κ => h (κ, p)) (hU.preimage (by fun_prop))
    (a.contOn.comp (f := fun κ : ComplexCoordinates 4 => ((κ, p) : MomPair))
      (Continuous.continuousOn (by fun_prop)) fun _ hκ => hκ)
    fun b j => a.diff_fst (b, p) j
def diffPairs (O : Set (Fin 4 → ℂ)) : Set MomPair := {x | x.1 ∈ O ∧ x.1 - x.2 ∈ O}
theorem isOpen_diffPairs {O : Set (Fin 4 → ℂ)} (hO : IsOpen O) : IsOpen (diffPairs O) :=
  (hO.preimage continuous_fst).inter (hO.preimage (continuous_fst.sub continuous_snd))
variable {O : Set (Fin 4 → ℂ)} {β : (Fin 4 → ℂ) → ℂ}
theorem SepHolo.comp_fst (hβ : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => β z) :
    SepHolo (diffPairs O) fun x => β x.1 := by
  refine ⟨?_, fun x j => ?_, fun x j => ?_⟩
  · exact ((continuousOn_pi.1 hβ.2.1 0).comp continuous_fst.continuousOn fun x hx => hx.1)
  · exact (differentiableOn_coordLine hβ x.1 j).mono fun ζ hζ => hζ.1
  · change DifferentiableOn ℂ (fun _ => β x.1) _
    exact differentiableOn_const _
theorem SepHolo.comp_sub (hβ : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => β z) :
    SepHolo (diffPairs O) fun x => β (x.1 - x.2) := by
  refine ⟨?_, fun x j => ?_, fun x j => ?_⟩
  · exact ((continuousOn_pi.1 hβ.2.1 0).comp
      (continuous_fst.sub continuous_snd).continuousOn fun x hx => hx.2)
  · have e : ∀ ζ : ℂ, x.1 + ζ • stdBasisVector j - x.2 = (x.1 - x.2) + ζ • stdBasisVector j :=
      fun ζ => by abel
    simp only [e]
    refine (differentiableOn_coordLine hβ (x.1 - x.2) j).mono fun ζ hζ => ?_
    have := hζ.2
    simp only [e] at this
    exact this
  · have e : ∀ ζ : ℂ, x.1 - (x.2 + ζ • stdBasisVector j) =
        (x.1 - x.2) + (-ζ) • stdBasisVector j :=
      fun ζ => by
        rw [neg_smul]
        abel
    simp only [e]
    refine (differentiableOn_coordLine hβ (x.1 - x.2) j).comp (f := fun ζ : ℂ => -ζ)
      (differentiable_neg.differentiableOn) fun ζ hζ => ?_
    have := hζ.2
    simp only [e] at this
    exact this
theorem differentiable_expSum_fst {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → JetDomains.MomentumLinearForm) :
    Differentiable ℂ fun x : MomPair => JetDomains.expSum a f x.1 x.2 := by
  unfold JetDomains.expSum
  refine Differentiable.fun_sum fun j _ => (differentiable_const _).mul ?_
  have hf : Differentiable ℂ (f j) := (LinearMap.toContinuousLinearMap (f j)).differentiable
  exact (hf.comp (f := fun x : MomPair => (x.1, x.2)) (by fun_prop)).cexp
theorem differentiable_expSum_sub {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → JetDomains.MomentumLinearForm) :
    Differentiable ℂ fun x : MomPair => JetDomains.expSum a f (x.1 - x.2) x.2 := by
  unfold JetDomains.expSum
  refine Differentiable.fun_sum fun j _ => (differentiable_const _).mul ?_
  have hf : Differentiable ℂ (f j) := (LinearMap.toContinuousLinearMap (f j)).differentiable
  exact (hf.comp (f := fun x : MomPair => (x.1 - x.2, x.2)) (by fun_prop)).cexp
variable {F I : PeriodicData} [Fintype I.UnitQuot] {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
open JetDomains
theorem sepHolo_basisDensity (h : OpFunJetProperties F I I T)
    (hβ : ∀ i k : I.UnitQuot, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun κ _ =>
      linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) κ)) i k)
    (c c' : F.UnitQuot) :
    SepHolo (diffPairs O) fun x => basisDensity F I T c c' x.1 x.2 := by
  have h11 : ∀ k i : I.UnitQuot, SepHolo (diffPairs O) fun x : MomPair =>
      linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f11 x.1) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f11 k i
      simp only [ha]
      exact SepHolo.of_differentiable (differentiable_expSum_fst _ f)
  have h01 : ∀ k i : I.UnitQuot, SepHolo (diffPairs O) fun x : MomPair =>
      linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f01 x.1) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f01 k i
      simp only [ha]
      exact SepHolo.of_differentiable (differentiable_expSum_fst _ f)
  have h10 : ∀ k i : I.UnitQuot, SepHolo (diffPairs O) fun x : MomPair =>
      linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f10 (x.1 - x.2)) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f10 k i
      simp only [ha]
      exact SepHolo.of_differentiable (differentiable_expSum_sub _ f)
  have e : (fun x : MomPair => basisDensity F I T c c' x.1 x.2) = fun x =>
      ∑ i, ((∑ k, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) x.1)) i k *
          linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f11 x.1) k i) -
        ∑ k, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) x.1)) i k *
          ∑ l, linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f10 (x.1 - x.2)) k l *
            ∑ m, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T)
              (x.1 - x.2))) l m *
              linearMapEntry ((jetAlong F I I T x.2 (stdUnit c) (stdUnit c')).f01 x.1) m i) := by
    funext x
    exact densityTrace_eq_sum _ _ _ _ _
  rw [e]
  refine SepHolo.sum _ fun i => (SepHolo.sum _ fun k => ?_).sub (SepHolo.sum _ fun k => ?_)
  · exact (SepHolo.comp_fst (hβ i k)).mul (h11 k i)
  · refine (SepHolo.comp_fst (hβ i k)).mul (SepHolo.sum _ fun l => ?_)
    refine (h10 k l).mul (SepHolo.sum _ fun m => ?_)
    exact (SepHolo.comp_sub (hβ l m)).mul (h01 m i)
end SeparateHolomorphy
section PeriodBox
def periodBox (r : ℝ) : Set (Fin 4 → ℂ) :=
  {z | ∀ μ, (z μ).re ∈ Icc 0 (2 * Real.pi) ∧ |(z μ).im| ≤ r}
theorem isCompact_periodBox (r : ℝ) : IsCompact (periodBox r) := by
  have e : periodBox r =
      Set.pi univ fun _ : Fin 4 => Icc 0 (2 * Real.pi) ×ℂ Icc (-r) r := by
    ext z
    simp [periodBox, Complex.mem_reProdIm, abs_le]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_Icc.reProdIm isCompact_Icc
theorem exists_addTwoPiInt_eq (z : Fin 4 → ℂ) :
    ∃ (e : Fin 4 → ℤ) (z₀ : Fin 4 → ℂ), z = addTwoPiInt z₀ e ∧
      ∀ μ, (z₀ μ).re ∈ Icc 0 (2 * Real.pi) ∧ (z₀ μ).im = (z μ).im := by
  refine ⟨fun μ => ⌊(z μ).re / (2 * Real.pi)⌋,
    fun μ => z μ - 2 * Real.pi * (⌊(z μ).re / (2 * Real.pi)⌋ : ℂ), ?_, fun μ => ?_⟩
  · funext μ
    simp [addTwoPiInt]
  · dsimp only
    have hpi : 0 < 2 * Real.pi := by positivity
    have h1 := Int.floor_le ((z μ).re / (2 * Real.pi))
    have h2 := Int.lt_floor_add_one ((z μ).re / (2 * Real.pi))
    set m := ⌊(z μ).re / (2 * Real.pi)⌋
    have hc : 2 * (Real.pi : ℂ) * (m : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · have := (le_div_iff₀ hpi).1 h1
      linarith
    · have := (div_lt_iff₀ hpi).1 h2
      linarith
end PeriodBox
theorem claim_holds (hLocal : JetDomains.OpFunJetTheory) (hCalc : JetCalculus.Claim) : Claim := by
  intro F I hF hI T hT δ hδ hinv
  have := hF.finite_quot
  have := hI.finite_quot
  let _ : Fintype F.UnitQuot := Fintype.ofFinite _
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  have hfacts := hLocal.2.1 F I I hF hI hI T hT
  have h0 : (0 : Fin 4 → ℂ) ∈ imStrip δ := fun μ => by simpa using hδ.le
  obtain ⟨-, hJinv⟩ :=
    (hLocal.2.2 I I I hI hI hI δ 0 hδ h0).zeroPart_isJet _ (hinv 0 h0 0 0)
  obtain ⟨O₁, hO₁, hsub, hhol⟩ := hJinv.holo_f00
  have hβ : ∀ i k : I.UnitQuot, ComplexCoordinates.IsHolomorphicIn (N' := 1) O₁ fun κ _ =>
      linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) κ)) i k := hhol
  have hgood := fun c c' => sepHolo_basisDensity hfacts hβ c c'
  have hU := isOpen_diffPairs hO₁
  have hstrip : ∀ κ : Fin 4 → ℂ, (∀ μ, |(κ μ).im| ≤ 2 * δ) → κ ∈ O₁ := fun κ h => hsub h
  have hKU : periodBox δ ×ˢ periodBox 0 ⊆ diffPairs O₁ := by
    rintro ⟨κ, p⟩ ⟨h1, h2⟩
    refine ⟨hstrip _ fun μ => ?_, hstrip _ fun μ => ?_⟩
    · have := (h1 μ).2
      change |(κ μ).im| ≤ 2 * δ
      linarith
    · have a := (h1 μ).2
      have b := (h2 μ).2
      change |(κ μ - p μ).im| ≤ 2 * δ
      rw [Complex.sub_im]
      have := abs_sub (κ μ).im (p μ).im
      linarith
  have hbox : ∀ c c', ∃ M : ℝ, ∀ x ∈ periodBox δ ×ˢ periodBox 0,
      ‖basisDensity F I T c c' x.1 x.2‖ ≤ M := fun c c' =>
    ((isCompact_periodBox δ).prod (isCompact_periodBox 0)).exists_bound_of_continuousOn
      ((hgood c c').contOn.mono hKU)
  choose M hM using hbox
  let w : F.UnitQuot → ℝ := fun c => (Real.sqrt (F.quotWeight 1 c))⁻¹
  have hw : ∀ c, 0 ≤ w c := fun c => inv_nonneg.2 (Real.sqrt_nonneg _)
  let S : ℝ := ∑ c, ∑ c', w c * w c' * |M c c'|
  have hS : 0 ≤ S := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun c' _ =>
    mul_nonneg (mul_nonneg (hw c) (hw c')) (abs_nonneg _)
  refine ⟨⟨S + 1, by linarith, fun p εPlus εMinus => ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · have e : logDensity (toComplexVec p)
        (jetAlong F I I T (toComplexVec p) εPlus εMinus) = fun κ =>
          ∑ c, ∑ c', εPlus c * εMinus c' * basisDensity F I T c c' κ (toComplexVec p) :=
      funext fun κ => logDensity_eq_sum_basisDensity hfacts _ κ _ _
    rw [e]
    have hg : SepHolo (diffPairs O₁) fun x : MomPair =>
        ∑ c, ∑ c', εPlus c * εMinus c' * basisDensity F I T c c' x.1 x.2 :=
      SepHolo.sum _ fun c => SepHolo.sum _ fun c' => (SepHolo.const _).mul (hgood c c')
    have hs := hg.isHolomorphicIn_slice hU (toComplexVec p)
    refine ⟨{κ | (κ, toComplexVec p) ∈ diffPairs O₁}, fun κ hκ => ?_, hs⟩
    change κ ∈ O₁ ∧ κ - toComplexVec p ∈ O₁
    refine ⟨hstrip _ fun μ => ?_, hstrip _ fun μ => ?_⟩
    · have := hκ μ
      linarith
    · have := hκ μ
      simp only [Pi.sub_apply, Complex.sub_im, toComplexVec, Complex.ofReal_im, sub_zero]
      linarith
  · intro κ _ q hq
    obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, q μ = (n μ : ℝ) * (2 * Real.pi) := hq
    have e : κ + toComplexVec q = addTwoPiInt κ n := by
      funext μ
      simp only [Pi.add_apply, addTwoPiInt, toComplexVec, hn μ]
      push_cast
      ring
    rw [e]
    obtain ⟨q0, q1, q2, q3⟩ := hfacts.quasiPeriodic (toComplexVec p) εPlus εMinus
    exact logDensity_addTwoPiInt hI q0 q1 q2 q3 n κ
  · intro κ hκ
    obtain ⟨e, p₀, hp, hp₀⟩ := exists_addTwoPiInt_eq (toComplexVec p)
    obtain ⟨e', κ₀, hκe, hκ₀⟩ := exists_addTwoPiInt_eq κ
    have hx : ((κ₀, p₀) : MomPair) ∈ periodBox δ ×ˢ periodBox 0 := by
      refine ⟨fun μ => ⟨(hκ₀ μ).1, ?_⟩, fun μ => ⟨(hp₀ μ).1, ?_⟩⟩
      · rw [(hκ₀ μ).2]
        exact hκ μ
      · rw [(hp₀ μ).2]
        simp [toComplexVec]
    set ε₁ := phaseMul F e εPlus with hε₁
    set ε₂ := phaseMul F (-e) εMinus with hε₂
    have hval : logDensity (toComplexVec p)
        (jetAlong F I I T (toComplexVec p) εPlus εMinus) κ =
          ∑ c, ∑ c', ε₁ c * ε₂ c' * basisDensity F I T c c' κ₀ p₀ := by
      obtain ⟨q0, q1, q2, q3⟩ := hfacts.quasiPeriodic p₀ ε₁ ε₂
      rw [hp, logDensity_jetAlong_addTwoPiInt hF hI hfacts, hκe,
        logDensity_addTwoPiInt hI q0 q1 q2 q3 e' κ₀]
      exact logDensity_eq_sum_basisDensity hfacts _ _ _ _
    have hn₁ : wNorm (F.quotWeight 1) ε₁ = wNorm (F.quotWeight 1) εPlus :=
      wNorm_phaseMul hF _ _
    have hn₂ : wNorm (F.quotWeight 1) ε₂ = wNorm (F.quotWeight 1) εMinus :=
      wNorm_phaseMul hF _ _
    rw [hval]
    set N₁ := wNorm (F.quotWeight 1) εPlus
    set N₂ := wNorm (F.quotWeight 1) εMinus
    have hN₁ : 0 ≤ N₁ := Real.sqrt_nonneg _
    have hN₂ : 0 ≤ N₂ := Real.sqrt_nonneg _
    calc ‖∑ c, ∑ c', ε₁ c * ε₂ c' * basisDensity F I T c c' κ₀ p₀‖
        ≤ ∑ c, ∑ c', ‖ε₁ c * ε₂ c' * basisDensity F I T c c' κ₀ p₀‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => norm_sum_le _ _)
      _ ≤ ∑ c, ∑ c', w c * w c' * |M c c'| * (N₁ * N₂) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
          have a : ‖ε₁ c‖ ≤ w c * N₁ := by
            have := norm_apply_le_wNorm hF ε₁ c
            rwa [hn₁] at this
          have b : ‖ε₂ c'‖ ≤ w c' * N₂ := by
            have := norm_apply_le_wNorm hF ε₂ c'
            rwa [hn₂] at this
          have m : ‖basisDensity F I T c c' κ₀ p₀‖ ≤ |M c c'| :=
            (hM c c' _ hx).trans (le_abs_self _)
          rw [norm_mul, norm_mul]
          calc ‖ε₁ c‖ * ‖ε₂ c'‖ * ‖basisDensity F I T c c' κ₀ p₀‖
              ≤ (w c * N₁) * (w c' * N₂) * |M c c'| := by gcongr
            _ = _ := by ring
      _ = S * (N₁ * N₂) := by simp only [S, Finset.sum_mul]
      _ ≤ (S + 1) * N₁ * N₂ := by nlinarith [mul_nonneg hN₁ hN₂]
  · let Cube : Set AmbientSpace := Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi
    let O : Set (Fin 4 → ℂ) := {p | ∀ μ, |(p μ).im| < 2 * δ}
    have hO : IsOpen O := by
      have : O = ⋂ μ, {p : Fin 4 → ℂ | |(p μ).im| < 2 * δ} := by
        ext p
        simp [O]
      rw [this]
      exact isOpen_iInter_of_finite fun μ => isOpen_lt (by fun_prop) continuous_const
    have hsubO : imStrip δ ⊆ O := fun p hp μ => (hp μ).trans_lt (by linarith)
    have hpair : ∀ (κ : AmbientSpace) (p : Fin 4 → ℂ), p ∈ O →
        ((toComplexVec κ, p) : MomPair) ∈ diffPairs O₁ := by
      intro κ p hp
      refine ⟨hstrip _ fun μ => ?_, hstrip _ fun μ => ?_⟩
      · simp [toComplexVec]
        positivity
      · have := hp μ
        simp only [Pi.sub_apply, Complex.sub_im, toComplexVec, Complex.ofReal_im, zero_sub,
          abs_neg]
        exact this.le
    have hcv : Continuous toComplexVec := by
      unfold toComplexVec
      fun_prop
    have hcont : ∀ c c', ContinuousOn
        (fun q : AmbientSpace × ComplexCoordinates 4 =>
          basisDensity F I T c c' (toComplexVec q.1) q.2)
        (Cube ×ˢ O) := fun c c' =>
      (hgood c c').contOn.comp
        (f := fun q : AmbientSpace × ComplexCoordinates 4 => ((toComplexVec q.1, q.2) : MomPair))
        (Continuous.continuousOn (by fun_prop)) fun q hq => hpair q.1 q.2 hq.2
    have hline : ∀ c c', ∀ x ∈ Cube, ∀ a j, DifferentiableOn ℂ
        (fun ζ : ℂ => basisDensity F I T c c' (toComplexVec x) (a + ζ • stdBasisVector j))
        (coordLine O a j) := fun c c' x _ a j =>
      ((hgood c c').diff_snd (toComplexVec x, a) j).mono fun ζ hζ => hpair x _ hζ
    have hCc : IsCompact Cube := isCompact_Icc
    have hCm : MeasurableSet Cube := measurableSet_Icc
    refine ⟨O, hO, hsubO, fun c c' p => torusAverage fun κ =>
      basisDensity F I T c c' (toComplexVec κ) p, fun c c' => ?_, fun p hp εPlus εMinus => ?_⟩
    · have h1 := continuousOn_setIntegral_slice
        (Φ := fun κ p => basisDensity F I T c c' (toComplexVec κ) p) hCc hCm hO (hcont c c')
      have h2 := differentiableOn_setIntegral_coordLine
        (Φ := fun κ p => basisDensity F I T c c' (toComplexVec κ) p) hCc hCm hO (hcont c c')
        (hline c c')
      exact isHolomorphicIn_of_coordLine hO (continuousOn_const.mul h1)
        fun a j => (h2 a j).const_mul _
    · have hlog := ((hCalc δ p hδ hp).2.2.2.2.2.2.1 I hI).2 _ (hinv p hp εPlus εMinus)
      rw [hlog]
      have hint : ∀ c c', IntegrableOn
          (fun κ => basisDensity F I T c c' (toComplexVec κ) p) Cube volume := fun c c' =>
        integrableOn_slice (Φ := fun κ p => basisDensity F I T c c' (toComplexVec κ) p) hCc
          (hcont c c') (hsubO hp)
      have e₁ : ∀ κ : AmbientSpace, logDensity p (jetAlong F I I T p εPlus εMinus)
          (toComplexVec κ) =
            ∑ c, ∑ c', εPlus c * εMinus c' * basisDensity F I T c c' (toComplexVec κ) p :=
        fun κ => logDensity_eq_sum_basisDensity hfacts _ _ _ _
      have e₂ : ∫ κ in Cube, ∑ c, ∑ c', εPlus c * εMinus c' *
            basisDensity F I T c c' (toComplexVec κ) p =
          ∑ c, ∑ c', εPlus c * εMinus c' *
            ∫ κ in Cube, basisDensity F I T c c' (toComplexVec κ) p := by
        rw [integral_finsetSum _ fun c _ =>
          integrable_finsetSum _ fun c' _ => (hint c c').const_mul _]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [integral_finsetSum _ fun c' _ => (hint c c').const_mul _]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [integral_const_mul]
      simp only [torusAverage, e₁, tsum_fintype]
      change _ * ∫ κ in Cube, _ = _
      rw [e₂, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring
end YangMills.Construction.PeriodicOperators.LogDensityBounds
end
