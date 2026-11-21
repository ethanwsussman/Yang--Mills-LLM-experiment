import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocal
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTheSumOfItsDensity
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps Filter
namespace StepDensityIsLocal
variable {n : ℕ}
private theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
private theorem eventually_isCold_nhds_trivial [NeZero n] {s : ℝ} (hs : 0 < s) :
    ∀ᶠ W in 𝓝 (trivialField n), IsCold s W := by
  unfold TorusFields.IsCold
  refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun μ => Filter.eventually_all.2 fun ν => ?_
  have hlim := (continuous_curvature x μ ν).tendsto (trivialField n)
  have hzero : curvature (trivialField n) x μ ν = 0 := by simp [curvature, holonomy, trivialField]
  have hlim' : Filter.Tendsto (fun W : TorusField n => curvature W x μ ν) (𝓝 (trivialField n)) (𝓝 0) := by
    rwa [hzero] at hlim
  exact (hlim'.eventually (Iio_mem_nhds hs)).mono fun W hW _ => hW
abbrev _root_.YangMills.SharedProofs.p23383 := @eventually_isCold_nhds_trivial
private theorem iteratedFDeriv_comp_continuousLinearMap_zero {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (D : E →L[ℝ] E) (hf : ContDiffAt ℝ k f (D 0)) :
    iteratedFDeriv ℝ k (f ∘ D) 0 =
      (iteratedFDeriv ℝ k f (D 0)).compContinuousLinearMap fun _ => D := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := k) le_rfl (by simp)
  obtain ⟨v, hvu, hvo, hv0⟩ := mem_nhds_iff.mp hu
  have hcv : ContDiffOn ℝ k f v := hc.mono hvu
  have hop : IsOpen (D ⁻¹' v) := hvo.preimage D.continuous
  have h0 : (0 : E) ∈ D ⁻¹' v := hv0
  have key := D.iteratedFDerivWithin_comp_right (f := f) (s := v) hcv
    hvo.uniqueDiffOn hop.uniqueDiffOn (x := 0) hv0 (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hop h0, iteratedFDerivWithin_of_isOpen k hvo hv0] at key
  exact key
abbrev _root_.YangMills.SharedProofs.p19667 := @iteratedFDeriv_comp_continuousLinearMap_zero
private theorem perturb_smul {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (lam σ : Fin k → ℝ) (W : TorusField n) :
    perturb c (fun l => lam l • X l) σ W = perturb c X (fun l => lam l * σ l) W := by
  funext x i
  simp only [perturb]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [smul_smul, mul_comm]
  · rfl
abbrev _root_.YangMills.SharedProofs.p106687 := @perturb_smul
private theorem mixedDeriv_smul {k : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (lam : Fin k → ℝ)
    (hs : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv G W c (fun l => lam l • X l) = (∏ l, lam l) * mixedDeriv G W c X := by
  let D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => lam l • ContinuousLinearMap.proj l
  have hD : ∀ σ l, D σ l = lam l * σ l := fun σ l => by simp [D]
  have hD0 : D 0 = 0 := map_zero D
  have hf : (fun σ : Fin k → ℝ => G (perturb c (fun l => lam l • X l) σ W)) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) ∘ D := by
    funext σ
    simp only [Function.comp]
    rw [perturb_smul]
    congr 2
  have hs' : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) (D 0) := by rwa [hD0]
  unfold mixedDeriv
  rw [hf, iteratedFDeriv_comp_continuousLinearMap_zero _ D hs', hD0]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun l => (fun _ : Fin k => (D : (Fin k → ℝ) → (Fin k → ℝ))) l (Pi.single l 1 : Fin k → ℝ)) =
      fun l => lam l • (Pi.single l 1 : Fin k → ℝ) := by
    funext l
    funext j
    simp only []
    rw [hD]
    by_cases h : j = l
    · subst h
      simp
    · simp [h]
  erw [hv, ContinuousMultilinearMap.map_smul_univ]
  simp
abbrev _root_.YangMills.DeltaSharedProofs.p501338 := @mixedDeriv_smul
private theorem mixedDeriv_pair_smul (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 2 → TorusBond n)
    (X X' : imaginaryQuaternions) (a a' : ℝ)
    (hs : ContDiffAt ℝ (2 : ℕ) (fun σ : Fin 2 → ℝ => G (perturb c ![X, X'] σ W)) 0) :
    mixedDeriv G W c ![a • X, a' • X'] = a * a' * mixedDeriv G W c ![X, X'] := by
  have h := mixedDeriv_smul G W c ![X, X'] ![a, a'] hs
  have e : (fun l => (![a, a'] : Fin 2 → ℝ) l • (![X, X'] : Fin 2 → imaginaryQuaternions) l) =
      ![a • X, a' • X'] := by
    funext l
    fin_cases l <;> rfl
  rw [e] at h
  rw [h, Fin.prod_univ_two]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502158 := @mixedDeriv_pair_smul
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem exists_smul_unit (X : imaginaryQuaternions) :
    ∃ (a : ℝ) (X₀ : imaginaryQuaternions), ‖X₀‖ = 1 ∧ X = a • X₀ := by
  by_cases h : X = 0
  · exact ⟨0, quaternionI, norm_quaternionI, by simp [h]⟩
  · have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨‖X‖, ‖X‖⁻¹ • X, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
private theorem bondOffsetInBox_of_offsetNorm (c : LatticeBond) {m : ℕ} (hm : offsetNorm c.1 + 1 ≤ m) :
    BondOffsetInBox m c := by
  have hi : ∀ i, (c.1 i).natAbs ≤ offsetNorm c.1 := fun i =>
    Finset.le_sup (f := fun i => (c.1 i).natAbs) (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := hi i
    rw [abs_le]
    omega
  · have := hi i
    have h1 : |(Pi.single c.2 (1 : ℤ) : Fin 4 → ℤ) i| ≤ 1 := by
      by_cases h : i = c.2
      · subst h
        simp
      · simp [h]
    rw [abs_le] at h1 ⊢
    simp only [Pi.add_apply]
    omega
abbrev _root_.YangMills.DeltaSharedProofs.p501634 := @bondOffsetInBox_of_offsetNorm
abbrev _root_.YangMills.SharedProofs.p38965 := @bondOffsetInBox_of_offsetNorm
private theorem bondFrom_zero_pair (N : ℕ) (c c' : LatticeBond) :
    (fun l => bondFrom (0 : TorusSite N) ((![c, c'] : Fin 2 → LatticeBond) l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
  funext l
  fin_cases l <;> rfl
private theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (h : ‖X‖ = 1) (h' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by
  intro l
  fin_cases l
  · exact h
  · exact h'
abbrev _root_.YangMills.SharedProofs.p1051 := @areUnitVectors_pair
private theorem tendsto_mul_exp_neg {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun m : ℕ => C * Real.exp (-(c * m))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => c * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h2 : Tendsto (fun m : ℕ => Real.exp (-(c * m))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  simpa using h2.const_mul C
abbrev _root_.YangMills.SharedProofs.p101442 := @tendsto_mul_exp_neg
private theorem hasLimitSecondDeriv_of_bounds {s c C : ℝ} {ℓ : StepParameters} {h : LocalDensity}
    (hs : 0 < s) (hc : 0 < c) (hB : HasStepDensityBounds s ℓ c C h) : HasLimitSecondDeriv h := by
  intro b b' X X'
  obtain ⟨a, X₀, hX₀, rfl⟩ := exists_smul_unit X
  obtain ⟨a', X₀', hX₀', rfl⟩ := exists_smul_unit X'
  have hC : CauchySeq fun n : ℕ =>
      mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X₀, X₀'] := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h1 : ∀ᶠ m : ℕ in atTop, C * Real.exp (-(c * m)) < ε :=
      (tendsto_mul_exp_neg hc C).eventually (gt_mem_nhds hε)
    obtain ⟨M, hM, hM'⟩ := (h1.and (eventually_ge_atTop (offsetNorm b.1 + offsetNorm b'.1 + 1))).exists
    refine ⟨max 64 (2 * M + 3), fun n hn n' hn' => ?_⟩
    have a1 := le_max_left 64 (2 * M + 3)
    have a2 := le_max_right 64 (2 * M + 3)
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero n' := ⟨by omega⟩
    rw [Real.dist_eq]
    have key := hB.local_comparison n n' (show 64 ≤ n by omega) (show 64 ≤ n' by omega) 0 0
      (trivialField n) (trivialField n') M
      (by omega) (by omega) (isCold_trivialField hs n) (isCold_trivialField hs n') (fun _ _ => rfl) 2
      ![b, b'] ![X₀, X₀'] le_rfl
      (by
        intro l
        fin_cases l
        · exact bondOffsetInBox_of_offsetNorm (m := M) b (by omega)
        · exact bondOffsetInBox_of_offsetNorm (m := M) b' (by omega))
      (areUnitVectors_pair hX₀ hX₀')
    rw [bondFrom_zero_pair, bondFrom_zero_pair] at key
    exact lt_of_le_of_lt key hM
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨a * a' * v, (hv.const_mul (a * a')).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 64] with n hn
  haveI : NeZero n := ⟨by omega⟩
  exact (mixedDeriv_pair_smul _ _ _ _ _ _ _
    (hB.analyticAt n hn 0 (trivialField n) (isCold_trivialField hs n) 2 _ _).contDiffAt).symm
private theorem isLocalGaugeDensity_of_bounds {s c C : ℝ} {ℓ : StepParameters} {h : LocalDensity}
    (hs : 0 < s) (hc : 0 < c) (hB : HasStepDensityBounds s ℓ c C h) : IsLocalGaugeDensity h where
  contDiffAt := by
    filter_upwards [eventually_ge_atTop 64] with n hn y k b X
    haveI : NeZero n := ⟨by omega⟩
    exact (hB.analyticAt n hn y (trivialField n) (isCold_trivialField hs n) k b X).contDiffAt
  gauge_invariant := by
    filter_upwards [eventually_ge_atTop 64] with n hn y
    haveI : NeZero n := ⟨by omega⟩
    have h1 : Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n => p.2)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually (eventually_isCold_nhds_trivial hs)] with p hp
    exact hB.admissible.gauge n hn y p.1 p.2 hp
  translation_invariant := by
    filter_upwards [eventually_ge_atTop 64] with n hn y u
    haveI : NeZero n := ⟨by omega⟩
    filter_upwards [eventually_isCold_nhds_trivial hs] with V hV
    exact hB.admissible.translation n hn y u V hV
  kernel_decay := by
    refine ⟨C, c, hc, ?_⟩
    filter_upwards [eventually_ge_atTop 64] with n hn b b' X X' hX hX'
    haveI : NeZero n := ⟨by omega⟩
    exact hB.decay n hn 0 (trivialField n) (isCold_trivialField hs n) 2 ![b, b'] ![X, X']
      (by norm_num) (by norm_num) (areUnitVectors_pair hX hX')
  tendsto := hasLimitSecondDeriv_of_bounds hs hc hB
end StepDensityIsLocal
open StepDensityIsLocal in
theorem StepDensityIsLocal.holds (hD : StepDensityBoundsAtFixedParameters) (hS : StepTotalEqDensitySum) :
    StepDensityIsLocal.Claim := by
  obtain ⟨rt₀, cD, -, hc, H⟩ := hD
  intro T hT t
  obtain ⟨C, -, hB, -⟩ := H T hT
  have hσ := hT.σ_pos
  have hσ' : 0 < 9 / 8 * T.threshold := by positivity
  refine ⟨isLocalGaugeDensity_of_bounds hσ (hc _) (hB T.floorMin t le_rfl), ?_⟩
  filter_upwards [eventually_ge_atTop 64] with n hn
  haveI : NeZero n := ⟨by omega⟩
  filter_upwards [eventually_isCold_nhds_trivial hσ'] with V hV
  exact hS T hT t n V hn hV
end YangMills.Construction.RunningCouplingSlope
end
