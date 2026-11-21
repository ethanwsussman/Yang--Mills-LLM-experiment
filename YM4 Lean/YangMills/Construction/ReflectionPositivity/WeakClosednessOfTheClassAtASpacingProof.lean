import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.WeakLimitsOfStatesAndACriterionForErgodicity
import YangMills.Construction.ReflectionPositivity.DecayAndLawAtASpacing
import YangMills.Construction.ReflectionPositivity.FunctionsOfTheBondsInASet
import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslation
import YangMills.Construction.ReflectionPositivity.ReflectionSizesAtASpacing
import YangMills.Construction.ReflectionPositivity.WeakClosednessOfTheClassAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ComplexConjugate ComplexOrder Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.WeakClosedMesh
open InfiniteLattice (GaugeField LatticePoint AmbientSpace IsBoundedObservable IsLocalObservable
  IsSymmetricUnder axisStep shift regionObservables observableSupNorm scaledCube plateauPairing
  longRangeOrderParameter)
open GibbsAtFixedSpacing (BorelProb linfNorm continuousLocal)
open LatticeAtSpacing (reflectionPositiveSet IsErgodicState)
open CoarseStepsInverseSquare (shiftedCorrelation cubeGap reflectionSize reflectionSizeRoots)
open SmearingFilter (spectralRateConst spectralRateFn)
variable {a : ℝ}
theorem continuous_actOn (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (ha : 0 < a) (s : InfiniteLattice.LatticeSymmetry a) {F : GaugeField a → ℂ}
    (ho : IsBoundedObservable F) (hc : Continuous F) : Continuous (s.actOn F) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := (hF a ha).2.2.1 s s
  exact h F ho hc
theorem tendstoWeak_mem_reflectionPositiveSet
    (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hW : LatticeAtSpacing.WeakLimitsAndErgodicity)
    (hS : HalfAndShift.HalfAndShiftStatement) (ha : 0 < a) {ν : ℕ → BorelProb a} {ρ : BorelProb a}
    (hν : ∀ i, ν i ∈ reflectionPositiveSet a) (hlim : BorelProb.TendstoWeak ν ρ) :
    ρ ∈ reflectionPositiveSet a := by
  obtain ⟨hinv, hform, -⟩ := hW a ha
  have hclass := (hS.1 a ha).2.2.1
  refine ⟨fun v => hinv ν ρ (shift v) hlim fun i => (hν i).1 v, fun P F hl hFP => ?_⟩
  have hρ : IsSymmetricUnder ρ.1 P.reflect :=
    hinv ν ρ P.reflect hlim fun i => hclass _ (hν i) P
  refine (hform P ρ hρ).2 (fun H hH hHP => ?_) F hl hFP
  obtain ⟨hc, ho, hloc⟩ := hH
  have hG : Continuous fun U => conj (P.reflect.actOn H U) * H U :=
    (Complex.continuous_conj.comp (continuous_actOn hF ha _ ho hc)).mul hc
  exact ge_of_tendsto' (hlim _ hG) fun i => (hν i).2 P H hloc hHP
theorem exists_mem_regionObservables_centeredCube (hB : RegionFunctions.RegionFunctionsStatement)
    (ha : 0 < a) {A : GaugeField a → ℂ} (ho : IsBoundedObservable A) (hl : IsLocalObservable A) :
    ∃ r : ℕ+, A ∈ regionObservables a (scaledCube a r) := by
  obtain ⟨S, hS, hm⟩ := hl
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  obtain ⟨m, hm'⟩ := exists_nat_gt (C / a)
  refine ⟨Nat.succPNat m, ?_⟩
  refine (hB a ha S _).2.1.1 ?_ ⟨ho, hm⟩
  rintro x ⟨hx, -⟩
  rw [LatticeAtSpacing.centeredCube_eq ha]
  change linfNorm x ≤ _
  unfold linfNorm
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have h₁ : |x μ| ≤ ‖x‖ := by simpa using norm_le_pi_norm x μ
  have h₂ : C < (m : ℝ) * a := (div_lt_iff₀ ha).1 hm'
  have h₃ : (m : ℝ) * a ≤ LatticeAtSpacing.cubeHalfWidth a (Nat.succPNat m) := by
    simp only [LatticeAtSpacing.cubeHalfWidth]
    have : ((Nat.succPNat m : ℕ+) : ℝ) = (m : ℝ) + 1 := by simp
    rw [this]
    nlinarith
  linarith [hC x hx]
theorem linfNorm_nsmul_axisStep (ha : 0 < a) (m : ℕ) :
    linfNorm ((m • axisStep a 0 : LatticePoint a) : AmbientSpace) = (m : ℝ) * a := by
  have hv : ∀ μ : Fin 4, ((m • axisStep a 0 : LatticePoint a) : AmbientSpace) μ =
      if μ = 0 then (m : ℝ) * a else 0 := by
    intro μ
    have h : ((m • axisStep a 0 : LatticePoint a) : AmbientSpace) =
        m • ((axisStep a 0 : LatticePoint a) : AmbientSpace) := rfl
    rw [h]
    by_cases hμ : μ = 0
    · subst hμ
      simp [axisStep]
    · simp [axisStep, hμ]
  have hnn : 0 ≤ (m : ℝ) * a := by positivity
  refine le_antisymm ?_ ?_
  · unfold linfNorm
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [hv]
    split_ifs
    · rw [abs_of_nonneg hnn]
    · simpa using hnn
  · calc (m : ℝ) * a = |((m • axisStep a 0 : LatticePoint a) : AmbientSpace) 0| := by
          rw [hv, if_pos rfl, abs_of_nonneg hnn]
      _ ≤ linfNorm ((m • axisStep a 0 : LatticePoint a) : AmbientSpace) :=
          Finset.le_sup' (fun μ : Fin 4 => |((m • axisStep a 0 : LatticePoint a) : AmbientSpace) μ|)
            (Finset.mem_univ (0 : Fin 4))
theorem cubeGap_nsmul_axisStep (ha : 0 < a) (r : ℕ+) (k : ℕ) :
    cubeGap a r ((k + 2 * (r : ℕ)) • axisStep a 0) = k := by
  simp only [cubeGap]
  rw [linfNorm_nsmul_axisStep ha]
  field_simp
  push_cast
  ring
theorem norm_shiftedCorrelation_sub_le (hZ : ReflectionSizeBoundsAtMesh)
    (hL : SpacingDecayAndLaw.Statement) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) {r : ℕ+} {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) {y : LatticePoint a} {k : ℕ} (hk : 1 ≤ k)
    (hy : cubeGap a r y = k) :
    ‖shiftedCorrelation ν A A y - plateauPairing ν.1 A A‖ ≤
      spectralRateFn (((r : ℕ) : ℝ) / (k : ℝ)) * observableSupNorm A ^ 2 := by
  obtain ⟨-, hlaw, -, hfar, -⟩ := hL a ha ν hν r A hA A hA 0
  obtain ⟨-, hcorr, hsemi, -, -⟩ := hZ a ha ν hν r
  have hq : 0 ≤ spectralRateFn (((r : ℕ) : ℝ) / (k : ℝ)) := by
    have hC : 0 ≤ spectralRateConst := hfar.1
    have hu : 0 ≤ ((r : ℕ) : ℝ) / (k : ℝ) := by positivity
    exact mul_nonneg hC (by positivity)
  have h₁ := hlaw y (by rw [hy]; exact_mod_cast hk)
  rw [hy] at h₁
  refine h₁.trans (mul_le_mul_of_nonneg_left ?_ hq)
  obtain ⟨-, -, -, -, hgreat, hnn, -⟩ := hcorr A hA
  have hs₀ : 0 ≤ reflectionSize ha ν r A :=
    (Complex.le_def.1 (hnn 0 1)).1.trans (hgreat.2 ⟨(0, 1), rfl⟩)
  have hs₁ : reflectionSize ha ν r A ≤ observableSupNorm A ^ 2 := (hsemi.2 A hA).2.2
  have hroots : reflectionSizeRoots ha ν r A A = reflectionSize ha ν r A := by
    simp only [reflectionSizeRoots]
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hs₀]
  rw [hroots]
  exact hs₁
theorem longRangeOrderParameter_eq_zero (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) (hZ : ReflectionSizeBoundsAtMesh)
    (hL : SpacingDecayAndLaw.Statement) (ha : 0 < a) {ν : ℕ → BorelProb a} {ρ : BorelProb a}
    (hν : ∀ i, ν i ∈ reflectionPositiveSet a ∧ IsErgodicState (ν i))
    (hρ : ρ ∈ reflectionPositiveSet a) (hlim : BorelProb.TendstoWeak ν ρ)
    {A : GaugeField a → ℂ} (hA : A ∈ continuousLocal a) :
    longRangeOrderParameter ρ.1 A = 0 := by
  obtain ⟨hc, ho, hl⟩ := hA
  obtain ⟨r, hAr⟩ := exists_mem_regionObservables_centeredCube hB ha ho hl
  have key : ∀ k : ℕ, 1 ≤ k → ‖longRangeOrderParameter ρ.1 A‖ ≤
      2 * (spectralRateFn (((r : ℕ) : ℝ) / (k : ℝ)) * observableSupNorm A ^ 2) := by
    intro k hk
    have hy := cubeGap_nsmul_axisStep ha r k
    set y : LatticePoint a := (k + 2 * (r : ℕ)) • axisStep a 0 with hydef
    have hG : Continuous fun U => conj (A U) * (shift y).actOn A U :=
      (Complex.continuous_conj.comp hc).mul (continuous_actOn hF ha _ ho hc)
    have hb : ∀ i, ‖(ν i).integral (fun U => conj (A U) * (shift y).actOn A U) -
        conj ((ν i).integral A) * (ν i).integral A‖ ≤
          spectralRateFn (((r : ℕ) : ℝ) / (k : ℝ)) * observableSupNorm A ^ 2 := by
      intro i
      have h := norm_shiftedCorrelation_sub_le hZ hL ha (hν i).1 hAr hk hy
      rwa [(hL a ha (ν i) (hν i).1 r A hAr A hAr 0).2.2.2.2 (hν i).2] at h
    have hlimit := ((hlim _ hG).sub
      (((Complex.continuous_conj.tendsto _).comp (hlim A hc)).mul (hlim A hc))).norm
    have h₁ := le_of_tendsto' hlimit hb
    have h₂ := norm_shiftedCorrelation_sub_le hZ hL ha hρ hAr hk hy
    have heq : longRangeOrderParameter ρ.1 A =
        (ρ.integral (fun U => conj (A U) * (shift y).actOn A U) -
          conj (ρ.integral A) * ρ.integral A) -
        (shiftedCorrelation ρ A A y - plateauPairing ρ.1 A A) := by
      have hz : conj (ρ.integral A) * ρ.integral A = ((‖ρ.integral A‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        push_cast
        rfl
      have e₁ : longRangeOrderParameter ρ.1 A =
          plateauPairing ρ.1 A A - ((‖ρ.integral A‖ ^ 2 : ℝ) : ℂ) := rfl
      have e₂ : shiftedCorrelation ρ A A y =
          ρ.integral (fun U => conj (A U) * (shift y).actOn A U) := rfl
      rw [hz, e₁, e₂]
      ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hu : Tendsto (fun k : ℕ => ((r : ℕ) : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hq : Continuous spectralRateFn := by
    unfold spectralRateFn
    fun_prop
  have hq₀ : spectralRateFn 0 = 0 := by simp [spectralRateFn]
  have hlimit : Tendsto (fun k : ℕ =>
      2 * (spectralRateFn (((r : ℕ) : ℝ) / (k : ℝ)) * observableSupNorm A ^ 2)) atTop (𝓝 0) := by
    have h := ((hq.tendsto 0).comp hu).mul_const (observableSupNorm A ^ 2) |>.const_mul 2
    simpa [hq₀, Function.comp_def] using h
  have hle : ‖longRangeOrderParameter ρ.1 A‖ ≤ 0 :=
    ge_of_tendsto hlimit ((eventually_ge_atTop 1).mono key)
  exact norm_le_zero_iff.1 hle
theorem weakClosedEveryMesh_holds (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hW : LatticeAtSpacing.WeakLimitsAndErgodicity)
    (hS : HalfAndShift.HalfAndShiftStatement) (hB : RegionFunctions.RegionFunctionsStatement)
    (hZ : ReflectionSizeBoundsAtMesh) (hL : SpacingDecayAndLaw.Statement) :
    WeakClosedEveryMesh := by
  intro a ha
  obtain ⟨-, -, -, hmet, -⟩ := (hF a ha).1
  have := hmet
  have hseq : ∀ (ν : ℕ → BorelProb a) (ρ : BorelProb a), Tendsto ν atTop (𝓝 ρ) →
      BorelProb.TendstoWeak ν ρ := fun ν ρ h =>
    (LatticeAtSpacing.tendsto_nhds_iff_tendstoWeak ν ρ).1 h
  refine ⟨IsSeqClosed.isClosed fun ν ρ hν h =>
      tendstoWeak_mem_reflectionPositiveSet hF hW hS ha hν (hseq ν ρ h),
    IsSeqClosed.isClosed fun ν ρ hν h => ?_⟩
  have hlim := hseq ν ρ h
  have hρ := tendstoWeak_mem_reflectionPositiveSet hF hW hS ha (fun i => (hν i).1) hlim
  obtain ⟨hsub, -, -, -, hdense, -⟩ := (hF a ha).2.1
  exact ⟨hρ, (hW a ha).2.2 ρ (continuousLocal a) hρ.1 hsub hdense fun A hA =>
    longRangeOrderParameter_eq_zero hF hB hZ hL ha hν hρ hlim hA⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures.WeakClosedMesh
