import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStripProof
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluations
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.ScaledNormsOfSmallIteratesAtTheSideInfinity
import YangMills.Construction.Towers.StepKernelsOfTheIteratedAveragesAtTheSideInfinity
import YangMills.Construction.Towers.StepsOfTheIteratedAveragesNearTheFreeStepsAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RescaledNormBounds
open Matrices
open PeriodicOperators
open PeriodicOperators.Quotients (finiteNormSpace)
open SmoothingContraction (OpNormLE)
open IterStepsNearFree (edgeStepKernel vertexStepKernel)
section Norms
variable {J : Type}
theorem normSummable_iff {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (f : J → ℂ) :
    NormSummable w f ↔ Summable fun i => w i * ‖f i‖ ^ 2 := by
  unfold NormSummable
  have e : (fun i => |w i * ‖f i‖ ^ 2|) = fun i => w i * ‖f i‖ ^ 2 := by
    funext i
    exact abs_of_nonneg (mul_nonneg (hw i) (sq_nonneg _))
  rw [e]
theorem normSummable_add_and_wNorm_add_le {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) {f g : J → ℂ}
    (hf : NormSummable w f) (hg : NormSummable w g) :
    NormSummable w (f + g) ∧ wNorm w (f + g) ≤ wNorm w f + wNorm w g := by
  rw [normSummable_iff hw] at hf hg
  set u : J → ℝ := fun i => Real.sqrt (w i) * ‖f i‖ with hu
  set v : J → ℝ := fun i => Real.sqrt (w i) * ‖g i‖ with hv
  have hu0 : ∀ i, 0 ≤ u i := fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hv0 : ∀ i, 0 ≤ v i := fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have eu : ∀ i, u i ^ (2 : ℝ) = w i * ‖f i‖ ^ 2 := fun i => by
    rw [Real.rpow_two, hu]
    simp only [mul_pow, Real.sq_sqrt (hw i)]
  have ev : ∀ i, v i ^ (2 : ℝ) = w i * ‖g i‖ ^ 2 := fun i => by
    rw [Real.rpow_two, hv]
    simp only [mul_pow, Real.sq_sqrt (hw i)]
  have su : Summable fun i => u i ^ (2 : ℝ) := by simpa only [eu] using hf
  have sv : Summable fun i => v i ^ (2 : ℝ) := by simpa only [ev] using hg
  obtain ⟨h₁, h₂⟩ := Real.Lp_add_le_tsum_of_nonneg (p := 2) (by norm_num) hu0 hv0 su sv
  have le : ∀ i, w i * ‖(f + g) i‖ ^ 2 ≤ (u i + v i) ^ (2 : ℝ) := fun i => by
    have e : (u i + v i) ^ (2 : ℝ) = w i * (‖f i‖ + ‖g i‖) ^ 2 := by
      rw [Real.rpow_two, hu, hv]
      simp only
      rw [← mul_add, mul_pow, Real.sq_sqrt (hw i)]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (hw i)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have s : Summable fun i => w i * ‖(f + g) i‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (sq_nonneg _)) le h₁
  refine ⟨(normSummable_iff hw _).2 s, ?_⟩
  have t : ∑' i, w i * ‖(f + g) i‖ ^ 2 ≤ ∑' i, (u i + v i) ^ (2 : ℝ) := s.tsum_le_tsum le h₁
  have e₁ : wNorm w f = (∑' i, u i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    unfold wNorm
    rw [Real.sqrt_eq_rpow]
    simp only [eu]
  have e₂ : wNorm w g = (∑' i, v i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    unfold wNorm
    rw [Real.sqrt_eq_rpow]
    simp only [ev]
  rw [e₁, e₂]
  refine le_trans ?_ h₂
  unfold wNorm
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow (tsum_nonneg fun i => mul_nonneg (hw i) (sq_nonneg _)) t (by norm_num)
theorem normSummable_smul {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (z : ℂ) {f : J → ℂ}
    (hf : NormSummable w f) : NormSummable w (z • f) := by
  rw [normSummable_iff hw] at hf ⊢
  refine (hf.mul_left (‖z‖ ^ 2)).congr fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring
theorem wNorm_smul (w : J → ℝ) (z : ℂ) (f : J → ℂ) :
    wNorm w (z • f) = ‖z‖ * wNorm w f := by apply _root_.YangMills.SharedProofs.p112894 <;> assumption
theorem eq_zero_of_wNorm_eq_zero {w : J → ℝ} (hw : ∀ i, 0 < w i) {f : J → ℂ}
    (hf : NormSummable w f) (h : wNorm w f = 0) : f = 0 := by
  have hw' : ∀ i, 0 ≤ w i := fun i => (hw i).le
  rw [normSummable_iff hw'] at hf
  have h₀ : ∀ i, 0 ≤ w i * ‖f i‖ ^ 2 := fun i => mul_nonneg (hw' i) (sq_nonneg _)
  have h₁ : ∑' i, w i * ‖f i‖ ^ 2 = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.1 h) (tsum_nonneg h₀)
  have h₂ := (hasSum_zero_iff_of_nonneg h₀).1 (h₁ ▸ hf.hasSum)
  funext i
  have h₃ := congrFun h₂ i
  simp only [Pi.zero_apply] at h₃ ⊢
  have h₄ : ‖f i‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h₃ with h₅ | h₅
    · exact absurd h₅ (hw i).ne'
    · exact h₅
  simpa using h₄
theorem applyKernel_smul {J' : Type} (T : J' → J → ℂ) (z : ℂ) (f : J → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_smul <;> assumption
theorem applyKernel_add_kernel {J' : Type} {T S : J' → J → ℂ} {f : J → ℂ}
    (hT : ∀ x', ApplySummableAt T f x') (hS : ∀ x', ApplySummableAt S f x') :
    applyKernel (T + S) f = applyKernel T f + applyKernel S f := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.applyKernel_add_kernel <;> assumption
end Norms
section Kernels
variable {I I' : PeriodicData} {T S : I'.Carrier → I.Carrier → ℂ} {c c' : ℝ}
theorem applyKernel_wNorm_le (hw : ∀ x, 0 < I.weightOf x) (hc : 0 ≤ c)
    (h : OpNormLE I I' T c) {f : I.Carrier → ℂ} (hf : NormSummable I.weightOf f) :
    NormSummable I'.weightOf (applyKernel T f) ∧
      wNorm I'.weightOf (applyKernel T f) ≤ c * wNorm I.weightOf f := by
  refine ⟨(h.1 f hf).2, ?_⟩
  rcases eq_or_ne (wNorm I.weightOf f) 0 with h₀ | h₀
  · have : f = 0 := eq_zero_of_wNorm_eq_zero hw hf h₀
    subst this
    have e : applyKernel T (0 : I.Carrier → ℂ) = 0 := by
      funext x'
      simp [applyKernel]
    rw [e]
    simp [wNorm]
  · have hn : 0 < wNorm I.weightOf f := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h₀)
    set n := wNorm I.weightOf f with hn'
    have hz : ‖((n⁻¹ : ℝ) : ℂ)‖ = n⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hn.le)]
    have hu : ((n⁻¹ : ℝ) : ℂ) • f ∈ wUnitBall I.weightOf (finiteNormSpace I) := by
      have hf' := normSummable_smul (fun x => (hw x).le) ((n⁻¹ : ℝ) : ℂ) hf
      refine ⟨hf', hf', ?_⟩
      rw [wNorm_smul, hz, ← hn', inv_mul_cancel₀ hn.ne']
    have h₁ : ENNReal.ofReal (wNorm I'.weightOf (applyKernel T (((n⁻¹ : ℝ) : ℂ) • f))) ≤
        ENNReal.ofReal c :=
      le_trans (le_iSup₂ (f := fun f (_ : f ∈ wUnitBall I.weightOf (finiteNormSpace I)) =>
        ENNReal.ofReal (wNorm I'.weightOf (applyKernel T f))) _ hu) h.2.2
    have h₂ := (ENNReal.ofReal_le_ofReal_iff hc).1 h₁
    rw [applyKernel_smul, wNorm_smul, hz] at h₂
    have h₃ := mul_le_mul_of_nonneg_left h₂ hn.le
    rwa [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_comm n c] at h₃
theorem add_applyKernel_wNorm_le (hw : ∀ x, 0 < I.weightOf x) (hw' : ∀ x, 0 ≤ I'.weightOf x)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hT : OpNormLE I I' T c) (hS : OpNormLE I I' S c')
    {f : I.Carrier → ℂ} (hf : NormSummable I.weightOf f) :
    NormSummable I'.weightOf (applyKernel T f + applyKernel S f) ∧
      wNorm I'.weightOf (applyKernel T f + applyKernel S f) ≤
        (c + c') * wNorm I.weightOf f := by
  obtain ⟨a₁, a₂⟩ := applyKernel_wNorm_le hw hc hT hf
  obtain ⟨b₁, b₂⟩ := applyKernel_wNorm_le hw hc' hS hf
  obtain ⟨d₁, d₂⟩ := normSummable_add_and_wNorm_add_le hw' a₁ b₁
  refine ⟨d₁, d₂.trans ?_⟩
  rw [add_mul]
  exact add_le_add a₂ b₂
theorem opNormLE_of_forall (hc : 0 ≤ c)
    (hact : ∀ f, NormSummable I.weightOf f → ∀ x', ApplySummableAt T f x')
    (hb' : ∀ f, NormSummable I.weightOf f → ∃ g : I'.Carrier → ℂ, applyKernel T f = g ∧
      NormSummable I'.weightOf g ∧ wNorm I'.weightOf g ≤ c * wNorm I.weightOf f) :
    OpNormLE I I' T c := by
  have hb : ∀ f, NormSummable I.weightOf f → NormSummable I'.weightOf (applyKernel T f) ∧
      wNorm I'.weightOf (applyKernel T f) ≤ c * wNorm I.weightOf f := fun f hf => by
    obtain ⟨g, e, h₁, h₂⟩ := hb' f hf
    rw [e]
    exact ⟨h₁, h₂⟩
  refine ⟨fun f hf => ⟨hact f hf, (hb f hf).1⟩, fun f hf => (hb f hf.1).1, ?_⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  calc wNorm I'.weightOf (applyKernel T f)
      ≤ c * wNorm I.weightOf f := (hb f hf.1).2
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hf.2.2 hc
    _ = c := mul_one c
end Kernels
section Chains
variable (I : ℕ → PeriodicData) (M : ∀ j, ((I j).Carrier → ℂ) → (I (j + 1)).Carrier → ℂ)
def composeUpTo (f : (I 0).Carrier → ℂ) : ∀ j, (I j).Carrier → ℂ
  | 0 => f
  | j + 1 => M j (composeUpTo f j)
variable {I M}
theorem composeUpTo_wNorm_le {k : ℕ} {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    (H : ∀ j < k, ∀ f, NormSummable (I j).weightOf f →
      NormSummable (I (j + 1)).weightOf (M j f) ∧
        wNorm (I (j + 1)).weightOf (M j f) ≤ c j * wNorm (I j).weightOf f)
    {f : (I 0).Carrier → ℂ} (hf : NormSummable (I 0).weightOf f) :
    ∀ j ≤ k, NormSummable (I j).weightOf (composeUpTo I M f j) ∧
      wNorm (I j).weightOf (composeUpTo I M f j) ≤
        (∏ i ∈ Finset.range j, c i) * wNorm (I 0).weightOf f := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hf, by simp [composeUpTo]⟩
  | succ j ih =>
    intro hj
    obtain ⟨h₁, h₂⟩ := ih (by omega)
    obtain ⟨h₃, h₄⟩ := H j (by omega) _ h₁
    refine ⟨h₃, h₄.trans ?_⟩
    rw [Finset.prod_range_succ]
    calc c j * wNorm (I j).weightOf (composeUpTo I M f j)
        ≤ c j * ((∏ i ∈ Finset.range j, c i) * wNorm (I 0).weightOf f) :=
          mul_le_mul_of_nonneg_left h₂ (hc j)
      _ = _ := by ring
end Chains
section Numbers
variable {L : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem meshAt_succ (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    meshAt L k (j + 1) = L * meshAt L k j := by apply _root_.YangMills.SharedProofs.p23229 <;> assumption
theorem meshAt_self (k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem sum_meshAt_le (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    ∑ i ∈ Finset.range j, meshAt L k i ≤ meshAt L k j := by
  induction j with
  | zero => simpa using (meshAt_pos hL k 0).le
  | succ j ih =>
    rw [Finset.sum_range_succ, meshAt_succ hL]
    have h₁ := meshAt_pos hL k j
    have h₂ : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
    nlinarith
theorem prod_one_add_le_exp (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hA' : A ≤ 1 / 41) :
    ∏ j ∈ Finset.range k, (1 + C * (20 * meshAt L k j * A)) ≤ Real.exp (30 * C) := by
  have h₁ : ∏ j ∈ Finset.range k, (1 + C * (20 * meshAt L k j * A)) ≤
      ∏ j ∈ Finset.range k, Real.exp (C * (20 * meshAt L k j * A)) := by
    refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
    · have := meshAt_pos hL k j
      positivity
    · rw [add_comm]
      exact Real.add_one_le_exp _
  refine h₁.trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have e : ∑ j ∈ Finset.range k, C * (20 * meshAt L k j * A) =
      20 * C * A * ∑ j ∈ Finset.range k, meshAt L k j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have h₂ : ∑ j ∈ Finset.range k, meshAt L k j ≤ 1 :=
    (sum_meshAt_le hL k k).trans (meshAt_self k).le
  have h₃ : 0 ≤ ∑ j ∈ Finset.range k, meshAt L k j :=
    Finset.sum_nonneg fun j _ => (meshAt_pos hL k j).le
  have h₄ : 20 * C * A ≤ 20 * C * (1 / 41) := mul_le_mul_of_nonneg_left hA' (by positivity)
  calc 20 * C * A * ∑ j ∈ Finset.range k, meshAt L k j
      ≤ 20 * C * (1 / 41) * 1 :=
        mul_le_mul h₄ h₂ h₃ (by positivity)
    _ ≤ 30 * C := by nlinarith
end Numbers
section Coefficients
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (z : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (z • X) = z * pauliCoeff a X := by
  unfold pauliCoeff
  rw [dif_pos hX, dif_pos (Submodule.smul_mem _ z hX)]
  have e : (⟨z • X, Submodule.smul_mem _ z hX⟩ : ComplexMatrix2.traceless) = z • ⟨X, hX⟩ := rfl
  rw [e, map_smul]
  rfl
theorem real_smul_eq_ofReal_smul (z : ℝ) (X : ComplexMatrix2) : z • X = (z : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem real_smul_mem_traceless (z : ℝ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    z • X ∈ ComplexMatrix2.traceless := by
  rw [real_smul_eq_ofReal_smul]
  exact Submodule.smul_mem _ _ hX
theorem pauliCoeff_real_smul {z : ℝ} (hz : z ≠ 0) (X : ComplexMatrix2) (a : Fin 3) :
    pauliCoeff a (z • X) = (z : ℂ) * pauliCoeff a X := by
  by_cases hX : X ∈ ComplexMatrix2.traceless
  · rw [real_smul_eq_ofReal_smul]
    exact pauliCoeff_smul _ hX a
  · have h : z • X ∉ ComplexMatrix2.traceless := fun h => hX (by
      have := real_smul_mem_traceless z⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hz, one_smul] at this)
    unfold pauliCoeff
    rw [dif_neg hX, dif_neg h, mul_zero]
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (c + c') x = ofPauliCoeffs c x + ofPauliCoeffs c' x := by
  simp only [ofPauliCoeffs, Pi.add_apply, add_smul, Finset.sum_add_distrib]
theorem ofPauliCoeffs_smul {σ : Type} (z : ℂ) (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs (z • c) x = z • ofPauliCoeffs c x := by
  simp only [ofPauliCoeffs, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) : ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end Coefficients
section Forms
variable {L k j : ℕ}
theorem positive_or_opposite_positive {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    (b.IsPositivelyOriented ∧ ¬ b.opposite.IsPositivelyOriented) ∨
      (b.opposite.IsPositivelyOriented ∧ ¬ b.IsPositivelyOriented) := by
  rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
      fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
      fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
def formOfCoeffs (f : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) : Edge L k j → ComplexMatrix2 :=
  (edgePauliCoordinates L k j).ofCoeffs f
def coeffsOfForm (B : Edge L k j → ComplexMatrix2) : Fin 3 × PositiveEdge (meshAt L k j) → ℂ :=
  (edgePauliCoordinates L k j).coeffs B
def positiveValues (f : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) : Edge L k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0
theorem formOfCoeffs_apply_pos (f : Fin 3 × PositiveEdge (meshAt L k j) → ℂ)
    {b : Edge L k j} (h : b.IsPositivelyOriented) : formOfCoeffs f b = ofPauliCoeffs f ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_apply <;> assumption
theorem formOfCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    formOfCoeffs f ∈ complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_mem <;> assumption
theorem coeffsOfForm_formOfCoeffs (f : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    coeffsOfForm (formOfCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.FreeOperators.toPauliCoeffs_restrict_edgeValue <;> assumption
theorem formOfCoeffs_coeffsOfForm (hL : Conventions.IsAdmissibleBlockingFactor L)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    formOfCoeffs (coeffsOfForm B) = B := by
  have hpos : ∀ b (h : InfiniteLattice.Link.IsPositivelyOriented b),
      formOfCoeffs (coeffsOfForm B) b = B b := fun b h => by
    rw [formOfCoeffs_apply_pos _ h]
    exact sum_pauliCoeff_smul (hB.1 b h)
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact hpos b h
  · rcases positive_or_opposite_positive (meshAt_pos hL k j) b with ⟨h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd h₁ h
    · have r := (formOfCoeffs_mem hL (coeffsOfForm B)).2 b.opposite
      have r' : (InfiniteLattice.Link.opposite b).opposite = b := rfl
      rw [r'] at r
      rw [r, hpos _ h₁, hB.2 b, neg_neg]
end Forms
section Steps
variable {L k j : ℕ}
def EdgeStepIsLocal (L k j : ℕ) (V : Edge L k j → ComplexMatrix2) : Prop :=
  ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∃ (P : Finset (PositiveEdge (meshAt L k j)))
      (T : PositiveEdge (meshAt L k j) → ComplexMatrix2 → ComplexMatrix2),
      (∀ b ∈ P, ∀ X ∈ ComplexMatrix2.traceless, T b X ∈ ComplexMatrix2.traceless) ∧
      (∀ b ∈ P, ∀ X ∈ ComplexMatrix2.traceless, ∀ Y ∈ ComplexMatrix2.traceless,
        T b (X + Y) = T b X + T b Y) ∧
      (∀ b ∈ P, ∀ z : ℂ, ∀ X ∈ ComplexMatrix2.traceless, T b (z • X) = z • T b X) ∧
      ∀ B ∈ complexEdgeForms (meshAt L k j),
        covariantSmoothingDeriv V B c = ∑ b ∈ P, T b (B b.1)
def edgeStep (L k j : ℕ) (V : Edge L k j → ComplexMatrix2) :
    (Fin 3 × PositiveEdge (meshAt L k j) → ℂ) →
      Fin 3 × PositiveEdge (meshAt L k (j + 1)) → ℂ :=
  (edgePauliCoordinates L k j).mapOnCoeffs (edgePauliCoordinates L k (j + 1))
    fun B => (L : ℝ)⁻¹ • covariantSmoothingDeriv V B
theorem edgeStep_apply (V : Edge L k j → ComplexMatrix2) (f) (a : Fin 3)
    (c : PositiveEdge (meshAt L k (j + 1))) :
    edgeStep L k j V f (a, c) = pauliCoeff a
      ((L : ℝ)⁻¹ • covariantSmoothingDeriv V (formOfCoeffs f) c.1) := rfl
theorem covariantSmoothingDeriv_mem {V : Edge L k j → ComplexMatrix2}
    (R : EdgeStepIsLocal L k j V) {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c ∈ ComplexMatrix2.traceless := by
  obtain ⟨P, T, h₁, _, _, h₄⟩ := R c hc
  rw [h₄ B hB]
  exact Submodule.sum_mem _ fun b hb => h₁ b hb _ (hB.1 b.1 b.2)
theorem edgeStep_linear_local (hL : Conventions.IsAdmissibleBlockingFactor L)
    {V : Edge L k j → ComplexMatrix2} (R : EdgeStepIsLocal L k j V) :
    (∀ f g, edgeStep L k j V (f + g) = edgeStep L k j V f + edgeStep L k j V g) ∧
    (∀ (z : ℂ) f, edgeStep L k j V (z • f) = z • edgeStep L k j V f) ∧
    ∀ x', ∃ A : Finset (Fin 3 × PositiveEdge (meshAt L k j)), ∀ f g,
      (∀ x ∈ A, f x = g x) → edgeStep L k j V f x' = edgeStep L k j V g x' := by
  have hz : ((L : ℝ)⁻¹) ≠ 0 := by
    have := hL.2
    have h : (L : ℝ) ≠ 0 := by
      have : L ≠ 0 := by omega
      exact_mod_cast this
    exact inv_ne_zero h
  have key : ∀ (a : Fin 3) (c : PositiveEdge (meshAt L k (j + 1))),
      ∃ (P : Finset (PositiveEdge (meshAt L k j)))
        (E : (Fin 3 × PositiveEdge (meshAt L k j) → ℂ) → ComplexMatrix2),
        (∀ f, E f ∈ ComplexMatrix2.traceless) ∧ (∀ f g, E (f + g) = E f + E g) ∧
        (∀ (z : ℂ) f, E (z • f) = z • E f) ∧
        (∀ f g, (∀ b ∈ P, ∀ a', f (a', b) = g (a', b)) → E f = E g) ∧
        ∀ f, edgeStep L k j V f (a, c) = (((L : ℝ)⁻¹ : ℝ) : ℂ) * pauliCoeff a (E f) := by
    intro a c
    obtain ⟨P, T, h₁, h₂, h₃, h₄⟩ := R c.1 c.2
    refine ⟨P, fun f => ∑ b ∈ P, T b (ofPauliCoeffs f b), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun f => Submodule.sum_mem _ fun b hb => h₁ b hb _ (ofPauliCoeffs_mem _ _)
    · intro f g
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [ofPauliCoeffs_add, h₂ b hb _ (ofPauliCoeffs_mem _ _) _ (ofPauliCoeffs_mem _ _)]
    · intro z f
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [ofPauliCoeffs_smul, h₃ b hb _ _ (ofPauliCoeffs_mem _ _)]
    · intro f g h
      refine Finset.sum_congr rfl fun b hb => ?_
      have : ofPauliCoeffs f b = ofPauliCoeffs g b := by
        simp only [ofPauliCoeffs, h b hb]
      rw [this]
    · intro f
      rw [edgeStep_apply, pauliCoeff_real_smul hz, h₄ _ (formOfCoeffs_mem hL f)]
      congr 2
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [formOfCoeffs_apply_pos f b.2]
  refine ⟨fun f g => ?_, fun z f => ?_, fun x' => ?_⟩
  · funext ⟨a, c⟩
    obtain ⟨P, E, e₁, e₂, _, _, e₅⟩ := key a c
    simp only [Pi.add_apply, e₅]
    rw [e₂, pauliCoeff_add (e₁ f) (e₁ g), mul_add]
  · funext ⟨a, c⟩
    obtain ⟨P, E, e₁, _, e₃, _, e₅⟩ := key a c
    simp only [Pi.smul_apply, e₅, smul_eq_mul]
    rw [e₃, pauliCoeff_smul _ (e₁ f)]
    ring
  · obtain ⟨a, c⟩ := x'
    obtain ⟨P, E, _, _, _, e₄, e₅⟩ := key a c
    refine ⟨Finset.univ ×ˢ P, fun f g h => ?_⟩
    rw [e₅, e₅, e₄ f g fun b hb a' => h (a', b) (by simp [hb])]
def deltaFunction {P : Type} (x : Fin 3 × P) : Fin 3 × P → ℂ := open Classical in Pi.single x 1
theorem basisFunction_eq_deltaFunction {P : Type} (x : Fin 3 × P) :
    ((basisFunction x : finsuppFunctions (Fin 3 × P)) : Fin 3 × P → ℂ) = deltaFunction x := by
  classical
  funext x'
  simp [basisFunction, deltaFunction, Pi.single_apply]
end Steps
section Bounds
variable {L k j : ℕ}
theorem colourEdges_weight_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ)
    (x : (colourEdges L k j).Carrier) : 0 < (colourEdges L k j).weightOf x :=
  pow_pos (meshAt_pos hL k j) 4
theorem colourVertices_weight_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ)
    (x : (colourVertices L k j).Carrier) : 0 < (colourVertices L k j).weightOf x :=
  pow_pos (meshAt_pos hL k j) 4
def freeEdgeKernel (L k j : ℕ) :
    (colourEdges L k (j + 1)).Carrier → (colourEdges L k j).Carrier → ℂ :=
  (edgePauliCoordinates L k j).kernelOfBasisImages (edgePauliCoordinates L k (j + 1)) fun B =>
    (L : ℝ)⁻¹ • crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j) B
def freeVertexKernel (L k j : ℕ) :
    (colourVertices L k (j + 1)).Carrier → (colourVertices L k j).Carrier → ℂ :=
  (vertexCoordinate (Vertex L k j)).kernelOfBasisImages (vertexCoordinate (Vertex L k (j + 1)))
    (vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j))
theorem edgeStep_delta (V : Edge L k j → ComplexMatrix2) (a : Fin 3)
    (d : PositiveEdge (meshAt L k (j + 1))) (x : Fin 3 × PositiveEdge (meshAt L k j)) :
    edgeStep L k j V (deltaFunction x) (a, d) = pauliCoeff a
      ((L : ℝ)⁻¹ • covariantSmoothingDeriv V (formOfCoeffs (deltaFunction x)) d.1) := rfl
theorem edgeStepKernel_apply (V : Edge L k j → ComplexMatrix2) (a : Fin 3)
    (d : PositiveEdge (meshAt L k (j + 1))) (x : Fin 3 × PositiveEdge (meshAt L k j)) :
    edgeStepKernel L k j V (a, d) x = pauliCoeff a
      (((L : ℝ)⁻¹ • (covariantSmoothingDeriv V (formOfCoeffs (deltaFunction x)) -
        crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
          (formOfCoeffs (deltaFunction x)))) d.1) := rfl
theorem freeEdgeKernel_apply (a : Fin 3)
    (d : PositiveEdge (meshAt L k (j + 1))) (x : Fin 3 × PositiveEdge (meshAt L k j)) :
    freeEdgeKernel L k j (a, d) x = pauliCoeff a
      (((L : ℝ)⁻¹ • crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
          (formOfCoeffs (deltaFunction x))) d.1) := rfl
theorem edgeStep_wNorm_le (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hF : OneStepComplexForms.OneStepClaim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (R : EdgeStepIsLocal L k j V) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hT : OpNormLE (colourEdges L k j) (colourEdges L k (j + 1)) (edgeStepKernel L k j V) c)
    (hS : OpNormLE (colourEdges L k j) (colourEdges L k (j + 1)) (freeEdgeKernel L k j) c')
    {f : (colourEdges L k j).Carrier → ℂ} (hf : NormSummable (colourEdges L k j).weightOf f) :
    NormSummable (colourEdges L k (j + 1)).weightOf (edgeStep L k j V f) ∧
      wNorm (colourEdges L k (j + 1)).weightOf (edgeStep L k j V f) ≤
        (c + c') * wNorm (colourEdges L k j).weightOf f := by
  obtain ⟨l₁, l₂, l₃⟩ := edgeStep_linear_local hL R
  have G := (hK _ _ (edgeStep L k j V) l₁ l₂ l₃).1
  have e : (fun (x' : Fin 3 × PositiveEdge (meshAt L k (j + 1)))
      (x : Fin 3 × PositiveEdge (meshAt L k j)) => edgeStep L k j V (basisFunction x).1 x') =
      edgeStepKernel L k j V + freeEdgeKernel L k j := by
    funext x' x
    obtain ⟨a, d⟩ := x'
    have hE := formOfCoeffs_mem (k := k) (j := j) hL (deltaFunction x)
    have hc₁ := covariantSmoothingDeriv_mem R d.2 hE
    have hc₂ : crossingSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (formOfCoeffs (deltaFunction x)) d.1 ∈ ComplexMatrix2.traceless :=
      ((hF L hL k j hj).crossingSmoothing_mapsTo hE).1 d.1 d.2
    simp only [basisFunction_eq_deltaFunction]
    show edgeStep L k j V (deltaFunction x) (a, d) =
      edgeStepKernel L k j V (a, d) x + freeEdgeKernel L k j (a, d) x
    rw [edgeStep_delta, edgeStepKernel_apply, freeEdgeKernel_apply]
    simp only [Pi.smul_apply, Pi.sub_apply]
    rw [← pauliCoeff_add (real_smul_mem_traceless _ (Submodule.sub_mem _ hc₁ hc₂))
      (real_smul_mem_traceless _ hc₂), ← smul_add, sub_add_cancel]
  have e' := (G f).2
  rw [e] at e'
  have e'' := applyKernel_add_kernel (hT.1 f hf).1 (hS.1 f hf).1
  have e₃ := e''.symm.trans e'
  rw [← e₃]
  exact add_applyKernel_wNorm_le (colourEdges_weight_pos hL k j)
    (fun x => (colourEdges_weight_pos hL k (j + 1) x).le) hc hc' hT hS hf
def vertexStep (L k j : ℕ) (V : Edge L k j → ComplexMatrix2) :
    (Fin 3 × Vertex L k j → ℂ) → Fin 3 × Vertex L k (j + 1) → ℂ :=
  (vertexCoordinate (Vertex L k j)).mapOnCoeffs (vertexCoordinate (Vertex L k (j + 1)))
    (adjointCubeAverage V)
theorem vertexStep_apply (V : Edge L k j → ComplexMatrix2) (f) (a : Fin 3)
    (y : Vertex L k (j + 1)) :
    vertexStep L k j V f (a, y) = pauliCoeff a (adjointCubeAverage V (ofPauliCoeffs f) y) :=
  rfl
theorem vertexStep_linear_local (hLin : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j)
    (hfin : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite) :
    (∀ f g, vertexStep L k j V (f + g) = vertexStep L k j V f + vertexStep L k j V g) ∧
    (∀ (z : ℂ) f, vertexStep L k j V (z • f) = z • vertexStep L k j V f) ∧
    ∀ x', ∃ A : Finset (Fin 3 × Vertex L k j), ∀ f g,
      (∀ x ∈ A, f x = g x) → vertexStep L k j V f x' = vertexStep L k j V g x' := by
  obtain ⟨-, -, hC, hD⟩ := hLin L hL k j hj V hV
  have hm := fun f : Fin 3 × Vertex L k j → ℂ => ofPauliCoeffs_mem (σ := Vertex L k j) f
  have hz : adjointCubeAverage V (0 : Vertex L k j → ComplexMatrix2) = 0 := by
    have h := (hD 0 0 (fun _ => Submodule.zero_mem _) (fun _ => Submodule.zero_mem _) 1).2
    simpa using h
  refine ⟨fun f g => ?_, fun z f => ?_, fun x' => ?_⟩
  · funext ⟨a, y⟩
    have e : ofPauliCoeffs (f + g) = (1 : ℂ) • ofPauliCoeffs f + ofPauliCoeffs g := by
      funext x
      simp [ofPauliCoeffs_add]
    have h := (hD _ _ (hm f) (hm g) 1).2
    rw [one_smul] at h
    simp only [Pi.add_apply, vertexStep_apply]
    rw [e, (hD _ _ (hm f) (hm g) 1).2, one_smul]
    exact pauliCoeff_add ((hC _ (hm f)).2 y) ((hC _ (hm g)).2 y) a
  · funext ⟨a, y⟩
    have e : ofPauliCoeffs (z • f) = z • ofPauliCoeffs f + 0 := by
      funext x
      simp [ofPauliCoeffs_smul]
    simp only [Pi.smul_apply, vertexStep_apply, smul_eq_mul]
    rw [e, (hD _ 0 (hm f) (fun _ => Submodule.zero_mem _) z).2, hz, add_zero]
    exact pauliCoeff_smul z ((hC _ (hm f)).2 y) a
  · obtain ⟨a, y⟩ := x'
    refine ⟨Finset.univ ×ˢ (hfin y).toFinset, fun f g h => ?_⟩
    simp only [vertexStep_apply]
    congr 1
    show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    have : ofPauliCoeffs f x = ofPauliCoeffs g x := by
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [h (a', x) (by simpa using hx)]
    rw [this]
theorem vertexStep_delta (V : Edge L k j → ComplexMatrix2) (a : Fin 3) (y : Vertex L k (j + 1))
    (x : Fin 3 × Vertex L k j) :
    vertexStep L k j V (deltaFunction x) (a, y) = pauliCoeff a
      (adjointCubeAverage V (ofPauliCoeffs (deltaFunction x)) y) := rfl
theorem vertexStepKernel_apply (V : Edge L k j → ComplexMatrix2) (a : Fin 3)
    (y : Vertex L k (j + 1)) (x : Fin 3 × Vertex L k j) :
    vertexStepKernel L k j V (a, y) x = pauliCoeff a
      ((adjointCubeAverage V (ofPauliCoeffs (deltaFunction x)) -
        vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
          (ofPauliCoeffs (deltaFunction x))) y) := rfl
theorem freeVertexKernel_apply (a : Fin 3) (y : Vertex L k (j + 1))
    (x : Fin 3 × Vertex L k j) :
    freeVertexKernel L k j (a, y) x = pauliCoeff a
      (vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (ofPauliCoeffs (deltaFunction x)) y) := rfl
theorem vertexStep_wNorm_le (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hF : OneStepComplexForms.OneStepClaim)
    (hLin : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j)
    (hfin : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite)
    {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hT : OpNormLE (colourVertices L k j) (colourVertices L k (j + 1))
      (vertexStepKernel L k j V) c)
    (hS : OpNormLE (colourVertices L k j) (colourVertices L k (j + 1)) (freeVertexKernel L k j) c')
    {f : (colourVertices L k j).Carrier → ℂ}
    (hf : NormSummable (colourVertices L k j).weightOf f) :
    NormSummable (colourVertices L k (j + 1)).weightOf (vertexStep L k j V f) ∧
      wNorm (colourVertices L k (j + 1)).weightOf (vertexStep L k j V f) ≤
        (c + c') * wNorm (colourVertices L k j).weightOf f := by
  obtain ⟨l₁, l₂, l₃⟩ := vertexStep_linear_local hLin hL hj hV hfin
  have G := (hK _ _ (vertexStep L k j V) l₁ l₂ l₃).1
  obtain ⟨-, -, hC, -⟩ := hLin L hL k j hj V hV
  have e : (fun (x' : Fin 3 × Vertex L k (j + 1)) (x : Fin 3 × Vertex L k j) =>
      vertexStep L k j V (basisFunction x).1 x') =
      vertexStepKernel L k j V + freeVertexKernel L k j := by
    funext x' x
    obtain ⟨a, y⟩ := x'
    set E : Vertex L k j → ComplexMatrix2 := ofPauliCoeffs (deltaFunction x) with hE
    have hEm : ∀ v, E v ∈ ComplexMatrix2.traceless := ofPauliCoeffs_mem _
    have hc₁ := (hC E hEm).2 y
    have hc₂ : vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j) E y ∈
        ComplexMatrix2.traceless :=
      Submodule.mem_pi.1 ((hF L hL k j hj).vertexSmoothing_mapsTo
        (Submodule.mem_pi.2 fun v _ => hEm v)) y (Set.mem_univ y)
    simp only [basisFunction_eq_deltaFunction]
    show vertexStep L k j V (deltaFunction x) (a, y) =
      vertexStepKernel L k j V (a, y) x + freeVertexKernel L k j (a, y) x
    rw [vertexStep_delta, vertexStepKernel_apply, freeVertexKernel_apply]
    simp only [Pi.sub_apply]
    rw [← pauliCoeff_add (Submodule.sub_mem _ hc₁ hc₂) hc₂, sub_add_cancel]
  have e' := (G f).2
  rw [e] at e'
  have e'' := applyKernel_add_kernel (hT.1 f hf).1 (hS.1 f hf).1
  have e₃ := e''.symm.trans e'
  rw [← e₃]
  exact add_applyKernel_wNorm_le (colourVertices_weight_pos hL k j)
    (fun x => (colourVertices_weight_pos hL k (j + 1) x).le) hc hc' hT hS hf
end Bounds
section Main
variable {L k : ℕ}
structure Hypotheses : Prop where
  nearFree : IterStepsNearFree.Bound
  contraction : SmoothingContraction.Claim
  kernels : ThreeMapKernels.Claim
  linearity : CovariantStepComplexLinear
  oneStep : OneStepComplexForms.OneStepClaim
  finiteSupport : FiniteSupportKernel.KernelOfFiniteSupportMap
  cubes : BlockStructure
  stepKernels : StepKernels.StepKernelBounds
  polydiscs : DoubleBlockPolydisc.PolydiscsHold
theorem edgeStepIsLocal_of_small (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < 3 / 4 * polydiscRadius L) :
    EdgeStepIsLocal L k j V := by
  classical
  intro c hc
  have K := G.stepKernels L hL k j hj c hc V hV hr
  have hfin : (StepKernels.positiveDoubleCubeLinks (L := L) (k := k) (j := j) c).Finite :=
    ((G.polydiscs L hL k j hj).2 c hc).finite_open.finite.subset fun b h => h.1
  have hmem : ∀ b : PositiveEdge (meshAt L k j),
      b ∈ hfin.toFinset.subtype (fun b => InfiniteLattice.Link.IsPositivelyOriented b) →
      b.1 ∈ StepKernels.positiveDoubleCubeLinks (L := L) (k := k) (j := j) c := fun b hb => by
    simpa using hb
  refine ⟨hfin.toFinset.subtype (fun b => InfiniteLattice.Link.IsPositivelyOriented b),
    fun b X => covariantSmoothingDeriv V (StepKernels.singleLinkForm b.1 X) c, ?_, ?_, ?_, ?_⟩
  · intro b hb X hX
    obtain ⟨T, h₁, -⟩ := K.kernel_bound b.1 (hmem b hb)
    have := h₁ ⟨X, hX⟩
    simp only at this
    simp only
    rw [← this]
    exact (T ⟨X, hX⟩).2
  · intro b hb X hX Y hY
    obtain ⟨T, h₁, -⟩ := K.kernel_bound b.1 (hmem b hb)
    have e₁ := h₁ ⟨X, hX⟩
    have e₂ := h₁ ⟨Y, hY⟩
    have e₃ := h₁ (⟨X, hX⟩ + ⟨Y, hY⟩)
    simp only [Submodule.coe_add, map_add] at e₁ e₂ e₃
    simp only
    rw [← e₁, ← e₂, ← e₃]
  · intro b hb z X hX
    obtain ⟨T, h₁, -⟩ := K.kernel_bound b.1 (hmem b hb)
    have e₁ := h₁ ⟨X, hX⟩
    have e₃ := h₁ (z • ⟨X, hX⟩)
    simp only [Submodule.coe_smul, map_smul] at e₁ e₃
    simp only
    rw [← e₁, ← e₃]
  · intro B hB
    rw [K.sum_eq_finsum B hB, finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact (Finset.sum_subtype_of_mem (fun b => covariantSmoothingDeriv V
      (StepKernels.singleLinkForm b (B b)) c)
      fun b hb => ((Set.Finite.mem_toFinset hfin).1 hb).2).symm
abbrev edgeIndexSets (L k : ℕ) : ℕ → PeriodicData := fun j => colourEdges L k j
abbrev vertexIndexSets (L k : ℕ) : ℕ → PeriodicData := fun j => colourVertices L k j
def edgeSteps (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    ∀ j, ((edgeIndexSets L k j).Carrier → ℂ) → (edgeIndexSets L k (j + 1)).Carrier → ℂ :=
  fun j => edgeStep L k j (complexIter L k j U)
def vertexSteps (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    ∀ j, ((vertexIndexSets L k j).Carrier → ℂ) → (vertexIndexSets L k (j + 1)).Carrier → ℂ :=
  fun j => vertexStep L k j (complexIter L k j U)
theorem composeUpTo_edgeSteps (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : Edge L k 0 → ComplexMatrix2}
    (hV : ∀ j < k, complexIter L k j U ∈ smallComplexFields L k j)
    (R : ∀ j < k, EdgeStepIsLocal L k j (complexIter L k j U))
    (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    ∀ j ≤ k, (composeUpTo (edgeIndexSets L k) (edgeSteps L k U) f j :
        Fin 3 × PositiveEdge (meshAt L k j) → ℂ) =
        (((((L : ℝ)⁻¹) ^ j : ℝ)) : ℂ) • coeffsOfForm (iterCovariantDeriv L k U j (formOfCoeffs f)) ∧
      (j < k → iterCovariantDeriv L k U j (formOfCoeffs f) ∈ complexEdgeForms (meshAt L k j)) := by
  have hne : ((L : ℝ)⁻¹) ≠ 0 := by
    have := hL.2
    have h : (L : ℝ) ≠ 0 := by
      have : L ≠ 0 := by omega
      exact_mod_cast this
    exact inv_ne_zero h
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, fun _ => formOfCoeffs_mem hL f⟩
    show f = _
    have e : iterCovariantDeriv L k U 0 (formOfCoeffs f) = formOfCoeffs f := rfl
    rw [e, coeffsOfForm_formOfCoeffs]
    simp
  | succ j ih =>
    intro hj
    have hj' : j < k := by omega
    obtain ⟨e₁, hB⟩ := ih hj'.le
    have hBj := hB hj'
    obtain ⟨-, l₂, -⟩ := edgeStep_linear_local hL (R j hj')
    set B := iterCovariantDeriv L k U j (formOfCoeffs f) with hBdef
    have step : edgeStep L k j (complexIter L k j U) (coeffsOfForm B) =
        (((L : ℝ)⁻¹ : ℝ) : ℂ) • coeffsOfForm (covariantSmoothingDeriv (complexIter L k j U) B) := by
      funext ⟨a, d⟩
      rw [edgeStep_apply, formOfCoeffs_coeffsOfForm hL hBj, pauliCoeff_real_smul hne]
      rfl
    refine ⟨?_, fun hj₁ => ?_⟩
    · show edgeStep L k j (complexIter L k j U)
        (composeUpTo (edgeIndexSets L k) (edgeSteps L k U) f j) = _
      rw [e₁, l₂, step, smul_smul]
      have e₂ : iterCovariantDeriv L k U (j + 1) (formOfCoeffs f) =
          covariantSmoothingDeriv (complexIter L k j U) B := rfl
      rw [e₂]
      congr 1
      push_cast
      rw [pow_succ]
    · have e₂ : iterCovariantDeriv L k U (j + 1) (formOfCoeffs f) =
          complexSmoothingDeriv (complexIter L k j U) B +
            covDiff (complexIter L k (j + 1) U) (contourLogDrift (complexIter L k j U) B) := rfl
      obtain ⟨hA, -, -, -⟩ := G.linearity L hL k j hj' _ (hV j hj')
      obtain ⟨-, -, hC, -⟩ := G.linearity L hL k (j + 1) hj₁ _ (hV (j + 1) hj₁)
      have a₁ := (hA B hBj).1
      have d₁ := (hC _ (hA B hBj).2).1
      rw [e₂]
      refine ⟨fun b h => Submodule.add_mem _ (a₁.1 b h) (d₁.1 b h), fun b => ?_⟩
      simp only [Pi.add_apply, a₁.2, d₁.2]
      abel
theorem composeUpTo_vertexSteps (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : Edge L k 0 → ComplexMatrix2}
    (hV : ∀ j < k, complexIter L k j U ∈ smallComplexFields L k j)
    (f : Fin 3 × Vertex L k 0 → ℂ) :
    ∀ j ≤ k, (composeUpTo (vertexIndexSets L k) (vertexSteps L k U) f j :
        Fin 3 × Vertex L k j → ℂ) =
        toPauliCoeffs (iterAdjointCubeAverage L k U j (ofPauliCoeffs f)) ∧
      ∀ x, iterAdjointCubeAverage L k U j (ofPauliCoeffs f) x ∈ ComplexMatrix2.traceless := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨(toPauliCoeffs_ofPauliCoeffs f).symm, ofPauliCoeffs_mem f⟩
  | succ j ih =>
    intro hj
    have hj' : j < k := by omega
    obtain ⟨e₁, hB⟩ := ih hj'.le
    obtain ⟨-, -, hC, -⟩ := G.linearity L hL k j hj' _ (hV j hj')
    refine ⟨?_, (hC _ hB).2⟩
    show vertexStep L k j (complexIter L k j U)
      (composeUpTo (vertexIndexSets L k) (vertexSteps L k U) f j) = _
    rw [e₁]
    funext ⟨a, y⟩
    rw [vertexStep_apply, ofPauliCoeffs_toPauliCoeffs hB]
    rfl
theorem free_opNormLE_one (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {j : ℕ} (hj : j < k) :
    OpNormLE (colourEdges L k j) (colourEdges L k (j + 1)) (freeEdgeKernel L k j) 1 ∧
      OpNormLE (colourVertices L k j) (colourVertices L k (j + 1)) (freeVertexKernel L k j) 1 := by
  obtain ⟨⟨hz, hθ⟩, -⟩ := G.contraction L hL k hk
  have b₁ := (hθ 0).1 j (by omega)
  have hv : TorusMetric.l1NormVec (0 : InfiniteLattice.AmbientSpace) = 0 := by
    simp [TorusMetric.l1NormVec]
  have e₁ : expConjOfMap (IndexedEvaluation.edgeForms L k j) (IndexedEvaluation.edgeForms L k (j + 1)) 0
      (fun B => (L : ℝ)⁻¹ • crossingSmoothing L (a := meshAt L k (j + 1))
        (a' := meshAt L k j) B) = freeEdgeKernel L k j :=
    hz 1 1 j (j + 1) hj.le hj (freeEdgeKernel L k j)
  have e₂ : expConjOfMap (IndexedEvaluation.vertices L k j) (IndexedEvaluation.vertices L k (j + 1)) 0
      (vertexSmoothing L (a := meshAt L k (j + 1)) (a' := meshAt L k j)) =
      freeVertexKernel L k j :=
    hz 0 0 j (j + 1) hj.le hj (freeVertexKernel L k j)
  have x₁ := b₁.1
  have x₂ := b₁.2
  rw [e₁, hv, mul_zero, zero_mul, Real.exp_zero] at x₁
  rw [e₂, hv, zero_mul, Real.exp_zero] at x₂
  exact ⟨x₁, x₂⟩
theorem cubeVertices_finite (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (hj : j < k) (y : Vertex L k (j + 1)) : (cubeVertices L (meshAt L k j) y).Finite := by
  have hcubes := G.cubes L k (j + 1) hL (by omega) (by omega) (by omega)
  have hcard := (hcubes.2.1 y).2.2.1
  have hpos : 0 < L ^ 4 := by
    have := hL.2
    positivity
  have hf : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_pos (hcard.symm ▸ hpos)
  exact hf.preimage Subtype.val_injective.injOn
structure IteratesNearOne (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) (A : ℝ) : Prop where
  mem_small : ∀ j < k, complexIter L k j U ∈ smallComplexFields L k j
  lt_half : ∀ j < k, ∀ b, ComplexMatrix2.operatorNorm (complexIter L k j U b - 1) <
    polydiscRadius L / 2
  le_bound : ∀ j < k, ∀ b, ComplexMatrix2.operatorNorm (complexIter L k j U b - 1) ≤
    20 * meshAt L k j * A
theorem opNormLE_Q (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2} {A : ℝ} (hU : U ∈ smallIterateFields L k)
    (S : IteratesNearOne L k U A) (hA : 0 ≤ A) (hA' : A ≤ 1 / 41) :
    OpNormLE (colourEdges L k 0) (colourEdges L k k) (rescaledOperators L k U).Q
      (Real.exp (30 * smoothingStepConstant L)) := by
  set C := smoothingStepConstant L with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    unfold smoothingStepConstant
    positivity
  have hne : finestMesh L k ≠ 0 := (meshAt_pos hL k 0).ne'
  have hnorm : ∀ j < k, ∀ b, ComplexMatrix2.operatorNorm (complexIter L k j U b - 1) <
      3 / 4 * polydiscRadius L := fun j hj b => by
    have h₁ := S.lt_half j hj b
    have h₂ : 0 ≤ ComplexMatrix2.operatorNorm (complexIter L k j U b - 1) := norm_nonneg _
    linarith
  have R : ∀ j < k, EdgeStepIsLocal L k j (complexIter L k j U) := fun j hj =>
    edgeStepIsLocal_of_small G hL hj (S.mem_small j hj).1 (hnorm j hj)
  have H : ∀ j < k, ∀ f, NormSummable (edgeIndexSets L k j).weightOf f →
      NormSummable (edgeIndexSets L k (j + 1)).weightOf (edgeSteps L k U j f) ∧
        wNorm (edgeIndexSets L k (j + 1)).weightOf (edgeSteps L k U j f) ≤
          (1 + C * (20 * meshAt L k j * A)) * wNorm (edgeIndexSets L k j).weightOf f := by
    intro j hj f hf
    have hs := meshAt_pos hL k j
    have h₁ := G.nearFree L hL k j hj _ (S.mem_small j hj).1 (S.lt_half j hj) _ (S.le_bound j hj)
    have h₂ := edgeStep_wNorm_le G.finiteSupport G.oneStep hL hj (R j hj)
      (c := C * (20 * meshAt L k j * A)) (c' := 1) (by positivity) zero_le_one h₁.1
      (free_opNormLE_one G hL hk hj).1 hf
    rw [add_comm (C * (20 * meshAt L k j * A)) 1] at h₂
    exact h₂
  have HK := ((G.kernels L hL k hk).2.2.2.2 U hU).1
  have hMap : (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k)
      (fun B => finestMesh L k • iterCovariantDeriv L k U k B) =
      ((finestMesh L k : ℝ) : ℂ) • (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k)
        (iterCovariantDeriv L k U k) := by
    funext f
    funext ⟨a, d⟩
    exact pauliCoeff_real_smul hne _ a
  have hg : Represents (rescaledOperators L k U).Q ((edgePauliCoordinates L k 0).mapOnCoeffs
      (edgePauliCoordinates L k k) (fun B => finestMesh L k • iterCovariantDeriv L k U k B)) :=
    Classical.epsilon_spec (p := fun T => Represents T ((edgePauliCoordinates L k 0).mapOnCoeffs
      (edgePauliCoordinates L k k) (fun B => finestMesh L k • iterCovariantDeriv L k U k B)))
      ⟨_, hMap ▸ HK.smul_represents _⟩
  refine opNormLE_of_forall (Real.exp_pos _).le (fun f _ => (hg f).1) fun f hf => ?_
  have hη : finestMesh L k = ((L : ℝ)⁻¹) ^ k := by
    unfold finestMesh meshAt
    simp [zpow_neg, inv_pow]
  have e := (composeUpTo_edgeSteps G hL S.mem_small R f k le_rfl).1
  have hact : applyKernel (rescaledOperators L k U).Q f =
      composeUpTo (edgeIndexSets L k) (edgeSteps L k U) f k := by
    rw [(hg f).2, hMap, e, hη]
    rfl
  obtain ⟨c₁, c₂⟩ := composeUpTo_wNorm_le (I := edgeIndexSets L k) (M := edgeSteps L k U) (k := k)
    (c := fun j => 1 + C * (20 * meshAt L k j * A))
    (fun j => by
      have := meshAt_pos hL k j
      positivity) H hf k le_rfl
  exact ⟨_, hact, c₁, c₂.trans (mul_le_mul_of_nonneg_right (prod_one_add_le_exp hL k hC hA hA')
    (Real.sqrt_nonneg _))⟩
theorem opNormLE_R (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2} {A : ℝ} (hU : U ∈ smallIterateFields L k)
    (S : IteratesNearOne L k U A) (hA : 0 ≤ A) (hA' : A ≤ 1 / 41) :
    OpNormLE (colourVertices L k 0) (colourVertices L k k) (rescaledOperators L k U).R
      (Real.exp (30 * smoothingStepConstant L)) := by
  set C := smoothingStepConstant L with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    unfold smoothingStepConstant
    positivity
  have H : ∀ j < k, ∀ f, NormSummable (vertexIndexSets L k j).weightOf f →
      NormSummable (vertexIndexSets L k (j + 1)).weightOf (vertexSteps L k U j f) ∧
        wNorm (vertexIndexSets L k (j + 1)).weightOf (vertexSteps L k U j f) ≤
          (1 + C * (20 * meshAt L k j * A)) * wNorm (vertexIndexSets L k j).weightOf f := by
    intro j hj f hf
    have hs := meshAt_pos hL k j
    have h₁ := G.nearFree L hL k j hj _ (S.mem_small j hj).1 (S.lt_half j hj) _ (S.le_bound j hj)
    have h₂ := vertexStep_wNorm_le G.finiteSupport G.oneStep G.linearity hL hj (S.mem_small j hj)
      (cubeVertices_finite G hL hj)
      (c := C * (20 * meshAt L k j * A)) (c' := 1) (by positivity) zero_le_one h₁.2
      (free_opNormLE_one G hL hk hj).2 hf
    rw [add_comm (C * (20 * meshAt L k j * A)) 1] at h₂
    exact h₂
  have HK := ((G.kernels L hL k hk).2.2.2.2 U hU).2
  have hg := HK.represents
  refine opNormLE_of_forall (Real.exp_pos _).le (fun f _ => (hg f).1) fun f hf => ?_
  have e := (composeUpTo_vertexSteps G hL S.mem_small f k le_rfl).1
  have hact : applyKernel (rescaledOperators L k U).R f =
      composeUpTo (vertexIndexSets L k) (vertexSteps L k U) f k := (hg f).2.trans e.symm
  obtain ⟨c₁, c₂⟩ := composeUpTo_wNorm_le (I := vertexIndexSets L k) (M := vertexSteps L k U)
    (k := k) (c := fun j => 1 + C * (20 * meshAt L k j * A))
    (fun j => by
      have := meshAt_pos hL k j
      positivity) H hf k le_rfl
  exact ⟨_, hact, c₁, c₂.trans (mul_le_mul_of_nonneg_right (prod_one_add_le_exp hL k hC hA hA')
    (Real.sqrt_nonneg _))⟩
end Main
theorem rescaledNormsBounded_holds (h₁ : IterStepsNearFree.Bound)
    (h₂ : SmoothingContraction.Claim) (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (h₅ : OneStepComplexForms.OneStepClaim)
    (h₆ : FiniteSupportKernel.KernelOfFiniteSupportMap) (h₇ : BlockStructure)
    (h₈ : StepKernels.StepKernelBounds)
    (h₉ : DoubleBlockPolydisc.PolydiscsHold) : RescaledNormsBounded := by
  have G : Hypotheses := ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  intro L hL k hk a _ hsup hI
  have hA : 0 ≤ (maxOperatorNorm a).toReal := ENNReal.toReal_nonneg
  have hA' : (maxOperatorNorm a).toReal ≤ 1 / 41 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) hsup
  have hsmall : ∀ j < k, complexIter L k j (remainderGaugeField a) ∈
      smallComplexFields L k j := fun j hj => ⟨hI.mem_fields j hj, fun b => by
    have h₁ := hI.norm_sub_one_lt_half j hj b
    have h₂ : 0 ≤ ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) :=
      norm_nonneg _
    linarith⟩
  have hU : remainderGaugeField a ∈ smallIterateFields L k :=
    ⟨hI.mem_fields 0 (by omega), hsmall⟩
  have S : IteratesNearOne L k (remainderGaugeField a) (maxOperatorNorm a).toReal :=
    ⟨hsmall, hI.norm_sub_one_lt_half, hI.norm_sub_one_le⟩
  have e : (12 * (L : ℝ) ^ 3 + 2) * (2560 * (polydiscRadius L ^ 2)⁻¹) =
      smoothingStepConstant L := by
    unfold smoothingStepConstant
    rw [inv_pow]
  rw [e]
  exact ⟨opNormLE_Q G hL hk hU S hA hA', opNormLE_R G hL hk hU S hA hA'⟩
end YangMills.Construction.Tower.FullSpace.RescaledNormBounds
end
