import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFiniteProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficient
import YangMills.Construction.RunningCouplingSlope.SecondMomentThroughABlockKernel
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open TorusFields TorusLumps Filter
open BlockAverages hiding unitStep gaugeTransform
namespace SlopeCoefficient.Pullback
section OffsetDecay
theorem natAbs_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem offsetNorm_le {h : Fin 4 → ℤ} {m : ℕ} (H : ∀ i, (h i).natAbs ≤ m) : offsetNorm h ≤ m :=
  Finset.sup_le fun i _ => H i
theorem offsetNorm_add_le (a b : Fin 4 → ℤ) : offsetNorm (a + b) ≤ offsetNorm a + offsetNorm b := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
theorem offsetNorm_neg (a : Fin 4 → ℤ) : offsetNorm (-a) = offsetNorm a := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
theorem offsetNormReal_add_le (a b : Fin 4 → ℤ) :
    offsetNormReal (a + b) ≤ offsetNormReal a + offsetNormReal b := by
  unfold offsetNormReal
  exact_mod_cast offsetNorm_add_le a b
theorem offsetNormReal_neg (a : Fin 4 → ℤ) : offsetNormReal (-a) = offsetNormReal a := by
  simp [offsetNormReal, offsetNorm_neg]
theorem offsetNormReal_nonneg (a : Fin 4 → ℤ) : 0 ≤ offsetNormReal a := Nat.cast_nonneg _
theorem offsetNormReal_sub_comm (a b : Fin 4 → ℤ) : offsetNormReal (a - b) = offsetNormReal (b - a) := by
  rw [← neg_sub, offsetNormReal_neg]
theorem offsetNormReal_le_add_sub (a b : Fin 4 → ℤ) :
    offsetNormReal a ≤ offsetNormReal b + offsetNormReal (a - b) := by
  have := offsetNormReal_add_le b (a - b)
  simpa using this
theorem abs_coord_le_offsetNormReal (a : Fin 4 → ℤ) (i : Fin 4) : |((a i : ℤ) : ℝ)| ≤ offsetNormReal a := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
theorem summable_exp_neg_offsetNormReal {c : ℝ} (hc : 0 < c) :
    Summable fun h : Fin 4 → ℤ => Real.exp (-(c * offsetNormReal h)) := by apply _root_.YangMills.Construction.TorusLumps.PotentialSums.summable_exp_neg_offsetNorm <;> assumption
theorem summable_exp_neg_offsetNormReal_sub {c : ℝ} (hc : 0 < c) (a : Fin 4 → ℤ) :
    Summable fun h : Fin 4 → ℤ => Real.exp (-(c * offsetNormReal (h - a))) :=
  (Equiv.subRight a).summable_iff.mpr (summable_exp_neg_offsetNormReal hc)
def SubexponentialGrowth (g : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z, |g z| ≤ C * Real.exp (ε * offsetNormReal z)
theorem SubexponentialGrowth.exists_nonneg {g : (Fin 4 → ℤ) → ℝ} (hg : SubexponentialGrowth g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |g z| ≤ C * Real.exp (ε * offsetNormReal z) := by
  obtain ⟨C, hC⟩ := hg ε hε
  refine ⟨max C 0, le_max_right _ _, fun z => (hC z).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
theorem SubexponentialGrowth.of_bounded {g : (Fin 4 → ℤ) → ℝ} {C : ℝ} (h : ∀ z, |g z| ≤ C) :
    SubexponentialGrowth g := by
  intro ε hε
  refine ⟨|C|, fun z => (h z).trans ?_⟩
  have h1 : 1 ≤ Real.exp (ε * offsetNormReal z) :=
    Real.one_le_exp (mul_nonneg hε.le (offsetNormReal_nonneg z))
  nlinarith [abs_nonneg C, le_abs_self C]
theorem SubexponentialGrowth.mul {g h : (Fin 4 → ℤ) → ℝ} (hg : SubexponentialGrowth g)
    (hh : SubexponentialGrowth h) : SubexponentialGrowth fun z => g z * h z := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hg.exists_nonneg (half_pos hε)
  obtain ⟨D, hD0, hD⟩ := hh.exists_nonneg (half_pos hε)
  refine ⟨C * D, fun z => ?_⟩
  rw [abs_mul]
  calc |g z| * |h z| ≤ (C * Real.exp (ε / 2 * offsetNormReal z)) *
        (D * Real.exp (ε / 2 * offsetNormReal z)) :=
        mul_le_mul (hC z) (hD z) (abs_nonneg _) (mul_nonneg hC0 (Real.exp_pos _).le)
    _ = C * D * Real.exp (ε * offsetNormReal z) := by
        have : Real.exp (ε * offsetNormReal z) =
            Real.exp (ε / 2 * offsetNormReal z) * Real.exp (ε / 2 * offsetNormReal z) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [this]
        ring
theorem subexponentialGrowth_offsetNormReal : SubexponentialGrowth offsetNormReal := by
  intro ε hε
  refine ⟨ε⁻¹, fun z => ?_⟩
  rw [abs_of_nonneg (offsetNormReal_nonneg z)]
  have h := Real.add_one_le_exp (ε * offsetNormReal z)
  have h0 : 0 < ε⁻¹ := inv_pos.mpr hε
  calc offsetNormReal z = ε⁻¹ * (ε * offsetNormReal z) := by field_simp
    _ ≤ ε⁻¹ * Real.exp (ε * offsetNormReal z) := by
      refine mul_le_mul_of_nonneg_left ?_ h0.le
      linarith
theorem subexponentialGrowth_coord (i : Fin 4) : SubexponentialGrowth fun z => ((z i : ℤ) : ℝ) := by
  intro ε hε
  obtain ⟨C, hC⟩ := subexponentialGrowth_offsetNormReal ε hε
  refine ⟨C, fun z => (abs_coord_le_offsetNormReal z i).trans ?_⟩
  have := hC z
  rwa [abs_of_nonneg (offsetNormReal_nonneg z)] at this
theorem SubexponentialGrowth.pow {g : (Fin 4 → ℤ) → ℝ} (hg : SubexponentialGrowth g) (k : ℕ) :
    SubexponentialGrowth fun z => g z ^ k := by
  induction k with
  | zero => exact SubexponentialGrowth.of_bounded (C := 1) (by simp)
  | succ k ih =>
    have := ih.mul hg
    intro ε hε
    obtain ⟨C, hC⟩ := this ε hε
    exact ⟨C, fun z => by simpa [pow_succ] using hC z⟩
theorem summable_mul_and_abs_tsum_le {θ : ℝ} (hθ : 0 < θ) {g : (Fin 4 → ℤ) → ℝ}
    (hg : SubexponentialGrowth g) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (a : Fin 4 → ℤ) (T : (Fin 4 → ℤ) → ℝ), 0 ≤ M →
      (∀ z, |T z| ≤ M * Real.exp (-(θ * offsetNormReal (z - a)))) →
      Summable (fun z => T z * g z) ∧
        |∑' z, T z * g z| ≤ M * C * Real.exp (ε * offsetNormReal a) := by
  set e : ℝ := min ε (θ / 2) with he
  have he0 : 0 < e := lt_min hε (half_pos hθ)
  have heε : e ≤ ε := min_le_left _ _
  have heθ : e ≤ θ / 2 := min_le_right _ _
  obtain ⟨C₀, hC0, hC⟩ := hg.exists_nonneg he0
  set S : ℝ := ∑' h : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal h)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C₀ * S, mul_nonneg hC0 hS0, fun M a T hM hT => ?_⟩
  have hb : ∀ z, ‖T z * g z‖ ≤ M * C₀ * Real.exp (ε * offsetNormReal a) *
      Real.exp (-(θ / 2 * offsetNormReal (z - a))) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hT z
    have h2 := hC z
    have h3 := offsetNormReal_le_add_sub z a
    have h4 := offsetNormReal_nonneg (z - a)
    have h5 := offsetNormReal_nonneg a
    calc |T z| * |g z| ≤ (M * Real.exp (-(θ * offsetNormReal (z - a)))) *
          (C₀ * Real.exp (e * offsetNormReal z)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
      _ = M * C₀ * Real.exp (-(θ * offsetNormReal (z - a)) + e * offsetNormReal z) := by
          rw [Real.exp_add]
          ring
      _ ≤ M * C₀ * Real.exp (ε * offsetNormReal a + -(θ / 2 * offsetNormReal (z - a))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hM hC0)
          nlinarith [mul_nonneg (sub_nonneg.mpr heε) h5, mul_nonneg he0.le h4,
            mul_nonneg (sub_nonneg.mpr heθ) h4, mul_le_mul_of_nonneg_left h3 he0.le]
      _ = _ := by
          rw [Real.exp_add]
          ring
  have hsa := summable_exp_neg_offsetNormReal_sub (half_pos hθ) a
  have hsum : Summable fun z => M * C₀ * Real.exp (ε * offsetNormReal a) *
      Real.exp (-(θ / 2 * offsetNormReal (z - a))) := hsa.mul_left _
  have hsm : Summable (fun z => T z * g z) := Summable.of_norm_bounded hsum hb
  refine ⟨hsm, ?_⟩
  have ht : ∑' z, Real.exp (-(θ / 2 * offsetNormReal (z - a))) = S :=
    (Equiv.subRight a).tsum_eq fun h => Real.exp (-(θ / 2 * offsetNormReal h))
  have := tsum_of_norm_bounded hsum.hasSum hb
  rw [tsum_mul_left, ht, Real.norm_eq_abs] at this
  calc _ ≤ _ := this
    _ = _ := by ring
end OffsetDecay
section AbelianHessian
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem fderiv_fderiv_comp_clm {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (L : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_comp_clm <;> assumption
theorem fderiv_fderiv_apply_eq_zero_of_eventually {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (w : F)
    (h : ∀ᶠ θ in 𝓝 (0 : F), fderiv ℝ Ψ θ w = 0) (u : F) : fderiv ℝ (fderiv ℝ Ψ) 0 u w = 0 := by
  have hΨ2 : DifferentiableAt ℝ (fderiv ℝ Ψ) 0 :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun θ => fderiv ℝ Ψ θ w) ((fderiv ℝ (fderiv ℝ Ψ) 0).flip w) 0 := by
    have := hΨ2.hasFDerivAt.clm_apply (hasFDerivAt_const w (0 : F))
    simpa using this
  have h2 : HasFDerivAt (fun θ => fderiv ℝ Ψ θ w) (0 : F →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq h
  have h3 := h1.unique h2
  have := congrArg (fun L : F →L[ℝ] ℝ => L u) h3
  simpa using this
end Calculus
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_smul_mul_smul (X : imaginaryQuaternions) (u v : ℝ) :
    expUnit (u • X) * expUnit (v • X) = expUnit ((u + v) • X) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
theorem expUnit_smul_inv (X : imaginaryQuaternions) (u : ℝ) : (expUnit (u • X))⁻¹ = expUnit ((-u) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
variable {n : ℕ} [NeZero n]
def abelianField (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (θ (x, i) • X)
def abelianRestriction (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions)
    (θ : TorusBond n → ℝ) : ℝ :=
  H n (abelianField X θ)
def bondDirection {k : ℕ} (c : Fin k → TorusBond n) : (Fin k → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ) else 0
theorem bondDirection_apply {k : ℕ} (c : Fin k → TorusBond n) (σ : Fin k → ℝ) (b : TorusBond n) :
    bondDirection c σ b = ∑ l, if c l = b then σ l else 0 := by
  simp only [bondDirection, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem bondDirection_single {k : ℕ} (c : Fin k → TorusBond n) (l : Fin k) :
    bondDirection c (Pi.single l 1) = Pi.single (c l) 1 := by
  funext b
  rw [bondDirection_apply, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
theorem perturb_trivial_const {k : ℕ} (c : Fin k → TorusBond n) (X : imaginaryQuaternions) (σ : Fin k → ℝ) :
    perturb c (fun _ => X) σ (trivialField n) = abelianField X (bondDirection c σ) := by
  funext x i
  have h : (∑ l, if c l = (x, i) then σ l • X else 0) = (bondDirection c σ (x, i)) • X := by
    rw [bondDirection_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  simp only [perturb, trivialField, abelianField, mul_one, h]
theorem abelianRestriction_comp_bondDirection {H : GaugeTotal} {k : ℕ} (c : Fin k → TorusBond n)
    (X : imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => H n (perturb c (fun _ => X) σ (trivialField n))) =
      abelianRestriction H n X ∘ bondDirection c := by
  funext σ
  simp only [Function.comp, abelianRestriction, perturb_trivial_const]
theorem contDiffAt_abelianRestriction {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0) :
    ContDiffAt ℝ 2 (abelianRestriction H n X) 0 := by
  classical
  let e := Fintype.equivFin (TorusBond n)
  let c : Fin (Fintype.card (TorusBond n)) → TorusBond n := e.symm
  let π₀ : (TorusBond n → ℝ) →ₗ[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    { toFun := fun θ l => θ (c l)
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  let π : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ θ : TorusBond n → ℝ, bondDirection c (π θ) = θ := by
    intro θ
    funext b
    rw [bondDirection_apply, Finset.sum_eq_single (e b)]
    · simp [c, π, π₀]
    · intro l _ hl
      have : c l ≠ b := fun h => hl (by simp [← h, c])
      simp [this]
    · simp
  have hφ := hs _ c fun _ => X
  have hcomp : abelianRestriction H n X =
      (fun σ => H n (perturb c (fun _ => X) σ (trivialField n))) ∘ π := by
    funext θ
    simp only [Function.comp, perturb_trivial_const, abelianRestriction, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond n → ℝ) ?_ π.contDiff.contDiffAt
  simpa using hφ
def abelianHessian (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions) :
    (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (abelianRestriction H n X)) 0
theorem hessianAtTrivial_eq_abelianHessian {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0) (c c' : TorusBond n) :
    hessianAtTrivial H n c c' X X = abelianHessian H n X (Pi.single c 1) (Pi.single c' 1) := by
  have hX : (![X, X] : Fin 2 → imaginaryQuaternions) = fun _ => X := by
    funext l
    fin_cases l <;> rfl
  unfold hessianAtTrivial mixedDeriv
  rw [hX, iteratedFDeriv_two_apply,
    abelianRestriction_comp_bondDirection (H := H) (![c, c'] : Fin 2 → TorusBond n) X,
    fderiv_fderiv_comp_clm (contDiffAt_abelianRestriction X hs), bondDirection_single, bondDirection_single]
  rfl
theorem abelianHessian_symm {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (u v : TorusBond n → ℝ) :
    abelianHessian H n X u v = abelianHessian H n X v u :=
  ((contDiffAt_abelianRestriction X hs).isSymmSndFDerivAt (by simp)) u v
def latticeGradient (φ : TorusSite n → ℝ) : TorusBond n → ℝ :=
  fun b => φ (b.1 + unitStep n b.2) - φ b.1
theorem gaugeTransform_abelianField (X : imaginaryQuaternions) (φ : TorusSite n → ℝ) (s : ℝ)
    (θ : TorusBond n → ℝ) :
    gaugeTransform (fun x => expUnit ((s * φ x) • X)) (abelianField X θ) =
      abelianField X (θ - s • latticeGradient φ) := by
  funext x i
  simp only [gaugeTransform, abelianField, expUnit_smul_inv, expUnit_smul_mul_smul]
  congr 2
  simp only [Pi.sub_apply, Pi.smul_apply, latticeGradient, smul_eq_mul]
  ring
theorem continuous_abelianField (X : imaginaryQuaternions) : Continuous (abelianField (n := n) X) :=
  continuous_pi fun x => continuous_pi fun i =>
    continuous_expUnit.comp ((continuous_apply (x, i)).smul continuous_const)
theorem abelianField_zero (X : imaginaryQuaternions) : abelianField (n := n) X 0 = trivialField n := by
  funext x i
  simp [abelianField, trivialField, expUnit_zero]
theorem abelianHessian_latticeGradient {H : GaugeTotal} (X : imaginaryQuaternions) (hg : IsGaugeTotalAt H n)
    (φ : TorusSite n → ℝ) (u : TorusBond n → ℝ) : abelianHessian H n X u (latticeGradient φ) = 0 := by
  have hC := contDiffAt_abelianRestriction X hg.contDiffAt_perturb
  refine fderiv_fderiv_apply_eq_zero_of_eventually hC _ ?_ u
  have hcont : Continuous fun p : (TorusBond n → ℝ) × ℝ =>
      (((fun x => expUnit ((p.2 * φ x) • X)) : TorusSite n → UnitQuaternion), abelianField X p.1) := by
    refine Continuous.prodMk ?_ ((continuous_abelianField X).comp continuous_fst)
    exact continuous_pi fun x => continuous_expUnit.comp
      ((continuous_snd.mul continuous_const).smul continuous_const)
  have hlim : Tendsto (fun p : (TorusBond n → ℝ) × ℝ =>
      (((fun x => expUnit ((p.2 * φ x) • X)) : TorusSite n → UnitQuaternion), abelianField X p.1))
      (𝓝 (0, 0)) (𝓝 (1, trivialField n)) := by
    have e0 : (((fun x => expUnit (((0 : ℝ) * φ x) • X)) : TorusSite n → UnitQuaternion),
        abelianField X (0 : TorusBond n → ℝ)) = (1, trivialField n) := by
      refine Prod.ext ?_ (abelianField_zero X)
      funext x
      simp [expUnit_zero]
    exact (hcont.tendsto (0, 0)).mono_right (le_of_eq (congrArg 𝓝 e0))
  have hinv := hlim.eventually hg.gauge_invariant_near
  have hprod : ∀ᶠ p in 𝓝 (0 : TorusBond n → ℝ) ×ˢ 𝓝 (0 : ℝ),
      abelianRestriction H n X (p.1 - p.2 • latticeGradient φ) = abelianRestriction H n X p.1 := by
    rw [← nhds_prod_eq]
    filter_upwards [hinv] with p hp
    rw [gaugeTransform_abelianField] at hp
    exact hp
  have hcur := hprod.curry
  have hdiff : ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), DifferentiableAt ℝ (abelianRestriction H n X) θ :=
    (hC.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  filter_upwards [hcur, hdiff] with θ hθ hd
  have hcurve : HasDerivAt (fun s : ℝ => θ - s • latticeGradient φ) (-latticeGradient φ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (latticeGradient φ)).const_sub θ
    simpa using this
  have hd' : HasFDerivAt (abelianRestriction H n X) (fderiv ℝ (abelianRestriction H n X) θ)
      (θ - (0 : ℝ) • latticeGradient φ) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hcurve
  have h2 : HasDerivAt (fun s : ℝ => abelianRestriction H n X (θ - s • latticeGradient φ)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (abelianRestriction H n X θ)).congr_of_eventuallyEq hθ
  have h3 := h1.unique h2
  simpa using h3
variable {H : GaugeTotal}
def zmodValInt (z : ZMod n) : ℤ := (z.val : ℤ)
theorem cast_zmodValInt (z : ZMod n) : ((zmodValInt z : ℤ) : ZMod n) = z := by
  simp [zmodValInt]
def translateAngles (u : TorusSite n) : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (b.1 - u, b.2)
def translationIsometry (u : TorusSite n) : TorusIsometry where
  axisPerm := 1
  axisSign := fun _ => 1
  offset := fun i => zmodValInt (u i)
  axisSign_unit := fun _ => Or.inl rfl
theorem translationIsometry_mapSite (u x : TorusSite n) : (translationIsometry u).mapSite x = x + u := by
  funext i
  simp [TorusIsometry.mapSite, translationIsometry, cast_zmodValInt]
theorem translationIsometry_transports (X : imaginaryQuaternions) (u : TorusSite n) (θ : TorusBond n → ℝ) :
    (translationIsometry u).Transports (abelianField X θ) (abelianField X (translateAngles u θ)) := by
  intro x k
  have h1 : (translationIsometry u).axisSign ((translationIsometry u).axisPerm.symm k) = 1 := rfl
  rw [if_pos h1, translationIsometry_mapSite]
  simp [abelianField, translateAngles, translationIsometry, Equiv.Perm.one_def]
theorem abelianHessian_isometry_invariant (X : imaginaryQuaternions) (ht : IsGaugeTotalAt H n)
    (g : TorusIsometry) (A : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ))
    (hg : ∀ θ, g.Transports (abelianField X θ) (abelianField X (A θ)))
    (a b : TorusBond n → ℝ) : abelianHessian H n X (A a) (A b) = abelianHessian H n X a b := by
  have hC := contDiffAt_abelianRestriction X ht.contDiffAt_perturb
  have hlim : Tendsto (abelianField (n := n) X) (𝓝 0) (𝓝 (trivialField n)) := by
    have h := (continuous_abelianField (n := n) X).tendsto 0
    rwa [abelianField_zero] at h
  have hev : (abelianRestriction H n X ∘ A) =ᶠ[𝓝 0] abelianRestriction H n X := by
    filter_upwards [hlim.eventually (ht.isometry_invariant g)] with θ hθ
    exact hθ _ (hg θ)
  have e1 := fderiv_fderiv_comp_clm hC A a b
  have e2 : fderiv ℝ (fderiv ℝ (abelianRestriction H n X ∘ A)) 0 =
      fderiv ℝ (fderiv ℝ (abelianRestriction H n X)) 0 := hev.fderiv.fderiv_eq
  rw [e2] at e1
  exact e1.symm
theorem translateAngles_single (u : TorusSite n) (b : TorusBond n) :
    translateAngles u (Pi.single b 1) = Pi.single (b.1 + u, b.2) 1 := by
  classical
  funext ⟨x, i⟩
  simp only [translateAngles, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply, Pi.single_apply]
  have : ((x - u, i) : TorusBond n) = b ↔ ((x, i) : TorusBond n) = (b.1 + u, b.2) := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      have h1 := (Prod.ext_iff.mp h).1
      have h2 := (Prod.ext_iff.mp h).2
      simp only at h1 h2
      refine Prod.ext ?_ h2
      simp [h1]
  simp [this]
def reflectionIsometry : TorusIsometry where
  axisPerm := 1
  axisSign := fun _ => -1
  offset := fun _ => 0
  axisSign_unit := fun _ => Or.inr rfl
theorem reflectionIsometry_mapSite (x : TorusSite n) : reflectionIsometry.mapSite x = -x := by
  funext i
  simp [TorusIsometry.mapSite, reflectionIsometry]
def reflectAngles : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => -ContinuousLinearMap.proj (-b.1 - unitStep n b.2, b.2)
theorem reflectionIsometry_transports (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) :
    reflectionIsometry.Transports (abelianField X θ) (abelianField X (reflectAngles θ)) := by
  intro x k
  have h1 : ¬ reflectionIsometry.axisSign (reflectionIsometry.axisPerm.symm k) = 1 := by
    simp [reflectionIsometry]
  rw [if_neg h1, reflectionIsometry_mapSite]
  simp only [reflectionIsometry, Equiv.Perm.one_symm, Equiv.Perm.coe_one, id_eq, abelianField, reflectAngles,
    ContinuousLinearMap.coe_pi', ContinuousLinearMap.neg_apply, ContinuousLinearMap.proj_apply,
    expUnit_smul_inv]
  simp
theorem reflectAngles_single (b : TorusBond n) :
    reflectAngles (Pi.single b (1 : ℝ)) = -Pi.single (-b.1 - unitStep n b.2, b.2) (1 : ℝ) := by
  classical
  funext ⟨x, i⟩
  obtain ⟨y, j⟩ := b
  simp only [reflectAngles, ContinuousLinearMap.coe_pi', ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, Pi.neg_apply]
  have : ((-x - unitStep n i, i) : TorusBond n) = (y, j) ↔
      ((x, i) : TorusBond n) = (-y - unitStep n j, j) := by
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨h1, rfl⟩
      refine ⟨?_, rfl⟩
      rw [← h1]
      abel
    · rintro ⟨h1, rfl⟩
      refine ⟨?_, rfl⟩
      rw [h1]
      abel
  simp [this]
end AbelianHessian
section LatticeKernel
variable {H : GaugeTotal} {K : LatticeBond → LatticeBond → ℝ}
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem inner_quaternionI_self :
    inner ℝ ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.inner_quaternionI_self <;> assumption
theorem valMinAbs_intCast_of_small {n : ℕ} [NeZero n] {z : ℤ} (h : 2 * z.natAbs + 1 < n) :
    ((z : ZMod n)).valMinAbs = z := by
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_, ?_⟩ <;> omega
theorem siteOfInt_add {n : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfInt (a + b) : TorusSite n) = siteOfInt a + siteOfInt b := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
theorem siteOfInt_sub {n : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfInt (a - b) : TorusSite n) = siteOfInt a - siteOfInt b := by
  funext i
  simp [siteOfInt]
theorem siteOfInt_neg {n : ℕ} (a : Fin 4 → ℤ) : (siteOfInt (-a) : TorusSite n) = -siteOfInt a := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
theorem siteOfInt_latticeUnitVector {n : ℕ} (ν : Fin 4) :
    (siteOfInt (latticeUnitVector ν) : TorusSite n) = unitStep n ν := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem supDist_siteOfInt {n : ℕ} [NeZero n] (a b : Fin 4 → ℤ) (h : 2 * offsetNorm (a - b) + 1 < n) :
    supDist (siteOfInt a : TorusSite n) (siteOfInt b) = offsetNorm (a - b) := by
  unfold supDist offsetNorm
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : ((siteOfInt a : TorusSite n) i - (siteOfInt b : TorusSite n) i) = (((a - b) i : ℤ) : ZMod n) := by
    simp [siteOfInt]
  rw [e, valMinAbs_intCast_of_small]
  have := natAbs_le_offsetNorm (a - b) i
  omega
theorem bondFrom_zero {n : ℕ} (c : LatticeBond) : bondFrom (0 : TorusSite n) c = (siteOfInt c.1, c.2) := by
  simp [bondFrom]
section OnTheTorus
variable {n : ℕ} [NeZero n]
theorem hessianAtTrivial_symm_bonds (ht : IsGaugeTotalAt H n) (X : imaginaryQuaternions) (b b' : TorusBond n) :
    hessianAtTrivial H n b b' X X = hessianAtTrivial H n b' b X X := by
  rw [hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb,
    hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb, abelianHessian_symm X ht.contDiffAt_perturb]
theorem hessianAtTrivial_translate (ht : IsGaugeTotalAt H n) (X : imaginaryQuaternions) (u : TorusSite n)
    (b b' : TorusBond n) :
    hessianAtTrivial H n (b.1 + u, b.2) (b'.1 + u, b'.2) X X = hessianAtTrivial H n b b' X X := by
  rw [hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb,
    hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb, ← translateAngles_single,
    ← translateAngles_single]
  exact abelianHessian_isometry_invariant X ht (translationIsometry u) (translateAngles u)
    (translationIsometry_transports X u) _ _
theorem hessianAtTrivial_reflect (ht : IsGaugeTotalAt H n) (X : imaginaryQuaternions) (b b' : TorusBond n) :
    hessianAtTrivial H n (-b.1 - unitStep n b.2, b.2) (-b'.1 - unitStep n b'.2, b'.2) X X =
      hessianAtTrivial H n b b' X X := by
  rw [hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb,
    hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb]
  have h := abelianHessian_isometry_invariant X ht reflectionIsometry reflectAngles
    (reflectionIsometry_transports X) (Pi.single b 1) (Pi.single b' 1)
  rw [reflectAngles_single, reflectAngles_single] at h
  simpa using h
theorem latticeGradient_single (y : TorusSite n) :
    latticeGradient (Pi.single y (1 : ℝ) : TorusSite n → ℝ) =
      ∑ ν : Fin 4, ((Pi.single (y - unitStep n ν, ν) (1 : ℝ) : TorusBond n → ℝ) -
        Pi.single (y, ν) (1 : ℝ)) := by
  classical
  funext ⟨w, μ⟩
  simp only [latticeGradient, Finset.sum_apply, Pi.sub_apply]
  rw [Finset.sum_eq_single μ]
  · simp only [Pi.single_apply, Prod.mk.injEq, and_true]
    have : w + unitStep n μ = y ↔ w = y - unitStep n μ := by
      constructor
      · intro h
        rw [← h]
        abel
      · intro h
        rw [h]
        abel
    simp [this]
  · intro ν _ hν
    simp [Pi.single_apply, hν.symm]
  · simp
theorem hessianAtTrivial_divergence (ht : IsGaugeTotalAt H n) (X : imaginaryQuaternions) (b : TorusBond n)
    (y : TorusSite n) :
    ∑ ν : Fin 4, (hessianAtTrivial H n b (y - unitStep n ν, ν) X X - hessianAtTrivial H n b (y, ν) X X) = 0 := by
  have h := abelianHessian_latticeGradient (H := H) X ht (Pi.single y (1 : ℝ)) (Pi.single b (1 : ℝ))
  rw [latticeGradient_single, map_sum] at h
  simp_rw [map_sub] at h
  simp_rw [hessianAtTrivial_eq_abelianHessian X ht.contDiffAt_perturb]
  exact h
end OnTheTorus
theorem tendsto_hessian_quaternionI (hK : IsLocalGaugeTotal atTop H K) (c c' : LatticeBond) :
    Tendsto (fun n => hessianAtTrivial H n (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI) atTop
      (𝓝 (K c c')) := by
  have h := hK.tendsto_kernel c c' quaternionI quaternionI
  rwa [inner_quaternionI_self, one_mul] at h
theorem kernel_exp_decay (hK : IsLocalGaugeTotal atTop H K) : ∃ M θ : ℝ, 0 < θ ∧
    ∀ c c', |K c c'| ≤ M * Real.exp (-(θ * offsetNormReal (c'.1 - c.1))) := by
  obtain ⟨M, θ, hθ, h⟩ := hK.exp_decay
  refine ⟨M, θ, hθ, fun c c' => ?_⟩
  refine le_of_tendsto (tendsto_hessian_quaternionI hK c c').abs ?_
  filter_upwards [h, eventually_gt_atTop (2 * offsetNorm (c.1 - c'.1) + 1)] with m hm hgt
  have hm0 : NeZero m := ⟨by omega⟩
  have a := hm (bondFrom 0 c) (bondFrom 0 c') quaternionI quaternionI norm_quaternionI norm_quaternionI
  rw [bondFrom_zero, bondFrom_zero] at a ⊢
  simp only at a
  rw [supDist_siteOfInt _ _ hgt] at a
  rw [offsetNormReal_sub_comm]
  exact a
theorem isLatticeHessianKernel_of_isLocalGaugeTotal (hK : IsLocalGaugeTotal atTop H K) :
    IsLatticeHessianKernel K where
  exp_decay := kernel_exp_decay hK
  symm := fun c c' => by
    refine tendsto_nhds_unique (tendsto_hessian_quaternionI hK c c')
      ((tendsto_hessian_quaternionI hK c' c).congr' ?_)
    filter_upwards [hK.eventually_isGaugeTotalAt, eventually_gt_atTop 0] with m ht hm
    have : NeZero m := ⟨hm.ne'⟩
    exact hessianAtTrivial_symm_bonds ht _ _ _
  translation_invariant := fun u c c' => by
    refine tendsto_nhds_unique (tendsto_hessian_quaternionI hK _ _)
      ((tendsto_hessian_quaternionI hK c c').congr' ?_)
    filter_upwards [hK.eventually_isGaugeTotalAt, eventually_gt_atTop 0] with m ht hm
    have : NeZero m := ⟨hm.ne'⟩
    have := hessianAtTrivial_translate ht quaternionI (siteOfInt u : TorusSite m) (bondFrom 0 c) (bondFrom 0 c')
    rw [bondFrom_zero, bondFrom_zero] at this ⊢
    rw [bondFrom_zero, bondFrom_zero]
    simp only [siteOfInt_add] at *
    exact this.symm
  divergence_zero := fun c x => by
    have h : Tendsto (fun m => ∑ ν : Fin 4,
        (hessianAtTrivial H m (bondFrom 0 c) (bondFrom 0 (x - latticeUnitVector ν, ν)) quaternionI quaternionI -
          hessianAtTrivial H m (bondFrom 0 c) (bondFrom 0 (x, ν)) quaternionI quaternionI)) atTop
        (𝓝 (∑ ν, (K c (x - latticeUnitVector ν, ν) - K c (x, ν)))) :=
      tendsto_finset_sum _ fun ν _ =>
        (tendsto_hessian_quaternionI hK _ _).sub (tendsto_hessian_quaternionI hK _ _)
    refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
    filter_upwards [hK.eventually_isGaugeTotalAt, eventually_gt_atTop 0] with m ht hm
    have : NeZero m := ⟨hm.ne'⟩
    have e := hessianAtTrivial_divergence ht quaternionI (bondFrom 0 c) (siteOfInt x : TorusSite m)
    simp only [bondFrom_zero, siteOfInt_sub, siteOfInt_latticeUnitVector] at e ⊢
    exact e.symm
  reflect_invariant := fun c c' => by
    refine tendsto_nhds_unique (tendsto_hessian_quaternionI hK _ _)
      ((tendsto_hessian_quaternionI hK c c').congr' ?_)
    filter_upwards [hK.eventually_isGaugeTotalAt, eventually_gt_atTop 0] with m ht hm
    have : NeZero m := ⟨hm.ne'⟩
    have := hessianAtTrivial_reflect ht quaternionI (bondFrom 0 c) (bondFrom 0 c')
    simp only [bondFrom_zero, reflectBond, siteOfInt_sub, siteOfInt_neg, siteOfInt_latticeUnitVector] at this ⊢
    exact this.symm
end LatticeKernel
section BlockKernel
variable {L : ℕ} {p : BlockFieldMap L} {P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ}
  {Pl : LatticeBond → LatticeBond → ℝ}
theorem blockCentreSite_siteOfInt {n : ℕ} [NeZero n] (c : Fin 4 → ℤ) :
    blockCentreSite L (siteOfInt c : TorusSite n) = siteOfInt ((L : ℤ) • c) := by
  funext i
  simp only [blockCentreSite, siteOfInt, Pi.smul_apply, smul_eq_mul]
  have h1 : (((c i : ZMod n)).val : ℤ) = c i % (n : ℤ) := ZMod.val_intCast (c i)
  have h2 : ((L * ((c i : ZMod n)).val : ℕ) : ℤ) = (L : ℤ) * (c i % (n : ℤ)) := by
    push_cast
    rw [h1]
  have h3 : (((L * ((c i : ZMod n)).val : ℕ) : ℤ) : ZMod (n * L)) =
      (((L : ℤ) * c i : ℤ) : ZMod (n * L)) := by
    rw [h2, ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨c i / (n : ℤ), ?_⟩
    have := Int.mul_ediv_add_emod (c i) (n : ℤ)
    push_cast
    have e : (L : ℤ) * c i - (L : ℤ) * (c i % (n : ℤ)) = (L : ℤ) * ((n : ℤ) * (c i / (n : ℤ))) := by
      rw [← mul_sub]
      congr 1
      linarith
    rw [e]
    ring
  simpa using h3
theorem isLatticeBlockKernel_of_isBlockMap (hL : 0 < L) (hM : IsBlockMap L p P Pl) :
    IsLatticeBlockKernel L Pl where
  exp_decay := by
    obtain ⟨M, θ, hθ, h⟩ := hM.exp_decay
    refine ⟨M, θ, hθ, fun b c => ?_⟩
    refine le_of_tendsto (hM.tendsto_kernel b c).abs ?_
    filter_upwards [h, eventually_gt_atTop (2 * offsetNorm (b.1 - (L : ℤ) • c.1) + 1)] with m hm hgt
    have hm0 : NeZero m := ⟨by omega⟩
    have hmL : NeZero (m * L) := ⟨Nat.mul_ne_zero hm0.out hL.ne'⟩
    have hgt' : 2 * offsetNorm (b.1 - (L : ℤ) • c.1) + 1 < m * L :=
      lt_of_lt_of_le hgt (Nat.le_mul_of_pos_right _ hL)
    have a := hm (bondFrom 0 b) (bondFrom 0 c)
    rw [bondFrom_zero, bondFrom_zero] at a ⊢
    simp only at a
    rw [blockCentreSite_siteOfInt, supDist_siteOfInt _ _ hgt'] at a
    exact a
  translation_invariant := fun u b c => by
    refine tendsto_nhds_unique (hM.tendsto_kernel _ _) ((hM.tendsto_kernel b c).congr' ?_)
    filter_upwards [hM.translation_invariant, eventually_gt_atTop 0] with m hm hgt
    have hm0 : NeZero m := ⟨hgt.ne'⟩
    have a := hm (bondFrom 0 b) (bondFrom 0 c) (siteOfInt u)
    rw [blockCentreSite_siteOfInt] at a
    simp only [bondFrom_zero, siteOfInt_add] at a ⊢
    exact a.symm
  constant_form := hM.constant_form secondAxis
  linear_potential := hM.linear_potential
end BlockKernel
section ChainRuleAtZero
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem fderiv_fderiv_comp_of_fderiv_eq_zero {Ψ : F → ℝ} {w : E → F} (hΨ : ContDiffAt ℝ 2 Ψ 0)
    (hw : ContDiffAt ℝ 2 w 0) (h0 : w 0 = 0) (hD : fderiv ℝ Ψ 0 = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ w)) 0 u v =
      fderiv ℝ (fderiv ℝ Ψ) 0 (fderiv ℝ w 0 u) (fderiv ℝ w 0 v) := by
  have hΨd : ∀ᶠ A in 𝓝 (0 : F), DifferentiableAt ℝ Ψ A :=
    (hΨ.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  have hwd : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ w y :=
    (hw.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  have hwc : Tendsto w (𝓝 0) (𝓝 (0 : F)) := by
    have := hw.continuousAt.tendsto
    rwa [h0] at this
  have hev : fderiv ℝ (Ψ ∘ w) =ᶠ[𝓝 0] fun y => (fderiv ℝ Ψ (w y)).comp (fderiv ℝ w y) := by
    filter_upwards [hwc.eventually hΨd, hwd] with y h1 h2
    exact fderiv_comp y h1 h2
  rw [hev.fderiv_eq]
  have hΨ2 : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) 0) (w 0) := by
    rw [h0]
    exact ((hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hw1 : HasFDerivAt w (fderiv ℝ w 0) 0 := (hw.differentiableAt (by simp)).hasFDerivAt
  have hw2 : HasFDerivAt (fderiv ℝ w) (fderiv ℝ (fderiv ℝ w) 0) 0 :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hA := hΨ2.comp (0 : E) hw1
  have hB : HasFDerivAt (fun y => (fderiv ℝ Ψ (w y)).comp (fderiv ℝ w y)) _ 0 := hA.clm_comp hw2
  rw [hB.fderiv]
  simp [h0, hD]
end ChainRuleAtZero
section Logarithm
def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - ((q.re : ℝ) : ℍ[ℝ]), by
    show (q - ((q.re : ℝ) : ℍ[ℝ])).re = 0
    simp⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    ext <;> simp
  map_smul' r a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    ext <;> simp
def imPart : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imPartLinear
theorem imPart_apply (q : ℍ[ℝ]) : ((imPart q : imaginaryQuaternions) : ℍ[ℝ]) = q - ((q.re : ℝ) : ℍ[ℝ]) :=
  rfl
theorem imPart_coe (w : imaginaryQuaternions) : imPart (w : ℍ[ℝ]) = w := by
  apply Subtype.ext
  rw [imPart_apply]
  have : (w : ℍ[ℝ]).re = 0 := w.2
  simp [this]
def imExp (w : imaginaryQuaternions) : imaginaryQuaternions := imPart (NormedSpace.exp (w : ℍ[ℝ]))
theorem contDiffAt_exp_quaternion (q : ℍ[ℝ]) : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
theorem contDiffAt_imExp : ContDiffAt ℝ 2 imExp 0 := by
  have h1 : ContDiffAt ℝ 2 (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) 0 :=
    imaginaryQuaternions.subtypeL.contDiff.contDiffAt
  exact imPart.contDiff.contDiffAt.comp (0 : imaginaryQuaternions)
    ((contDiffAt_exp_quaternion _).comp (0 : imaginaryQuaternions) h1)
theorem hasFDerivAt_imExp_zero : HasFDerivAt imExp
    ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
      imaginaryQuaternions →L[ℝ] imaginaryQuaternions) 0 := by
  have h1 : HasFDerivAt (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) imaginaryQuaternions.subtypeL 0 :=
    imaginaryQuaternions.subtypeL.hasFDerivAt
  have h2 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      (((0 : imaginaryQuaternions) : ℍ[ℝ])) :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)).hasFDerivAt
  have h3 := imPart.hasFDerivAt.comp (0 : imaginaryQuaternions) (h2.comp (0 : imaginaryQuaternions) h1)
  refine h3.congr_fderiv ?_
  ext w : 1
  simp [imPart_coe]
def imLog : imaginaryQuaternions → imaginaryQuaternions :=
  contDiffAt_imExp.localInverse hasFDerivAt_imExp_zero (by norm_num)
theorem imExp_zero : imExp 0 = 0 := by
  apply Subtype.ext
  simp [imExp, imPart_apply]
theorem contDiffAt_imLog : ContDiffAt ℝ 2 imLog 0 := by
  have := contDiffAt_imExp.to_localInverse hasFDerivAt_imExp_zero (by norm_num)
  rwa [imExp_zero] at this
theorem imLog_zero : imLog 0 = 0 := by
  have := contDiffAt_imExp.localInverse_apply_image hasFDerivAt_imExp_zero (by norm_num)
  rwa [imExp_zero] at this
theorem hasFDerivAt_imLog_zero : HasFDerivAt imLog (ContinuousLinearMap.id ℝ imaginaryQuaternions) 0 := by
  have h := ((contDiffAt_imExp.hasStrictFDerivAt' hasFDerivAt_imExp_zero (by norm_num)).to_localInverse).hasFDerivAt
  rw [imExp_zero] at h
  exact h
theorem imExp_imLog : ∀ᶠ v in 𝓝 (0 : imaginaryQuaternions), imExp (imLog v) = v := by
  have h := (contDiffAt_imExp.hasStrictFDerivAt' hasFDerivAt_imExp_zero (by norm_num)).eventually_right_inverse
  rw [imExp_zero] at h
  exact h
def quaternionLog (q : ℍ[ℝ]) : imaginaryQuaternions := imLog (imPart q)
theorem imPart_one : imPart (1 : ℍ[ℝ]) = 0 := by
  apply Subtype.ext
  simp [imPart_apply]
theorem quaternionLog_one : quaternionLog 1 = 0 := by
  simp [quaternionLog, imPart_one, imLog_zero]
theorem contDiffAt_quaternionLog : ContDiffAt ℝ 2 quaternionLog 1 := by
  have h := contDiffAt_imLog
  rw [← imPart_one] at h
  exact h.comp (1 : ℍ[ℝ]) imPart.contDiff.contDiffAt
theorem hasFDerivAt_quaternionLog_one : HasFDerivAt quaternionLog imPart 1 := by
  have h := hasFDerivAt_imLog_zero
  rw [← imPart_one] at h
  have := h.comp (1 : ℍ[ℝ]) imPart.hasFDerivAt
  rw [ContinuousLinearMap.id_comp] at this
  exact this
theorem eq_of_imPart_eq {a b : ℍ[ℝ]} (ha : Quaternion.normSq a = 1) (hb : Quaternion.normSq b = 1)
    (h : imPart a = imPart b) (pa : 0 < a.re) (pb : 0 < b.re) : a = b := by
  have h' := congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) h
  simp only [imPart_apply] at h'
  have e1 := congrArg (fun q : ℍ[ℝ] => q.imI) h'
  have e2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h'
  have e3 := congrArg (fun q : ℍ[ℝ] => q.imK) h'
  simp at e1 e2 e3
  rw [Quaternion.normSq_def'] at ha hb
  have e4 : a.re ^ 2 = b.re ^ 2 := by
    rw [e1, e2, e3] at ha
    linarith
  have e5 : a.re = b.re := by
    nlinarith [sq_nonneg (a.re - b.re)]
  ext <;> assumption
theorem exp_quaternionLog : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), Quaternion.normSq q = 1 →
    NormedSpace.exp ((quaternionLog q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  have h1 : Tendsto (fun q : ℍ[ℝ] => imPart q) (𝓝 1) (𝓝 0) := by
    have := imPart.continuous.tendsto (1 : ℍ[ℝ])
    rwa [imPart_one] at this
  have h2 := h1.eventually imExp_imLog
  have h3 : ∀ᶠ q : ℍ[ℝ] in 𝓝 1, 0 < q.re := by
    have hc : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h4 : ContinuousAt (fun q : ℍ[ℝ] => NormedSpace.exp ((quaternionLog q : imaginaryQuaternions) : ℍ[ℝ])) 1 := by
    have hc := contDiffAt_quaternionLog.continuousAt
    have he : ContinuousAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
        (((quaternionLog 1 : imaginaryQuaternions) : ℍ[ℝ])) :=
      (contDiffAt_exp_quaternion _).continuousAt
    exact ContinuousAt.comp (f := fun q => ((quaternionLog q : imaginaryQuaternions) : ℍ[ℝ])) he
      (continuous_subtype_val.continuousAt.comp hc)
  have h5 : ∀ᶠ q : ℍ[ℝ] in 𝓝 1,
      0 < (NormedSpace.exp ((quaternionLog q : imaginaryQuaternions) : ℍ[ℝ])).re := by
    have hc : ContinuousAt
        (fun q : ℍ[ℝ] => (NormedSpace.exp ((quaternionLog q : imaginaryQuaternions) : ℍ[ℝ])).re) 1 :=
      Quaternion.continuous_re.continuousAt.comp h4
    refine hc.eventually (lt_mem_nhds ?_)
    simp [quaternionLog_one]
  filter_upwards [h2, h3, h5] with q a2 a3 a5 hq
  refine eq_of_imPart_eq ?_ hq a2 a5 a3
  have := (expUnit (quaternionLog q)).2
  exact show Quaternion.normSq (((expUnit (quaternionLog q) : UnitQuaternion)) : ℍ[ℝ]) = 1 from by
    have h := (Unitary.mem_iff.mp this).1
    rw [Quaternion.star_mul_self] at h
    have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h
    simpa using h2
end Logarithm
section ExponentialChart
variable {m : ℕ} [NeZero m] {H : GaugeTotal}
def fieldOfLie (w : TorusBond m → imaginaryQuaternions) : TorusField m := fun x i => expUnit (w (x, i))
def expChart (H : GaugeTotal) (m : ℕ) [NeZero m] (w : TorusBond m → imaginaryQuaternions) : ℝ :=
  H m (fieldOfLie w)
theorem perturb_trivial_eq_fieldOfLie {k : ℕ} (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) :
    perturb c X σ (trivialField m) = fieldOfLie fun b => ∑ l, if c l = b then σ l • X l else 0 := by
  funext x i
  simp [perturb, fieldOfLie, trivialField]
theorem contDiffAt_expChart (ht : IsGaugeTotalAt H m) : ContDiffAt ℝ 2 (expChart H m) 0 := by
  classical
  let Bs := Module.finBasis ℝ imaginaryQuaternions
  let e := Fintype.equivFin (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))
  let c : Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → TorusBond m :=
    fun l => (e.symm l).1
  let X : Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) →
      imaginaryQuaternions := fun l => Bs (e.symm l).2
  let π₀ : (TorusBond m → imaginaryQuaternions) →ₗ[ℝ]
      (Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → ℝ) :=
    { toFun := fun w l => Bs.coord (e.symm l).2 (w (e.symm l).1)
      map_add' := by
        intro a b
        funext l
        simp
      map_smul' := by
        intro r a
        funext l
        simp }
  let π : (TorusBond m → imaginaryQuaternions) →L[ℝ]
      (Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ (w : TorusBond m → imaginaryQuaternions) (b : TorusBond m),
      (∑ l, if c l = b then π w l • X l else 0) = w b := by
    intro w b
    have h1 := Equiv.sum_comp e.symm (fun q : TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions) =>
      if q.1 = b then (Bs.coord q.2 (w q.1)) • Bs q.2 else 0)
    have h2 : (∑ l, if c l = b then π w l • X l else 0) =
        ∑ l, (fun q : TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions) =>
          if q.1 = b then (Bs.coord q.2 (w q.1)) • Bs q.2 else 0) (e.symm l) := rfl
    rw [h2, h1, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp only [if_true]
      exact Bs.sum_repr (w b)
    · intro b' _ hb
      simp [hb]
    · simp
  have hcomp : expChart H m = (fun σ => H m (perturb c X σ (trivialField m))) ∘ π := by
    funext w
    simp only [Function.comp, expChart, perturb_trivial_eq_fieldOfLie, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond m → imaginaryQuaternions) ?_ π.contDiff.contDiffAt
  simpa using ht.contDiffAt_perturb _ c X
def lineLift (Y : imaginaryQuaternions) : (TorusBond m → ℝ) →L[ℝ] (TorusBond m → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => (ContinuousLinearMap.proj b).smulRight Y
theorem abelianRestriction_eq_expChart_comp (Y : imaginaryQuaternions) :
    abelianRestriction H m Y = expChart H m ∘ lineLift Y := by
  funext θ
  rfl
theorem lineLift_single (Y : imaginaryQuaternions) (b : TorusBond m) :
    lineLift Y (Pi.single b (1 : ℝ)) = Pi.single b Y := by
  classical
  funext b'
  by_cases h : b' = b
  · subst h
    simp [lineLift]
  · simp [lineLift, Pi.single_apply, h]
theorem fderiv_abelianRestriction_isometry_invariant (ht : IsGaugeTotalAt H m) (X : imaginaryQuaternions)
    (g : TorusIsometry) (A : (TorusBond m → ℝ) →L[ℝ] (TorusBond m → ℝ))
    (hg : ∀ θ, g.Transports (abelianField X θ) (abelianField X (A θ))) (a : TorusBond m → ℝ) :
    fderiv ℝ (abelianRestriction H m X) 0 (A a) = fderiv ℝ (abelianRestriction H m X) 0 a := by
  have hC := contDiffAt_abelianRestriction X ht.contDiffAt_perturb
  have hd : DifferentiableAt ℝ (abelianRestriction H m X) 0 := hC.differentiableAt (by simp)
  have hlim : Tendsto (abelianField (n := m) X) (𝓝 0) (𝓝 (trivialField m)) := by
    have h := (continuous_abelianField (n := m) X).tendsto 0
    rwa [abelianField_zero] at h
  have hev : (abelianRestriction H m X ∘ A) =ᶠ[𝓝 0] abelianRestriction H m X := by
    filter_upwards [hlim.eventually (ht.isometry_invariant g)] with θ hθ
    exact hθ _ (hg θ)
  have h0 : DifferentiableAt ℝ (abelianRestriction H m X) (A 0) := by simpa using hd
  have e1 : fderiv ℝ (abelianRestriction H m X ∘ A) 0 = (fderiv ℝ (abelianRestriction H m X) 0).comp A := by
    rw [fderiv_comp 0 h0 A.differentiableAt, A.fderiv]
    simp
  rw [hev.fderiv_eq] at e1
  exact (DFunLike.congr_fun e1 a).symm
theorem fderiv_abelianRestriction_single (ht : IsGaugeTotalAt H m) (Y : imaginaryQuaternions)
    (b : TorusBond m) : fderiv ℝ (abelianRestriction H m Y) 0 (Pi.single b (1 : ℝ)) = 0 := by
  have h1 := fderiv_abelianRestriction_isometry_invariant ht Y reflectionIsometry reflectAngles
    (reflectionIsometry_transports Y) (Pi.single b (1 : ℝ))
  have h2 := fderiv_abelianRestriction_isometry_invariant ht Y (translationIsometry (-b.1 - unitStep m b.2 - b.1))
    (translateAngles (-b.1 - unitStep m b.2 - b.1)) (translationIsometry_transports Y _) (Pi.single b (1 : ℝ))
  rw [reflectAngles_single, map_neg] at h1
  rw [translateAngles_single] at h2
  have e : ((b.1 + (-b.1 - unitStep m b.2 - b.1), b.2) : TorusBond m) = (-b.1 - unitStep m b.2, b.2) := by
    refine Prod.ext ?_ rfl
    simp only
    abel
  rw [e] at h2
  linarith
theorem fderiv_expChart_zero (ht : IsGaugeTotalAt H m) : fderiv ℝ (expChart H m) 0 = 0 := by
  classical
  have hC := contDiffAt_expChart ht
  have hd : DifferentiableAt ℝ (expChart H m) 0 := hC.differentiableAt (by simp)
  have hsingle : ∀ (b : TorusBond m) (Y : imaginaryQuaternions),
      fderiv ℝ (expChart H m) 0 (Pi.single b Y) = 0 := by
    intro b Y
    have h0 : DifferentiableAt ℝ (expChart H m) (lineLift Y 0) := by simpa using hd
    have e1 : fderiv ℝ (expChart H m ∘ lineLift Y) 0 = (fderiv ℝ (expChart H m) 0).comp (lineLift Y) := by
      rw [fderiv_comp 0 h0 (lineLift Y).differentiableAt, (lineLift Y).fderiv]
      simp
    have h2 := fderiv_abelianRestriction_single ht Y b
    rw [abelianRestriction_eq_expChart_comp, e1] at h2
    simpa [lineLift_single] using h2
  ext w
  have e : w = ∑ b, Pi.single b (w b) := (Finset.univ_sum_single w).symm
  rw [e, map_sum]
  simp [hsingle]
theorem hessianAtTrivial_eq_fderiv_expChart (ht : IsGaugeTotalAt H m) (b b' : TorusBond m)
    (X X' : imaginaryQuaternions) :
    hessianAtTrivial H m b b' X X' =
      fderiv ℝ (fderiv ℝ (expChart H m)) 0 (Pi.single b X) (Pi.single b' X') := by
  classical
  let dirM : (Fin 2 → ℝ) →L[ℝ] (TorusBond m → imaginaryQuaternions) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single b X) +
      (ContinuousLinearMap.proj 1).smulRight (Pi.single b' X')
  have hcomp : (fun σ : Fin 2 → ℝ => H m (perturb ![b, b'] ![X, X'] σ (trivialField m))) =
      expChart H m ∘ dirM := by
    funext σ
    simp only [Function.comp, expChart, perturb_trivial_eq_fieldOfLie]
    congr 2
    funext b₀
    rw [Fin.sum_univ_two]
    simp only [dirM, Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply,
      Pi.single_apply]
    by_cases h1 : b = b₀ <;> by_cases h2 : b' = b₀ <;> simp [h1, h2, eq_comm]
  unfold hessianAtTrivial mixedDeriv
  rw [iteratedFDeriv_two_apply, hcomp, fderiv_fderiv_comp_clm (contDiffAt_expChart ht)]
  have d0 : dirM (Pi.single 0 1) = Pi.single b X := by
    simp [dirM]
  have d1 : dirM (Pi.single 1 1) = Pi.single b' X' := by
    simp [dirM]
  rw [d0, d1]
end ExponentialChart
section PullbackHessian
variable {L n : ℕ} [NeZero n] [NeZero (n * L)] {H : GaugeTotal} {p : BlockFieldMap L}
  {P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ}
theorem perturb_zero {m k : ℕ} (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    perturb c X 0 (trivialField m) = trivialField m := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.perturb_zero_trivialField <;> assumption
theorem perturb_pair_first {m : ℕ} (c c' : TorusBond m) (X X' : imaginaryQuaternions) (s : ℝ) :
    perturb ![c, c'] ![X, X'] (s • Pi.single 0 1) (trivialField m) = perturb ![c] ![X] ![s] (trivialField m) := by
  funext x i
  simp [perturb, Fin.sum_univ_two]
theorem perturb_pair_second {m : ℕ} (c c' : TorusBond m) (X X' : imaginaryQuaternions) (s : ℝ) :
    perturb ![c, c'] ![X, X'] (s • Pi.single 1 1) (trivialField m) = perturb ![c'] ![X'] ![s] (trivialField m) := by
  funext x i
  simp [perturb, Fin.sum_univ_two]
theorem imPart_smul_coe (r : ℝ) (X : imaginaryQuaternions) : imPart (r • (X : ℍ[ℝ])) = r • X := by
  rw [map_smul, imPart_coe]
theorem hessianAtTrivial_pullbackTotal (ht : IsGaugeTotalAt H (n * L)) (hflat : p n (trivialField n) = trivialField (n * L))
    (hsm : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * L)),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
        ((p n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0)
    (hfirst : ∀ (b : TorusBond (n * L)) (c : TorusBond n) (X : imaginaryQuaternions),
      HasDerivAt (fun s : ℝ => ((p n (perturb ![c] ![X] ![s] (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
        (P n b c • (X : ℍ[ℝ])) 0) (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial (pullbackTotal H p) n c c' X X' =
      ∑ b, ∑ b', P n b c * P n b' c' * hessianAtTrivial H (n * L) b b' X X' := by
  classical
  set u : TorusBond (n * L) → (Fin 2 → ℝ) → ℍ[ℝ] := fun b σ =>
    ((p n (perturb ![c, c'] ![X, X'] σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) with hu
  have hC : ∀ b, ContDiffAt ℝ 2 (u b) 0 := fun b => hsm 2 _ _ b
  have hu0 : ∀ b, u b 0 = 1 := by
    intro b
    simp only [hu, perturb_zero, hflat, trivialField]
    rfl
  set w : (Fin 2 → ℝ) → TorusBond (n * L) → imaginaryQuaternions := fun σ b => quaternionLog (u b σ) with hw
  have hlog : ∀ b, ContDiffAt ℝ 2 quaternionLog (u b 0) := fun b => by
    rw [hu0]
    exact contDiffAt_quaternionLog
  have hwC : ContDiffAt ℝ 2 w 0 := contDiffAt_pi.mpr fun b => (hlog b).comp 0 (hC b)
  have hw0 : w 0 = 0 := by
    funext b
    simp only [hw, hu0, quaternionLog_one]
    rfl
  have hcont : ∀ b, Tendsto (u b) (𝓝 0) (𝓝 1) := by
    intro b
    have := (hC b).continuousAt.tendsto
    rwa [hu0] at this
  have hexp : ∀ᶠ σ in 𝓝 (0 : Fin 2 → ℝ), ∀ b,
      NormedSpace.exp ((w σ b : imaginaryQuaternions) : ℍ[ℝ]) = u b σ := by
    rw [eventually_all]
    intro b
    filter_upwards [(hcont b).eventually exp_quaternionLog] with σ hσ
    refine hσ ?_
    have hu1 := (p n (perturb ![c, c'] ![X, X'] σ (trivialField n)) b.1 b.2).2
    have h := (Unitary.mem_iff.mp hu1).1
    rw [Quaternion.star_mul_self] at h
    have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h
    simpa using h2
  have hev : (fun σ : Fin 2 → ℝ => pullbackTotal H p n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =ᶠ[𝓝 0]
      expChart H (n * L) ∘ w := by
    filter_upwards [hexp] with σ hσ
    simp only [pullbackTotal, Function.comp, expChart]
    congr 1
    funext x i
    apply Subtype.ext
    exact (hσ (x, i)).symm
  have hfu : ∀ b, HasFDerivAt (u b) (fderiv ℝ (u b) 0) 0 := fun b =>
    ((hC b).differentiableAt (by simp)).hasFDerivAt
  have hfw : ∀ b, HasFDerivAt (fun σ => w σ b) (imPart.comp (fderiv ℝ (u b) 0)) 0 := by
    intro b
    have h1 : HasFDerivAt quaternionLog imPart (u b 0) := by
      rw [hu0]
      exact hasFDerivAt_quaternionLog_one
    exact h1.comp 0 (hfu b)
  have hfW : HasFDerivAt w (ContinuousLinearMap.pi fun b => imPart.comp (fderiv ℝ (u b) 0)) 0 :=
    hasFDerivAt_pi.mpr hfw
  have line : ∀ (l : Fin 2) (b : TorusBond (n * L)) (v : ℍ[ℝ]),
      HasDerivAt (fun s : ℝ => u b (s • Pi.single l 1)) v 0 →
      fderiv ℝ (u b) 0 (Pi.single l 1) = v := by
    intro l b v hv
    have h0 : HasDerivAt (fun s : ℝ => s • (Pi.single l 1 : Fin 2 → ℝ)) (Pi.single l 1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin 2 → ℝ)
    have h1 : HasFDerivAt (u b) (fderiv ℝ (u b) 0) ((0 : ℝ) • (Pi.single l 1 : Fin 2 → ℝ)) := by
      simpa using hfu b
    have h2 := h1.comp_hasDerivAt (0 : ℝ) h0
    exact h2.unique hv
  have hA : fderiv ℝ w 0 (Pi.single 0 1) = ∑ b, P n b c • Pi.single b X := by
    rw [hfW.fderiv]
    funext b
    have e := line 0 b _ (by
      have := hfirst b c X
      simp only [hu, perturb_pair_first]
      exact this)
    simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply, e, imPart_smul_coe,
      Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Pi.single_apply, hb.symm]
    · simp
  have hB : fderiv ℝ w 0 (Pi.single 1 1) = ∑ b, P n b c' • Pi.single b X' := by
    rw [hfW.fderiv]
    funext b
    have e := line 1 b _ (by
      have := hfirst b c' X'
      simp only [hu, perturb_pair_second]
      exact this)
    simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply, e, imPart_smul_coe,
      Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Pi.single_apply, hb.symm]
    · simp
  have hlhs : hessianAtTrivial (pullbackTotal H p) n c c' X X' = fderiv ℝ (fderiv ℝ
      (fun σ : Fin 2 → ℝ => pullbackTotal H p n (perturb ![c, c'] ![X, X'] σ (trivialField n)))) 0
      (Pi.single 0 1) (Pi.single 1 1) := by
    unfold hessianAtTrivial mixedDeriv
    rw [iteratedFDeriv_two_apply]
  rw [hlhs, hev.fderiv.fderiv_eq]
  have hcz := fderiv_fderiv_comp_of_fderiv_eq_zero (contDiffAt_expChart ht) hwC hw0 (fderiv_expChart_zero ht)
    (Pi.single 0 1) (Pi.single 1 1)
  rw [hcz, hA, hB]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [hessianAtTrivial_eq_fderiv_expChart ht]
  ring
end PullbackHessian
section PullbackDecay
section SupDistance
variable {n : ℕ}
def minimalCoords (u : TorusSite n) : Fin 4 → ℤ := fun i => (u i).valMinAbs
theorem minimalCoords_injective [NeZero n] : Function.Injective (minimalCoords (n := n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
theorem supDist_eq_offsetNorm (x y : TorusSite n) : supDist x y = offsetNorm (minimalCoords (x - y)) := rfl
theorem supDist_comm [NeZero n] (x y : TorusSite n) : supDist x y = supDist y x := by apply _root_.YangMills.Construction.TorusFields.supDist_comm <;> assumption
theorem supDist_triangle [NeZero n] (x y z : TorusSite n) : supDist x z ≤ supDist x y + supDist y z := by apply _root_.YangMills.Construction.TorusFields.supDist_triangle <;> assumption
theorem sum_exp_neg_supDist_le [NeZero n] {α : ℝ} (hα : 0 < α) (y : TorusSite n) :
    ∑ w : TorusSite n, Real.exp (-(α * supDist w y)) ≤
      ∑' z : Fin 4 → ℤ, Real.exp (-(α * offsetNormReal z)) := by
  classical
  have hs := summable_exp_neg_offsetNormReal hα
  have hinj : Function.Injective fun w : TorusSite n => minimalCoords (w - y) := fun a b h => by
    have := minimalCoords_injective h
    simpa using this
  calc ∑ w : TorusSite n, Real.exp (-(α * supDist w y))
      = ∑ z ∈ Finset.univ.image (fun w : TorusSite n => minimalCoords (w - y)),
          Real.exp (-(α * offsetNormReal z)) := by
        rw [Finset.sum_image fun a _ b _ h => hinj h]
        rfl
    _ ≤ _ := hs.sum_le_tsum _ fun z _ => (Real.exp_pos _).le
end SupDistance
theorem valMinAbs_blockCentre_sub {n L : ℕ} [NeZero n] [NeZero (n * L)] (hL : 0 < L) (a b : ZMod n) :
    (((L * a.val : ℕ) : ZMod (n * L)) - ((L * b.val : ℕ) : ZMod (n * L))).valMinAbs =
      (L : ℤ) * (a - b).valMinAbs := by
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨?_, ?_⟩
  · have hcast : ((a - b).valMinAbs : ZMod n) = a - b := ZMod.coe_valMinAbs _
    have h1 : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ZMod n) = (((a - b).valMinAbs : ℤ) : ZMod n) := by
      rw [hcast]
      simp
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp h1
    obtain ⟨k, hk⟩ := h2
    have h3 : (((L : ℤ) * ((a.val : ℤ) - (b.val : ℤ)) : ℤ) : ZMod (n * L)) =
        (((L : ℤ) * (a - b).valMinAbs : ℤ) : ZMod (n * L)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine ⟨k, ?_⟩
      push_cast
      rw [← mul_sub, hk]
      ring
    push_cast at h3 ⊢
    rw [← h3]
    ring
  · have h := (ZMod.valMinAbs_mem_Ioc (a - b))
    obtain ⟨h1, h2⟩ := h
    constructor
    · push_cast
      nlinarith
    · push_cast
      nlinarith
theorem supDist_le_blockCentreSite {n L : ℕ} [NeZero n] [NeZero (n * L)] (hL : 0 < L) (x y : TorusSite n) :
    supDist x y ≤ supDist (blockCentreSite L x) (blockCentreSite L y) := by
  refine Finset.sup_le fun i _ => ?_
  have h := Finset.le_sup
    (f := fun i => ((blockCentreSite L x i - blockCentreSite L y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : (blockCentreSite L x i - blockCentreSite L y i).valMinAbs = (L : ℤ) * (x i - y i).valMinAbs :=
    valMinAbs_blockCentre_sub hL (x i) (y i)
  have h2 : ((blockCentreSite L x i - blockCentreSite L y i).valMinAbs).natAbs ≤
      supDist (blockCentreSite L x) (blockCentreSite L y) := h
  rw [e, Int.natAbs_mul, Int.natAbs_natCast] at h2
  exact le_trans (Nat.le_mul_of_pos_left _ hL) h2
section Bounds
variable {m : ℕ} [NeZero m] {H : GaugeTotal}
theorem hessianAtTrivial_smul (ht : IsGaugeTotalAt H m) (b b' : TorusBond m) (r r' : ℝ)
    (X X' : imaginaryQuaternions) :
    hessianAtTrivial H m b b' (r • X) (r' • X') = r * r' * hessianAtTrivial H m b b' X X' := by
  rw [hessianAtTrivial_eq_fderiv_expChart ht, hessianAtTrivial_eq_fderiv_expChart ht]
  have e : ∀ (c : TorusBond m) (s : ℝ) (Y : imaginaryQuaternions),
      (Pi.single c (s • Y) : TorusBond m → imaginaryQuaternions) = s • Pi.single c Y := by
    intro c s Y
    funext c'
    by_cases h : c' = c
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [e, e]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
theorem hessianAtTrivial_zero_left (ht : IsGaugeTotalAt H m) (b b' : TorusBond m) (X' : imaginaryQuaternions) :
    hessianAtTrivial H m b b' 0 X' = 0 := by
  have := hessianAtTrivial_smul ht b b' 0 1 (0 : imaginaryQuaternions) X'
  simpa using this
theorem hessianAtTrivial_zero_right (ht : IsGaugeTotalAt H m) (b b' : TorusBond m) (X : imaginaryQuaternions) :
    hessianAtTrivial H m b b' X 0 = 0 := by
  have := hessianAtTrivial_smul ht b b' 1 0 X (0 : imaginaryQuaternions)
  simpa using this
theorem abs_hessianAtTrivial_le (ht : IsGaugeTotalAt H m) {B : ℝ} (b b' : TorusBond m)
    (hB : ∀ Y Y' : imaginaryQuaternions, ‖Y‖ = 1 → ‖Y'‖ = 1 → |hessianAtTrivial H m b b' Y Y'| ≤ B)
    (X X' : imaginaryQuaternions) :
    |hessianAtTrivial H m b b' X X'| ≤ ‖X‖ * ‖X'‖ * B := by
  by_cases h0 : X = 0
  · subst h0
    have hB0 : 0 ≤ ‖(0 : imaginaryQuaternions)‖ * ‖X'‖ * B := by simp
    rw [hessianAtTrivial_zero_left ht]
    simpa using hB0
  by_cases h1 : X' = 0
  · subst h1
    rw [hessianAtTrivial_zero_right ht]
    simp
  have n0 : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have n1 : ‖X'‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have e0 : X = ‖X‖ • (‖X‖⁻¹ • X) := by
    rw [smul_smul, mul_inv_cancel₀ n0, one_smul]
  have e1 : X' = ‖X'‖ • (‖X'‖⁻¹ • X') := by
    rw [smul_smul, mul_inv_cancel₀ n1, one_smul]
  have u0 : ‖‖X‖⁻¹ • X‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n0]
  have u1 : ‖‖X'‖⁻¹ • X'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1]
  have h := hB _ _ u0 u1
  conv_lhs => rw [e0, e1]
  rw [hessianAtTrivial_smul ht, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg X),
    abs_of_nonneg (norm_nonneg X')]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg _) (norm_nonneg _))
end Bounds
theorem sum_bonds_exp_neg_supDist_le {m : ℕ} [NeZero m] {α : ℝ} (hα : 0 < α) (y : TorusSite m) :
    ∑ b : TorusBond m, Real.exp (-(α * supDist b.1 y)) ≤
      4 * ∑' z : Fin 4 → ℤ, Real.exp (-(α * offsetNormReal z)) := by
  rw [Fintype.sum_prod_type]
  calc ∑ w : TorusSite m, ∑ _i : Fin 4, Real.exp (-(α * supDist w y))
      = 4 * ∑ w : TorusSite m, Real.exp (-(α * supDist w y)) := by
        simp [Finset.mul_sum]
    _ ≤ _ := by
        have := sum_exp_neg_supDist_le hα y
        linarith
section Decay
variable {L n : ℕ} [NeZero n] [NeZero (n * L)] {H : GaugeTotal}
  {P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ}
theorem abs_pullback_sum_le (hL : 0 < L) {MP MK θ : ℝ} (hMP : 0 ≤ MP) (hMK : 0 ≤ MK) (hθ : 0 < θ)
    (hP : ∀ (b : TorusBond (n * L)) (c : TorusBond n),
      |P n b c| ≤ MP * Real.exp (-(θ * supDist b.1 (blockCentreSite L c.1))))
    (hK : ∀ (c c' : TorusBond (n * L)) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      |hessianAtTrivial H (n * L) c c' X X'| ≤ MK * Real.exp (-(θ * supDist c.1 c'.1)))
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |∑ b, ∑ b', P n b c * P n b' c' * hessianAtTrivial H (n * L) b b' X X'| ≤
      (MP * MP * MK * (4 * ∑' z : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal z))) ^ 2) *
        Real.exp (-(θ / 2 * supDist c.1 c'.1)) := by
  set S : ℝ := 4 * ∑' z : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal z)) with hS
  have hθ2 : 0 < θ / 2 := half_pos hθ
  set E : ℝ := Real.exp (-(θ / 2 * supDist c.1 c'.1)) with hE
  have hterm : ∀ b b' : TorusBond (n * L), |P n b c * P n b' c' * hessianAtTrivial H (n * L) b b' X X'| ≤
      (MP * MP * MK * E) * (Real.exp (-(θ / 2 * supDist b.1 (blockCentreSite L c.1))) *
        Real.exp (-(θ / 2 * supDist b'.1 (blockCentreSite L c'.1)))) := by
    intro b b'
    rw [abs_mul, abs_mul]
    have e1 := hP b c
    have e2 := hP b' c'
    have e3 := hK b b' X X' hX hX'
    set A : ℝ := (supDist b.1 (blockCentreSite L c.1) : ℝ) with hA
    set B : ℝ := (supDist b'.1 (blockCentreSite L c'.1) : ℝ) with hB
    set C : ℝ := (supDist b.1 b'.1 : ℝ) with hC
    have tri : (supDist c.1 c'.1 : ℝ) ≤ A + C + B := by
      have t0 := supDist_le_blockCentreSite hL c.1 c'.1
      have t1 := supDist_triangle (blockCentreSite L c.1) b.1 (blockCentreSite L c'.1)
      have t2 := supDist_triangle b.1 b'.1 (blockCentreSite L c'.1)
      rw [supDist_comm (blockCentreSite L c.1) b.1] at t1
      have : supDist c.1 c'.1 ≤ supDist b.1 (blockCentreSite L c.1) + supDist b.1 b'.1 +
          supDist b'.1 (blockCentreSite L c'.1) := by omega
      calc (supDist c.1 c'.1 : ℝ) ≤ ((supDist b.1 (blockCentreSite L c.1) + supDist b.1 b'.1 +
            supDist b'.1 (blockCentreSite L c'.1) : ℕ) : ℝ) := Nat.cast_le.mpr this
        _ = A + C + B := by
            push_cast
            rfl
    have nC : 0 ≤ C := Nat.cast_nonneg _
    calc |P n b c| * |P n b' c'| * |hessianAtTrivial H (n * L) b b' X X'|
        ≤ (MP * Real.exp (-(θ * A))) * (MP * Real.exp (-(θ * B))) * (MK * Real.exp (-(θ * C))) := by
          gcongr
      _ = MP * MP * MK * Real.exp (-(θ * A) + -(θ * B) + -(θ * C)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ ≤ MP * MP * MK * Real.exp (-(θ / 2 * supDist c.1 c'.1) + (-(θ / 2 * A) + -(θ / 2 * B))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left tri hθ.le, mul_nonneg hθ.le nC]
      _ = _ := by
          rw [Real.exp_add, Real.exp_add]
          ring
  have hs1 := sum_bonds_exp_neg_supDist_le (m := n * L) hθ2 (blockCentreSite L c.1)
  have hs2 := sum_bonds_exp_neg_supDist_le (m := n * L) hθ2 (blockCentreSite L c'.1)
  have hs10 : 0 ≤ ∑ b : TorusBond (n * L), Real.exp (-(θ / 2 * supDist b.1 (blockCentreSite L c.1))) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hs20 : 0 ≤ ∑ b : TorusBond (n * L), Real.exp (-(θ / 2 * supDist b.1 (blockCentreSite L c'.1))) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc |∑ b, ∑ b', P n b c * P n b' c' * hessianAtTrivial H (n * L) b b' X X'|
      ≤ ∑ b, ∑ b', |P n b c * P n b' c' * hessianAtTrivial H (n * L) b b' X X'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L), (MP * MP * MK * E) *
          (Real.exp (-(θ / 2 * supDist b.1 (blockCentreSite L c.1))) *
            Real.exp (-(θ / 2 * supDist b'.1 (blockCentreSite L c'.1)))) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hterm b b'
    _ = (MP * MP * MK * E) *
          ((∑ b : TorusBond (n * L), Real.exp (-(θ / 2 * supDist b.1 (blockCentreSite L c.1)))) *
            ∑ b' : TorusBond (n * L), Real.exp (-(θ / 2 * supDist b'.1 (blockCentreSite L c'.1)))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (MP * MP * MK * E) * (S * S) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hs1 hs2 hs20 (hs10.trans hs1)
    _ = _ := by ring
end Decay
end PullbackDecay
section PullbackLimit
theorem sum_bonds_bonds_eq {m : ℕ} [NeZero m] (g : TorusBond m → TorusBond m → ℝ) :
    ∑ b, ∑ b', g b b' =
      ∑ ν : Fin 4, ∑ ν' : Fin 4, ∑ r : TorusSite m × TorusSite m, g (r.1, ν) (r.2, ν') := by
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (TorusSite m))) (t := (Finset.univ : Finset (Fin 4)))]
theorem siteOfInt_minimalCoords {m : ℕ} [NeZero m] (w : TorusSite m) :
    (siteOfInt (minimalCoords w) : TorusSite m) = w := by
  funext i
  simp [siteOfInt, minimalCoords]
theorem minimalCoords_siteOfInt {m : ℕ} [NeZero m] {z : Fin 4 → ℤ} (h : 2 * offsetNorm z + 1 < m) :
    minimalCoords (siteOfInt z : TorusSite m) = z := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_siteOfInt <;> assumption
theorem tendsto_mul_const_atTop {L : ℕ} (hL : 0 < L) : Tendsto (fun n : ℕ => n * L) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hL) tendsto_id
section Limit
variable {L : ℕ} {H : GaugeTotal} {K : LatticeBond → LatticeBond → ℝ} {p : BlockFieldMap L}
  {P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ} {Pl : LatticeBond → LatticeBond → ℝ}
open Classical in
def pullbackTerm (L : ℕ) (H : GaugeTotal) (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ) (ν ν' : Fin 4)
    (c c' : LatticeBond) (X X' : imaginaryQuaternions) (n : ℕ) (q : (Fin 4 → ℤ) × (Fin 4 → ℤ)) : ℝ :=
  if minimalCoords (siteOfInt q.1 : TorusSite (n * L)) = q.1 ∧
      minimalCoords (siteOfInt q.2 : TorusSite (n * L)) = q.2 then
    P n (siteOfInt q.1, ν) (bondFrom 0 c) * P n (siteOfInt q.2, ν') (bondFrom 0 c') *
      hessianAtTrivial H (n * L) (siteOfInt q.1, ν) (siteOfInt q.2, ν') X X' else 0
theorem sum_pullbackTerm (n : ℕ) [NeZero (n * L)] (ν ν' : Fin 4) (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    ∑ r : TorusSite (n * L) × TorusSite (n * L), P n (r.1, ν) (bondFrom 0 c) * P n (r.2, ν') (bondFrom 0 c') *
        hessianAtTrivial H (n * L) (r.1, ν) (r.2, ν') X X' =
      ∑' q, pullbackTerm L H P ν ν' c c' X X' n q := by
  classical
  have hinj : Function.Injective fun r : TorusSite (n * L) × TorusSite (n * L) =>
      (minimalCoords r.1, minimalCoords r.2) :=
    fun a b h => Prod.ext (minimalCoords_injective (Prod.ext_iff.mp h).1)
      (minimalCoords_injective (Prod.ext_iff.mp h).2)
  have hsup : Function.support (pullbackTerm L H P ν ν' c c' X X' n) ⊆
      Set.range fun r : TorusSite (n * L) × TorusSite (n * L) => (minimalCoords r.1, minimalCoords r.2) := by
    intro q hq
    have hc : minimalCoords (siteOfInt q.1 : TorusSite (n * L)) = q.1 ∧
        minimalCoords (siteOfInt q.2 : TorusSite (n * L)) = q.2 := by
      by_contra h
      exact hq (by simp [pullbackTerm, h])
    exact ⟨(siteOfInt q.1, siteOfInt q.2), Prod.ext hc.1 hc.2⟩
  rw [← hinj.tsum_eq hsup, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [pullbackTerm, siteOfInt_minimalCoords, if_true, and_self]
theorem tendsto_hessian_pullbackTotal (hL : 0 < L) (hK : IsLocalGaugeTotal atTop H K)
    (hM : IsBlockMap L p P Pl) (c c' : LatticeBond) (X X' : imaginaryQuaternions) :
    Tendsto (fun n => hessianAtTrivial (pullbackTotal H p) n (bondFrom 0 c) (bondFrom 0 c') X X') atTop
      (𝓝 (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * kernelPullback Pl K c c')) := by
  classical
  set I : ℝ := inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) with hI
  obtain ⟨MP, θP, hθP, hPd⟩ := hM.exp_decay
  obtain ⟨MK, θK, hθK, hKd⟩ := hK.exp_decay
  have htend := tendsto_mul_const_atTop hL
  have hKd' := htend.eventually hKd
  have hTot := htend.eventually hK.eventually_isGaugeTotalAt
  set θ : ℝ := min θK θP with hθdef
  have hθ : 0 < θ := lt_min hθK hθP
  have hMP : 0 ≤ MP := by
    obtain ⟨n, h1, h2⟩ := (hPd.and (eventually_gt_atTop 0)).exists
    have : NeZero n := ⟨h2.ne'⟩
    have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero h2.ne' hL.ne'⟩
    have a := h1 (bondFrom 0 (0, 0)) (bondFrom 0 (0, 0))
    by_contra hneg
    have hneg' : MP < 0 := not_le.mp hneg
    have := mul_neg_of_neg_of_pos hneg' (Real.exp_pos (-(θP * supDist (bondFrom (0 : TorusSite (n * L)) (0, 0)).1
      (blockCentreSite L (bondFrom (0 : TorusSite n) (0, 0)).1))))
    linarith [abs_nonneg (P n (bondFrom 0 (0, 0)) (bondFrom 0 (0, 0)))]
  have hMK : 0 ≤ MK := by
    obtain ⟨n, h1, h2⟩ := (hKd.and (eventually_gt_atTop 0)).exists
    have : NeZero n := ⟨h2.ne'⟩
    have a := h1 (bondFrom 0 (0, 0)) (bondFrom 0 (0, 0)) quaternionI quaternionI norm_quaternionI norm_quaternionI
    by_contra hneg
    have hneg' : MK < 0 := not_le.mp hneg
    have := mul_neg_of_neg_of_pos hneg' (Real.exp_pos (-(θK * supDist (bondFrom (0 : TorusSite n) (0, 0)).1
      (bondFrom (0 : TorusSite n) (0, 0)).1)))
    linarith [abs_nonneg (hessianAtTrivial H n (bondFrom 0 (0, 0)) (bondFrom 0 (0, 0)) quaternionI quaternionI)]
  set a₁ : Fin 4 → ℤ := (L : ℤ) • c.1 with ha₁
  set a₂ : Fin 4 → ℤ := (L : ℤ) • c'.1 with ha₂
  set B : (Fin 4 → ℤ) × (Fin 4 → ℤ) → ℝ := fun q =>
    ((MP * Real.exp (θ * offsetNormReal a₁)) * (MP * Real.exp (θ * offsetNormReal a₂)) * (‖X‖ * ‖X'‖ * MK) *
      Real.exp (-(θ * offsetNormReal q.1))) * Real.exp (-(θ * offsetNormReal q.2)) with hB
  have hBsum : Summable B :=
    Summable.mul_of_nonneg ((summable_exp_neg_offsetNormReal hθ).mul_left _) (summable_exp_neg_offsetNormReal hθ)
      (fun _ => by positivity) (fun _ => by positivity)
  have hPbound : ∀ᶠ n in atTop, ∀ (ν : Fin 4) (d : LatticeBond) (w : TorusSite (n * L)),
      2 * offsetNorm ((L : ℤ) • d.1) + 1 < n * L → 0 < n →
      |P n (w, ν) (bondFrom 0 d)| ≤ (MP * Real.exp (θ * offsetNormReal ((L : ℤ) • d.1))) *
        Real.exp (-(θ * offsetNormReal (minimalCoords w))) := by
    filter_upwards [hPd] with n hn ν d w hgt hpos
    have hn0 : NeZero n := ⟨hpos.ne'⟩
    have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero hpos.ne' hL.ne'⟩
    have a := hn (w, ν) (bondFrom 0 d)
    rw [bondFrom_zero] at a ⊢
    simp only at a
    rw [blockCentreSite_siteOfInt] at a
    set y : TorusSite (n * L) := siteOfInt ((L : ℤ) • d.1) with hy
    have t1 := supDist_triangle w y 0
    have t2 : supDist y (0 : TorusSite (n * L)) = offsetNorm ((L : ℤ) • d.1) := by
      have h0 : (0 : TorusSite (n * L)) = siteOfInt 0 := by
        funext i
        simp [siteOfInt]
      have hgt' : 2 * offsetNorm ((L : ℤ) • d.1 - 0) + 1 < n * L := by simpa using hgt
      rw [h0, hy, supDist_siteOfInt _ _ hgt']
      simp
    have t3 : supDist w (0 : TorusSite (n * L)) = offsetNorm (minimalCoords w) := by
      rw [supDist_eq_offsetNorm, sub_zero]
    have t4 : offsetNormReal (minimalCoords w) ≤ (supDist w y : ℝ) + offsetNormReal ((L : ℤ) • d.1) := by
      unfold offsetNormReal
      rw [t2, t3] at t1
      exact_mod_cast t1
    have hle : θ ≤ θP := min_le_right _ _
    have n0 : (0 : ℝ) ≤ supDist w y := Nat.cast_nonneg _
    refine a.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hMP
    nlinarith [mul_le_mul_of_nonneg_left t4 hθ.le, mul_le_mul_of_nonneg_right hle n0]
  have hFbound : ∀ (ν ν' : Fin 4), ∀ᶠ n in atTop, ∀ q,
      ‖pullbackTerm L H P ν ν' c c' X X' n q‖ ≤ B q := by
    intro ν ν'
    filter_upwards [hPbound, hKd', hTot, eventually_gt_atTop 0,
      htend.eventually (eventually_gt_atTop (2 * offsetNorm a₁ + 1)),
      htend.eventually (eventually_gt_atTop (2 * offsetNorm a₂ + 1))] with n hP1 hK1 hT1 hpos g1 g2 q
    have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero hpos.ne' hL.ne'⟩
    have hBq : 0 ≤ B q := by
      simp only [hB]
      positivity
    unfold pullbackTerm
    split_ifs with hc
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have p1 := hP1 ν c (siteOfInt q.1) g1 hpos
      have p2 := hP1 ν' c' (siteOfInt q.2) g2 hpos
      rw [hc.1] at p1
      rw [hc.2] at p2
      have k1 : |hessianAtTrivial H (n * L) (siteOfInt q.1, ν) (siteOfInt q.2, ν') X X'| ≤ ‖X‖ * ‖X'‖ * MK := by
        refine abs_hessianAtTrivial_le hT1 _ _ (fun Y Y' hY hY' => ?_) X X'
        refine (hK1 _ _ Y Y' hY hY').trans ?_
        have : Real.exp (-(θK * supDist ((siteOfInt q.1 : TorusSite (n * L)), ν).1
            ((siteOfInt q.2 : TorusSite (n * L)), ν').1)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ supDist ((siteOfInt q.1 : TorusSite (n * L)), ν).1
              ((siteOfInt q.2 : TorusSite (n * L)), ν').1 :=
            Nat.cast_nonneg _
          nlinarith
        nlinarith
      calc _ ≤ ((MP * Real.exp (θ * offsetNormReal a₁)) * Real.exp (-(θ * offsetNormReal q.1))) *
            ((MP * Real.exp (θ * offsetNormReal a₂)) * Real.exp (-(θ * offsetNormReal q.2))) *
              (‖X‖ * ‖X'‖ * MK) := by
            gcongr
        _ = B q := by
            simp only [hB]
            ring
    · simpa using hBq
  have hPlim : ∀ (b d : LatticeBond),
      Tendsto (fun n => P n (bondFrom 0 b) (bondFrom 0 d)) atTop (𝓝 (Pl b d)) :=
    hM.tendsto_kernel
  have hFlim : ∀ (ν ν' : Fin 4) (q : (Fin 4 → ℤ) × (Fin 4 → ℤ)),
      Tendsto (fun n => pullbackTerm L H P ν ν' c c' X X' n q) atTop
        (𝓝 (Pl (q.1, ν) c * Pl (q.2, ν') c' * (I * K (q.1, ν) (q.2, ν')))) := by
    intro ν ν' q
    have h1 := ((hPlim (q.1, ν) c).mul (hPlim (q.2, ν') c')).mul
      ((hK.tendsto_kernel (q.1, ν) (q.2, ν') X X').comp htend)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0, htend.eventually (eventually_gt_atTop (2 * offsetNorm q.1 + 1)),
      htend.eventually (eventually_gt_atTop (2 * offsetNorm q.2 + 1))] with n hpos g1 g2
    have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero hpos.ne' hL.ne'⟩
    have e1 := minimalCoords_siteOfInt g1
    have e2 := minimalCoords_siteOfInt g2
    simp only [pullbackTerm, e1, e2, and_self, if_true, Function.comp, bondFrom_zero]
  have hT : ∀ ν ν' : Fin 4, Tendsto (fun n => ∑' q, pullbackTerm L H P ν ν' c c' X X' n q) atTop
      (𝓝 (∑' q : (Fin 4 → ℤ) × (Fin 4 → ℤ), Pl (q.1, ν) c * Pl (q.2, ν') c' * (I * K (q.1, ν) (q.2, ν')))) :=
    fun ν ν' => tendsto_tsum_of_dominated_convergence hBsum (hFlim ν ν') (hFbound ν ν')
  have hAll := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin 4)) fun ν' _ => hT ν ν'
  have hg : ∀ ν ν' : Fin 4, Summable fun q : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      Pl (q.1, ν) c * Pl (q.2, ν') c' * (I * K (q.1, ν) (q.2, ν')) := by
    intro ν ν'
    refine Summable.of_norm_bounded hBsum fun q => ?_
    refine le_of_tendsto (hFlim ν ν' q).norm ?_
    filter_upwards [hFbound ν ν'] with n hn
    exact hn q
  have hval : ∑ ν : Fin 4, ∑ ν' : Fin 4, ∑' q : (Fin 4 → ℤ) × (Fin 4 → ℤ),
      Pl (q.1, ν) c * Pl (q.2, ν') c' * (I * K (q.1, ν) (q.2, ν')) = I * kernelPullback Pl K c c' := by
    unfold kernelPullback latticeBondSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have e1 : ∀ ν' : Fin 4, ∑' q : (Fin 4 → ℤ) × (Fin 4 → ℤ),
        Pl (q.1, ν) c * Pl (q.2, ν') c' * (I * K (q.1, ν) (q.2, ν')) =
        ∑' z : Fin 4 → ℤ, I * (Pl (z, ν) c * ∑' z' : Fin 4 → ℤ, K (z, ν) (z', ν') * Pl (z', ν') c') := by
      intro ν'
      rw [(hg ν ν').tsum_prod]
      refine tsum_congr fun z => ?_
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr fun z' => by ring
    simp_rw [e1]
    rw [← Summable.tsum_finsetSum, ← tsum_mul_left]
    · refine tsum_congr fun z => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    · intro ν' _
      have := (hg ν ν').prod
      refine this.congr fun z => ?_
      simp only
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr fun z' => by ring
  rw [hval] at hAll
  refine hAll.congr' ?_
  filter_upwards [hM.map_trivial, hM.contDiffAt_perturb, hM.hasDerivAt_perturb, hTot, eventually_gt_atTop 0]
    with n f1 f2 f3 f4 hpos
  have hn0 : NeZero n := ⟨hpos.ne'⟩
  have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero hpos.ne' hL.ne'⟩
  rw [hessianAtTrivial_pullbackTotal f4 f1 f2 f3, sum_bonds_bonds_eq]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ν' _ => ?_
  exact (sum_pullbackTerm n ν ν' c c' X X').symm
end Limit
end PullbackLimit
section MainProof
theorem pullbackKeepsSlopeCoefficient_of_secondMomentPullbackInvariant (hS : SecondMomentPullbackInvariant) :
    PullbackKeepsSlopeCoefficient := by
  intro L H p P Pl b hL hM ⟨K, hK, hsum⟩ hT
  have htend := tendsto_mul_const_atTop hL
  obtain ⟨MP, θP, hθP, hPd⟩ := hM.exp_decay
  obtain ⟨MK, θK, hθK, hKd⟩ := hK.exp_decay
  set θ : ℝ := min θK θP with hθdef
  have hθ : 0 < θ := lt_min hθK hθP
  have hloc : IsLocalGaugeTotal atTop (pullbackTotal H p) (kernelPullback Pl K) := by
    refine ⟨hT, ?_, tendsto_hessian_pullbackTotal hL hK hM⟩
    refine ⟨max MP 0 * max MP 0 * max MK 0 *
        (4 * ∑' z : Fin 4 → ℤ, Real.exp (-(θ / 2 * offsetNormReal z))) ^ 2, θ / 2, half_pos hθ, ?_⟩
    filter_upwards [hPd, htend.eventually hKd, htend.eventually hK.eventually_isGaugeTotalAt, hM.map_trivial,
      hM.contDiffAt_perturb, hM.hasDerivAt_perturb, eventually_gt_atTop 0] with n g1 g2 f4 f1 f2 f3 hpos
    have hn0 : NeZero n := ⟨hpos.ne'⟩
    have hnL : NeZero (n * L) := ⟨Nat.mul_ne_zero hpos.ne' hL.ne'⟩
    intro c c' X X' hX hX'
    rw [hessianAtTrivial_pullbackTotal f4 f1 f2 f3]
    refine abs_pullback_sum_le hL (le_max_right _ _) (le_max_right _ _) hθ (fun b d => ?_)
      (fun d d' Y Y' hY hY' => ?_) c c' X X' hX hX'
    · refine (g1 b d).trans ?_
      have h1 : (0 : ℝ) ≤ supDist b.1 (blockCentreSite L d.1) := Nat.cast_nonneg _
      have h2 : θ ≤ θP := min_le_right _ _
      refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (le_max_right _ _)
      nlinarith [mul_le_mul_of_nonneg_right h2 h1]
    · refine (g2 d d' Y Y' hY hY').trans ?_
      have h1 : (0 : ℝ) ≤ supDist d.1 d'.1 := Nat.cast_nonneg _
      have h2 : θ ≤ θK := min_le_left _ _
      refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (le_max_right _ _)
      nlinarith [mul_le_mul_of_nonneg_right h2 h1]
  refine ⟨kernelPullback Pl K, hloc, ?_⟩
  have hmom := hS L K Pl hL (isLatticeHessianKernel_of_isLocalGaugeTotal hK)
    (isLatticeBlockKernel_of_isBlockMap hL hM)
  have hb : b = -(1 / 2) * latticeSecondMoment K := by
    rw [← hsum.tsum_eq]
    unfold latticeSecondMoment
    rw [← tsum_mul_left]
    refine tsum_congr fun z => ?_
    simp only [secondMomentTerm]
    ring
  obtain ⟨M', θ', hθ', hd'⟩ := kernel_exp_decay hloc
  have hM' : 0 ≤ M' := by
    have := hd' (0, 0) (0, 0)
    have h0 : offsetNormReal ((0 : Fin 4 → ℤ) - 0) = 0 := by simp [offsetNormReal, offsetNorm]
    simp only [h0, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨C, -, hC⟩ := summable_mul_and_abs_tsum_le hθ'
    (SubexponentialGrowth.pow (subexponentialGrowth_coord 0) 2) one_pos
  have hs := (hC M' 0 (fun z => kernelPullback Pl K (0, secondAxis) (z, secondAxis)) hM'
    fun z => hd' _ _).1
  have hs2 : Summable (secondMomentTerm (kernelPullback Pl K)) := by
    refine (hs.mul_left (-(1 / 2))).congr fun z => ?_
    simp only [secondMomentTerm]
    ring
  have hv : ∑' z, secondMomentTerm (kernelPullback Pl K) z = b := by
    rw [hb, ← hmom]
    unfold latticeSecondMoment
    rw [← tsum_mul_left]
    refine tsum_congr fun z => ?_
    simp only [secondMomentTerm]
    ring
  rw [← hv]
  exact hs2.hasSum
end MainProof
end SlopeCoefficient.Pullback
end YangMills.Construction
end
