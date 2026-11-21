import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.ContourKernelsAreLocalProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.NumberOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps SlopeCoefficient
namespace RunningCouplingSlope.CoefficientFromDensity
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem eventually_differentiableAt_of_contDiffAt {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∀ᶠ A in 𝓝 (0 : E), DifferentiableAt ℝ f A :=
  (hf.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
theorem fderiv_fderiv_comp_clm {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (L : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_comp_clm <;> assumption
theorem fderiv_fderiv_apply_eq_zero_of_eventually {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (w : F)
    (h : ∀ᶠ θ in 𝓝 (0 : F), fderiv ℝ Ψ θ w = 0) (u : F) : fderiv ℝ (fderiv ℝ Ψ) 0 u w = 0 := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.fderiv_fderiv_apply_eq_zero_of_eventually <;> assumption
theorem fderiv_sub_const_fun (f : E → ℝ) (c : ℝ) :
    fderiv ℝ (fun θ => f θ - c) = fderiv ℝ f := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.fderiv_sub_const_fun <;> assumption
theorem fderiv_fderiv_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0) (u v : E) :
    fderiv ℝ (fderiv ℝ fun θ => ∑ i ∈ s, f i θ) 0 u v =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) 0 u v := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_sum <;> assumption
end Calculus
section Fields
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_smul_mul_smul (X : imaginaryQuaternions) (u v : ℝ) :
    expUnit (u • X) * expUnit (v • X) = expUnit ((u + v) • X) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
theorem expUnit_smul_inv (X : imaginaryQuaternions) (u : ℝ) :
    (expUnit (u • X))⁻¹ = expUnit ((-u) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
variable {n : ℕ} [NeZero n]
def abelianField (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (θ (x, i) • X)
def abelianRestrict (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions)
    (θ : TorusBond n → ℝ) : ℝ :=
  H n (abelianField X θ)
def weightedBondMap {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    w l • (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ) else 0
theorem weightedBondMap_apply {k : ℕ} (c : Fin k → TorusBond n) (w σ : Fin k → ℝ) (b : TorusBond n) :
    weightedBondMap c w σ b = ∑ l, if c l = b then w l * σ l else 0 := by
  simp only [weightedBondMap, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem weightedBondMap_single {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ) (l : Fin k) :
    weightedBondMap c w (Pi.single l 1) = w l • Pi.single (c l) (1 : ℝ) := by
  funext b
  rw [weightedBondMap_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
theorem perturb_smul_trivialField {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ)
    (X : imaginaryQuaternions) (σ : Fin k → ℝ) :
    perturb c (fun l => w l • X) σ (trivialField n) = abelianField X (weightedBondMap c w σ) := by
  funext x i
  have h : (∑ l, if c l = (x, i) then σ l • (w l • X) else 0) = (weightedBondMap c w σ (x, i)) • X := by
    rw [weightedBondMap_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [smul_smul, mul_comm]
    · simp
  simp only [perturb, trivialField, abelianField, mul_one, h]
theorem perturb_comp_eq {H : GaugeTotal} {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ)
    (X : imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => H n (perturb c (fun l => w l • X) σ (trivialField n))) =
      abelianRestrict H n X ∘ weightedBondMap c w := by
  funext σ
  simp only [Function.comp, abelianRestrict, perturb_smul_trivialField]
theorem contDiffAt_abelianRestrict {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0) :
    ContDiffAt ℝ 2 (abelianRestrict H n X) 0 := by
  classical
  let e := Fintype.equivFin (TorusBond n)
  let c : Fin (Fintype.card (TorusBond n)) → TorusBond n := e.symm
  let w : Fin (Fintype.card (TorusBond n)) → ℝ := fun _ => 1
  let π₀ : (TorusBond n → ℝ) →ₗ[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    { toFun := fun θ l => θ (c l)
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  let π : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ θ : TorusBond n → ℝ, weightedBondMap c w (π θ) = θ := by
    intro θ
    funext b
    rw [weightedBondMap_apply, Finset.sum_eq_single (e b)]
    · simp [c, π, π₀, w]
    · intro l _ hl
      have : c l ≠ b := fun h => hl (by simp [← h, c])
      simp [this]
    · simp
  have hφ := hs _ c fun l => w l • X
  have hcomp : abelianRestrict H n X =
      (fun σ => H n (perturb c (fun l => w l • X) σ (trivialField n))) ∘ π := by
    funext θ
    simp only [Function.comp, perturb_smul_trivialField, abelianRestrict, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond n → ℝ) ?_ π.contDiff.contDiffAt
  simpa using hφ
def abelianHessian (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions) :
    (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (abelianRestrict H n X)) 0
theorem mixedDeriv_smul {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (c c' : TorusBond n) (a a' : ℝ) :
    mixedDeriv (H n) (trivialField n) ![c, c'] ![a • X, a' • X] =
      a * a' * abelianHessian H n X (Pi.single c 1) (Pi.single c' 1) := by
  have hX : (![a • X, a' • X] : Fin 2 → imaginaryQuaternions) = fun l => (![a, a'] : Fin 2 → ℝ) l • X := by
    funext l
    fin_cases l <;> rfl
  unfold mixedDeriv
  rw [hX, iteratedFDeriv_two_apply, perturb_comp_eq (H := H) (![c, c'] : Fin 2 → TorusBond n) ![a, a'] X,
    fderiv_fderiv_comp_clm (contDiffAt_abelianRestrict X hs), weightedBondMap_single,
    weightedBondMap_single]
  simp only [abelianHessian, Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
theorem abelianHessian_symm {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (u v : TorusBond n → ℝ) :
    abelianHessian H n X u v = abelianHessian H n X v u :=
  ((contDiffAt_abelianRestrict X hs).isSymmSndFDerivAt (by simp)) u v
def latticeGradient (φ : TorusSite n → ℝ) : TorusBond n → ℝ :=
  fun b => φ (b.1 + TorusFields.unitStep n b.2) - φ b.1
theorem gaugeTransform_abelianField (X : imaginaryQuaternions) (φ : TorusSite n → ℝ) (s : ℝ)
    (θ : TorusBond n → ℝ) :
    TorusFields.gaugeTransform (fun x => expUnit ((s * φ x) • X)) (abelianField X θ) =
      abelianField X (θ - s • latticeGradient φ) := by
  funext x i
  simp only [TorusFields.gaugeTransform, abelianField, expUnit_smul_inv, expUnit_smul_mul_smul]
  congr 2
  simp only [Pi.sub_apply, Pi.smul_apply, latticeGradient, smul_eq_mul]
  ring
theorem continuous_abelianField (X : imaginaryQuaternions) : Continuous (abelianField (n := n) X) :=
  continuous_pi fun x => continuous_pi fun i =>
    continuous_expUnit.comp ((continuous_apply (x, i)).smul continuous_const)
theorem abelianField_zero (X : imaginaryQuaternions) : abelianField (n := n) X 0 = trivialField n := by
  funext x i
  simp [abelianField, trivialField, expUnit_zero]
theorem tendsto_abelianField (X : imaginaryQuaternions) :
    Tendsto (abelianField (n := n) X) (𝓝 0) (𝓝 (trivialField n)) := by
  have := (continuous_abelianField (n := n) X).tendsto 0
  rwa [abelianField_zero] at this
theorem abelianHessian_gradient {H : GaugeTotal} (X : imaginaryQuaternions)
    (hg : IsGaugeFunctionNear H n) (φ : TorusSite n → ℝ)
    (u : TorusBond n → ℝ) : abelianHessian H n X u (latticeGradient φ) = 0 := by
  have hC := contDiffAt_abelianRestrict X hg.contDiffAt_perturb
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
      abelianRestrict H n X (p.1 - p.2 • latticeGradient φ) = abelianRestrict H n X p.1 := by
    rw [← nhds_prod_eq]
    filter_upwards [hinv] with p hp
    rw [gaugeTransform_abelianField] at hp
    exact hp
  have hcur := hprod.curry
  filter_upwards [hcur, eventually_differentiableAt_of_contDiffAt hC] with θ hθ hd
  have hcurve : HasDerivAt (fun s : ℝ => θ - s • latticeGradient φ) (-latticeGradient φ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (latticeGradient φ)).const_sub θ
    simpa using this
  have hd' : HasFDerivAt (abelianRestrict H n X) (fderiv ℝ (abelianRestrict H n X) θ)
      (θ - (0 : ℝ) • latticeGradient φ) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hcurve
  have h2 : HasDerivAt (fun s : ℝ => abelianRestrict H n X (θ - s • latticeGradient φ)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (abelianRestrict H n X θ)).congr_of_eventuallyEq hθ
  have h3 := h1.unique h2
  simpa using h3
theorem latticeGradient_single (u : TorusSite n) :
    latticeGradient (Pi.single u (1 : ℝ)) =
      ∑ i, (Pi.single (u - TorusFields.unitStep n i, i) (1 : ℝ) - Pi.single (u, i) (1 : ℝ) : TorusBond n → ℝ) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.latticeGradient_single <;> assumption
def angleTranslate (u : TorusSite n) : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (b.1 + u, b.2)
theorem angleTranslate_single (u : TorusSite n) (c : TorusBond n) :
    angleTranslate u (Pi.single c 1) = Pi.single (c.1 - u, c.2) (1 : ℝ) := by
  classical
  funext ⟨x, i⟩
  simp only [angleTranslate, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  have : ((x + u, i) = c) ↔ ((x, i) = (c.1 - u, c.2)) := by
    obtain ⟨y, j⟩ := c
    simp [eq_sub_iff_add_eq]
  simp [this]
theorem translate_abelianField (X : imaginaryQuaternions) (u : TorusSite n) (θ : TorusBond n → ℝ) :
    TorusFields.translate u (abelianField X θ) = abelianField X (angleTranslate u θ) := by
  funext x i
  simp [TorusFields.translate, abelianField, angleTranslate]
end Fields
section Sums
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
def siteWeight (c : ℝ) (h : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(c * offsetNorm h)) * (1 + (offsetNorm h : ℝ)) ^ 4
theorem siteWeight_nonneg (c : ℝ) (h : Fin 4 → ℤ) : 0 ≤ siteWeight c h := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.expPolyWeight_nonneg <;> assumption
theorem natAbs_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem summable_siteWeight {c : ℝ} (hc : 0 < c) : Summable (siteWeight c) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_expPolyWeight <;> assumption
def bondWeight (c : ℝ) (b : LatticeBond) : ℝ := siteWeight c b.1
theorem bondWeight_nonneg (c : ℝ) (b : LatticeBond) : 0 ≤ bondWeight c b := siteWeight_nonneg c b.1
theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by
  have h := (summable_siteWeight hc).mul_of_nonneg (g := fun _ : Fin 4 => (1 : ℝ))
    (hasSum_fintype _).summable (siteWeight_nonneg c) (fun _ => zero_le_one)
  show Summable fun x : (Fin 4 → ℤ) × Fin 4 => siteWeight c x.1
  simpa using h
def latticeUnit (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
theorem offsetNorm_add_latticeUnit (z : Fin 4 → ℤ) (i : Fin 4) :
    offsetNorm (z + latticeUnit i) ≤ offsetNorm z + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
theorem abs_coord_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) :
    |((z i : ℤ) : ℝ)| ≤ (offsetNorm z : ℝ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.abs_coord_le_offsetNorm <;> assumption
def IsQuarticGrowth (f : LatticeBond → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ c, |f c| ≤ C * (1 + (offsetNorm c.1 : ℝ)) ^ 4
def IsCubicGrowth (ψ : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |ψ z| ≤ C * (1 + (offsetNorm z : ℝ)) ^ 3
def bondDifference (ψ : (Fin 4 → ℤ) → ℝ) (c : LatticeBond) : ℝ := ψ (c.1 + latticeUnit c.2) - ψ c.1
theorem quarticGrowth_of_cubic {ψ : (Fin 4 → ℤ) → ℝ} (hψ : IsCubicGrowth ψ) :
    IsQuarticGrowth fun c => ψ c.1 := by
  obtain ⟨C, hC, h⟩ := hψ
  refine ⟨C, hC, fun c => (h c.1).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact pow_le_pow_right₀ (by linarith) (by norm_num)
theorem quarticGrowth_of_cubic_shift {ψ : (Fin 4 → ℤ) → ℝ} (hψ : IsCubicGrowth ψ) :
    IsQuarticGrowth fun c => ψ (c.1 + latticeUnit c.2) := by
  obtain ⟨C, hC, h⟩ := hψ
  refine ⟨8 * C, by positivity, fun c => (h _).trans ?_⟩
  set s : ℝ := (offsetNorm c.1 : ℝ) with hs
  have h1 : (offsetNorm (c.1 + latticeUnit c.2) : ℝ) ≤ s + 1 := by
    rw [hs]
    exact_mod_cast offsetNorm_add_latticeUnit c.1 c.2
  have h3 : (1 + (offsetNorm (c.1 + latticeUnit c.2) : ℝ)) ^ 3 ≤ (2 * (1 + s)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h4 : (1 + s) ^ 3 ≤ (1 + s) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  calc C * (1 + (offsetNorm (c.1 + latticeUnit c.2) : ℝ)) ^ 3 ≤ C * (2 * (1 + s)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hC
    _ = 8 * C * (1 + s) ^ 3 := by ring
    _ ≤ 8 * C * (1 + s) ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
theorem IsQuarticGrowth.sub {f g : LatticeBond → ℝ} (hf : IsQuarticGrowth f) (hg : IsQuarticGrowth g) :
    IsQuarticGrowth fun c => f c - g c := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, by positivity, fun c => ?_⟩
  have := abs_sub (f c) (g c)
  have h1 := hf c
  have h2 := hg c
  nlinarith
theorem quarticGrowth_bondDifference {ψ : (Fin 4 → ℤ) → ℝ} (hψ : IsCubicGrowth ψ) :
    IsQuarticGrowth (bondDifference ψ) :=
  (quarticGrowth_of_cubic_shift hψ).sub (quarticGrowth_of_cubic hψ)
structure IsDecayingGaugeKernel (q : LatticeBond → LatticeBond → ℝ) (M θ : ℝ) : Prop where
  rate_pos : 0 < θ
  const_nonneg : 0 ≤ M
  abs_le : ∀ c c', |q c c'| ≤ M * Real.exp (-(θ * (max (offsetNorm c.1) (offsetNorm c'.1) : ℕ)))
  symm : ∀ c c', q c c' = q c' c
  divergence_free : ∀ (u : Fin 4 → ℤ) (c' : LatticeBond),
    ∑ i, (q (u - latticeUnit i, i) c' - q (u, i) c') = 0
variable {q : LatticeBond → LatticeBond → ℝ} {M θ : ℝ}
theorem summable_kernel_mul_mul (hq : IsDecayingGaugeKernel q M θ) {f g : LatticeBond → ℝ}
    (hf : IsQuarticGrowth f) (hg : IsQuarticGrowth g) :
    Summable fun cc : LatticeBond × LatticeBond => q cc.1 cc.2 * f cc.1 * g cc.2 := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  have hθ : 0 < θ / 2 := half_pos hq.rate_pos
  have hs := ((summable_bondWeight hθ).mul_of_nonneg (summable_bondWeight hθ) (bondWeight_nonneg _)
    (bondWeight_nonneg _)).mul_left (M * C * D)
  refine Summable.of_norm_bounded hs fun cc => ?_
  obtain ⟨c, c'⟩ := cc
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  set s : ℝ := (offsetNorm c.1 : ℝ) with hs1
  set s' : ℝ := (offsetNorm c'.1 : ℝ) with hs2
  have hexp : Real.exp (-(θ * (max (offsetNorm c.1) (offsetNorm c'.1) : ℕ))) ≤
      Real.exp (-(θ / 2 * s)) * Real.exp (-(θ / 2 * s')) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : s ≤ ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ) := by
      rw [hs1]
      exact_mod_cast le_max_left _ _
    have h2 : s' ≤ ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ) := by
      rw [hs2]
      exact_mod_cast le_max_right _ _
    nlinarith [hq.rate_pos]
  have hb := (hq.abs_le c c').trans (mul_le_mul_of_nonneg_left hexp hq.const_nonneg)
  have hfc : |f c| ≤ C * (1 + s) ^ 4 := hf c
  have hgc : |g c'| ≤ D * (1 + s') ^ 4 := hg c'
  have hB0 : 0 ≤ M * (Real.exp (-(θ / 2 * s)) * Real.exp (-(θ / 2 * s'))) :=
    mul_nonneg hq.const_nonneg (by positivity)
  have hA0 : 0 ≤ C * (1 + s) ^ 4 := by positivity
  simp only [bondWeight, siteWeight]
  rw [← hs1, ← hs2]
  calc |q c c'| * |f c| * |g c'|
      ≤ (M * (Real.exp (-(θ / 2 * s)) * Real.exp (-(θ / 2 * s')))) * (C * (1 + s) ^ 4) *
          (D * (1 + s') ^ 4) :=
        mul_le_mul (mul_le_mul hb hfc (abs_nonneg _) hB0) hgc (abs_nonneg _) (mul_nonneg hB0 hA0)
    _ = _ := by ring
theorem quarticGrowth_one : IsQuarticGrowth fun _ => 1 := by
  refine ⟨1, zero_le_one, fun c => ?_⟩
  have : (1 : ℝ) ≤ (1 + (offsetNorm c.1 : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
  simpa using this
theorem summable_kernel_mul_left (hq : IsDecayingGaugeKernel q M θ) {f : LatticeBond → ℝ}
    (hf : IsQuarticGrowth f) (c' : LatticeBond) :
    Summable fun c => q c c' * f c := by
  have h := (summable_kernel_mul_mul hq quarticGrowth_one hf).prod_factor c'
  refine h.congr fun c => ?_
  rw [hq.symm c' c]
  ring
theorem tsum_kernel_mul_bondDifference (hq : IsDecayingGaugeKernel q M θ) {ψ : (Fin 4 → ℤ) → ℝ}
    (hψ : IsCubicGrowth ψ) (c' : LatticeBond) :
    ∑' c, q c c' * bondDifference ψ c = 0 := by
  have hA : ∀ i, Summable fun x => q (x, i) c' * ψ (x + latticeUnit i) := fun i => by
    have h := (summable_kernel_mul_left hq (quarticGrowth_of_cubic_shift hψ) c')
    exact h.comp_injective (i := fun x => ((x, i) : LatticeBond)) fun a b hab => (Prod.ext_iff.mp hab).1
  have hB : ∀ i, Summable fun x => q (x, i) c' * ψ x := fun i => by
    have h := (summable_kernel_mul_left hq (quarticGrowth_of_cubic hψ) c')
    exact h.comp_injective (i := fun x => ((x, i) : LatticeBond)) fun a b hab => (Prod.ext_iff.mp hab).1
  have hG := summable_kernel_mul_left hq (quarticGrowth_bondDifference hψ) c'
  have hshift : ∀ i, ∑' x, q (x, i) c' * ψ (x + latticeUnit i) =
      ∑' u, q (u - latticeUnit i, i) c' * ψ u := fun i => by
    have := (Equiv.subRight (latticeUnit i)).tsum_eq fun x => q (x, i) c' * ψ (x + latticeUnit i)
    rw [← this]
    refine tsum_congr fun u => ?_
    simp
  have hA' : ∀ i, Summable fun u => q (u - latticeUnit i, i) c' * ψ u := fun i => by
    have := (Equiv.subRight (latticeUnit i)).summable_iff.mpr (hA i)
    refine this.congr fun u => ?_
    simp
  calc ∑' c, q c c' * bondDifference ψ c
      = ∑' x, ∑' i, q ((x, i) : LatticeBond) c' * bondDifference ψ (x, i) := hG.tsum_prod
    _ = ∑' x, ∑ i, q ((x, i) : LatticeBond) c' * bondDifference ψ (x, i) := by simp only [tsum_fintype]
    _ = ∑ i, ∑' x, q ((x, i) : LatticeBond) c' * bondDifference ψ (x, i) :=
        Summable.tsum_finsetSum fun i _ => by
          have := (hA i).sub (hB i)
          refine this.congr fun x => ?_
          simp only [bondDifference]
          ring
    _ = ∑ i, (∑' u, q (u - latticeUnit i, i) c' * ψ u - ∑' u, q (u, i) c' * ψ u) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hshift, ← (hA i).tsum_sub (hB i)]
        refine tsum_congr fun x => ?_
        simp only [bondDifference]
        ring
    _ = ∑ i, ∑' u, (q (u - latticeUnit i, i) c' - q (u, i) c') * ψ u := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (hA' i).tsum_sub (hB i)]
        refine tsum_congr fun u => ?_
        ring
    _ = ∑' u, ∑ i, (q (u - latticeUnit i, i) c' - q (u, i) c') * ψ u :=
        (Summable.tsum_finsetSum fun i _ => by
          have := (hA' i).sub (hB i)
          refine this.congr fun u => ?_
          ring).symm
    _ = 0 := by
        have : ∀ u, ∑ i, (q (u - latticeUnit i, i) c' - q (u, i) c') * ψ u = 0 := fun u => by
          rw [← Finset.sum_mul, hq.divergence_free u c', zero_mul]
        simp only [this, tsum_zero]
theorem hasSum_zero_bondDifference_left (hq : IsDecayingGaugeKernel q M θ) {ψ : (Fin 4 → ℤ) → ℝ}
    (hψ : IsCubicGrowth ψ) {g : LatticeBond → ℝ} (hg : IsQuarticGrowth g) :
    HasSum (fun cc : LatticeBond × LatticeBond => q cc.1 cc.2 * bondDifference ψ cc.1 * g cc.2) 0 := by
  have S := summable_kernel_mul_mul hq (quarticGrowth_bondDifference hψ) hg
  have S' := (Equiv.prodComm LatticeBond LatticeBond).summable_iff.mpr S
  have h : ∑' cc : LatticeBond × LatticeBond, q cc.1 cc.2 * bondDifference ψ cc.1 * g cc.2 = 0 := by
    have e := (Equiv.prodComm LatticeBond LatticeBond).tsum_eq
      (fun cc : LatticeBond × LatticeBond => q cc.1 cc.2 * bondDifference ψ cc.1 * g cc.2)
    have hz : ∀ c', ∑' c, q c c' * bondDifference ψ c * g c' = 0 := fun c' => by
      rw [tsum_mul_right, tsum_kernel_mul_bondDifference hq hψ c', zero_mul]
    rw [← e]
    refine S'.tsum_prod.trans ?_
    simpa [Function.comp_def] using tsum_congr hz
  rw [← h]
  exact S.hasSum
theorem hasSum_zero_bondDifference_right (hq : IsDecayingGaugeKernel q M θ) {ψ : (Fin 4 → ℤ) → ℝ}
    (hψ : IsCubicGrowth ψ) {f : LatticeBond → ℝ} (hf : IsQuarticGrowth f) :
    HasSum (fun cc : LatticeBond × LatticeBond => q cc.1 cc.2 * f cc.1 * bondDifference ψ cc.2) 0 := by
  have S := summable_kernel_mul_mul hq hf (quarticGrowth_bondDifference hψ)
  have h : ∑' cc : LatticeBond × LatticeBond, q cc.1 cc.2 * f cc.1 * bondDifference ψ cc.2 = 0 := by
    rw [S.tsum_prod]
    have : ∀ c, ∑' c', q c c' * f c * bondDifference ψ c' = 0 := fun c => by
      have h1 : ∀ c', q c c' * f c * bondDifference ψ c' = f c * (q c' c * bondDifference ψ c') :=
        fun c' => by
          rw [hq.symm c c']
          ring
      simp only [h1]
      rw [tsum_mul_left, tsum_kernel_mul_bondDifference hq hψ c, mul_zero]
    simpa using tsum_congr this
  rw [← h]
  exact S.hasSum
end Sums
section Number
variable {q : LatticeBond → LatticeBond → ℝ} {M θ : ℝ}
def secondAxisIndicator (c : LatticeBond) : ℝ := if c.2 = secondAxis then 1 else 0
def secondAxisFirstCoord (c : LatticeBond) : ℝ :=
  if c.2 = secondAxis then ((c.1 0 : ℤ) : ℝ) else 0
def secondAxisFirstCoordSq (c : LatticeBond) : ℝ :=
  if c.2 = secondAxis then ((c.1 0 : ℤ) : ℝ) ^ 2 else 0
def secondCoordinate (z : Fin 4 → ℤ) : ℝ := ((z 1 : ℤ) : ℝ)
def halfCoordProduct (z : Fin 4 → ℤ) : ℝ := ((z 0 : ℤ) : ℝ) * ((z 1 : ℤ) : ℝ) / 2
def linearPotentialCoeff (c : LatticeBond) : ℝ :=
  secondAxisFirstCoord c - bondDifference halfCoordProduct c
theorem bondDifference_secondCoordinate : bondDifference secondCoordinate = secondAxisIndicator := by
  funext ⟨z, i⟩
  by_cases hi : i = secondAxis
  · subst hi
    simp [bondDifference, secondCoordinate, secondAxisIndicator, latticeUnit, secondAxis]
  · have : (1 : Fin 4) ≠ i := fun h => hi (by rw [← h]; rfl)
    simp [bondDifference, secondCoordinate, secondAxisIndicator, latticeUnit, hi, Pi.single_apply,
      this.symm]
theorem sq_le_one_add_pow_three (s : ℝ) (hs : 0 ≤ s) : s ^ 2 ≤ (1 + s) ^ 3 := by
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs]
theorem cubicGrowth_secondCoordinate : IsCubicGrowth secondCoordinate := by
  refine ⟨1, zero_le_one, fun z => ?_⟩
  have hs : (0 : ℝ) ≤ offsetNorm z := Nat.cast_nonneg _
  have h := abs_coord_le_offsetNorm z 1
  have : (offsetNorm z : ℝ) ≤ (1 + (offsetNorm z : ℝ)) ^ 3 := by
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs]
  simp only [secondCoordinate, one_mul]
  linarith
theorem cubicGrowth_halfCoordProduct : IsCubicGrowth halfCoordProduct := by
  refine ⟨1, zero_le_one, fun z => ?_⟩
  have hs : (0 : ℝ) ≤ offsetNorm z := Nat.cast_nonneg _
  have h0 := abs_coord_le_offsetNorm z 0
  have h1 := abs_coord_le_offsetNorm z 1
  have h2 : |((z 0 : ℤ) : ℝ) * ((z 1 : ℤ) : ℝ)| ≤ (offsetNorm z : ℝ) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul h0 h1 (abs_nonneg _) hs
  have h3 := sq_le_one_add_pow_three _ hs
  simp only [halfCoordProduct, one_mul, abs_div, abs_two]
  have h4 := abs_nonneg (((z 0 : ℤ) : ℝ) * ((z 1 : ℤ) : ℝ))
  linarith
theorem quarticGrowth_secondAxisFirstCoord : IsQuarticGrowth secondAxisFirstCoord := by
  refine ⟨1, zero_le_one, fun c => ?_⟩
  have hs : (0 : ℝ) ≤ offsetNorm c.1 := Nat.cast_nonneg _
  have h := abs_coord_le_offsetNorm c.1 0
  have h2 : (offsetNorm c.1 : ℝ) ≤ (1 + (offsetNorm c.1 : ℝ)) ^ 4 := by
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs,
      mul_nonneg (mul_nonneg hs hs) (mul_nonneg hs hs)]
  simp only [secondAxisFirstCoord, one_mul]
  split_ifs
  · linarith
  · simpa using (hs.trans h2)
theorem quarticGrowth_secondAxisFirstCoordSq : IsQuarticGrowth secondAxisFirstCoordSq := by
  refine ⟨1, zero_le_one, fun c => ?_⟩
  have hs : (0 : ℝ) ≤ offsetNorm c.1 := Nat.cast_nonneg _
  have h := abs_coord_le_offsetNorm c.1 0
  have h1 : |((c.1 0 : ℤ) : ℝ) ^ 2| ≤ (offsetNorm c.1 : ℝ) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : (offsetNorm c.1 : ℝ) ^ 2 ≤ (1 + (offsetNorm c.1 : ℝ)) ^ 4 := by
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs,
      mul_nonneg (mul_nonneg hs hs) (mul_nonneg hs hs)]
  simp only [secondAxisFirstCoordSq, one_mul]
  split_ifs
  · linarith
  · simpa using ((sq_nonneg _).trans h2)
theorem quarticGrowth_linearPotentialCoeff : IsQuarticGrowth linearPotentialCoeff :=
  quarticGrowth_secondAxisFirstCoord.sub (quarticGrowth_bondDifference cubicGrowth_halfCoordProduct)
theorem summable_kernel_translate (hq : IsDecayingGaugeKernel q M θ) (z : Fin 4 → ℤ) :
    Summable fun u : Fin 4 → ℤ => q (u, secondAxis) (u + z, secondAxis) := by
  refine Summable.of_norm_bounded ((summable_siteWeight hq.rate_pos).mul_left M) fun u => ?_
  rw [Real.norm_eq_abs]
  refine (hq.abs_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hq.const_nonneg)
  have h1 : (offsetNorm u : ℝ) ≤ ((max (offsetNorm u) (offsetNorm (u + z)) : ℕ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  have h2 : Real.exp (-(θ * ((max (offsetNorm u) (offsetNorm (u + z)) : ℕ) : ℝ))) ≤
      Real.exp (-(θ * (offsetNorm u : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hq.rate_pos]
  have h3 : (1 : ℝ) ≤ (1 + (offsetNorm u : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
  unfold siteWeight
  calc _ ≤ Real.exp (-(θ * (offsetNorm u : ℝ))) := h2
    _ ≤ _ := le_mul_of_one_le_right (Real.exp_pos _).le h3
theorem hasSum_kernel_potential (hq : IsDecayingGaugeKernel q M θ) {b : ℝ}
    (hK : HasSum (fun z : Fin 4 → ℤ => -(1 / 2) *
      (∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2) b) :
    HasSum (fun cc : LatticeBond × LatticeBond =>
      q cc.1 cc.2 * linearPotentialCoeff cc.1 * linearPotentialCoeff cc.2) b := by
  classical
  set S := ∑' cc : LatticeBond × LatticeBond,
    q cc.1 cc.2 * secondAxisFirstCoord cc.1 * secondAxisFirstCoord cc.2 with hS
  have h1 : HasSum (fun cc : LatticeBond × LatticeBond =>
      q cc.1 cc.2 * secondAxisFirstCoord cc.1 * secondAxisFirstCoord cc.2) S :=
    (summable_kernel_mul_mul hq quarticGrowth_secondAxisFirstCoord quarticGrowth_secondAxisFirstCoord).hasSum
  have h2 := hasSum_zero_bondDifference_left hq cubicGrowth_halfCoordProduct quarticGrowth_secondAxisFirstCoord
  have h3 := hasSum_zero_bondDifference_right hq cubicGrowth_halfCoordProduct quarticGrowth_linearPotentialCoeff
  have hT : HasSum (fun cc : LatticeBond × LatticeBond =>
      q cc.1 cc.2 * linearPotentialCoeff cc.1 * linearPotentialCoeff cc.2) S := by
    have h := (h1.sub h2).sub h3
    simp only [sub_zero] at h
    have e : (fun cc : LatticeBond × LatticeBond =>
        q cc.1 cc.2 * linearPotentialCoeff cc.1 * linearPotentialCoeff cc.2) =
        fun cc => q cc.1 cc.2 * secondAxisFirstCoord cc.1 * secondAxisFirstCoord cc.2 -
          q cc.1 cc.2 * bondDifference halfCoordProduct cc.1 * secondAxisFirstCoord cc.2 -
          q cc.1 cc.2 * linearPotentialCoeff cc.1 * bondDifference halfCoordProduct cc.2 := by
      funext cc
      simp only [linearPotentialCoeff]
      ring
    rw [e]
    exact h
  have k1 := hasSum_zero_bondDifference_right hq cubicGrowth_secondCoordinate
    quarticGrowth_secondAxisFirstCoordSq
  have k2 := hasSum_zero_bondDifference_left hq cubicGrowth_secondCoordinate
    quarticGrowth_secondAxisFirstCoordSq
  rw [bondDifference_secondCoordinate] at k1 k2
  let Y : LatticeBond × LatticeBond → ℝ := fun cc => q cc.1 cc.2 *
    (if cc.1.2 = secondAxis ∧ cc.2.2 = secondAxis then
      (((cc.2.1 0 : ℤ) : ℝ) - ((cc.1.1 0 : ℤ) : ℝ)) ^ 2 else 0)
  have hY : HasSum Y (0 + 0 - 2 * S) := by
    have h := (k1.add k2).sub (h1.mul_left 2)
    have e : Y = fun cc => q cc.1 cc.2 * secondAxisFirstCoordSq cc.1 * secondAxisIndicator cc.2 +
        q cc.1 cc.2 * secondAxisIndicator cc.1 * secondAxisFirstCoordSq cc.2 -
        2 * (q cc.1 cc.2 * secondAxisFirstCoord cc.1 * secondAxisFirstCoord cc.2) := by
      funext ⟨⟨u, i⟩, ⟨v, j⟩⟩
      by_cases hi : i = secondAxis <;> by_cases hj : j = secondAxis <;>
        simp [Y, secondAxisIndicator, secondAxisFirstCoord, secondAxisFirstCoordSq, hi, hj] <;> ring
    rw [e]
    exact h
  let ι : (Fin 4 → ℤ) × (Fin 4 → ℤ) → LatticeBond × LatticeBond := fun p =>
    ((p.1, secondAxis), (p.1 + p.2, secondAxis))
  have hinj : Function.Injective ι := by
    rintro ⟨u, z⟩ ⟨u', z'⟩ h
    simp only [ι, Prod.mk.injEq, and_true] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [Prod.mk.injEq, true_and]
    exact add_left_cancel h2
  have hoff : ∀ cc, cc ∉ Set.range ι → Y cc = 0 := by
    rintro ⟨⟨u, i⟩, ⟨v, j⟩⟩ hc
    have : ¬ (i = secondAxis ∧ j = secondAxis) := by
      rintro ⟨rfl, rfl⟩
      exact hc ⟨(u, v - u), by simp [ι]⟩
    simp [Y, this]
  have h4 : HasSum (Y ∘ ι) (0 + 0 - 2 * S) := (hinj.hasSum_iff hoff).mpr hY
  have h4' : HasSum ((Y ∘ ι) ∘ (Equiv.prodComm (Fin 4 → ℤ) (Fin 4 → ℤ))) (0 + 0 - 2 * S) :=
    ((Equiv.prodComm (Fin 4 → ℤ) (Fin 4 → ℤ)).hasSum_iff).mpr h4
  have hfib : ∀ z : Fin 4 → ℤ, HasSum
      (fun u => ((Y ∘ ι) ∘ (Equiv.prodComm (Fin 4 → ℤ) (Fin 4 → ℤ))) (z, u))
      ((∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2) := by
    intro z
    have h := ((summable_kernel_translate hq z).hasSum).mul_right (((z 0 : ℤ) : ℝ) ^ 2)
    have e : (fun u => ((Y ∘ ι) ∘ (Equiv.prodComm (Fin 4 → ℤ) (Fin 4 → ℤ))) (z, u)) =
        fun u => q (u, secondAxis) (u + z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2 := by
      funext u
      simp [Y, ι]
    rw [e]
    exact h
  have h5 := HasSum.prod_fiberwise h4' hfib
  have h6 : HasSum (fun z : Fin 4 → ℤ => -(1 / 2) *
      ((∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2))
      (-(1 / 2) * (0 + 0 - 2 * S)) := h5.mul_left _
  have hb : b = S := by
    have e : (fun z : Fin 4 → ℤ => -(1 / 2) *
        ((∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2)) =
        fun z : Fin 4 → ℤ => -(1 / 2) *
        (∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2 :=
      funext fun z => by ring
    rw [e] at h6
    have h7 := hK.unique h6
    rw [h7]
    ring
  rw [hb]
  exact hT
end Number
section Torus
def densityAtOrigin (h : LocalDensity) : GaugeTotal := fun n V => h n 0 V
def originKernel (h : LocalDensity) (n : ℕ) (c c' : TorusBond n) : ℝ :=
  mixedDeriv (h n 0) (trivialField n) ![c, c'] ![quaternionI, quaternionI]
def siteCoords {n : ℕ} (u : TorusSite n) : Fin 4 → ℤ := fun i => (u i).valMinAbs
theorem siteCoords_injective {n : ℕ} [NeZero n] : Function.Injective (siteCoords (n := n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
theorem supDist_zero_eq {n : ℕ} [NeZero n] (w : TorusSite n) :
    supDist (0 : TorusSite n) w = offsetNorm (siteCoords w) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.supDist_zero_left <;> assumption
theorem siteCoords_siteOfInt {n : ℕ} [NeZero n] {z : Fin 4 → ℤ} (h : 2 * offsetNorm z + 1 < n) :
    siteCoords (siteOfInt z : TorusSite n) = z := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_siteOfInt <;> assumption
theorem siteOfInt_add {n : ℕ} (u z : Fin 4 → ℤ) :
    (siteOfInt (u + z) : TorusSite n) = siteOfInt z + siteOfInt u := by
  funext i
  simp [siteOfInt, add_comm]
theorem siteOfInt_sub_latticeUnit {n : ℕ} (u : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (u - latticeUnit i) : TorusSite n) = siteOfInt u - TorusFields.unitStep n i := by apply _root_.YangMills.DeltaSharedProofs.p500696 <;> assumption
theorem bondFrom_zero {n : ℕ} (c : LatticeBond) :
    bondFrom (0 : TorusSite n) c = (siteOfInt c.1, c.2) := by
  simp [bondFrom]
theorem max_supDist_le_supportDiam {n : ℕ} [NeZero n] (c c' : TorusBond n) :
    max (supDist (0 : TorusSite n) c.1) (supDist (0 : TorusSite n) c'.1) ≤
      supportDiam (0 : TorusSite n) ![c, c'] := by
  refine max_le ?_ ?_
  · exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => supDist (0 : TorusSite n) ((![c, c'] l).1))
      (Finset.mem_univ (0 : Fin 2)))
  · exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => supDist (0 : TorusSite n) ((![c, c'] l).1))
      (Finset.mem_univ (1 : Fin 2)))
theorem offsetNorm_le_supportDiam {n : ℕ} [NeZero n] (c c' : TorusBond n) :
    offsetNorm (siteCoords c.1) ≤ supportDiam (0 : TorusSite n) ![c, c'] := by
  rw [← supDist_zero_eq]
  exact le_trans (le_max_left _ _) (max_supDist_le_supportDiam c c')
theorem inner_quaternionI_self : inner ℝ (quaternionI : ℍ[ℝ]) (quaternionI : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.inner_quaternionI_self <;> assumption
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem linearPotential_unitPlaneCurvature (c : LatticeBond) :
    linearPotential unitPlaneCurvature c = linearPotentialCoeff c • quaternionI := by
  obtain ⟨z, i⟩ := c
  fin_cases i <;>
    simp [linearPotential, unitPlaneCurvature, planeCurvature, Fin.sum_univ_four, linearPotentialCoeff,
      secondAxisFirstCoord, bondDifference, halfCoordProduct, latticeUnit, secondAxis,
      Pi.single_apply] <;>
    module
variable {n : ℕ} [NeZero n]
theorem originKernel_eq {h : LocalDensity}
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => h n 0 (perturb c X σ (trivialField n))) 0)
    (c c' : TorusBond n) :
    originKernel h n c c' =
      abelianHessian (densityAtOrigin h) n quaternionI (Pi.single c 1) (Pi.single c' 1) := by
  have := mixedDeriv_smul (H := densityAtOrigin h) quaternionI hs c c' 1 1
  simp only [one_smul, mul_one, one_mul] at this
  exact this
theorem hessianAtTrivial_eq_sum {h : LocalDensity} {H : GaugeTotal}
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => h n 0 (perturb c X σ (trivialField n))) 0)
    (htr : ∀ y u : TorusSite n, ∀ᶠ V in 𝓝 (trivialField n), h n y (TorusFields.translate u V) = h n (y + u) V)
    (hH : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (hden : ∀ᶠ V in 𝓝 (trivialField n), centeredDensityTotal h n V = H n V) (c c' : TorusBond n) :
    hessianAtTrivial H n c c' quaternionI quaternionI =
      ∑ y : TorusSite n, originKernel h n (c.1 - y, c.2) (c'.1 - y, c'.2) := by
  have hF : ContDiffAt ℝ 2 (abelianRestrict (densityAtOrigin h) n quaternionI) 0 :=
    contDiffAt_abelianRestrict quaternionI hs
  have hFy : ∀ y : TorusSite n,
      ContDiffAt ℝ 2 (abelianRestrict (densityAtOrigin h) n quaternionI ∘ angleTranslate y) 0 :=
    fun y => ContDiffAt.comp (0 : TorusBond n → ℝ) (by simpa using hF) (angleTranslate y).contDiff.contDiffAt
  have hev : abelianRestrict H n quaternionI =ᶠ[𝓝 0] fun θ => ∑ y : TorusSite n,
      ((abelianRestrict (densityAtOrigin h) n quaternionI ∘ angleTranslate y) θ - h n y (trivialField n)) := by
    have h1 := (tendsto_abelianField (n := n) quaternionI).eventually hden
    have h2 := (tendsto_abelianField (n := n) quaternionI).eventually
      (Filter.eventually_all.mpr fun y => htr 0 y)
    filter_upwards [h1, h2] with θ a1 a2
    simp only [abelianRestrict]
    rw [← a1]
    simp only [centeredDensityTotal, dif_neg (NeZero.ne n)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered, Function.comp, abelianRestrict, densityAtOrigin, ← translate_abelianField,
      a2 y, zero_add]
  have hq : abelianHessian H n quaternionI (Pi.single c 1) (Pi.single c' 1) = ∑ y : TorusSite n,
      abelianHessian (densityAtOrigin h) n quaternionI (angleTranslate y (Pi.single c 1))
        (angleTranslate y (Pi.single c' 1)) := by
    simp only [abelianHessian]
    rw [hev.fderiv.fderiv_eq, fderiv_fderiv_sum Finset.univ
      (fun (y : TorusSite n) θ =>
        (abelianRestrict (densityAtOrigin h) n quaternionI ∘ angleTranslate y) θ - h n y (trivialField n))
      (fun y _ => (hFy y).sub contDiffAt_const)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [fderiv_sub_const_fun, fderiv_fderiv_comp_clm hF]
  have hc := mixedDeriv_smul (H := H) quaternionI hH c c' 1 1
  simp only [one_smul, mul_one] at hc
  simp only [hessianAtTrivial]
  rw [hc, one_mul, hq]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [angleTranslate_single, angleTranslate_single, originKernel_eq hs]
def extendedKernel (h : LocalDensity) (z : Fin 4 → ℤ) (m : ℕ) (u : Fin 4 → ℤ) : ℝ :=
  Function.extend (siteCoords (n := m))
    (fun w => originKernel h m (w, secondAxis) (siteOfInt z + w, secondAxis)) 0 u
theorem extendedKernel_siteCoords (h : LocalDensity) (z : Fin 4 → ℤ) (w : TorusSite n) :
    extendedKernel h z n (siteCoords w) =
      originKernel h n (w, secondAxis) (siteOfInt z + w, secondAxis) :=
  siteCoords_injective.extend_apply _ _ _
theorem extendedKernel_of_not_mem (h : LocalDensity) (z : Fin 4 → ℤ) {u : Fin 4 → ℤ}
    (hu : ¬ ∃ w : TorusSite n, siteCoords w = u) : extendedKernel h z n u = 0 := by
  unfold extendedKernel
  rw [Function.extend_apply' _ _ _ hu]
  rfl
theorem tsum_extendedKernel (h : LocalDensity) (z : Fin 4 → ℤ) :
    ∑' u, extendedKernel h z n u =
      ∑ w : TorusSite n, originKernel h n (w, secondAxis) (siteOfInt z + w, secondAxis) := by
  have hsup : Function.support (extendedKernel h z n) ⊆ Set.range (siteCoords (n := n)) := by
    intro u hu
    by_contra hc
    exact hu (extendedKernel_of_not_mem h z hc)
  rw [← siteCoords_injective.tsum_eq hsup, tsum_fintype]
  exact Finset.sum_congr rfl fun w _ => extendedKernel_siteCoords h z w
theorem norm_extendedKernel_le {h : LocalDensity} {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ)
    (hd : ∀ c c' : TorusBond n, |originKernel h n c c'| ≤
      M * Real.exp (-(θ * supportDiam (0 : TorusSite n) ![c, c']))) (z u : Fin 4 → ℤ) :
    ‖extendedKernel h z n u‖ ≤ M * siteWeight θ u := by
  by_cases hu : ∃ w : TorusSite n, siteCoords w = u
  · obtain ⟨w, rfl⟩ := hu
    rw [extendedKernel_siteCoords, Real.norm_eq_abs]
    refine (hd _ _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    have h1 : offsetNorm (siteCoords w) ≤
        supportDiam (0 : TorusSite n) ![(w, secondAxis), (siteOfInt z + w, secondAxis)] :=
      offsetNorm_le_supportDiam (w, secondAxis) (siteOfInt z + w, secondAxis)
    have h2 : (offsetNorm (siteCoords w) : ℝ) ≤
        (supportDiam (0 : TorusSite n) ![(w, secondAxis), (siteOfInt z + w, secondAxis)] : ℝ) := by
      exact_mod_cast h1
    have h3 : (1 : ℝ) ≤ (1 + (offsetNorm (siteCoords w) : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
    unfold siteWeight
    calc _ ≤ Real.exp (-(θ * (offsetNorm (siteCoords w) : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := le_mul_of_one_le_right (Real.exp_pos _).le h3
  · rw [extendedKernel_of_not_mem h z hu, norm_zero]
    exact mul_nonneg hM (siteWeight_nonneg θ u)
end Torus
theorem claim_holds : CoefficientFromDensity.Claim := by
  intro h H b hl hcoef hden
  obtain ⟨K, hK, hsum⟩ := hcoef
  obtain ⟨M₀, θ, hθ, hdec⟩ := hl.kernel_decay
  set M : ℝ := |M₀| with hMdef
  have hM : 0 ≤ M := abs_nonneg _
  set q : LatticeBond → LatticeBond → ℝ :=
    fun c c' => secondDerivLimit h c c' quaternionI quaternionI with hqdef
  have tend : ∀ c c' : LatticeBond, Tendsto (fun m => originKernel h m (bondFrom 0 c) (bondFrom 0 c')) atTop
      (𝓝 (q c c')) := by
    intro c c'
    obtain ⟨v, hv⟩ := hl.tendsto c c' quaternionI quaternionI
    have : q c c' = v := hv.limUnder_eq
    rw [this]
    exact hv
  have hgood : ∀ᶠ m : ℕ in atTop, 0 < m ∧
      (∀ (k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
        ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => h m 0 (perturb c X σ (trivialField m))) 0) ∧
      (∀ᶠ p : (TorusSite m → UnitQuaternion) × TorusField m in 𝓝 (1, trivialField m),
        h m 0 (TorusFields.gaugeTransform p.1 p.2) = h m 0 p.2) ∧
      (∀ c c' : TorusBond m, |originKernel h m c c'| ≤
        M * Real.exp (-(θ * supportDiam (0 : TorusSite m) ![c, c']))) := by
    filter_upwards [eventually_gt_atTop 0, hl.contDiffAt, hl.gauge_invariant, hdec] with m h0 a1 a2 a3
    refine ⟨h0, a1 0, a2 0, fun c c' => ?_⟩
    refine (a3 c c' quaternionI quaternionI norm_quaternionI norm_quaternionI).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  have hker : IsDecayingGaugeKernel q M θ := by
    refine ⟨hθ, hM, fun c c' => ?_, fun c c' => ?_, fun u c' => ?_⟩
    · refine le_of_tendsto (tend c c').abs ?_
      filter_upwards [hgood, eventually_gt_atTop (2 * offsetNorm c.1 + 1),
        eventually_gt_atTop (2 * offsetNorm c'.1 + 1)] with m ⟨h0, _, _, a3⟩ b1 b2
      haveI : NeZero m := ⟨h0.ne'⟩
      refine (a3 _ _).trans (mul_le_mul_of_nonneg_left ?_ hM)
      have hsp := max_supDist_le_supportDiam (bondFrom (0 : TorusSite m) c) (bondFrom (0 : TorusSite m) c')
      rw [supDist_zero_eq, supDist_zero_eq, bondFrom_zero, bondFrom_zero] at hsp
      simp only [siteCoords_siteOfInt b1, siteCoords_siteOfInt b2] at hsp
      rw [bondFrom_zero, bondFrom_zero]
      have h2 : ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ) ≤
          (supportDiam (0 : TorusSite m) ![(siteOfInt c.1, c.2), (siteOfInt c'.1, c'.2)] : ℝ) := by
        exact_mod_cast hsp
      exact Real.exp_le_exp.mpr (by nlinarith)
    · refine tendsto_nhds_unique (tend c c') ((tend c' c).congr' ?_)
      filter_upwards [hgood] with m ⟨h0, a1, _, _⟩
      haveI : NeZero m := ⟨h0.ne'⟩
      rw [originKernel_eq a1, originKernel_eq a1]
      exact abelianHessian_symm quaternionI a1 _ _
    · have hlim : Tendsto (fun m => ∑ i, (originKernel h m (bondFrom 0 (u - latticeUnit i, i)) (bondFrom 0 c') -
          originKernel h m (bondFrom 0 (u, i)) (bondFrom 0 c'))) atTop
          (𝓝 (∑ i, (q (u - latticeUnit i, i) c' - q (u, i) c'))) :=
        tendsto_finset_sum _ fun i _ => (tend _ _).sub (tend _ _)
      refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
      filter_upwards [hgood] with m ⟨h0, a1, a2, _⟩
      haveI : NeZero m := ⟨h0.ne'⟩
      have hg : IsGaugeFunctionNear (densityAtOrigin h) m := ⟨a1, a2⟩
      have hz := abelianHessian_gradient quaternionI hg (Pi.single (siteOfInt u) (1 : ℝ))
        (Pi.single (bondFrom (0 : TorusSite m) c') 1)
      rw [latticeGradient_single, map_sum] at hz
      show (0 : ℝ) = _
      rw [← hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : bondFrom (0 : TorusSite m) (u - latticeUnit i, i) = (siteOfInt u - TorusFields.unitStep m i, i) := by
        rw [bondFrom_zero, siteOfInt_sub_latticeUnit]
      have e2 : bondFrom (0 : TorusSite m) (u, i) = (siteOfInt u, i) := bondFrom_zero _
      rw [e1, e2, originKernel_eq a1, originKernel_eq a1, map_sub,
        abelianHessian_symm quaternionI a1 (Pi.single (siteOfInt u - TorusFields.unitStep m i, i) 1),
        abelianHessian_symm quaternionI a1 (Pi.single (siteOfInt u, i) 1)]
  have hKz : ∀ z : Fin 4 → ℤ, K (0, secondAxis) (z, secondAxis) =
      ∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis) := by
    intro z
    have hlim := hK.tendsto_kernel (0, secondAxis) (z, secondAxis) quaternionI quaternionI
    rw [inner_quaternionI_self, one_mul] at hlim
    have htan : Tendsto (fun m => ∑' u, extendedKernel h z m u) atTop
        (𝓝 (∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis))) := by
      refine tendsto_tsum_of_dominated_convergence (bound := fun u => M * siteWeight θ u)
        ((summable_siteWeight hθ).mul_left M) ?_ ?_
      · intro u
        refine (tend (u, secondAxis) (u + z, secondAxis)).congr' ?_
        filter_upwards [hgood, eventually_gt_atTop (2 * offsetNorm u + 1)] with m ⟨h0, _, _, _⟩ b1
        haveI : NeZero m := ⟨h0.ne'⟩
        have e1 := extendedKernel_siteCoords h z (siteOfInt u : TorusSite m)
        rw [siteCoords_siteOfInt b1] at e1
        rw [e1, bondFrom_zero, bondFrom_zero, siteOfInt_add]
      · filter_upwards [hgood] with m ⟨h0, _, _, a3⟩ u
        haveI : NeZero m := ⟨h0.ne'⟩
        exact norm_extendedKernel_le hM hθ a3 z u
    refine tendsto_nhds_unique hlim (htan.congr' ?_)
    filter_upwards [hgood, hK.eventually_isGaugeTotalAt, hl.translation_invariant, hden]
      with m ⟨h0, a1, _, _⟩ t1 t2 t3
    haveI : NeZero m := ⟨h0.ne'⟩
    have e1 := hessianAtTrivial_eq_sum a1 t2 t1.contDiffAt_perturb t3
      (bondFrom (0 : TorusSite m) ((0 : Fin 4 → ℤ), secondAxis))
      (bondFrom (0 : TorusSite m) (z, secondAxis))
    have h0' : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite m) = 0 := by
      funext i
      simp [siteOfInt]
    rw [tsum_extendedKernel, e1, bondFrom_zero, bondFrom_zero]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun w => ?_
    simp [h0', sub_neg_eq_add]
  have hsum' : HasSum (fun z : Fin 4 → ℤ => -(1 / 2) *
      (∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2) b := by
    have e1 : secondMomentTerm K = fun z : Fin 4 → ℤ => -(1 / 2) *
        (∑' u : Fin 4 → ℤ, q (u, secondAxis) (u + z, secondAxis)) * ((z 0 : ℤ) : ℝ) ^ 2 :=
      funext fun z => by simp only [secondMomentTerm, hKz]
    rwa [e1] at hsum
  have hfin := hasSum_kernel_potential hker hsum'
  convert hfin using 2 with cc
  obtain ⟨c, c'⟩ := cc
  simp only [limitFormTerm, linearPotential_unitPlaneCurvature]
  have hl2 : Tendsto (fun m => mixedDeriv (h m 0) (trivialField m) ![bondFrom 0 c, bondFrom 0 c']
      ![linearPotentialCoeff c • quaternionI, linearPotentialCoeff c' • quaternionI]) atTop
      (𝓝 (q c c' * linearPotentialCoeff c * linearPotentialCoeff c')) := by
    refine (((tend c c').mul_const (linearPotentialCoeff c)).mul_const (linearPotentialCoeff c')).congr' ?_
    filter_upwards [hgood] with m ⟨h0, a1, _, _⟩
    haveI : NeZero m := ⟨h0.ne'⟩
    have e1 : mixedDeriv (h m 0) (trivialField m) ![bondFrom 0 c, bondFrom 0 c']
        ![linearPotentialCoeff c • quaternionI, linearPotentialCoeff c' • quaternionI] = _ :=
      mixedDeriv_smul (H := densityAtOrigin h) quaternionI a1 (bondFrom 0 c) (bondFrom 0 c')
        (linearPotentialCoeff c) (linearPotentialCoeff c')
    rw [e1, originKernel_eq a1]
    ring
  exact hl2.limUnder_eq
end RunningCouplingSlope.CoefficientFromDensity
end YangMills.Construction
end
