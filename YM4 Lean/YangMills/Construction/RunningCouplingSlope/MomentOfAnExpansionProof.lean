import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.RunningCouplingSlope.DensitiesOfAnExpansionHaveNoCoefficientProof
import YangMills.Construction.RunningCouplingSlope.MomentOfASumOfForms
import YangMills.Construction.RunningCouplingSlope.MomentOfAnExpansion
import YangMills.Construction.RunningCouplingSlope.NumberOfALocalDensityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages hiding unitStep gaugeTransform
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps Filter
namespace YangMills.Construction.RunningCouplingSlope.CenteredDensityMoment
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem eventually_differentiableAt_of_contDiffAt_two {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∀ᶠ A in 𝓝 (0 : E), DifferentiableAt ℝ f A :=
  (hf.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
theorem fderiv_fderiv_comp_clm {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (L : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_comp_clm <;> assumption
theorem fderiv_fderiv_apply_eq_zero_of_eventually {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (w : F)
    (h : ∀ᶠ θ in 𝓝 (0 : F), fderiv ℝ Ψ θ w = 0) (u : F) : fderiv ℝ (fderiv ℝ Ψ) 0 u w = 0 := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.fderiv_fderiv_apply_eq_zero_of_eventually <;> assumption
theorem fderiv_sub_const_fun (f : E → ℝ) (c : ℝ) :
    fderiv ℝ (fun θ => f θ - c) = fderiv ℝ f := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.fderiv_sub_const_fun <;> assumption
theorem fderiv_fderiv_sum_apply {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0) (u v : E) :
    fderiv ℝ (fderiv ℝ fun θ => ∑ i ∈ s, f i θ) 0 u v =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) 0 u v := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_sum <;> assumption
end Calculus
section Fields
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_smul_mul_expUnit_smul (X : imaginaryQuaternions) (u v : ℝ) :
    expUnit (u • X) * expUnit (v • X) = expUnit ((u + v) • X) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
theorem expUnit_smul_inv (X : imaginaryQuaternions) (u : ℝ) :
    (expUnit (u • X))⁻¹ = expUnit ((-u) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
variable {n : ℕ} [NeZero n]
def abelianField (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (θ (x, i) • X)
def abelianRestriction (G : TorusField n → ℝ) (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) : ℝ :=
  G (abelianField X θ)
def bondDirection {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    w l • (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ) else 0
theorem bondDirection_apply {k : ℕ} (c : Fin k → TorusBond n) (w σ : Fin k → ℝ) (b : TorusBond n) :
    bondDirection c w σ b = ∑ l, if c l = b then w l * σ l else 0 := by
  simp only [bondDirection, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem bondDirection_single {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ) (l : Fin k) :
    bondDirection c w (Pi.single l 1) = w l • Pi.single (c l) (1 : ℝ) := by
  funext b
  rw [bondDirection_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
theorem perturb_trivial_abelian {k : ℕ} (c : Fin k → TorusBond n) (w : Fin k → ℝ)
    (X : imaginaryQuaternions) (σ : Fin k → ℝ) :
    perturb c (fun l => w l • X) σ (trivialField n) = abelianField X (bondDirection c w σ) := by
  funext x i
  have h : (∑ l, if c l = (x, i) then σ l • (w l • X) else 0) =
      (bondDirection c w σ (x, i)) • X := by
    rw [bondDirection_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [smul_smul, mul_comm]
    · simp
  simp only [perturb, trivialField, abelianField, mul_one, h]
theorem perturb_comp_bondDirection {G : TorusField n → ℝ} {k : ℕ} (c : Fin k → TorusBond n)
    (w : Fin k → ℝ) (X : imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => G (perturb c (fun l => w l • X) σ (trivialField n))) =
      abelianRestriction G X ∘ bondDirection c w := by
  funext σ
  simp only [Function.comp, abelianRestriction, perturb_trivial_abelian]
def IsC2AtTrivial (G : TorusField n → ℝ) : Prop :=
  ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => G (perturb c X σ (trivialField n))) 0
theorem contDiffAt_abelianRestriction {G : TorusField n → ℝ} (X : imaginaryQuaternions)
    (hs : IsC2AtTrivial G) : ContDiffAt ℝ 2 (abelianRestriction G X) 0 := by
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
  have hid : ∀ θ : TorusBond n → ℝ, bondDirection c w (π θ) = θ := by
    intro θ
    funext b
    rw [bondDirection_apply, Finset.sum_eq_single (e b)]
    · simp [c, π, π₀, w]
    · intro l _ hl
      have : c l ≠ b := fun h => hl (by simp [← h, c])
      simp [this]
    · simp
  have hφ := hs _ c fun l => w l • X
  have hcomp : abelianRestriction G X =
      (fun σ => G (perturb c (fun l => w l • X) σ (trivialField n))) ∘ π := by
    funext θ
    simp only [Function.comp, perturb_trivial_abelian, abelianRestriction, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond n → ℝ) ?_ π.contDiff.contDiffAt
  simpa using hφ
def abelianHessian (G : TorusField n → ℝ) (X : imaginaryQuaternions) :
    (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (abelianRestriction G X)) 0
theorem mixedDeriv_smul_smul {G : TorusField n → ℝ} (X : imaginaryQuaternions) (hs : IsC2AtTrivial G)
    (c c' : TorusBond n) (a a' : ℝ) :
    mixedDeriv G (trivialField n) ![c, c'] ![a • X, a' • X] =
      a * a' * abelianHessian G X (Pi.single c 1) (Pi.single c' 1) := by
  have hX : (![a • X, a' • X] : Fin 2 → imaginaryQuaternions) = fun l => (![a, a'] : Fin 2 → ℝ) l • X := by
    funext l
    fin_cases l <;> rfl
  unfold mixedDeriv
  rw [hX, iteratedFDeriv_two_apply,
    perturb_comp_bondDirection (G := G) (![c, c'] : Fin 2 → TorusBond n) ![a, a'] X,
    fderiv_fderiv_comp_clm (contDiffAt_abelianRestriction X hs), bondDirection_single,
    bondDirection_single]
  simp only [abelianHessian, Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
theorem abelianHessian_symm {G : TorusField n → ℝ} (X : imaginaryQuaternions) (hs : IsC2AtTrivial G)
    (u v : TorusBond n → ℝ) : abelianHessian G X u v = abelianHessian G X v u :=
  ((contDiffAt_abelianRestriction X hs).isSymmSndFDerivAt (by simp)) u v
def angleGradient (φ : TorusSite n → ℝ) : TorusBond n → ℝ :=
  fun b => φ (b.1 + unitStep n b.2) - φ b.1
theorem gaugeTransform_abelianField (X : imaginaryQuaternions) (φ : TorusSite n → ℝ) (s : ℝ)
    (θ : TorusBond n → ℝ) :
    _root_.YangMills.Construction.TorusFields.gaugeTransform (fun x => expUnit ((s * φ x) • X)) (abelianField X θ) =
      abelianField X (θ - s • angleGradient φ) := by
  funext x i
  simp only [_root_.YangMills.Construction.TorusFields.gaugeTransform, abelianField, expUnit_smul_inv, expUnit_smul_mul_expUnit_smul]
  congr 2
  simp only [Pi.sub_apply, Pi.smul_apply, angleGradient, smul_eq_mul]
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
theorem abelianHessian_angleGradient {G : TorusField n → ℝ} (X : imaginaryQuaternions)
    (hs : IsC2AtTrivial G)
    (hg : ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
      G (_root_.YangMills.Construction.TorusFields.gaugeTransform p.1 p.2) = G p.2)
    (φ : TorusSite n → ℝ) (u : TorusBond n → ℝ) : abelianHessian G X u (angleGradient φ) = 0 := by
  have hC := contDiffAt_abelianRestriction X hs
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
  have hinv := hlim.eventually hg
  have hprod : ∀ᶠ p in 𝓝 (0 : TorusBond n → ℝ) ×ˢ 𝓝 (0 : ℝ),
      abelianRestriction G X (p.1 - p.2 • angleGradient φ) = abelianRestriction G X p.1 := by
    rw [← nhds_prod_eq]
    filter_upwards [hinv] with p hp
    rw [gaugeTransform_abelianField] at hp
    exact hp
  have hcur := hprod.curry
  filter_upwards [hcur, eventually_differentiableAt_of_contDiffAt_two hC] with θ hθ hd
  have hcurve : HasDerivAt (fun s : ℝ => θ - s • angleGradient φ) (-angleGradient φ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (angleGradient φ)).const_sub θ
    simpa using this
  have hd' : HasFDerivAt (abelianRestriction G X) (fderiv ℝ (abelianRestriction G X) θ)
      (θ - (0 : ℝ) • angleGradient φ) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hcurve
  have h2 : HasDerivAt (fun s : ℝ => abelianRestriction G X (θ - s • angleGradient φ)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (abelianRestriction G X θ)).congr_of_eventuallyEq hθ
  have h3 := h1.unique h2
  simpa using h3
def shiftAngles (u : TorusSite n) : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (b.1 + u, b.2)
theorem shiftAngles_single (u : TorusSite n) (c : TorusBond n) :
    shiftAngles u (Pi.single c 1) = Pi.single (c.1 - u, c.2) (1 : ℝ) := by
  classical
  funext ⟨x, i⟩
  simp only [shiftAngles, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  have : ((x + u, i) = c) ↔ ((x, i) = (c.1 - u, c.2)) := by
    obtain ⟨y, j⟩ := c
    simp [eq_sub_iff_add_eq]
  simp [this]
theorem translate_abelianField (X : imaginaryQuaternions) (u : TorusSite n) (θ : TorusBond n → ℝ) :
    TorusFields.translate u (abelianField X θ) = abelianField X (shiftAngles u θ) := by
  funext x i
  simp [TorusFields.translate, abelianField, shiftAngles]
theorem eq_sum_single_angles (u : TorusBond n → ℝ) :
    u = ∑ c, u c • (Pi.single c 1 : TorusBond n → ℝ) := by
  funext b
  rw [Finset.sum_apply]
  simp [Pi.single_apply]
theorem bilinear_expand_left (Q : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ)
    (u w : TorusBond n → ℝ) :
    Q u w = ∑ c, u c * Q (Pi.single c 1) w := by
  conv_lhs => rw [eq_sum_single_angles u]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
theorem bilinear_expand (Q : (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ)
    (u w : TorusBond n → ℝ) :
    Q u w = ∑ c, ∑ c', u c * w c' * Q (Pi.single c 1) (Pi.single c' 1) := by
  rw [bilinear_expand_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [eq_sum_single_angles w]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  ring
theorem card_torusBond : (Fintype.card (TorusBond n) : ℝ) = 4 * (n : ℝ) ^ 4 := by
  simp [Fintype.card_prod, ZMod.card]
  ring
theorem abs_double_sum_le {g : TorusBond n → TorusBond n → ℝ} {B : ℝ} (h : ∀ c c', |g c c'| ≤ B) :
    |∑ c, ∑ c', g c c'| ≤ 16 * (n : ℝ) ^ 8 * B := by
  calc |∑ c, ∑ c', g c c'| ≤ ∑ c, |∑ c', g c c'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, ∑ c', |g c c'| := Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : TorusBond n, ∑ _c' : TorusBond n, B :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => h c c'
    _ = 16 * (n : ℝ) ^ 8 * B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_torusBond]
        ring
end Fields
section Lattice
def latticeUnit (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
def halfProduct (z : Fin 4 → ℤ) : ℝ := ((z 0 : ℤ) : ℝ) * ((z 1 : ℤ) : ℝ) / 2
def unitCurvaturePotential (c : LatticeBond) : ℝ :=
  latticeLinearPotential c - (halfProduct (c.1 + latticeUnit c.2) - halfProduct c.1)
theorem natAbs_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem offsetNorm_add_latticeUnit (z : Fin 4 → ℤ) (i : Fin 4) :
    offsetNorm (z + latticeUnit i) ≤ offsetNorm z + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
theorem abs_coord_le_offsetNorm (z : Fin 4 → ℤ) (i : Fin 4) : |((z i : ℤ) : ℝ)| ≤ (offsetNorm z : ℝ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.abs_coord_le_offsetNorm <;> assumption
theorem abs_halfProduct_le (z : Fin 4 → ℤ) : |halfProduct z| ≤ (offsetNorm z : ℝ) ^ 2 / 2 := by
  unfold halfProduct
  rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h0 := abs_coord_le_offsetNorm z 0
  have h1 := abs_coord_le_offsetNorm z 1
  have := mul_le_mul h0 h1 (abs_nonneg _) (Nat.cast_nonneg _)
  nlinarith
theorem abs_latticeLinearPotential_le (c : LatticeBond) :
    |latticeLinearPotential c| ≤ (offsetNorm c.1 : ℝ) := by
  unfold latticeLinearPotential
  split_ifs
  · exact abs_coord_le_offsetNorm c.1 0
  · simp
theorem abs_unitCurvaturePotential_le (c : LatticeBond) :
    |unitCurvaturePotential c| ≤ 2 * (1 + (offsetNorm c.1 : ℝ)) ^ 2 := by
  unfold unitCurvaturePotential
  set s : ℝ := (offsetNorm c.1 : ℝ) with hs
  have h1 := abs_latticeLinearPotential_le c
  have h2 := abs_halfProduct_le c.1
  have h3 := abs_halfProduct_le (c.1 + latticeUnit c.2)
  have h4 : (offsetNorm (c.1 + latticeUnit c.2) : ℝ) ≤ s + 1 := by
    rw [hs]
    exact_mod_cast offsetNorm_add_latticeUnit c.1 c.2
  have h5 : (offsetNorm (c.1 + latticeUnit c.2) : ℝ) ^ 2 ≤ (s + 1) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h4 2
  have h6 := abs_sub (latticeLinearPotential c)
    (halfProduct (c.1 + latticeUnit c.2) - halfProduct c.1)
  have h7 := abs_sub (halfProduct (c.1 + latticeUnit c.2)) (halfProduct c.1)
  rw [← hs] at h1 h2
  nlinarith
theorem linearPotential_planeCurvature (X : imaginaryQuaternions) (c : LatticeBond) :
    TorusLumps.linearPotential (planeCurvature X 0 1) c = unitCurvaturePotential c • X := by
  obtain ⟨z, i⟩ := c
  fin_cases i <;>
    simp [TorusLumps.linearPotential, planeCurvature, Fin.sum_univ_four, unitCurvaturePotential,
      latticeLinearPotential, halfProduct, latticeUnit, SlopeCoefficient.secondAxis,
      Pi.single_apply] <;>
    module
theorem planeCurvature_antisymm (X : imaginaryQuaternions) (μ ν : Fin 4) :
    planeCurvature X 0 1 μ ν = -planeCurvature X 0 1 ν μ := by
  unfold planeCurvature
  by_cases h1 : μ = 0 ∧ ν = 1
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : μ = 1 ∧ ν = 0
    · obtain ⟨rfl, rfl⟩ := h2
      simp
    · have h3 : ¬ (ν = 0 ∧ μ = 1) := fun h => h2 ⟨h.2, h.1⟩
      have h4 : ¬ (ν = 1 ∧ μ = 0) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h3, h4]
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
def latticeWeight (c : ℝ) (h : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(c * offsetNorm h)) * (1 + (offsetNorm h : ℝ)) ^ 4
theorem latticeWeight_nonneg (c : ℝ) (h : Fin 4 → ℤ) : 0 ≤ latticeWeight c h := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.expPolyWeight_nonneg <;> assumption
def bondWeight (c : ℝ) (b : LatticeBond) : ℝ := latticeWeight c b.1
theorem bondWeight_nonneg (c : ℝ) (b : LatticeBond) : 0 ≤ bondWeight c b := latticeWeight_nonneg c b.1
theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by apply _root_.YangMills.Construction.RunningCouplingSlope.CoefficientFromDensity.summable_bondWeight <;> assumption
theorem summable_bondWeight_mul {c : ℝ} (hc : 0 < c) :
    Summable fun cc : LatticeBond × LatticeBond => bondWeight c cc.1 * bondWeight c cc.2 :=
  (summable_bondWeight hc).mul_of_nonneg (summable_bondWeight hc) (bondWeight_nonneg c)
    (bondWeight_nonneg c)
theorem abs_finset_sum_le_of_hasSum_zero {ι : Type*} {t g : ι → ℝ} (hs : HasSum t 0)
    (hg : Summable g) (h0 : ∀ i, 0 ≤ g i)
    (S : Finset ι) (h : ∀ i, i ∉ S → |t i| ≤ g i) : |∑ i ∈ S, t i| ≤ ∑' i, g i := by
  classical
  have hlim : Tendsto (fun s' : Finset ι => |∑ i ∈ s', t i - ∑ i ∈ S, t i|) atTop
      (𝓝 |0 - ∑ i ∈ S, t i|) := ((Tendsto.sub_const hs _).abs)
  have e : |0 - ∑ i ∈ S, t i| = |∑ i ∈ S, t i| := by
    rw [zero_sub, abs_neg]
  rw [← e]
  refine le_of_tendsto hlim ((eventually_ge_atTop S).mono fun s' hs' => ?_)
  have h1 := Finset.sum_sdiff (f := t) hs'
  have h2 : ∑ i ∈ s', t i - ∑ i ∈ S, t i = ∑ i ∈ s' \ S, t i := by linarith
  rw [h2]
  calc |∑ i ∈ s' \ S, t i| ≤ ∑ i ∈ s' \ S, |t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s' \ S, g i :=
        Finset.sum_le_sum fun i hi => h i (Finset.mem_sdiff.mp hi).2
    _ ≤ ∑' i, g i := hg.sum_le_tsum _ fun i _ => h0 i
end Lattice
section Coordinates
variable {n : ℕ}
def siteCoords (u : TorusSite n) : Fin 4 → ℤ := fun i => (u i).valMinAbs
def liftBond (c : TorusBond n) : LatticeBond := (siteCoords c.1, c.2)
variable [NeZero n]
theorem siteCoords_injective : Function.Injective (siteCoords (n := n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
theorem liftBond_injective : Function.Injective (liftBond (n := n)) := by
  intro c c' h
  have h1 : siteCoords c.1 = siteCoords c'.1 := congrArg Prod.fst h
  have h2 : c.2 = c'.2 := congrArg (Prod.snd : LatticeBond → Fin 4) h
  exact Prod.ext (siteCoords_injective h1) h2
theorem supDist_zero_eq_offsetNorm (w : TorusSite n) :
    supDist (0 : TorusSite n) w = offsetNorm (siteCoords w) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.supDist_zero_left <;> assumption
theorem siteCoords_siteOfInt {z : Fin 4 → ℤ} (h : 2 * offsetNorm z + 1 < n) :
    siteCoords (siteOfInt z : TorusSite n) = z := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_siteOfInt <;> assumption
theorem siteOfInt_siteCoords (x : TorusSite n) : (siteOfInt (siteCoords x) : TorusSite n) = x := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_minimalCoords <;> assumption
theorem bondFrom_zero (c : LatticeBond) : bondFrom (0 : TorusSite n) c = (siteOfInt c.1, c.2) := by
  simp [bondFrom]
theorem bondFrom_liftBond (c : TorusBond n) : bondFrom (0 : TorusSite n) (liftBond c) = c := by
  rw [bondFrom_zero]
  exact Prod.ext (siteOfInt_siteCoords c.1) rfl
theorem siteOfInt_siteCoords_add_latticeUnit (x : TorusSite n) (i : Fin 4) :
    (siteOfInt (siteCoords x + latticeUnit i) : TorusSite n) = x + unitStep n i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [siteOfInt, siteCoords, latticeUnit, unitStep]
  · simp [siteOfInt, siteCoords, latticeUnit, unitStep, hj]
theorem siteCoords_add_unitStep {x : TorusSite n} (i : Fin 4)
    (h : 2 * offsetNorm (siteCoords x) + 3 < n) :
    siteCoords (x + unitStep n i) = siteCoords x + latticeUnit i := by
  rw [← siteOfInt_siteCoords_add_latticeUnit]
  refine siteCoords_siteOfInt ?_
  have := offsetNorm_add_latticeUnit (siteCoords x) i
  omega
theorem offsetNorm_latticeUnit_le (i : Fin 4) : offsetNorm (latticeUnit i) ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p501726 <;> assumption
theorem supDist_zero_add_unitStep_le (h : 3 < n) (x : TorusSite n) (i : Fin 4) :
    supDist (0 : TorusSite n) (x + unitStep n i) ≤ supDist (0 : TorusSite n) x + 1 := by
  rw [supDist_zero_eq_offsetNorm, supDist_zero_eq_offsetNorm]
  refine Finset.sup_le fun j _ => ?_
  have h1 := natAbs_le_offsetNorm (siteCoords x) j
  have h2 : siteCoords (unitStep n i) = latticeUnit i := by
    have e : (siteOfInt (latticeUnit i) : TorusSite n) = unitStep n i := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [siteOfInt, latticeUnit, unitStep]
      · simp [siteOfInt, latticeUnit, unitStep, hj]
    rw [← e]
    refine siteCoords_siteOfInt ?_
    have := offsetNorm_latticeUnit_le i
    omega
  have h3 := natAbs_le_offsetNorm (latticeUnit i) j
  have h4 := offsetNorm_latticeUnit_le i
  have h5 : (siteCoords (unitStep n i) j).natAbs ≤ 1 := by
    rw [h2]
    omega
  have h6 := ZMod.natAbs_valMinAbs_add_le (x j) (unitStep n i j)
  have h7 := Int.natAbs_add_le (x j).valMinAbs (unitStep n i j).valMinAbs
  simp only [siteCoords, Pi.add_apply] at h1 h5 ⊢
  omega
theorem abs_valMinAbs_le (u : ZMod n) : |((u.valMinAbs : ℤ) : ℝ)| ≤ (n : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  have := ZMod.natAbs_valMinAbs_le u
  have h2 : u.valMinAbs.natAbs ≤ n := this.trans (Nat.div_le_self _ _)
  exact_mod_cast h2
theorem abs_linearPotential_le (c : TorusBond n) : |RunningCouplingSlope.linearPotential c| ≤ (n : ℝ) := by
  unfold RunningCouplingSlope.linearPotential
  split_ifs
  · exact abs_valMinAbs_le _
  · simp
def halfProductPotential (x : TorusSite n) : ℝ := halfProduct (siteCoords x)
theorem abs_halfProductPotential_le (x : TorusSite n) : |halfProductPotential x| ≤ (n : ℝ) ^ 2 / 2 := by
  unfold halfProductPotential halfProduct
  rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h0 := abs_valMinAbs_le (x 0)
  have h1 := abs_valMinAbs_le (x 1)
  have := mul_le_mul h0 h1 (abs_nonneg _) (Nat.cast_nonneg _)
  simp only [siteCoords]
  nlinarith
def torusCurvaturePotential (c : TorusBond n) : ℝ :=
  RunningCouplingSlope.linearPotential c - angleGradient halfProductPotential c
theorem abs_torusCurvaturePotential_le (c : TorusBond n) :
    |torusCurvaturePotential c| ≤ 2 * (n : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have h1 := abs_linearPotential_le c
  have h2 := abs_halfProductPotential_le c.1
  have h3 := abs_halfProductPotential_le (c.1 + unitStep n c.2)
  have h4 := abs_sub (RunningCouplingSlope.linearPotential c) (angleGradient halfProductPotential c)
  have h5 := abs_sub (halfProductPotential (c.1 + unitStep n c.2)) (halfProductPotential c.1)
  unfold torusCurvaturePotential
  unfold angleGradient at h4 ⊢
  nlinarith
theorem torusCurvaturePotential_eq {c : TorusBond n} (h : 2 * offsetNorm (siteCoords c.1) + 3 < n) :
    torusCurvaturePotential c = unitCurvaturePotential (liftBond c) := by
  unfold torusCurvaturePotential unitCurvaturePotential angleGradient halfProductPotential
  rw [siteCoords_add_unitStep c.2 h]
  rfl
end Coordinates
section Cold
variable {n : ℕ}
theorem isCold_trivialField {s : ℝ} (hs : 0 < s) : IsCold s (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
theorem eventually_isCold [NeZero n] {s : ℝ} (hs : 0 < s) :
    ∀ᶠ V in 𝓝 (trivialField n), IsCold s V := by apply _root_.YangMills.SharedProofs.p23383 <;> assumption
end Cold
section Scaling
variable {n : ℕ}
theorem mixedDeriv_sub_const (g : TorusField n → ℝ) (C : ℝ) {k : Fin 2 → TorusBond n}
    (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv (fun V => g V - C) (trivialField n) k X = mixedDeriv g (trivialField n) k X := by apply _root_.YangMills.Construction.RunningCouplingSlope.ColdDensitiesZeroCoefficientProof.mixedDeriv_sub_const <;> assumption
end Scaling
section WilsonWeightSeriesExpansion
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
theorem E_div_weight_le (hE : 0 ≤ ℓ.E) (m : ℕ) :
    ℓ.E / ℓ.weight m ≤ ℓ.E * Real.exp (-(ℓ.weightRate * m)) := by
  unfold StepParameters.weight
  have h1 : Real.exp (ℓ.weightRate * m) ≤
      max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) * Real.exp (ℓ.weightRate * m) :=
    le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hE (Real.exp_pos _) h1
theorem areUnitVectors_pair {X : imaginaryQuaternions} (hX : ‖X‖ = 1) : AreUnitVectors ![X, X] := by
  intro l
  fin_cases l
  · exact hX
  · exact hX
theorem isC2AtTrivial_of_coldExpansion (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f)
    {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (y : TorusSite n) : IsC2AtTrivial (f n y) :=
  fun k c X => (hrow.smooth n hn y (trivialField n) (isCold_trivialField hσ) k c X).of_le (by norm_num)
theorem eventually_gauge_of_coldExpansion (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f)
    {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (y : TorusSite n) :
    ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
      f n y (_root_.YangMills.Construction.TorusFields.gaugeTransform p.1 p.2) = f n y p.2 := by
  have hc : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
      (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
    continuous_snd.tendsto _
  filter_upwards [hc.eventually (eventually_isCold hσ)] with p hp
  exact hrow.gauge n hn y p.1 p.2 hp
def densityHessian (f : LocalDensity) (n : ℕ) (X : imaginaryQuaternions) (Y : TorusSite n)
    (c c' : TorusBond n) : ℝ :=
  mixedDeriv (f n Y) (trivialField n) ![c, c'] ![X, X]
theorem densityHessian_eq (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) (X : imaginaryQuaternions) (Y : TorusSite n) (c c' : TorusBond n) :
    densityHessian f n X Y c c' = abelianHessian (f n Y) X (Pi.single c 1) (Pi.single c' 1) := by
  have := mixedDeriv_smul_smul (G := f n Y) X (isC2AtTrivial_of_coldExpansion hσ hrow hn Y) c c' 1 1
  simpa [densityHessian] using this
theorem densityHessian_translate (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f) {n : ℕ}
    [NeZero n] (hn : ℓ.n₀ ≤ n) (X : imaginaryQuaternions) (Y u : TorusSite n) (c c' : TorusBond n) :
    densityHessian f n X (Y + u) (c.1 + u, c.2) (c'.1 + u, c'.2) = densityHessian f n X Y c c' := by
  have hF := contDiffAt_abelianRestriction X (isC2AtTrivial_of_coldExpansion hσ hrow hn Y)
  have hev : abelianRestriction (f n (Y + u)) X =ᶠ[𝓝 0]
      abelianRestriction (f n Y) X ∘ shiftAngles u := by
    filter_upwards [(tendsto_abelianField (n := n) X).eventually (eventually_isCold hσ)] with θ hθ
    simp only [abelianRestriction, Function.comp]
    rw [← translate_abelianField, hrow.translation n hn Y u _ hθ]
  rw [densityHessian_eq hσ hrow hn, densityHessian_eq hσ hrow hn]
  simp only [abelianHessian]
  rw [hev.fderiv.fderiv_eq, fderiv_fderiv_comp_clm hF, shiftAngles_single, shiftAngles_single]
  simp
theorem densityHessian_siteGradient (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f) {n : ℕ}
    [NeZero n] (hn : ℓ.n₀ ≤ n) (X : imaginaryQuaternions) (Y : TorusSite n) (φ : TorusSite n → ℝ)
    (c : TorusBond n) :
    ∑ b, densityHessian f n X Y b c * siteGradient φ b = 0 := by
  have hs := isC2AtTrivial_of_coldExpansion hσ hrow hn Y
  have h := abelianHessian_angleGradient X hs (eventually_gauge_of_coldExpansion hσ hrow hn Y) φ
    (Pi.single c 1)
  rw [abelianHessian_symm X hs, bilinear_expand_left] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [densityHessian_eq hσ hrow hn, mul_comm]
  rfl
theorem abs_densityHessian_le (hσ : 0 < ℓ.threshold) (hE : 0 ≤ ℓ.E) (hrow : ColdExpansion ℓ t x D f)
    {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (Y : TorusSite n)
    (c c' : TorusBond n) :
    |densityHessian f n X Y c c'| ≤ ℓ.E * Real.exp (-(ℓ.weightRate * supportDiam Y ![c, c'])) := by
  have h := hrow.decay n hn Y (trivialField n) (isCold_trivialField hσ) 2 ![c, c'] ![X, X]
    (by norm_num) (by norm_num) (areUnitVectors_pair hX)
  simp only [show ¬ (2 = 3) by norm_num, if_false] at h
  exact h.trans (E_div_weight_le hE _)
theorem densityHessian_isDecayingFormFamily (hσ : 0 < ℓ.threshold) (hE : 0 ≤ ℓ.E)
    (hrow : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) {v : ℝ} (hv : v ≤ ℓ.weightRate) :
    IsDecayingFormFamily ℓ.E v (densityHessian f n X) where
  symm := fun Y c c' => by
    rw [densityHessian_eq hσ hrow hn, densityHessian_eq hσ hrow hn]
    exact abelianHessian_symm X (isC2AtTrivial_of_coldExpansion hσ hrow hn Y) _ _
  translation_invariant := fun Y u c c' => densityHessian_translate hσ hrow hn X Y u c c'
  vanish_on_gradient := fun Y φ c => densityHessian_siteGradient hσ hrow hn X Y φ c
  exp_decay := fun Y c c' => by
    refine (abs_densityHessian_le hσ hE hrow hn hX Y c c').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE
    have : (0 : ℝ) ≤ (supportDiam Y ![c, c'] : ℝ) := Nat.cast_nonneg _
    nlinarith
theorem hessianAtTrivial_centeredDensityTotal (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f)
    {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (X : imaginaryQuaternions) (c c' : TorusBond n) :
    SlopeCoefficient.hessianAtTrivial (centeredDensityTotal f) n c c' X X =
      ∑ Y, densityHessian f n X Y c c' := by
  have den : ∀ V : TorusField n,
      centeredDensityTotal f n V = ∑ y, (f n y V - f n y (trivialField n)) := by
    intro V
    simp [centeredDensityTotal, NeZero.ne n, centered]
  have hH : IsC2AtTrivial (centeredDensityTotal f n) := fun k b Z => by
    have e : (fun σ : Fin k → ℝ => centeredDensityTotal f n (perturb b Z σ (trivialField n))) =
        fun σ => ∑ y, (f n y (perturb b Z σ (trivialField n)) - f n y (trivialField n)) := by
      funext σ
      exact den _
    rw [e]
    exact ContDiffAt.sum fun y _ =>
      (isC2AtTrivial_of_coldExpansion hσ hrow hn y k b Z).sub contDiffAt_const
  have hc := mixedDeriv_smul_smul X hH c c' 1 1
  simp only [one_smul, mul_one, one_mul] at hc
  have e : abelianRestriction (centeredDensityTotal f n) X =
      fun θ => ∑ y, (abelianRestriction (f n y) X θ - f n y (trivialField n)) := by
    funext θ
    exact den _
  simp only [SlopeCoefficient.hessianAtTrivial]
  rw [hc]
  simp only [abelianHessian]
  rw [e, fderiv_fderiv_sum_apply Finset.univ
    (fun (y : TorusSite n) θ => abelianRestriction (f n y) X θ - f n y (trivialField n))
    (fun y _ => (contDiffAt_abelianRestriction X
      (isC2AtTrivial_of_coldExpansion hσ hrow hn y)).sub contDiffAt_const)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fderiv_sub_const_fun, densityHessian_eq hσ hrow hn]
  rfl
theorem bondOffsetInBox_of_offsetNorm {m : ℕ} {b : LatticeBond} (h : offsetNorm b.1 + 1 ≤ m) :
    TorusFields.BondOffsetInBox m b := by apply _root_.YangMills.Construction.AbelianSecondOrder.bondOffsetInBox_of_le <;> assumption
theorem abs_mixedDeriv_sub_le_of_two_sides (hσ : 0 < ℓ.threshold) (hrow : ColdExpansion ℓ t x D f)
    {n n' : ℕ} [NeZero n] [NeZero n'] (hn : ℓ.n₀ ≤ n) (hn' : ℓ.n₀ ≤ n') {m : ℕ} (h1 : 2 * m + 2 < n)
    (h2 : 2 * m + 2 < n') {c c' : LatticeBond} (hb : TorusFields.BondOffsetInBox m c)
    (hb' : TorusFields.BondOffsetInBox m c') {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X] -
      mixedDeriv (f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X]| ≤
        ℓ.E / ℓ.weight m := by
  have agree : FieldsAgreeNear (trivialField n) (trivialField n') 0 0 m := fun _ _ => rfl
  have hl := hrow.local_density n n' hn hn' 0 0 (trivialField n) (trivialField n') m h1 h2
    (isCold_trivialField hσ) (isCold_trivialField hσ) agree 2 ![c, c'] ![X, X] (by norm_num) (by
      intro l
      fin_cases l
      · exact hb
      · exact hb')
    (areUnitVectors_pair hX)
  have eb : ∀ k : ℕ, (fun l : Fin 2 => bondFrom (0 : TorusSite k) (![c, c'] l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
    intro k
    funext l
    fin_cases l <;> rfl
  rw [eb, eb] at hl
  have e1 : mixedDeriv (centered f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X] =
      mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X] :=
    mixedDeriv_sub_const (f n 0) (f n 0 (trivialField n)) _
  have e2 : mixedDeriv (centered f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X] =
      mixedDeriv (f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X] :=
    mixedDeriv_sub_const (f n' 0) (f n' 0 (trivialField n')) _
  rwa [e1, e2] at hl
theorem exists_tendsto_mixedDeriv (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) (c c' : LatticeBond) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) :
    ∃ v : ℝ, Tendsto (fun n : ℕ =>
      mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X]) atTop (𝓝 v) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlim : Tendsto (fun m : ℕ => ℓ.E * Real.exp (-(ℓ.weightRate * m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ℓ.weightRate * (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hrate
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ℓ.E
    simpa [Function.comp_def] using h2
  have hbig := (hlim.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop (offsetNorm c.1 + offsetNorm c'.1 + 1))
  obtain ⟨m, hm1, hm2⟩ := hbig.exists
  refine ⟨max ℓ.n₀ (2 * m + 3), fun n hn n' hn' => ?_⟩
  have g1 : ℓ.n₀ ≤ n := (le_max_left _ _).trans hn
  have g2 : ℓ.n₀ ≤ n' := (le_max_left _ _).trans hn'
  have g3 : 2 * m + 2 < n := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hn)
  have g4 : 2 * m + 2 < n' := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hn')
  have i1 : NeZero n := ⟨by omega⟩
  have i2 : NeZero n' := ⟨by omega⟩
  have hl := abs_mixedDeriv_sub_le_of_two_sides hσ hrow g1 g2 g3 g4
    (bondOffsetInBox_of_offsetNorm (b := c) (by omega))
    (bondOffsetInBox_of_offsetNorm (b := c') (by omega)) hX
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hl.trans (E_div_weight_le hE m)) hm1
theorem tendsto_secondDerivLimit (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) (c c' : LatticeBond) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) :
    Tendsto (fun n : ℕ => mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X])
      atTop (𝓝 (secondDerivLimit f c c' X X)) := by
  obtain ⟨v, hv⟩ := exists_tendsto_mixedDeriv hσ hrate hE hn₀ hrow c c' hX
  have e : secondDerivLimit f c c' X X = v := hv.limUnder_eq
  rw [e]
  exact hv
theorem secondDerivLimit_smul_smul (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) (c c' : LatticeBond) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) (a a' : ℝ) :
    secondDerivLimit f c c' (a • X) (a' • X) = a * a' * secondDerivLimit f c c' X X := by
  have hl := (tendsto_secondDerivLimit hσ hrate hE hn₀ hrow c c' hX).const_mul (a * a')
  have h2 : Tendsto (fun n : ℕ =>
      mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![a • X, a' • X])
      atTop (𝓝 (a * a' * secondDerivLimit f c c' X X)) := by
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop ℓ.n₀] with m hm
    have i1 : NeZero m := ⟨by omega⟩
    have h3 := mixedDeriv_smul_smul X (isC2AtTrivial_of_coldExpansion hσ hrow hm 0)
      (bondFrom 0 c) (bondFrom 0 c') a a'
    have h4 := mixedDeriv_smul_smul X (isC2AtTrivial_of_coldExpansion hσ hrow hm 0)
      (bondFrom 0 c) (bondFrom 0 c') 1 1
    simp only [one_smul, mul_one, one_mul] at h4
    rw [h3, h4]
  exact h2.limUnder_eq
theorem abs_mixedDeriv_sub_secondDerivLimit_le (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate)
    (hE : 0 ≤ ℓ.E) (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) {m : ℕ} (h1 : 2 * m + 2 < n) {c c' : LatticeBond}
    (hb : TorusFields.BondOffsetInBox m c) (hb' : TorusFields.BondOffsetInBox m c')
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    |mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X] -
      secondDerivLimit f c c' X X| ≤ ℓ.E / ℓ.weight m := by
  have hl := ((tendsto_secondDerivLimit hσ hrate hE hn₀ hrow c c' hX).const_sub
    (mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X])).abs
  refine le_of_tendsto hl ?_
  filter_upwards [eventually_ge_atTop (max ℓ.n₀ (2 * m + 3))] with n' hn'
  have g1 : ℓ.n₀ ≤ n' := (le_max_left _ _).trans hn'
  have g2 : 2 * m + 2 < n' := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hn')
  have i1 : NeZero n' := ⟨by omega⟩
  exact abs_mixedDeriv_sub_le_of_two_sides hσ hrow hn g1 h1 g2 hb hb' hX
theorem max_supDist_le_supportDiam {n : ℕ} [NeZero n] (c c' : TorusBond n) :
    max (supDist (0 : TorusSite n) c.1) (supDist (0 : TorusSite n) c'.1) ≤
      supportDiam (0 : TorusSite n) ![c, c'] := by apply _root_.YangMills.Construction.RunningCouplingSlope.CoefficientFromDensity.max_supDist_le_supportDiam <;> assumption
theorem abs_secondDerivLimit_le (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) (c c' : LatticeBond) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) :
    |secondDerivLimit f c c' X X| ≤
      ℓ.E * Real.exp (-(ℓ.weightRate * ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ))) := by
  refine le_of_tendsto (tendsto_secondDerivLimit hσ hrate hE hn₀ hrow c c' hX).abs ?_
  filter_upwards [eventually_ge_atTop (max ℓ.n₀ (2 * (offsetNorm c.1 + offsetNorm c'.1) + 3))]
    with m hm
  have g1 : ℓ.n₀ ≤ m := (le_max_left _ _).trans hm
  have g2 : 2 * (offsetNorm c.1 + offsetNorm c'.1) + 3 ≤ m := (le_max_right _ _).trans hm
  have i1 : NeZero m := ⟨by omega⟩
  have h := abs_densityHessian_le hσ hE hrow g1 hX 0 (bondFrom 0 c) (bondFrom 0 c')
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE)
  have h1 := max_supDist_le_supportDiam (bondFrom (0 : TorusSite m) c) (bondFrom (0 : TorusSite m) c')
  rw [bondFrom_zero, bondFrom_zero] at h1
  simp only [supDist_zero_eq_offsetNorm] at h1
  rw [siteCoords_siteOfInt (by omega), siteCoords_siteOfInt (by omega)] at h1
  rw [bondFrom_zero, bondFrom_zero]
  have h2 : ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ) ≤
      (supportDiam (0 : TorusSite m)
        ![((siteOfInt c.1 : TorusSite m), c.2), ((siteOfInt c'.1 : TorusSite m), c'.2)] : ℝ) := by
    exact_mod_cast h1
  nlinarith
end WilsonWeightSeriesExpansion
section Torus
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
theorem le_supportDiam_of_not_near {n : ℕ} [NeZero n] (h64 : 64 ≤ n) {c c' : TorusBond n}
    (hnr : ¬ (IsNearOriginBond (momentCutoff n) c ∧ IsNearOriginBond (momentCutoff n) c')) :
    n ≤ 32 * supportDiam (0 : TorusSite n) ![c, c'] := by
  have h1 := max_supDist_le_supportDiam c c'
  have h2 := supDist_zero_add_unitStep_le (by omega : 3 < n) c.1 c.2
  have h3 := supDist_zero_add_unitStep_le (by omega : 3 < n) c'.1 c'.2
  have h4 := le_max_left (supDist (0 : TorusSite n) c.1) (supDist (0 : TorusSite n) c'.1)
  simp only [IsNearOriginBond, momentCutoff] at hnr
  omega
theorem le_supportDiam_of_not_box {n : ℕ} [NeZero n] {c c' : TorusBond n}
    (hb : ¬ (offsetNorm (siteCoords c.1) ≤ n / 8 ∧ offsetNorm (siteCoords c'.1) ≤ n / 8)) :
    n ≤ 32 * supportDiam (0 : TorusSite n) ![c, c'] := by
  have h1 := max_supDist_le_supportDiam c c'
  simp only [supDist_zero_eq_offsetNorm] at h1
  omega
theorem sum_filter_sum_filter {n : ℕ} [NeZero n] (b : TorusBond n → Prop) [DecidablePred b]
    (g : TorusBond n → TorusBond n → ℝ) :
    ∑ c ∈ Finset.univ.filter b, ∑ c' ∈ Finset.univ.filter b, g c c' =
      ∑ c, ∑ c', if b c ∧ b c' then g c c' else 0 := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : b c
  · simp only [hc, if_true, true_and]
    rw [Finset.sum_filter]
  · simp [hc]
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b, neg_abs_le c, neg_abs_le d],
    by linarith [le_abs_self a, le_abs_self b, le_abs_self c, le_abs_self d]⟩
theorem abs_mul_mul_le {u w k U W B : ℝ} (hu : |u| ≤ U) (hw : |w| ≤ W) (hk : |k| ≤ B) :
    |u * w * k| ≤ U * W * B := by
  rw [abs_mul, abs_mul]
  have hU : 0 ≤ U := (abs_nonneg _).trans hu
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  exact mul_le_mul (mul_le_mul hu hw (abs_nonneg _) hU) hk (abs_nonneg _) (mul_nonneg hU hW)
theorem abs_potential_mul_le_bondWeight {ρ E q : ℝ} (hρ : 0 < ρ) (hE : 0 ≤ E) {c c' : LatticeBond}
    {R : ℕ}
    (hq : |q| ≤ E * Real.exp (-(ρ * ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ))))
    (hR : R ≤ max (offsetNorm c.1) (offsetNorm c'.1)) :
    |unitCurvaturePotential c * unitCurvaturePotential c' * q| ≤
      (4 * E * Real.exp (-(ρ * R / 2))) * (bondWeight (ρ / 4) c * bondWeight (ρ / 4) c') := by
  set M : ℝ := ((max (offsetNorm c.1) (offsetNorm c'.1) : ℕ) : ℝ) with hM
  set s : ℝ := (offsetNorm c.1 : ℝ) with hs
  set s' : ℝ := (offsetNorm c'.1 : ℝ) with hs'
  have h1 : s ≤ M := by
    rw [hs, hM]
    exact_mod_cast le_max_left _ _
  have h2 : s' ≤ M := by
    rw [hs', hM]
    exact_mod_cast le_max_right _ _
  have h3 : (R : ℝ) ≤ M := by
    rw [hM]
    exact_mod_cast hR
  have he : Real.exp (-(ρ * M)) ≤
      Real.exp (-(ρ * R / 2)) * (Real.exp (-(ρ / 4 * s)) * Real.exp (-(ρ / 4 * s'))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ ρ * (M / 2 - R / 2 + (M - s) / 4 + (M - s') / 4) := by
      refine mul_nonneg hρ.le ?_
      linarith
    nlinarith
  have p1 : (1 + s) ^ 2 ≤ (1 + s) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : (1 + s') ^ 2 ≤ (1 + s') ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have a1 : |unitCurvaturePotential c| ≤ 2 * (1 + s) ^ 4 :=
    (abs_unitCurvaturePotential_le c).trans (by linarith)
  have a2 : |unitCurvaturePotential c'| ≤ 2 * (1 + s') ^ 4 :=
    (abs_unitCurvaturePotential_le c').trans (by linarith)
  have b1 : |q| ≤ E * (Real.exp (-(ρ * R / 2)) *
      (Real.exp (-(ρ / 4 * s)) * Real.exp (-(ρ / 4 * s')))) :=
    hq.trans (mul_le_mul_of_nonneg_left he hE)
  refine (abs_mul_mul_le a1 a2 b1).trans (le_of_eq ?_)
  simp only [bondWeight, latticeWeight]
  rw [← hs, ← hs']
  ring
theorem abs_formOnLinearPotential_le (hσ : 0 < ℓ.threshold) (hrate : 0 < ℓ.weightRate) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n)
    (h64 : 64 ≤ n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {v : ℝ} (hv0 : 0 < v)
    (hv : v ≤ ℓ.weightRate) :
    |formOnLinearPotential (momentCutoff n) (densityHessian f n X 0)| ≤
      (144 * (n : ℝ) ^ 12 +
        4 * ∑' cc : LatticeBond × LatticeBond,
          bondWeight (ℓ.weightRate / 4) cc.1 * bondWeight (ℓ.weightRate / 4) cc.2) *
        ℓ.E * Real.exp (-(v * n / 32)) := by
  classical
  set e : ℝ := Real.exp (-(v * n / 32)) with he
  have he0 : 0 < e := Real.exp_pos _
  set G₀ : ℝ := ∑' cc : LatticeBond × LatticeBond,
    bondWeight (ℓ.weightRate / 4) cc.1 * bondWeight (ℓ.weightRate / 4) cc.2 with hG₀
  set K := densityHessian f n X 0 with hK
  set Q := abelianHessian (f n 0) X with hQdef
  have hQ : ∀ c c' : TorusBond n, Q (Pi.single c 1) (Pi.single c' 1) = K c c' :=
    fun c c' => (densityHessian_eq hσ hrow hn X 0 c c').symm
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hexp : ∀ r : ℝ, (n : ℝ) ≤ 32 * r → ℓ.E * Real.exp (-(ℓ.weightRate * r)) ≤ ℓ.E * e := by
    intro r hr
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE
    have : v * n ≤ v * (32 * r) := mul_le_mul_of_nonneg_left hr hv0.le
    nlinarith
  have hfar : ∀ c c' : TorusBond n, n ≤ 32 * supportDiam (0 : TorusSite n) ![c, c'] →
      |K c c'| ≤ ℓ.E * e := by
    intro c c' h
    refine (abs_densityHessian_le hσ hE hrow hn hX 0 c c').trans (hexp _ ?_)
    exact_mod_cast h
  have hEe : 0 ≤ ℓ.E * e := mul_nonneg hE he0.le
  have k1 : ∀ u : TorusBond n → ℝ, Q u (angleGradient halfProductPotential) = 0 :=
    fun u => abelianHessian_angleGradient X (isC2AtTrivial_of_coldExpansion hσ hrow hn 0)
      (eventually_gauge_of_coldExpansion hσ hrow hn 0) _ u
  have k2 : ∀ u : TorusBond n → ℝ, Q (angleGradient halfProductPotential) u = 0 := fun u => by
    rw [hQdef, abelianHessian_symm X (isC2AtTrivial_of_coldExpansion hσ hrow hn 0)]
    exact k1 u
  have hdec : (RunningCouplingSlope.linearPotential : TorusBond n → ℝ) =
      torusCurvaturePotential + angleGradient halfProductPotential := by
    funext c
    simp [torusCurvaturePotential]
  have hβα : Q RunningCouplingSlope.linearPotential RunningCouplingSlope.linearPotential =
      Q torusCurvaturePotential torusCurvaturePotential := by
    rw [hdec]
    simp only [map_add, ContinuousLinearMap.add_apply, k1, k2, add_zero]
  have A1 : |formOnLinearPotential (momentCutoff n) K -
      Q RunningCouplingSlope.linearPotential RunningCouplingSlope.linearPotential| ≤
      16 * (n : ℝ) ^ 8 * ((n : ℝ) * n * (ℓ.E * e)) := by
    rw [bilinear_expand Q RunningCouplingSlope.linearPotential RunningCouplingSlope.linearPotential]
    simp only [hQ]
    unfold formOnLinearPotential
    simp only [← Finset.sum_sub_distrib]
    refine abs_double_sum_le fun c c' => ?_
    by_cases hnr : IsNearOriginBond (momentCutoff n) c ∧ IsNearOriginBond (momentCutoff n) c'
    · rw [if_pos hnr]
      have : K c c' * RunningCouplingSlope.linearPotential c * RunningCouplingSlope.linearPotential c' -
          RunningCouplingSlope.linearPotential c * RunningCouplingSlope.linearPotential c' * K c c' = 0 := by ring
      rw [this, abs_zero]
      positivity
    · rw [if_neg hnr, zero_sub, abs_neg]
      exact abs_mul_mul_le (abs_linearPotential_le c) (abs_linearPotential_le c')
        (hfar c c' (le_supportDiam_of_not_near h64 hnr))
  set b : TorusBond n → Prop := fun c => offsetNorm (siteCoords c.1) ≤ n / 8 with hb
  set Bx : Finset (TorusBond n) := Finset.univ.filter b with hBx
  have A2 : |Q torusCurvaturePotential torusCurvaturePotential -
      ∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c'| ≤
      16 * (n : ℝ) ^ 8 * (2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2) * (ℓ.E * e)) := by
    rw [bilinear_expand Q torusCurvaturePotential torusCurvaturePotential, hBx, sum_filter_sum_filter]
    simp only [hQ]
    simp only [← Finset.sum_sub_distrib]
    refine abs_double_sum_le fun c c' => ?_
    by_cases hnr : b c ∧ b c'
    · rw [if_pos hnr, sub_self, abs_zero]
      positivity
    · rw [if_neg hnr, sub_zero]
      exact abs_mul_mul_le (abs_torusCurvaturePotential_le c) (abs_torusCurvaturePotential_le c')
        (hfar c c' (le_supportDiam_of_not_box hnr))
  set t : LatticeBond × LatticeBond → ℝ :=
    fun cc => unitCurvaturePotential cc.1 * unitCurvaturePotential cc.2 *
      secondDerivLimit f cc.1 cc.2 X X with ht
  have hm : 2 * (n / 8 + 1) + 2 < n := by omega
  have A3 : |∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c' -
      ∑ c ∈ Bx, ∑ c' ∈ Bx, t (liftBond c, liftBond c')| ≤
      16 * (n : ℝ) ^ 8 * (2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2) * (ℓ.E * e)) := by
    rw [hBx, sum_filter_sum_filter, sum_filter_sum_filter]
    simp only [← Finset.sum_sub_distrib]
    refine abs_double_sum_le fun c c' => ?_
    by_cases hnr : b c ∧ b c'
    · rw [if_pos hnr, if_pos hnr]
      have q1 : 2 * offsetNorm (siteCoords c.1) + 3 < n := by
        have := hnr.1
        simp only [hb] at this
        omega
      have q2 : 2 * offsetNorm (siteCoords c'.1) + 3 < n := by
        have := hnr.2
        simp only [hb] at this
        omega
      have r1 : offsetNorm (liftBond c).1 + 1 ≤ n / 8 + 1 := by
        have := hnr.1
        simp only [hb] at this
        simpa [liftBond] using this
      have r2 : offsetNorm (liftBond c').1 + 1 ≤ n / 8 + 1 := by
        have := hnr.2
        simp only [hb] at this
        simpa [liftBond] using this
      have hl := abs_mixedDeriv_sub_secondDerivLimit_le hσ hrate hE hn₀ hrow hn hm
        (bondOffsetInBox_of_offsetNorm r1) (bondOffsetInBox_of_offsetNorm r2) hX
      rw [bondFrom_liftBond, bondFrom_liftBond] at hl
      have hl2 : |K c c' - secondDerivLimit f (liftBond c) (liftBond c') X X| ≤ ℓ.E * e := by
        refine hl.trans ((E_div_weight_le hE _).trans (hexp _ ?_))
        have : n ≤ 32 * (n / 8 + 1) := by omega
        exact_mod_cast this
      have e1 : torusCurvaturePotential c * torusCurvaturePotential c' * K c c' -
          t (liftBond c, liftBond c') =
          torusCurvaturePotential c * torusCurvaturePotential c' *
            (K c c' - secondDerivLimit f (liftBond c) (liftBond c') X X) := by
        simp only [ht]
        rw [torusCurvaturePotential_eq q1, torusCurvaturePotential_eq q2]
        ring
      rw [e1]
      exact abs_mul_mul_le (abs_torusCurvaturePotential_le c) (abs_torusCurvaturePotential_le c') hl2
    · rw [if_neg hnr, if_neg hnr, sub_zero, abs_zero]
      positivity
  have hsum : HasSum t 0 := by
    have h := hrow.no_curvature_term (planeCurvature X 0 1) (planeCurvature X 0 1)
      (planeCurvature_antisymm X) (planeCurvature_antisymm X)
    have e1 : (fun cc : LatticeBond × LatticeBond => secondDerivLimit f cc.1 cc.2
        (TorusLumps.linearPotential (planeCurvature X 0 1) cc.1)
        (TorusLumps.linearPotential (planeCurvature X 0 1) cc.2)) = t := by
      funext cc
      rw [linearPotential_planeCurvature, linearPotential_planeCurvature,
        secondDerivLimit_smul_smul hσ hrate hE hn₀ hrow cc.1 cc.2 hX]
    rwa [e1] at h
  set S : Finset (LatticeBond × LatticeBond) := (Bx.image liftBond) ×ˢ (Bx.image liftBond) with hS
  have hSsum : ∑ c ∈ Bx, ∑ c' ∈ Bx, t (liftBond c, liftBond c') = ∑ cc ∈ S, t cc := by
    rw [hS, Finset.sum_product, Finset.sum_image liftBond_injective.injOn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_image liftBond_injective.injOn]
  have hin : ∀ c : LatticeBond, offsetNorm c.1 ≤ n / 8 → c ∈ Bx.image liftBond := by
    intro c hc
    have hz : siteCoords (siteOfInt c.1 : TorusSite n) = c.1 := siteCoords_siteOfInt (by omega)
    refine Finset.mem_image.mpr ⟨((siteOfInt c.1 : TorusSite n), c.2), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [hb, hz]
      exact hc
    · simp only [liftBond, hz]
  have hrho : 0 < ℓ.weightRate / 4 := by positivity
  have A4 : |∑ cc ∈ S, t cc| ≤ 4 * ℓ.E * e * G₀ := by
    have hsg := (summable_bondWeight_mul hrho).mul_left (4 * ℓ.E * e)
    have hg0 : ∀ cc : LatticeBond × LatticeBond,
        0 ≤ 4 * ℓ.E * e * (bondWeight (ℓ.weightRate / 4) cc.1 * bondWeight (ℓ.weightRate / 4) cc.2) :=
      fun cc => mul_nonneg (by positivity) (mul_nonneg (bondWeight_nonneg _ _) (bondWeight_nonneg _ _))
    have h := abs_finset_sum_le_of_hasSum_zero hsum hsg hg0 S ?_
    · rwa [tsum_mul_left] at h
    intro cc hcc
    have hR : n / 8 ≤ max (offsetNorm cc.1.1) (offsetNorm cc.2.1) := by
      by_contra hlt
      apply hcc
      have h1 : offsetNorm cc.1.1 ≤ n / 8 := by
        have := le_max_left (offsetNorm cc.1.1) (offsetNorm cc.2.1)
        omega
      have h2 : offsetNorm cc.2.1 ≤ n / 8 := by
        have := le_max_right (offsetNorm cc.1.1) (offsetNorm cc.2.1)
        omega
      exact Finset.mem_product.mpr ⟨hin _ h1, hin _ h2⟩
    have h1 := abs_potential_mul_le_bondWeight hrate hE
      (abs_secondDerivLimit_le hσ hrate hE hn₀ hrow cc.1 cc.2 hX) hR
    refine h1.trans (mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (bondWeight_nonneg _ _) (bondWeight_nonneg _ _)))
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h16 : (n : ℝ) ≤ 16 * ((n / 8 : ℕ) : ℝ) := by
      have : n ≤ 16 * (n / 8) := by omega
      exact_mod_cast this
    have hR0 : (0 : ℝ) ≤ ((n / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : v * n ≤ v * (16 * ((n / 8 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h16 hv0.le
    have h4 : v * ((n / 8 : ℕ) : ℝ) ≤ ℓ.weightRate * ((n / 8 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hv hR0
    nlinarith
  rw [hSsum] at A3
  have hn2 : (n : ℝ) * n ≤ (n : ℝ) ^ 4 := by
    have : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
    nlinarith
  have hn8 : 0 ≤ 16 * (n : ℝ) ^ 8 := by positivity
  have A1' : |formOnLinearPotential (momentCutoff n) K -
      Q RunningCouplingSlope.linearPotential RunningCouplingSlope.linearPotential| ≤
      16 * (n : ℝ) ^ 8 * ((n : ℝ) ^ 4 * (ℓ.E * e)) :=
    A1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn2 hEe) hn8)
  rw [hβα] at A1'
  have tri := abs_add_four_le
    (formOnLinearPotential (momentCutoff n) K - Q torusCurvaturePotential torusCurvaturePotential)
    (Q torusCurvaturePotential torusCurvaturePotential -
      ∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c')
    (∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c' -
      ∑ cc ∈ S, t cc)
    (∑ cc ∈ S, t cc)
  have e0 : (formOnLinearPotential (momentCutoff n) K -
      Q torusCurvaturePotential torusCurvaturePotential) +
      (Q torusCurvaturePotential torusCurvaturePotential -
        ∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c') +
      (∑ c ∈ Bx, ∑ c' ∈ Bx, torusCurvaturePotential c * torusCurvaturePotential c' * K c c' -
        ∑ cc ∈ S, t cc) +
      (∑ cc ∈ S, t cc) = formOnLinearPotential (momentCutoff n) K := by ring
  rw [e0] at tri
  have e1 : (144 * (n : ℝ) ^ 12 + 4 * G₀) * ℓ.E * e =
      16 * (n : ℝ) ^ 8 * ((n : ℝ) ^ 4 * (ℓ.E * e)) +
      16 * (n : ℝ) ^ 8 * (2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2) * (ℓ.E * e)) +
      16 * (n : ℝ) ^ 8 * (2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2) * (ℓ.E * e)) +
      4 * ℓ.E * e * G₀ := by ring
  rw [e1]
  linarith
end Torus
theorem pow_mul_exp_le {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s) :
    s ^ 12 * Real.exp (-(v * s / 32)) ≤ (768 / v) ^ 12 * Real.exp (-(v * s / 64)) := by
  set y : ℝ := v * s / 768 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have h2 : y ^ 12 ≤ Real.exp (v * s / 64) := by
    have h3 : y ^ 12 ≤ Real.exp y ^ 12 := pow_le_pow_left₀ hy0 h1 12
    have h4 : Real.exp y ^ 12 = Real.exp (v * s / 64) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hy]
      push_cast
      ring
    linarith
  have h5 : s = 768 / v * y := by
    rw [hy]
    field_simp
  have h6 : Real.exp (-(v * s / 32)) = Real.exp (-(v * s / 64)) * Real.exp (-(v * s / 64)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h7 : Real.exp (v * s / 64) * Real.exp (-(v * s / 64)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc s ^ 12 * Real.exp (-(v * s / 32))
      = (768 / v) ^ 12 * (y ^ 12 * Real.exp (-(v * s / 64))) * Real.exp (-(v * s / 64)) := by
        rw [h6]
        nth_rewrite 1 [h5]
        ring
    _ ≤ (768 / v) ^ 12 * (Real.exp (v * s / 64) * Real.exp (-(v * s / 64))) *
        Real.exp (-(v * s / 64)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (768 / v) ^ 12 * Real.exp (-(v * s / 64)) := by
        rw [h7]
        ring
theorem centeredDensityMomentDecay_of_formFamily (hForms : formFamilyMomentStatement) :
    CenteredDensityMomentDecay := by
  intro T hT
  set ρ : ℝ := T.rt / 2 ^ 10 with hρdef
  have hρ : 0 < ρ := by
    have := hT.rt_pos
    positivity
  set v : ℝ := min ρ 1 with hvdef
  have hv0 : 0 < v := lt_min hρ one_pos
  have hv1 : v ≤ 1 := min_le_right _ _
  have hvρ : v ≤ ρ := min_le_left _ _
  obtain ⟨Cf, hCf, hF⟩ := hForms v hv0 hv1
  set G₀ : ℝ := ∑' cc : LatticeBond × LatticeBond, bondWeight (ρ / 4) cc.1 * bondWeight (ρ / 4) cc.2
    with hG₀
  have hG₀0 : 0 ≤ G₀ :=
    tsum_nonneg fun cc => mul_nonneg (bondWeight_nonneg _ _) (bondWeight_nonneg _ _)
  have hE : 0 < T.E := by
    have := hT.B_ge
    unfold RenormalizationStepParameters.ParameterAssignment.E
    linarith
  refine ⟨Cf * T.E + 144 * T.E * (768 / v) ^ 12 + 4 * G₀ * T.E + 1, v / 64, by positivity,
    by positivity, ?_⟩
  intro y t x D f hy hrow n _ X hn hX
  have h4096 := hT.n₀_ge
  have hnT : (T.stepParameters y).n₀ ≤ n := hn
  have hσ : 0 < (T.stepParameters y).threshold := hT.σ_pos
  have hrate : 0 < (T.stepParameters y).weightRate := hρ
  have hEl : 0 ≤ (T.stepParameters y).E := hE.le
  have hn₀ : 0 < (T.stepParameters y).n₀ := by
    show 0 < T.n₀
    omega
  have h64 : 64 ≤ n := by omega
  have hfam := densityHessian_isDecayingFormFamily hσ hEl hrow hnT hX (v := v) hvρ
  have h1 := hF n (T.stepParameters y).E (densityHessian f n X) h64 hEl hfam
  have h2 := abs_formOnLinearPotential_le hσ hrate hEl hn₀ hrow hnT h64 hX hv0 hvρ
  have hM : gaugeTotalMoment (centeredDensityTotal f) n X =
      kernelSecondMoment fun c c' => ∑ Y, densityHessian f n X Y c c' := by
    unfold gaugeTotalMoment
    congr 1
    funext c c'
    exact hessianAtTrivial_centeredDensityTotal hσ hrow hnT X c c'
  rw [hM]
  change |_ - formOnLinearPotential (momentCutoff n) (densityHessian f n X 0)| ≤ Cf * T.E * _ at h1
  change |formOnLinearPotential (momentCutoff n) (densityHessian f n X 0)| ≤
    (144 * (n : ℝ) ^ 12 + 4 * G₀) * T.E * _ at h2
  set e1 : ℝ := Real.exp (-(v * n / 32)) with he1
  set e2 : ℝ := Real.exp (-(v * n / 64)) with he2
  have e2eq : Real.exp (-(v / 64 * n)) = e2 := by
    rw [he2]
    congr 1
    ring
  rw [e2eq]
  have he2p : 0 < e2 := Real.exp_pos _
  have h3 : e1 ≤ e2 := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ v * (n : ℝ) := by positivity
    linarith
  have h4 : (n : ℝ) ^ 12 * e1 ≤ (768 / v) ^ 12 * e2 := pow_mul_exp_le hv0 (Nat.cast_nonneg n)
  have h5 := abs_sub_abs_le_abs_sub
    (kernelSecondMoment fun c c' => ∑ Y, densityHessian f n X Y c c')
    (formOnLinearPotential (momentCutoff n) (densityHessian f n X 0))
  have h6 : (144 * (n : ℝ) ^ 12 + 4 * G₀) * T.E * e1 ≤
      144 * T.E * ((768 / v) ^ 12 * e2) + 4 * G₀ * T.E * e2 := by
    have a1 : 144 * T.E * ((n : ℝ) ^ 12 * e1) ≤ 144 * T.E * ((768 / v) ^ 12 * e2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have a2 : 4 * G₀ * T.E * e1 ≤ 4 * G₀ * T.E * e2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  nlinarith
end YangMills.Construction.RunningCouplingSlope.CenteredDensityMoment
end
