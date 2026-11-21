import YangMills.Construction.EuclideanFunctionals.ConeConditionOfAReconstructionInThreeFormsAndTheCalculusOverThePyramid
import YangMills.Construction.EuclideanFunctionals.FormsOfTheOperatorsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.StronglyContinuousUnitaryGroupsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeOperatorForms
open HilbertSpaceBasics (UnboundedOp ofBounded)
open BorelSpectral
open BorelCalculus (IsBoundedFn)
open SpectralMeasureCalculus
  (UnboundedCalculusLaws BoundedCalculusLaws PushforwardAndSupportLaws)
open SpectralTheorem
  (IsSpectralIntegralOf RealLineSet spectralIntegralOp pushforwardToLine spectralMeasure)
open ResolvedOps (IsDiagonalized StronglyCommute expComplex)
open ResolvedFacts (rightClosedHalfPlane realSpectralIntegral)
open ForwardTube (closedForwardTube)
open SpectralPoint
open EuclidFunctionalWithRecon
section Plane
theorem lightCone_exponent_eq (p : EPlanePoints) (v : ℂ × ℂ) :
    v.1 * (p.1 0 : ℂ) - Complex.I * v.2 * (p.1 1 : ℂ) =
      ForwardTube.lightConePlus v * (lightConePlus p : ℂ) +
        ForwardTube.lightConeMinus v * (lightConeMinus p : ℂ) := by
  simp only [ForwardTube.lightConePlus, ForwardTube.lightConeMinus, lightConePlus, lightConeMinus]
  push_cast
  ring
theorem planeExpKernel_eq_exp (v : ℂ × ℂ) (p : EPlanePoints) :
    planeExpKernel v p =
      Complex.exp (-(ForwardTube.lightConePlus v * (lightConePlus p : ℂ)) -
        ForwardTube.lightConeMinus v * (lightConeMinus p : ℂ)) := by
  unfold planeExpKernel
  congr 1
  linear_combination -(lightCone_exponent_eq p v)
theorem norm_planeExpKernel_eq (v : ℂ × ℂ) (p : EPlanePoints) :
    ‖planeExpKernel v p‖ =
      Real.exp (-((ForwardTube.lightConePlus v).re * lightConePlus p) -
        (ForwardTube.lightConeMinus v).re * lightConeMinus p) := by
  rw [planeExpKernel_eq_exp, Complex.norm_exp]
  simp
theorem wedge_eq_lightCone :
    wedge.1 = {p | 0 ≤ lightConePlus p ∧ 0 ≤ lightConeMinus p} := by
  ext p
  change |p.1 1| ≤ p.1 0 ↔ 0 ≤ lightConePlus p ∧ 0 ≤ lightConeMinus p
  simp only [lightConePlus, lightConeMinus, abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
theorem norm_planeExpKernel_le_one {v : ℂ × ℂ} (hv : v ∈ closedForwardTube) {p : EPlanePoints}
    (hp : p ∈ wedge.1) : ‖planeExpKernel v p‖ ≤ 1 := by
  rw [wedge_eq_lightCone] at hp
  obtain ⟨h₁, h₂⟩ := hp
  obtain ⟨k₁, k₂⟩ := hv
  rw [norm_planeExpKernel_eq, Real.exp_le_one_iff]
  have := mul_nonneg k₁ h₁
  have := mul_nonneg k₂ h₂
  linarith
theorem wedgeInLightConeCoords_holds : WedgeInLightConeCoords :=
  ⟨wedge_eq_lightCone, fun p v => ⟨lightCone_exponent_eq p v, planeExpKernel_eq_exp v p,
    norm_planeExpKernel_eq v p⟩, fun _ hv _ hp => norm_planeExpKernel_le_one hv hp⟩
def complexEnergy (p : EPlanePoints) : ℂ := ((p.1 0 : ℝ) : ℂ)
def complexMomentum (p : EPlanePoints) : ℂ := ((p.1 1 : ℝ) : ℂ)
theorem measurable_complexEnergy : Measurable complexEnergy :=
  Complex.measurable_ofReal.comp measurable_planeEnergyCoord
theorem measurable_complexMomentum : Measurable complexMomentum :=
  Complex.measurable_ofReal.comp measurable_planeMomentumCoord
theorem measurable_planeExpKernel (v : ℂ × ℂ) : Measurable (planeExpKernel v) := by
  exact show Measurable fun p : EPlanePoints =>
      Complex.exp (-(v.1 * complexEnergy p) + Complex.I * v.2 * complexMomentum p) from
    Complex.measurable_exp.comp
      ((measurable_complexEnergy.const_mul v.1).neg.add
        (measurable_complexMomentum.const_mul _))
theorem measurable_lightConePlusCoord : Measurable lightConePlus := by
  exact show Measurable fun p : EPlanePoints => 1 / 2 * (planeEnergyCoord p - planeMomentumCoord p) from
    (measurable_planeEnergyCoord.sub measurable_planeMomentumCoord).const_mul _
theorem measurable_lightConeMinusCoord : Measurable lightConeMinus := by
  exact show Measurable fun p : EPlanePoints => 1 / 2 * (planeEnergyCoord p + planeMomentumCoord p) from
    (measurable_planeEnergyCoord.add measurable_planeMomentumCoord).const_mul _
def diamondCutoff (k : ℕ) : EPlanePoints → ℂ := indicator {p | |p.1 0| + |p.1 1| ≤ (k : ℝ)} 1
theorem measurable_diamondCutoff (k : ℕ) : Measurable (diamondCutoff k) := by
  have h : Measurable fun p : EPlanePoints => |planeEnergyCoord p| + |planeMomentumCoord p| :=
    measurable_planeEnergyCoord.abs.add measurable_planeMomentumCoord.abs
  exact measurable_one.indicator (measurableSet_le h measurable_const)
theorem isBoundedFn_mul_diamondCutoff {g : EPlanePoints → ℂ}
    (hg : ∀ p, ‖g p‖ ≤ |p.1 0| + |p.1 1|) (k : ℕ) :
    IsBoundedFn (g * diamondCutoff k) := by
  refine ⟨k, fun p => ?_⟩
  by_cases hp : p ∈ {p : EPlanePoints | |p.1 0| + |p.1 1| ≤ (k : ℝ)}
  · simp only [Pi.mul_apply, diamondCutoff, indicator_of_mem hp, Pi.one_apply, mul_one]
    exact (hg p).trans hp
  · simp only [Pi.mul_apply, diamondCutoff, indicator_of_notMem hp, mul_zero, norm_zero]
    exact Nat.cast_nonneg k
theorem norm_one_sub_diamondCutoff_le (k : ℕ) (p : EPlanePoints) : ‖1 - diamondCutoff k p‖ ≤ 1 := by
  by_cases hp : p ∈ {p : EPlanePoints | |p.1 0| + |p.1 1| ≤ (k : ℝ)}
  · simp [diamondCutoff, indicator_of_mem hp]
  · simp [diamondCutoff, indicator_of_notMem hp]
theorem eventually_diamondCutoff_eq_one (p : EPlanePoints) :
    ∀ᶠ k in atTop, diamondCutoff k p = 1 := by
  obtain ⟨r, hr⟩ := exists_nat_ge (|p.1 0| + |p.1 1|)
  filter_upwards [eventually_ge_atTop r] with k hk
  have hp : p ∈ {p : EPlanePoints | |p.1 0| + |p.1 1| ≤ (k : ℝ)} :=
    hr.trans (by exact_mod_cast hk)
  simp [diamondCutoff, indicator_of_mem hp]
def halfLineExp (ζ : ℂ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator fun x => Complex.exp (-ζ * (x : ℂ))
theorem measurable_halfLineExp (ζ : ℂ) : Measurable (halfLineExp ζ) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  exact Complex.measurable_exp.comp (Complex.measurable_ofReal.const_mul _)
theorem norm_halfLineExp_le {ζ : ℂ} (hζ : ζ ∈ rightClosedHalfPlane) (x : ℝ) :
    ‖halfLineExp ζ x‖ ≤ 1 := by
  by_cases hx : x ∈ Ici (0 : ℝ)
  · have hx' : (0 : ℝ) ≤ x := hx
    have hz : (0 : ℝ) ≤ ζ.re := hζ
    simp only [halfLineExp, indicator_of_mem hx]
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [mul_nonneg hz hx']
  · simp [halfLineExp, indicator_of_notMem hx]
end Plane
section Calculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {E : SpectralMeasure Y H}
theorem mem_integralDom_iff_memLp {g : Y → ℂ} (hg : Measurable g) (ψ : H) :
    ψ ∈ E.integralDom g ↔ MemLp g 2 (E.diagMeasure ψ) := by
  have h : MemLp g 2 (E.diagMeasure ψ) ↔ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞ := by
    constructor
    · intro hm
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := E.diagMeasure ψ)
        (f := g) (p := 2) (by norm_num) (by norm_num)).1 hm.2
      simpa using this
    · intro hl
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).2 ?_
      simpa using hl
  exact h.symm
theorem tendsto_integralOp_mul_cutoff (hA : UnboundedCalculusLaws E) {g : Y → ℂ}
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ E.integralDom g) (c : ℕ → Y → ℂ)
    (hc : ∀ k, Measurable (c k)) (hb : ∀ k, IsBoundedFn (g * c k))
    (h₁ : ∀ k y, ‖1 - c k y‖ ≤ 1) (hlim : ∀ y, ∀ᶠ k in atTop, c k y = 1) :
    Tendsto (fun k => E.integralOp (g * c k) ψ) atTop (𝓝 (E.integralApply g ψ)) := by
  have hs := fun k => hA.norm_sub_sq g (g * c k) hg (hg.mul (hc k)) (hb k) ψ hψ
  have hint : Integrable (fun y => ‖g y‖ ^ 2) (E.diagMeasure ψ) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1
      ((mem_integralDom_iff_memLp hg ψ).1 hψ)
  have hto : Tendsto (fun k => ∫ y, ‖g y - (g * c k) y‖ ^ 2 ∂E.diagMeasure ψ) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂E.diagMeasure ψ)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖ ^ 2)
      (fun k => ((hg.sub (hg.mul (hc k))).norm.pow_const 2).aestronglyMeasurable) hint
      (fun k => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have he : g y - (g * c k) y = g y * (1 - c k y) := by
        simp only [Pi.mul_apply]
        ring
      rw [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
      have h₂ : ‖1 - c k y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (h₁ k y)
      exact mul_le_of_le_one_right (by positivity) h₂
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim y] with k hk
      simp [hk]
  rw [integral_zero] at hto
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : (fun k => ‖E.integralOp (g * c k) ψ - E.integralApply g ψ‖) =
      fun k => Real.sqrt (∫ y, ‖g y - (g * c k) y‖ ^ 2 ∂E.diagMeasure ψ) := by
    funext k
    rw [← hs k, Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
  rw [hsq]
  have hlim₀ := (Real.continuous_sqrt.tendsto 0).comp hto
  rw [Real.sqrt_zero] at hlim₀
  exact hlim₀
theorem expComplex_realSpectralIntegral (hI : PushforwardAndSupportLaws E) {g : Y → ℝ}
    (hg : Measurable g) (hs : spectralMeasure (realSpectralIntegral E g) = pushforwardToLine E g hg)
    {ζ : ℂ} (hζ : ζ ∈ rightClosedHalfPlane) :
    expComplex (realSpectralIntegral E g) ζ =
      E.integralOp fun y => halfLineExp ζ (g y) := by
  have hf : Measurable fun y : RealLineSet => halfLineExp ζ (y.1 0) :=
    (measurable_halfLineExp ζ).comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have hκ : Measurable fun y : Y => (⟨fun _ => g y, mem_univ _⟩ : RealLineSet) :=
    Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => hg)
  have hb : ∀ y : RealLineSet, ‖halfLineExp ζ (y.1 0)‖ ≤ 1 :=
    fun y => norm_halfLineExp_le hζ _
  have hb' : ∀ y : Y, ‖halfLineExp ζ (g y)‖ ≤ 1 :=
    fun y => norm_halfLineExp_le hζ _
  have hs' := hI.integral_image le_rfl MeasurableSet.univ _ hκ _ hf
  change (spectralMeasure (realSpectralIntegral E g)).integralOp
    (fun y => halfLineExp ζ (y.1 0)) = _
  rw [hs]
  ext ψ
  rw [← SpectralMeasure.integralApply_eq_integralOp _ hb,
    ← SpectralMeasure.integralApply_eq_integralOp _ hb']
  refine hs'.2 ψ ?_
  have hd := SpectralMeasure.integralDom_eq_univ (pushforwardToLine E g hg) hb
  exact hd ▸ mem_univ ψ
theorem isSpectralIntegralOf_of_eq (hA : UnboundedCalculusLaws E) {g : Y → ℂ} (hg : Measurable g)
    {A : UnboundedOp H} (h : A = spectralIntegralOp E g) : IsSpectralIntegralOf A E g := by
  rw [h]
  exact hA.isIntegralOf g hg
theorem isBoundedFn_smul {X : Type*} (a : ℂ) {f : X → ℂ} (hf : IsBoundedFn f) :
    IsBoundedFn (a • f) := by apply _root_.YangMills.Construction.UnitaryGroups.Stone.isBoundedFn_smul <;> assumption
theorem zeroExtend_of_mem {X β : Type*} [Zero β] {Δ : Set X} (g : Δ → β) {y : X} (hy : y ∈ Δ) :
    zeroExtend Δ g y = g ⟨y, hy⟩ :=
  dif_pos hy
theorem norm_zeroExtend_le {X : Type*} {Δ : Set X} {g : Δ → ℂ} (hg : ∀ y, ‖g y‖ ≤ 1) (y : X) :
    ‖zeroExtend Δ g y‖ ≤ 1 := by
  by_cases h : y ∈ Δ
  · rw [zeroExtend_of_mem g h]
    exact hg _
  · have h₀ : zeroExtend Δ g y = 0 := dif_neg h
    rw [h₀, norm_zero]
    exact zero_le_one
end Calculus
section OnThePlane
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure EPlanePoints H}
theorem integralApply_linearCombo (hB : BoundedCalculusLaws E) (hA : UnboundedCalculusLaws E)
    (a b : ℂ) {g : EPlanePoints → ℂ} (hg : Measurable g)
    (hform : ∀ p, g p = a * complexEnergy p + b * complexMomentum p)
    (hbound : ∀ p : EPlanePoints, ‖g p‖ ≤ |p.1 0| + |p.1 1|) {ψ : H}
    (h₀ : ψ ∈ E.integralDom complexEnergy) (h₁ : ψ ∈ E.integralDom complexMomentum) :
    ψ ∈ E.integralDom g ∧
      E.integralApply g ψ =
        a • E.integralApply complexEnergy ψ + b • E.integralApply complexMomentum ψ := by
  have hgeq : g = a • complexEnergy + b • complexMomentum := funext fun p => by simp [hform]
  have hdom : ψ ∈ E.integralDom g := by
    rw [mem_integralDom_iff_memLp hg, hgeq]
    exact (((mem_integralDom_iff_memLp measurable_complexEnergy ψ).1 h₀).const_smul a).add
      (((mem_integralDom_iff_memLp measurable_complexMomentum ψ).1 h₁).const_smul b)
  refine ⟨hdom, ?_⟩
  have hbE : ∀ p : EPlanePoints, ‖complexEnergy p‖ ≤ |p.1 0| + |p.1 1| := fun p => by
    simp only [complexEnergy, Complex.norm_real, Real.norm_eq_abs]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hbM : ∀ p : EPlanePoints, ‖complexMomentum p‖ ≤ |p.1 0| + |p.1 1| := fun p => by
    simp only [complexMomentum, Complex.norm_real, Real.norm_eq_abs]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have t := tendsto_integralOp_mul_cutoff hA hg hdom diamondCutoff measurable_diamondCutoff
    (isBoundedFn_mul_diamondCutoff hbound) norm_one_sub_diamondCutoff_le
    eventually_diamondCutoff_eq_one
  have t₀ := tendsto_integralOp_mul_cutoff hA measurable_complexEnergy h₀ diamondCutoff
    measurable_diamondCutoff (isBoundedFn_mul_diamondCutoff hbE) norm_one_sub_diamondCutoff_le
    eventually_diamondCutoff_eq_one
  have t₁ := tendsto_integralOp_mul_cutoff hA measurable_complexMomentum h₁ diamondCutoff
    measurable_diamondCutoff (isBoundedFn_mul_diamondCutoff hbM) norm_one_sub_diamondCutoff_le
    eventually_diamondCutoff_eq_one
  have hk : ∀ k, E.integralOp (g * diamondCutoff k) =
      a • E.integralOp (complexEnergy * diamondCutoff k) +
        b • E.integralOp (complexMomentum * diamondCutoff k) := fun k => by
    have hf : g * diamondCutoff k =
        a • (complexEnergy * diamondCutoff k) + b • (complexMomentum * diamondCutoff k) := by
      rw [hgeq]
      funext p
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have m₀ := measurable_complexEnergy.mul (measurable_diamondCutoff k)
    have m₁ := measurable_complexMomentum.mul (measurable_diamondCutoff k)
    have b₀ := isBoundedFn_mul_diamondCutoff hbE k
    have b₁ := isBoundedFn_mul_diamondCutoff hbM k
    rw [hf, hB.add _ _ (m₀.const_smul a) (isBoundedFn_smul a b₀) (m₁.const_smul b)
      (isBoundedFn_smul b b₁), hB.smul a _ m₀ b₀, hB.smul b _ m₁ b₁]
  have hfun : (fun k => E.integralOp (g * diamondCutoff k) ψ) = fun k =>
      a • E.integralOp (complexEnergy * diamondCutoff k) ψ +
        b • E.integralOp (complexMomentum * diamondCutoff k) ψ :=
    funext fun k => by
      rw [hk k]
      rfl
  rw [hfun] at t
  exact tendsto_nhds_unique t ((t₀.const_smul a).add (t₁.const_smul b))
theorem realSpectralIntegral_linearCombo (hB : BoundedCalculusLaws E)
    (hA : UnboundedCalculusLaws E) (a b : ℂ)
    {H₀ P₀ : UnboundedOp H} (hH : IsSpectralIntegralOf H₀ E complexEnergy)
    (hP : IsSpectralIntegralOf P₀ E complexMomentum) {u : EPlanePoints → ℝ} (hm : Measurable u)
    (hform : ∀ p, ((u p : ℝ) : ℂ) = a * complexEnergy p + b * complexMomentum p)
    (hbound : ∀ p : EPlanePoints, |u p| ≤ |p.1 0| + |p.1 1|) (ψ : H) (h₀ : ψ ∈ H₀.domain)
    (h₁ : ψ ∈ P₀.domain) :
    ∃ h : ψ ∈ (realSpectralIntegral E u).domain,
      realSpectralIntegral E u ⟨ψ, h⟩ = a • H₀ ⟨ψ, h₀⟩ + b • P₀ ⟨ψ, h₁⟩ := by
  have hmc : Measurable fun p => ((u p : ℝ) : ℂ) := Complex.measurable_ofReal.comp hm
  obtain ⟨hd, hv⟩ := integralApply_linearCombo hB hA a b hmc hform
    (fun p => by simpa using hbound p) ((hH.1 ψ).1 h₀) ((hP.1 ψ).1 h₁)
  have hU : IsSpectralIntegralOf (realSpectralIntegral E u) E fun p => ((u p : ℝ) : ℂ) :=
    hA.isIntegralOf _ hmc
  refine ⟨(hU.1 ψ).2 hd, ?_⟩
  have e₀ := hH.2 ⟨ψ, h₀⟩
  have e₁ := hP.2 ⟨ψ, h₁⟩
  have eU := hU.2 ⟨ψ, (hU.1 ψ).2 hd⟩
  refine (eU.trans hv).trans ?_
  rw [e₀, e₁]
end OnThePlane
section Reconstruction
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem planeMeasureIsPushforward_holds (hL : ReconstructionMeasureOperatorFacts) :
    PlaneMeasureIsPushforward σ :=
  fun Δ' => (hL c S σ).1.planeMeasure_apply Δ'
theorem coneConditionIffOffWedgeNull_holds (hL : ReconstructionMeasureOperatorFacts) :
    ConeConditionIffOffWedgeNull σ := by
  have h : σ.planeMeasure ⟨wedge.1ᶜ, wedge.2.compl⟩ =
      σ.jointMeasure ⟨planeProj ⁻¹' wedge.1ᶜ, measurable_planeProj wedge.2.compl⟩ :=
    planeMeasureIsPushforward_holds σ hL _
  have hs : (⟨planeProj ⁻¹' wedge.1ᶜ, measurable_planeProj wedge.2.compl⟩ :
      BorelSubsets EMPoints) = belowAbsMomentum (basisVec 0) := by
    refine Subtype.ext ?_
    ext p
    change ¬ (|(planeProj p).1 1| ≤ (planeProj p).1 0) ↔
      SpectralPoint.energyOf p < |dot3 (basisVec 0) (SpectralPoint.momentumOf p)|
    have hd : dot3 (basisVec 0) (SpectralPoint.momentumOf p) = SpectralPoint.momentumOf p 0 := by
      simp [dot3, basisVec, Pi.single_apply]
    rw [hd, not_le]
    rfl
  unfold ConeConditionIffOffWedgeNull
  rw [h, hs]
  rfl
abbrev energyMomentumGens : Fin 2 → UnboundedOp σ.space :=
  ![σ.recon.ham, σ.recon.mom 0]
theorem energyMomentumGens_isDiagonalized (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (k : Fin 2) : IsDiagonalized (energyMomentumGens σ k) := by
  have h := (hC.1 σ.space).2.2.2.1
  fin_cases k
  · exact h _ σ.recon.ham_selfAdjoint
  · exact h _ (σ.recon.mom_selfAdjoint 0)
theorem energyMomentumGens_commute (j k : Fin 2) (hjk : j ≠ k) :
    StronglyCommute (energyMomentumGens σ j) (energyMomentumGens σ k) := by
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · exact fun Δ Δ' => (σ.recon.mom_commute_ham 0 Δ' Δ).symm
  · exact σ.recon.mom_commute_ham 0
  · exact absurd rfl hjk
theorem ham_eq_spectralIntegral (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation) :
    σ.recon.ham = spectralIntegralOp σ.planeMeasure complexEnergy :=
  ((hJ σ.space).1 2 (by norm_num) (energyMomentumGens σ) (energyMomentumGens_isDiagonalized σ hC)
    (energyMomentumGens_commute σ)).2.2.2.2.1 0
theorem mom_eq_spectralIntegral (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation) :
    σ.recon.mom 0 = spectralIntegralOp σ.planeMeasure complexMomentum :=
  ((hJ σ.space).1 2 (by norm_num) (energyMomentumGens σ) (energyMomentumGens_isDiagonalized σ hC)
    (energyMomentumGens_commute σ)).2.2.2.2.1 1
theorem tubeOp_eq_ofBounded (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hcar : σ.planeMeasure.IsCarriedBy wedge) {v : ℂ × ℂ} (hv : v ∈ closedForwardTube) :
    σ.tubeOp v = ofBounded (σ.wedgeIntegralOp v) ∧
      ‖σ.wedgeIntegralOp v‖ ≤ 1 := by
  have hm : Measurable fun p : wedge.1 => planeExpKernel v p.1 :=
    (measurable_planeExpKernel v).comp measurable_subtype_coe
  obtain ⟨-, -, -, -, -, -, h⟩ := (hJ σ.space).1 2 (by norm_num) (energyMomentumGens σ)
    (energyMomentumGens_isDiagonalized σ hC) (energyMomentumGens_commute σ)
  obtain ⟨h₁, h₂⟩ := h wedge (fun p => planeExpKernel v p.1) hcar hm
    ⟨1, fun p => norm_planeExpKernel_le_one hv p.2⟩
  exact ⟨h₁, h₂.trans (Real.iSup_le (fun p => norm_planeExpKernel_le_one hv p.2) zero_le_one)⟩
theorem expComplex_mul_lightCone (hF : ResolvedFacts.DiagonalizedFacts)
    (hD : SpectralMeasureCalculus.CalculusTheorem) {ζ ζ' : ℂ}
    (hζ : ζ ∈ rightClosedHalfPlane) (hζ' : ζ' ∈ rightClosedHalfPlane) :
    expComplex σ.lightConeOpPlus ζ * expComplex σ.lightConeOpMinus ζ' =
        σ.planeMeasure.integralOp
          ((fun y => halfLineExp ζ (lightConePlus y)) *
            fun y => halfLineExp ζ' (lightConeMinus y)) ∧
      expComplex σ.lightConeOpMinus ζ' * expComplex σ.lightConeOpPlus ζ =
        σ.planeMeasure.integralOp
          ((fun y => halfLineExp ζ (lightConePlus y)) *
            fun y => halfLineExp ζ' (lightConeMinus y)) := by
  obtain ⟨hR, -⟩ := (hF σ.space).2.2.2.2.2.1 2 univ σ.planeMeasure univ_nonempty
  obtain ⟨-, hB, -, -, hI, -⟩ := hD σ.space 2 univ σ.planeMeasure
  have mp := measurable_lightConePlusCoord
  have mm := measurable_lightConeMinusCoord
  have e₁ : expComplex σ.lightConeOpPlus ζ =
      σ.planeMeasure.integralOp fun y => halfLineExp ζ (lightConePlus y) :=
    expComplex_realSpectralIntegral hI mp (hR _ mp).2.1 hζ
  have e₂ : expComplex σ.lightConeOpMinus ζ' =
      σ.planeMeasure.integralOp fun y => halfLineExp ζ' (lightConeMinus y) :=
    expComplex_realSpectralIntegral hI mm (hR _ mm).2.1 hζ'
  have m₁ : Measurable fun y => halfLineExp ζ (lightConePlus y) :=
    (measurable_halfLineExp ζ).comp mp
  have m₂ : Measurable fun y => halfLineExp ζ' (lightConeMinus y) :=
    (measurable_halfLineExp ζ').comp mm
  have b₁ : IsBoundedFn fun y => halfLineExp ζ (lightConePlus y) :=
    ⟨1, fun y => norm_halfLineExp_le hζ _⟩
  have b₂ : IsBoundedFn fun y => halfLineExp ζ' (lightConeMinus y) :=
    ⟨1, fun y => norm_halfLineExp_le hζ' _⟩
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂, hB.mul _ _ m₁ b₁ m₂ b₂]
  · rw [e₁, e₂, ← hB.mul _ _ m₂ b₂ m₁ b₁, mul_comm]
theorem integralOp_halfLineExp_prod_eq (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hcar : σ.planeMeasure.IsCarriedBy wedge) {v : ℂ × ℂ} (hv : v ∈ closedForwardTube) :
    σ.planeMeasure.integralOp
        ((fun y => halfLineExp (ForwardTube.lightConePlus v) (lightConePlus y)) *
          fun y => halfLineExp (ForwardTube.lightConeMinus v) (lightConeMinus y)) =
      σ.wedgeIntegralOp v := by
  obtain ⟨-, hB, -⟩ := hD σ.space 2 univ σ.planeMeasure
  have hp : ForwardTube.lightConePlus v ∈ rightClosedHalfPlane := hv.1
  have hm : ForwardTube.lightConeMinus v ∈ rightClosedHalfPlane := hv.2
  have m₁ : Measurable fun y => halfLineExp (ForwardTube.lightConePlus v) (lightConePlus y) :=
    (measurable_halfLineExp _).comp measurable_lightConePlusCoord
  have m₂ : Measurable fun y => halfLineExp (ForwardTube.lightConeMinus v) (lightConeMinus y) :=
    (measurable_halfLineExp _).comp measurable_lightConeMinusCoord
  have hΦ : ∀ p : wedge.1, ‖planeExpKernel v p.1‖ ≤ 1 :=
    fun p => norm_planeExpKernel_le_one hv p.2
  refine hB.congr _ (zeroExtend wedge.1 fun p => planeExpKernel v p.1) wedge (m₁.mul m₂)
    ⟨1, fun y => ?_⟩ (measurable_zeroExtend wedge.2
      ((measurable_planeExpKernel v).comp measurable_subtype_coe))
    ⟨1, norm_zeroExtend_le hΦ⟩ hcar fun y hy => ?_
  · change ‖halfLineExp (ForwardTube.lightConePlus v) (lightConePlus y) *
      halfLineExp (ForwardTube.lightConeMinus v) (lightConeMinus y)‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ (norm_halfLineExp_le hp _) (norm_nonneg _)
      (norm_halfLineExp_le hm _)
  · have hy' := hy
    rw [wedge_eq_lightCone] at hy'
    have e₁ : halfLineExp (ForwardTube.lightConePlus v) (lightConePlus y) =
        Complex.exp (-ForwardTube.lightConePlus v * (lightConePlus y : ℂ)) :=
      indicator_of_mem (mem_Ici.2 hy'.1) _
    have e₂ : halfLineExp (ForwardTube.lightConeMinus v) (lightConeMinus y) =
        Complex.exp (-ForwardTube.lightConeMinus v * (lightConeMinus y : ℂ)) :=
      indicator_of_mem (mem_Ici.2 hy'.2) _
    change halfLineExp (ForwardTube.lightConePlus v) (lightConePlus y) *
      halfLineExp (ForwardTube.lightConeMinus v) (lightConeMinus y) = _
    rw [e₁, e₂, zeroExtend_of_mem _ hy, planeExpKernel_eq_exp, ← Complex.exp_add]
    congr 1
    ring
theorem tubeOpIsExpProduct_holds (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hcar : σ.planeMeasure.IsCarriedBy wedge) {v : ℂ × ℂ} (hv : v ∈ closedForwardTube) :
    TubeOpIsExpProduct σ v := by
  obtain ⟨h₁, h₂⟩ := tubeOp_eq_ofBounded σ hC hJ hcar hv
  obtain ⟨e₁, e₂⟩ := expComplex_mul_lightCone σ hF hD (ζ := ForwardTube.lightConePlus v)
    (ζ' := ForwardTube.lightConeMinus v) hv.1 hv.2
  have hw := integralOp_halfLineExp_prod_eq σ hD hcar hv
  refine ⟨h₁, h₂, ?_, ?_⟩
  · rw [e₁, hw]
    exact h₁
  · rw [e₂, hw]
    exact h₁
theorem lightConeOpsFacts_holds (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hcar : σ.planeMeasure.IsCarriedBy wedge) : LightConeOpsFacts σ := by
  obtain ⟨hR, hcomm⟩ := (hF σ.space).2.2.2.2.2.1 2 univ σ.planeMeasure univ_nonempty
  obtain ⟨-, hB, hA, -, -, -, hRe, -⟩ := hD σ.space 2 univ σ.planeMeasure
  have mp := measurable_lightConePlusCoord
  have mm := measurable_lightConeMinusCoord
  have rp : IsDiagonalized σ.lightConeOpPlus := (hR _ mp).1
  have rm : IsDiagonalized σ.lightConeOpMinus := (hR _ mm).1
  have hSA := fun A => ((hC.1 σ.space).2.2.2.2.1 A).1
  have nn : ∀ g : EPlanePoints → ℝ, Measurable g → (∀ y ∈ wedge.1, 0 ≤ g y) →
      OperatorTransport.IsNonnegUnbounded (realSpectralIntegral σ.planeMeasure g) :=
    fun g hg hpos => hRe.isNonnegative _ wedge (Complex.measurable_ofReal.comp hg)
      (fun _ => Complex.ofReal_im _) hcar (fun y hy => Complex.zero_le_real.2 (hpos y hy))
  have np : OperatorTransport.IsNonnegUnbounded σ.lightConeOpPlus :=
    nn _ mp fun y hy => by
      rw [wedge_eq_lightCone] at hy
      exact hy.1
  have nm : OperatorTransport.IsNonnegUnbounded σ.lightConeOpMinus :=
    nn _ mm fun y hy => by
      rw [wedge_eq_lightCone] at hy
      exact hy.2
  have hIH : IsSpectralIntegralOf σ.recon.ham σ.planeMeasure complexEnergy :=
    isSpectralIntegralOf_of_eq hA measurable_complexEnergy (ham_eq_spectralIntegral σ hC hJ)
  have hIP : IsSpectralIntegralOf (σ.recon.mom 0) σ.planeMeasure complexMomentum :=
    isSpectralIntegralOf_of_eq hA measurable_complexMomentum (mom_eq_spectralIntegral σ hC hJ)
  have fam : ∀ A : UnboundedOp σ.space, IsDiagonalized A →
      OperatorTransport.IsNonnegUnbounded A → IsContractiveHolSemigroup A := fun A h₁ h₂ => by
    obtain ⟨a, b, -, -, -, -, d⟩ := (hF σ.space).2.2.2.1 A h₁ h₂
    exact ⟨a, b, d⟩
  refine ⟨rp, rm, hSA _ rp, hSA _ rm, hcomm _ _ mp mm, np, nm, fun ψ hH hP => ⟨?_, ?_⟩,
    fun ζ hζ ζ' hζ' => ?_, fam _ rp np, fam _ rm nm⟩
  · obtain ⟨h, e⟩ := realSpectralIntegral_linearCombo hB hA (1 / 2) (-1 / 2) hIH hIP mp
      (fun p => by
        simp only [lightConePlus, complexEnergy, complexMomentum]
        push_cast
        ring)
      (fun p => by
        simp only [lightConePlus]
        rw [abs_le]
        constructor <;>
          linarith [le_abs_self (p.1 0), neg_abs_le (p.1 0), le_abs_self (p.1 1),
            neg_abs_le (p.1 1), abs_nonneg (p.1 0), abs_nonneg (p.1 1)])
      ψ hH hP
    exact ⟨h, e.trans (by module)⟩
  · obtain ⟨h, e⟩ := realSpectralIntegral_linearCombo hB hA (1 / 2) (1 / 2) hIH hIP mm
      (fun p => by
        simp only [lightConeMinus, complexEnergy, complexMomentum]
        push_cast
        ring)
      (fun p => by
        simp only [lightConeMinus]
        rw [abs_le]
        constructor <;>
          linarith [le_abs_self (p.1 0), neg_abs_le (p.1 0), le_abs_self (p.1 1),
            neg_abs_le (p.1 1), abs_nonneg (p.1 0), abs_nonneg (p.1 1)])
      ψ hH hP
    exact ⟨h, e.trans (by module)⟩
  · obtain ⟨e₁, e₂⟩ := expComplex_mul_lightCone σ hF hD hζ hζ'
    exact e₁.trans e₂.symm
theorem tubeOpIsPyramidIntegral_holds (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hL : ReconstructionMeasureOperatorFacts)
    (h3 : EuclidFunctionalWithRecon.ConeForms.Holds)
    (hcone : σ.ConeCondition) (hcar : σ.planeMeasure.IsCarriedBy wedge) {v : ℂ × ℂ}
    (hv : v ∈ closedForwardTube) : TubeOpIsPyramidIntegral σ v := by
  refine ⟨?_, fun p => ?_⟩
  · obtain ⟨h12, h23, h⟩ := h3 σ
    have hj := h12.1 hcone
    have hc := h23.1 hj
    obtain ⟨hfun, -⟩ := h hcone hj hc
    have hκ : ∀ p : EMPoints, p ∈ pyramid.1 → energyMomentumPlane p ∈ wedge.1 :=
      fun p hp => hp 0
    let Ψ : pyramid.1 → ℂ := fun p => Complex.exp (planeExponent v p.1)
    have hmΨ : Measurable Ψ :=
      (measurable_planeExpKernel v).comp
        (measurable_energyMomentumPlane.comp measurable_subtype_coe)
    have hΨ : ∀ p, ‖Ψ p‖ ≤ 1 := fun p => by
      change ‖planeExpKernel v (energyMomentumPlane p.1)‖ ≤ 1
      exact norm_planeExpKernel_le_one hv (hκ _ p.2)
    have hfb := (hfun Ψ hmΨ ⟨1, hΨ⟩).1
    have hΦ : ∀ p : wedge.1, ‖planeExpKernel v p.1‖ ≤ 1 :=
      fun p => norm_planeExpKernel_le_one hv p.2
    let f : EPlanePoints → ℂ := zeroExtend wedge.1 fun p => planeExpKernel v p.1
    have mf : Measurable f := measurable_zeroExtend wedge.2
      ((measurable_planeExpKernel v).comp measurable_subtype_coe)
    have bf : ∀ y, ‖f y‖ ≤ 1 := norm_zeroExtend_le hΦ
    have hpl := (hL c S σ).1.planeIntegralOp_eq f mf ⟨1, bf⟩
    have hB4 := (hD σ.space 4 univ σ.jointMeasure).2.1
    have heq : σ.wedgeIntegralOp v = σ.pyramidCalc Ψ := by
      refine hpl.trans (hB4.congr _ _ pyramid (mf.comp measurable_energyMomentumPlane)
        ⟨1, fun y => bf _⟩ (measurable_zeroExtend pyramid.2 hmΨ)
        ⟨1, norm_zeroExtend_le hΨ⟩ hc fun y hy => ?_)
      have a₁ : f (energyMomentumPlane y) = planeExpKernel v (energyMomentumPlane y) :=
        zeroExtend_of_mem _ (hκ y hy)
      change f (energyMomentumPlane y) = _
      rw [a₁, zeroExtend_of_mem _ hy]
      rfl
    have hb := (tubeOp_eq_ofBounded σ hC hJ hcar hv).1
    rw [hb, heq, ← hfb]
    rfl
  · simp only [planeExponent, ForwardTube.lightConePlus, ForwardTube.lightConeMinus]
    push_cast
    ring
end Reconstruction
theorem holds (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts)
    (hJ : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hL : ReconstructionMeasureOperatorFacts)
    (h3 : EuclidFunctionalWithRecon.ConeForms.Holds) : Holds := by
  intro c S σ v hv
  have hcarOf : σ.ConeCondition → σ.planeMeasure.IsCarriedBy wedge :=
    (coneConditionIffOffWedgeNull_holds σ hL).1
  exact ⟨planeMeasureIsPushforward_holds σ hL, wedgeInLightConeCoords_holds,
    coneConditionIffOffWedgeNull_holds σ hL,
    fun hcone => ⟨tubeOpIsExpProduct_holds σ hC hF hJ hD (hcarOf hcone) hv,
      lightConeOpsFacts_holds σ hC hF hJ hD (hcarOf hcone)⟩,
    fun hcone => tubeOpIsPyramidIntegral_holds σ hC hJ hD hL h3 hcone (hcarOf hcone) hv⟩
end YangMills.Construction.EuclideanFunctionals.TubeOperatorForms
