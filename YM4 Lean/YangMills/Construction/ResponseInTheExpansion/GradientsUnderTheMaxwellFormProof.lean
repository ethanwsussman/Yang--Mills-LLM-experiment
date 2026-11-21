import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartForm
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.LawByMomentsOfTheFlow.MaxwellFormOfTheBareLevelProof
import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellForm
import YangMills.Construction.RunningCouplingSlope.TheLengthsOfTheWholeChainAreALocalFamilyProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages FrameTransfer LumpContours ColdStepAtMirrorFrames TorusFields WeightedResponses
namespace ResponseInTheExpansion
namespace MaxwellGradients
section Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
private theorem iteratedFDeriv_two_comp_clm {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (ι : G →L[ℝ] E) (m : Fin 2 → G) :
    iteratedFDeriv ℝ 2 (fun s => Φ (ι s)) 0 m = fderiv ℝ (fderiv ℝ Φ) 0 (ι (m 0)) (ι (m 1)) := by apply _root_.YangMills.SharedProofs.p5330 <;> assumption
private theorem hessian_apply_invariant_dir {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (g : E)
    (hg : ∀ (σ : E) (t : ℝ), Φ (σ + t • g) = Φ σ) (A : E) :
    fderiv ℝ (fderiv ℝ Φ) 0 g A = 0 := by
  have hsym : IsSymmSndFDerivAt ℝ Φ 0 := h.isSymmSndFDerivAt (by simp)
  rw [hsym.eq g A]
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ σ in 𝓝 (0 : E), DifferentiableAt ℝ Φ σ :=
    (h.eventually (by simp)).mono fun σ hσ => hσ.differentiableAt (by norm_num)
  have h0 : (fun σ => fderiv ℝ Φ σ g) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with σ hσ
    have hline : HasDerivAt (fun t : ℝ => σ + t • g) g 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add σ
    have hf : HasFDerivAt Φ (fderiv ℝ Φ σ) ((fun t : ℝ => σ + t • g) 0) := by
      simpa using hσ.hasFDerivAt
    have h1 : HasDerivAt (Φ ∘ fun t : ℝ => σ + t • g) (fderiv ℝ Φ σ g) 0 :=
      hf.comp_hasDerivAt 0 hline
    have h2 : (Φ ∘ fun t : ℝ => σ + t • g) = fun _ => Φ σ := funext fun t => hg σ t
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const _ _)
  have h3 : HasFDerivAt (fun σ => fderiv ℝ Φ σ g)
      ((ContinuousLinearMap.apply ℝ ℝ g).comp (fderiv ℝ (fderiv ℝ Φ) 0)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ g).hasFDerivAt.comp 0 hd.hasFDerivAt
  have h4 : HasFDerivAt (fun σ => fderiv ℝ Φ σ g) (0 : E →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq h0
  have h5 := h3.unique h4
  have h6 := congrArg (fun f : E →L[ℝ] ℝ => f A) h5
  simpa using h6
private theorem tendsto_div_sq_of_hasDerivAt {ψ ψ' : ℝ → ℝ} {c : ℝ} (h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt ψ (ψ' τ) τ)
    (h0 : ψ 0 = 0) (h0' : ψ' 0 = 0) (h2 : HasDerivAt ψ' c 0) :
    Tendsto (fun τ => ψ τ / τ ^ 2) (𝓝[≠] 0) (𝓝 (c / 2)) := by apply _root_.YangMills.SharedProofs.p94778 <;> assumption
private theorem tendsto_min_one_sub_cos_div_sq (κ m : ℝ) (hm : 0 < m) :
    Tendsto (fun τ : ℝ => min (2 * (1 - Real.cos (τ * κ))) m / τ ^ 2) (𝓝[≠] 0) (𝓝 (κ ^ 2)) := by
  have h1 : Tendsto (fun τ : ℝ => 2 * (1 - Real.cos (τ * κ)) / τ ^ 2) (𝓝[≠] 0) (𝓝 ((2 * κ ^ 2) / 2)) := by
    refine tendsto_div_sq_of_hasDerivAt (ψ' := fun τ => 2 * (κ * Real.sin (τ * κ))) (Eventually.of_forall fun τ => ?_)
      (by simp) (by simp) ?_
    · have h := ((hasDerivAt_id τ).mul_const κ).cos
      have h2 := (h.const_sub 1).const_mul 2
      refine h2.congr_deriv ?_
      simp only [id]
      ring
    · have h := ((hasDerivAt_id (0 : ℝ)).mul_const κ).sin
      have h2 := (h.const_mul κ).const_mul 2
      refine h2.congr_deriv ?_
      simp
      ring
  have e : (2 * κ ^ 2) / 2 = κ ^ 2 := by ring
  rw [e] at h1
  refine h1.congr' ?_
  have hcont : Continuous fun τ : ℝ => 2 * (1 - Real.cos (τ * κ)) := by fun_prop
  have h0 := hcont.tendsto 0
  simp only [zero_mul, Real.cos_zero, sub_self, mul_zero] at h0
  have hlt : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), 2 * (1 - Real.cos (τ * κ)) < m :=
    (h0.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hm)
  filter_upwards [hlt] with τ hτ
  rw [min_eq_left hτ.le]
private theorem hessian_lower_bound {Φ : E → ℝ} (h : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (hnn : ∀ σ, 0 ≤ Φ σ)
    (A : E) {ι : Type*} (P : Finset ι) (κ : ι → ℝ) (c m : ℝ) (hm : 0 < m)
    (hc : ∀ τ : ℝ, c * ∑ p ∈ P, min (2 * (1 - Real.cos (τ * κ p))) m ≤ Φ (τ • A)) :
    2 * c * ∑ p ∈ P, κ p ^ 2 ≤ fderiv ℝ (fderiv ℝ Φ) 0 A A := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ σ in 𝓝 (0 : E), DifferentiableAt ℝ Φ σ :=
    (h.eventually (by simp)).mono fun σ hσ => hσ.differentiableAt (by norm_num)
  have hmin : IsLocalMin Φ 0 := Eventually.of_forall fun σ => by rw [h0]; exact hnn σ
  have hz : fderiv ℝ Φ 0 = 0 := hmin.fderiv_eq_zero
  have hline : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => t • A) A τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const A
  have hcl : Continuous fun t : ℝ => t • A := by fun_prop
  have h1 : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt (fun t : ℝ => Φ (t • A)) (fderiv ℝ Φ (τ • A) A) τ := by
    have : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ Φ (τ • A) := by
      have h00 : (fun t : ℝ => t • A) 0 = 0 := by simp
      have := hcl.continuousAt (x := 0)
      exact this.eventually (by rw [h00]; exact hev)
    filter_upwards [this] with τ hτ
    exact hτ.hasFDerivAt.comp_hasDerivAt τ (hline τ)
  have h2 : HasDerivAt (fun τ : ℝ => fderiv ℝ Φ (τ • A) A) (fderiv ℝ (fderiv ℝ Φ) 0 A A) 0 := by
    have hf : HasFDerivAt (fun σ => fderiv ℝ Φ σ A)
        ((ContinuousLinearMap.apply ℝ ℝ A).comp (fderiv ℝ (fderiv ℝ Φ) 0)) ((fun t : ℝ => t • A) 0) := by
      have h00 : (fun t : ℝ => t • A) 0 = 0 := by simp
      rw [h00]
      exact (ContinuousLinearMap.apply ℝ ℝ A).hasFDerivAt.comp 0 hd.hasFDerivAt
    exact hf.comp_hasDerivAt 0 (hline 0)
  have hr := tendsto_div_sq_of_hasDerivAt h1 (by simp [h0]) (by simp [hz]) h2
  have hl : Tendsto (fun τ : ℝ => c * ∑ p ∈ P, min (2 * (1 - Real.cos (τ * κ p))) m / τ ^ 2) (𝓝[≠] 0)
      (𝓝 (c * ∑ p ∈ P, κ p ^ 2)) :=
    (tendsto_finsetSum P fun p _ => tendsto_min_one_sub_cos_div_sq (κ p) m hm).const_mul c
  have hle : c * ∑ p ∈ P, κ p ^ 2 ≤ fderiv ℝ (fderiv ℝ Φ) 0 A A / 2 := by
    refine le_of_tendsto_of_tendsto' hl hr fun τ => ?_
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hc τ) (sq_nonneg τ)
  linarith
private theorem bilinear_sum_basis {B : Type*} [Fintype B] [DecidableEq B]
    (D : (B → ℝ) →L[ℝ] (B → ℝ) →L[ℝ] ℝ) (A A' : B → ℝ) :
    ∑ b, ∑ b', A b * D (Pi.single b 1) (Pi.single b' 1) * A' b' = D A A' := by apply _root_.YangMills.SharedProofs.p21054 <;> assumption
end Calculus
section OneColour
private theorem expUnit_zero_eq : expUnit 0 = 1 := Subtype.ext (by simp [expUnit])
private theorem expUnit_generator_add (s t : ℝ) :
    expUnit ((s + t) • unitGenerator) = expUnit (s • unitGenerator) * expUnit (t • unitGenerator) := by apply _root_.YangMills.SharedProofs.p21518 <;> assumption
private theorem inv_expUnit_generator (s : ℝ) :
    (expUnit (s • unitGenerator))⁻¹ = expUnit ((-s) • unitGenerator) := by apply _root_.YangMills.SharedProofs.p1618 <;> assumption
private theorem re_expUnit_generator (s : ℝ) :
    ((expUnit (s • unitGenerator) : UnitQuaternion) : ℍ[ℝ]).re = Real.cos s := by apply _root_.YangMills.SharedProofs.p36152 <;> assumption
variable {n : ℕ}
private def abelianField (σ : TorusBond n → ℝ) : TorusField n := fun x i => expUnit (σ (x, i) • unitGenerator)
private theorem holonomy_abelianField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (abelianField σ) x μ ν = expUnit (curl σ (x, μ, ν) • unitGenerator) := by
  simp only [holonomy, abelianField, curl]
  rw [inv_expUnit_generator, inv_expUnit_generator, ← expUnit_generator_add, ← expUnit_generator_add,
    ← expUnit_generator_add]
  congr 2
private theorem curvature_sq_abelianField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    TorusFields.curvature (abelianField σ) x μ ν ^ 2 = 2 * (1 - Real.cos (curl σ (x, μ, ν))) := by
  rw [TorusFields.curvature, sq_norm_unitQuaternion_sub_one, holonomy_abelianField, re_expUnit_generator]
private theorem plaquetteEnergy_abelianField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    TorusFields.plaquetteEnergy (abelianField σ) x μ ν = 1 - Real.cos (curl σ (x, μ, ν)) := by
  rw [TorusFields.plaquetteEnergy, holonomy_abelianField, re_expUnit_generator]
private theorem curl_smul_eq (τ : ℝ) (A : TorusBond n → ℝ) (p : TorusPlaquette n) :
    curl (τ • A) p = τ * curl A p := by
  simp only [curl, Pi.smul_apply, smul_eq_mul]
  ring
abbrev _root_.YangMills.SharedProofs.p39240 := @curl_smul_eq
private theorem curl_add_gradient (σ : TorusBond n → ℝ) (t : ℝ) (φ : TorusSite n → ℝ) (p : TorusPlaquette n) :
    curl (σ + t • latticeGradient φ) p = curl σ p := by
  have e : p.1 + TorusFields.unitStep n p.2.1 + TorusFields.unitStep n p.2.2 =
      p.1 + TorusFields.unitStep n p.2.2 + TorusFields.unitStep n p.2.1 := by abel
  simp only [curl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, latticeGradient]
  rw [e]
  ring
private theorem abelianField_add_gradient (σ : TorusBond n → ℝ) (t : ℝ) (φ : TorusSite n → ℝ) :
    abelianField (σ + t • latticeGradient φ) =
      TorusFields.gaugeTransform (fun x => expUnit ((-(t * φ x)) • unitGenerator)) (abelianField σ) := by
  funext x i
  simp only [abelianField, TorusFields.gaugeTransform]
  rw [inv_expUnit_generator, ← expUnit_generator_add, ← expUnit_generator_add]
  congr 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, latticeGradient]
  ring
end OneColour
section MaxwellForm
variable {n : ℕ} [NeZero n]
private theorem abelianField_zero : abelianField (0 : TorusBond n → ℝ) = trivialField n := by
  funext x i
  simp [abelianField, trivialField, expUnit_zero_eq]
private theorem maxwellKernel_eq_hessian (a : ℝ) (L u : ℕ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianField σ)) 0)
    (b b' : TorusBond n) :
    maxwellKernel a L u b b' =
      fderiv ℝ (fderiv ℝ fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianField σ)) 0
        (Pi.single b 1) (Pi.single b' 1) := by
  let ι : (Fin 2 → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single b 1) +
      (ContinuousLinearMap.proj 1).smulRight (Pi.single b' 1)
  have e1 : ∀ (d : TorusBond n) (x : TorusSite n) (i : Fin 4) (s : ℝ),
      (if d = (x, i) then s • unitGenerator else (0 : imaginaryQuaternions)) =
        (s * (Pi.single d (1 : ℝ) : TorusBond n → ℝ) (x, i)) • unitGenerator := by
    intro d x i s
    by_cases h : d = (x, i)
    · rw [if_pos h, h]
      simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
      simp
  have hfun : (fun σ : Fin 2 → ℝ => actionAtLevel a L u Finset.univ
      (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField n))) =
      fun σ => (fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianField σ)) (ι σ) := by
    funext σ
    show actionAtLevel a L u Finset.univ _ = actionAtLevel a L u Finset.univ _
    congr 1
    funext x i
    have hs : (∑ l : Fin 2, if (![b, b'] : Fin 2 → TorusBond n) l = (x, i) then
        σ l • (![unitGenerator, unitGenerator] : Fin 2 → imaginaryQuaternions) l
        else 0) = (ι σ (x, i)) • unitGenerator := by
      rw [Fin.sum_univ_two]
      show (if b = (x, i) then σ 0 • unitGenerator else (0 : imaginaryQuaternions)) +
        (if b' = (x, i) then σ 1 • unitGenerator else (0 : imaginaryQuaternions)) = _
      rw [e1, e1, ← add_smul]
      simp [ι]
    show expUnit _ * 1 = expUnit _
    rw [mul_one, hs]
  unfold maxwellKernel mixedDeriv
  rw [hfun, iteratedFDeriv_two_comp_clm hC ι]
  simp [ι]
private theorem maxwell_bounds_of_action (a : ℝ) (L u : ℕ) (c m : ℝ) (hm : 0 < m)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianField σ)) 0)
    (h0 : actionAtLevel a L u Finset.univ (abelianField (0 : TorusBond n → ℝ)) = 0)
    (hnn : ∀ σ : TorusBond n → ℝ, 0 ≤ actionAtLevel a L u Finset.univ (abelianField σ))
    (hinv : ∀ (σ : TorusBond n → ℝ) (t : ℝ) (φ : TorusSite n → ℝ),
      actionAtLevel a L u Finset.univ (abelianField (σ + t • latticeGradient φ)) =
        actionAtLevel a L u Finset.univ (abelianField σ))
    (hco : ∀ σ : TorusBond n → ℝ, c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      min (TorusFields.curvature (abelianField σ) p.1 p.2.1 p.2.2 ^ 2) m ≤
        actionAtLevel a L u Finset.univ (abelianField σ)) :
    (∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ), maxwellForm a L u (latticeGradient φ) A = 0) ∧
      ∀ A : TorusBond n → ℝ, 2 * c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤
        maxwellForm a L u A A := by
  have hform : ∀ A A' : TorusBond n → ℝ, maxwellForm a L u A A' =
      fderiv ℝ (fderiv ℝ fun σ : TorusBond n → ℝ => actionAtLevel a L u Finset.univ (abelianField σ)) 0 A A' := by
    intro A A'
    rw [← bilinear_sum_basis]
    unfold maxwellForm
    simp only [maxwellKernel_eq_hessian a L u hC]
  refine ⟨fun φ A => ?_, fun A => ?_⟩
  · rw [hform]
    exact hessian_apply_invariant_dir hC (latticeGradient φ) (fun σ t => hinv σ t φ) A
  · rw [hform]
    refine hessian_lower_bound hC h0 hnn A _ (fun p => curl A p) c m hm fun τ => ?_
    have h := hco (τ • A)
    refine le_trans (le_of_eq ?_) h
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curvature_sq_abelianField]
    have e : curl (τ • A) (p.1, p.2.1, p.2.2) = τ * curl A p := curl_smul_eq τ A p
    rw [e]
end MaxwellForm
section Frames
variable {n : ℕ}
private theorem frameToTorus_add_unitStep {F : BlockFrame} {j m : ℕ} (hm : ∀ k, F.period j k = m) (y : F.Site j)
    (i : Fin 4) :
    frameToTorus m (y + BlockAverages.unitStep j i) = frameToTorus m y + TorusFields.unitStep m i := by
  have e : y + BlockAverages.unitStep j i = torusToFrame F j (frameToTorus m y + TorusFields.unitStep m i) := by
    rw [torusToFrame_add hm, torusToFrame_unitStep hm, torusToFrame_frameToTorus hm]
  rw [e, frameToTorus_torusToFrame hm]
private theorem readAtLevel_gaugeTransform {F : BlockFrame} {j m : ℕ} (hm : ∀ k, F.period j k = m)
    (g : TorusSite m → UnitQuaternion) (W : TorusField m) :
    readAtLevel F j (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun y => g (frameToTorus m y)) (readAtLevel F j W) := by
  funext y i
  show g (frameToTorus m y) * W (frameToTorus m y) i * (g (frameToTorus m y + TorusFields.unitStep m i))⁻¹ =
    g (frameToTorus m y) * W (frameToTorus m y) i * (g (frameToTorus m (y + BlockAverages.unitStep j i)))⁻¹
  rw [frameToTorus_add_unitStep hm]
private theorem readAtLevel_trivialField (F : BlockFrame) (j : ℕ) :
    readAtLevel F j (trivialField n) = flatField F j := rfl
private theorem plaquetteDefect_readAtLevel {F : BlockFrame} {j m : ℕ} (hm : ∀ k, F.period j k = m)
    (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W) (torusToFrame F j x, μ, ν) = TorusFields.curvature W x μ ν := by
  unfold plaquetteDefect TorusFields.curvature
  rw [plaquetteHolonomy_readAtLevel hm]
private theorem sum_cutPlaquettes_eq {F : BlockFrame} {j m : ℕ} [NeZero m] (hm : ∀ k, F.period j k = m)
    (f : F.Site j × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ cutPlaquettes (sitesOfTorus F j (Finset.univ : Finset (TorusSite m))), f p =
      ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), f (torusToFrame F j q.1, q.2.1, q.2.2) := by
  symm
  refine Finset.sum_bij (fun q _ => (torusToFrame F j q.1, q.2.1, q.2.2)) ?_ ?_ ?_ fun _ _ => rfl
  · intro q hq
    exact (torusToFrame_mem_cutPlaquettes hm Finset.univ q.1 q.2.1 q.2.2).2 hq
  · intro q _ q' _ h
    have h1 : q.1 = q'.1 := torusToFrame_injective hm (congrArg Prod.fst h)
    have h2 : q.2.1 = q'.2.1 := congrArg (fun z => z.2.1) h
    have h3 : q.2.2 = q'.2.2 := congrArg (fun z => z.2.2) h
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro p hp
    obtain ⟨y, μ, ν⟩ := p
    have e : torusToFrame F j (frameToTorus m y) = y := torusToFrame_frameToTorus hm y
    refine ⟨(frameToTorus m y, μ, ν), ?_, ?_⟩
    · refine (torusToFrame_mem_cutPlaquettes hm Finset.univ (frameToTorus m y) μ ν).1 ?_
      rw [e]
      exact hp
    · show (torusToFrame F j (frameToTorus m y), μ, ν) = (y, μ, ν)
      rw [e]
private theorem contDiffAt_of_bondAnalytic [NeZero n] {Eo : Type} [NormedAddCommGroup Eo] [NormedSpace ℝ Eo]
    [CompleteSpace Eo] {F : BlockFrame} (hm : ∀ k, F.period F.top k = n) (Gf : F.GaugeField F.top → Eo)
    (h : IsBondAnalyticAt Gf (flatField F F.top)) :
    ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => Gf (readAtLevel F F.top (abelianField σ))) 0 := by
  classical
  let e : Fin (Fintype.card (TorusBond n)) ≃ TorusBond n := (Fintype.equivFin (TorusBond n)).symm
  let c : Fin (Fintype.card (TorusBond n)) → F.Site F.top × Fin 4 := fun l => (torusToFrame F F.top (e l).1, (e l).2)
  let Xs : Fin (Fintype.card (TorusBond n)) → imaginaryQuaternions := fun _ => unitGenerator
  have hturn : ∀ σ' : Fin (Fintype.card (TorusBond n)) → ℝ,
      rotatedField (BlockAverages.bondSpread c Xs σ') (flatField F F.top) =
        readAtLevel F F.top (abelianField fun b => σ' (e.symm b)) := by
    intro σ'
    funext y i
    have hs : BlockAverages.bondSpread c Xs σ' y i = σ' (e.symm (frameToTorus n y, i)) • unitGenerator := by
      unfold BlockAverages.bondSpread
      rw [Finset.sum_eq_single (e.symm (frameToTorus n y, i))]
      · rw [if_pos]
        show (torusToFrame F F.top (e (e.symm (frameToTorus n y, i))).1, (e (e.symm (frameToTorus n y, i))).2) = (y, i)
        rw [Equiv.apply_symm_apply]
        exact Prod.ext (torusToFrame_frameToTorus hm y) rfl
      · intro l _ hl
        rw [if_neg]
        intro hc
        apply hl
        have h1 : torusToFrame F F.top (e l).1 = y := congrArg Prod.fst hc
        have h2 : (e l).2 = i := congrArg Prod.snd hc
        rw [Equiv.eq_symm_apply]
        refine Prod.ext ?_ h2
        rw [← h1, frameToTorus_torusToFrame hm]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    show expUnit (BlockAverages.bondSpread c Xs σ' y i) * 1 = expUnit (σ' (e.symm (frameToTorus n y, i)) • unitGenerator)
    rw [hs, mul_one]
  have hA := h _ c Xs
  let P : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (e l)
  have hA' : ContDiffAt ℝ 2 (fun σ' => Gf (rotatedField (BlockAverages.bondSpread c Xs σ') (flatField F F.top))) (P 0) := by
    rw [map_zero]
    exact hA.contDiffAt
  have hc := hA'.comp (0 : TorusBond n → ℝ) P.contDiff.contDiffAt
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
  show Gf (readAtLevel F F.top (abelianField σ)) = Gf (rotatedField (BlockAverages.bondSpread c Xs (P σ)) (flatField F F.top))
  rw [hturn]
  have e2 : (fun b => P σ (e.symm b)) = σ := by
    funext b
    show σ (e (e.symm b)) = σ b
    rw [Equiv.apply_symm_apply]
  rw [e2]
private theorem cold_minimizer_data {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible) {F : BlockFrame}
    (hFL : F.blockSide = Tb.side) (hamb : IsAdmissibleAmbient F)
    (S : Finset F.Cell) (hS : ∀ z, z ∈ S) (s : ℝ) (hs : 0 < s) (hsA : s ≤ Tb.σA) (V : F.GaugeField F.top)
    (hV : IsCold S F.top s V) :
    HasColdMinimizer Tb.coupling Tb.ρA (Tb.N 0) s S V ∧ HasRegularCellShares Tb.coupling Tb.δ₁ s Tb.N S V ∧
      HasRegularCoordinates Tb.coupling Tb.δ₁ Tb.ρA Tb.N S V := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hD.chain
  have hreg : IsOrthantRegular S 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => hS _⟩
  obtain ⟨h1, -, h3, h4, -⟩ := h F 1024 S hFL hamb le_rfl hreg s V hs hsA hV
  exact ⟨h1, h3, h4⟩
end Frames
section Levels
variable {n : ℕ} [NeZero n]
private theorem maxwell_bounds_upper {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : flatTopVanishingStatement) (hLeast : minimalChainExistenceStatement)
    (hGauge : MinimalActionGaugeCovariance) (hCost : WholeCellCostEqualsMinimalAction) (t : ℕ) (hn : 64 ≤ n) :
    (∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ),
        maxwellForm Tb.coupling Tb.side (t + 1) (latticeGradient φ) A = 0) ∧
      ∀ A : TorusBond n → ℝ, 2 * Tb.coercivity * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤
        maxwellForm Tb.coupling Tb.side (t + 1) A A := by
  have hm : ∀ k, (torusFrame Tb.side t n).period (torusFrame Tb.side t n).top k = n := TorusFrame.period_torusFrame
  have ha : 0 ≤ Tb.coupling := by linarith [hD.a_ge]
  have hodd : Odd (torusFrame Tb.side t n).blockSide := hD.L_odd
  have hσ : 0 < Tb.σA := by
    obtain ⟨-, -, -, -, -, h, -⟩ := hD.chain
    exact h
  have hall : ∀ z, z ∈ cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n)) := fun z =>
    Finset.mem_image.2 ⟨frameToTorus n z, Finset.mem_univ _, torusToFrame_frameToTorus hm z⟩
  have hamb : IsAdmissibleAmbient (torusFrame Tb.side t n) := Or.inr fun _ => hn
  have hfl := hFlat (torusFrame Tb.side t n) Tb.coupling
    (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n))) ha hodd
  have hcold := hfl.1 (torusFrame Tb.side t n).top Tb.σA hσ
  have hcut : ∀ V, cutEffectiveAction Tb.coupling (torusFrame Tb.side t n).top
      (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n))) V =
      minimalAction Tb.coupling (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n)))
        (torusFrame Tb.side t n).top V := by
    intro V
    have h := hCost (torusFrame Tb.side t n) Tb.coupling
      (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n))) hodd ha
    have e : cutBelow (torusFrame Tb.side t n).top
        (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n))) =
        cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n)) := by
      rw [h.1 _ le_rfl]
      ext y
      exact TorusFrame.mem_sitesOfCells_torusFrame _ y
    have h2 := h.2.1 _ le_rfl V
    rwa [e] at h2
  have hS : cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n)) =
      sitesOfTorus (torusFrame Tb.side t n) (torusFrame Tb.side t n).top (Finset.univ : Finset (TorusSite n)) := by
    ext y
    simp [mem_sitesOfTorus hm, hall y]
  refine maxwell_bounds_of_action Tb.coupling Tb.side (t + 1) Tb.coercivity ((Tb.side : ℝ) ^ (-4 : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
  · have hL : (0 : ℝ) < Tb.side := by exact_mod_cast hD.L_odd.pos
    positivity
  · exact contDiffAt_of_bondAnalytic hm _
      (cold_minimizer_data hD rfl hamb _ hall Tb.σA hσ le_rfl _ hcold).2.1.1
  · rw [abelianField_zero]
    exact hfl.2.1 (torusFrame Tb.side t n).top
  · intro σ
    exact (hLeast (torusFrame Tb.side t n) Tb.coupling _ ha).2.1 _ _
  · intro σ s φ
    rw [abelianField_add_gradient]
    show minimalAction Tb.coupling _ (torusFrame Tb.side t n).top
        (readAtLevel (torusFrame Tb.side t n) (torusFrame Tb.side t n).top (TorusFields.gaugeTransform _ _)) =
      minimalAction Tb.coupling _ (torusFrame Tb.side t n).top
        (readAtLevel (torusFrame Tb.side t n) (torusFrame Tb.side t n).top _)
    rw [readAtLevel_gaugeTransform hm]
    exact hGauge.1 _ _ _ _ hD.L_odd.pos le_rfl _ _
  · intro σ
    have h := (hD.coercive (torusFrame Tb.side t n) rfl hamb (torusFrame Tb.side t n).top le_rfl).2
      (cellsOfSites (torusFrame Tb.side t n) (Finset.univ : Finset (TorusSite n)))
      (readAtLevel (torusFrame Tb.side t n) (torusFrame Tb.side t n).top (abelianField σ))
    rw [hcut] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    rw [hS, sum_cutPlaquettes_eq hm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [plaquetteDefect_readAtLevel hm]
private theorem coercivity_le_half {cK a : ℝ} {L : ℕ} (hco : RenormalizationStepParameters.CoercivityBound cK a L) (ha : 0 ≤ a)
    (hodd : Odd L) (hBlock : SiteDecomposition) (hCost : WholeCellCostEqualsMinimalAction)
    (M : ℕ) [NeZero M] (hM : 64 ≤ M) : cK ≤ 1 / 2 := by
  have hL : 0 < L := hodd.pos
  have hm0 : ∀ k, (torusFrame L 0 M).period 0 k = M * L := by
    intro k
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have hmT : ∀ k, (torusFrame L 0 M).period (torusFrame L 0 M).top k = M := TorusFrame.period_torusFrame
  have hML : 64 ≤ M * L := le_trans hM (Nat.le_mul_of_pos_right M hL)
  have : NeZero (M * L) := ⟨by omega⟩
  have : Fact (1 < M * L) := ⟨by omega⟩
  have hall : ∀ z, z ∈ cellsOfSites (torusFrame L 0 M) (Finset.univ : Finset (TorusSite M)) := fun z =>
    Finset.mem_image.2 ⟨frameToTorus M z, Finset.mem_univ _, torusToFrame_frameToTorus hmT z⟩
  have hcost := hCost (torusFrame L 0 M) a (cellsOfSites (torusFrame L 0 M) (Finset.univ : Finset (TorusSite M))) hodd ha
  have hsite : sitesOfCells (cellsOfSites (torusFrame L 0 M) (Finset.univ : Finset (TorusSite M))) 0 =
      sitesOfTorus (torusFrame L 0 M) 0 (Finset.univ : Finset (TorusSite (M * L))) := by
    ext x
    simp only [mem_sitesOfTorus hm0, Finset.mem_univ, iff_true]
    have hb := (hBlock (torusFrame L 0 M) hodd fun _ => le_trans (by norm_num) hM).2.1 x
    have e : (torusFrame L 0 M).blockSide ^ ((torusFrame L 0 M).top - 0) = (torusFrame L 0 M).blockSide := by
      simp [BlockFrame.top, torusFrame]
    unfold sitesOfCells
    refine Finset.mem_biUnion.2 ⟨enclosingCell x, hall _, Finset.mem_image.2 ⟨cellOffset x, ?_, hb.1⟩⟩
    rw [e]
    exact hb.2
  have hineq : ∀ (A : TorusBond (M * L) → ℝ) (τ : ℝ),
      cK * ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (M * L))),
          min (2 * (1 - Real.cos (τ * curl A q))) ((L : ℝ) ^ (-4 : ℤ)) ≤
        ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (M * L))),
          (1 / 2) * min (2 * (1 - Real.cos (τ * curl A q))) 5 := by
    intro A τ
    have h := (hco (torusFrame L 0 M) rfl (Or.inr fun _ => hM) 0 (Nat.zero_le _)).2
      (cutBelow 0 (cellsOfSites (torusFrame L 0 M) (Finset.univ : Finset (TorusSite M))))
      (readAtLevel (torusFrame L 0 M) 0 (abelianField (τ • A)))
    rw [hcost.2.1 0 (Nat.zero_le _)] at h
    rw [hcost.1 0 (Nat.zero_le _), hsite, sum_cutPlaquettes_eq hm0] at h
    have hr : minimalAction a (cellsOfSites (torusFrame L 0 M) (Finset.univ : Finset (TorusSite M))) 0
        (readAtLevel (torusFrame L 0 M) 0 (abelianField (τ • A))) =
        ∑ p ∈ cutPlaquettes (sitesOfTorus (torusFrame L 0 M) 0 (Finset.univ : Finset (TorusSite (M * L)))),
          (1 - ((plaquetteHolonomy (readAtLevel (torusFrame L 0 M) 0 (abelianField (τ • A))) p : UnitQuaternion) :
            ℍ[ℝ]).re) := by
      rw [← hsite]
      rfl
    rw [hr, sum_cutPlaquettes_eq hm0] at h
    refine le_trans (le_trans (le_of_eq ?_) h) (le_of_eq ?_)
    · congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [plaquetteDefect_readAtLevel hm0, curvature_sq_abelianField]
      have e : curl (τ • A) (q.1, q.2.1, q.2.2) = τ * curl A q := curl_smul_eq τ A q
      rw [e]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [plaquetteHolonomy_readAtLevel hm0, holonomy_abelianField, re_expUnit_generator]
      have e : curl (τ • A) (q.1, q.2.1, q.2.2) = τ * curl A q := curl_smul_eq τ A q
      rw [e, min_eq_left (by nlinarith [Real.neg_one_le_cos (τ * curl A q)])]
      ring
  let b0 : TorusBond (M * L) := (0, 0)
  let A : TorusBond (M * L) → ℝ := Pi.single b0 1
  let q0 : TorusPlaquette (M * L) := (0, 0, 1)
  have hq0 : q0 ∈ plaquettesIn (Finset.univ : Finset (TorusSite (M * L))) := by
    simp [plaquettesIn, q0]
  have hne1 : ((0 : TorusSite (M * L)) + TorusFields.unitStep (M * L) 0, (1 : Fin 4)) ≠ b0 := by
    intro h
    have := congrArg Prod.snd h
    simp [b0] at this
  have hne2 : ((0 : TorusSite (M * L)) + TorusFields.unitStep (M * L) 1, (0 : Fin 4)) ≠ b0 := by
    intro h
    have h1 := congrFun (congrArg Prod.fst h) 1
    simp [b0, TorusFields.unitStep] at h1
  have hne3 : ((0 : TorusSite (M * L)), (1 : Fin 4)) ≠ b0 := by
    intro h
    have := congrArg Prod.snd h
    simp [b0] at this
  have hk : curl A q0 = 1 := by
    show A ((0 : TorusSite (M * L)), (0 : Fin 4)) + A ((0 : TorusSite (M * L)) + TorusFields.unitStep (M * L) 0, (1 : Fin 4)) -
      A ((0 : TorusSite (M * L)) + TorusFields.unitStep (M * L) 1, (0 : Fin 4)) - A ((0 : TorusSite (M * L)), (1 : Fin 4)) = 1
    have e0 : A ((0 : TorusSite (M * L)), (0 : Fin 4)) = 1 := Pi.single_eq_same b0 1
    rw [e0]
    simp only [A]
    rw [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2, Pi.single_eq_of_ne hne3]
    ring
  have hpos : 0 < ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (M * L))), curl A q ^ 2 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun q _ => sq_nonneg (curl A q)) hq0)
    rw [hk]
    norm_num
  have hLp : (0 : ℝ) < (L : ℝ) ^ (-4 : ℤ) := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hl := (tendsto_finsetSum (plaquettesIn (Finset.univ : Finset (TorusSite (M * L)))) fun q _ =>
    tendsto_min_one_sub_cos_div_sq (curl A q) _ hLp).const_mul cK
  have hr := tendsto_finsetSum (plaquettesIn (Finset.univ : Finset (TorusSite (M * L)))) fun q _ =>
    (tendsto_min_one_sub_cos_div_sq (curl A q) 5 (by norm_num)).const_mul (1 / 2 : ℝ)
  have hle := le_of_tendsto_of_tendsto' hl hr fun τ => by
    have h := div_le_div_of_nonneg_right (hineq A τ) (sq_nonneg τ)
    rw [mul_div_assoc, Finset.sum_div, Finset.sum_div] at h
    refine le_trans h (le_of_eq ?_)
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [← Finset.mul_sum] at hle
  have := le_of_mul_le_mul_right hle hpos
  exact this
private theorem maxwell_bounds_zero (a : ℝ) (L : ℕ) (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1 / 2) :
    (∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ), maxwellForm a L 0 (latticeGradient φ) A = 0) ∧
      ∀ A : TorusBond n → ℝ, 2 * c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤
        maxwellForm a L 0 A A := by
  have hact : ∀ σ : TorusBond n → ℝ, actionAtLevel a L 0 Finset.univ (abelianField σ) =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), (1 - Real.cos (curl σ p)) := fun σ =>
    Finset.sum_congr rfl fun p _ => plaquetteEnergy_abelianField σ p.1 p.2.1 p.2.2
  refine maxwell_bounds_of_action a L 0 c 1 one_pos ?_ ?_ ?_ ?_ ?_
  · have hcd : ContDiff ℝ 2 fun σ : TorusBond n → ℝ =>
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), (1 - Real.cos (curl σ p)) := by
      refine ContDiff.sum fun p _ => contDiff_const.sub (Real.contDiff_cos.comp ?_)
      unfold curl
      exact (((contDiff_apply ℝ ℝ _).add (contDiff_apply ℝ ℝ _)).sub (contDiff_apply ℝ ℝ _)).sub
        (contDiff_apply ℝ ℝ _)
    have e : (fun σ : TorusBond n → ℝ => actionAtLevel a L 0 Finset.univ (abelianField σ)) = _ := funext hact
    rw [e]
    exact hcd.contDiffAt
  · rw [hact]
    simp [curl]
  · intro σ
    rw [hact]
    exact Finset.sum_nonneg fun p _ => sub_nonneg.2 (Real.cos_le_one _)
  · intro σ t φ
    rw [hact, hact]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curl_add_gradient]
  · intro σ
    rw [hact, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [curvature_sq_abelianField]
    have e : curl σ (p.1, p.2.1, p.2.2) = curl σ p := rfl
    rw [e]
    have h1 : 0 ≤ 1 - Real.cos (curl σ p) := sub_nonneg.2 (Real.cos_le_one _)
    calc c * min (2 * (1 - Real.cos (curl σ p))) 1 ≤ c * (2 * (1 - Real.cos (curl σ p))) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le
      _ ≤ 1 - Real.cos (curl σ p) := by nlinarith
end Levels
section Response
variable {n : ℕ} [NeZero n]
private theorem mem_finiteCells {F : BlockFrame} (hm : ∀ k, F.period F.top k = n) (z : F.Cell) : z ∈ finiteCells F := by
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      rw [hm i]
      exact inferInstance
    exact Pi.finite
  unfold finiteCells
  rw [dif_pos hfin]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
private theorem minimizingChart_flat {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) {F : BlockFrame} (hFL : F.blockSide = Tb.side)
    (hm : ∀ k, F.period F.top k = n) (hside : ∀ i, 64 ≤ F.extent i) :
    IsMinimizingChart Tb.coupling (finiteCells F) (flatField F F.top) Tb.ρA fun _ _ => 0 := by
  have ha : 0 ≤ Tb.coupling := by linarith [hD.a_ge]
  have hodd : Odd F.blockSide := hFL ▸ hD.L_odd
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := hD.chain
  have hall := mem_finiteCells hm
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => le_trans (by norm_num) (hside i)
  have hfl := hFlat F Tb.coupling (finiteCells F) ha hodd
  have hch : ∀ s, 0 < s → s ≤ Tb.σA →
      HasColdMinimizer Tb.coupling Tb.ρA (Tb.N 0) s (finiteCells F) (flatField F F.top) :=
    fun s hs hsA => (cold_minimizer_data hD hFL (Or.inr hside) _ hall s hs hsA _ (hfl.1 F.top s hs)).1
  have hwide : ∀ (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (r : ℝ),
      IsMinimizingChart Tb.coupling (finiteCells F) (flatField F F.top) (min Tb.ρA r) w →
      IsMinimizingChart Tb.coupling (finiteCells F) (flatField F F.top) Tb.ρA w := fun w r h =>
    ⟨h.1, fun b hb => le_trans (h.2.1 b hb) (min_le_left _ _), h.2.2⟩
  obtain ⟨w, hw, -, -⟩ := hch Tb.σA hσ le_rfl
  have hw' := hwide w _ hw
  have huniq := (hOne F Tb.coupling Tb.ρA (Tb.N 0) Tb.σA (flatField F F.top) w hodd h2 hρ1
    (hch Tb.σA hσ le_rfl) hw').1
  have hsmall : ∀ b ∈ chordBonds (finiteCells F), ∀ s, 0 < s → s ≤ Tb.σA → ‖w b.1 b.2‖ ≤ Tb.N 0 * s := by
    intro b hb s hs hsA
    obtain ⟨ws, hws, -, -⟩ := hch s hs hsA
    have e := huniq ws (hwide ws _ hws)
    rw [← e]
    exact le_trans (hws.2.1 b hb) (min_le_right _ _)
  have hz : w = fun _ _ => 0 := by
    funext x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
    · by_contra hne
      have hp : 0 < ‖w x i‖ := norm_pos_iff.2 hne
      have hN0 := hN 0
      have hs : 0 < min Tb.σA (‖w x i‖ / (2 * Tb.N 0)) := lt_min hσ (by positivity)
      have h1 := hsmall (x, i) hb _ hs (min_le_left _ _)
      have h3 : Tb.N 0 * min Tb.σA (‖w x i‖ / (2 * Tb.N 0)) ≤ Tb.N 0 * (‖w x i‖ / (2 * Tb.N 0)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hN0.le
      have h4 : Tb.N 0 * (‖w x i‖ / (2 * Tb.N 0)) = ‖w x i‖ / 2 := by
        field_simp
      have h5 : ‖w x i‖ ≤ ‖w x i‖ / 2 := le_trans h1 (by rw [← h4]; exact h3)
      linarith
    · exact hw.1 (x, i) hb
  rw [← hz]
  exact hw'
private theorem minimizingCoordinates_gauge {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) (hGauge : MinimalActionGaugeCovariance)
    {F : BlockFrame} (hFL : F.blockSide = Tb.side)
    (hm : ∀ k, F.period F.top k = n) (hside : ∀ i, 64 ≤ F.extent i) (γ : F.Cell → UnitQuaternion)
    (hcold : IsCold (finiteCells F) F.top Tb.σA (BlockAverages.gaugeTransform γ (flatField F F.top))) :
    minimizingCoordinates Tb.coupling (finiteCells F) (BlockAverages.gaugeTransform γ (flatField F F.top)) Tb.ρA =
      fun _ _ => 0 := by
  have hodd : Odd F.blockSide := hFL ▸ hD.L_odd
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := hD.chain
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => le_trans (by norm_num) (hside i)
  have hl := hGauge.2 F Tb.coupling Tb.ρA (flatField F F.top) (fun _ _ => 0) γ hodd h2
    (minimizingChart_flat hD hFlat hOne hFL hm hside)
  simp only [map_zero] at hl
  have h1 := (cold_minimizer_data hD hFL (Or.inr hside) _ (mem_finiteCells hm) Tb.σA hσ le_rfl _ hcold).1
  have huniq := (hOne F Tb.coupling Tb.ρA (Tb.N 0) Tb.σA _ _ hodd h2 hρ1 h1 hl).1
  have hex : ∃ w, IsMinimizingChart Tb.coupling (finiteCells F)
      (BlockAverages.gaugeTransform γ (flatField F F.top)) Tb.ρA w := ⟨_, hl⟩
  unfold minimizingCoordinates
  rw [dif_pos hex]
  exact huniq _ hex.choose_spec
private theorem abelian_gradient_eq_gauge {F : BlockFrame} (hm : ∀ k, F.period F.top k = n) (t : ℝ)
    (φ : TorusSite n → ℝ) :
    readAtLevel F F.top (abelianField (t • latticeGradient φ)) =
      BlockAverages.gaugeTransform (fun y => expUnit ((-(t * φ (frameToTorus n y))) • unitGenerator))
        (flatField F F.top) := by
  have h := abelianField_add_gradient (0 : TorusBond n → ℝ) t φ
  rw [zero_add, abelianField_zero] at h
  rw [h, readAtLevel_gaugeTransform hm, readAtLevel_trivialField]
private theorem abelian_gradient_isCold {F : BlockFrame} (hm : ∀ k, F.period F.top k = n) (t : ℝ)
    (φ : TorusSite n → ℝ) (S : Finset F.Cell) (s : ℝ) (hs : 0 < s) :
    IsCold S F.top s (readAtLevel F F.top (abelianField (t • latticeGradient φ))) := by
  intro p _
  obtain ⟨y, μ, ν⟩ := p
  have e : torusToFrame F F.top (frameToTorus n y) = y := torusToFrame_frameToTorus hm y
  rw [← e, plaquetteDefect_readAtLevel hm]
  have hc : curl (t • latticeGradient φ) (frameToTorus n y, μ, ν) = 0 := by
    have h := curl_add_gradient (0 : TorusBond n → ℝ) t φ (frameToTorus n y, μ, ν)
    rw [zero_add] at h
    rw [h]
    simp [curl]
  have h2 := curvature_sq_abelianField (t • latticeGradient φ) (frameToTorus n y) μ ν
  rw [hc] at h2
  have h3 : TorusFields.curvature (abelianField (t • latticeGradient φ)) (frameToTorus n y) μ ν = 0 := by
    have : TorusFields.curvature (abelianField (t • latticeGradient φ)) (frameToTorus n y) μ ν ^ 2 = 0 := by
      rw [h2]
      simp
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  rw [h3]
  exact hs
private theorem bondCoordinate_of_not_mem (a ρ : ℝ) {F : BlockFrame} (S : Finset F.Cell)
    (b : F.Site F.depth × Fin 4) (hb : b ∉ chordBonds S) (V : F.GaugeField F.top) :
    minimizingBondCoordinate a ρ S b V = 0 := by
  unfold minimizingBondCoordinate minimizingCoordinates
  by_cases h : ∃ w, IsMinimizingChart a S V ρ w
  · rw [dif_pos h]
    exact h.choose_spec.1 b hb
  · rw [dif_neg h]
private theorem coordinate_deriv_gradient_sum {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) (hGauge : MinimalActionGaugeCovariance)
    {F : BlockFrame} (hFL : F.blockSide = Tb.side)
    (hm : ∀ k, F.period F.top k = n) (hside : ∀ i, 64 ≤ F.extent i) (φ : TorusSite n → ℝ)
    (b : F.Site F.depth × Fin 4) :
    ∑ c : TorusBond n, (- (((bondDeriv (torusCoordinate Tb.coupling Tb.ρA b) (uniformField F F.top)
      ![(torusToFrame F F.top c.1, c.2)] ![unitGenerator] : imaginaryQuaternions) : ℍ[ℝ]) *
        (unitGenerator : ℍ[ℝ])).re) * latticeGradient φ c = 0 := by
  classical
  have : FiniteDimensional ℝ imaginaryQuaternions := FiniteDimensional.finiteDimensional_submodule imaginaryQuaternions
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  have ha : 0 ≤ Tb.coupling := by linarith [hD.a_ge]
  have hodd : Odd F.blockSide := hFL ▸ hD.L_odd
  have hσ : 0 < Tb.σA := by
    obtain ⟨-, -, -, -, -, h, -⟩ := hD.chain
    exact h
  have hall := mem_finiteCells hm
  let Gf : (TorusBond n → ℝ) → imaginaryQuaternions := fun σ =>
    torusCoordinate Tb.coupling Tb.ρA b (readAtLevel F F.top (abelianField σ))
  have hdiff : DifferentiableAt ℝ Gf 0 := by
    by_cases hb : b ∈ chordBonds (finiteCells F)
    · have hAn := ((cold_minimizer_data hD hFL (Or.inr hside) _ hall Tb.σA hσ le_rfl _
        ((hFlat F Tb.coupling (finiteCells F) ha hodd).1 F.top Tb.σA hσ)).2.2 b hb).1
      exact (contDiffAt_of_bondAnalytic hm _ hAn).differentiableAt (by norm_num)
    · have e : Gf = fun _ => 0 := funext fun σ => bondCoordinate_of_not_mem _ _ _ b hb _
      rw [e]
      exact differentiableAt_const _
  have hzero : ∀ t : ℝ, Gf (t • latticeGradient φ) = 0 := by
    intro t
    show minimizingBondCoordinate Tb.coupling Tb.ρA (finiteCells F) b
      (readAtLevel F F.top (abelianField (t • latticeGradient φ))) = 0
    have hc := abelian_gradient_isCold hm t φ (finiteCells F) Tb.σA hσ
    rw [abelian_gradient_eq_gauge hm] at hc ⊢
    unfold minimizingBondCoordinate
    rw [minimizingCoordinates_gauge hD hFlat hOne hGauge hFL hm hside _ hc]
  have hfd : fderiv ℝ Gf 0 (latticeGradient φ) = 0 := by
    have hline : HasDerivAt (fun t : ℝ => t • latticeGradient φ) (latticeGradient φ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (latticeGradient φ)
    have hf : HasFDerivAt Gf (fderiv ℝ Gf 0) ((fun t : ℝ => t • latticeGradient φ) 0) := by
      simpa using hdiff.hasFDerivAt
    have h1 := hf.comp_hasDerivAt (0 : ℝ) hline
    have h2 : (Gf ∘ fun t : ℝ => t • latticeGradient φ) = fun _ => 0 := funext hzero
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const _ _)
  have hD1 : ∀ c : TorusBond n, bondDeriv (torusCoordinate Tb.coupling Tb.ρA b) (uniformField F F.top)
      ![(torusToFrame F F.top c.1, c.2)] ![unitGenerator] = fderiv ℝ Gf 0 (Pi.single c 1) := by
    intro c
    let ι : (Fin 1 → ℝ) →L[ℝ] (TorusBond n → ℝ) := (ContinuousLinearMap.proj 0).smulRight (Pi.single c 1)
    have hfun : (fun τ : Fin 1 → ℝ => torusCoordinate Tb.coupling Tb.ρA b
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![(torusToFrame F F.top c.1, c.2)] ![unitGenerator] τ)
          (uniformField F F.top))) = Gf ∘ ι := by
      funext τ
      show torusCoordinate Tb.coupling Tb.ρA b _ = torusCoordinate Tb.coupling Tb.ρA b _
      congr 1
      funext y k
      show expUnit (ColdStepAtMirrorFrames.bondSpread ![(torusToFrame F F.top c.1, c.2)] ![unitGenerator] τ y k) * 1 =
        expUnit ((ι τ (frameToTorus n y, k)) • unitGenerator)
      rw [mul_one]
      congr 1
      have hs : ColdStepAtMirrorFrames.bondSpread ![(torusToFrame F F.top c.1, c.2)] ![unitGenerator] τ y k =
          if (torusToFrame F F.top c.1, c.2) = (y, k) then τ 0 • unitGenerator
          else (0 : imaginaryQuaternions) := by
        unfold ColdStepAtMirrorFrames.bondSpread
        rw [Fin.sum_univ_one]
        rfl
      rw [hs]
      have hι : ι τ (frameToTorus n y, k) = τ 0 * (Pi.single c (1 : ℝ) : TorusBond n → ℝ) (frameToTorus n y, k) := by
        simp [ι]
      rw [hι]
      by_cases h : (torusToFrame F F.top c.1, c.2) = (y, k)
      · have h1 : torusToFrame F F.top c.1 = y := congrArg Prod.fst h
        have h2 : c.2 = k := congrArg Prod.snd h
        have h3 : (frameToTorus n y, k) = c := by
          rw [← h1, frameToTorus_torusToFrame hm, ← h2]
        rw [if_pos h, h3]
        simp
      · have h3 : (frameToTorus n y, k) ≠ c := by
          intro h4
          apply h
          rw [← h4]
          exact Prod.ext (torusToFrame_frameToTorus hm y) rfl
        rw [if_neg h, Pi.single_eq_of_ne h3]
        simp
    unfold bondDeriv
    rw [hfun, iteratedFDeriv_one_apply]
    have h0 : HasFDerivAt Gf (fderiv ℝ Gf 0) (ι 0) := by
      simpa using hdiff.hasFDerivAt
    have hcomp : HasFDerivAt (Gf ∘ ι) ((fderiv ℝ Gf 0).comp ι) 0 := h0.comp 0 ι.hasFDerivAt
    rw [hcomp.fderiv]
    simp [ι]
  let R : imaginaryQuaternions →ₗ[ℝ] ℝ :=
    { toFun := fun q => -(((q : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ])).re)
      map_add' := fun u v => by
        simp only [Submodule.coe_add, add_mul, Quaternion.re_add]
        ring
      map_smul' := fun r u => by
        simp
        ring }
  have hg : latticeGradient φ = ∑ c : TorusBond n, latticeGradient φ c • (Pi.single c (1 : ℝ) : TorusBond n → ℝ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : ∑ c : TorusBond n, R (fderiv ℝ Gf 0 (Pi.single c 1)) * latticeGradient φ c =
      R (fderiv ℝ Gf 0 (latticeGradient φ)) := by
    conv_rhs => rw [hg]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfd, map_zero] at hsum
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hsum
  rw [hD1]
  rfl
open Classical in
private theorem crossing_gradient_sum (hBlock : SiteDecomposition) {F : BlockFrame} (hodd : Odd F.blockSide)
    (h2 : ∀ i, 2 ≤ F.extent i) (hm : ∀ k, F.period F.top k = n) (φ : TorusSite n → ℝ) (x : F.Site F.depth)
    (i : Fin 4) :
    ∑ c : TorusBond n, (if IsCrossingBond (x, i) ∧ enclosingCell x = torusToFrame F F.top c.1 ∧ i = c.2 then (1 : ℝ)
      else 0) * latticeGradient φ c =
      φ (frameToTorus n (enclosingCell (x + BlockAverages.unitStep F.depth i))) - φ (frameToTorus n (enclosingCell x)) := by
  have hB := (hBlock F hodd h2).2.2.2 x i
  by_cases hx : IsCrossingBond (x, i)
  · have hnext : enclosingCell (x + BlockAverages.unitStep F.depth i) =
        enclosingCell x + BlockAverages.unitStep F.top i := hB.resolve_left hx
    rw [Finset.sum_eq_single (frameToTorus n (enclosingCell x), i)]
    · rw [if_pos ⟨hx, (torusToFrame_frameToTorus hm _).symm, rfl⟩, one_mul, hnext, frameToTorus_add_unitStep hm]
      rfl
    · intro c _ hc
      rw [if_neg, zero_mul]
      rintro ⟨-, h1, h3⟩
      apply hc
      refine Prod.ext ?_ h3.symm
      show c.1 = frameToTorus n (enclosingCell x)
      rw [h1, frameToTorus_torusToFrame hm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hs : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := not_not.1 hx
    rw [hs, sub_self]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg (fun h => hx h.1), zero_mul]
private theorem parentBlock_eq {L u : ℕ} (x' : TorusSite (n * L)) :
    TorusLumps.parentBlock L x' =
      frameToTorus n (enclosingCell (torusToFrame (torusFrame L u n) (torusFrame L u n).depth x')) := by
  have hm : ∀ k, (torusFrame L u n).period (torusFrame L u n).top k = n := TorusFrame.period_torusFrame
  have hmB : ∀ k, (torusFrame L u n).period (torusFrame L u n).depth k = n * L := by
    intro k
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have hnt : (torusFrame L u n).top - (torusFrame L u n).depth = 1 := by
    simp [BlockFrame.top, torusFrame]
  funext i
  have e1 : frameToTorus n (enclosingCell (torusToFrame (torusFrame L u n) (torusFrame L u n).depth x')) =
      siteOfInt fun k => (siteCoords (torusToFrame (torusFrame L u n) (torusFrame L u n).depth x') k +
        ((L : ℤ) ^ 1 - 1) / 2) / (L : ℤ) ^ 1 := by
    unfold enclosingCell
    rw [hnt, ← torusToFrame_siteOfInt hm, frameToTorus_torusToFrame hm]
    rfl
  rw [e1]
  have e2 : siteCoords (torusToFrame (torusFrame L u n) (torusFrame L u n).depth x') i = (x' i).cast :=
    intCast_cast_of_eq (hmB i).symm (x' i)
  show ((((x' i).cast + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) =
    (((siteCoords (torusToFrame (torusFrame L u n) (torusFrame L u n).depth x') i + ((L : ℤ) ^ 1 - 1) / 2) /
      (L : ℤ) ^ 1 : ℤ) : ZMod n)
  rw [e2, pow_one]
private theorem responseMap_gradient {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) (hGauge : MinimalActionGaugeCovariance)
    (hBlock : SiteDecomposition) (u : ℕ) (hn : 64 ≤ n) (φ : TorusSite n → ℝ) :
    responseMap Tb.coupling Tb.ρA Tb.side u (latticeGradient φ) =
      latticeGradient fun x => φ (TorusLumps.parentBlock Tb.side x) := by
  have hm : ∀ k, (torusFrame Tb.side u n).period (torusFrame Tb.side u n).top k = n := TorusFrame.period_torusFrame
  have hmB : ∀ k, (torusFrame Tb.side u n).period (torusFrame Tb.side u n).depth k = n * Tb.side := by
    intro k
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have hside : ∀ i, 64 ≤ (torusFrame Tb.side u n).extent i := fun _ => hn
  funext b
  have h1 := coordinate_deriv_gradient_sum hD hFlat hOne hGauge (F := torusFrame Tb.side u n) rfl hm hside φ
    (torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1, b.2)
  have h2 := crossing_gradient_sum hBlock (F := torusFrame Tb.side u n) hD.L_odd (fun _ => le_trans (by norm_num) hn)
    hm φ (torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1) b.2
  have hu : torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth
      (b.1 + TorusFields.unitStep (n * Tb.side) b.2) =
      torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1 +
        BlockAverages.unitStep (torusFrame Tb.side u n).depth b.2 := by
    rw [torusToFrame_add hmB, torusToFrame_unitStep hmB]
  show ∑ c : TorusBond n, responseKernel Tb.coupling Tb.ρA Tb.side u b c * latticeGradient φ c =
    φ (TorusLumps.parentBlock Tb.side (b.1 + TorusFields.unitStep (n * Tb.side) b.2)) -
      φ (TorusLumps.parentBlock Tb.side b.1)
  have hentry : ∀ c : TorusBond n, responseKernel Tb.coupling Tb.ρA Tb.side u b c * latticeGradient φ c =
      (-(((bondDeriv (torusCoordinate Tb.coupling Tb.ρA
          (torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1, b.2))
        (uniformField (torusFrame Tb.side u n) (torusFrame Tb.side u n).top)
        ![(torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).top c.1, c.2)] ![unitGenerator] :
          imaginaryQuaternions) : ℍ[ℝ]) *
        (unitGenerator : ℍ[ℝ])).re) * latticeGradient φ c +
      (open Classical in if IsCrossingBond (torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1, b.2) ∧
        enclosingCell (torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).depth b.1) =
          torusToFrame (torusFrame Tb.side u n) (torusFrame Tb.side u n).top c.1 ∧ b.2 = c.2 then (1 : ℝ) else 0) *
        latticeGradient φ c := by
    intro c
    rw [← add_mul]
    rfl
  rw [Finset.sum_congr rfl fun c _ => hentry c, Finset.sum_add_distrib, h1, zero_add, h2,
    parentBlock_eq (u := u), parentBlock_eq (u := u) b.1, hu]
abbrev _root_.YangMills.SharedProofs.p10520 := @responseMap_gradient
end Response
end MaxwellGradients
theorem gradientMaxwellStatement_holds (hFlat : flatTopVanishingStatement)
    (hLeast : minimalChainExistenceStatement) (hOne : MinimizingChartUnique)
    (hGauge : MinimalActionGaugeCovariance) (hBlock : SiteDecomposition)
    (hCost : WholeCellCostEqualsMinimalAction) : gradientMaxwellStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ _
  refine ⟨0, fun y _ _ _ => ?_⟩
  intro u n _ hn
  have hn64 : 64 ≤ n := by
    have := hD.n₀_ge
    omega
  have hcl : (∀ (φ : TorusSite n → ℝ) (A : TorusBond n → ℝ),
        maxwellForm T.coupling T.side u (latticeGradient φ) A = 0) ∧
      ∀ A : TorusBond n → ℝ, 2 * T.coercivity * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤
        maxwellForm T.coupling T.side u A A := by
    cases u with
    | zero =>
      have ha : 0 ≤ T.coupling := by linarith [hD.a_ge]
      exact MaxwellGradients.maxwell_bounds_zero T.coupling T.side T.coercivity hD.cK_pos
        (MaxwellGradients.coercivity_le_half hD.coercive ha hD.L_odd hBlock hCost n hn64)
    | succ t => exact MaxwellGradients.maxwell_bounds_upper hD hFlat hLeast hGauge hCost t hn64
  exact ⟨fun φ => MaxwellGradients.responseMap_gradient hD hFlat hOne hGauge hBlock u hn64 φ, hcl.1, hcl.2⟩
end ResponseInTheExpansion
end YangMills.Construction
end
