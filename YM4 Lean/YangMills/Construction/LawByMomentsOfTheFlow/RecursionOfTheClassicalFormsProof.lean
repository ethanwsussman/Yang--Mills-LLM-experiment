import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import YangMills.Construction.LawByMomentsOfTheFlow.CurveOfLeastFieldsOfOneColour
import YangMills.Construction.LawByMomentsOfTheFlow.LeastValueOfAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.RecursionOfTheClassicalForms
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import Mathlib
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages hiding unitStep
open TorusContours hiding contourIndex contourWeight
open TorusFields TorusShares RenormalizationStepParameters StepCosts ShareFamilies WeightedResponses SecondOrder
open ResponseInTheExpansion ResponseInTheExpansion.SingleColourFields TopLevelSites TorusPaths ClusterExpansionOfAStep
namespace MomentLaw
namespace RecursionLemmas
section Angles
variable {m : ℕ}
private def alongAngles (G : TorusField m → ℝ) (θ : TorusBond m → ℝ) : ℝ := G (expOfColourForm 1 θ)
private theorem contDiffAt_alongAngles [NeZero m] {G : TorusField m → ℝ} (h : ContDiffThreeAt G (trivialField m)) :
    ContDiffAt ℝ 2 (alongAngles G) 0 := by
  classical
  set e := Fintype.equivFin (TorusBond m) with he
  have h3 := h _ e.symm (fun _ => unitGenerator)
  have hm : ∀ σ : Fin (Fintype.card (TorusBond m)) → ℝ, perturb e.symm (fun _ => unitGenerator) σ (trivialField m) =
      expOfColourForm 1 (fun b => σ (e b)) := by
    intro σ
    funext x i
    show expUnit (∑ l, if e.symm l = (x, i) then σ l • unitGenerator else 0) * 1 =
      expUnit ((1 * σ (e (x, i))) • unitGenerator)
    rw [mul_one, one_mul]
    congr 1
    rw [Finset.sum_eq_single (e (x, i))]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h
      exact hl (by rw [← h]; simp)
    · simp
  have hA : alongAngles G = (fun σ : Fin (Fintype.card (TorusBond m)) → ℝ =>
      G (perturb e.symm (fun _ => unitGenerator) σ (trivialField m))) ∘
        (fun θ : TorusBond m → ℝ => fun l => θ (e.symm l)) := by
    funext θ
    simp only [Function.comp, hm]
    simp [alongAngles]
  rw [hA]
  have hl : ContDiffAt ℝ 2 (fun θ : TorusBond m → ℝ => fun l => θ (e.symm l)) 0 := by
    refine ContDiff.contDiffAt (contDiff_pi.mpr fun l => ?_)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond m => ℝ) (e.symm l)).contDiff
  have h3' : ContDiffAt ℝ 2 (fun σ : Fin (Fintype.card (TorusBond m)) → ℝ =>
      G (perturb e.symm (fun _ => unitGenerator) σ (trivialField m)))
      ((fun θ : TorusBond m → ℝ => fun l => θ (e.symm l)) 0) := h3.of_le (by norm_num)
  exact ContDiffAt.comp (0 : TorusBond m → ℝ) h3' hl
abbrev _root_.YangMills.DeltaSharedProofs.p855 := @contDiffAt_alongAngles
private theorem hessianAtIdentity_apply_eq [NeZero m] {G : TorusField m → ℝ} (hC : ContDiffAt ℝ 2 (alongAngles G) 0)
    (b b' : TorusBond m) :
    hessianAtIdentity G b b' = hessianAtZero (alongAngles G) (Pi.single b 1) (Pi.single b' 1) := by
  classical
  set ι : (Fin 2 → ℝ) →L[ℝ] (TorusBond m → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single b 1) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (Pi.single b' 1) with hι
  have hm : ∀ σ : Fin 2 → ℝ, perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField m) =
      expOfColourForm 1 (ι σ) := by
    intro σ
    funext x i
    show expUnit (∑ l, if ![b, b'] l = (x, i) then σ l • ![unitGenerator, unitGenerator] l else 0) * 1 =
      expUnit ((1 * ι σ (x, i)) • unitGenerator)
    rw [mul_one, one_mul, Fin.sum_univ_two]
    congr 1
    by_cases h1 : b = (x, i) <;> by_cases h2 : b' = (x, i) <;>
      simp [hι, h1, h2, eq_comm, add_smul]
  unfold hessianAtIdentity mixedDeriv
  rw [iteratedFDeriv_two_apply]
  have e : (fun σ : Fin 2 → ℝ => G (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField m))) =
      fun σ => alongAngles G (ι σ) := funext fun σ => by rw [hm]; rfl
  rw [e]
  have h := hessianAtZero_comp_clm hC ι (Pi.single 0 1) (Pi.single 1 1)
  have e0 : ι (Pi.single 0 1) = Pi.single b 1 := by simp [hι]
  have e1 : ι (Pi.single 1 1) = Pi.single b' 1 := by simp [hι]
  rw [e0, e1] at h
  exact h
abbrev _root_.YangMills.DeltaSharedProofs.p501250 := @hessianAtIdentity_apply_eq
private theorem bilinearEval_hessian_eq [NeZero m] {G : TorusField m → ℝ} (hC : ContDiffAt ℝ 2 (alongAngles G) 0)
    (A A' : TorusBond m → ℝ) :
    bilinearEval (hessianAtIdentity G) A A' = hessianAtZero (alongAngles G) A A' := by
  classical
  have hs : ∀ A : TorusBond m → ℝ, A = ∑ b, A b • (Pi.single b 1 : TorusBond m → ℝ) := by
    intro A
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hs A, hs A']
  rw [hessianAtZero_sum_left]
  simp only [hessianAtZero_sum_right, hessianAtZero_smul_left, hessianAtZero_smul_right]
  unfold bilinearEval
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [hessianAtIdentity_apply_eq hC]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p502044 := @bilinearEval_hessian_eq
private theorem fderiv_eq_zero_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : DifferentiableAt ℝ f 0) (h : ∀ v : E, ∀ᶠ τ in 𝓝 (0 : ℝ), f (τ • v) = f ((-τ) • v)) :
    fderiv ℝ f 0 = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hD : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hf.hasFDerivAt
  have hD' : HasFDerivAt f (fderiv ℝ f 0) ((-(0 : ℝ)) • v) := by
    rw [neg_zero, zero_smul]
    exact hf.hasFDerivAt
  have hl : HasDerivAt (fun τ : ℝ => τ • v) v 0 := by
    have h3 : HasDerivAt (fun τ : ℝ => τ • v) ((1 : ℝ) • v) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const _
    rwa [one_smul] at h3
  have hl' : HasDerivAt (fun τ : ℝ => (-τ) • v) (-v) 0 := by
    have h3 : HasDerivAt (fun τ : ℝ => (-τ) • v) ((-1 : ℝ) • v) 0 :=
      (hasDerivAt_id' (0 : ℝ)).fun_neg.smul_const _
    rwa [neg_one_smul] at h3
  have h1 : HasDerivAt (fun τ : ℝ => f (τ • v)) (fderiv ℝ f 0 v) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => τ • v) (0 : ℝ) hD hl
  have h2 : HasDerivAt (fun τ : ℝ => f ((-τ) • v)) (fderiv ℝ f 0 (-v)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => (-τ) • v) (0 : ℝ) hD' hl'
  have h3 := h1.unique (h2.congr_of_eventuallyEq (h v))
  rw [map_neg] at h3
  simp only [ContinuousLinearMap.zero_apply]
  linarith
end Angles
section Wilson
variable {m : ℕ} [NeZero m]
private theorem holonomy_expOfColourForm (τ : ℝ) (B : TorusBond m → ℝ) (x : TorusSite m) (μ ν : Fin 4) :
    holonomy (expOfColourForm τ B) x μ ν =
      colourRotation (τ * (B (x, μ) + B (x + unitStep m μ, ν) - B (x + unitStep m ν, μ) - B (x, ν))) := by
  unfold holonomy
  simp only [expOfColourForm_apply, colourRotation_inv, ← colourRotation_add]
  congr 1
  ring
private theorem plaquetteEnergyOf_exp (θ : TorusBond m → ℝ) (p : TorusPlaquette m) :
    plaquetteEnergyOf (expOfColourForm 1 θ) p = 1 - Real.cos (curl θ p) := by
  unfold plaquetteEnergyOf plaquetteEnergy
  rw [holonomy_expOfColourForm, coe_colourRotation, one_mul]
  simp [curl]
private theorem curl_smul (τ : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (τ • A) p = τ * curl A p := by
  simp only [curl, Pi.smul_apply, smul_eq_mul]
  ring
private theorem contDiff_curl (p : TorusPlaquette m) : ContDiff ℝ 2 (fun θ : TorusBond m → ℝ => curl θ p) := by
  unfold curl
  have hc : ∀ b : TorusBond m, ContDiff ℝ 2 (fun θ : TorusBond m → ℝ => θ b) := fun b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond m => ℝ) b).contDiff
  exact (((hc _).add (hc _)).sub (hc _)).sub (hc _)
private def weightedCosineAction (w : TorusPlaquette m → ℝ) (θ : TorusBond m → ℝ) : ℝ :=
  ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), w p * (1 - Real.cos (curl θ p))
private theorem contDiff_weightedCosineAction (w : TorusPlaquette m → ℝ) :
    ContDiff ℝ 2 (weightedCosineAction w) := by
  unfold weightedCosineAction
  exact ContDiff.sum fun p _ => contDiff_const.mul
    (contDiff_const.sub (Real.contDiff_cos.comp (contDiff_curl p)))
private theorem secondJet_weightedCosineAction (w : TorusPlaquette m → ℝ) (A : TorusBond m → ℝ) :
    SecondJet (fun τ : ℝ => weightedCosineAction w (τ • A)) 0 0
      (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), w p * curl A p ^ 2) := by
  have J := SecondJet.sum (plaquettesIn (Finset.univ : Finset (TorusSite m)))
    (g := fun p τ => w p * (1 - Real.cos (τ * curl A p))) (a0 := fun p => w p * (1 - 1))
    (a1 := fun p => w p * (0 - 0)) (a2 := fun p => w p * (0 - -curl A p ^ 2))
    fun p _ => ((SecondJet.const 1).sub (SecondJet.cos_mul (curl A p))).const_mul (w p)
  convert J using 1
  · funext τ
    simp only [weightedCosineAction, curl_smul]
  · simp
  · simp
  · simp
private theorem hessianAtZero_weightedCosineAction (w : TorusPlaquette m → ℝ) (A : TorusBond m → ℝ) :
    hessianAtZero (weightedCosineAction w) A A =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), w p * curl A p ^ 2 := by
  rw [← deriv_deriv_along_line (contDiff_weightedCosineAction w).contDiffAt A]
  exact (secondJet_weightedCosineAction w A).secondDeriv
private theorem fderiv_weightedCosineAction (w : TorusPlaquette m → ℝ) :
    fderiv ℝ (weightedCosineAction w) 0 = 0 := by
  refine fderiv_eq_zero_of_even ((contDiff_weightedCosineAction w).differentiable (by norm_num) _) fun v => ?_
  refine Filter.Eventually.of_forall fun τ => ?_
  unfold weightedCosineAction
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [curl_smul, curl_smul, neg_mul, Real.cos_neg]
private theorem alongAngles_siteResponse (y : TorusSite m) (h : PlaquetteWeight m) :
    alongAngles (fun W => siteResponse y W h) =
      weightedCosineAction (fun p => vertexMultiplicity y p / 4 * h p) := by
  funext θ
  unfold alongAngles siteResponse weightedCosineAction
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteEnergyOf_exp]
  ring
private theorem levelShare_zero (a : ℝ) (L : ℕ) (y : TorusSite m) :
    levelShare a L 0 Finset.univ y = fun W => siteResponse y W (constOneWeight m) := by
  funext W
  show ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
    (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 * plaquetteEnergy W p.1 p.2.1 p.2.2 = _
  unfold siteResponse
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [vertexMultiplicity, plaquetteEnergyOf, constOneWeight]
private theorem bilinearEval_linearComb (κ : ℝ) (q r : BondBilinear m) (A : TorusBond m → ℝ) :
    bilinearEval (fun b b' => κ * q b b' + r b b') A A = κ * bilinearEval q A A + bilinearEval r A A := by
  unfold bilinearEval
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem bilinearEval_level_zero (κ : ℝ) (y : TorusSite m) (h : PlaquetteWeight m) {R : TorusField m → ℝ}
    (hR : ∀ W, R W = siteResponse y W h - κ * siteResponse y W (constOneWeight m)) (A : TorusBond m → ℝ) :
    κ * bilinearEval (hessianAtIdentity fun W => siteResponse y W (constOneWeight m)) A A +
        bilinearEval (hessianAtIdentity R) A A =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), vertexMultiplicity y p / 4 * h p * curl A p ^ 2 := by
  have e1 := alongAngles_siteResponse y (constOneWeight m)
  have e2 : alongAngles R = weightedCosineAction
      (fun p => vertexMultiplicity y p / 4 * h p - κ * (vertexMultiplicity y p / 4 * constOneWeight m p)) := by
    funext θ
    have a1 := congrFun (alongAngles_siteResponse y h) θ
    have a2 := congrFun e1 θ
    simp only [alongAngles] at a1 a2
    simp only [alongAngles, hR, a1, a2]
    unfold weightedCosineAction
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have c1 : ContDiffAt ℝ 2 (alongAngles fun W => siteResponse y W (constOneWeight m)) 0 := by
    rw [e1]
    exact (contDiff_weightedCosineAction _).contDiffAt
  have c2 : ContDiffAt ℝ 2 (alongAngles R) 0 := by
    rw [e2]
    exact (contDiff_weightedCosineAction _).contDiffAt
  rw [bilinearEval_hessian_eq c1, bilinearEval_hessian_eq c2, e1, e2, hessianAtZero_weightedCosineAction,
    hessianAtZero_weightedCosineAction, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring
private theorem sum_vertexMultiplicity_div (p : TorusPlaquette m) :
    ∑ y : TorusSite m, vertexMultiplicity y p / 4 = 1 := by
  classical
  have h : ∀ y : TorusSite m, vertexMultiplicity y p =
      (if p.1 = y then 1 else 0) + (if p.1 + unitStep m p.2.1 = y then 1 else 0) +
        (if p.1 + unitStep m p.2.2 = y then 1 else 0) +
        (if p.1 + unitStep m p.2.1 + unitStep m p.2.2 = y then 1 else 0) := by
    intro y
    unfold vertexMultiplicity plaquetteVertices
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    push_cast
    ring
  simp only [h]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  norm_num
end Wilson
section Frame
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem period_fine (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period u i = n * L :=
  period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem period_coarse (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period (u + 1) i = n :=
  period_top_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem sumAlongPath_smul {N : ℕ} (τ : ℝ) (θ : TorusBond N → ℝ) (l : List PathStep) :
    ∀ x, sumAlongPath (τ • θ) x l = τ * sumAlongPath θ x l := by apply _root_.YangMills.SharedProofs.p13483 <;> assumption
private theorem contourSum_smul {N : ℕ} (L : ℕ) {n : ℕ} (τ : ℝ) (θ : TorusBond N → ℝ) (c : TorusBond n)
    (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourSum L (τ • θ) c k = τ * contourSum L θ c k := sumAlongPath_smul _ _ _ _
private theorem contourSum_zero {N : ℕ} (L : ℕ) {n : ℕ} (c : TorusBond n) (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourSum L (0 : TorusBond N → ℝ) c k = 0 := by apply _root_.YangMills.SharedProofs.p22967 <;> assumption
private theorem contDiff_sumAlongPath {N : ℕ} [NeZero N] (l : List PathStep) :
    ∀ x, ContDiff ℝ 2 (fun θ : TorusBond N → ℝ => sumAlongPath θ x l) := by apply _root_.YangMills.SharedProofs.p9311 <;> assumption
private abbrev AnglePair (L n : ℕ) : Type := (TorusBond (n * L) → ℝ) × (TorusBond n → ℝ)
private def angleFit (L : ℕ) (p : AnglePair L n) (c : TorusBond n) : ℝ :=
  Real.sqrt (contourCosMean L p.1 c 1 ^ 2 + contourSinMean L p.1 c 1 ^ 2) -
    (contourCosMean L p.1 c 1 * Real.cos (1 * p.2 c) + contourSinMean L p.1 c 1 * Real.sin (1 * p.2 c))
private theorem secondJet_angleFit (hL : Odd L) (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ)
    (c : TorusBond n) :
    SecondJet (fun τ : ℝ => angleFit L (τ • ((W, B) : AnglePair L n)) c) 0 0
      ((∑ k ∈ contourIndex L, contourWeight L * contourSum L W c k - B c) ^ 2) := by
  have h := SecondJet.rotationFit (contourIndex L) (fun _ => contourWeight L) (fun k => contourSum L W c k) (B c)
    (sum_contourWeight hL)
  convert h using 1
  funext τ
  simp only [angleFit, contourCosMean, contourSinMean, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul, one_mul, contourSum_smul]
private theorem contDiff_contourCosMean (c : TorusBond n) :
    ContDiff ℝ 2 (fun p : AnglePair L n => contourCosMean L p.1 c 1) := by apply _root_.YangMills.DeltaSharedProofs.p502436 <;> assumption
private theorem contDiff_contourSinMean (c : TorusBond n) :
    ContDiff ℝ 2 (fun p : AnglePair L n => contourSinMean L p.1 c 1) := by apply _root_.YangMills.DeltaSharedProofs.p501378 <;> assumption
private theorem contourCosMean_zero (hL : Odd L) (c : TorusBond n) :
    contourCosMean L (0 : TorusBond (n * L) → ℝ) c 1 = 1 := by apply _root_.YangMills.SharedProofs.p15344 <;> assumption
private theorem contourSinMean_zero (c : TorusBond n) : contourSinMean L (0 : TorusBond (n * L) → ℝ) c 1 = 0 := by
  simp [contourSinMean, contourSum_zero]
private theorem contDiffAt_angleFit (hL : Odd L) (c : TorusBond n) :
    ContDiffAt ℝ 2 (fun p : AnglePair L n => angleFit L p c) 0 := by
  unfold angleFit
  have hC := contDiff_contourCosMean (L := L) c
  have hS := contDiff_contourSinMean (L := L) c
  have h2 : ContDiff ℝ 2 (fun p : AnglePair L n => p.2 c) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) c).contDiff.comp contDiff_snd
  refine ContDiffAt.sub (ContDiffAt.sqrt ?_ ?_) ?_
  · exact ((hC.pow 2).add (hS.pow 2)).contDiffAt
  · have e1 : contourCosMean L (0 : AnglePair L n).1 c 1 = 1 := contourCosMean_zero hL c
    have e2 : contourSinMean L (0 : AnglePair L n).1 c 1 = 0 := contourSinMean_zero c
    rw [e1, e2]
    norm_num
  · exact ((hC.mul (Real.contDiff_cos.comp (contDiff_const.mul h2))).add
      (hS.mul (Real.contDiff_sin.comp (contDiff_const.mul h2)))).contDiffAt
private theorem angleFit_zero (hL : Odd L) (c : TorusBond n) : angleFit L (0 : AnglePair L n) c = 0 := by
  unfold angleFit
  have e1 : contourCosMean L (0 : AnglePair L n).1 c 1 = 1 := contourCosMean_zero hL c
  have e2 : contourSinMean L (0 : AnglePair L n).1 c 1 = 0 := contourSinMean_zero c
  rw [e1, e2]
  simp
private theorem blockFitAt_eq_angleFit (θ : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ) (c : TorusBond n) :
    blockFitAt L (expOfColourForm 1 θ) (expOfColourForm 1 B) c = angleFit L ((θ, B) : AnglePair L n) c :=
  SingleColourFields.blockFit_readAtLevel (G := TorusLumps.stepBlockFrame L n) (period_fine L 0 n)
    (period_coarse L 0 n) 1 θ B c
private theorem angleFit_nonneg (p : AnglePair L n) (c : TorusBond n) : 0 ≤ angleFit L p c := by
  have e : angleFit L p c = blockFitAt L (expOfColourForm 1 p.1) (expOfColourForm 1 p.2) c :=
    (blockFitAt_eq_angleFit p.1 p.2 c).symm
  rw [e]
  exact blockFit_nonneg _ _ _
private theorem fderiv_angleFit (hL : Odd L) (c : TorusBond n) :
    fderiv ℝ (fun p : AnglePair L n => angleFit L p c) 0 = 0 := by
  have hmin : IsLocalMin (fun p : AnglePair L n => angleFit L p c) 0 := by
    refine Filter.Eventually.of_forall fun p => ?_
    show angleFit L (0 : AnglePair L n) c ≤ angleFit L p c
    rw [angleFit_zero hL]
    exact angleFit_nonneg p c
  exact hmin.fderiv_eq_zero
private theorem contourAverage_eq (W : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L W c = ∑ k ∈ contourIndex L, contourWeight L * contourSum L W c k := by apply _root_.YangMills.SharedProofs.p107193 <;> assumption
private theorem sumAlongWord_add {N : ℕ} (A A' : TorusBond N → ℝ) (w : BondWord N) :
    sumAlongWord (A + A') w = sumAlongWord A w + sumAlongWord A' w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
private theorem contourAverage_add (W W' : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (W + W') c = _root_.YangMills.Construction.MomentLaw.contourAverage L W c + _root_.YangMills.Construction.MomentLaw.contourAverage L W' c := by
  unfold _root_.YangMills.Construction.MomentLaw.contourAverage
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun e _ => sumAlongWord_add _ _ _
private theorem expOfColourForm_one_smul {m : ℕ} (τ : ℝ) (B : TorusBond m → ℝ) :
    expOfColourForm 1 (τ • B) = expOfColourForm τ B := by apply _root_.YangMills.SharedProofs.p43028 <;> assumption
end Frame
section Even
variable {m : ℕ} [NeZero m]
private theorem eventually_curvature_lt (B : TorusBond m → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (q : TorusSite m × Fin 4 × Fin 4) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), curvature (expOfColourForm τ B) q.1 q.2.1 q.2.2 < σ := by apply _root_.YangMills.SharedProofs.p47205 <;> assumption
private theorem eventually_cold (B : TorusBond m → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ q : TorusSite m × Fin 4 × Fin 4,
      curvature (expOfColourForm τ B) q.1 q.2.1 q.2.2 < σ :=
  Filter.eventually_all.2 (eventually_curvature_lt B hσ)
private def quatJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
private theorem quatJ_re : quatJ.re = 0 := rfl
private theorem quatJ_imI : quatJ.imI = 0 := rfl
private theorem quatJ_imJ : quatJ.imJ = 1 := rfl
private theorem quatJ_imK : quatJ.imK = 0 := rfl
private def unitJ : UnitQuaternion := ⟨quatJ, by
  rw [Unitary.mem_iff]
  constructor <;> apply Quaternion.ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, quatJ_re, quatJ_imI, quatJ_imJ, quatJ_imK]⟩
private theorem unitJ_conj_colourRotation (s : ℝ) : unitJ * colourRotation s * unitJ⁻¹ = colourRotation (-s) := by
  apply Subtype.ext
  show quatJ * ((colourRotation s : UnitQuaternion) : ℍ[ℝ]) * star quatJ =
    ((colourRotation (-s) : UnitQuaternion) : ℍ[ℝ])
  rw [coe_colourRotation, coe_colourRotation]
  apply Quaternion.ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, quatJ_re, quatJ_imI,
      quatJ_imJ, quatJ_imK, Real.cos_neg, Real.sin_neg]
private theorem gaugeTransform_unitJ (θ : TorusBond m → ℝ) :
    TorusFields.gaugeTransform (fun _ => unitJ) (expOfColourForm 1 θ) = expOfColourForm 1 (-θ) := by
  funext x i
  show unitJ * expOfColourForm 1 θ x i * unitJ⁻¹ = expOfColourForm 1 (-θ) x i
  rw [expOfColourForm_apply, expOfColourForm_apply, unitJ_conj_colourRotation]
  simp
end Even
section Shares
variable {m : ℕ} [NeZero m]
private theorem levelShare_angle_facts (hS : LevelSharesFormCurvatureFamily) (T : ParameterAssignment)
    (hD : T.Admissible) (u : ℕ) (hm : T.n₀ ≤ m) (y : TorusSite m) :
    ContDiffAt ℝ 2 (alongAngles (levelShare T.coupling T.side u Finset.univ y)) 0 ∧
      fderiv ℝ (alongAngles (levelShare T.coupling T.side u Finset.univ y)) 0 = 0 := by
  cases u with
  | zero =>
    rw [levelShare_zero, alongAngles_siteResponse]
    exact ⟨(contDiff_weightedCosineAction _).contDiffAt, fderiv_weightedCosineAction _⟩
  | succ k =>
    have hF := (hS T hD T.floorMin le_rfl k).1
    have e : levelShareFamily T.coupling T.side (k + 1) m y = levelShare T.coupling T.side (k + 1) Finset.univ y := by
      funext V
      unfold levelShareFamily
      rw [dif_neg (NeZero.ne m)]
    have hσ : 0 < (T.stepParameters T.floorMin).threshold := hD.σ_pos
    have hc : IsCold (T.stepParameters T.floorMin).threshold (trivialField m) := by
      intro x μ ν _
      have : curvature (trivialField m) x μ ν = 0 := by simp [curvature, holonomy, trivialField]
      rw [this]
      exact hσ
    have h3 := hF.smooth m hm y (trivialField m) hc
    rw [e] at h3
    have hC2 := contDiffAt_alongAngles h3
    refine ⟨hC2, fderiv_eq_zero_of_even (hC2.differentiableAt (by norm_num)) fun v => ?_⟩
    refine (eventually_cold v hσ).mono fun τ hτ => ?_
    have hcold : IsCold (T.stepParameters T.floorMin).threshold (expOfColourForm 1 (τ • v)) := by
      rw [expOfColourForm_one_smul]
      exact fun x μ ν _ => hτ (x, μ, ν)
    have hg := hF.gauge m hm y (fun _ => unitJ) _ hcold
    rw [e, gaugeTransform_unitJ] at hg
    unfold alongAngles
    rw [neg_smul]
    exact hg.symm
end Shares
section Step
private def fitSlope (a ρ : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (B : TorusBond n → ℝ) (c : TorusBond n) : ℝ :=
  _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u B) c - B c
private theorem responseMap_add (a ρ : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (B B' : TorusBond n → ℝ) :
    responseMap a ρ L u (B + B') = responseMap a ρ L u B + responseMap a ρ L u B' := by
  funext b
  simp only [responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem fitSlope_add (a ρ : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (B B' : TorusBond n → ℝ)
    (c : TorusBond n) :
    fitSlope a ρ L u (B + B') c = fitSlope a ρ L u B c + fitSlope a ρ L u B' c := by
  unfold fitSlope
  rw [responseMap_add, contourAverage_add]
  simp only [Pi.add_apply]
  ring
private theorem angleFit_along_curve {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L)
    {γ : ℝ → TorusBond (n * L) → ℝ} (hγ : ContDiffAt ℝ 2 γ 0) (h0 : γ 0 = 0) (B : TorusBond n → ℝ)
    (c : TorusBond n) :
    ContDiffAt ℝ 2 (fun τ : ℝ => angleFit L ((γ τ, τ • B) : AnglePair L n) c) 0 ∧
      deriv (deriv fun τ : ℝ => angleFit L ((γ τ, τ • B) : AnglePair L n) c) 0 =
        (_root_.YangMills.Construction.MomentLaw.contourAverage L (deriv γ 0) c - B c) ^ 2 := by
  set cv : ℝ → AnglePair L n := fun τ => (γ τ, τ • B) with hcv
  have cC : ContDiffAt ℝ 2 cv 0 := hγ.prodMk (contDiffAt_id.smul contDiffAt_const)
  have c0 : cv 0 = 0 := Prod.ext h0 (zero_smul ℝ B)
  have cd : deriv cv 0 = (deriv γ 0, B) := by
    have h1 : HasDerivAt γ (deriv γ 0) 0 := (hγ.differentiableAt (by norm_num)).hasDerivAt
    have h2 : HasDerivAt (fun τ : ℝ => τ • B) B 0 := by
      have h3 : HasDerivAt (fun τ : ℝ => τ • B) ((1 : ℝ) • B) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const _
      rwa [one_smul] at h3
    exact (h1.prodMk h2).deriv
  have hF := contDiffAt_angleFit (L := L) hL c
  refine ⟨?_, ?_⟩
  · have h0' : ContDiffAt ℝ 2 (fun p : AnglePair L n => angleFit L p c) (cv 0) := by
      rw [c0]
      exact hF
    exact ContDiffAt.comp (g := fun p : AnglePair L n => angleFit L p c) (f := cv) (0 : ℝ) h0' cC
  · have e := deriv_deriv_along_curve hF (fderiv_angleFit hL c) cC c0
    rw [cd] at e
    refine e.trans ?_
    rw [← deriv_deriv_along_line hF, (secondJet_angleFit hL (deriv γ 0) B c).secondDeriv, contourAverage_eq]
variable (hC : minimizerCurveStatement) (hSp : LevelShareSplits)
  (hS : LevelSharesFormCurvatureFamily) (T : ParameterAssignment) (hD : T.Admissible)
include hC hSp hS hD
private theorem levelShare_hessian_diag (u n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (Y : TorusSite n)
    (B : TorusBond n → ℝ) :
    hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) B B =
      ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y}, hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y))
        (responseMap T.coupling T.ρA T.side u B) (responseMap T.coupling T.ρA T.side u B) +
      T.coupling * (1 / 2 * ∑ i : Fin 4, (fitSlope T.coupling T.ρA T.side u B (Y, i) ^ 2 +
        fitSlope T.coupling T.ρA T.side u B (Y - unitStep n i, i) ^ 2)) := by
  classical
  have hL : Odd T.side := hD.L_odd
  have ha : 0 < T.coupling := lt_of_lt_of_le one_pos hD.a_ge
  have hn64 : 64 ≤ n := by
    have := hD.n₀_ge
    omega
  have hσ : 0 < T.σA := hD.chain.2.2.2.2.2.1
  have hnL : T.n₀ ≤ n * T.side :=
    hn.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne T.side)))
  obtain ⟨γ, hγ, h0, hd, hev⟩ := hC T hD u n hn64 B
  have hf := (levelShare_angle_facts hS T hD (u + 1) hn Y).1
  rw [← deriv_deriv_along_line hf B]
  set g1 : TorusSite (n * T.side) → ℝ → ℝ :=
    fun y τ => alongAngles (levelShare T.coupling T.side u Finset.univ y) (γ τ) with hg1
  set g2 : TorusBond n → ℝ → ℝ := fun c τ => angleFit T.side ((γ τ, τ • B) : AnglePair T.side n) c with hg2
  have s1 : ∀ y, ContDiffAt ℝ 2 (g1 y) 0 := by
    intro y
    have h1 := (levelShare_angle_facts hS T hD u hnL y).1
    have h0' : ContDiffAt ℝ 2 (alongAngles (levelShare T.coupling T.side u Finset.univ y)) (γ 0) := by
      rw [h0]
      exact h1
    exact ContDiffAt.comp (g := alongAngles (levelShare T.coupling T.side u Finset.univ y)) (f := γ) (0 : ℝ) h0' hγ
  have d1 : ∀ y, deriv (deriv (g1 y)) 0 = hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y))
      (responseMap T.coupling T.ρA T.side u B) (responseMap T.coupling T.ρA T.side u B) := by
    intro y
    have h1 := levelShare_angle_facts hS T hD u hnL y
    have e := deriv_deriv_along_curve h1.1 h1.2 hγ h0
    rw [hd] at e
    exact e
  have s2 : ∀ c, ContDiffAt ℝ 2 (g2 c) 0 := fun c => (angleFit_along_curve hL hγ h0 B c).1
  have d2 : ∀ c, deriv (deriv (g2 c)) 0 = fitSlope T.coupling T.ρA T.side u B c ^ 2 := by
    intro c
    have e := (angleFit_along_curve hL hγ h0 B c).2
    rw [hd] at e
    exact e
  have heq : (fun τ : ℝ => alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y) (τ • B)) =ᶠ[𝓝 0]
      fun τ => ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y}, g1 y τ +
        T.coupling * (1 / 2 * ∑ i : Fin 4, (g2 (Y, i) τ + g2 (Y - unitStep n i, i) τ)) := by
    filter_upwards [hev, eventually_cold B hσ] with τ h1 h2
    have hreg : IsLocallyOrthantClosed (Finset.univ : Finset (TorusSite n)) 1024 := fun z =>
      ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
    have hcold : IsColdOn (Finset.univ : Finset (TorusSite n)) T.σA (expOfColourForm τ B) :=
      fun x μ ν _ _ => h2 (x, μ, ν)
    have hs := hSp T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N ha hL hD.chain u n Finset.univ
      (expOfColourForm τ B) T.σA Y hn64 hσ le_rfl hreg hcold (Finset.mem_univ Y)
    have hb : TorusLumps.sitesInBlocks T.side (Finset.univ : Finset (TorusSite n)) = Finset.univ := by
      ext x
      simp [TorusLumps.sitesInBlocks]
    rw [h1, hb] at hs
    unfold alongAngles
    rw [expOfColourForm_one_smul, hs]
    refine congrArg₂ (· + ·) rfl (congrArg (T.coupling * ·) ?_)
    unfold halfBlockFits
    simp only [Finset.mem_univ, if_true]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← expOfColourForm_one_smul τ B, blockFitAt_eq_angleFit, blockFitAt_eq_angleFit]
  rw [heq.deriv.deriv_eq]
  have J1 := SecondJet.sum (TorusLumps.sitesInBlocks T.side {Y}) (g := g1) (a0 := fun y => g1 y 0)
    (a1 := fun y => deriv (g1 y) 0) (a2 := fun y => deriv (deriv (g1 y)) 0)
    fun y _ => SecondJet.of_contDiffAt (s1 y)
  have J2 := SecondJet.sum (Finset.univ : Finset (Fin 4))
    (g := fun i τ => g2 (Y, i) τ + g2 (Y - unitStep n i, i) τ)
    (a0 := fun i => g2 (Y, i) 0 + g2 (Y - unitStep n i, i) 0)
    (a1 := fun i => deriv (g2 (Y, i)) 0 + deriv (g2 (Y - unitStep n i, i)) 0)
    (a2 := fun i => deriv (deriv (g2 (Y, i))) 0 + deriv (deriv (g2 (Y - unitStep n i, i))) 0)
    fun i _ => (SecondJet.of_contDiffAt (s2 _)).add (SecondJet.of_contDiffAt (s2 _))
  have J := J1.add ((J2.const_mul (1 / 2)).const_mul T.coupling)
  rw [J.secondDeriv]
  simp only [d1, d2]
private theorem levelShare_hessian_polar (u n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (Y : TorusSite n)
    (B B' : TorusBond n → ℝ) :
    hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) B B' =
      ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y}, hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y))
        (responseMap T.coupling T.ρA T.side u B) (responseMap T.coupling T.ρA T.side u B') +
      T.coupling * (1 / 2 * ∑ i : Fin 4,
        (fitSlope T.coupling T.ρA T.side u B (Y, i) * fitSlope T.coupling T.ρA T.side u B' (Y, i) +
          fitSlope T.coupling T.ρA T.side u B (Y - unitStep n i, i) *
            fitSlope T.coupling T.ρA T.side u B' (Y - unitStep n i, i))) := by
  have hnL : T.n₀ ≤ n * T.side :=
    hn.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne T.side)))
  have e1 := levelShare_hessian_diag hC hSp hS T hD u n hn Y (B + B')
  have e2 := levelShare_hessian_diag hC hSp hS T hD u n hn Y B
  have e3 := levelShare_hessian_diag hC hSp hS T hD u n hn Y B'
  have hf := (levelShare_angle_facts hS T hD (u + 1) hn Y).1
  set M := responseMap T.coupling T.ρA T.side u B with hM
  set M' := responseMap T.coupling T.ρA T.side u B' with hM'
  have l1 : hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) (B + B') (B + B') =
      hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) B B +
        2 * hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) B B' +
        hessianAtZero (alongAngles (levelShare T.coupling T.side (u + 1) Finset.univ Y)) B' B' := by
    rw [hessianAtZero_add_left, hessianAtZero_add_right, hessianAtZero_add_right, hessianAtZero_comm hf B' B]
    ring
  have t1 : ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y}, hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y))
      (responseMap T.coupling T.ρA T.side u (B + B')) (responseMap T.coupling T.ρA T.side u (B + B')) =
      ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y}, hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y)) M M +
        2 * ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y},
          hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y)) M M' +
        ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y},
          hessianAtZero (alongAngles (levelShare T.coupling T.side u Finset.univ y)) M' M' := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [responseMap_add, hessianAtZero_add_left, hessianAtZero_add_right, hessianAtZero_add_right,
      hessianAtZero_comm (levelShare_angle_facts hS T hD u hnL y).1 M' M]
    ring
  have t2 : ∑ i : Fin 4, (fitSlope T.coupling T.ρA T.side u (B + B') (Y, i) ^ 2 +
      fitSlope T.coupling T.ρA T.side u (B + B') (Y - unitStep n i, i) ^ 2) =
      ∑ i : Fin 4, (fitSlope T.coupling T.ρA T.side u B (Y, i) ^ 2 +
        fitSlope T.coupling T.ρA T.side u B (Y - unitStep n i, i) ^ 2) +
        2 * ∑ i : Fin 4, (fitSlope T.coupling T.ρA T.side u B (Y, i) * fitSlope T.coupling T.ρA T.side u B' (Y, i) +
          fitSlope T.coupling T.ρA T.side u B (Y - unitStep n i, i) *
            fitSlope T.coupling T.ρA T.side u B' (Y - unitStep n i, i)) +
        ∑ i : Fin 4, (fitSlope T.coupling T.ρA T.side u B' (Y, i) ^ 2 +
          fitSlope T.coupling T.ρA T.side u B' (Y - unitStep n i, i) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fitSlope_add, fitSlope_add]
    ring
  rw [l1, t1, t2] at e1
  linear_combination (1 / 2) * e1 - (1 / 2) * e2 - (1 / 2) * e3
private theorem shareHessian_succ (u n : ℕ) [NeZero n] (hn : T.n₀ ≤ n) (Y : TorusSite n) (c c' : TorusBond n) :
    shareHessian T.coupling T.side (u + 1) Y c c' =
      ∑ y ∈ TorusLumps.sitesInBlocks T.side {Y},
        pullbackForm T.coupling T.ρA T.side u (shareHessian T.coupling T.side u y) c c' +
      T.coupling / 2 * ∑ i : Fin 4,
        (fitDefect T.side T.coupling T.ρA u (Y, i) c * fitDefect T.side T.coupling T.ρA u (Y, i) c' +
          fitDefect T.side T.coupling T.ρA u (Y - unitStep n i, i) c *
            fitDefect T.side T.coupling T.ρA u (Y - unitStep n i, i) c') := by
  classical
  have hnL : T.n₀ ≤ n * T.side :=
    hn.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne T.side)))
  have hf := (levelShare_angle_facts hS T hD (u + 1) hn Y).1
  have hM : ∀ e : TorusBond n, responseMap T.coupling T.ρA T.side u (Pi.single e 1) =
      fun b => responseKernel T.coupling T.ρA T.side u b e := by
    intro e
    funext b
    unfold responseMap
    rw [Finset.sum_eq_single e]
    · simp
    · intro c₀ _ hc
      simp [hc]
    · simp
  have hs : ∀ (e c₀ : TorusBond n),
      fitSlope T.coupling T.ρA T.side u (Pi.single e 1) c₀ = fitDefect T.side T.coupling T.ρA u c₀ e := by
    intro e c₀
    unfold fitSlope fitDefect bondIndicator
    rw [hM e]
    congr 1
    by_cases h : c₀ = e
    · subst h
      simp
    · simp [h]
  show hessianAtIdentity (levelShare T.coupling T.side (u + 1) Finset.univ Y) c c' = _
  rw [hessianAtIdentity_apply_eq hf, levelShare_hessian_polar hC hSp hS T hD u n hn Y]
  simp only [hs]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun y _ => ?_) ?_
  · rw [← bilinearEval_hessian_eq (levelShare_angle_facts hS T hD u hnL y).1, hM, hM]
    rfl
  · ring
end Step
section Assembly
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (A : ∀ t, ResponseSetup (T.stage t).toStepSetup)
private theorem pullbackForm_linearComb (a ρ : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (κ : ℝ)
    (q r : BondBilinear (n * L)) (c c' : TorusBond n) :
    pullbackForm a ρ L u (n := n) (fun b b' => κ * q b b' + r b b') c c' =
      κ * pullbackForm a ρ L u q c c' + pullbackForm a ρ L u r c c' := by
  unfold pullbackForm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem sum_shift_aux {ι : Type*} (S : Finset ι) (H C R : ι → ℝ) (K X : ℝ) :
    K * (∑ y ∈ S, C y + X) + ∑ y ∈ S, ((H y - K) * C y + R y) = ∑ y ∈ S, (H y * C y + R y) + K * X := by
  have e : ∑ y ∈ S, ((H y - K) * C y + R y) = ∑ y ∈ S, (H y * C y + R y) - K * ∑ y ∈ S, C y := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  ring
private theorem classicalQuadratic_succ_of (t n : ℕ) [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (T.stage (t + 1)).depth n)) (Y : TorusSite n) (c c' : TorusBond n) (X : ℝ)
    (H : shareHessian ℓ.coupling ℓ.side ((T.stage t).depth + 1) Y c c' =
      ∑ y ∈ TorusLumps.sitesInBlocks ℓ.side {Y}, pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side
        (T.stage t).depth (shareHessian ℓ.coupling ℓ.side (T.stage t).depth y) c c' + X) :
    classicalQuadratic T A (t + 1) n h Y c c' =
      ∑ y ∈ TorusLumps.sitesInBlocks ℓ.side {Y}, pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side
        (T.stage t).depth (classicalQuadratic T A t (n * ℓ.side) h y) c c' +
      WeightedResponses.blockMean ℓ.side ((T.stage t).depth + 1) n Y h * X := by
  show WeightedResponses.blockMean ℓ.side ((T.stage t).depth + 1) n Y h *
        shareHessian ℓ.coupling ℓ.side ((T.stage t).depth + 1) Y c c' +
      ∑ y ∈ TorusLumps.sitesInBlocks ℓ.side {Y}, pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side
        (T.stage t).depth (n := n) (fun b b' =>
        (WeightedResponses.blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h -
            WeightedResponses.blockMean ℓ.side ((T.stage t).depth + 1) n Y h) *
            shareHessian ℓ.coupling ℓ.side (T.stage t).depth y b b' +
          classicalRemainder T A t (n * ℓ.side) h y b b') c c' = _
  rw [H]
  have e : ∀ y, pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth (n := n)
      (classicalQuadratic T A t (n * ℓ.side) h y) c c' =
      WeightedResponses.blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h *
          pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth
            (shareHessian ℓ.coupling ℓ.side (T.stage t).depth y) c c' +
        pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth
          (classicalRemainder T A t (n * ℓ.side) h y) c c' :=
    fun y => pullbackForm_linearComb _ _ _ _ _ _ _ _ _
  simp only [pullbackForm_linearComb, e]
  exact sum_shift_aux _ (fun y => WeightedResponses.blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h)
    (fun y => pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth
      (shareHessian ℓ.coupling ℓ.side (T.stage t).depth y) c c')
    (fun y => pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth
      (classicalRemainder T A t (n * ℓ.side) h y) c c') _ _
end Assembly
end RecursionLemmas
open RecursionLemmas in
theorem classicalQuadraticRecursion_holds (hC : minimizerCurveStatement)
    (hSp : LevelShareSplits) (hS : LevelSharesFormCurvatureFamily) :
    classicalQuadraticRecursionStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  refine ⟨0, fun y _ _ _ g _ _ k _ _ _ R d _ => ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S => ?_⟩⟩
  have h0 : (S.tower.stage 0).anchorRadius = Tb.ρA := by
    have e := congrArg (fun z : ResponseInTheExpansion.StageWithResponse (Tb.stepParameters y) => z.1.anchorRadius)
      (S.stage_eq 0 (Nat.zero_le _))
    exact e.trans S.isInitial.anchorRadius_eq
  have hρ : ∀ t, (S.tower.stage t).anchorRadius = Tb.ρA := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => exact ih
  have ht0 : (S.tower.stage 0).depth = 0 := S.startsAtWilson.depth_eq
  refine ⟨?_, ?_⟩
  · intro t _ n _ hn h Y c c'
    have H := shareHessian_succ hC hSp hS Tb hD (S.tower.stage t).depth n hn Y c c'
    rw [← hρ t] at H
    have K := classicalQuadratic_succ_of S.tower S.resp t n h Y c c' _ H
    refine K.trans ?_
    refine congrArg₂ (· + ·) rfl ?_
    have aux : ∀ p q r : ℝ, p * (q * r) = q * p * r := fun p q r => by ring
    exact aux _ _ _
  · intro n _ hn h h' hh A
    have hone : HEq (constOneWeight n)
        (constOneWeight (fineSide (Tb.stepParameters y).side (S.tower.stage 0).depth n)) := by
      have e : n = fineSide (Tb.stepParameters y).side (S.tower.stage 0).depth n := by
        rw [ht0]
        rfl
      exact congr_arg_heq constOneWeight e
    have each : ∀ z : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp 0 n h' z) A A =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexMultiplicity z p / 4 * h p * curl A p ^ 2 := by
      intro z
      have hs : shareHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side (S.tower.stage 0).depth z =
          hessianAtIdentity fun W => siteResponse z W (constOneWeight n) := by
        unfold shareHessian
        rw [ht0, levelShare_zero]
      set κ := WeightedResponses.blockMean (Tb.stepParameters y).side (S.tower.stage 0).depth n z h' with hκ
      have e1 : classicalQuadratic S.tower S.resp 0 n h' z = fun b b' =>
          κ * (hessianAtIdentity fun W => siteResponse z W (constOneWeight n)) b b' +
            hessianAtIdentity (responseRemainder (S.resp 0).cold n z h') b b' := by
        funext b b'
        show κ * shareHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side
          (S.tower.stage 0).depth z b b' + _ = _
        rw [hs]
        rfl
      rw [e1, bilinearEval_linearComb]
      refine bilinearEval_level_zero κ z h (fun W => ?_) A
      unfold responseRemainder
      rw [S.cold_zero n z W h h' hh, S.cold_zero n z W (constOneWeight n) _ hone]
    simp only [each]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e2 : ∀ z : TorusSite n, vertexMultiplicity z p / 4 * h p * curl A p ^ 2 =
        (vertexMultiplicity z p / 4) * (h p * curl A p ^ 2) := fun z => by ring
    simp only [e2]
    rw [← Finset.sum_mul, sum_vertexMultiplicity_div, one_mul]
end MomentLaw
end YangMills.Construction
end
