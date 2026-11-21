import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvature
import YangMills.Construction.ResponseInTheExpansion.KernelsCarriedFromAMirror
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages hiding unitStep adjointAction
open LumpContours ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps
namespace ResponseInTheExpansion
open Classical
open MirrorKernels
namespace ColdMirrorFunctionals
variable {n : ℕ}
theorem exists_adjointAction_eq_neg (X : imaginaryQuaternions) :
    ∃ u : UnitQuaternion, _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X = -X := by
  obtain ⟨p, r, hN, hd⟩ : ∃ p r : ℝ, p ^ 2 + r ^ 2 = 1 ∧ p * (X : ℍ[ℝ]).imI + r * (X : ℍ[ℝ]).imJ = 0 := by
    set a := (X : ℍ[ℝ]).imI
    set b := (X : ℍ[ℝ]).imJ
    by_cases h : a ^ 2 + b ^ 2 = 0
    · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact ⟨1, 0, by norm_num, by simp [ha]⟩
    · have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hs : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hpos.le
      have hs0 : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      refine ⟨b / Real.sqrt (a ^ 2 + b ^ 2), -a / Real.sqrt (a ^ 2 + b ^ 2), ?_, ?_⟩
      · field_simp
        nlinarith
      · field_simp
        ring
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  obtain ⟨q, q0, q1, q2, q3⟩ : ∃ q : ℍ[ℝ], q.re = 0 ∧ q.imI = p ∧ q.imJ = r ∧ q.imK = 0 :=
    ⟨⟨0, p, r, 0⟩, rfl, rfl, rfl, rfl⟩
  have hu : q ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor <;> ext <;> simp [q0, q1, q2, q3] <;> nlinarith
  refine ⟨⟨q, hu⟩, ?_⟩
  apply Subtype.ext
  show q * (X : ℍ[ℝ]) * star q = -(X : ℍ[ℝ])
  ext
  · simp [q0, q1, q2, q3, hre]
    ring
  · simp [q0, q1, q2, q3, hre]
    linear_combination (2 * p) * hd - (X : ℍ[ℝ]).imI * hN
  · simp [q0, q1, q2, q3, hre]
    linear_combination (2 * r) * hd - (X : ℍ[ℝ]).imJ * hN
  · simp [q0, q1, q2, q3, hre]
    linear_combination -(X : ℍ[ℝ]).imK * hN
theorem gaugeTransform_perturb_trivialField [NeZero n] {u : UnitQuaternion} {c : Fin 1 → TorusBond n}
    {X : Fin 1 → imaginaryQuaternions} (hu : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u (X 0) = -X 0) (τ : Fin 1 → ℝ) :
    TorusFields.gaugeTransform (fun _ => u) (perturb c X τ (trivialField n)) = perturb c X (-τ) (trivialField n) := by
  funext x i
  show u * (expUnit (∑ l, if c l = (x, i) then τ l • X l else 0) * 1) * u⁻¹ =
    expUnit (∑ l, if c l = (x, i) then (-τ) l • X l else 0) * 1
  rw [mul_one, mul_one, ← Adjoint.expUnit_adjointAction, Fin.sum_univ_one, Fin.sum_univ_one]
  congr 1
  by_cases h : c 0 = (x, i)
  · simp only [h, if_true]
    have e : (-τ) 0 • X 0 = τ 0 • (-X 0) := by
      apply Subtype.ext
      show ((-τ) 0) • (X 0 : ℍ[ℝ]) = τ 0 • (-(X 0 : ℍ[ℝ]))
      rw [Pi.neg_apply, neg_smul, smul_neg]
    rw [Adjoint.adjointAction_smul, hu, e]
  · simp only [h, if_false]
    exact Adjoint.adjointAction_zero u
theorem eventually_isCold_perturb_trivialField [NeZero n] {c : Fin 1 → TorusBond n}
    {X : Fin 1 → imaginaryQuaternions} {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ τ : Fin 1 → ℝ in 𝓝 0, IsCold σ (perturb c X τ (trivialField n)) := by
  have hcont : Continuous fun τ : Fin 1 → ℝ => 4 * (|τ 0| * ‖(X 0 : ℍ[ℝ])‖) := by fun_prop
  have h0 : (4 * (|(0 : Fin 1 → ℝ) 0| * ‖(X 0 : ℍ[ℝ])‖)) < σ := by simpa using hσ
  filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds h0)] with τ hτ
  intro x μ ν _
  have h := TopLevelSites.curvature_le_add (perturb c X τ (trivialField n)) (trivialField n) x μ ν
  have h0 : curvature (trivialField n) x μ ν = 0 := by simp [curvature, holonomy, trivialField]
  have hb : ∀ (y : TorusSite n) (i : Fin 4),
      ‖((perturb c X τ (trivialField n) y i : UnitQuaternion) : ℍ[ℝ]) -
        ((trivialField n y i : UnitQuaternion) : ℍ[ℝ])‖ ≤ |τ 0| * ‖(X 0 : ℍ[ℝ])‖ := by
    intro y i
    show ‖((expUnit (∑ l, if c l = (y, i) then τ l • X l else 0) * 1 : UnitQuaternion) : ℍ[ℝ]) -
      ((1 : UnitQuaternion) : ℍ[ℝ])‖ ≤ _
    rw [mul_one, Fin.sum_univ_one, OneMemClass.coe_one]
    refine (TorusFrame.norm_expUnit_sub_one_le _).trans ?_
    by_cases hc : c 0 = (y, i)
    · rw [if_pos hc]
      show ‖τ 0 • (X 0 : ℍ[ℝ])‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
    · rw [if_neg hc]
      show ‖(0 : ℍ[ℝ])‖ ≤ _
      rw [norm_zero]
      positivity
  have a1 := hb x μ
  have a2 := hb (x + unitStep n μ) ν
  have a3 := hb (x + unitStep n ν) μ
  have a4 := hb x ν
  linarith
theorem mixedDeriv_one_eq_zero_of_gauge_invariant [NeZero n] {G : TorusField n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W →
      G (TorusFields.gaugeTransform g W) = G W)
    (hC : ContDiffThreeAt G (trivialField n)) (c : Fin 1 → TorusBond n) (X : Fin 1 → imaginaryQuaternions) :
    mixedDeriv G (trivialField n) c X = 0 := by
  obtain ⟨u, hu⟩ := exists_adjointAction_eq_neg (X 0)
  set f : (Fin 1 → ℝ) → ℝ := fun τ => G (perturb c X τ (trivialField n)) with hf
  have hd : DifferentiableAt ℝ f 0 := (hC 1 c X).differentiableAt (by norm_num)
  have he : f =ᶠ[𝓝 0] fun τ => f (-τ) := by
    filter_upwards [eventually_isCold_perturb_trivialField (c := c) (X := X) hσ] with τ hτ
    have := hg (fun _ => u) _ hτ
    rw [gaugeTransform_perturb_trivialField hu] at this
    exact this.symm
  have h1 : fderiv ℝ f 0 = fderiv ℝ (fun τ => f (-τ)) 0 := he.fderiv_eq
  have hn : HasFDerivAt (fun τ : Fin 1 → ℝ => -τ) (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0 :=
    (hasFDerivAt_id _).neg
  have hd' : HasFDerivAt f (fderiv ℝ f 0) (-(0 : Fin 1 → ℝ)) := by
    simpa using hd.hasFDerivAt
  have h3 : HasFDerivAt (fun τ => f (-τ)) ((fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ))) 0 :=
    hd'.comp 0 hn
  rw [h3.fderiv] at h1
  have h2 : ∀ v, fderiv ℝ f 0 v = 0 := by
    intro v
    have := congrArg (fun L : (Fin 1 → ℝ) →L[ℝ] ℝ => L v) h1
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg] at this
    linarith
  unfold mixedDeriv
  rw [iteratedFDeriv_one_apply]
  exact h2 _
theorem mixedDeriv_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
theorem mixedDeriv_sub_const {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) {F : TorusField n → ℝ} {W : TorusField n}
    (hC : ContDiffThreeAt F W) (κ : ℝ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun V => F V - κ) W c X = mixedDeriv F W c X := by
  unfold mixedDeriv
  have h1 : ContDiffAt ℝ k (fun σ : Fin k → ℝ => F (perturb c X σ W)) 0 :=
    (hC k c X).of_le (by exact_mod_cast hk3)
  have h2 : ContDiffAt ℝ k (fun _ : Fin k → ℝ => -κ) 0 := contDiffAt_const
  have h3 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (x := (0 : Fin k → ℝ)) h1 h2
  have e : (fun σ : Fin k → ℝ => F (perturb c X σ W) - κ) =
      (fun σ : Fin k → ℝ => F (perturb c X σ W)) + fun _ : Fin k → ℝ => -κ := by
    funext σ
    simp [sub_eq_add_neg]
  have h4 : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => -κ) = 0 := iteratedFDeriv_const_of_ne (by omega) (-κ)
  rw [e, h3, h4]
  simp
theorem contDiffThreeAt_sub_const {F : TorusField n → ℝ} {W : TorusField n} (hC : ContDiffThreeAt F W) (κ : ℝ) :
    ContDiffThreeAt (fun V => F V - κ) W :=
  fun k c X => (hC k c X).sub contDiffAt_const
theorem weightRate_pos {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) : 0 < ℓ.weightRate := by apply _root_.YangMills.Construction.AbelianSecondOrder.weightRate_pos <;> assumption
theorem one_div_weight_le_exp {ℓ : TorusLumps.StepParameters} (_hfit : ℓ.Admissible) (m : ℕ) :
    1 / ℓ.weight m ≤ Real.exp (-(ℓ.weightRate * m)) := by
  have he := Real.exp_pos (ℓ.weightRate * m)
  have hw : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by
    unfold TorusLumps.StepParameters.weight
    exact le_mul_of_one_le_left he.le (le_max_left _ _)
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ he hw
theorem isCold_trivialField [NeZero n] {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField n) := by apply _root_.YangMills.Construction.ImageDensities.isCold_trivialField <;> assumption
theorem isLocalGaugeFunctional_sub_trivial {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) [NeZero n]
    {K ρ₀ : ℝ} {F : TorusField n → ℝ} {y : TorusSite n} (hρ₀ : 2 ≤ ρ₀) (hK : 0 ≤ K)
    (hs : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt F W)
    (hg : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold ℓ.threshold W →
      F (TorusFields.gaugeTransform g W) = F W)
    (hd : ∀ W, IsCold ℓ.threshold W → ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      1 ≤ k → k ≤ 3 → AreUnitVectors X → |mixedDeriv F W c X| ≤ K / ℓ.weight (supportDiam y c))
    (hc : ∀ W W', IsCold ℓ.threshold W → IsCold ℓ.threshold W' → FieldsAgreeNear W W' y y ⌊ρ₀⌋₊ →
      |(F W - F (trivialField n)) - (F W' - F (trivialField n))| ≤ K / ℓ.weight ⌊ρ₀⌋₊) :
    IsLocalGaugeFunctional ℓ.threshold K ℓ.weightRate (ℓ.weightRate / 2) ρ₀
      (fun W => F W - F (trivialField n)) y := by
  have hσ := hfit.σ_pos
  have hr := weightRate_pos hfit
  have hw : ∀ m : ℕ, K / ℓ.weight m ≤ K * Real.exp (-(ℓ.weightRate * m)) := fun m => by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_weight_le_exp hfit m) hK
  refine ⟨fun W hW => contDiffThreeAt_sub_const (hs W hW) _, fun g W hW => by simp only [hg g W hW], ?_, ?_,
    by simp, ?_⟩
  · intro W hW k b X h1 h3 hX
    rw [mixedDeriv_sub_const h1 h3 (hs W hW)]
    exact (hd W hW k b X h1 h3 hX).trans (hw _)
  · intro W W' hW hW' hag
    refine (hc W W' hW hW' hag).trans ((hw _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK))
    have h1 : ρ₀ < (⌊ρ₀⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ρ₀
    nlinarith
  · exact mixedDeriv_one_eq_zero_of_gauge_invariant hσ (fun g W hW => by simp only [hg g W hW])
      (contDiffThreeAt_sub_const (hs _ (isCold_trivialField hσ)) _)
def restrictKernel {N : ℕ} (S : Finset (TorusPlaquette N)) (κ : TorusPlaquette N → TorusPlaquette N → ℝ)
    (a b : TorusPlaquette N) : ℝ :=
  if a ∈ S ∧ b ∈ S then κ a b else 0
theorem kernelQuadraticForm_restrictKernel [NeZero n] (κ : TorusPlaquette n → TorusPlaquette n → ℝ)
    (y : TorusSite n) (ρ₀ : ℝ) (F : TorusPlaquette n → imaginaryQuaternions) :
    kernelQuadraticForm (restrictKernel (plaquettesIn (supBall y ρ₀)) κ) y ρ₀ F = kernelQuadraticForm κ y ρ₀ F := by
  unfold kernelQuadraticForm
  congr 1
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
  rw [restrictKernel, if_pos ⟨hp, hp'⟩]
theorem isQuadraticInCurvature_restrictKernel [NeZero n] {σ C c K ρ₀ : ℝ} {G : TorusField n → ℝ}
    {y : TorusSite n} {κ : TorusPlaquette n → TorusPlaquette n → ℝ}
    (h : IsQuadraticInCurvature σ C c K ρ₀ G y κ) :
    IsQuadraticInCurvature σ C c K ρ₀ G y (restrictKernel (plaquettesIn (supBall y ρ₀)) κ) := by
  intro g W s h1 h2 h3 h4
  rw [kernelQuadraticForm_restrictKernel]
  exact h g W s h1 h2 h3 h4
section Site
variable {m : ℕ} [NeZero n] [NeZero (4 * m)]
theorem translatePlaquette_mem_plaquettesIn (z : TorusSite n) (o : TorusSite n) {r ρ : ℝ} (hρ : ρ + 1 ≤ m)
    (hb : ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) {a : TorusPlaquette (4 * m)}
    (ha : a ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) :
    translatePlaquette z a ∈ plaquettesIn (supBall o r) := by
  have hc := (Finset.mem_filter.mp ha).2.2
  have c0 : a.1 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
  have c1 : a.1 + unitStep (4 * m) a.2.1 ∈ supBall (0 : TorusSite (4 * m)) ρ :=
    hc _ (by simp [plaquetteVertices])
  have c2 : a.1 + unitStep (4 * m) a.2.2 ∈ supBall (0 : TorusSite (4 * m)) ρ :=
    hc _ (by simp [plaquetteVertices])
  have c3 : a.1 + unitStep (4 * m) a.2.1 + unitStep (4 * m) a.2.2 ∈ supBall (0 : TorusSite (4 * m)) ρ :=
    hc _ (by simp [plaquetteVertices])
  have hin : ∀ x ∈ supBall (0 : TorusSite (4 * m)) ρ,
      z + siteOfInt (MirrorDensities.offset 0 x) ∈ supBall o r := by
    intro x hx
    apply hb
    have : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt (MirrorDensities.offset 0 x)) z ≤ _root_.YangMills.Construction.TorusFields.supDist x (0 : TorusSite (4 * m)) :=
      _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_translatePlaquette_le z (x, 0, 0)
    exact le_trans (by exact_mod_cast this) (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_le_of_mem_supBall hx)
  have hn : ∀ (x : TorusSite (4 * m)), x ∈ supBall (0 : TorusSite (4 * m)) ρ → ∀ i,
      z + siteOfInt (MirrorDensities.offset 0 (x + unitStep (4 * m) i)) =
        z + siteOfInt (MirrorDensities.offset 0 x) + unitStep n i := fun x hx i => by
    rw [offset_add_unitStep i (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_one_le_of_mem_supBall hx hρ), add_siteOfInt_add,
      ← unitStep_eq_siteOfInt]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1, ?_⟩
  intro c hcm
  simp only [plaquetteVertices, translatePlaquette, List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl | rfl
  · exact hin _ c0
  · rw [← hn _ c0]
    exact hin _ c1
  · rw [← hn _ c0]
    exact hin _ c2
  · rw [← hn _ c0, ← hn _ c1]
    exact hin _ c3
theorem norm_lieFormCurl_ballLog_le (g : TorusSite n → UnitQuaternion) (W : TorusField n) (o : TorusSite n)
    {r s : ℝ}
    (hs : ∀ b : TorusBond n, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    {p : TorusPlaquette n} (hp : p ∈ plaquettesIn (supBall o r)) :
    ‖((lieFormCurl (ballLog g W o r) p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 4 * s := by
  have hc := (Finset.mem_filter.mp hp).2.2
  have c0 : p.1 ∈ supBall o r := hc _ (by simp [plaquetteVertices])
  have c1 : p.1 + unitStep n p.2.1 ∈ supBall o r := hc _ (by simp [plaquetteVertices])
  have c2 : p.1 + unitStep n p.2.2 ∈ supBall o r := hc _ (by simp [plaquetteVertices])
  have hB : ∀ (x : TorusSite n) (i : Fin 4), x ∈ supBall o r → ‖(ballLog g W o r (x, i) : ℍ[ℝ])‖ ≤ s := by
    intro x i hx
    unfold ballLog
    rw [if_pos hx]
    exact hs (x, i) hx
  have e : ((lieFormCurl (ballLog g W o r) p : imaginaryQuaternions) : ℍ[ℝ]) =
      (ballLog g W o r (p.1, p.2.1) : ℍ[ℝ]) + (ballLog g W o r (p.1 + unitStep n p.2.1, p.2.2) : ℍ[ℝ]) -
        (ballLog g W o r (p.1 + unitStep n p.2.2, p.2.1) : ℍ[ℝ]) - (ballLog g W o r (p.1, p.2.2) : ℍ[ℝ]) := rfl
  rw [e]
  have a1 := hB _ p.2.1 c0
  have a2 := hB _ p.2.2 c1
  have a3 := hB _ p.2.1 c2
  have a4 := hB _ p.2.2 c0
  refine (norm_sub_le _ _).trans ?_
  have b1 := norm_sub_le ((ballLog g W o r (p.1, p.2.1) : ℍ[ℝ]) +
    (ballLog g W o r (p.1 + unitStep n p.2.1, p.2.2) : ℍ[ℝ])) (ballLog g W o r (p.1 + unitStep n p.2.2, p.2.1) : ℍ[ℝ])
  have b2 := norm_add_le (ballLog g W o r (p.1, p.2.1) : ℍ[ℝ])
    (ballLog g W o r (p.1 + unitStep n p.2.1, p.2.2) : ℍ[ℝ])
  linarith
theorem abs_sub_mirror_form_le {σ C c K ρ s e₁ D d r : ℝ} {G : TorusField (4 * m) → ℝ}
    {κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ}
    (hExp : IsQuadraticInCurvature σ C c K ρ G 0 κ) (hd : 0 < d) (hD : 0 ≤ D)
    (hκ : ∀ a ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ), ∀ b ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ),
      |κ a b| ≤ D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ))))
    (z : TorusSite n) (W : TorusField n) (g : TorusSite n → UnitQuaternion) (o : TorusSite n) (hm : 2 ≤ m)
    (hρ : ρ + 1 ≤ m) (hb : ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) (hs0 : 0 ≤ s)
    (h5 : 5 * (4 * s) ≤ σ)
    (hs : ∀ b : TorusBond n, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    (hcold : IsCold σ (TorusMirror.mirrorField m z W)) (Φ : TorusPlaquette n → imaginaryQuaternions) (he₁ : 0 ≤ e₁)
    (he : ∀ p ∈ plaquettesIn (supBall o r),
      ‖((lieFormCurl (ballLog g W o r) p - Φ p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ e₁) :
    |G (TorusMirror.mirrorField m z W) - (1 / 2) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
          translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ p p' * lieInner (Φ p) (Φ p')| ≤
      C * K * ((4 * s) ^ 3 + Real.exp (-(c * ρ))) +
        3 / 2 * (D * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2) * (e₁ * (8 * s + e₁)) := by
  set S := plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ) with hS
  have hSord : ∀ a ∈ S, a.2.1 < a.2.2 := fun a ha => (Finset.mem_filter.mp ha).2.1
  have hnear := isNearIdentity_mirrorField z W g o hm hρ hb hs0 hs
  have h1 := hExp (mirrorGauge z g) (TorusMirror.mirrorField m z W) (4 * s) (by positivity) h5 hcold hnear
  have e1 : kernelQuadraticForm κ 0 ρ
        (lieFormCurl (ballLog (mirrorGauge z g) (TorusMirror.mirrorField m z W) 0 ρ)) =
      (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, κ a b *
        lieInner (lieFormCurl (ballLog g W o r) (translatePlaquette z a))
          (lieFormCurl (ballLog g W o r) (translatePlaquette z b)) := by
    unfold kernelQuadraticForm
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb' => ?_
    rw [lieFormCurl_mirrorField z W g o hm hρ hb ha, lieFormCurl_mirrorField z W g o hm hρ hb hb', lieInner]
  rw [e1] at h1
  have e2 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        translatedKernel S z κ p p' * lieInner (Φ p) (Φ p') =
      ∑ a ∈ S, ∑ b ∈ S, κ a b * lieInner (Φ (translatePlaquette z a)) (Φ (translatePlaquette z b)) :=
    sum_translatedKernel_mul S z κ (fun p p' => lieInner (Φ p) (Φ p')) hSord
  rw [e2]
  have hbound : ∀ a ∈ S, ∀ b ∈ S,
      |lieInner (lieFormCurl (ballLog g W o r) (translatePlaquette z a))
          (lieFormCurl (ballLog g W o r) (translatePlaquette z b)) -
        lieInner (Φ (translatePlaquette z a)) (Φ (translatePlaquette z b))| ≤ 3 * (e₁ * (8 * s + e₁)) / 1 := by
    intro a ha b hb'
    have ma := translatePlaquette_mem_plaquettesIn z o hρ hb ha
    have mb := translatePlaquette_mem_plaquettesIn z o hρ hb hb'
    have n1 := norm_lieFormCurl_ballLog_le g W o hs ma
    have n2 := norm_lieFormCurl_ballLog_le g W o hs mb
    have d1 := he _ ma
    have d2 := he _ mb
    have n3 : ‖((Φ (translatePlaquette z a) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 4 * s + e₁ := by
      have e3 : ((Φ (translatePlaquette z a) : imaginaryQuaternions) : ℍ[ℝ]) =
          ((lieFormCurl (ballLog g W o r) (translatePlaquette z a) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((lieFormCurl (ballLog g W o r) (translatePlaquette z a) - Φ (translatePlaquette z a) :
            imaginaryQuaternions) : ℍ[ℝ]) := by
        simp
      rw [e3]
      exact (norm_sub_le _ _).trans (add_le_add n1 d1)
    refine (abs_lieInner_sub_le _ _ _ _).trans ?_
    rw [div_one]
    have m1 := mul_le_mul d1 n2 (norm_nonneg _) he₁
    have m2 := mul_le_mul n3 d2 (norm_nonneg _) (by positivity : 0 ≤ 4 * s + e₁)
    nlinarith
  have hsum := sum_abs_kernel_le_sq S κ hd hD hκ
  have hdiff : |(1 / 2) * ∑ a ∈ S, ∑ b ∈ S, κ a b *
        lieInner (lieFormCurl (ballLog g W o r) (translatePlaquette z a))
          (lieFormCurl (ballLog g W o r) (translatePlaquette z b)) -
      (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, κ a b * lieInner (Φ (translatePlaquette z a)) (Φ (translatePlaquette z b))| ≤
      3 / 2 * (D * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2) * (e₁ * (8 * s + e₁)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
    have : |∑ a ∈ S, (∑ b ∈ S, κ a b *
          lieInner (lieFormCurl (ballLog g W o r) (translatePlaquette z a))
            (lieFormCurl (ballLog g W o r) (translatePlaquette z b)) -
        ∑ b ∈ S, κ a b * lieInner (Φ (translatePlaquette z a)) (Φ (translatePlaquette z b)))| ≤
        ∑ a ∈ S, ∑ b ∈ S, |κ a b| * (3 * (e₁ * (8 * s + e₁))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb' => ?_)
      rw [← mul_sub, abs_mul]
      have := hbound a ha b hb'
      rw [div_one] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have h2 : ∑ a ∈ S, ∑ b ∈ S, |κ a b| * (3 * (e₁ * (8 * s + e₁))) =
        (∑ a ∈ S, ∑ b ∈ S, |κ a b|) * (3 * (e₁ * (8 * s + e₁))) := by
      simp only [Finset.sum_mul]
    rw [h2] at this
    have h3 := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 3 * (e₁ * (8 * s + e₁)))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith
  have h4 := abs_sub_le (G (TorusMirror.mirrorField m z W))
    ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, κ a b *
        lieInner (lieFormCurl (ballLog g W o r) (translatePlaquette z a))
          (lieFormCurl (ballLog g W o r) (translatePlaquette z b)))
    ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, κ a b * lieInner (Φ (translatePlaquette z a)) (Φ (translatePlaquette z b)))
  linarith
end Site
section Sum
variable [NeZero n]
def plaquetteForm (Φ : TorusPlaquette n → imaginaryQuaternions) (K : TorusPlaquette n → TorusPlaquette n → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
    ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), K p p' * lieInner (Φ p) (Φ p')
theorem plaquetteForm_linear (Φ : TorusPlaquette n → imaginaryQuaternions) (a b : ℝ)
    (K K' : TorusPlaquette n → TorusPlaquette n → ℝ) :
    plaquetteForm Φ (fun p p' => a * K p p' + b * K' p p') = a * plaquetteForm Φ K + b * plaquetteForm Φ K' := by
  unfold plaquetteForm
  rw [mul_left_comm a, mul_left_comm b, ← mul_add]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p' _ => ?_
  ring
theorem abs_sum_sub_plaquetteForm_le (B : Finset (TorusSite n)) (hh : TorusSite n → ℝ) (al : ℝ)
    (ka k1 k2 : TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ)
    (Φ : TorusPlaquette n → imaginaryQuaternions) (v g0 g1 g2 : TorusSite n → ℝ) {E0 E1 E2 : ℝ}
    (hoff : ∀ z, z ∉ B → hh z = 0) (hh1 : ∀ z ∈ B, |hh z| ≤ 1) (hal : |al| ≤ 2)
    (hv : ∀ z ∈ B, v z = hh z * (al * g0 z + g1 z) + g2 z)
    (h0 : ∀ z ∈ B, |g0 z - plaquetteForm Φ (ka z)| ≤ E0) (h1 : ∀ z ∈ B, |g1 z - plaquetteForm Φ (k1 z)| ≤ E1)
    (h2 : ∀ z ∈ B, |g2 z - plaquetteForm Φ (k2 z)| ≤ E2) :
    |∑ z ∈ B, v z - (1 / 2) * ∑ z, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (hh z * al * ka z p p' + (if z ∈ B then hh z * k1 z p p' + k2 z p p' else 0)) *
          ∑ e : Fin 3, imaginaryComponent e (Φ p) * imaginaryComponent e (Φ p')| ≤
      B.card * (2 * E0 + E1 + E2) := by
  have hz : ∀ z, (1 / 2 : ℝ) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (hh z * al * ka z p p' + (if z ∈ B then hh z * k1 z p p' + k2 z p p' else 0)) *
          ∑ e : Fin 3, imaginaryComponent e (Φ p) * imaginaryComponent e (Φ p') =
      if z ∈ B then hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z)
      else 0 := by
    intro z
    by_cases hzB : z ∈ B
    · rw [if_pos hzB]
      have e1 := plaquetteForm_linear Φ (hh z * al) 1 (ka z) (fun p p' => hh z * k1 z p p' + k2 z p p')
      have e2 := plaquetteForm_linear Φ (hh z) 1 (k1 z) (k2 z)
      simp only [one_mul] at e1 e2
      have e3 : hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z) =
          hh z * al * plaquetteForm Φ (ka z) + plaquetteForm Φ (fun p p' => hh z * k1 z p p' + k2 z p p') := by
        rw [e2]
        ring
      rw [e3, ← e1]
      unfold plaquetteForm lieInner
      simp only [if_pos hzB]
    · rw [if_neg hzB, hoff z hzB]
      simp [hzB]
  have hsum : (1 / 2 : ℝ) * ∑ z, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (hh z * al * ka z p p' + (if z ∈ B then hh z * k1 z p p' + k2 z p p' else 0)) *
          ∑ e : Fin 3, imaginaryComponent e (Φ p) * imaginaryComponent e (Φ p') =
      ∑ z ∈ B, (hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z)) := by
    rw [Finset.mul_sum]
    simp only [hz]
    rw [Finset.sum_ite_mem]
    simp
  rw [hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ z ∈ B,
      |v z - (hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z))| ≤
        2 * E0 + E1 + E2 := by
    intro z hzB
    rw [hv z hzB]
    have e : hh z * (al * g0 z + g1 z) + g2 z -
        (hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z)) =
        hh z * al * (g0 z - plaquetteForm Φ (ka z)) + hh z * (g1 z - plaquetteForm Φ (k1 z)) +
          (g2 z - plaquetteForm Φ (k2 z)) := by
      ring
    rw [e]
    have a0 := h0 z hzB
    have a1 := h1 z hzB
    have a2 := h2 z hzB
    have a3 := hh1 z hzB
    have b1 : |hh z * al * (g0 z - plaquetteForm Φ (ka z))| ≤ 2 * E0 := by
      rw [abs_mul, abs_mul]
      have : |hh z| * |al| ≤ 1 * 2 := mul_le_mul a3 hal (abs_nonneg _) (by norm_num)
      calc |hh z| * |al| * |g0 z - plaquetteForm Φ (ka z)| ≤ (1 * 2) * E0 :=
            mul_le_mul this a0 (abs_nonneg _) (by norm_num)
        _ = 2 * E0 := by ring
    have b2 : |hh z * (g1 z - plaquetteForm Φ (k1 z))| ≤ E1 := by
      rw [abs_mul]
      calc |hh z| * |g1 z - plaquetteForm Φ (k1 z)| ≤ 1 * E1 := mul_le_mul a3 a1 (abs_nonneg _) (by norm_num)
        _ = E1 := one_mul _
    have b3 := abs_add_le (hh z * al * (g0 z - plaquetteForm Φ (ka z)) + hh z * (g1 z - plaquetteForm Φ (k1 z)))
      (g2 z - plaquetteForm Φ (k2 z))
    have b4 := abs_add_le (hh z * al * (g0 z - plaquetteForm Φ (ka z))) (hh z * (g1 z - plaquetteForm Φ (k1 z)))
    linarith
  calc ∑ z ∈ B, |v z - (hh z * (al * plaquetteForm Φ (ka z) + plaquetteForm Φ (k1 z)) + plaquetteForm Φ (k2 z))|
      ≤ ∑ _z ∈ B, (2 * E0 + E1 + E2) := Finset.sum_le_sum hb
    _ = B.card * (2 * E0 + E1 + E2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
end Sum
section Bottom
variable {ℓ : TorusLumps.StepParameters}
theorem norm_minimalLog_gaugeDescent_le (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (g : TorusSite n → UnitQuaternion), IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
    ∀ b : TorusBond (fineSide ℓ.side d n), b.1 ∈ supBall o (ResponseInTheExpansion.ballRadius ℓ.side nn ρ₀ 0) →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (gaugeDescent k d n u g)
        (topField ℓ k _ (sampleBelow ℓ k d n u)) b) : ℍ[ℝ])‖ ≤ s
  | 0, n, _, u, o, g, h, b, hb => h b hb
  | d + 1, n, _, u, o, g, h, b, hb => by
    have h' : IsGaugeSmallAlong T k nn ρ₀ s d (n * ℓ.side) u.1 o
        (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) := h.2.2
    exact norm_minimalLog_gaugeDescent_le T k nn ρ₀ s d (n * ℓ.side) u.1 o _ h' b hb
end Bottom
section Kernels
variable {m : ℕ} [NeZero (4 * m)]
structure IsMirrorKernel (σ C c ρ K d D : ℝ) (G : TorusField (4 * m) → ℝ)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) : Prop where
  symm : ∀ a b, κ a b = κ b a
  eq_zero_of_far : ∀ a b, ρ < (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) ∨
    ρ < (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ) → κ a b = 0
  bound : ∀ a b, |κ a b| ≤
    D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)))
  quadratic : IsQuadraticInCurvature σ C c K ρ G 0 κ
  eq_zero_of_not_mem : ∀ a b, ¬ (a ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ) ∧
    b ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) → κ a b = 0
def HasLocalKernels (σ del C c ρ₁ : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n] (K ρ₀ : ℝ) (G : TorusField n → ℝ) (y : TorusSite n), ρ₁ ≤ ρ₀ → 2 * ρ₀ + 2 < n → 0 ≤ K →
    IsLocalGaugeFunctional σ K del (del / 2) ρ₀ G y →
    ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ, (∀ p p', κ p p' = κ p' p) ∧
      (∀ p p', ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) ∨ ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ) → κ p p' = 0) ∧
      (∀ p p', |κ p p'| ≤ C * K * Real.exp (-(del / 2 * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ)))) ∧
      IsQuadraticInCurvature σ C c K ρ₀ G y κ
theorem exists_isMirrorKernel_of_local {σ del C c ρ₁ K ρ : ℝ} (hL : HasLocalKernels σ del C c ρ₁) (hρ : ρ₁ ≤ ρ)
    (hM : 2 * ρ + 2 < ((4 * m : ℕ) : ℝ)) (hK : 0 ≤ K) {G : TorusField (4 * m) → ℝ}
    (hG : IsLocalGaugeFunctional σ K del (del / 2) ρ G 0) :
    ∃ κ, IsMirrorKernel σ C c ρ K (del / 2) (|C| * K) G κ := by
  obtain ⟨κ, h1, h2, h3, h4⟩ := hL (4 * m) K ρ G 0 hρ hM hK hG
  set S := plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ) with hS
  refine ⟨restrictKernel S κ, ⟨fun a b => ?_, fun a b h => ?_, fun a b => ?_,
    isQuadraticInCurvature_restrictKernel h4, fun a b h => ?_⟩⟩
  · unfold restrictKernel
    by_cases h : a ∈ S ∧ b ∈ S
    · rw [if_pos h, if_pos h.symm, h1]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  · unfold restrictKernel
    split_ifs
    · exact h2 a b h
    · rfl
  · unfold restrictKernel
    split_ifs
    · refine (h3 a b).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hK) (Real.exp_pos _).le)
    · rw [abs_zero]
      positivity
  · unfold restrictKernel
    rw [if_neg h]
theorem exists_isMirrorKernel_share {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) {C c ρ₁ Cs ρ : ℝ}
    (hL : HasLocalKernels ℓ.threshold ℓ.weightRate C c ρ₁) (hCs : 0 ≤ Cs) (t : ℕ)
    (hfam : IsCurvatureFamily ℓ Cs (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side t)) (hρ : ρ₁ ≤ ρ)
    (hρ2 : 2 ≤ ρ) (hM : 2 * ρ + 2 < ((4 * m : ℕ) : ℝ)) (hn : ℓ.n₀ ≤ 4 * m) :
    ∃ κ, IsMirrorKernel ℓ.threshold C c ρ Cs (ℓ.weightRate / 2) (|C| * Cs)
      (centered (ShareFamilies.levelShareFamily ℓ.coupling ℓ.side t) (4 * m) 0) κ := by
  refine exists_isMirrorKernel_of_local hL hρ hM hCs (isLocalGaugeFunctional_sub_trivial hfit hρ2 hCs
    (fun W hW => hfam.smooth _ hn 0 W hW) (fun g W hW => hfam.gauge _ hn 0 g W hW)
    (fun W hW k c X h1 h3 hX => hfam.decay _ hn 0 W hW k c X h1 h3 hX) ?_)
  intro W W' hW hW' hag
  have hm : 2 * ⌊ρ⌋₊ + 2 < 4 * m := by
    have : (⌊ρ⌋₊ : ℝ) ≤ ρ := Nat.floor_le (by linarith)
    have : ((2 * ⌊ρ⌋₊ + 2 : ℕ) : ℝ) < ((4 * m : ℕ) : ℝ) := by
      push_cast at hM ⊢
      linarith
    exact_mod_cast this
  have h := hfam.local_density (4 * m) (4 * m) hn hn 0 0 W W' ⌊ρ⌋₊ hm hm hW hW' hag 0 (fun l => l.elim0)
    (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_zero, mixedDeriv_zero] at h
  exact h
theorem exists_isMirrorKernel_density {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) {C c ρ₁ ρ E η : ℝ}
    (hL : HasLocalKernels ℓ.threshold ℓ.weightRate C c ρ₁) {f : LocalDensity} (hE : 0 ≤ E) (hη : 0 < η)
    (hη1 : η ≤ 1) (hfam : ColdDensityBounds ℓ E (E / η) f) (hρ : ρ₁ ≤ ρ) (hρ2 : 2 ≤ ρ)
    (hM : 2 * ρ + 2 < ((4 * m : ℕ) : ℝ)) (hn : ℓ.n₀ ≤ 4 * m) :
    ∃ κ, IsMirrorKernel ℓ.threshold C c ρ (E / η) (ℓ.weightRate / 2) (|C| * (E / η)) (centered f (4 * m) 0) κ := by
  have hEη : E ≤ E / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  have hK : 0 ≤ E / η := by positivity
  have hw : ∀ j : ℕ, 0 < ℓ.weight j := fun j => by
    unfold TorusLumps.StepParameters.weight
    have := Real.exp_pos (ℓ.weightRate * j)
    have h1 : (0 : ℝ) < max 1 (((j : ℝ) / ℓ.n₁) ^ 16000) := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  refine exists_isMirrorKernel_of_local hL hρ hM hK (isLocalGaugeFunctional_sub_trivial hfit hρ2 hK
    (fun W hW => hfam.smooth _ hn 0 W hW) (fun g W hW => hfam.gauge _ hn 0 g W hW)
    (fun W hW k c X h1 h3 hX => ?_) ?_)
  · refine (hfam.decay _ hn 0 W hW k c X h1 h3 hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (hw _).le
    split_ifs
    · exact le_rfl
    · exact hEη
  · intro W W' hW hW' hag
    have hm : 2 * ⌊ρ⌋₊ + 2 < 4 * m := by
      have : (⌊ρ⌋₊ : ℝ) ≤ ρ := Nat.floor_le (by linarith)
      have : ((2 * ⌊ρ⌋₊ + 2 : ℕ) : ℝ) < ((4 * m : ℕ) : ℝ) := by
        push_cast at hM ⊢
        linarith
      exact_mod_cast this
    have h := hfam.local_density (4 * m) (4 * m) hn hn 0 0 W W' ⌊ρ⌋₊ hm hm hW hW' hag 0 (fun l => l.elim0)
      (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
    rw [mixedDeriv_zero, mixedDeriv_zero] at h
    exact h.trans (div_le_div_of_nonneg_right hEη (hw _).le)
theorem exists_isMirrorKernel_remainder {ℓ : TorusLumps.StepParameters} (hfit : ℓ.Admissible) {C c ρ₁ ρ Lh : ℝ}
    (hL : HasLocalKernels ℓ.threshold ℓ.weightRate C c ρ₁) {Kr : ResponseParameters} (hη : 0 < Kr.η₃)
    (hη1 : Kr.η₃ ≤ 1) (hKc : 1 ≤ Kr.Kc) {t : ℕ} {P : ColdResponse ℓ.side t} (hrem : RemainderBounds ℓ Kr t P)
    (hP : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n)
      (h : PlaquetteWeight (fineSide ℓ.side t n)), P n y (TorusFields.gaugeTransform g W) h = P n y W h)
    (h' : PlaquetteWeight (fineSide ℓ.side t (4 * m))) (hlip : weightLipschitz ℓ.side t h' ≤ Lh)
    (hlip0 : 0 ≤ weightLipschitz ℓ.side t h') (hρ : ρ₁ ≤ ρ) (hρ2 : 2 ≤ ρ) (hM : 2 * ρ + 2 < ((4 * m : ℕ) : ℝ))
    (hn : ℓ.n₀ ≤ 4 * m) :
    ∃ κ, IsMirrorKernel ℓ.threshold C c ρ (Kr.Kc / Kr.η₃ * Lh) (ℓ.weightRate / 2) (|C| * (Kr.Kc / Kr.η₃ * Lh))
      (fun W => centeredRemainder P (4 * m) 0 h' W) κ := by
  have hLh : 0 ≤ Lh := hlip0.trans hlip
  have hKη : Kr.Kc ≤ Kr.Kc / Kr.η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  have hK : 0 ≤ Kr.Kc / Kr.η₃ * Lh := by
    have : 0 ≤ Kr.Kc / Kr.η₃ := by
      have : 0 ≤ Kr.Kc := by linarith
      positivity
    positivity
  have hw : ∀ j : ℕ, 0 < ℓ.weight j := fun j => by
    unfold TorusLumps.StepParameters.weight
    have := Real.exp_pos (ℓ.weightRate * j)
    have h1 : (0 : ℝ) < max 1 (((j : ℝ) / ℓ.n₁) ^ 16000) := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hKc1 : 0 ≤ Kr.Kc / Kr.η₃ := by positivity
  have hbase : ∀ W, IsCold ℓ.threshold W → ∀ (k : ℕ) (c : Fin k → TorusBond (4 * m))
      (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (responseRemainder P (4 * m) 0 h') W c X| ≤ Kr.Kc / Kr.η₃ * Lh / ℓ.weight (supportDiam 0 c) := by
    intro W hW k c X h1 h3 hX
    refine (hrem.decay _ hn 0 W hW h' k c X h1 h3 hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (hw _).le
    refine mul_le_mul ?_ hlip hlip0 hKc1
    split_ifs
    · exact le_rfl
    · exact hKη
  have hloc : IsLocalGaugeFunctional ℓ.threshold (Kr.Kc / Kr.η₃ * Lh) ℓ.weightRate (ℓ.weightRate / 2) ρ
      (fun W => responseRemainder P (4 * m) 0 h' W - responseRemainder P (4 * m) 0 h' (trivialField _)) 0 := by
    refine isLocalGaugeFunctional_sub_trivial hfit hρ2 hK (fun W hW => hrem.smooth _ hn 0 W hW h')
      (fun g W _ => ?_) hbase ?_
    · unfold responseRemainder
      rw [hP, hP]
    · intro W W' hW hW' hag
      have hm : 2 * ⌊ρ⌋₊ + 2 < 4 * m := by
        have : (⌊ρ⌋₊ : ℝ) ≤ ρ := Nat.floor_le (by linarith)
        have : ((2 * ⌊ρ⌋₊ + 2 : ℕ) : ℝ) < ((4 * m : ℕ) : ℝ) := by
          push_cast at hM ⊢
          linarith
        exact_mod_cast this
      have h := hrem.compare _ hn 0 W W' ⌊ρ⌋₊ hm hW hW' hag h' 0 (fun l => l.elim0) (fun l => l.elim0)
        (by omega) (fun l => l.elim0) (fun l => l.elim0)
      rw [mixedDeriv_zero, mixedDeriv_zero] at h
      refine h.trans (div_le_div_of_nonneg_right ?_ (hw _).le)
      exact mul_le_mul hKη hlip hlip0 hKc1
  exact exists_isMirrorKernel_of_local hL hρ hM hK hloc
end Kernels
section Assembly
variable {m : ℕ} [NeZero n] [NeZero (4 * m)]
theorem centeredResponse_eq {L t : ℕ} [NeZero L] (P : ColdResponse L t) (y : TorusSite n) (W : TorusField n)
    (h : PlaquetteWeight (fineSide L t n)) :
    centeredResponse P n y W h =
      blockMean L t n y h * centeredResponse P n y W (constOneWeight _) + centeredRemainder P n y h W := by
  unfold centeredResponse centeredRemainder responseRemainder
  ring
theorem weightLipschitz_nonneg (L t : ℕ) {N : ℕ} (h : PlaquetteWeight N) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
theorem isLocalKernel_translatedKernel {ρ d D : ℝ} {R : ℕ} (hR : ρ = R) (hn : 2 * R < n) (hd : 0 ≤ d)
    (hD : 0 ≤ D) {κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ}
    (hκ : ∀ a b, |κ a b| ≤
      D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)))) :
    IsLocalKernel ρ d D fun z : TorusSite n =>
      translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ := by
  have hS : ∀ a ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ), (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) ≤ ρ := by
    intro a ha
    exact _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_le_of_mem_supBall ((Finset.mem_filter.mp ha).2.2 _ (by simp [plaquetteVertices]))
  refine ⟨fun z p p' h => translatedKernel_eq_zero_of_far _ z κ hS p p' h, fun z p p' => ?_⟩
  refine abs_translatedKernel_le _ z κ hn (fun a ha => ?_) hd hD (fun a _ b _ => hκ a b) p p'
  have := hS a ha
  rw [hR] at this
  exact_mod_cast this
def mirrorSiteError (C c ρ d s e₁ K : ℝ) : ℝ :=
  C * K * ((4 * s) ^ 3 + Real.exp (-(c * ρ))) +
    3 / 2 * (|C| * K * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2) * (e₁ * (8 * s + e₁))
theorem abs_sum_response_sub_form_le (B : Finset (TorusSite n)) (hh : TorusSite n → ℝ) (al : ℝ)
    (κ0 κ1 : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ)
    (κ2 : TorusSite n → TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) (G0 G1 : TorusField (4 * m) → ℝ)
    (G2 : TorusSite n → TorusField (4 * m) → ℝ) {σ C c ρ K0 K1 K2 d r s e₁ : ℝ}
    (g0 : IsMirrorKernel σ C c ρ K0 d (|C| * K0) G0 κ0) (g1 : IsMirrorKernel σ C c ρ K1 d (|C| * K1) G1 κ1)
    (g2 : ∀ z, IsMirrorKernel σ C c ρ K2 d (|C| * K2) (G2 z) (κ2 z)) (hd : 0 < d) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (hoff : ∀ z, z ∉ B → hh z = 0) (hh1 : ∀ z ∈ B, |hh z| ≤ 1) (hal : |al| ≤ 2) (W : TorusField n)
    (g : TorusSite n → UnitQuaternion) (o : TorusSite n) (hm : 2 ≤ m) (hρ : ρ + 1 ≤ m)
    (hb : ∀ z ∈ B, ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) (hs0 : 0 ≤ s)
    (h5 : 5 * (4 * s) ≤ σ)
    (hs : ∀ b : TorusBond n, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    (hcold : ∀ z ∈ B, IsCold σ (TorusMirror.mirrorField m z W)) (Φ : TorusPlaquette n → imaginaryQuaternions)
    (he₁ : 0 ≤ e₁)
    (he : ∀ p ∈ plaquettesIn (supBall o r),
      ‖((lieFormCurl (ballLog g W o r) p - Φ p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ e₁) (v : TorusSite n → ℝ)
    (hv : ∀ z ∈ B, v z = hh z * (al * G0 (TorusMirror.mirrorField m z W) + G1 (TorusMirror.mirrorField m z W)) +
      G2 z (TorusMirror.mirrorField m z W)) :
    |∑ z ∈ B, v z - (1 / 2) * ∑ z, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (hh z * al * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ0 p p' +
          (if z ∈ B then hh z * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p' +
            translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z (κ2 z) p p' else 0)) *
          ∑ e : Fin 3, imaginaryComponent e (Φ p) * imaginaryComponent e (Φ p')| ≤
      B.card * (2 * mirrorSiteError C c ρ d s e₁ K0 + mirrorSiteError C c ρ d s e₁ K1 +
        mirrorSiteError C c ρ d s e₁ K2) := by
  have hsite : ∀ {K : ℝ} {G : TorusField (4 * m) → ℝ} {κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ},
      0 ≤ K → IsMirrorKernel σ C c ρ K d (|C| * K) G κ → ∀ z ∈ B,
      |G (TorusMirror.mirrorField m z W) -
          plaquetteForm Φ (translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ)| ≤
        mirrorSiteError C c ρ d s e₁ K := by
    intro K G κ hK hg z hz
    exact abs_sub_mirror_form_le hg.quadratic hd (by positivity) (fun a _ b _ => hg.bound a b) z W g o hm hρ
      (hb z hz) hs0 h5 hs (hcold z hz) Φ he₁ he
  exact abs_sum_sub_plaquetteForm_le B hh al (fun z => translatedKernel _ z κ0) (fun z => translatedKernel _ z κ1)
    (fun z => translatedKernel _ z (κ2 z)) Φ v (fun z => G0 (TorusMirror.mirrorField m z W))
    (fun z => G1 (TorusMirror.mirrorField m z W)) (fun z => G2 z (TorusMirror.mirrorField m z W)) hoff hh1 hal hv
    (hsite hK0 g0) (hsite hK1 g1) (fun z hz => hsite hK2 (g2 z) z hz)
theorem mirrorSiteError_le {C c ρ d s e₁ K Ad ε : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hexp : Real.exp (-(c * ρ)) ≤ ε) (hAd : 0 ≤ Ad) (he : e₁ = Ad * (s ^ 2 + ε))
    (hΛ : 0 ≤ (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2) :
    mirrorSiteError C c ρ d s e₁ K ≤
      K * (|C| * (64 + 9 / 2 * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2 * Ad * (8 + Ad))) * (s ^ 3 + ε) := by
  set Λ := (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2 with hΛd
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have h1 : C * K * ((4 * s) ^ 3 + Real.exp (-(c * ρ))) ≤ |C| * K * (64 * (s ^ 3 + ε)) := by
    have a1 : (4 * s) ^ 3 + Real.exp (-(c * ρ)) ≤ 64 * (s ^ 3 + ε) := by nlinarith
    have a2 : 0 ≤ (4 * s) ^ 3 + Real.exp (-(c * ρ)) := by positivity
    have a3 : C * K ≤ |C| * K := mul_le_mul_of_nonneg_right (le_abs_self _) hK
    calc C * K * ((4 * s) ^ 3 + Real.exp (-(c * ρ))) ≤ |C| * K * ((4 * s) ^ 3 + Real.exp (-(c * ρ))) :=
          mul_le_mul_of_nonneg_right a3 a2
      _ ≤ _ := mul_le_mul_of_nonneg_left a1 (by positivity)
  have h2 : e₁ * (8 * s + e₁) ≤ 3 * (Ad * (8 + Ad)) * (s ^ 3 + ε) := by
    rw [he]
    have b1 : (s ^ 2 + ε) * s ≤ s ^ 3 + ε := by nlinarith [mul_nonneg hε0 hs0]
    have b2 : (s ^ 2 + ε) ^ 2 ≤ s ^ 3 + 3 * ε := by
      have c1 : s ^ 4 ≤ s ^ 3 := by nlinarith [pow_nonneg hs0 3]
      have c2 : s ^ 2 * ε ≤ ε := by nlinarith [mul_nonneg hε0 (sq_nonneg s)]
      have c3 : ε ^ 2 ≤ ε := by nlinarith
      nlinarith
    have b3 : Ad * (s ^ 2 + ε) * (8 * s + Ad * (s ^ 2 + ε)) =
        8 * Ad * ((s ^ 2 + ε) * s) + Ad ^ 2 * (s ^ 2 + ε) ^ 2 := by ring
    rw [b3]
    have b4 := mul_le_mul_of_nonneg_left b1 (by positivity : 0 ≤ 8 * Ad)
    have b5 := mul_le_mul_of_nonneg_left b2 (by positivity : 0 ≤ Ad ^ 2)
    have b7 : 0 ≤ Ad * (s ^ 3 + ε) := by positivity
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 3 / 2 * (|C| * K * Λ))
  unfold mirrorSiteError
  calc _ ≤ |C| * K * (64 * (s ^ 3 + ε)) + 3 / 2 * (|C| * K * Λ) * (3 * (Ad * (8 + Ad)) * (s ^ 3 + ε)) :=
        add_le_add h1 h3
    _ = _ := by ring
end Assembly
section Numbers
theorem sum_filter_eq_of_support {α : Type} {S U : Finset α} (hSU : S ⊆ U) (κ : α → α → ℝ)
    (hz : ∀ a b, ¬ (a ∈ S ∧ b ∈ S) → κ a b = 0) (P P' : α → Prop) [DecidablePred P] [DecidablePred P'] :
    ∑ a ∈ U.filter P, ∑ b ∈ U.filter P', κ a b = ∑ a ∈ S.filter P, ∑ b ∈ S.filter P', κ a b := by
  symm
  have h1 : ∀ a ∈ S.filter P, ∑ b ∈ S.filter P', κ a b = ∑ b ∈ U.filter P', κ a b := by
    intro a ha
    refine Finset.sum_subset (Finset.filter_subset_filter _ hSU) fun b hb hnb => ?_
    refine hz a b fun h => hnb (Finset.mem_filter.mpr ⟨h.2, (Finset.mem_filter.mp hb).2⟩)
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_subset (Finset.filter_subset_filter _ hSU) fun a ha hna => ?_
  refine Finset.sum_eq_zero fun b _ => hz a b fun h => hna (Finset.mem_filter.mpr ⟨h.1, (Finset.mem_filter.mp ha).2⟩)
theorem abs_sub_le_of_estimates {a κ V Q Cm n4 e sz card E0 E1 E2 K0 K1 K2 Ka Kc B₀ s ε A δ : ℝ}
    (h1 : |a - κ - V| ≤ Cm * n4 * e * sz) (h2 : |V - Q| ≤ card * (2 * E0 + E1 + E2))
    (hE0 : E0 ≤ K0 * B₀ * (s ^ 3 + ε)) (hE1 : E1 ≤ K1 * B₀ * (s ^ 3 + ε)) (hE2 : E2 ≤ K2 * B₀ * (s ^ 3 + ε))
    (hK0 : 0 ≤ K0) (hK1 : K1 ≤ Ka) (hK2 : K2 ≤ Kc) (hK1' : 0 ≤ K1) (hK2' : 0 ≤ K2) (hcard0 : 0 ≤ card)
    (hcard : card ≤ 25 ^ 4 * n4) (he0 : 0 ≤ e) (he : e ≤ ε) (hsz0 : 0 ≤ sz) (hsz : sz ≤ 1) (hn4 : 0 ≤ n4)
    (hB₀ : 0 ≤ B₀) (hs0 : 0 ≤ s) (hε : 0 ≤ ε) (hs : s ≤ A + δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    |a - κ - Q| ≤ n4 * (4 * (25 ^ 4 * (2 * K0 + Ka + Kc) * B₀) + |Cm| + 1) * (A ^ 3 + (δ ^ 3 + ε)) := by
  set T := A ^ 3 + (δ ^ 3 + ε) with hT
  have hA3 : 0 ≤ A ^ 3 := by positivity
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  have hs3 : s ^ 3 ≤ 4 * (A ^ 3 + δ ^ 3) := by
    have b1 : s ^ 3 ≤ (A + δ) ^ 3 := pow_le_pow_left₀ hs0 hs 3
    have b2 : (A + δ) ^ 3 ≤ 4 * (A ^ 3 + δ ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg hA hδ) (sq_nonneg (A - δ))]
    linarith
  have hS : s ^ 3 + ε ≤ 4 * T := by
    rw [hT]
    linarith
  have hS0 : 0 ≤ s ^ 3 + ε := by positivity
  set Sx := s ^ 3 + ε with hSx
  have hKa : 0 ≤ Ka := hK1'.trans hK1
  have hKc : 0 ≤ Kc := hK2'.trans hK2
  have hsum : 2 * E0 + E1 + E2 ≤ (2 * K0 + Ka + Kc) * B₀ * Sx := by
    have c1 : K1 * B₀ * Sx ≤ Ka * B₀ * Sx :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hB₀) hS0
    have c2 : K2 * B₀ * Sx ≤ Kc * B₀ * Sx :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hB₀) hS0
    nlinarith
  have hG0 : 0 ≤ (2 * K0 + Ka + Kc) * B₀ * Sx := by positivity
  have h3 : |V - Q| ≤ 25 ^ 4 * n4 * ((2 * K0 + Ka + Kc) * B₀ * Sx) :=
    h2.trans ((mul_le_mul_of_nonneg_left hsum hcard0).trans (mul_le_mul_of_nonneg_right hcard hG0))
  have h4 : Cm * n4 * e * sz ≤ |Cm| * n4 * ε := by
    have c1 : Cm * n4 ≤ |Cm| * n4 := mul_le_mul_of_nonneg_right (le_abs_self _) hn4
    have c2 : e * sz ≤ ε := by nlinarith
    calc Cm * n4 * e * sz = Cm * n4 * (e * sz) := by ring
      _ ≤ |Cm| * n4 * (e * sz) := mul_le_mul_of_nonneg_right c1 (by positivity)
      _ ≤ |Cm| * n4 * ε := mul_le_mul_of_nonneg_left c2 (by positivity)
  have h5 : |a - κ - Q| ≤ |a - κ - V| + |V - Q| := by
    have : a - κ - Q = (a - κ - V) + (V - Q) := by ring
    rw [this]
    exact abs_add_le _ _
  have hεT : ε ≤ T := by
    rw [hT]
    linarith
  set G := 25 ^ 4 * (2 * K0 + Ka + Kc) * B₀ with hG
  have hG0' : 0 ≤ G := by positivity
  have h6 : 25 ^ 4 * n4 * ((2 * K0 + Ka + Kc) * B₀ * Sx) = n4 * (G * Sx) := by
    rw [hG]
    ring
  rw [h6] at h3
  have h7 : n4 * (G * Sx) ≤ n4 * (G * (4 * T)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hG0') hn4
  have h8 : |Cm| * n4 * ε ≤ |Cm| * n4 * T := mul_le_mul_of_nonneg_left hεT (by positivity)
  have h9 : 0 ≤ n4 * T := by positivity
  nlinarith
end Numbers
section Pointwise
variable {m : ℕ} [NeZero n] [NeZero (4 * m)]
theorem abs_response_sub_form_le (B : Finset (TorusSite n)) (hh : TorusSite n → ℝ) (al : ℝ)
    (κ0 κ1 : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ)
    (κ2 : TorusSite n → TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) (G0 G1 : TorusField (4 * m) → ℝ)
    (G2 : TorusSite n → TorusField (4 * m) → ℝ)
    {σ C c ρ K0 K1 K2 Ka Kc d r s ε Ad a κ Cm n4 e sz A δ : ℝ}
    (g0 : IsMirrorKernel σ C c ρ K0 d (|C| * K0) G0 κ0) (g1 : IsMirrorKernel σ C c ρ K1 d (|C| * K1) G1 κ1)
    (g2 : ∀ z, IsMirrorKernel σ C c ρ K2 d (|C| * K2) (G2 z) (κ2 z)) (hd : 0 < d)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK1a : K1 ≤ Ka) (hK2c : K2 ≤ Kc)
    (hoff : ∀ z, z ∉ B → hh z = 0) (hh1 : ∀ z ∈ B, |hh z| ≤ 1) (hal : |al| ≤ 2) (W : TorusField n)
    (g : TorusSite n → UnitQuaternion) (o : TorusSite n) (hm : 2 ≤ m) (hρ : ρ + 1 ≤ m)
    (hb : ∀ z ∈ B, ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h5 : 5 * (4 * s) ≤ σ)
    (hs : ∀ b : TorusBond n, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s)
    (hcold : ∀ z ∈ B, IsCold σ (TorusMirror.mirrorField m z W)) (Φ : TorusPlaquette n → imaginaryQuaternions)
    (hAd : 0 ≤ Ad) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hexp : Real.exp (-(c * ρ)) ≤ ε)
    (he : ∀ p ∈ plaquettesIn (supBall o r),
      ‖((lieFormCurl (ballLog g W o r) p - Φ p : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ Ad * (s ^ 2 + ε))
    (v : TorusSite n → ℝ)
    (hv : ∀ z ∈ B, v z = hh z * (al * G0 (TorusMirror.mirrorField m z W) + G1 (TorusMirror.mirrorField m z W)) +
      G2 z (TorusMirror.mirrorField m z W))
    (hclose : |a - κ - ∑ z ∈ B, v z| ≤ Cm * n4 * e * sz) (hcard : (B.card : ℝ) ≤ 25 ^ 4 * n4) (he0 : 0 ≤ e)
    (heε : e ≤ ε) (hsz0 : 0 ≤ sz) (hsz : sz ≤ 1) (hn4 : 0 ≤ n4) (hsA : s ≤ A + δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    |a - κ - (1 / 2) * ∑ z, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (hh z * al * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ0 p p' +
          (if z ∈ B then hh z * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p' +
            translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z (κ2 z) p p' else 0)) *
          ∑ e : Fin 3, imaginaryComponent e (Φ p) * imaginaryComponent e (Φ p')| ≤
      n4 * (4 * (25 ^ 4 * (2 * K0 + Ka + Kc) *
        (|C| * (64 + 9 / 2 * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2 * Ad * (8 + Ad)))) + |Cm| + 1) *
        (A ^ 3 + (δ ^ 3 + ε)) := by
  have he₁ : 0 ≤ Ad * (s ^ 2 + ε) := by positivity
  have hR := abs_sum_response_sub_form_le B hh al κ0 κ1 κ2 G0 G1 G2 g0 g1 g2 hd hK0 hK1 hK2 hoff hh1 hal W g o hm
    hρ hb hs0 h5 hs hcold Φ he₁ he v hv
  have hE : ∀ K : ℝ, 0 ≤ K → mirrorSiteError C c ρ d s (Ad * (s ^ 2 + ε)) K ≤
      K * (|C| * (64 + 9 / 2 * (16 * ExponentialSums.expLatticeSum (d / 2)) ^ 2 * Ad * (8 + Ad))) * (s ^ 3 + ε) :=
    fun K hK => mirrorSiteError_le hK hs0 hs1 hε0 hε1 hexp hAd rfl (by positivity)
  exact abs_sub_le_of_estimates hclose hR (hE K0 hK0) (hE K1 hK1) (hE K2 hK2) hK0 hK1a hK2c hK1 hK2
    (by positivity) hcard he0 heε hsz0 hsz hn4 (by positivity) hs0 hε0 hsA hA hδ
theorem isLocalKernel_remainderPart (B : Finset (TorusSite n)) (hh : TorusSite n → ℝ)
    (κ1 : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ)
    (κ2 : TorusSite n → TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) {ρ d D1 D2 size : ℝ} {R : ℕ}
    (hR : ρ = R) (hn : 2 * R < n) (hd : 0 ≤ d) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hsize : D1 + D2 ≤ size)
    (hh1 : ∀ z, |hh z| ≤ 1)
    (h1 : ∀ a b, |κ1 a b| ≤
      D1 * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ))))
    (h2 : ∀ z a b, |κ2 z a b| ≤
      D2 * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)))) :
    IsLocalKernel ρ d size fun (z : TorusSite n) p p' => if z ∈ B then
      hh z * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p' +
        translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z (κ2 z) p p' else 0 := by
  have l1 := isLocalKernel_translatedKernel (n := n) (m := m) hR hn hd hD1 h1
  have l2 := fun z : TorusSite n => isLocalKernel_translatedKernel (n := n) (m := m) hR hn hd hD2 (h2 z)
  have hs0 : 0 ≤ size := (add_nonneg hD1 hD2).trans hsize
  refine ⟨fun z p p' hpp => ?_, fun z p p' => ?_⟩
  · by_cases hz : z ∈ B
    · simp only [if_pos hz]
      rw [l1.support z p p' hpp, (l2 z).support z p p' hpp]
      simp
    · simp only [if_neg hz]
  · by_cases hz : z ∈ B
    · simp only [if_pos hz]
      have a1 := l1.decay z p p'
      have a2 := (l2 z).decay z p p'
      have a3 := abs_add_le (hh z * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p')
        (translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z (κ2 z) p p')
      have a4 : |hh z * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p'| ≤
          |translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p'| := by
        rw [abs_mul]
        calc _ ≤ 1 * |translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) z κ1 p p'| :=
              mul_le_mul_of_nonneg_right (hh1 z) (abs_nonneg _)
          _ = _ := one_mul _
      refine (a3.trans (add_le_add a4 le_rfl)).trans ((add_le_add a1 a2).trans ?_)
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hsize (Real.exp_pos _).le
    · simp only [if_neg hz]
      rw [abs_zero]
      positivity
end Pointwise
end ColdMirrorFunctionals
end ResponseInTheExpansion
end YangMills.Construction
end
