import YangMills.Construction.ClusterExpansionOfAStep.OneNumberOfACarriedFamilyProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifferenceProof
import YangMills.Construction.LawInAState.TheMarkOfAFunctionOfTheField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open TorusFields AxialForms StateLaw FlatHessian ExponentialSums BlockAverages
open TorusLumps hiding quaternionI
namespace BoxForm
private theorem abs_le_offsetSupNorm (a : Fin 4 → ℤ) (i : Fin 4) : |(a i : ℝ)| ≤ offsetSupNorm a := by apply _root_.YangMills.Construction.LatticeSums.abs_le_offsetSupNorm <;> assumption
private theorem summable_exp_neg_offsetSupNorm {θ : ℝ} (hθ : 0 < θ) :
    Summable fun a : Fin 4 → ℤ => Real.exp (-θ * offsetSupNorm a) := by apply _root_.YangMills.Construction.LatticeSums.summable_exp_neg_offsetSupNorm <;> assumption
private def offsetMajorant (θ : ℝ) (c : LatticeBond) : ℝ :=
  4 * offsetSupNorm c.1 * Real.exp (-θ * offsetSupNorm c.1)
private theorem offsetMajorant_nonneg (θ : ℝ) (c : LatticeBond) : 0 ≤ offsetMajorant θ c := by
  unfold offsetMajorant
  positivity
private theorem summable_offsetMajorant {θ : ℝ} (hθ : 0 < θ) : Summable (offsetMajorant θ) := by
  have h1 : Summable fun a : Fin 4 → ℤ => 4 * (offsetSupNorm a : ℝ) * Real.exp (-θ * offsetSupNorm a) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun a => ?_)
      ((summable_exp_neg_offsetSupNorm (show 0 < θ / 2 by positivity)).mul_left (8 / θ))
    have hx : (θ / 2) * (offsetSupNorm a : ℝ) ≤ Real.exp ((θ / 2) * offsetSupNorm a) := by
      have := Real.add_one_le_exp ((θ / 2) * (offsetSupNorm a : ℝ))
      linarith
    have e : Real.exp (-θ * offsetSupNorm a) * Real.exp ((θ / 2) * offsetSupNorm a) =
        Real.exp (-(θ / 2) * offsetSupNorm a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 4 * (offsetSupNorm a : ℝ) * Real.exp (-θ * offsetSupNorm a)
        = (8 / θ) * (((θ / 2) * offsetSupNorm a) * Real.exp (-θ * offsetSupNorm a)) := by
          field_simp
          ring
      _ ≤ (8 / θ) * (Real.exp ((θ / 2) * offsetSupNorm a) * Real.exp (-θ * offsetSupNorm a)) := by
          gcongr
      _ = _ := by rw [mul_comm (Real.exp _), e]
  have h2 := Summable.mul_of_nonneg h1
    (summable_of_hasFiniteSupport (Set.toFinite _) : Summable fun _ : Fin 4 => (1 : ℝ))
    (fun _ => by positivity) (fun _ => zero_le_one)
  refine h2.congr fun c => ?_
  simp [offsetMajorant]
private theorem mem_bondsWithin {m : ℕ} {c : LatticeBond} : c ∈ bondsWithin m ↔ offsetSupNorm c.1 ≤ m := by apply _root_.YangMills.Construction.LatticeSums.mem_bondsWithin_iff <;> assumption
private def linearCoeff (ω : Fin 4 → Fin 4 → ℝ) (c : LatticeBond) : ℝ :=
  (1 / 2) * ∑ l, (c.1 l : ℝ) * ω l c.2
private theorem linearPotential_along_eq (ω : Fin 4 → Fin 4 → ℝ) (c : LatticeBond) :
    linearPotential (curvatureAlong quaternionI ω) c = linearCoeff ω c • quaternionI := by
  simp only [linearPotential, curvatureAlong, linearCoeff, smul_smul, Finset.smul_sum, Finset.sum_smul,
    Finset.mul_sum]
private theorem abs_linearCoeff_le {ω : Fin 4 → Fin 4 → ℝ} (h1 : ∀ i j, |ω i j| ≤ 1) (c : LatticeBond) :
    |linearCoeff ω c| ≤ 2 * offsetSupNorm c.1 := by
  unfold linearCoeff
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have : |∑ l, (c.1 l : ℝ) * ω l c.2| ≤ 4 * offsetSupNorm c.1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _l : Fin 4, (offsetSupNorm c.1 : ℝ) := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          have := abs_le_offsetSupNorm c.1 l
          nlinarith [abs_nonneg (c.1 l : ℝ), abs_nonneg (ω l c.2), h1 l c.2]
      _ = _ := by simp
  linarith
private theorem abs_constantCurvaturePotential_le {ω : Fin 4 → Fin 4 → ℝ} (h1 : ∀ i j, |ω i j| ≤ 1)
    (c : LatticeBond) : |constantCurvaturePotential ω c| ≤ 4 * offsetSupNorm c.1 := by
  unfold constantCurvaturePotential axialForm
  rw [abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin 4, (offsetSupNorm c.1 : ℝ) := Finset.sum_le_sum fun l _ => by
        split_ifs
        · refine (abs_intervalSum_le _ _ 1 fun j _ => h1 _ _).trans ?_
          simpa using abs_le_offsetSupNorm c.1 l
        · simp
    _ = _ := by simp
private theorem offsetSupNorm_truncate_le (a : Fin 4 → ℤ) (ν : Fin 4) {j : ℤ} (hj : |j| ≤ |a ν|) :
    offsetSupNorm (truncate a ν j) ≤ offsetSupNorm a := by apply _root_.YangMills.Construction.CurvatureKernel.offsetSupNorm_truncate_le <;> assumption
private theorem abs_axialPathSum_linearCoeff_le {ω : Fin 4 → Fin 4 → ℝ} (h1 : ∀ i j, |ω i j| ≤ 1)
    (a : Fin 4 → ℤ) :
    |axialPathSum (fun a μ => linearCoeff ω (a, μ)) a| ≤ 8 * (offsetSupNorm a : ℝ) ^ 2 := by
  unfold axialPathSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _l : Fin 4, 2 * (offsetSupNorm a : ℝ) ^ 2 := Finset.sum_le_sum fun l _ => by
        refine (abs_intervalSum_le _ _ (2 * offsetSupNorm a) fun j hj => ?_).trans ?_
        · refine (abs_linearCoeff_le h1 _).trans ?_
          have : (offsetSupNorm (truncate a l j) : ℝ) ≤ offsetSupNorm a := by
            exact_mod_cast offsetSupNorm_truncate_le a l hj
          simpa using this
        · have := abs_le_offsetSupNorm a l
          nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm a)]
    _ = _ := by
      simp
      ring
private theorem latticeCurl_linearCoeff {ω : Fin 4 → Fin 4 → ℝ} (h : ∀ i j, ω i j = - ω j i)
    (a : Fin 4 → ℤ) (μ ν : Fin 4) :
    latticeCurl (fun a μ => linearCoeff ω (a, μ)) a μ ν = ω μ ν := by
  simp only [latticeCurl, linearCoeff]
  have e1 : ∀ (b : Fin 4 → ℤ) (ρ κ : Fin 4), ∑ l, ((b + Pi.single ρ 1 : Fin 4 → ℤ) l : ℝ) * ω l κ =
      ∑ l, (b l : ℝ) * ω l κ + ω ρ κ := by
    intro b ρ κ
    have : ∀ l, ((b + Pi.single ρ 1 : Fin 4 → ℤ) l : ℝ) * ω l κ =
        (b l : ℝ) * ω l κ + (if l = ρ then ω l κ else 0) := by
      intro l
      by_cases hl : l = ρ
      · subst hl
        simp [add_mul]
      · simp [hl]
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_add_distrib]
    simp
  rw [e1, e1, h ν μ]
  ring
private theorem constantCurvaturePotential_eq {ω : Fin 4 → Fin 4 → ℝ} (h : ∀ i j, ω i j = - ω j i)
    (c : LatticeBond) :
    constantCurvaturePotential ω c = linearCoeff ω c -
      (axialPathSum (fun a μ => linearCoeff ω (a, μ)) (c.1 + Pi.single c.2 1) -
        axialPathSum (fun a μ => linearCoeff ω (a, μ)) c.1) := by
  have h1 := eq_pathSum_sub_add_axialForm (fun a μ => linearCoeff ω (a, μ)) c.1 c.2
  have h2 : axialForm (latticeCurl fun a μ => linearCoeff ω (a, μ)) (c.1, c.2) =
      constantCurvaturePotential ω c := by
    unfold constantCurvaturePotential axialForm
    simp only [latticeCurl_linearCoeff h]
  rw [h2] at h1
  linarith
private theorem norm_quaternionI : ‖(quaternionI : imaginaryQuaternions)‖ = 1 := by apply _root_.YangMills.SharedProofs.p83019 <;> assumption
private theorem inner_smul_quaternionI (s s' : ℝ) :
    inner ℝ (((s • quaternionI : imaginaryQuaternions)) : ℍ[ℝ])
      (((s' • quaternionI : imaginaryQuaternions)) : ℍ[ℝ]) = s * s' := by
  have h : inner ℝ ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])
      ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := norm_quaternionI
    rw [this]
    norm_num
  simp only [Submodule.coe_smul, inner_smul_left, inner_smul_right, h]
  simp [mul_comm]
private theorem mixedDeriv_centered {n : ℕ} (f : LocalDensity) (y : TorusSite n) {W : TorusField n}
    (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions)
    (hC : ContDiffAt ℝ 3 (fun σ : Fin 2 → ℝ => f n y (TorusFields.perturb c X σ W)) 0) :
    mixedDeriv (TorusLumps.centered f n y) W c X = mixedDeriv (f n y) W c X := by
  unfold mixedDeriv TorusLumps.centered
  have h1 : (fun σ : Fin 2 → ℝ => f n y (TorusFields.perturb c X σ W) - f n y (trivialField n)) =
      (fun σ => f n y (TorusFields.perturb c X σ W)) + fun _ => -f n y (trivialField n) := by
    funext σ
    simp [sub_eq_add_neg]
  rw [h1, iteratedFDeriv_add_apply (hC.of_le (by norm_num)) contDiffAt_const]
  simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (show (2 : ℕ) ≠ 0 by norm_num)]
variable {ℓ : StepParameters} {C : ℝ} {f : LocalDensity}
private theorem trivialField_isCold (hℓ : ℓ.Admissible) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by
  intro x μ ν _
  simpa [TorusFields.curvature, holonomy, trivialField] using hℓ.σ_pos
private theorem exp_le_weight (ℓ : StepParameters) (m : ℕ) : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by apply _root_.YangMills.SharedProofs.p47115 <;> assumption
private theorem flatHessian_sub_mixedDeriv_le (hℓ : ℓ.Admissible) (hf : IsCurvatureFamily ℓ C f) {n n' : ℕ}
    [NeZero n] [NeZero n'] (z : TorusSite n) {m : ℕ} (hn : ℓ.n₀ ≤ n) (hn' : ℓ.n₀ ≤ n')
    (h2 : 2 * (m + 1) + 2 < n) (h2' : 2 * (m + 1) + 2 < n') {c c' : LatticeBond}
    (hc : c ∈ bondsWithin m) (hc' : c' ∈ bondsWithin m) :
    |flatHessian (f n z) (bondFrom z c) (bondFrom z c') -
        mixedDeriv (f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![quaternionI, quaternionI]| ≤
      C / ℓ.weight (m + 1) := by
  have inbox : ∀ d : LatticeBond, d ∈ bondsWithin m → TorusFields.BondOffsetInBox (m + 1) d := by
    intro d hd
    have hs := mem_bondsWithin.1 hd
    have hi : ∀ i, (d.1 i).natAbs ≤ m := fun i =>
      (Finset.le_sup (f := fun i => (d.1 i).natAbs) (Finset.mem_univ i)).trans hs
    constructor
    · intro i
      have := hi i
      rw [abs_le]
      push_cast
      constructor <;> omega
    · intro i
      have := hi i
      rw [abs_le]
      push_cast
      by_cases h : i = d.2
      · subst h
        simp only [Pi.add_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne h]
        constructor <;> omega
  have h := hf.local_density n n' hn hn' z 0 (trivialField n) (trivialField n') (m + 1) h2 h2'
    (trivialField_isCold hℓ n) (trivialField_isCold hℓ n')
    (fun _ _ => rfl) 2 ![c, c'] ![quaternionI, quaternionI] le_rfl (fun l => by
      fin_cases l
      · exact inbox c hc
      · exact inbox c' hc') (fun l => by fin_cases l <;> exact norm_quaternionI)
  have a1 : (fun l => bondFrom z ((![c, c'] : Fin 2 → LatticeBond) l)) = ![bondFrom z c, bondFrom z c'] := by
    funext l
    fin_cases l <;> rfl
  have a2 : (fun l => bondFrom (0 : TorusSite n') ((![c, c'] : Fin 2 → LatticeBond) l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
    funext l
    fin_cases l <;> rfl
  rw [a1, a2, mixedDeriv_centered f z _ _ (hf.smooth n hn z _ (trivialField_isCold hℓ n) 2 _ _),
    mixedDeriv_centered f 0 _ _ (hf.smooth n' hn' 0 _ (trivialField_isCold hℓ n') 2 _ _)] at h
  simpa [flatHessian] using h
private theorem abs_sum_sub_tsum_le (hℓ : ℓ.Admissible) (hC : 0 ≤ C) (hrate : 0 < ℓ.weightRate)
    (hH : HessianAtTrivialFieldStatement) (hS : SecondOrderAtAbelianFields)
    (hf : IsCurvatureFamily ℓ C f) {ω ω' : Fin 4 → Fin 4 → ℝ} (ha : ∀ i j, ω i j = - ω j i)
    (ha' : ∀ i j, ω' i j = - ω' j i)
    (h1 : ∀ i j, |ω i j| ≤ 1) (h1' : ∀ i j, |ω' i j| ≤ 1) {n : ℕ} [NeZero n] (z : TorusSite n) {m : ℕ}
    (hn : ℓ.n₀ ≤ n) (h2 : 2 * (m + 1) + 2 < n) :
    |∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian (f n z) (bondFrom z c) (bondFrom z c') *
        (constantCurvaturePotential ω c * constantCurvaturePotential ω' c') -
      ∑' cc, limitFormTerm f (curvatureAlong quaternionI ω) (curvatureAlong quaternionI ω') cc| ≤
      2 * C * (∑' cc : LatticeBond × LatticeBond,
        offsetMajorant (ℓ.weightRate / 4) cc.1 * offsetMajorant (ℓ.weightRate / 4) cc.2) *
        Real.exp (-(ℓ.weightRate / 2 * m)) := by
  obtain ⟨hlim, hbound, hsymm, hpoly, hcurv, hgrad, -, -⟩ := hS ℓ hℓ C f hf
  set q : LatticeBond → LatticeBond → ℝ := fun c c' => secondDerivLimit f c c' quaternionI quaternionI with hq
  have hbil : ∀ (s s' : ℝ) (c c' : LatticeBond),
      secondDerivLimit f c c' (s • quaternionI) (s' • quaternionI) = s * s' * q c c' := by
    intro s s' c c'
    have t1 := hlim c c' (s • quaternionI) (s' • quaternionI)
    have t2 := (hlim c c' quaternionI quaternionI).const_mul (s * s')
    refine tendsto_nhds_unique_of_eventuallyEq t1 t2 ?_
    filter_upwards [eventually_ge_atTop (max ℓ.n₀ 1)] with k hk
    have : NeZero k := ⟨by have := le_max_right ℓ.n₀ 1; omega⟩
    have := (hH ℓ hℓ C f hf k ((le_max_left _ _).trans hk) 0 (bondFrom 0 c) (bondFrom 0 c')).1
      (s • quaternionI) (s' • quaternionI)
    rw [this, inner_smul_quaternionI]
  have pg : ∀ {ζ : Fin 4 → Fin 4 → ℝ}, (∀ i j, ζ i j = - ζ j i) → (∀ i j, |ζ i j| ≤ 1) →
      HasPolynomialGrowth (fun c => constantCurvaturePotential ζ c • quaternionI) ∧
        HasPolynomialGrowth (fun c => linearCoeff ζ c • quaternionI) := by
    intro ζ _ hz
    constructor
    · refine ⟨4, 1, fun c => ?_⟩
      rw [norm_smul, norm_quaternionI, mul_one, Real.norm_eq_abs, pow_one]
      have := abs_constantCurvaturePotential_le hz c
      nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm c.1)]
    · refine ⟨2, 1, fun c => ?_⟩
      rw [norm_smul, norm_quaternionI, mul_one, Real.norm_eq_abs, pow_one]
      have := abs_linearCoeff_le hz c
      nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm c.1)]
  have tg : ∀ {ζ : Fin 4 → Fin 4 → ℝ}, (∀ i j, |ζ i j| ≤ 1) → ∃ (K : ℝ) (p : ℕ), ∀ a,
      ‖axialPathSum (fun a μ => linearCoeff ζ (a, μ)) a • quaternionI‖ ≤ K * (1 + (offsetSupNorm a : ℝ)) ^ p := by
    intro ζ hz
    refine ⟨8, 2, fun a => ?_⟩
    rw [norm_smul, norm_quaternionI, mul_one, Real.norm_eq_abs]
    have := abs_axialPathSum_linearCoeff_le hz a
    nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm a)]
  set D : LatticeBond → ℝ := fun c => axialPathSum (fun a μ => linearCoeff ω (a, μ)) (c.1 + Pi.single c.2 1) -
    axialPathSum (fun a μ => linearCoeff ω (a, μ)) c.1 with hD
  set D' : LatticeBond → ℝ := fun c => axialPathSum (fun a μ => linearCoeff ω' (a, μ)) (c.1 + Pi.single c.2 1) -
    axialPathSum (fun a μ => linearCoeff ω' (a, μ)) c.1 with hD'
  have g1 := hgrad (fun a => axialPathSum (fun a μ => linearCoeff ω (a, μ)) a • quaternionI)
    (fun c => linearCoeff ω' c • quaternionI) (tg h1) (pg ha' h1').2
  have g2 := hgrad (fun a => axialPathSum (fun a μ => linearCoeff ω' (a, μ)) a • quaternionI)
    (fun c => constantCurvaturePotential ω c • quaternionI) (tg h1') (pg ha h1).1
  have gr : ∀ (ζ : Fin 4 → Fin 4 → ℝ) (c : LatticeBond),
      discreteGradient (fun a => axialPathSum (fun a μ => linearCoeff ζ (a, μ)) a • quaternionI) c =
        (axialPathSum (fun a μ => linearCoeff ζ (a, μ)) (c.1 + Pi.single c.2 1) -
          axialPathSum (fun a μ => linearCoeff ζ (a, μ)) c.1) • quaternionI := by
    intro ζ c
    simp only [discreteGradient]
    apply Subtype.ext
    simp [sub_smul]
  simp only [gr, hbil] at g1 g2
  have g1' : HasSum (fun cc : LatticeBond × LatticeBond => D cc.1 * linearCoeff ω' cc.2 * q cc.1 cc.2) 0 := g1
  have g2' : HasSum (fun cc : LatticeBond × LatticeBond =>
      D' cc.1 * constantCurvaturePotential ω cc.2 * q cc.1 cc.2) 0 := g2
  have hqs : ∀ c c', q c c' = q c' c := fun c c' => hsymm c c' quaternionI quaternionI
  have g3 : HasSum (fun cc : LatticeBond × LatticeBond =>
      constantCurvaturePotential ω cc.1 * D' cc.2 * q cc.1 cc.2) 0 := by
    have h := (Equiv.prodComm LatticeBond LatticeBond).hasSum_iff.2 g2'
    have fe : ((fun cc : LatticeBond × LatticeBond => D' cc.1 * constantCurvaturePotential ω cc.2 * q cc.1 cc.2) ∘
        (Equiv.prodComm LatticeBond LatticeBond)) =
        fun cc : LatticeBond × LatticeBond => constantCurvaturePotential ω cc.1 * D' cc.2 * q cc.1 cc.2 := by
      funext cc
      simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [hqs]
      ring
    rwa [fe] at h
  have antis : ∀ {ζ : Fin 4 → Fin 4 → ℝ}, (∀ i j, ζ i j = - ζ j i) →
      ∀ i j, curvatureAlong quaternionI ζ i j = - curvatureAlong quaternionI ζ j i := by
    intro ζ hz i j
    simp only [curvatureAlong]
    rw [hz i j]
    apply Subtype.ext
    simp
  have hT : HasSum (fun cc : LatticeBond × LatticeBond => linearCoeff ω cc.1 * linearCoeff ω' cc.2 * q cc.1 cc.2)
      (∑' cc, limitFormTerm f (curvatureAlong quaternionI ω) (curvatureAlong quaternionI ω') cc) := by
    have hs := (hcurv _ _ (antis ha) (antis ha')).hasSum
    have fe : ∀ cc : LatticeBond × LatticeBond, secondDerivLimit f cc.1 cc.2
        (linearPotential (curvatureAlong quaternionI ω) cc.1)
        (linearPotential (curvatureAlong quaternionI ω') cc.2) =
        linearCoeff ω cc.1 * linearCoeff ω' cc.2 * q cc.1 cc.2 := by
      intro cc
      rw [linearPotential_along_eq, linearPotential_along_eq, hbil]
    simp only [fe] at hs
    have e2 : (∑' cc, limitFormTerm f (curvatureAlong quaternionI ω) (curvatureAlong quaternionI ω') cc) =
        ∑' cc : LatticeBond × LatticeBond, linearCoeff ω cc.1 * linearCoeff ω' cc.2 * q cc.1 cc.2 :=
      tsum_congr fun cc => fe cc
    rw [e2]
    exact hs
  set S := ∑' cc, limitFormTerm f (curvatureAlong quaternionI ω) (curvatureAlong quaternionI ω') cc with hSdef
  set F : LatticeBond × LatticeBond → ℝ := fun cc =>
    q cc.1 cc.2 * (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2) with hFdef
  have hF : HasSum F S := by
    have h := (hT.sub g1').sub g3
    simp only [sub_zero] at h
    have e : (fun b : LatticeBond × LatticeBond => linearCoeff ω b.1 * linearCoeff ω' b.2 * q b.1 b.2 -
        D b.1 * linearCoeff ω' b.2 * q b.1 b.2 - constantCurvaturePotential ω b.1 * D' b.2 * q b.1 b.2) = F := by
      funext cc
      have a1 : constantCurvaturePotential ω cc.1 = linearCoeff ω cc.1 - D cc.1 :=
        constantCurvaturePotential_eq ha cc.1
      have a2 : constantCurvaturePotential ω' cc.2 = linearCoeff ω' cc.2 - D' cc.2 :=
        constantCurvaturePotential_eq ha' cc.2
      simp only [hFdef]
      linear_combination (-(linearCoeff ω' cc.2) * q cc.1 cc.2) * a1 +
        (-(q cc.1 cc.2) * constantCurvaturePotential ω cc.1) * a2
    rwa [e] at h
  set θ := ℓ.weightRate / 4 with hθdef
  have hθ : 0 < θ := by positivity
  set M : LatticeBond × LatticeBond → ℝ := fun cc => offsetMajorant θ cc.1 * offsetMajorant θ cc.2 with hMdef
  have hM : Summable M := Summable.mul_of_nonneg (summable_offsetMajorant hθ) (summable_offsetMajorant hθ)
    (offsetMajorant_nonneg θ) (offsetMajorant_nonneg θ)
  have hM0 : ∀ cc, 0 ≤ M cc := fun cc => mul_nonneg (offsetMajorant_nonneg θ _) (offsetMajorant_nonneg θ _)
  set e := Real.exp (-(ℓ.weightRate / 2 * m)) with hedef
  have he : 0 < e := Real.exp_pos _
  have split : ∀ (a b T : ℕ), a ≤ T → b ≤ T → m ≤ T →
      Real.exp (-(ℓ.weightRate * T)) ≤ e * Real.exp (-θ * a) * Real.exp (-θ * b) := by
    intro a b T ha hb hm
    rw [hedef, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha' : (a : ℝ) ≤ T := by exact_mod_cast ha
    have hb' : (b : ℝ) ≤ T := by exact_mod_cast hb
    have hm' : (m : ℝ) ≤ T := by exact_mod_cast hm
    simp only [hθdef]
    nlinarith
  have prodM : ∀ (cc : LatticeBond × LatticeBond) (T : ℕ), offsetSupNorm cc.1.1 ≤ T →
      offsetSupNorm cc.2.1 ≤ T → m ≤ T →
      |constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2| *
        Real.exp (-(ℓ.weightRate * T)) ≤ e * M cc := by
    intro cc T ha hb hm
    have s1 := split _ _ T ha hb hm
    have a1 := abs_constantCurvaturePotential_le h1 cc.1
    have a2 := abs_constantCurvaturePotential_le h1' cc.2
    rw [abs_mul]
    calc |constantCurvaturePotential ω cc.1| * |constantCurvaturePotential ω' cc.2| *
          Real.exp (-(ℓ.weightRate * T))
        ≤ (4 * offsetSupNorm cc.1.1) * (4 * offsetSupNorm cc.2.1) *
            (e * Real.exp (-θ * offsetSupNorm cc.1.1) * Real.exp (-θ * offsetSupNorm cc.2.1)) := by
          gcongr
      _ = e * M cc := by
          simp only [hMdef, offsetMajorant]
          ring
  have hQ : ∀ c ∈ bondsWithin m, ∀ c' ∈ bondsWithin m,
      |flatHessian (f n z) (bondFrom z c) (bondFrom z c') - q c c'| ≤ C * Real.exp (-(ℓ.weightRate * m)) := by
    intro c hc c' hc'
    have hl : Tendsto (fun k : ℕ => |flatHessian (f n z) (bondFrom z c) (bondFrom z c') -
        mixedDeriv (f k 0) (trivialField k) ![bondFrom 0 c, bondFrom 0 c'] ![quaternionI, quaternionI]|) atTop
        (𝓝 |flatHessian (f n z) (bondFrom z c) (bondFrom z c') - q c c'|) :=
      (tendsto_const_nhds.sub (hlim c c' quaternionI quaternionI)).abs
    refine le_of_tendsto hl ?_
    filter_upwards [eventually_ge_atTop (max ℓ.n₀ (2 * (m + 1) + 3))] with k hk
    have hk1 := (le_max_left _ _).trans hk
    have hk2 := (le_max_right _ _).trans hk
    have : NeZero k := ⟨by omega⟩
    refine (flatHessian_sub_mixedDeriv_le hℓ hf z hn hk1 h2 (by omega) hc hc').trans ?_
    have hw : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight (m + 1) := by
      refine le_trans (Real.exp_le_exp.mpr ?_) (exp_le_weight ℓ (m + 1))
      push_cast
      nlinarith
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hw
  have hoff : ∀ cc ∉ bondsWithin m ×ˢ bondsWithin m, |F cc| ≤ C * e * M cc := by
    intro cc hcc
    have hs : m ≤ offsetTriangleDiameter cc.1.1 cc.2.1 := by
      by_contra hlt
      push Not at hlt
      apply hcc
      have l1 : offsetSupNorm cc.1.1 ≤ offsetTriangleDiameter cc.1.1 cc.2.1 :=
        (le_max_left _ _).trans (le_max_left _ _)
      have l2 : offsetSupNorm cc.2.1 ≤ offsetTriangleDiameter cc.1.1 cc.2.1 :=
        (le_max_right _ _).trans (le_max_left _ _)
      exact Finset.mem_product.2 ⟨mem_bondsWithin.2 (by omega), mem_bondsWithin.2 (by omega)⟩
    have hb := hbound cc.1 cc.2 quaternionI quaternionI
    rw [norm_quaternionI, one_mul, one_mul] at hb
    have hb2 : |q cc.1 cc.2| ≤ C * Real.exp (-(ℓ.weightRate * offsetTriangleDiameter cc.1.1 cc.2.1)) := by
      refine hb.trans ?_
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hC
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) (exp_le_weight ℓ _)
    have hp := prodM cc (offsetTriangleDiameter cc.1.1 cc.2.1) ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)) hs
    simp only [hFdef]
    rw [abs_mul]
    calc |q cc.1 cc.2| * |constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2|
        ≤ C * Real.exp (-(ℓ.weightRate * offsetTriangleDiameter cc.1.1 cc.2.1)) *
            |constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2| := by
          gcongr
      _ = C * (|constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2| *
            Real.exp (-(ℓ.weightRate * offsetTriangleDiameter cc.1.1 cc.2.1))) := by ring
      _ ≤ C * (e * M cc) := by gcongr
      _ = C * e * M cc := by ring
  set s := bondsWithin m ×ˢ bondsWithin m with hsdef
  have hon : ∀ cc ∈ s, |(flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
      (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)| ≤ C * e * M cc := by
    intro cc hcc
    obtain ⟨c1, c2⟩ := Finset.mem_product.1 hcc
    have hp := prodM cc m (mem_bondsWithin.1 c1) (mem_bondsWithin.1 c2) le_rfl
    rw [abs_mul]
    calc _ ≤ C * Real.exp (-(ℓ.weightRate * m)) *
          |constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2| := by
          gcongr
          exact hQ _ c1 _ c2
      _ = C * (|constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2| *
          Real.exp (-(ℓ.weightRate * m))) := by ring
      _ ≤ C * (e * M cc) := by gcongr
      _ = C * e * M cc := by ring
  have first : |∑ cc ∈ s, (flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
      (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)| ≤ C * e * ∑' cc, M cc := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hon).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hM.sum_le_tsum s fun cc _ => hM0 cc) (by positivity)
  have second : |S - ∑ cc ∈ s, F cc| ≤ C * e * ∑' cc, M cc := by
    have hF1 : HasSum (fun cc => if cc ∈ s then F cc else 0) (∑ cc ∈ s, F cc) := by
      have h : HasSum (fun cc => if cc ∈ s then F cc else 0) (∑ cc ∈ s, (if cc ∈ s then F cc else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun cc hcc => by simp [hcc])
      have e2 : ∑ cc ∈ s, (if cc ∈ s then F cc else 0) = ∑ cc ∈ s, F cc :=
        Finset.sum_congr rfl fun cc hcc => by simp [hcc]
      rwa [e2] at h
    have hG := hF.sub hF1
    have hB := hM.hasSum.mul_left (C * e)
    have := hG.norm_le_of_bounded hB (fun cc => by
      by_cases hcc : cc ∈ s
      · simp only [hcc, if_true, sub_self, norm_zero]
        exact mul_nonneg (by positivity) (hM0 cc)
      · simp only [hcc, if_false, sub_zero, Real.norm_eq_abs]
        exact hoff cc hcc)
    simpa using this
  have key : ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian (f n z) (bondFrom z c) (bondFrom z c') *
      (constantCurvaturePotential ω c * constantCurvaturePotential ω' c') =
      (∑ cc ∈ s, (flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
        (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)) + ∑ cc ∈ s, F cc := by
    rw [← Finset.sum_add_distrib, hsdef, ← Finset.sum_product' (bondsWithin m) (bondsWithin m)
      (fun c c' => flatHessian (f n z) (bondFrom z c) (bondFrom z c') *
        (constantCurvaturePotential ω c * constantCurvaturePotential ω' c'))]
    refine Finset.sum_congr rfl fun cc _ => ?_
    simp only [hFdef]
    ring
  rw [key]
  have hfin : |(∑ cc ∈ s, (flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
      (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)) + ∑ cc ∈ s, F cc - S| ≤
      |∑ cc ∈ s, (flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
        (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)| + |S - ∑ cc ∈ s, F cc| := by
    have := abs_add_le (∑ cc ∈ s, (flatHessian (f n z) (bondFrom z cc.1) (bondFrom z cc.2) - q cc.1 cc.2) *
      (constantCurvaturePotential ω cc.1 * constantCurvaturePotential ω' cc.2)) (∑ cc ∈ s, F cc - S)
    rw [abs_sub_comm (∑ cc ∈ s, F cc) S] at this
    rwa [add_sub_assoc]
  refine hfin.trans ((add_le_add first second).trans (le_of_eq ?_))
  ring
theorem boxFormStatement_holds (hH : HessianAtTrivialFieldStatement)
    (hS : SecondOrderAtAbelianFields) : boxFormStatement := by
  intro ℓ hℓ C hC
  have hrate : 0 < ℓ.weightRate := by
    have := hℓ.rt_pos
    unfold StepParameters.weightRate
    positivity
  refine ⟨2 * C * (∑' cc : LatticeBond × LatticeBond, offsetMajorant (ℓ.weightRate / 4) cc.1 *
    offsetMajorant (ℓ.weightRate / 4) cc.2), ℓ.weightRate / 2, by positivity, ?_⟩
  intro f hf ω ω' ha ha' h1 h1' n _ z m hn h2
  exact abs_sum_sub_tsum_le hℓ hC hrate hH hS hf ha ha' h1 h1' z hn h2
end BoxForm
end YangMills.Construction
end
