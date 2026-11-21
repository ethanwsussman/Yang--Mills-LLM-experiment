import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageProof
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamilyProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfAStepOfTheCurvatureProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.StateLaw
open TorusFields TorusLumps FlatHessian
open BlockAverages hiding unitStep gaugeTransform
namespace SecondOrderExpansion
variable {n : ℕ}
private theorem iteratedFDeriv_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x := by
  simp only [← iteratedFDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedFDerivWithin_eq (by simpa using h) h.self_of_nhds k
private theorem iteratedFDeriv_comp_clm_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : F → ℝ} (L : E →L[ℝ] F) (hg : ContDiffAt ℝ 3 g (L 0)) {k : ℕ} (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (g ∘ L) 0 = (iteratedFDeriv ℝ k g (L 0)).compContinuousLinearMap fun _ => L := by
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨s, hss₀, hso, h0⟩ := mem_nhds_iff.1 hs₀
  have hs := hgs₀.mono hss₀
  have hpre : IsOpen (L ⁻¹' s) := hso.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hs hso.uniqueDiffOn hpre.uniqueDiffOn (x := 0) h0 (i := k)
    (by exact_mod_cast hk)
  rwa [iteratedFDerivWithin_of_isOpen k hpre (show (0 : E) ∈ L ⁻¹' s from h0), iteratedFDerivWithin_of_isOpen k hso h0] at h
private def matrixCLM {N k : ℕ} (A : Fin N → Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun l => ∑ i, A l i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
private theorem matrixCLM_apply {N k : ℕ} (A : Fin N → Fin k → ℝ) (s : Fin k → ℝ) (l : Fin N) :
    matrixCLM A s l = ∑ i, A l i * s i := by
  simp [matrixCLM]
private def chart {N : ℕ} (u : TorusField n → ℝ) (W : TorusField n) (c : Fin N → TorusBond n)
    (X : Fin N → imaginaryQuaternions) : (Fin N → ℝ) → ℝ :=
  fun s => u (perturb c X s W)
private theorem mixedDeriv_eq_chart {N k : ℕ} {u : TorusField n → ℝ} {W : TorusField n} {c : Fin N → TorusBond n}
    {X : Fin N → imaginaryQuaternions} {c' : Fin k → TorusBond n} {X' : Fin k → imaginaryQuaternions}
    (A : Fin N → Fin k → ℝ) (hk : k ≤ 3)
    (hC : ContDiffAt ℝ 3 (chart u W c X) 0) (hA : ∀ s, perturb c' X' s W = perturb c X (matrixCLM A s) W) :
    mixedDeriv u W c' X' = iteratedFDeriv ℝ k (chart u W c X) 0 (fun i => matrixCLM A (Pi.single i 1)) := by
  have e : (fun s : Fin k → ℝ => u (perturb c' X' s W)) = chart u W c X ∘ matrixCLM A := by
    funext s
    simp [chart, hA]
  unfold mixedDeriv
  rw [e, iteratedFDeriv_comp_clm_zero (matrixCLM A) (by simpa using hC) hk]
  simp
private def relabelMatrix {N k : ℕ} (f : Fin k → Fin N) : Fin N → Fin k → ℝ := fun l i => if f i = l then 1 else 0
private theorem matrixCLM_relabel_single {N k : ℕ} (f : Fin k → Fin N) (i : Fin k) :
    matrixCLM (relabelMatrix f) (Pi.single i 1) = Pi.single (f i) 1 := by
  funext l
  rw [matrixCLM_apply]
  simp [relabelMatrix, Pi.single_apply, eq_comm]
private theorem perturb_relabel {N k : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions) (f : Fin k → Fin N)
    (W : TorusField n) (s : Fin k → ℝ) :
    perturb (c ∘ f) (X ∘ f) s W = perturb c X (matrixCLM (relabelMatrix f) s) W := by
  funext x i
  simp only [perturb]
  congr 2
  have h : ∀ l, (if c l = (x, i) then matrixCLM (relabelMatrix f) s l • X l else 0) =
      ∑ j, if f j = l then (if c (f j) = (x, i) then s j • X (f j) else 0) else 0 := by
    intro l
    rw [matrixCLM_apply]
    by_cases hc : c l = (x, i)
    · rw [if_pos hc, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hf : f j = l
      · simp [relabelMatrix, hf, hc]
      · simp [relabelMatrix, hf]
    · rw [if_neg hc]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hf : f j = l
      · simp [hf, hc]
      · simp [hf]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
private theorem mixedDeriv_comp {N k : ℕ} {u : TorusField n → ℝ} {W : TorusField n} {c : Fin N → TorusBond n}
    {X : Fin N → imaginaryQuaternions} (f : Fin k → Fin N)
    (hk : k ≤ 3) (hC : ContDiffAt ℝ 3 (chart u W c X) 0) :
    mixedDeriv u W (c ∘ f) (X ∘ f) = iteratedFDeriv ℝ k (chart u W c X) 0 (fun i => Pi.single (f i) 1) := by
  rw [mixedDeriv_eq_chart (relabelMatrix f) hk hC (perturb_relabel c X f W)]
  simp only [matrixCLM_relabel_single]
private def quaternionJ : imaginaryQuaternions := ⟨⟨0, 0, 1, 0⟩, rfl⟩
private def quaternionK : imaginaryQuaternions := ⟨⟨0, 0, 0, 1⟩, rfl⟩
private def imagBasis : Fin 3 → imaginaryQuaternions := ![_root_.YangMills.Construction.FlatHessian.quaternionI, quaternionJ, quaternionK]
private theorem norm_eq_one_of_normSq {q : ℍ[ℝ]} (h : Quaternion.normSq q = 1) : ‖q‖ = 1 := by
  have h2 : ‖q‖ * ‖q‖ = 1 := by rw [← Quaternion.normSq_eq_norm_mul_self, h]
  nlinarith [norm_nonneg q]
private theorem normSq_imagBasis (e : Fin 3) : Quaternion.normSq (imagBasis e : ℍ[ℝ]) = 1 := by
  rw [Quaternion.normSq_def']
  fin_cases e <;> simp [imagBasis, _root_.YangMills.Construction.FlatHessian.quaternionI, quaternionJ, quaternionK]
private theorem norm_imagBasis (e : Fin 3) : ‖(imagBasis e : ℍ[ℝ])‖ = 1 := norm_eq_one_of_normSq (normSq_imagBasis e)
private theorem imagBasis_coords (e : Fin 3) : ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).re = 0 ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imI = (if e = 0 then 1 else 0) ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imJ = (if e = 1 then 1 else 0) ∧
    ((imagBasis e : imaginaryQuaternions) : ℍ[ℝ]).imK = (if e = 2 then 1 else 0) := by
  fin_cases e <;> refine ⟨rfl, ?_, ?_, ?_⟩ <;> first | rfl | simp [imagBasis, _root_.YangMills.Construction.FlatHessian.quaternionI, quaternionJ, quaternionK]
private theorem eq_sum_imaginaryComponent (v : imaginaryQuaternions) : v = ∑ e, imaginaryComponent e v • imagBasis e := by
  apply Subtype.ext
  have hv : (v : ℍ[ℝ]).re = 0 := v.2
  have c0 := imagBasis_coords 0
  have c1 := imagBasis_coords 1
  have c2 := imagBasis_coords 2
  simp only [Fin.sum_univ_three, Submodule.coe_add, Submodule.coe_smul]
  ext
  · simp [imaginaryComponent, c0.1, c1.1, c2.1, hv]
  · simp [imaginaryComponent, c0.2.1, c1.2.1, c2.2.1]
  · simp [imaginaryComponent, c0.2.2.1, c1.2.2.1, c2.2.2.1]
  · simp [imaginaryComponent, c0.2.2.2, c1.2.2.2, c2.2.2.2]
private theorem abs_imaginaryComponent_le (e : Fin 3) (v : imaginaryQuaternions) :
    |imaginaryComponent e v| ≤ ‖(v : ℍ[ℝ])‖ := by apply _root_.YangMills.SharedProofs.p13926 <;> assumption
private def unitOfNormSq (q : ℍ[ℝ]) (h : Quaternion.normSq q = 1) : UnitQuaternion :=
  ⟨q, by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, h]
      simp
    · rw [Quaternion.self_mul_star, h]
      simp⟩
private theorem coe_inv_unitQuaternion (q : UnitQuaternion) : ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (q : ℍ[ℝ])⁻¹ := by
  have h : (q : ℍ[ℝ]) * ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    have : ((q * q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by simp
    exact this
  exact eq_inv_of_mul_eq_one_right h
private local instance quaternionRatAlgebra : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
private theorem conj_expUnit (q : UnitQuaternion) (v v' : imaginaryQuaternions)
    (h : (q : ℍ[ℝ]) * (v : ℍ[ℝ]) = (v' : ℍ[ℝ]) * q) :
    q * expUnit v * q⁻¹ = expUnit v' := by
  have hq : (q : ℍ[ℝ]) ≠ 0 := by
    intro h0
    have := norm_coe_unitQuaternion q
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  apply Subtype.ext
  have hv : (v' : ℍ[ℝ]) = (Units.mk0 _ hq : (ℍ[ℝ])ˣ) * (v : ℍ[ℝ]) * ((Units.mk0 _ hq : (ℍ[ℝ])ˣ)⁻¹ : (ℍ[ℝ])ˣ) := by
    simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [h, mul_assoc, mul_inv_cancel₀ hq, mul_one]
  change (q : ℍ[ℝ]) * NormedSpace.exp (v : ℍ[ℝ]) * ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (v' : ℍ[ℝ])
  rw [hv, NormedSpace.exp_units_conj, coe_inv_unitQuaternion]
  simp
private def bondSum {N : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions) (s : Fin N → ℝ)
    (b : TorusBond n) : imaginaryQuaternions :=
  ∑ l, if c l = b then s l • X l else 0
private theorem perturb_trivialField {N : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions) (s : Fin N → ℝ) :
    perturb c X s (trivialField n) = expField (bondSum c X s) := by
  funext x i
  simp [perturb, trivialField, expField, bondSum]
private theorem norm_coe_mul_sub_one (a b : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem norm_coe_inv_sub_one_self (a : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem isCold_expField_of_small {σ ε : ℝ} (ξ : TorusBond n → imaginaryQuaternions)
    (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ ε) (h : 4 * ε < σ) :
    IsCold σ (expField ξ) := by
  intro x μ ν _
  have hb : ∀ b : TorusBond n, ‖((expUnit (ξ b) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := fun b =>
    (norm_exp_sub_one_le (ξ b).2).trans (hξ b)
  have h1 := norm_coe_mul_sub_one
    (expField ξ x μ * expField ξ (x + unitStep n μ) ν * (expField ξ (x + unitStep n ν) μ)⁻¹)
    (expField ξ x ν)⁻¹
  have h2 := norm_coe_mul_sub_one (expField ξ x μ * expField ξ (x + unitStep n μ) ν)
    (expField ξ (x + unitStep n ν) μ)⁻¹
  have h3 := norm_coe_mul_sub_one (expField ξ x μ) (expField ξ (x + unitStep n μ) ν)
  rw [norm_coe_inv_sub_one_self] at h1 h2
  have b1 := hb (x, μ)
  have b2 := hb (x + unitStep n μ, ν)
  have b3 := hb (x + unitStep n ν, μ)
  have b4 := hb (x, ν)
  have e : curvature (expField ξ) x μ ν = ‖((expField ξ x μ * expField ξ (x + unitStep n μ) ν *
      (expField ξ (x + unitStep n ν) μ)⁻¹ * (expField ξ x ν)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := rfl
  rw [e]
  simp only [expField] at h1 h2 h3 ⊢
  linarith
abbrev _root_.YangMills.SharedProofs.p24113 := @isCold_expField_of_small
variable [NeZero n]
private theorem eventually_norm_bondSum_le {N : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : Fin N → ℝ), ∀ b, ‖(bondSum c X s b : ℍ[ℝ])‖ ≤ ε := by
  rw [eventually_all]
  intro b
  have hc : Continuous fun s : Fin N → ℝ => ‖(bondSum c X s b : ℍ[ℝ])‖ := by
    refine continuous_norm.comp (continuous_subtype_val.comp ?_)
    refine continuous_finsetSum _ fun l _ => ?_
    by_cases h : c l = b
    · simp only [h, if_true]
      exact (continuous_apply l).smul continuous_const
    · simp only [h, if_false]
      exact continuous_const
  have h0 : ‖(bondSum c X (0 : Fin N → ℝ) b : ℍ[ℝ])‖ = 0 := by
    simp [bondSum]
  have := hc.tendsto (0 : Fin N → ℝ)
  rw [h0] at this
  exact (this.eventually (gt_mem_nhds hε)).mono fun s h => le_of_lt h
variable {σ₀ E E₃ : ℝ} {w : ℕ → ℝ} {y : TorusSite n} {u : TorusField n → ℝ}
private theorem eventually_isCold_perturb {N : ℕ} (hσ : 0 < σ₀) (c : Fin N → TorusBond n)
    (X : Fin N → imaginaryQuaternions) :
    ∀ᶠ s in 𝓝 (0 : Fin N → ℝ), IsCold σ₀ (perturb c X s (trivialField n)) := by
  filter_upwards [eventually_norm_bondSum_le c X (show 0 < σ₀ / 8 by positivity)] with s h
  rw [perturb_trivialField]
  exact isCold_expField_of_small _ h (by linarith)
private theorem isCold_trivialField (hσ : 0 < σ₀) : IsCold σ₀ (trivialField n) := by apply _root_.YangMills.Construction.ImageDensities.isCold_trivialField <;> assumption
private theorem mixedDeriv_conj (hu : IsRegularObservable σ₀ E E₃ w y u) (hσ : 0 < σ₀) {k : ℕ} (c : Fin k → TorusBond n)
    (X X' : Fin k → imaginaryQuaternions) (q : UnitQuaternion)
    (h : ∀ l, (q : ℍ[ℝ]) * (X l : ℍ[ℝ]) = (X' l : ℍ[ℝ]) * q) :
    mixedDeriv u (trivialField n) c X' = mixedDeriv u (trivialField n) c X := by
  unfold mixedDeriv
  congr 1
  apply iteratedFDeriv_eq_of_eventuallyEq
  filter_upwards [eventually_isCold_perturb hσ c X] with s hc
  rw [← hu.gauge_invariant (fun _ => q) _ hc]
  congr 1
  funext x i
  simp only [gaugeTransform, perturb, trivialField, mul_one]
  refine (conj_expUnit q _ _ ?_).symm
  simp only [Submodule.coe_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : c l = (x, i)
  · simp [hl, h l]
  · simp [hl]
private theorem mixedDeriv_smul {W : TorusField n} {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (a : Fin k → ℝ)
    (hC : ContDiffAt ℝ 3 (chart u W c X) 0) :
    mixedDeriv u W c (fun l => a l • X l) = (∏ l, a l) * mixedDeriv u W c X := by
  have hA : ∀ s, perturb c (fun l => a l • X l) s W =
      perturb c X (matrixCLM (fun l i => if i = l then a l else 0) s) W := by
    intro s
    funext x i
    simp only [perturb]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [matrixCLM_apply]
    simp [smul_smul, mul_comm]
  rw [mixedDeriv_eq_chart _ hk hC hA]
  have e : (fun i => matrixCLM (fun l i => if i = l then a l else 0) (Pi.single i 1)) =
      fun i => a i • (Pi.single i 1 : Fin k → ℝ) := by
    funext i l
    rw [matrixCLM_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [e, ContinuousMultilinearMap.map_smul_univ]
  rfl
private theorem imagBasis_anticomm (e f : Fin 3) (h : e ≠ f) :
    (imagBasis e : ℍ[ℝ]) * (imagBasis f : ℍ[ℝ]) = ((-imagBasis f : imaginaryQuaternions) : ℍ[ℝ]) * (imagBasis e : ℍ[ℝ]) := by
  have ce := imagBasis_coords e
  have cf := imagBasis_coords f
  rw [Submodule.coe_neg]
  fin_cases e <;> fin_cases f <;> first | exact absurd rfl h | skip
  all_goals
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at ce cf
    ext <;> simp [ce.1, ce.2.1, ce.2.2.1, ce.2.2.2, cf.1, cf.2.1, cf.2.2.1, cf.2.2.2]
private def imagBasisUnit (e : Fin 3) : UnitQuaternion := unitOfNormSq (imagBasis e) (normSq_imagBasis e)
private def cyclicUnit : UnitQuaternion :=
  unitOfNormSq ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ ((Quaternion.normSq_def' _).trans (by norm_num))
private theorem cyclicUnit_coords : ((cyclicUnit : UnitQuaternion) : ℍ[ℝ]).re = 1 / 2 ∧
    ((cyclicUnit : UnitQuaternion) : ℍ[ℝ]).imI = 1 / 2 ∧
    ((cyclicUnit : UnitQuaternion) : ℍ[ℝ]).imJ = 1 / 2 ∧ ((cyclicUnit : UnitQuaternion) : ℍ[ℝ]).imK = 1 / 2 :=
  ⟨rfl, rfl, rfl, rfl⟩
private theorem cyclicUnit_conj_imagBasis (e : Fin 3) :
    ((cyclicUnit : UnitQuaternion) : ℍ[ℝ]) * (imagBasis e : ℍ[ℝ]) =
      (imagBasis (e + 1) : ℍ[ℝ]) * (cyclicUnit : UnitQuaternion) := by
  have ce := imagBasis_coords e
  have cf := imagBasis_coords (e + 1)
  obtain ⟨t0, t1, t2, t3⟩ := cyclicUnit_coords
  fin_cases e
  all_goals
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, zero_add, Fin.reduceAdd] at ce cf ⊢
    ext <;> simp [ce.1, ce.2.1, ce.2.2.1, ce.2.2.2, cf.1, cf.2.1, cf.2.2.1, cf.2.2.2, t0, t1, t2, t3]
variable (hu : IsRegularObservable σ₀ E E₃ w y u) (hσ : 0 < σ₀)
include hu hσ
private theorem contDiffAt_chart_trivialField {N : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (chart u (trivialField n) c X) 0 :=
  hu.contDiff _ (isCold_trivialField hσ) N c X
private theorem mixedDeriv_one_eq_zero (c : Fin 1 → TorusBond n) (X : Fin 1 → imaginaryQuaternions) (e : Fin 3)
    (hX : X 0 = imagBasis e) :
    mixedDeriv u (trivialField n) c X = 0 := by
  have hX' : X = fun _ => imagBasis e := by
    funext l
    rw [Subsingleton.elim l 0, hX]
  subst hX'
  obtain ⟨f, hf⟩ : ∃ f : Fin 3, e ≠ f := ⟨e + 1, by fin_cases e <;> decide⟩
  have h1 := mixedDeriv_conj hu hσ c (fun _ => imagBasis e) (fun _ => -imagBasis e) (imagBasisUnit f) (fun _ => by
    have := imagBasis_anticomm f e (Ne.symm hf)
    exact this)
  have h2 := mixedDeriv_smul (u := u) (W := trivialField n) (by norm_num) c (fun _ => imagBasis e) (fun _ => -1)
    (contDiffAt_chart_trivialField hu hσ c _)
  have e2 : (fun l : Fin 1 => (fun _ => (-1 : ℝ)) l • (fun _ => imagBasis e) l) = fun _ => -imagBasis e := by
    funext l
    exact neg_one_smul ℝ (imagBasis e)
  have hp : (∏ l : Fin 1, (fun _ => (-1 : ℝ)) l) = -1 := by simp
  rw [e2, hp] at h2
  rw [h2] at h1
  linarith
private theorem mixedDeriv_two_offDiag (b b' : TorusBond n) (e f : Fin 3) (h : e ≠ f) :
    mixedDeriv u (trivialField n) ![b, b'] ![imagBasis e, imagBasis f] = 0 := by
  have h1 := mixedDeriv_conj hu hσ ![b, b'] ![imagBasis e, imagBasis f] ![imagBasis e, -imagBasis f] (imagBasisUnit e)
    (fun l => by
      fin_cases l
      · rfl
      · exact imagBasis_anticomm e f h)
  have h2 := mixedDeriv_smul (u := u) (W := trivialField n) (by norm_num) ![b, b'] ![imagBasis e, imagBasis f] ![1, -1]
    (contDiffAt_chart_trivialField hu hσ _ _)
  have e2 : (fun l => (![1, -1] : Fin 2 → ℝ) l • (![imagBasis e, imagBasis f] : Fin 2 → imaginaryQuaternions) l) =
      ![imagBasis e, -imagBasis f] := by
    funext l
    fin_cases l
    · exact one_smul ℝ (imagBasis e)
    · exact neg_one_smul ℝ (imagBasis f)
  have hp : (∏ l : Fin 2, (![1, -1] : Fin 2 → ℝ) l) = -1 := by simp [Fin.prod_univ_two]
  rw [e2, hp] at h2
  rw [h2] at h1
  linarith
private theorem mixedDeriv_two_diag (b b' : TorusBond n) (e : Fin 3) :
    mixedDeriv u (trivialField n) ![b, b'] ![imagBasis e, imagBasis e] = flatHessian u b b' := by
  have step : ∀ e : Fin 3, mixedDeriv u (trivialField n) ![b, b'] ![imagBasis (e + 1), imagBasis (e + 1)] =
      mixedDeriv u (trivialField n) ![b, b'] ![imagBasis e, imagBasis e] := fun e =>
    mixedDeriv_conj hu hσ ![b, b'] _ _ cyclicUnit (fun l => by
      fin_cases l <;> exact cyclicUnit_conj_imagBasis e)
  have s0 := step 0
  have s1 := step 1
  unfold flatHessian
  fin_cases e
  · rfl
  · exact s0
  · exact s1.trans s0
private theorem mixedDeriv_two_eq_fderiv {N : ℕ} (c : Fin N → TorusBond n) (X : Fin N → imaginaryQuaternions)
    (W : TorusField n) (hC : ContDiffAt ℝ 3 (chart u W c X) 0) (l l' : Fin N) :
    mixedDeriv u W ![c l, c l'] ![X l, X l'] =
      fderiv ℝ (fderiv ℝ (chart u W c X)) 0 (Pi.single l 1) (Pi.single l' 1) := by
  have h := mixedDeriv_comp (u := u) (W := W) (c := c) (X := X) ![l, l'] (by norm_num) hC
  have e1 : c ∘ ![l, l'] = ![c l, c l'] := by
    funext i
    fin_cases i <;> rfl
  have e2 : X ∘ ![l, l'] = ![X l, X l'] := by
    funext i
    fin_cases i <;> rfl
  rw [e1, e2] at h
  rw [h, iteratedFDeriv_two_apply]
  rfl
private def bondEquiv (n : ℕ) [NeZero n] : TorusBond n ≃ Fin (Fintype.card (TorusBond n)) := Fintype.equivFin _
private theorem flatHessian_eq_fderiv (l l' : Fin (Fintype.card (TorusBond n))) :
    flatHessian u ((bondEquiv n).symm l) ((bondEquiv n).symm l') =
      fderiv ℝ (fderiv ℝ (chart u (trivialField n) (bondEquiv n).symm fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI)) 0
        (Pi.single l 1) (Pi.single l' 1) :=
  mixedDeriv_two_eq_fderiv hu hσ (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI) (trivialField n)
    (contDiffAt_chart_trivialField hu hσ _ _) l l'
private theorem flatHessian_symm (b b' : TorusBond n) : flatHessian u b b' = flatHessian u b' b := by
  have hC := contDiffAt_chart_trivialField hu hσ (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI)
  have hs : IsSymmSndFDerivAt ℝ (chart u (trivialField n) (bondEquiv n).symm fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI) 0 :=
    hC.isSymmSndFDerivAt (by simp; norm_num)
  have h1 := flatHessian_eq_fderiv hu hσ (bondEquiv n b) (bondEquiv n b')
  have h2 := flatHessian_eq_fderiv hu hσ (bondEquiv n b') (bondEquiv n b)
  simp only [Equiv.symm_apply_apply] at h1 h2
  rw [h1, h2]
  exact hs _ _
private theorem abs_flatHessian_le (b b' : TorusBond n) : |flatHessian u b b'| ≤ E / w (supportDiam y ![b, b']) := by
  have h := hu.deriv_bound (trivialField n) (isCold_trivialField hσ) 2 ![b, b'] ![_root_.YangMills.Construction.FlatHessian.quaternionI, _root_.YangMills.Construction.FlatHessian.quaternionI]
    (by norm_num) (by norm_num) (by
      intro l
      fin_cases l <;> exact norm_imagBasis 0)
  simpa [flatHessian] using h
omit hu hσ in
private theorem bondSum_bondEquiv (s : Fin (Fintype.card (TorusBond n)) → ℝ) (b : TorusBond n) :
    bondSum (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI) s b = s (bondEquiv n b) • _root_.YangMills.Construction.FlatHessian.quaternionI := by
  unfold bondSum
  rw [Finset.sum_eq_single (bondEquiv n b)]
  · simp
  · intro l _ hl
    have : (bondEquiv n).symm l ≠ b := fun h => hl (by rw [← h]; simp)
    simp [this]
  · simp
omit hu hσ in
private theorem expUnit_smul_mul_smul (v : imaginaryQuaternions) (p q : ℝ) :
    expUnit (p • v) * expUnit (q • v) = expUnit ((p + q) • v) := by apply _root_.YangMills.Construction.TorusFrame.expUnit_smul_mul <;> assumption
omit hu hσ in
private theorem expUnit_inv_eq (v : imaginaryQuaternions) : (expUnit v)⁻¹ = expUnit ((-1 : ℝ) • v) := by apply _root_.YangMills.SharedProofs.p44810 <;> assumption
omit hu hσ in
private theorem gaugeTransform_perturb (φ : TorusSite n → ℝ) (ε : ℝ) (s : Fin (Fintype.card (TorusBond n)) → ℝ) :
    gaugeTransform (fun x => expUnit ((ε * φ x) • _root_.YangMills.Construction.FlatHessian.quaternionI))
        (perturb (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI) s (trivialField n)) =
      perturb (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI)
        (s + ε • fun l => -latticeGradient φ ((bondEquiv n).symm l)) (trivialField n) := by
  rw [perturb_trivialField, perturb_trivialField]
  funext x i
  simp only [gaugeTransform, expField, bondSum_bondEquiv]
  rw [expUnit_inv_eq, smul_smul, expUnit_smul_mul_smul, expUnit_smul_mul_smul]
  congr 2
  simp [latticeGradient]
  ring
private theorem fderiv_chart_gradient_eq_zero (φ : TorusSite n → ℝ) :
    ∀ᶠ s in 𝓝 (0 : Fin (Fintype.card (TorusBond n)) → ℝ),
      fderiv ℝ (chart u (trivialField n) (bondEquiv n).symm fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI) s
        (fun l => -latticeGradient φ ((bondEquiv n).symm l)) = 0 := by
  have hC := contDiffAt_chart_trivialField hu hσ (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI)
  filter_upwards [eventually_isCold_perturb hσ (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI), hC.eventually (by simp)]
    with s hc hd
  set g := chart u (trivialField n) (bondEquiv n).symm fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI with hg
  set d : Fin (Fintype.card (TorusBond n)) → ℝ := fun l => -latticeGradient φ ((bondEquiv n).symm l) with hdd
  have hconst : ∀ ε : ℝ, g (s + ε • d) = g s := by
    intro ε
    simp only [hg, chart]
    rw [← gaugeTransform_perturb, hu.gauge_invariant _ _ hc]
  have hdiff : DifferentiableAt ℝ g s := hd.differentiableAt (by simp)
  have hline : HasDerivAt (fun ε : ℝ => s + ε • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add s
  have h1 : HasDerivAt (fun ε : ℝ => g (s + ε • d)) (fderiv ℝ g s d) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hline (by simp)
  have h2 : HasDerivAt (fun ε : ℝ => g (s + ε • d)) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact h1.unique h2
private theorem sum_latticeGradient_mul_flatHessian (φ : TorusSite n → ℝ) (b' : TorusBond n) :
    ∑ b, latticeGradient φ b * flatHessian u b b' = 0 := by
  have hC := contDiffAt_chart_trivialField hu hσ (bondEquiv n).symm (fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI)
  set g := chart u (trivialField n) (bondEquiv n).symm fun _ => _root_.YangMills.Construction.FlatHessian.quaternionI with hg
  set d : Fin (Fintype.card (TorusBond n)) → ℝ := fun l => -latticeGradient φ ((bondEquiv n).symm l) with hdd
  have hD : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hC.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hF : HasFDerivAt (fun s => fderiv ℝ g s d)
      ((ContinuousLinearMap.apply ℝ ℝ d).comp (fderiv ℝ (fderiv ℝ g) 0)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp 0 hD.hasFDerivAt
  have hZ : HasFDerivAt (fun s => fderiv ℝ g s d) (0 : (Fin (Fintype.card (TorusBond n)) → ℝ) →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq (fderiv_chart_gradient_eq_zero hu hσ φ)
  have hU := hF.unique hZ
  have hv : fderiv ℝ (fderiv ℝ g) 0 (Pi.single (bondEquiv n b') 1) d = 0 := by
    have := congrArg (fun L : (Fin (Fintype.card (TorusBond n)) → ℝ) →L[ℝ] ℝ => L (Pi.single (bondEquiv n b') 1)) hU
    simpa using this
  have hexp : d = ∑ l, d l • (Pi.single l 1 : Fin (Fintype.card (TorusBond n)) → ℝ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hexp, map_sum] at hv
  have e : ∀ l, fderiv ℝ (fderiv ℝ g) 0 (Pi.single (bondEquiv n b') 1)
      (d l • (Pi.single l 1 : Fin (Fintype.card (TorusBond n)) → ℝ)) =
      -(latticeGradient φ ((bondEquiv n).symm l) * flatHessian u ((bondEquiv n).symm l) b') := by
    intro l
    have h1 := flatHessian_eq_fderiv hu hσ (bondEquiv n b') l
    simp only [Equiv.symm_apply_apply] at h1
    rw [map_smul, ← hg] at *
    rw [← h1, flatHessian_symm hu hσ b' _]
    simp [hdd]
  rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_neg_distrib, neg_eq_zero] at hv
  rw [← Equiv.sum_comp (bondEquiv n).symm]
  exact hv
private def colorEquiv (n : ℕ) [NeZero n] : TorusBond n × Fin 3 ≃ Fin (Fintype.card (TorusBond n × Fin 3)) :=
  Fintype.equivFin _
private def colorBond : Fin (Fintype.card (TorusBond n × Fin 3)) → TorusBond n := fun l => ((colorEquiv n).symm l).1
private def colorDir : Fin (Fintype.card (TorusBond n × Fin 3)) → imaginaryQuaternions :=
  fun l => imagBasis ((colorEquiv n).symm l).2
private def colorCoords (ξ : TorusBond n → imaginaryQuaternions) : Fin (Fintype.card (TorusBond n × Fin 3)) → ℝ :=
  fun l => imaginaryComponent ((colorEquiv n).symm l).2 (ξ ((colorEquiv n).symm l).1)
omit hu hσ in
private theorem bondSum_colorCoords (ξ : TorusBond n → imaginaryQuaternions) (b : TorusBond n) :
    bondSum colorBond colorDir (colorCoords ξ) b = ξ b := by
  unfold bondSum
  rw [← Equiv.sum_comp (colorEquiv n)]
  simp only [colorBond, colorDir, colorCoords, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (eq_sum_imaginaryComponent (ξ b)).symm
omit hu hσ in
private theorem imaginaryComponent_smul (e : Fin 3) (τ : ℝ) (v : imaginaryQuaternions) :
    imaginaryComponent e (τ • v) = τ * imaginaryComponent e v := by
  fin_cases e <;> simp [imaginaryComponent]
omit hu hσ in
private theorem colorCoords_smul (τ : ℝ) (ξ : TorusBond n → imaginaryQuaternions) :
    colorCoords (fun b => τ • ξ b) = τ • colorCoords ξ := by
  funext l
  simp [colorCoords, imaginaryComponent_smul]
omit hu hσ in
private theorem perturb_line (ξ : TorusBond n → imaginaryQuaternions) (ε τ : ℝ) :
    perturb colorBond colorDir (ε • colorCoords ξ) (expField fun b => τ • ξ b) = expField fun b => (ε + τ) • ξ b := by
  funext x i
  have h := bondSum_colorCoords (fun b => ε • ξ b) (x, i)
  rw [colorCoords_smul] at h
  change expUnit (bondSum colorBond colorDir (ε • colorCoords ξ) (x, i)) * expUnit (τ • ξ (x, i)) =
    expUnit ((ε + τ) • ξ (x, i))
  rw [h, expUnit_smul_mul_smul]
omit hu hσ in
private theorem line_eq_chart_comp (ξ : TorusBond n → imaginaryQuaternions) (τ : ℝ) :
    (fun ε : ℝ => u (expField fun b => (ε + τ) • ξ b)) =
      chart u (expField fun b => τ • ξ b) colorBond colorDir ∘
        (ContinuousLinearMap.id ℝ ℝ).smulRight (colorCoords ξ) := by
  funext ε
  simp [chart, perturb_line]
omit hu hσ in
private theorem multilinear_apply_const_eq_sum {N k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) ℝ)
    (r : Fin N → ℝ) :
    M (fun _ => r) = ∑ f : Fin k → Fin N, (∏ i, r (f i)) * M (fun i => Pi.single (f i) 1) := by
  have hr : r = ∑ l, r l • (Pi.single l 1 : Fin N → ℝ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have h := M.map_sum (fun (_ : Fin k) (l : Fin N) => r l • (Pi.single l 1 : Fin N → ℝ))
  rw [← hr] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ]
  rfl
abbrev _root_.YangMills.SharedProofs.p104744 := @multilinear_apply_const_eq_sum
private theorem isCold_line {ξ : TorusBond n → imaginaryQuaternions} (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) {τ : ℝ}
    (hτ : |τ| < 2) :
    IsCold σ₀ (expField fun b => τ • ξ b) := by
  refine isCold_expField_of_small (ε := σ₀ / 8) _ (fun b => ?_) (by linarith)
  rw [Submodule.coe_smul, norm_smul, Real.norm_eq_abs]
  have := hξ b
  nlinarith [abs_nonneg τ, norm_nonneg (ξ b : ℍ[ℝ])]
private theorem contDiffAt_line {ξ : TorusBond n → imaginaryQuaternions} (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) {τ : ℝ}
    (hτ : |τ| < 2) :
    ContDiffAt ℝ 3 (fun t : ℝ => u (expField fun b => t • ξ b)) τ := by
  have hC : ContDiffAt ℝ 3 (chart u (expField fun b => τ • ξ b) colorBond colorDir) 0 :=
    hu.contDiff _ (isCold_line hu hσ hξ hτ) _ colorBond colorDir
  have h0 : ContDiffAt ℝ 3 (fun ε : ℝ => u (expField fun b => (ε + τ) • ξ b)) 0 := by
    rw [line_eq_chart_comp]
    refine ContDiffAt.comp (0 : ℝ) ?_ ((ContinuousLinearMap.id ℝ ℝ).smulRight (colorCoords ξ)).contDiff.contDiffAt
    simpa using hC
  have h1 : ContDiffAt ℝ 3 ((fun ε : ℝ => u (expField fun b => (ε + τ) • ξ b)) ∘ fun t : ℝ => t - τ) τ :=
    ContDiffAt.comp τ (by simpa using h0) (contDiffAt_id.sub contDiffAt_const)
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp
private theorem iteratedDeriv_line {ξ : TorusBond n → imaginaryQuaternions} (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) {τ : ℝ}
    (hτ : |τ| < 2) {k : ℕ} (hk : k ≤ 3) :
    iteratedDeriv k (fun t : ℝ => u (expField fun b => t • ξ b)) τ =
      ∑ f : Fin k → Fin (Fintype.card (TorusBond n × Fin 3)), (∏ i, colorCoords ξ (f i)) *
        mixedDeriv u (expField fun b => τ • ξ b) (colorBond ∘ f) (colorDir ∘ f) := by
  have hC : ContDiffAt ℝ 3 (chart u (expField fun b => τ • ξ b) colorBond colorDir) 0 :=
    hu.contDiff _ (isCold_line hu hσ hξ hτ) _ colorBond colorDir
  have h1 := congrFun (iteratedDeriv_comp_add_const k (fun t : ℝ => u (expField fun b => t • ξ b)) τ) 0
  simp only [zero_add] at h1
  rw [← h1, iteratedDeriv_eq_iteratedFDeriv, line_eq_chart_comp,
    iteratedFDeriv_comp_clm_zero ((ContinuousLinearMap.id ℝ ℝ).smulRight (colorCoords ξ)) (by simpa using hC) hk]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
  rw [multilinear_apply_const_eq_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mixedDeriv_comp f hk hC]
omit hu hσ in
private theorem abs_colorCoords_le (ξ : TorusBond n → imaginaryQuaternions) (l : Fin (Fintype.card (TorusBond n × Fin 3))) :
    |colorCoords ξ l| ≤ ‖(ξ (colorBond l) : ℍ[ℝ])‖ := abs_imaginaryComponent_le _ _
omit hu hσ in
private theorem sum_comp_colorBond (T : (Fin 3 → TorusBond n) → ℝ) :
    ∑ f : Fin 3 → Fin (Fintype.card (TorusBond n × Fin 3)), T (colorBond ∘ f) = 27 * ∑ g, T g := by
  let e : (Fin 3 → Fin (Fintype.card (TorusBond n × Fin 3))) ≃ (Fin 3 → TorusBond n) × (Fin 3 → Fin 3) :=
    (Equiv.arrowCongr (Equiv.refl (Fin 3)) (colorEquiv n).symm).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [Fintype.sum_equiv e (fun f => T (colorBond ∘ f)) (fun p => T p.1) (fun f => rfl), Fintype.sum_prod_type]
  simp [Finset.mul_sum]
private theorem abs_iteratedDeriv_three_line_le {ξ : TorusBond n → imaginaryQuaternions}
    (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) {τ : ℝ} (hτ : |τ| < 2)
    (hw : ∀ m, 0 < w m) (hE : 0 ≤ E₃) :
    |iteratedDeriv 3 (fun t : ℝ => u (expField fun b => t • ξ b)) τ| ≤
      27 * E₃ * ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam y f) := by
  rw [iteratedDeriv_line hu hσ hξ hτ le_rfl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ f : Fin 3 → Fin (Fintype.card (TorusBond n × Fin 3)),
      |(∏ i, colorCoords ξ (f i)) * mixedDeriv u (expField fun b => τ • ξ b) (colorBond ∘ f) (colorDir ∘ f)| ≤
        (fun g : Fin 3 → TorusBond n => E₃ * ((∏ i, ‖(ξ (g i) : ℍ[ℝ])‖) / w (supportDiam y g))) (colorBond ∘ f) := by
    intro f
    have hd := hu.deriv_bound _ (isCold_line hu hσ hξ hτ) 3 (colorBond ∘ f) (colorDir ∘ f) (by norm_num) le_rfl
      (fun l => norm_imagBasis _)
    simp only [if_true] at hd
    rw [abs_mul, Finset.abs_prod]
    have hp : ∏ i, |colorCoords ξ (f i)| ≤ ∏ i, ‖(ξ ((colorBond ∘ f) i) : ℍ[ℝ])‖ :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_colorCoords_le ξ (f i))
    have hnn : 0 ≤ ∏ i, ‖(ξ ((colorBond ∘ f) i) : ℍ[ℝ])‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    calc _ ≤ (∏ i, ‖(ξ ((colorBond ∘ f) i) : ℍ[ℝ])‖) * (E₃ / w (supportDiam y (colorBond ∘ f))) :=
          mul_le_mul hp hd (abs_nonneg _) hnn
      _ = _ := by
          simp only
          ring
  refine (Finset.sum_le_sum fun f _ => hb f).trans (le_of_eq ?_)
  rw [sum_comp_colorBond (fun g : Fin 3 → TorusBond n => E₃ * ((∏ i, ‖(ξ (g i) : ℍ[ℝ])‖) / w (supportDiam y g))),
    ← Finset.mul_sum, mul_assoc]
omit hu hσ in
private theorem expField_zero_smul (ξ : TorusBond n → imaginaryQuaternions) :
    (expField fun b => (0 : ℝ) • ξ b) = trivialField n := by
  funext x i
  apply Subtype.ext
  change NormedSpace.exp (((0 : ℝ) • ξ (x, i) : imaginaryQuaternions) : ℍ[ℝ]) = 1
  simp
omit hu hσ in
private theorem expField_one_smul (ξ : TorusBond n → imaginaryQuaternions) :
    (expField fun b => (1 : ℝ) • ξ b) = expField ξ := by
  simp
private theorem iteratedDeriv_one_line_zero {ξ : TorusBond n → imaginaryQuaternions}
    (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) :
    iteratedDeriv 1 (fun t : ℝ => u (expField fun b => t • ξ b)) 0 = 0 := by
  rw [iteratedDeriv_line hu hσ hξ (by simp) (by norm_num), expField_zero_smul]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [mixedDeriv_one_eq_zero hu hσ (colorBond ∘ f) (colorDir ∘ f) ((colorEquiv n).symm (f 0)).2 rfl, mul_zero]
private theorem iteratedDeriv_two_line_zero {ξ : TorusBond n → imaginaryQuaternions}
    (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16) :
    iteratedDeriv 2 (fun t : ℝ => u (expField fun b => t • ξ b)) 0 =
      ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b' := by
  rw [iteratedDeriv_line hu hσ hξ (by simp) (by norm_num), expField_zero_smul]
  have e1 : ∀ f : Fin 2 → Fin (Fintype.card (TorusBond n × Fin 3)),
      (∏ i, colorCoords ξ (f i)) * mixedDeriv u (trivialField n) (colorBond ∘ f) (colorDir ∘ f) =
        (fun p : Fin (Fintype.card (TorusBond n × Fin 3)) × Fin (Fintype.card (TorusBond n × Fin 3)) =>
          colorCoords ξ p.1 * colorCoords ξ p.2 *
            mixedDeriv u (trivialField n) ![colorBond p.1, colorBond p.2] ![colorDir p.1, colorDir p.2])
          (finTwoArrowEquiv _ f) := by
    intro f
    have a1 : colorBond ∘ f = ![colorBond (f 0), colorBond (f 1)] := by
      funext i
      fin_cases i <;> rfl
    have a2 : colorDir ∘ f = ![colorDir (f 0), colorDir (f 1)] := by
      funext i
      fin_cases i <;> rfl
    simp [a1, a2, Fin.prod_univ_two, finTwoArrowEquiv]
  rw [Finset.sum_congr rfl fun f _ => e1 f,
    Equiv.sum_comp (finTwoArrowEquiv _)
      (fun p : Fin (Fintype.card (TorusBond n × Fin 3)) × Fin (Fintype.card (TorusBond n × Fin 3)) =>
        colorCoords ξ p.1 * colorCoords ξ p.2 *
          mixedDeriv u (trivialField n) ![colorBond p.1, colorBond p.2] ![colorDir p.1, colorDir p.2]),
    Fintype.sum_prod_type]
  have hre : ∀ F : Fin (Fintype.card (TorusBond n × Fin 3)) → Fin (Fintype.card (TorusBond n × Fin 3)) → ℝ,
      ∑ l, ∑ l', F l l' = ∑ b : TorusBond n, ∑ e : Fin 3, ∑ b' : TorusBond n, ∑ e' : Fin 3,
        F (colorEquiv n (b, e)) (colorEquiv n (b', e')) := by
    intro F
    rw [← Equiv.sum_comp (colorEquiv n) (fun l => ∑ l', F l l'), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
    rw [← Equiv.sum_comp (colorEquiv n) (fun l' => F (colorEquiv n (b, e)) l'), Fintype.sum_prod_type]
  rw [hre (fun l l' => colorCoords ξ l * colorCoords ξ l' *
    mixedDeriv u (trivialField n) ![colorBond l, colorBond l'] ![colorDir l, colorDir l'])]
  simp only [colorBond, colorDir, colorCoords, Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl ?_
  intro b' _
  have hd : ∀ e f : Fin 3, mixedDeriv u (trivialField n) ![b, b'] ![imagBasis e, imagBasis f] =
      if e = f then flatHessian u b b' else 0 := by
    intro e f
    by_cases h : e = f
    · subst h
      simp [mixedDeriv_two_diag hu hσ]
    · simp [h, mixedDeriv_two_offDiag hu hσ b b' e f h]
  simp only [hd, colorPairing, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring
private theorem abs_sub_sub_half_le {ξ : TorusBond n → imaginaryQuaternions} (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ σ₀ / 16)
    (hw : ∀ m, 0 < w m) (hE : 0 ≤ E₃) :
    |u (expField ξ) - u (trivialField n) - (1 / 2) * ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b'| ≤
      27 * E₃ * ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam y f) := by
  set G : ℝ → ℝ := fun t : ℝ => u (expField fun b => t • ξ b) with hG
  set B := 27 * E₃ * ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam y f) with hB
  have hder : ∀ k : ℕ, k < 3 → ∀ τ : ℝ, |τ| < 2 → HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G τ) τ := by
    intro k hk τ hτ
    have hc : ContDiffAt ℝ 3 G τ := contDiffAt_line hu hσ hξ hτ
    have hd : DifferentiableAt ℝ (iteratedDeriv k G) τ := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.differentiableAt.comp _
        (hc.differentiableAt_iteratedFDeriv (by exact_mod_cast hk))
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt
  have hs : ∀ τ ∈ Set.Icc (0 : ℝ) 1, |τ| < 2 := fun τ h => by
    rw [abs_of_nonneg h.1]
    linarith [h.2]
  have h3 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDeriv 3 G τ‖ ≤ B := fun τ h =>
    abs_iteratedDeriv_three_line_le hu hσ hξ (hs τ h) hw hE
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (h3 0 (by simp))
  have z0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have z1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hdist : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖τ - 0‖ ≤ 1 := fun τ h => by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDeriv 2 G τ - iteratedDeriv 2 G 0‖ ≤ B := fun τ h => by
    have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := iteratedDeriv 2 G) (f' := iteratedDeriv 3 G)
      (fun x hx => (hder 2 (by norm_num) x (hs x hx)).hasDerivWithinAt) h3 z0 h
    exact this.trans (mul_le_of_le_one_right hB0 (hdist τ h))
  have h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDeriv 1 G τ - τ * iteratedDeriv 2 G 0 - iteratedDeriv 1 G 0‖ ≤ B := fun τ h => by
    have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => iteratedDeriv 1 G t - t * iteratedDeriv 2 G 0)
      (f' := fun t => iteratedDeriv 2 G t - iteratedDeriv 2 G 0)
      (fun x hx => by
        have a := hder 1 (by norm_num) x (hs x hx)
        have b : HasDerivAt (fun t : ℝ => t * iteratedDeriv 2 G 0) (iteratedDeriv 2 G 0) x := by
          simpa using (hasDerivAt_id x).mul_const (iteratedDeriv 2 G 0)
        exact (a.fun_sub b).hasDerivWithinAt) h2 z0 h
    have e0 : iteratedDeriv 1 G τ - τ * iteratedDeriv 2 G 0 - (iteratedDeriv 1 G 0 - 0 * iteratedDeriv 2 G 0) =
        iteratedDeriv 1 G τ - τ * iteratedDeriv 2 G 0 - iteratedDeriv 1 G 0 := by ring
    rw [e0] at this
    exact this.trans (mul_le_of_le_one_right hB0 (hdist τ h))
  have h0 := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => iteratedDeriv 0 G t - t * iteratedDeriv 1 G 0 - t ^ 2 / 2 * iteratedDeriv 2 G 0)
      (f' := fun t => iteratedDeriv 1 G t - t * iteratedDeriv 2 G 0 - iteratedDeriv 1 G 0)
      (fun x hx => by
        have a := hder 0 (by norm_num) x (hs x hx)
        have b : HasDerivAt (fun t : ℝ => t * iteratedDeriv 1 G 0) (iteratedDeriv 1 G 0) x := by
          simpa using (hasDerivAt_id x).mul_const (iteratedDeriv 1 G 0)
        have c : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * iteratedDeriv 2 G 0) (x * iteratedDeriv 2 G 0) x := by
          have := (((hasDerivAt_id x).fun_pow 2).div_const 2).mul_const (iteratedDeriv 2 G 0)
          refine (this.congr_deriv ?_)
          simp
        refine (((a.fun_sub b).fun_sub c).congr_deriv ?_).hasDerivWithinAt
        ring) h1 z0 z1
  have e1 := iteratedDeriv_one_line_zero hu hσ hξ
  have e2 := iteratedDeriv_two_line_zero hu hσ hξ
  simp only [iteratedDeriv_zero] at h0
  rw [← hG] at e1 e2
  have v1 : G 1 = u (expField ξ) := by simp only [hG, expField_one_smul]
  have v0 : G 0 = u (trivialField n) := by simp only [hG, expField_zero_smul]
  rw [e1, e2, v1, v0] at h0
  simp only [Real.norm_eq_abs] at h0
  have e3 : u (expField ξ) - 1 * 0 - 1 ^ 2 / 2 * (∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b') -
      (u (trivialField n) - 0 * 0 - 0 ^ 2 / 2 * (∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b')) =
      u (expField ξ) - u (trivialField n) - (1 / 2) * ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b' := by ring
  rw [e3] at h0
  simpa using h0
end SecondOrderExpansion
theorem secondOrderExpansion : secondOrderExpansionStatement := by
  intro n _ σ E E₃ w y u hσ hw hE hu
  exact ⟨SecondOrderExpansion.flatHessian_symm hu hσ, SecondOrderExpansion.abs_flatHessian_le hu hσ,
    SecondOrderExpansion.sum_latticeGradient_mul_flatHessian hu hσ,
    fun ξ hξ => SecondOrderExpansion.abs_sub_sub_half_le hu hσ hξ hw hE⟩
end YangMills.Construction.StateLaw
end
