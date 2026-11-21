import YangMills.Construction.ConfigurationSpace.IterDirDerivLinear
import YangMills.Construction.ConfigurationSpace.MinSeparationProof
import YangMills.Construction.Continuum.FactsOfConfigurationSpaceAndItsTestFunctions
import YangMills.Construction.Continuum.FiniteSeminormsOnTheSchwartzFunctions
import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDual
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.Continuum.TwoFamiliesOfSeminormsOnSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.Facts
theorem maxNorm_eq_norm {I : Type*} [Fintype I] [Nonempty I] (v : I → ℝ) :
    maxNorm v = ‖v‖ := by
  have h0 : 0 ≤ maxNorm v :=
    Real.iSup_nonneg fun ι => abs_nonneg _
  apply le_antisymm
  · exact ciSup_le fun ι => by simpa using norm_le_pi_norm v ι
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ι => ?_
    rw [Real.norm_eq_abs]
    exact le_ciSup (f := fun ι => |v ι|) (Set.finite_range _).bddAbove ι
theorem norm_apply_le_configMaxNorm {n : ℕ} (x : Config n) (i : Fin n) :
    ‖x i‖ ≤ configMaxNorm x := by apply _root_.YangMills.Construction.ConfigurationSpace.MinSep.norm_apply_le_configMaxNorm <;> assumption
theorem exists_pair_minSeparation {n : ℕ} (hne : (orderedPairs n).Nonempty) (x : Config n) :
    ∃ p ∈ orderedPairs n, minSeparation x = ENNReal.ofReal ‖x p.1 - x p.2‖ ∧
      ∀ q ∈ orderedPairs n, ‖x p.1 - x p.2‖ ≤ ‖x q.1 - x q.2‖ := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (orderedPairs n) (fun p => ‖x p.1 - x p.2‖) hne
  refine ⟨p, hp, le_antisymm ?_ ?_, hmin⟩
  · refine iInf₂_le_of_le p hp ?_
    rw [maxNorm_eq_norm]
  · refine le_iInf₂ fun q hq => ?_
    rw [maxNorm_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hmin q hq)
theorem orderedPairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (orderedPairs n).Nonempty := by apply _root_.YangMills.Construction.ConfigurationSpace.MinSep.orderedPairs_nonempty <;> assumption
theorem norm_sub_apply_le {n : ℕ} (x x' : Config n) (a b : Fin n) :
    ‖x a - x b‖ ≤ ‖x' a - x' b‖ + 2 * configMaxNorm (x - x') := by
  have h₁ := norm_apply_le_configMaxNorm (x - x') a
  have h₂ := norm_apply_le_configMaxNorm (x - x') b
  have e : x a - x b = (x' a - x' b) + ((x - x') a - (x - x') b) := by
    simp only [Pi.sub_apply]
    abel
  rw [e]
  calc _ ≤ ‖x' a - x' b‖ + ‖(x - x') a - (x - x') b‖ := norm_add_le _ _
    _ ≤ ‖x' a - x' b‖ + (‖(x - x') a‖ + ‖(x - x') b‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith
theorem isClosed_fatDiagonal (n : ℕ) : IsClosed (fatDiagonal n) := by apply _root_.YangMills.Construction.ConfigurationSpace.MinSep.isClosed_fatDiagonal <;> assumption
theorem pairDiagonal_codim_four {n : ℕ} (i i' : Fin n) (h : i < i') :
    ∃ W : Submodule ℝ (Config n),
      (W : Set (Config n)) = pairDiagonal i i' ∧ Module.finrank ℝ (Config n ⧸ W) = 4 := by
  let L : Config n →ₗ[ℝ] (Fin 4 → ℝ) :=
    (LinearMap.proj i : Config n →ₗ[ℝ] (Fin 4 → ℝ)) - LinearMap.proj i'
  have hL : ∀ x, L x = x i - x i' := fun _ => rfl
  have hs : Function.Surjective L := by
    intro y
    refine ⟨Pi.single i y, ?_⟩
    rw [hL]
    simp [Pi.single_eq_of_ne h.ne']
  refine ⟨LinearMap.ker L, ?_, ?_⟩
  · ext x
    simp [pairDiagonal, hL, sub_eq_zero]
  · rw [(L.quotKerEquivOfSurjective hs).finrank_eq]
    simp
theorem diagonalsAndMinSeparation {n : ℕ} (hn : 2 ≤ n) : DiagonalsAndMinSeparationFacts n := by
  have hne := orderedPairs_nonempty hn
  refine ⟨pairDiagonal_codim_four, fun x => ?_, fun x x' => ?_, ?_, isClosed_fatDiagonal n⟩
  · obtain ⟨p, -, hp, -⟩ := exists_pair_minSeparation hne x
    rw [hp]
    exact ENNReal.ofReal_ne_top
  · obtain ⟨p, hpm, hp, hmin⟩ := exists_pair_minSeparation hne x
    obtain ⟨p', hpm', hp', hmin'⟩ := exists_pair_minSeparation hne x'
    rw [hp, hp', ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal (norm_nonneg _)]
    have h₁ := norm_sub_apply_le x x' p'.1 p'.2
    have h₂ := norm_sub_apply_le x' x p.1 p.2
    have h₃ := hmin p' hpm'
    have h₄ := hmin' p hpm
    have e : configMaxNorm (x' - x) = configMaxNorm (x - x') := by
      have : ∀ ι, |coords (x' - x) ι| = |coords (x - x') ι| := fun ι => by
        simpa [coords] using abs_sub_comm _ _
      simp only [configMaxNorm, maxNorm, this]
    rw [e] at h₂
    rw [abs_le]
    constructor <;> linarith
  · ext x
    obtain ⟨p, hpm, hp, hmin⟩ := exists_pair_minSeparation hne x
    simp only [Set.mem_ofPred_eq, hp, ENNReal.ofReal_eq_zero]
    constructor
    · intro hx
      simp only [fatDiagonal, Set.mem_iUnion] at hx
      obtain ⟨q, hq, hxq⟩ := hx
      have := hmin q hq
      rw [show x q.1 - x q.2 = 0 from sub_eq_zero.2 hxq, norm_zero] at this
      exact this
    · intro h
      have h0 : ‖x p.1 - x p.2‖ = 0 := le_antisymm h (norm_nonneg _)
      simp only [fatDiagonal, Set.mem_iUnion]
      exact ⟨p, hpm, sub_eq_zero.1 (norm_eq_zero.1 h0)⟩
theorem weightComparison (n : ℕ) : WeightComparison n := by
  intro x
  have ht : 0 ≤ configNorm x := Real.sqrt_nonneg _
  set t := configNorm x
  rw [← Real.sqrt_eq_rpow]
  constructor
  · exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  · rw [← Real.sqrt_mul (by norm_num)]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (t - 1)])
theorem sobolevWeightNorm_mono {n k k' : ℕ} (h : k ≤ k') (φ : Config n → ℂ) :
    sobolevWeightNorm k φ ≤ sobolevWeightNorm k' φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le (hα.trans h) ?_))
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (configNorm x)]) ?_
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  linarith
theorem dualBounded {n : ℕ} (hn : 1 ≤ n)
    (h₁ : SeminormFamiliesComparison)
    (h₂ : schwartzSeminormsFinite) :
    DualBoundedByWeightNorms n := by
  intro S hS
  constructor
  · rintro ⟨-, k, q, b, hb, hB⟩
    refine ⟨max k q, b * (2 : ℝ) ^ ((k : ℝ) / 2), by positivity, fun φ => ?_⟩
    refine (hB φ).trans ?_
    rw [ENNReal.ofReal_mul hb, mul_assoc]
    gcongr
    exact (h₁ n hn).1 k q _ le_rfl φ.1 φ.2.1
  · rintro ⟨k', b, hb, hB⟩
    refine ⟨hS, k', k', b, hb, fun φ => (hB φ).trans ?_⟩
    gcongr
    exact ((h₂ n hn k' k' k').1 φ.1 φ.2.1).2
theorem agreesWithTestSpaces {n : ℕ} (hn : 1 ≤ n)
    (h₄ : YangMills.Construction.Continuum.UnifiedTestSpace.TestSpacesUnified) :
    AgreesWithTestSpaces n := by
  obtain ⟨⟨-, hS₁, hS₂, hS₃⟩, -, -⟩ := h₄ n hn
  refine ⟨?_, fun φ hφ k' hk => ?_, hS₃⟩
  · ext φ
    constructor
    · intro h
      exact (hS₁ φ h.1).1 h
    · intro h
      exact (hS₁ φ h.1).2 h
  · exact (hS₂ ⟨φ, hφ⟩ k' hk).symm ▸ rfl
theorem mem_flatSchwartzSet_of_tendsto {n : ℕ}
    (h₃ : IterDirDerivLinear)
    (ψ : ℕ → Config n → ℂ) (φ : Config n → ℂ) (hψ : ∀ j, ψ j ∈ flatSchwartzSet n)
    (hφ : φ ∈ schwartzSet n)
    (hlim : ∀ k' : ℕ, Filter.Tendsto (fun j => sobolevWeightNorm k' (ψ j - φ)) Filter.atTop (nhds 0)) :
    φ ∈ flatSchwartzSet n := by
  refine ⟨hφ, fun x hx α => ?_⟩
  obtain ⟨-, hadd, hsmul⟩ := h₃ (Config n) (CoordIndex n) coordBasis α
  have hb : ∀ j, ENNReal.ofReal ‖configMultiDeriv α φ x‖ ≤ sobolevWeightNorm α.order (ψ j - φ) := by
    intro j
    have hsm : ψ j ∈ smoothSet (Config n) := (hψ j).1.1
    have hfm : φ ∈ smoothSet (Config n) := hφ.1
    have hneg : (-1 : ℂ) • φ ∈ smoothSet (Config n) :=
      ContDiff.const_smul (-1 : ℂ) (show ContDiff ℝ ∞ φ from hfm)
    have e : configMultiDeriv α (ψ j - φ) x = - configMultiDeriv α φ x := by
      have e₁ : ψ j - φ = ψ j + (-1 : ℂ) • φ := by
        rw [neg_one_smul, sub_eq_add_neg]
      have e₂ := congrFun (hadd _ hsm _ hneg) x
      have e₃ := congrFun (hsmul (-1) _ hfm) x
      have e₄ : configMultiDeriv α (ψ j) x = 0 := (hψ j).2 x hx α
      rw [e₁]
      simp only [configMultiDeriv] at e₄ ⊢
      rw [e₂, Pi.add_apply, e₃, e₄]
      simp
    refine le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le le_rfl ?_))
    rw [e, norm_neg]
    refine ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (norm_nonneg _) ?_)
    exact Real.one_le_rpow (by nlinarith [sq_nonneg (configNorm x)]) (by positivity)
  have h0 : ENNReal.ofReal ‖configMultiDeriv α φ x‖ ≤ 0 := ge_of_tendsto' (hlim α.order) hb
  have : ‖configMultiDeriv α φ x‖ ≤ 0 := by
    simpa using h0
  exact norm_eq_zero.1 (le_antisymm this (norm_nonneg _))
theorem tensorsOffDiagonal {n : ℕ} : TensorsOffDiagonal n := by
  intro f hf
  have hsm : ∀ i, ContDiff ℝ ∞ (f i) := fun i => (hf.2 i).1
  have hcs : ∀ i, IsCompact (tsupport (f i)) := fun i => (hf.2 i).2.1
  have hsub : tsupport (ofRealFun (TestSpaces.tensorProd f)) ⊆
      Set.pi Set.univ fun i => tsupport (f i) := by
    refine closure_minimal (fun x hx => ?_) (isClosed_set_pi fun i _ => isClosed_tsupport _)
    intro i _
    refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [ofRealFun, TestSpaces.tensorProd]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simp
  have hK : IsCompact (Set.pi Set.univ fun i => tsupport (f i)) :=
    isCompact_univ_pi fun i => hcs i
  refine ⟨⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hsub⟩, fun x hx => ?_⟩
  · have hp : ContDiff ℝ ∞ (TestSpaces.tensorProd f) := by
      unfold TestSpaces.tensorProd
      exact contDiff_prod fun i _ => (hsm i).comp (contDiff_apply ℝ _ i)
    exact Complex.ofRealCLM.contDiff.comp hp
  · have hx' := hsub hx
    intro i i' hii
    by_contra hne
    have hd := hf.1.2 hne
    exact Set.disjoint_left.1 hd (hx' i (Set.mem_univ _)) (hii ▸ hx' i' (Set.mem_univ _))
section LipschitzConst
variable {f : (Fin 4 → ℝ) → ℝ}
theorem euclidNormVec_smul (t : ℝ) (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (t • v) = |t| * TorusMetric.euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem partialDerivR4_eq_fderiv (hd : Differentiable ℝ f) (c : Fin 4) (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 c f y = fderiv ℝ f y (Pi.single c 1) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.partialDerivR4_eq_fderiv <;> assumption
theorem fderiv_apply_eq_sum_partial (hd : Differentiable ℝ f) (y v : Fin 4 → ℝ) :
    fderiv ℝ f y v = ∑ c, v c * TestFunctions.partialDerivR4 c f y := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (Pi.single c (v c) : Fin 4 → ℝ) = v c • Pi.single c (1 : ℝ) := by
    ext j
    by_cases h : j = c
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [this, map_smul, partialDerivR4_eq_fderiv hd, smul_eq_mul]
theorem abs_fderiv_apply_le (hd : Differentiable ℝ f) (y v : Fin 4 → ℝ) :
    |fderiv ℝ f y v| ≤ ConfigGradients.gradLen f y * TorusMetric.euclidNormVec v := by
  rw [fderiv_apply_eq_sum_partial hd, mul_comm]
  unfold ConfigGradients.gradLen TorusMetric.euclidNormVec
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
theorem fderiv_apply_grad (hd : Differentiable ℝ f) (y : Fin 4 → ℝ) :
    fderiv ℝ f y (fun c => TestFunctions.partialDerivR4 c f y) =
      ConfigGradients.gradLen f y ^ 2 := by
  rw [fderiv_apply_eq_sum_partial hd]
  unfold ConfigGradients.gradLen TorusMetric.euclidNormVec
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun c _ => by ring
theorem gradSup_ne_top (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ConfigGradients.gradSup f ≠ ⊤ := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  let g : ((Fin 4 → ℝ) →L[ℝ] ℝ) → ℝ := fun L => Real.sqrt (∑ c : Fin 4, L (Pi.single c 1) ^ 2)
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hfun : ConfigGradients.gradLen f = g ∘ fderiv ℝ f := by
    funext y
    simp only [ConfigGradients.gradLen, TorusMetric.euclidNormVec, g, Function.comp,
      partialDerivR4_eq_fderiv hd]
  have hcont : Continuous (ConfigGradients.gradLen f) := by
    rw [hfun]
    exact hg.comp (hf.continuous_fderiv (by simp))
  have hcs : HasCompactSupport (ConfigGradients.gradLen f) := by
    rw [hfun]
    exact hc.fderiv (𝕜 := ℝ) |>.comp_left (by simp [g])
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun y => ?_)
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC y))
theorem lipschitz_bound_of_gradLen_le (hd : Differentiable ℝ f) {G : ℝ}
    (hG : ∀ y, ConfigGradients.gradLen f y ≤ G) (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ G * TestFunctions.euclidDistR4 x y := by
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (y + t • (x - y)))
      (fderiv ℝ f (y + t • (x - y)) (x - y)) t := by
    intro t
    have h₁ : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact (hd _).hasFDerivAt.comp_hasDerivAt t h₁
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => f (y + t • (x - y)))
    (f' := fun t => fderiv ℝ f (y + t • (x - y)) (x - y))
    (C := G * TestFunctions.euclidDistR4 x y)
    (fun t _ => (hder t).hasDerivWithinAt)
    (fun t _ => by
      rw [Real.norm_eq_abs]
      refine (abs_fderiv_apply_le hd _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hG _) (Real.sqrt_nonneg _))
  simpa using this
theorem gradLen_le_of_lipschitz (hd : Differentiable ℝ f) {C : ℝ} (hC : 0 ≤ C)
    (hl : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y) (y : Fin 4 → ℝ) :
    ConfigGradients.gradLen f y ≤ C := by
  set v : Fin 4 → ℝ := fun c => TestFunctions.partialDerivR4 c f y with hv
  set l := ConfigGradients.gradLen f y with hlen
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hvl : TorusMetric.euclidNormVec v = l := rfl
  have h₁ : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h₂ : HasFDerivAt f (fderiv ℝ f y) ((fun t : ℝ => y + t • v) 0) := by
    simpa using (hd y).hasFDerivAt
  have h₃ := h₂.comp_hasDerivAt (0 : ℝ) h₁
  have h₄ := h₃.le_of_lip' (C := C * l) (by positivity) (Filter.Eventually.of_forall fun t => by
    have := hl (y + t • v) y
    have e : TestFunctions.euclidDistR4 (y + t • v) y = |t| * l := by
      rw [TestFunctions.euclidDistR4, add_sub_cancel_left, euclidNormVec_smul, hvl]
    rw [e] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  rw [fderiv_apply_grad hd, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h₄
  rcases hl0.eq_or_lt with h | h
  · rw [← h]; exact hC
  · have : l * l ≤ C * l := by nlinarith
    exact le_of_mul_le_mul_right this h
theorem lipschitzConstEqGradSup (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    LipschitzConstEqGradSup f := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hfin := gradSup_ne_top hf hc
  set G := ConfigGradients.gradSup f with hGdef
  have hG0 : 0 ≤ G.toReal := ENNReal.toReal_nonneg
  have hG : ∀ y, ConfigGradients.gradLen f y ≤ G.toReal := fun y =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iSup (fun y => ENNReal.ofReal
      (ConfigGradients.gradLen f y)) y)
  have hb := lipschitz_bound_of_gradLen_le hd hG
  have hleast : IsLeast {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y}
      G.toReal := by
    refine ⟨⟨hG0, hb⟩, fun C hC => ?_⟩
    have : G ≤ ENNReal.ofReal C := iSup_le fun y =>
      ENNReal.ofReal_le_ofReal (gradLen_le_of_lipschitz hd hC.1 hC.2 y)
    exact ENNReal.toReal_le_of_le_ofReal hC.1 this
  have hlip : TestFunctions.lipConstR4 f = G.toReal := hleast.csInf_eq
  refine ⟨⟨G.toReal, hG0, hb⟩, ?_, fun M => ?_⟩
  · rw [hlip, ENNReal.ofReal_toReal hfin]
  · rw [TestFunctions.sharpNormR4, hlip]
end LipschitzConst
theorem configSpaceTestFunctionFacts
    (h₁ : SeminormFamiliesComparison)
    (h₂ : schwartzSeminormsFinite)
    (h₃ : IterDirDerivLinear)
    (h₄ : YangMills.Construction.Continuum.UnifiedTestSpace.TestSpacesUnified) :
    ConfigSpaceTestFunctionFacts := by
  refine ⟨fun n hn => ⟨diagonalsAndMinSeparation, ?_, weightComparison n,
    fun φ hφ k q k' => ⟨fun hk => (h₁ n hn).1 k q k' hk φ hφ,
      ((h₂ n hn k' k' k').1 φ hφ).2, fun hk => sobolevWeightNorm_mono hk φ⟩,
    dualBounded hn h₁ h₂, agreesWithTestSpaces hn h₄, ?_, tensorsOffDiagonal⟩,
    fun f hf => lipschitzConstEqGradSup hf.1 hf.2.1⟩
  · obtain ⟨⟨⟨-, -, -, -, hΔ⟩, -⟩, -, -⟩ := h₄ n hn
    have e : fatDiagonal n = (distinctConfigs n)ᶜ := hΔ
    rw [e, compl_compl]
  · obtain ⟨-, -, ⟨⟨hs, hl⟩, -⟩, hD⟩ := h₁ n hn
    exact ⟨hs, hl, mem_flatSchwartzSet_of_tendsto h₃, hD⟩
end YangMills.Construction.ConfigurationSpace.Facts
end
