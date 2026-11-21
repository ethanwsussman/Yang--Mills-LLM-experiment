import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsAlongMoves
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothingProof
import YangMills.Construction.ColdStepAtMirrorFrames.CountOfTheBonds
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesOfAChartInCoordinates
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.RunningCouplingSlope.EnergyOverTheCurveHasJets
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields StepSettings RenormalizationStepParameters
namespace RunningCouplingSlope
namespace JetBoundsLemmas
open ColdStepAtMirrorFrames.ChartSlopes (energyNear chartOffset energyNear_add_chartOffset energyNear_analyticAt
  iteratedFDeriv_chartRestriction_single iteratedFDeriv_comp_add_left_zero abs_multilinear_le_of_basis
  weightedNorm_nonneg abs_imaginaryCoord_le norm_chartDirections hasDerivAt_fderiv_along_line
  abs_sub_le_mul_of_hasDerivAt chartCoordinates_add chartCoordinates_zero chartOffset_smul expUnit_zero
  leftTranslate_zero)
section Calculus
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private theorem norm_le_mul_pow_of_abs_basis_le {N j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K) : ‖T‖ ≤ K * (N : ℝ) ^ j := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun ξ => ?_
  have h := abs_multilinear_le_of_basis T K (fun _ => 1) (fun _ => zero_le_one) hK (fun r => by simpa using hT r) ξ
  have hs : ∀ i, Calculus.weightedNorm (fun _ => (1 : ℝ)) (ξ i) ≤ N * ‖ξ i‖ := by
    intro i
    unfold Calculus.weightedNorm
    calc ∑ n, |ξ i n| * 1 ≤ ∑ _n : Fin N, ‖ξ i‖ := Finset.sum_le_sum fun n _ => by
          rw [mul_one]
          exact norm_le_pi_norm (ξ i) n
      _ = N * ‖ξ i‖ := by simp
  have hp : ∏ i, Calculus.weightedNorm (fun _ => (1 : ℝ)) (ξ i) ≤ ∏ i, ((N : ℝ) * ‖ξ i‖) :=
    Finset.prod_le_prod (fun i _ => _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (fun _ => zero_le_one) _) fun i _ => hs i
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  calc ‖T ξ‖ = |T ξ| := rfl
    _ ≤ K * ∏ i, Calculus.weightedNorm (fun _ => (1 : ℝ)) (ξ i) := h
    _ ≤ K * ((N : ℝ) ^ j * ∏ i, ‖ξ i‖) := mul_le_mul_of_nonneg_left hp hK
    _ = K * (N : ℝ) ^ j * ∏ i, ‖ξ i‖ := by ring
private theorem iteratedFDeriv_comp_clm {n : ℕ} {f : E → H} (A : G →L[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.1 hu
  have hcU : ContDiffOn ℝ n f U := hc.mono hUu
  have ht := (hcU.ftaylorSeriesWithin hUo.uniqueDiffOn).comp_continuousAffineMap A.toContinuousAffineMap
  have hopen : IsOpen (A ⁻¹' U) := hUo.preimage A.continuous
  have h1 := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hi) hopen.uniqueDiffOn
    (show x ∈ A ⁻¹' U from hxU)
  have h2 : iteratedFDerivWithin ℝ i (f ∘ A) (A ⁻¹' U) x = iteratedFDeriv ℝ i (f ∘ A) x :=
    iteratedFDerivWithin_of_isOpen i hopen (show x ∈ A ⁻¹' U from hxU)
  have h3 : iteratedFDerivWithin ℝ i f U (A x) = iteratedFDeriv ℝ i f (A x) :=
    iteratedFDerivWithin_of_isOpen i hUo hxU
  rw [← h2, ← h3]
  exact h1.symm
abbrev _root_.YangMills.SharedProofs.p40845 := @iteratedFDeriv_comp_clm
private theorem norm_iteratedFDeriv_comp_clm_le {n : ℕ} {f : E → H} (A : G →L[ℝ] E) {B : ℝ} (hA : ‖A‖ ≤ B)
    {x : G} (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ i f (A x)‖ * B ^ i := by
  rw [iteratedFDeriv_comp_clm A hf hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) hA i
private theorem norm_piSingle_one_le {N : ℕ} (m : Fin N) : ‖(Pi.single m (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.PlainAlignment.norm_single_le_one <;> assumption
end Calculus
section Vacuum
variable {F : BlockFrame}
private theorem pathHolonomy_flatField {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (flatField F j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.FlatTop.pathHolonomy_flatField <;> assumption
private theorem blockFit_flatField {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    blockFit (flatField F j) (flatField F (j + 1)) c = 0 := by
  obtain ⟨r, hr, hm⟩ : ∃ r : ℝ, 0 ≤ r ∧ _root_.YangMills.Construction.BlockAverages.contourAverage (flatField F j) c = (r : ℍ[ℝ]) := by
    refine ⟨(1 / (24 * (F.blockSide : ℝ) ^ 4)) * (((centredCube F.blockSide).card * Nat.factorial 4 : ℕ) : ℝ),
      by positivity, ?_⟩
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    simp only [pathHolonomy_flatField, OneMemClass.coe_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Nat.cast_mul, ← Quaternion.coe_natCast,
      ← Quaternion.coe_mul_eq_smul, ← Quaternion.coe_mul]
  unfold blockFit
  rw [hm]
  simp [flatField, abs_of_nonneg hr]
private abbrev vacuumEnergy (a : ℝ) (F : BlockFrame) : (Fin (chartDimension F) → ℝ) → ℝ :=
  energyNear a (fun _ _ => 0) (flatField F F.top)
private theorem vacuumEnergy_zero (hT : flatTopVanishingStatement) {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide) :
    vacuumEnergy a F 0 = 0 := by
  have e1 : chartedField (fun _ _ => (0 : imaginaryQuaternions)) (flatField F F.top) = flatField F F.depth := by
    funext x i
    unfold chartedField
    split_ifs <;> simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.expUnit_zero, flatField]
  have e2 : vacuumEnergy a F 0 = chartedEnergy a (fun _ _ => 0) (flatField F F.top) := by
    unfold vacuumEnergy energyNear chartRestriction
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [leftTranslate_zero]
  rw [e2]
  unfold chartedEnergy blockEnergy
  rw [e1, (hT F a (finiteCells F) ha hL).2.1 F.depth]
  have e3 : ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit (flatField F F.depth) (flatField F F.top) c = 0 :=
    Finset.sum_eq_zero fun c _ => blockFit_flatField c
  rw [e3]
  simp
private theorem vacuumEnergy_nonneg (hV : minimalChainExistenceStatement) {a : ℝ} (ha : 0 ≤ a)
    (σ : Fin (chartDimension F) → ℝ) : 0 ≤ vacuumEnergy a F σ := by
  obtain ⟨hfit, hleast, -⟩ := hV F a (finiteCells F) ha
  unfold vacuumEnergy energyNear chartRestriction chartedEnergy blockEnergy
  exact add_nonneg (hleast _ _) (mul_nonneg ha (Finset.sum_nonneg fun c _ => hfit _ _ _ c))
private theorem fderiv_vacuumEnergy_zero (hV : minimalChainExistenceStatement) (hT : flatTopVanishingStatement)
    {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide) : fderiv ℝ (vacuumEnergy a F) 0 = 0 := by
  have hmin : IsLocalMin (vacuumEnergy a F) 0 := Filter.Eventually.of_forall fun σ => by
    rw [vacuumEnergy_zero hT ha hL]
    exact vacuumEnergy_nonneg hV ha σ
  exact hmin.fderiv_eq_zero
private theorem norm_stepCoordinates_le (η : StepVariable (finiteCells F)) {r : ℝ}
    (h0 : 0 ≤ r) (hη : ∀ b, ‖η b‖ ≤ r) (x : F.Site F.depth) (i : Fin 4) : ‖stepCoordinates η x i‖ ≤ r := by apply _root_.YangMills.Construction.SecondOrderMoves.norm_stepCoordinates_le <;> assumption
private theorem norm_chartOffset_le (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x i, ‖dw x i‖ ≤ r) : ‖chartOffset (F := F) dw‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun n => ?_
  simp only [chartOffset, chartCoordinates]
  rcases (chartCoordinateEquiv F).symm n with p | p
  · exact (abs_imaginaryCoord_le _ _).trans (h _ _)
  · simpa [coordinateOfIndex] using hr
private theorem toImaginary_add_smul (u v : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) :
    toImaginary (u + θ • v) = toImaginary u + θ • toImaginary v := by apply _root_.YangMills.SharedProofs.p23127 <;> assumption
private theorem stepCoordinates_add_smul (ζ ζ' : StepVariable (finiteCells F)) (θ : ℝ) :
    stepCoordinates (ζ + θ • ζ') = fun x i => stepCoordinates ζ x i + θ • stepCoordinates ζ' x i := by
  funext x i
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_add_smul _ _ _
  · simp
private theorem stepCoordinates_zero :
    stepCoordinates (0 : StepVariable (finiteCells F)) = fun _ _ => 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.stepCoordinates_zero <;> assumption
private theorem stepCoordinates_smul (ζ : StepVariable (finiteCells F)) (θ : ℝ) :
    stepCoordinates (θ • ζ) = fun x i => θ • stepCoordinates ζ x i := by
  have h := stepCoordinates_add_smul (0 : StepVariable (finiteCells F)) ζ θ
  rw [zero_add, stepCoordinates_zero] at h
  simpa using h
private theorem shiftChart_zero (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    ColdStepAtMirrorFrames.ChartSlopes.shiftChart (fun _ _ => 0) dw = dw := by
  funext x i
  simp [ColdStepAtMirrorFrames.ChartSlopes.shiftChart]
private theorem vacuumEnergy_jets (hCE : ChartedEnergyInCoordinates) (hV : minimalChainExistenceStatement)
    (hT : flatTopVanishingStatement) {a r δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Ck : ℕ → ℝ) (hCk : ∀ k, 0 < Ck k)
    (hker : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ r) → ∀ (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (chartRestriction a (stepCoordinates ζ) (flatField F F.top) q) 0 ∧
      (2 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
        |chartMixedDeriv a (stepCoordinates ζ) (flatField F F.top) q| ≤
          Ck k * Real.exp (-(δ * directionDiameter q))))
    (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ r) :
    AnalyticAt ℝ (vacuumEnergy a F) (chartOffset (stepCoordinates ζ)) ∧
    ∀ j, 1 ≤ j → j ≤ 5 → ‖iteratedFDeriv ℝ j (vacuumEnergy a F) (chartOffset (stepCoordinates ζ))‖ ≤
      (Ck 2 + Ck 3 + Ck 4 + Ck 5) * ((chartDimension F : ℝ) + 1) ^ 5 := by
  have hAn : ∀ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ' b‖ ≤ r) →
      AnalyticAt ℝ (vacuumEnergy a F) (chartOffset (stepCoordinates ζ')) := fun ζ' h =>
    energyNear_analyticAt hCE hL hs a _ _ _ (by rw [shiftChart_zero]; exact (hker ζ' h _ _).1)
  have hEntry : ∀ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ' b‖ ≤ r) → ∀ j, 2 ≤ j →
      ∀ r' : Fin j → Fin (chartDimension F),
        |iteratedFDeriv ℝ j (vacuumEnergy a F) (chartOffset (stepCoordinates ζ')) fun i => Pi.single (r' i) 1| ≤
          Ck j := by
    intro ζ' h j hj r'
    have hshift : (fun z => vacuumEnergy a F (chartOffset (stepCoordinates ζ') + z)) =
        energyNear a (stepCoordinates ζ') (flatField F F.top) := by
      funext z
      have e := energyNear_add_chartOffset hCE hL hs a (fun _ _ => 0) (stepCoordinates ζ') (flatField F F.top) z
      rw [shiftChart_zero] at e
      exact e
    rw [← iteratedFDeriv_comp_add_left_zero, hshift]
    unfold energyNear
    rw [iteratedFDeriv_chartRestriction_single _ _ _ _ _ (hker ζ' h _ _).1]
    have hb := (hker ζ' h j (chartDirections F ∘ r')).2 hj fun l => norm_chartDirections _
    refine hb.trans ?_
    have he : Real.exp (-(δ * directionDiameter (chartDirections F ∘ r'))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ * (directionDiameter (chartDirections F ∘ r') : ℝ) := by positivity
      linarith
    have := hCk j
    nlinarith
  have hNorm : ∀ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ' b‖ ≤ r) → ∀ j, 2 ≤ j →
      ‖iteratedFDeriv ℝ j (vacuumEnergy a F) (chartOffset (stepCoordinates ζ'))‖ ≤
        Ck j * (chartDimension F : ℝ) ^ j :=
    fun ζ' h j hj => norm_le_mul_pow_of_abs_basis_le _ (hCk j).le (hEntry ζ' h j hj)
  set p := chartOffset (F := F) (stepCoordinates ζ) with hp
  have hp1 : ‖p‖ ≤ 1 := (norm_chartOffset_le _ hr0 (norm_stepCoordinates_le ζ hr0 hζ)).trans hr1
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ' b‖ ≤ r) ∧
      (0 : Fin (chartDimension F) → ℝ) + s • p = chartOffset (stepCoordinates ζ') := by
    intro s hs'
    refine ⟨s • ζ, fun b => ?_, ?_⟩
    · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs'.1]
      have := hζ b
      nlinarith [hs'.1, hs'.2]
    · rw [zero_add, stepCoordinates_smul, chartOffset_smul]
  have hFirst : ∀ m : Fin (chartDimension F),
      |fderiv ℝ (vacuumEnergy a F) p (Pi.single m 1)| ≤ Ck 2 * (chartDimension F : ℝ) ^ 2 := by
    intro m
    set e : Fin (chartDimension F) → ℝ := Pi.single m 1 with he
    have h := abs_sub_le_mul_of_hasDerivAt
      (f := fun s : ℝ => fderiv ℝ (vacuumEnergy a F) ((0 : Fin (chartDimension F) → ℝ) + s • p) e)
      (f' := fun s => iteratedFDeriv ℝ 2 (vacuumEnergy a F) ((0 : Fin (chartDimension F) → ℝ) + s • p) ![p, e])
      (M := Ck 2 * (chartDimension F : ℝ) ^ 2) (τ := 1) zero_le_one
      (fun t ht => by
        obtain ⟨ζ', h1, h2⟩ := hseg t ht
        refine hasDerivAt_fderiv_along_line ?_
        rw [h2]
        exact hAn ζ' h1)
      (fun t ht => by
        obtain ⟨ζ', h1, h2⟩ := hseg t ht
        rw [h2]
        have h3 := hNorm ζ' h1 2 le_rfl
        have h4 := ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ 2 (vacuumEnergy a F) (chartOffset (stepCoordinates ζ'))) ![p, e]
        rw [Fin.prod_univ_two] at h4
        have h5 : ‖(![p, e] : Fin 2 → Fin (chartDimension F) → ℝ) 0‖ *
            ‖(![p, e] : Fin 2 → Fin (chartDimension F) → ℝ) 1‖ ≤ 1 := by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact mul_le_one₀ hp1 (norm_nonneg _) (norm_piSingle_one_le m)
        have h6 : 0 ≤ ‖iteratedFDeriv ℝ 2 (vacuumEnergy a F) (chartOffset (stepCoordinates ζ'))‖ := norm_nonneg _
        calc |iteratedFDeriv ℝ 2 (vacuumEnergy a F) (chartOffset (stepCoordinates ζ')) ![p, e]| ≤ _ := h4
          _ ≤ ‖iteratedFDeriv ℝ 2 (vacuumEnergy a F) (chartOffset (stepCoordinates ζ'))‖ * 1 :=
            mul_le_mul_of_nonneg_left h5 h6
          _ ≤ _ := by simpa using h3)
    have e0 : fderiv ℝ (vacuumEnergy a F) ((0 : Fin (chartDimension F) → ℝ) + (0 : ℝ) • p) e = 0 := by
      simp only [zero_smul, add_zero]
      rw [fderiv_vacuumEnergy_zero hV hT ha hL]
      rfl
    have e1 : (0 : Fin (chartDimension F) → ℝ) + (1 : ℝ) • p = p := by simp
    simp only [e0, e1, sub_zero, mul_one] at h
    exact h
  refine ⟨hAn ζ hζ, fun j hj1 hj5 => ?_⟩
  have h2 := hCk 2
  have h3 := hCk 3
  have h4 := hCk 4
  have h5 := hCk 5
  have hD0 : (0 : ℝ) ≤ chartDimension F := by positivity
  have hpow : ∀ i, i ≤ 5 → (chartDimension F : ℝ) ^ i ≤ ((chartDimension F : ℝ) + 1) ^ 5 := fun i hi =>
    (pow_le_pow_left₀ hD0 (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi)
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega
    have hb := norm_le_mul_pow_of_abs_basis_le (iteratedFDeriv ℝ 1 (vacuumEnergy a F) p)
      (K := Ck 2 * (chartDimension F : ℝ) ^ 2) (by positivity) (fun r' => by
        rw [iteratedFDeriv_one_apply]
        exact hFirst _)
    refine hb.trans ?_
    have e : Ck 2 * (chartDimension F : ℝ) ^ 2 * (chartDimension F : ℝ) ^ 1 =
        Ck 2 * (chartDimension F : ℝ) ^ 3 := by ring
    rw [e]
    exact mul_le_mul (by linarith) (hpow 3 (by norm_num)) (by positivity) (by positivity)
  · refine (hNorm ζ hζ j hj).trans ?_
    have hCj : Ck j ≤ Ck 2 + Ck 3 + Ck 4 + Ck 5 := by
      interval_cases j <;> linarith
    exact mul_le_mul hCj (hpow j hj5) (by positivity) (by positivity)
end Vacuum
section Curve
variable {k n : ℕ}
private def topPerturbation (F : BlockFrame) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) : F.Site F.top → Fin 4 → imaginaryQuaternions :=
  fun y i => ∑ l, if c l = ((fun m => ((siteCoords y m : ℤ) : ZMod n)), i) then τ l • X l else 0
private theorem perturbedTop_eq (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    perturbedTop R n c X τ = ColdStepAtMirrorFrames.leftTranslate
      (topPerturbation (torusFrame R.params.side R.depth n) c X τ)
      (flatField (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top) := rfl
private theorem topPerturbation_add_smul (F : BlockFrame) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (τ τ' : Fin k → ℝ) (θ : ℝ) (y : F.Site F.top) (i : Fin 4) :
    topPerturbation F c X (τ + θ • τ') y i = topPerturbation F c X τ y i + θ • topPerturbation F c X τ' y i := by
  unfold topPerturbation
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp [add_smul, mul_smul]
  · simp
private theorem topPerturbation_zero (F : BlockFrame) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) : topPerturbation F c X 0 = fun _ _ => 0 := by
  funext y i
  simp [topPerturbation]
private def curveCoordinates (F : BlockFrame) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (q : StepVariable (finiteCells F) × (Fin k → ℝ)) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (stepCoordinates q.1) (topPerturbation F c X q.2)
private theorem curveCoordinates_add_smul (F : BlockFrame) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (q q' : StepVariable (finiteCells F) × (Fin k → ℝ)) (θ : ℝ) :
    curveCoordinates F c X (q + θ • q') = curveCoordinates F c X q + θ • curveCoordinates F c X q' := by
  unfold curveCoordinates
  rw [← chartCoordinates_add]
  show chartCoordinates (stepCoordinates (q.1 + θ • q'.1)) (topPerturbation F c X (q.2 + θ • q'.2)) = _
  rw [stepCoordinates_add_smul]
  congr 1
  funext y i
  exact topPerturbation_add_smul F c X _ _ _ y i
private theorem curveCoordinates_zero (F : BlockFrame) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) : curveCoordinates F c X 0 = 0 := by
  unfold curveCoordinates
  show chartCoordinates (stepCoordinates (0 : StepVariable (finiteCells F))) (topPerturbation F c X 0) = 0
  rw [stepCoordinates_zero, topPerturbation_zero, chartCoordinates_zero]
private def curveLinearMap (F : BlockFrame) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (StepVariable (finiteCells F) × (Fin k → ℝ)) →ₗ[ℝ] (Fin (chartDimension F) → ℝ) where
  toFun := curveCoordinates F c X
  map_add' q q' := by simpa using curveCoordinates_add_smul F c X q q' 1
  map_smul' θ q := by
    have h := curveCoordinates_add_smul F c X 0 q θ
    rw [curveCoordinates_zero, zero_add, zero_add] at h
    exact h
private theorem norm_topPerturbation_le (F : BlockFrame) (c : Fin k → TorusBond n)
    {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X) (τ : Fin k → ℝ) (y : F.Site F.top) (i : Fin 4) :
    ‖topPerturbation F c X τ y i‖ ≤ k * ‖τ‖ := by
  unfold topPerturbation
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l, ‖(if c l = ((fun m => ((siteCoords y m : ℤ) : ZMod n)), i) then τ l • X l else 0 :
        imaginaryQuaternions)‖
      ≤ ∑ _l : Fin k, ‖τ‖ := Finset.sum_le_sum fun l _ => by
        split_ifs
        · rw [norm_smul, hX l, mul_one]
          exact norm_le_pi_norm τ l
        · simp
    _ = k * ‖τ‖ := by simp
private theorem norm_curveCoordinates_le (F : BlockFrame) (c : Fin k → TorusBond n)
    {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X)
    (q : StepVariable (finiteCells F) × (Fin k → ℝ)) : ‖curveCoordinates F c X q‖ ≤ ((k : ℝ) + 1) * ‖q‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
  have h1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have h2 : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
  have hq := norm_nonneg q
  simp only [curveCoordinates, chartCoordinates]
  rcases (chartCoordinateEquiv F).symm m with p | p
  · refine (abs_imaginaryCoord_le _ _).trans ?_
    refine (norm_stepCoordinates_le q.1 (norm_nonneg _) (fun b => norm_le_pi_norm q.1 b) _ _).trans ?_
    nlinarith
  · refine (abs_imaginaryCoord_le _ _).trans ?_
    refine (norm_topPerturbation_le F c hX q.2 _ _).trans ?_
    nlinarith
private def curveCLM (F : BlockFrame) (c : Fin k → TorusBond n) {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) : (StepVariable (finiteCells F) × (Fin k → ℝ)) →L[ℝ] (Fin (chartDimension F) → ℝ) :=
  (curveLinearMap F c X).mkContinuous ((k : ℝ) + 1) (norm_curveCoordinates_le F c hX)
private theorem norm_curveCLM_le (F : BlockFrame) (c : Fin k → TorusBond n) {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) : ‖curveCLM F c hX‖ ≤ (k : ℝ) + 1 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _
private theorem curveCLM_zero_right (F : BlockFrame) (c : Fin k → TorusBond n)
    {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X) (ζ : StepVariable (finiteCells F)) :
    curveCLM F c hX (ζ, 0) = chartOffset (stepCoordinates ζ) := by
  show chartCoordinates (stepCoordinates ζ) (topPerturbation F c X 0) = _
  rw [topPerturbation_zero]
  rfl
private theorem chartedEnergyAlong_eq_comp (hCE : ChartedEnergyInCoordinates) (R : StepSetup) (n : ℕ)
    (c : Fin k → TorusBond n) {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X)
    (hL : Odd (torusFrame R.params.side R.depth n).blockSide)
    (hs : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i) :
    chartedEnergyAlong R n c X = vacuumEnergy R.params.coupling (torusFrame R.params.side R.depth n) ∘
      curveCLM (torusFrame R.params.side R.depth n) c hX := by
  funext q
  have e := (hCE (torusFrame R.params.side R.depth n) R.params.coupling (fun _ _ => 0) (stepCoordinates q.1)
    (flatField (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top)
    (topPerturbation (torusFrame R.params.side R.depth n) c X q.2) hL hs).1
  simp only [zero_add] at e
  unfold chartedEnergyAlong
  rw [perturbedTop_eq, ← e]
  rfl
private theorem card_finiteCells_torusFrame (L t n : ℕ) [NeZero n] :
    (finiteCells (torusFrame L t n)).card = n ^ 4 := by
  classical
  have hper : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := fun i => by
    simp [BlockFrame.period, torusFrame]
  have : ∀ i, NeZero ((torusFrame L t n).period (torusFrame L t n).top i) := fun i => ⟨by
    rw [hper]
    exact NeZero.ne n⟩
  have hfin : Finite (torusFrame L t n).Cell := by
    unfold BlockFrame.Cell BlockFrame.Site
    infer_instance
  have e : finiteCells (torusFrame L t n) = @Finset.univ _ (@Fintype.ofFinite _ hfin) := dif_pos hfin
  rw [e]
  let _ : Fintype (torusFrame L t n).Cell := @Fintype.ofFinite _ hfin
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  unfold BlockFrame.Cell BlockFrame.Site
  rw [Nat.card_pi]
  simp [hper]
abbrev _root_.YangMills.SharedProofs.p57413 := @card_finiteCells_torusFrame
private theorem chartDimension_eq (F : BlockFrame) :
    chartDimension F = 3 * (chordBonds (finiteCells F)).card + 3 * (innerBonds (finiteCells F) F.top).card := by
  unfold chartDimension ColdStepAtMirrorFrames.ChartCoordinateIndex
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_fin]
  ring
end Curve
section Parameters
private theorem isAdmissibleChartPoint_of_ball (hCov : BlocksCoverLowerLevel) (hFT : flatTopVanishingStatement)
    (T : ParameterAssignment) (hT : T.Admissible) {F : BlockFrame} (hFL : F.blockSide = T.side)
    (hs : ∀ i, 2 ≤ F.extent i) {σ₀ : ℝ} (hσ₀ : σ₀ = T.σA)
    (ζ : StepVariable (finiteCells F)) (hζ : ∀ b, ‖ζ b‖ ≤ T.ballRadius) :
    IsAdmissibleChartPoint T.side σ₀ (stepCoordinates ζ) (flatField F F.top) := by
  have hσ0 := hT.σ_pos
  have hσ1 := hT.σ_one
  have hρ0 : 0 ≤ T.ballRadius := by
    unfold ParameterAssignment.ballRadius
    positivity
  have hodd : Odd F.blockSide := hFL ▸ hT.L_odd
  have hcoord := norm_stepCoordinates_le ζ hρ0 hζ
  have hL1 : (1 : ℝ) ≤ T.side := by exact_mod_cast hT.L_odd.pos
  have hN0 : 0 ≤ T.N 0 := by
    obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := hT.chain
    exact (hN 0).le
  have hLσ : (T.side : ℝ) * T.threshold ≤ 2⁻¹ ^ 10 := by
    have h := hT.σ_L
    have h1 : 0 ≤ (T.side : ℝ) * T.threshold := by positivity
    have h2 : 0 ≤ (T.side : ℝ) * T.threshold * T.N 0 := by positivity
    norm_num at h ⊢
    nlinarith
  refine ⟨fun b _ => (hcoord b.1 b.2).trans ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    unfold ParameterAssignment.ballRadius
    norm_num at hLσ ⊢
    nlinarith
  · intro p hp
    have hall := hCov F hodd fun i => by
      have := hs i
      omega
    have hmem : p ∈ innerPlaquettes (finiteCells F) F.depth := by
      simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨hall _, hp, fun y _ => hall y⟩
    have hcold := (hFT F T.coupling (finiteCells F) (by have := hT.a_ge; linarith) hodd).1 F.top T.threshold hσ0
    have he : T.ballRadius ≤ 1 / 4 := by
      unfold ParameterAssignment.ballRadius
      linarith
    have hcur := GaugeFixing.plaquetteDefect_chartedField_le hs hodd (finiteCells F) (flatField F F.top)
      T.threshold T.ballRadius hσ0.le hcold (stepCoordinates ζ) he (fun d _ => hcoord d.1 d.2) p hmem
    have h2 := hT.σ_le
    have h3 : T.threshold + 8 * T.ballRadius < σ₀ := by
      rw [hσ₀]
      unfold ParameterAssignment.ballRadius
      linarith
    linarith
end Parameters
end JetBoundsLemmas
open JetBoundsLemmas in
open ColdStepAtMirrorFrames.ChartSlopes (chartOffset) in
theorem chartedEnergyJetBounds_of_kernels (hK : ChartEnergyKernelBound)
    (hCE : ChartedEnergyInCoordinates) (hCl : AdmissibleParametersExist)
    (hN : BondCount) (hCov : BlocksCoverLowerLevel)
    (hV : minimalChainExistenceStatement) (hFT : flatTopVanishingStatement) :
    ChartedEnergyJetBounds := by
  intro T hT k
  obtain ⟨cn, -, -, -, -, hσ, -, -, hcn⟩ :=
    hCl T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hT.a_ge hT.L_odd hT.chain
  obtain ⟨Ck, hCk, hker⟩ := hK T.coupling T.side cn hT.a_ge hT.L_odd hT.L_ge hcn
  obtain ⟨nb, hnb⟩ := hN T.side hT.L_odd
  have hM0 : 0 < Ck 2 + Ck 3 + Ck 4 + Ck 5 := by
    have h2 := hCk 2
    have h3 := hCk 3
    have h4 := hCk 4
    have h5 := hCk 5
    linarith
  refine ⟨(Ck 2 + Ck 3 + Ck 4 + Ck 5) * (((3 * nb + 13 : ℕ) : ℝ) * ((k : ℝ) + 1)) ^ 5, 20, by positivity,
    by norm_num, ?_⟩
  intro y R hy hR n _ c X hn hX η hη
  have hn4096 : 4096 ≤ n := hT.n₀_ge.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have haE : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hFL : (torusFrame R.params.side R.depth n).blockSide = T.side := hLe
  have hodd : Odd (torusFrame R.params.side R.depth n).blockSide := hFL ▸ hT.L_odd
  have hside : ∀ i, (torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  have hs : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun i => by
    rw [hside]
    omega
  have hF : IsBlockTorus T.side (torusFrame R.params.side R.depth n) := ⟨hFL, n, by omega, hside⟩
  have ha0 : 0 ≤ R.params.coupling := by
    rw [haE]
    have := hT.a_ge
    linarith
  have hσ0 := hT.σ_pos
  have hσ1 := hT.σ_one
  have hr0 : 0 ≤ T.ballRadius := by
    unfold ParameterAssignment.ballRadius
    positivity
  have hr1 : T.ballRadius ≤ 1 := by
    unfold ParameterAssignment.ballRadius
    linarith
  have hjets := vacuumEnergy_jets (F := torusFrame R.params.side R.depth n) hCE hV hFT (a := R.params.coupling)
    (r := T.ballRadius) (δ := cn.δ₁) ha0 hcn.positivity.1.le hr0 hr1 hodd hs Ck hCk (fun ζ hζ k' q => by
      rw [haE]
      exact hker _ _ _ hF (isAdmissibleChartPoint_of_ball hCov hFT T hT hFL hs hσ ζ hζ) k' q) η hη
  obtain ⟨hAn, hbound⟩ := hjets
  have hcomp := chartedEnergyAlong_eq_comp hCE R n c hX hodd hs
  have hat : curveCLM (torusFrame R.params.side R.depth n) c hX (η, 0) = chartOffset (stepCoordinates η) :=
    curveCLM_zero_right _ c hX η
  have hc5 : ContDiffAt ℝ ((5 : ℕ) : WithTop ℕ∞) (vacuumEnergy R.params.coupling (torusFrame R.params.side R.depth n))
      (curveCLM (torusFrame R.params.side R.depth n) c hX (η, 0)) := by
    rw [hat]
    exact hAn.contDiffAt
  refine ⟨?_, fun j hj1 hj5 => ?_⟩
  · rw [hcomp]
    exact ContDiffAt.comp (η, 0) hc5 (curveCLM (torusFrame R.params.side R.depth n) c hX).contDiff.contDiffAt
  rw [hcomp]
  refine (norm_iteratedFDeriv_comp_clm_le _ (norm_curveCLM_le _ c hX) hc5 hj5).trans ?_
  rw [hat]
  obtain ⟨hcb, hcc⟩ := hnb (torusFrame R.params.side R.depth n) n hFL (by omega) hside
  have hD : ((chartDimension (torusFrame R.params.side R.depth n) : ℝ) + 1) ≤
      ((3 * nb + 13 : ℕ) : ℝ) * (n : ℝ) ^ 4 := by
    rw [chartDimension_eq, hcb, hcc, card_finiteCells_torusFrame]
    push_cast
    have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
    nlinarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  have h1 := hbound j hj1 hj5
  have h2 : ((k : ℝ) + 1) ^ j ≤ ((k : ℝ) + 1) ^ 5 := pow_le_pow_right₀ hk1 hj5
  have h3 : ((chartDimension (torusFrame R.params.side R.depth n) : ℝ) + 1) ^ 5 ≤
      (((3 * nb + 13 : ℕ) : ℝ) * (n : ℝ) ^ 4) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hD 5
  have e20 : (n : ℝ) ^ (20 : ℝ) = ((n : ℝ) ^ 4) ^ 5 := by
    rw [← pow_mul, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e20]
  calc ‖iteratedFDeriv ℝ j (vacuumEnergy R.params.coupling (torusFrame R.params.side R.depth n))
        (chartOffset (stepCoordinates η))‖ * ((k : ℝ) + 1) ^ j
      ≤ ((Ck 2 + Ck 3 + Ck 4 + Ck 5) * ((chartDimension (torusFrame R.params.side R.depth n) : ℝ) + 1) ^ 5) *
          ((k : ℝ) + 1) ^ 5 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ ((Ck 2 + Ck 3 + Ck 4 + Ck 5) * (((3 * nb + 13 : ℕ) : ℝ) * (n : ℝ) ^ 4) ^ 5) * ((k : ℝ) + 1) ^ 5 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hM0.le) (by positivity)
    _ = _ := by ring
end RunningCouplingSlope
end YangMills.Construction
end
