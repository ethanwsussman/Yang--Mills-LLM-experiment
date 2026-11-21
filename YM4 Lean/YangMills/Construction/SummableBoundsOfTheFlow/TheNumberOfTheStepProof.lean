import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.HoleBesideASecondHole.EachHoleIsFilledProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensitiesProof
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessHasItsSecondOrder
import YangMills.Construction.SummableBoundsOfTheFlow.TheLimitsOfTheDensitiesAreSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheNumberOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.ReferenceDensity YangMills.Construction.ScaledVariables YangMills.Construction.FamilyNorms YangMills.Construction.RenormalizationStepParameters
namespace YangMills.Construction.StepDensities
variable {F : BlockFrame}
private theorem iteratedFDeriv_comp_clm_zero {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : E →L[ℝ] E) (hf : ContDiffAt ℝ k f (D 0)) :
    iteratedFDeriv ℝ k (f ∘ D) 0 =
      (iteratedFDeriv ℝ k f (D 0)).compContinuousLinearMap fun _ => D := by apply _root_.YangMills.SharedProofs.p19667 <;> assumption
private theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s τ : Fin k → ℝ) :
    bondSpread c (fun l => s l • X l) τ = bondSpread c X (fun l => s l * τ l) := by apply _root_.YangMills.SharedProofs.p12456 <;> assumption
private theorem bondDeriv_smul {k : ℕ} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (s : Fin k → ℝ)
    (hs : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv G V c (fun l => s l • X l) = (∏ l, s l) * bondDeriv G V c X := by
  let D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => s l • ContinuousLinearMap.proj l
  have hD : ∀ τ l, D τ l = s l * τ l := fun τ l => by simp [D]
  have hD0 : D 0 = 0 := map_zero D
  have hf : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c (fun l => s l • X l) τ) V)) =
      (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) ∘ D := by
    funext τ
    simp only [Function.comp]
    rw [bondSpread_smul]
    congr 3
  have hs' : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) (D 0) := by
    rwa [hD0]
  unfold bondDeriv
  rw [hf, iteratedFDeriv_comp_clm_zero _ D hs', hD0]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun l => (fun _ : Fin k => (D : (Fin k → ℝ) → (Fin k → ℝ))) l (Pi.single l 1 : Fin k → ℝ)) =
      fun l => s l • (Pi.single l 1 : Fin k → ℝ) := by
    funext l
    funext j
    simp only []
    rw [hD]
    by_cases h : j = l
    · subst h
      simp
    · simp [h]
  erw [hv, ContinuousMultilinearMap.map_smul_univ]
  simp
private theorem bondDeriv_pair_smul (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (X X' : imaginaryQuaternions) (a a' : ℝ)
    (hs : ContDiffAt ℝ (2 : ℕ) (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c ![X, X'] τ) V)) 0) :
    bondDeriv G V c ![a • X, a' • X'] = a * a' * bondDeriv G V c ![X, X'] := by
  have h := bondDeriv_smul G V c ![X, X'] ![a, a'] hs
  have e : (fun l => (![a, a'] : Fin 2 → ℝ) l • (![X, X'] : Fin 2 → imaginaryQuaternions) l) =
      ![a • X, a' • X'] := by
    funext l
    fin_cases l <;> rfl
  rw [e] at h
  rw [h, Fin.prod_univ_two]
  rfl
private theorem bondDeriv_add {k : ℕ} (G G' : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hs : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0)
    (hs' : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G' (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (fun V' => G V' + G' V') V c X = bondDeriv G V c X + bondDeriv G' V c X := by
  unfold bondDeriv
  have h2 : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V) +
      G' (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) +
        fun τ : Fin k → ℝ => G' (leftTranslate (bondSpread c X τ) V) := rfl
  rw [h2, iteratedFDeriv_add_apply hs hs']
  rfl
private theorem bondDeriv_sub_const (G : F.GaugeField F.top → ℝ) (d : ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (hk : k ≠ 0) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (fun V' => G V' - d) V c X = bondDeriv G V c X := by apply _root_.YangMills.SharedProofs.p7768 <;> assumption
private theorem uniform_isSmallCurvature (s : ℝ) (hs : 0 < s) {j : ℕ} :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p20907 <;> assumption
private theorem mem_finiteCells (hF : ∀ i, F.extent i ≠ 0) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p16107 <;> assumption
private theorem exists_unit_smul (X : imaginaryQuaternions) :
    ∃ (a : ℝ) (X₀ : imaginaryQuaternions), ‖X₀‖ = 1 ∧ X = a • X₀ ∧ |a| = ‖X‖ := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.exists_smul_unit <;> assumption
private theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (h : ‖X‖ = 1) (h' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
private theorem sup_fin_two (f : Fin 2 → ℕ) : Finset.univ.sup f = max (f 0) (f 1) := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.sup_univ_fin_two <;> assumption
private theorem offsetNorm_neg (h : Fin 4 → ℤ) : offsetNorm (-h) = offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private theorem offsetNorm_sub_le (h h' : Fin 4 → ℤ) : offsetNorm (h - h') ≤ offsetNorm h + offsetNorm h' := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.offsetNorm_sub_le <;> assumption
private theorem siteSupDist_siteOfCoords {j : ℕ} (h h' : Fin 4 → ℤ)
    (hn : ∀ i, 2 * offsetNorm (h - h') < F.period j i) :
    siteSupDist (siteOfCoords j h : F.Site j) (siteOfCoords j h') = offsetNorm (h - h') := by
  unfold siteSupDist offsetNorm
  refine Finset.sup_congr rfl fun i _ => ?_
  have hi : ((h - h') i).natAbs ≤ offsetNorm (h - h') :=
    Finset.le_sup (f := fun i => ((h - h') i).natAbs) (Finset.mem_univ i)
  have hp := hn i
  have : NeZero (F.period j i) := ⟨by omega⟩
  have e : ((siteOfCoords j h : F.Site j) i - (siteOfCoords j h' : F.Site j) i) =
      (((h - h') i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  rw [e]
  have hv : ((((h - h') i : ℤ) : ZMod (F.period j i))).valMinAbs = (h - h') i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  rw [hv]
private theorem siteSupDist_comm {j : ℕ} (y z : F.Site j) : siteSupDist y z = siteSupDist z y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.siteSupDist_comm <;> assumption
private theorem siteSupDist_self {j : ℕ} (y : F.Site j) : siteSupDist y y = 0 := by apply _root_.YangMills.Construction.HoleFilling.supDist_self <;> assumption
private theorem bondSpan_lattice (L t n : ℕ) (b b' : LatticeBond)
    (hn : 2 * (offsetNorm b.1 + offsetNorm b'.1) + 2 < n) :
    bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) = bondPairDiam b b' := by
  have hper : ∀ i, (cubicTorusFrame L t n).period (cubicTorusFrame L t n).top i = n := by
    intro i
    simp [BlockFrame.period, cubicTorusFrame]
  have z : (0 : (cubicTorusFrame L t n).Cell) = siteOfCoords (cubicTorusFrame L t n).top 0 := by
    funext i
    simp [siteOfCoords]
  have d := offsetNorm_sub_le b.1 b'.1
  have e1 : siteSupDist (0 : (cubicTorusFrame L t n).Cell)
      (0 + siteOfCoords (cubicTorusFrame L t n).top b.1) = offsetNorm b.1 := by
    rw [zero_add, z, siteSupDist_siteOfCoords _ _ (fun i => by rw [hper i]; simp [offsetNorm_neg]; omega)]
    simp [offsetNorm_neg]
  have e2 : siteSupDist (0 : (cubicTorusFrame L t n).Cell)
      (0 + siteOfCoords (cubicTorusFrame L t n).top b'.1) = offsetNorm b'.1 := by
    rw [zero_add, z, siteSupDist_siteOfCoords _ _ (fun i => by rw [hper i]; simp [offsetNorm_neg]; omega)]
    simp [offsetNorm_neg]
  have e3 : siteSupDist ((0 : (cubicTorusFrame L t n).Cell) + siteOfCoords (cubicTorusFrame L t n).top b.1)
      (0 + siteOfCoords (cubicTorusFrame L t n).top b'.1) = offsetNorm (b.1 - b'.1) := by
    rw [zero_add, zero_add, siteSupDist_siteOfCoords _ _ (fun i => by rw [hper i]; omega)]
  have e4 : siteSupDist ((0 : (cubicTorusFrame L t n).Cell) + siteOfCoords (cubicTorusFrame L t n).top b'.1)
      (0 + siteOfCoords (cubicTorusFrame L t n).top b.1) = offsetNorm (b.1 - b'.1) := by
    rw [siteSupDist_comm, e3]
  unfold bondSpan bondPairDiam
  simp only [sup_fin_two, bondsAt, Matrix.cons_val_zero, Matrix.cons_val_one, siteSupDist_self, e1, e2, e3, e4]
  omega
private theorem bondWithinRadius_of_offsetNorm (c : LatticeBond) {m : ℕ} (hm : offsetNorm c.1 + 1 ≤ m) :
    BondWithinRadius m c := by apply _root_.YangMills.DeltaSharedProofs.p501634 <;> assumption
private theorem tendsto_secondDerivLimit {h : LocalDensity} (hL : HasLimitSecondDeriv h) (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    Filter.Tendsto (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (secondDerivLimit h c c' X X')) := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.tendsto_secondDerivLimit <;> assumption
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem curvaturePairing_unitPlane :
    curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
private structure SecondDerivAtUniform (L t n₀ : ℕ) (g : TopLevelFamily) : Prop where
  smooth : ∀ n, n₀ ≤ n → ContDiffThreeAlongBonds (g (cubicTorusFrame L t n) 0) (uniformField _ _)
  read : ∀ (n : ℕ) (b b' : LatticeBond) (X X' : imaginaryQuaternions), n₀ ≤ n →
    mixedDeriv (densityOfTopFamily L t g n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] =
      secondDerivAtUniform g L t n b b' X X'
private theorem SecondDerivAtUniform.smul {L t n n₀ : ℕ} {g : TopLevelFamily}
    (h : SecondDerivAtUniform L t n₀ g) (hn : n₀ ≤ n)
    (b b' : LatticeBond) (X X' : imaginaryQuaternions) (a a' : ℝ) :
    secondDerivAtUniform g L t n b b' (a • X) (a' • X') = a * a' * secondDerivAtUniform g L t n b b' X X' :=
  bondDeriv_pair_smul _ _ _ X X' a a' ((h.smooth n hn 2 _ ![X, X']).of_le (by norm_num))
private theorem SecondDerivAtUniform.hasLimit {L t n₀ : ℕ} {g : TopLevelFamily}
    (h : SecondDerivAtUniform L t n₀ g)
    (hu : ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 → ∃ v : ℝ,
      Filter.Tendsto (fun n => secondDerivAtUniform g L t n b b' X X') Filter.atTop (𝓝 v)) :
    HasLimitSecondDeriv (densityOfTopFamily L t g) := by
  intro b b' X X'
  obtain ⟨a, X₀, hX₀, rfl, -⟩ := exists_unit_smul X
  obtain ⟨a', X₀', hX₀', rfl, -⟩ := exists_unit_smul X'
  obtain ⟨v, hv⟩ := hu b b' X₀ X₀' hX₀ hX₀'
  refine ⟨a * a' * v, (hv.const_mul (a * a')).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  rw [h.read n b b' _ _ hn, h.smul hn]
private theorem abs_secondDerivLimit_sub_le {L t n₀ : ℕ} {g g' : TopLevelFamily}
    (h : SecondDerivAtUniform L t n₀ g) (h' : SecondDerivAtUniform L t n₀ g')
    (hL : HasLimitSecondDeriv (densityOfTopFamily L t g)) (hL' : HasLimitSecondDeriv (densityOfTopFamily L t g'))
    (u : ℝ) (b b' : LatticeBond) (B : ℝ)
    (hB : ∀ X X' : imaginaryQuaternions, ‖X‖ = 1 → ‖X'‖ = 1 → ∀ᶠ n in Filter.atTop,
      |secondDerivAtUniform g L t n b b' X X' - u * secondDerivAtUniform g' L t n b b' X X'| ≤ B)
    (X X' : imaginaryQuaternions) :
    |secondDerivLimit (densityOfTopFamily L t g) b b' X X' -
      u * secondDerivLimit (densityOfTopFamily L t g') b b' X X'| ≤ ‖X‖ * ‖X'‖ * B := by
  obtain ⟨a, X₀, hX₀, rfl, ha⟩ := exists_unit_smul X
  obtain ⟨a', X₀', hX₀', rfl, ha'⟩ := exists_unit_smul X'
  have ht := ((tendsto_secondDerivLimit hL b b' (a • X₀) (a' • X₀')).sub
    ((tendsto_secondDerivLimit hL' b b' (a • X₀) (a' • X₀')).const_mul u)).abs
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop n₀, hB X₀ X₀' hX₀ hX₀'] with n hn hb
  rw [h.read n b b' _ _ hn, h'.read n b b' _ _ hn, h.smul hn, h'.smul hn]
  have e : a * a' * secondDerivAtUniform g L t n b b' X₀ X₀' -
      u * (a * a' * secondDerivAtUniform g' L t n b b' X₀ X₀') =
      a * a' * (secondDerivAtUniform g L t n b b' X₀ X₀' - u * secondDerivAtUniform g' L t n b b' X₀ X₀') := by
    ring
  rw [e, abs_mul, abs_mul, ha, ha']
  exact mul_le_mul_of_nonneg_left hb (by positivity)
private theorem abs_secondDerivLimit_le {L t n₀ : ℕ} {g : TopLevelFamily} (h : SecondDerivAtUniform L t n₀ g)
    (hL : HasLimitSecondDeriv (densityOfTopFamily L t g)) (b b' : LatticeBond) (B : ℝ)
    (hB : ∀ X X' : imaginaryQuaternions, ‖X‖ = 1 → ‖X'‖ = 1 → ∀ᶠ n in Filter.atTop,
      |secondDerivAtUniform g L t n b b' X X'| ≤ B)
    (X X' : imaginaryQuaternions) :
    |secondDerivLimit (densityOfTopFamily L t g) b b' X X'| ≤ ‖X‖ * ‖X'‖ * B := by
  obtain ⟨a, X₀, hX₀, rfl, ha⟩ := exists_unit_smul X
  obtain ⟨a', X₀', hX₀', rfl, ha'⟩ := exists_unit_smul X'
  have ht := (tendsto_secondDerivLimit hL b b' (a • X₀) (a' • X₀')).abs
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop n₀, hB X₀ X₀' hX₀ hX₀'] with n hn hb
  rw [h.read n b b' _ _ hn, h.smul hn, abs_mul, abs_mul, ha, ha']
  exact mul_le_mul_of_nonneg_left hb (by positivity)
private theorem exists_limits_at_units {L t n₀ : ℕ} {gD : TopLevelFamily} {gE : ℝ → TopLevelFamily}
    {y κ C₁ C₂ : ℝ} (hy : 0 < y) (hκ : 0 < κ) (hC₁ : 0 < C₁)
    (est : ∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      ∀ n, n₀ ≤ n → 2 * (offsetNorm b.1 + offsetNorm b'.1) + 2 < n →
      |secondDerivAtUniform (gE x) L t n b b' X X' - x⁻¹ * secondDerivAtUniform gD L t n b b' X X'| ≤
        C₁ * x ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * bondPairDiam b b')))
    (cmp : ∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      ∀ (n n' r : ℕ), n₀ ≤ n → n₀ ≤ n' → 2 * r + 2 < n → 2 * r + 2 < n' → offsetNorm b.1 + 1 ≤ r →
      offsetNorm b'.1 + 1 ≤ r →
      |secondDerivAtUniform (gE x) L t n b b' X X' - secondDerivAtUniform (gE x) L t n' b b' X X'| ≤
        C₂ * x ^ (-(3 / 4 : ℝ)) * Real.exp (-(κ / 2 ^ 9 * r))) :
    (∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      ∃ v : ℝ, Filter.Tendsto (fun n => secondDerivAtUniform (gE x) L t n b b' X X') Filter.atTop (𝓝 v)) ∧
    ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 → ∃ v : ℝ,
      Filter.Tendsto (fun n => secondDerivAtUniform gD L t n b b' X X') Filter.atTop (𝓝 v) := by
  have limE : ∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 →
      ‖X'‖ = 1 → ∃ v : ℝ,
      Filter.Tendsto (fun n => secondDerivAtUniform (gE x) L t n b b' X X') Filter.atTop (𝓝 v) := by
    intro x hx b b' X X' hX hX'
    have hC : CauchySeq fun n => secondDerivAtUniform (gE x) L t n b b' X X' := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have h1 : Filter.Tendsto (fun m : ℕ => C₂ * x ^ (-(3 / 4 : ℝ)) * Real.exp (-(κ / 2 ^ 9 * (m : ℝ))))
          Filter.atTop (𝓝 0) := by
        have hr : 0 < κ / 2 ^ 9 := by positivity
        have h2 : Filter.Tendsto (fun m : ℕ => κ / 2 ^ 9 * (m : ℝ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop hr
        have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul (C₂ * x ^ (-(3 / 4 : ℝ)))
        simpa using h3
      obtain ⟨M, hM, hM'⟩ := ((h1.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop
        (offsetNorm b.1 + offsetNorm b'.1 + 1))).exists
      refine ⟨max n₀ (2 * M + 3), fun n hn n' hn' => ?_⟩
      have a1 := le_max_left n₀ (2 * M + 3)
      have a2 := le_max_right n₀ (2 * M + 3)
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (cmp x hx b b' X X' hX hX' n n' M (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) hM
    exact cauchySeq_tendsto_of_complete hC
  refine ⟨limE, ?_⟩
  intro b b' X X' hX hX'
  have hC : CauchySeq fun n => secondDerivAtUniform gD L t n b b' X X' := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hw : Real.exp (-(κ / 2 ^ 6 * (bondPairDiam b b' : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ κ / 2 ^ 6 * (bondPairDiam b b' : ℝ) := by positivity
      linarith
    have h1 : Filter.Tendsto (fun x : ℝ => 2 * C₁ * x ^ (-(1 / 2 : ℝ))) Filter.atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * C₁)
      simpa using this
    obtain ⟨x, hx1, hx2⟩ := ((h1.eventually (gt_mem_nhds (half_pos hε))).and
      (Filter.eventually_ge_atTop y)).exists
    have hx0 : 0 < x := lt_of_lt_of_le hy hx2
    obtain ⟨v, hv⟩ := limE x hx2 b b' X X' hX hX'
    have hcE := hv.cauchySeq
    rw [Metric.cauchySeq_iff] at hcE
    obtain ⟨N, hN'⟩ := hcE (ε / (2 * x)) (by positivity)
    refine ⟨max (max N n₀) (2 * (offsetNorm b.1 + offsetNorm b'.1) + 3), fun n hn n' hn' => ?_⟩
    have a1 := (le_max_left (max N n₀) (2 * (offsetNorm b.1 + offsetNorm b'.1) + 3))
    have a2 := (le_max_right (max N n₀) (2 * (offsetNorm b.1 + offsetNorm b'.1) + 3))
    have a3 := le_max_left N n₀
    have a4 := le_max_right N n₀
    have e1 := est x hx2 b b' X X' hX hX' n (by omega) (by omega)
    have e2 := est x hx2 b b' X X' hX hX' n' (by omega) (by omega)
    have e3 := hN' n (by omega) n' (by omega)
    rw [Real.dist_eq] at e3 ⊢
    generalize secondDerivAtUniform (gE x) L t n b b' X X' = P at e1 e3
    generalize secondDerivAtUniform (gE x) L t n' b b' X X' = P' at e2 e3
    generalize secondDerivAtUniform gD L t n b b' X X' = Q at e1
    generalize secondDerivAtUniform gD L t n' b b' X X' = Q' at e2
    have hb : C₁ * x ^ (-(3 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * bondPairDiam b b')) ≤
        C₁ * x ^ (-(3 / 2 : ℝ)) := by
      have h0 : 0 ≤ C₁ * x ^ (-(3 / 2 : ℝ)) := by positivity
      nlinarith
    have hxP : x * (C₁ * x ^ (-(3 / 2 : ℝ))) = C₁ * x ^ (-(1 / 2 : ℝ)) := by
      have h0 : x * x ^ (-(3 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) := by
        nth_rewrite 1 [← Real.rpow_one x]
        rw [← Real.rpow_add hx0]
        norm_num
      calc x * (C₁ * x ^ (-(3 / 2 : ℝ))) = C₁ * (x * x ^ (-(3 / 2 : ℝ))) := by ring
        _ = _ := by rw [h0]
    have hdiff : x⁻¹ * |Q - Q'| ≤ |P - P'| + 2 * (C₁ * x ^ (-(3 / 2 : ℝ))) := by
      have e : x⁻¹ * (Q - Q') = (P - P') - (P - x⁻¹ * Q) + (P' - x⁻¹ * Q') := by ring
      have h4 : |x⁻¹ * (Q - Q')| = x⁻¹ * |Q - Q'| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hx0)]
      rw [← h4, e]
      calc |(P - P') - (P - x⁻¹ * Q) + (P' - x⁻¹ * Q')| ≤
          |(P - P') - (P - x⁻¹ * Q)| + |P' - x⁻¹ * Q'| := abs_add_le _ _
        _ ≤ |P - P'| + |P - x⁻¹ * Q| + |P' - x⁻¹ * Q'| := by
            have := abs_sub (P - P') (P - x⁻¹ * Q)
            linarith
        _ ≤ _ := by linarith
    have hfin : |Q - Q'| ≤ x * |P - P'| + 2 * (C₁ * x ^ (-(1 / 2 : ℝ))) := by
      have h5 := mul_le_mul_of_nonneg_left hdiff hx0.le
      rw [← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul, mul_add, mul_left_comm x 2, hxP] at h5
      exact h5
    have h6 : x * |P - P'| < ε / 2 := by
      have h7 := mul_lt_mul_of_pos_left e3 hx0
      calc x * |P - P'| < x * (ε / (2 * x)) := h7
        _ = ε / 2 := by field_simp
    have h7 : 2 * C₁ * x ^ (-(1 / 2 : ℝ)) < ε / 2 := hx1
    linarith
  exact cauchySeq_tendsto_of_complete hC
private theorem hasSum_limitFormTerm_of_bounds {hD hE : LocalDensity} {w : LatticeBond × LatticeBond → ℝ}
    {S C P u : ℝ} (hw : HasSum w S) (hw0 : ∀ cc, 0 ≤ w cc) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (bD : ∀ cc, ‖limitFormTerm hD unitPlaneCurvature unitPlaneCurvature cc‖ ≤ C * w cc)
    (bE : ∀ cc, ‖limitFormTerm hE unitPlaneCurvature unitPlaneCurvature cc -
      u * limitFormTerm hD unitPlaneCurvature unitPlaneCurvature cc‖ ≤ (C * P) * w cc) :
    ∃ v : ℝ, HasSum (limitFormTerm hE unitPlaneCurvature unitPlaneCurvature) v ∧
      HasSum (limitFormTerm hD unitPlaneCurvature unitPlaneCurvature) (curvatureCoefficient hD) ∧
      |curvatureCoefficient hD| ≤ C * S ∧ |v - u * curvatureCoefficient hD| ≤ (C * P) * S := by
  have sB : Summable w := hw.summable
  have sD : Summable (limitFormTerm hD unitPlaneCurvature unitPlaneCurvature) :=
    Summable.of_norm_bounded (sB.mul_left C) bD
  have hsD : HasSum (limitFormTerm hD unitPlaneCurvature unitPlaneCurvature) (curvatureCoefficient hD) :=
    sD.hasSum
  have sDiff : Summable fun cc => limitFormTerm hE unitPlaneCurvature unitPlaneCurvature cc -
      u * limitFormTerm hD unitPlaneCurvature unitPlaneCurvature cc :=
    Summable.of_norm_bounded (sB.mul_left (C * P)) bE
  have sE : Summable (limitFormTerm hE unitPlaneCurvature unitPlaneCurvature) := by
    have h1 := sDiff.add (sD.mul_left u)
    refine h1.congr fun cc => ?_
    ring
  refine ⟨_, sE.hasSum, hsD, ?_, ?_⟩
  · have h2 := tsum_of_norm_bounded (hw.mul_left C) bD
    rwa [Real.norm_eq_abs] at h2
  · have h1 : HasSum (fun cc => limitFormTerm hE unitPlaneCurvature unitPlaneCurvature cc -
        u * limitFormTerm hD unitPlaneCurvature unitPlaneCurvature cc)
        (∑' cc, limitFormTerm hE unitPlaneCurvature unitPlaneCurvature cc - u * curvatureCoefficient hD) :=
      sE.hasSum.sub (hsD.mul_left u)
    have h2 := tsum_of_norm_bounded (hw.mul_left (C * P)) bE
    rwa [h1.tsum_eq, Real.norm_eq_abs] at h2
private theorem hasUnitPlaneValue_of_sum_three {h₁ h₂ h₃ h : LocalDensity} {v₁ v₂ v₃ : ℝ} (n₀ : ℕ)
    (L₁ : HasLimitSecondDeriv h₁) (L₂ : HasLimitSecondDeriv h₂) (L₃ : HasLimitSecondDeriv h₃)
    (s₁ : HasSum (limitFormTerm h₁ unitPlaneCurvature unitPlaneCurvature) v₁)
    (s₂ : HasSum (limitFormTerm h₂ unitPlaneCurvature unitPlaneCurvature) v₂)
    (s₃ : HasSum (limitFormTerm h₃ unitPlaneCurvature unitPlaneCurvature) v₃)
    (hsplit : ∀ (n : ℕ) (b b' : LatticeBond) (X X' : imaginaryQuaternions), n₀ ≤ n →
      mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] =
        mixedDeriv (h₁ n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] +
        mixedDeriv (h₂ n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] +
        mixedDeriv (h₃ n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X']) :
    HasUnitPlaneValue h (v₁ + v₂ + v₃) := by
  have ten : ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), Filter.Tendsto
      (fun n : ℕ => mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'])
      Filter.atTop (𝓝 (secondDerivLimit h₁ b b' X X' + secondDerivLimit h₂ b b' X X' +
        secondDerivLimit h₃ b b' X X')) := by
    intro b b' X X'
    refine (((tendsto_secondDerivLimit L₁ b b' X X').add (tendsto_secondDerivLimit L₂ b b' X X')).add
      (tendsto_secondDerivLimit L₃ b b' X X')).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn'
    exact (hsplit n b b' X X' hn').symm
  have LS : HasLimitSecondDeriv h := fun b b' X X' => ⟨_, ten b b' X X'⟩
  refine ⟨LS, ?_⟩
  have hfe : limitFormTerm h unitPlaneCurvature unitPlaneCurvature = fun cc =>
      limitFormTerm h₁ unitPlaneCurvature unitPlaneCurvature cc +
        limitFormTerm h₂ unitPlaneCurvature unitPlaneCurvature cc +
        limitFormTerm h₃ unitPlaneCurvature unitPlaneCurvature cc := by
    funext cc
    exact tendsto_nhds_unique (tendsto_secondDerivLimit LS _ _ _ _) (ten _ _ _ _)
  rw [hfe]
  exact (s₁.add s₂).add s₃
private theorem secondDerivAtUniform_sum_three {L t n₀ n : ℕ} {g₁ g₂ g₃ g : TopLevelFamily}
    (h₁ : SecondDerivAtUniform L t n₀ g₁) (h₂ : SecondDerivAtUniform L t n₀ g₂)
    (h₃ : SecondDerivAtUniform L t n₀ g₃) (hn : n₀ ≤ n)
    (hg : g (cubicTorusFrame L t n) 0 = fun V' => (g₁ (cubicTorusFrame L t n) 0 V' +
      g₂ (cubicTorusFrame L t n) 0 V') + g₃ (cubicTorusFrame L t n) 0 V')
    (b b' : LatticeBond) (X X' : imaginaryQuaternions) :
    secondDerivAtUniform g L t n b b' X X' = secondDerivAtUniform g₁ L t n b b' X X' +
      secondDerivAtUniform g₂ L t n b b' X X' + secondDerivAtUniform g₃ L t n b b' X X' := by
  have c₁ := (h₁.smooth n hn 2 (bondsAt 0 ![b, b']) ![X, X']).of_le
    (m := ((2 : ℕ) : WithTop ℕ∞)) (by norm_num)
  have c₂ := (h₂.smooth n hn 2 (bondsAt 0 ![b, b']) ![X, X']).of_le
    (m := ((2 : ℕ) : WithTop ℕ∞)) (by norm_num)
  have c₃ := (h₃.smooth n hn 2 (bondsAt 0 ![b, b']) ![X, X']).of_le
    (m := ((2 : ℕ) : WithTop ℕ∞)) (by norm_num)
  unfold secondDerivAtUniform
  rw [hg, bondDeriv_add _ _ _ _ _ (c₁.add c₂) c₃, bondDeriv_add _ _ _ _ _ c₁ c₂]
theorem stepCurvatureValue_of_estimates (hE2 : densityExcessSecondOrderStatement)
    (hN : densitiesNearLimitsStatement) (hSm : densityExcessSmallStatement)
    (hLim : limitDensitiesSmoothStatement) (hRef : referenceSmoothStatement)
    (hTop : _root_.YangMills.Construction.TorusLumps.TopFamilyOnTori) (hFin : PotentialSumsFinite) :
    stepCurvatureValueStatement := by
  refine EventuallyOrdered.mono ((((hE2.and hN).and hSm).and hLim).and hRef) ?_
  rintro T hT hn ⟨⟨⟨⟨c₂, cN⟩, cSm⟩, cLim⟩, cRef⟩ hroom
  obtain ⟨y₁, C₁, hy₁, hC₁, g₂⟩ := c₂ hroom
  obtain ⟨y₂, C₂, hy₂, hC₂, gN⟩ := cN hroom
  obtain ⟨y₃, C₃, hy₃, hC₃, gSm⟩ := cSm hroom
  have gLim := cLim hroom
  obtain ⟨Eh, gRef⟩ := cRef hroom
  have hκ := hT.κ_pos
  have hσ := hT.σ_pos
  obtain ⟨sB, -, -, -, -, -, -⟩ := hFin T.κ 1 hκ one_pos
  have hyy₁ : y₁ ≤ max (max y₁ y₂) (max y₃ 1) := (le_max_left _ _).trans (le_max_left _ _)
  have hyy₂ : y₂ ≤ max (max y₁ y₂) (max y₃ 1) := (le_max_right _ _).trans (le_max_left _ _)
  have hyy₃ : y₃ ≤ max (max y₁ y₂) (max y₃ 1) := (le_max_left _ _).trans (le_max_right _ _)
  have hy1 : 1 ≤ max (max y₁ y₂) (max y₃ 1) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max (max y₁ y₂) (max y₃ 1) = y at hyy₁ hyy₂ hyy₃ hy1
  have hy0 : 0 < y := by linarith
  have hwS : HasSum (fun cc : LatticeBond × LatticeBond => potentialNorm cc.1 * potentialNorm cc.2 *
      Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2))) (potentialDecaySum T.κ) := sB.hasSum
  have hw0 : ∀ cc : LatticeBond × LatticeBond, 0 ≤ potentialNorm cc.1 * potentialNorm cc.2 *
      Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2)) := fun cc => by
    simp only [potentialNorm]
    positivity
  have hsB0 : 0 ≤ potentialDecaySum T.κ := hwS.nonneg hw0
  refine ⟨y, C₁ * (potentialDecaySum T.κ + 1), hy0, by positivity, ?_⟩
  intro ℓ hm hfits t
  have hcold : ∀ n : ℕ, IsSmallCurvature (5 / 4 * T.σ)
      (uniformField (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n).top) :=
    fun n => uniform_isSmallCurvature _ (by positivity)
  have hcold' : ∀ n : ℕ, IsSmallCurvature (9 / 8 * T.σ)
      (uniformField (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n).top) :=
    fun n => uniform_isSmallCurvature _ (by positivity)
  have htop : ∀ n, T.n₀ ≤ n → IsCubicTopTorus T.L t T.n₀ (cubicTorusFrame T.L t n) :=
    fun n h => ⟨rfl, rfl, n, fun _ => rfl, h⟩
  have hread : ∀ (g : TopLevelFamily) (n : ℕ) (b b' : LatticeBond) (X X' : imaginaryQuaternions), T.n₀ ≤ n →
      mixedDeriv (densityOfTopFamily T.L t g n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] =
        secondDerivAtUniform g T.L t n b b' X X' := by
    intro g n b b' X X' h
    have h1 := (hTop ℓ hfits t ℓ.threshold g le_rfl).2.2.2.2 b b' X X' n (by rw [hm.n₀_eq]; exact h)
    rwa [hm.side_eq] at h1
  have rD : SecondDerivAtUniform T.L t T.n₀ (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t)) :=
    ⟨fun n h => (g₂ t y hyy₁ _ 0 _ (htop n h) (hcold n)).1, fun n b b' X X' h => hread _ n b b' X X' h⟩
  have rG : SecondDerivAtUniform T.L t T.n₀ (fun _ Y V => stepDensity T.a T.ρA T.lam Y V) :=
    ⟨fun n h => (gLim t _ 0 _ (htop n h) (hcold n)).1, fun n b b' X X' h => hread _ n b b' X X' h⟩
  have rF : SecondDerivAtUniform T.L t T.n₀
      (fun _ Y V => cellCentredExpansion true T.a T.ρA 0 (T.localReference t) Y 0 V) :=
    ⟨fun n h => (gLim t _ 0 _ (htop n h) (hcold n)).2, fun n b b' X X' h => hread _ n b b' X X' h⟩
  have rE : ∀ x, y ≤ x → SecondDerivAtUniform T.L t T.n₀ (densityExcess T t x) := fun x hx =>
    ⟨fun n h => (gSm t x (hyy₃.trans hx) _ 0 _ (htop n h) (hcold n)).1,
      fun n b b' X X' h => hread _ n b b' X X' h⟩
  have est : ∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 →
      ‖X'‖ = 1 → ∀ n, T.n₀ ≤ n → 2 * (offsetNorm b.1 + offsetNorm b'.1) + 2 < n →
      |secondDerivAtUniform (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t)) T.L t n b b' X X'| ≤
        C₁ * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam b b')) ∧
      |secondDerivAtUniform (densityExcess T t x) T.L t n b b' X X' -
          x⁻¹ * secondDerivAtUniform (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t))
            T.L t n b b' X X'| ≤
        C₁ * x ^ (-(3 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam b b')) := by
    intro x hx b b' X X' hX hX' n hn' hn''
    have h1 := (g₂ t x (hyy₁.trans hx) _ 0 _ (htop n hn') (hcold n)).2 2 (bondsAt 0 ![b, b']) ![X, X'] le_rfl
      (areUnitVectors_pair hX hX')
    rwa [bondSpan_lattice T.L t n b b' hn''] at h1
  have cmp : ∀ (x : ℝ), y ≤ x → ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions), ‖X‖ = 1 →
      ‖X'‖ = 1 → ∀ (n n' r : ℕ),
      T.n₀ ≤ n → T.n₀ ≤ n' → 2 * r + 2 < n → 2 * r + 2 < n' → offsetNorm b.1 + 1 ≤ r →
      offsetNorm b'.1 + 1 ≤ r →
      |secondDerivAtUniform (densityExcess T t x) T.L t n b b' X X' -
          secondDerivAtUniform (densityExcess T t x) T.L t n' b b' X X'| ≤
        C₂ * x ^ (-(3 / 4 : ℝ)) * Real.exp (-(T.κ / 2 ^ 9 * r)) := by
    intro x hx b b' X X' hX hX' n n' r hn' hn'' hr hr' hb hb'
    have hs : ∀ m, 1 ≤ m → ∀ i, (cubicTorusFrame T.L t m).extent i ≠ 0 := by
      intro m hm' i
      simp only [cubicTorusFrame]
      omega
    have hag : AgreeOnBall (finiteCells (cubicTorusFrame T.L t n))
        (uniformField (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n).top)
        (finiteCells (cubicTorusFrame T.L t n'))
        (uniformField (cubicTorusFrame T.L t n') (cubicTorusFrame T.L t n').top) 0 0 r := by
      refine ⟨fun i => Or.inr hr, fun i => Or.inr hr', fun h _ => ?_, fun _ _ => rfl⟩
      exact ⟨fun _ => mem_finiteCells (hs n' (by omega)) _, fun _ => mem_finiteCells (hs n (by omega)) _⟩
    have h1 := (gN t x (hyy₂.trans hx)).2 (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n')
      (htop n hn') (htop n' hn'')
      0 0 _ _ r 2 ![b, b'] ![X, X'] (hcold' n) (hcold' n') hag le_rfl
      (by
        intro l
        fin_cases l
        · exact bondWithinRadius_of_offsetNorm b hb
        · exact bondWithinRadius_of_offsetNorm b' hb')
      (areUnitVectors_pair hX hX')
    have d₁ := bondDeriv_sub_const (densityExcess T t x (cubicTorusFrame T.L t n) 0)
      (densityExcess T t x (cubicTorusFrame T.L t n) 0 (uniformField _ _))
      (uniformField _ _) (k := 2) (by norm_num) (bondsAt 0 ![b, b']) ![X, X']
      (((rE x hx).smooth n hn' 2 _ _).of_le (by norm_num))
    have d₂ := bondDeriv_sub_const (densityExcess T t x (cubicTorusFrame T.L t n') 0)
      (densityExcess T t x (cubicTorusFrame T.L t n') 0 (uniformField _ _))
      (uniformField _ _) (k := 2) (by norm_num) (bondsAt 0 ![b, b']) ![X, X']
      (((rE x hx).smooth n' hn'' 2 _ _).of_le (by norm_num))
    have e₁ : bondDeriv (centredFamily (densityExcess T t x) (cubicTorusFrame T.L t n) 0)
        (uniformField _ _) (bondsAt 0 ![b, b']) ![X, X'] =
        secondDerivAtUniform (densityExcess T t x) T.L t n b b' X X' := d₁
    have e₂ : bondDeriv (centredFamily (densityExcess T t x) (cubicTorusFrame T.L t n') 0)
        (uniformField _ _) (bondsAt 0 ![b, b']) ![X, X'] =
        secondDerivAtUniform (densityExcess T t x) T.L t n' b b' X X' := d₂
    rw [e₁, e₂] at h1
    exact h1
  obtain ⟨limE, limD⟩ := exists_limits_at_units (gE := densityExcess T t) hy0 hκ hC₁
    (fun x hx b b' X X' hX hX' n h1 h2 => (est x hx b b' X X' hX hX' n h1 h2).2) cmp
  have LD : HasLimitSecondDeriv (T.secondOrderDensity t) := rD.hasLimit limD
  have LE : ∀ x, y ≤ x → HasLimitSecondDeriv (densityOfTopFamily T.L t (densityExcess T t x)) :=
    fun x hx => (rE x hx).hasLimit (limE x hx)
  have bD : ∀ cc : LatticeBond × LatticeBond,
      ‖limitFormTerm (T.secondOrderDensity t) unitPlaneCurvature unitPlaneCurvature cc‖ ≤
      C₁ * (potentialNorm cc.1 * potentialNorm cc.2 * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2))) := by
    intro cc
    have h1 := abs_secondDerivLimit_le rD LD cc.1 cc.2 (C₁ * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2)))
      (fun X X' hX hX' => by
        filter_upwards [Filter.eventually_ge_atTop
          (max T.n₀ (2 * (offsetNorm cc.1.1 + offsetNorm cc.2.1) + 3))] with n hn'
        have a1 := le_trans (le_max_left _ _) hn'
        have a2 := le_trans (le_max_right _ _) hn'
        exact (est y le_rfl cc.1 cc.2 X X' hX hX' n a1 (by omega)).1)
      (linearPotential unitPlaneCurvature cc.1) (linearPotential unitPlaneCurvature cc.2)
    rw [Real.norm_eq_abs]
    refine h1.trans (le_of_eq ?_)
    simp only [potentialNorm]
    ring
  have bE : ∀ (x : ℝ), y ≤ x → ∀ cc : LatticeBond × LatticeBond,
      ‖limitFormTerm (densityOfTopFamily T.L t (densityExcess T t x)) unitPlaneCurvature unitPlaneCurvature cc -
        x⁻¹ * limitFormTerm (T.secondOrderDensity t) unitPlaneCurvature unitPlaneCurvature cc‖ ≤
      (C₁ * x ^ (-(3 / 2 : ℝ))) *
        (potentialNorm cc.1 * potentialNorm cc.2 * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2))) := by
    intro x hx cc
    have h1 := abs_secondDerivLimit_sub_le (rE x hx) rD (LE x hx) LD x⁻¹ cc.1 cc.2
      (C₁ * x ^ (-(3 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondPairDiam cc.1 cc.2)))
      (fun X X' hX hX' => by
        filter_upwards [Filter.eventually_ge_atTop
          (max T.n₀ (2 * (offsetNorm cc.1.1 + offsetNorm cc.2.1) + 3))] with n hn'
        have a1 := le_trans (le_max_left _ _) hn'
        have a2 := le_trans (le_max_right _ _) hn'
        exact (est x hx cc.1 cc.2 X X' hX hX' n a1 (by omega)).2)
      (linearPotential unitPlaneCurvature cc.1) (linearPotential unitPlaneCurvature cc.2)
    rw [Real.norm_eq_abs]
    refine h1.trans (le_of_eq ?_)
    simp only [potentialNorm]
    ring
  obtain ⟨-, -, hsD, hdle, -⟩ := hasSum_limitFormTerm_of_bounds (hE := T.secondOrderDensity t) hwS hw0
    hC₁.le le_rfl bD (u := 1) (P := 0) (by
      intro cc
      simp)
  refine ⟨⟨⟨LD, hsD⟩, ?_⟩, ?_⟩
  · refine hdle.trans ?_
    have hd : T.secondCoeff t = curvatureCoefficient (T.secondOrderDensity t) := rfl
    nlinarith
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hx
  have hP0 : 0 < x ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  obtain ⟨vE, hsE, -, -, hdiff⟩ := hasSum_limitFormTerm_of_bounds hwS hw0 hC₁.le hP0.le bD (bE x hx)
  have hb := gRef ℓ hm hfits t
  have hu := hb.curvatureForm_step.2 unitPlaneCurvature unitPlaneCurvature
    unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  have hv := hb.curvatureForm_minimizer.2 unitPlaneCurvature unitPlaneCurvature
    unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlane, mul_one] at hu hv
  have hsplit : ∀ (n : ℕ) (b b' : LatticeBond) (X X' : imaginaryQuaternions), T.n₀ ≤ n →
      mixedDeriv (T.minimizerDensity t x n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] =
        mixedDeriv (T.stepDensity t n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] +
        mixedDeriv (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t) n 0) (trivialField n)
          ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] +
        mixedDeriv (densityOfTopFamily T.L t (densityExcess T t x) n 0) (trivialField n)
          ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] := by
    intro n b b' X X' hn'
    have e₁ := hread (fun _ Y V => interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p
      (T.localReference t) Y V + expansionDensity true T.a T.ρA T.ballRadius x 0 T.p (T.localReference t) Y V)
      n b b' X X' hn'
    have e₂ := hread (fun _ Y V => stepDensity T.a T.ρA T.lam Y V) n b b' X X' hn'
    have e₃ := hread (fun _ Y V => cellCentredExpansion true T.a T.ρA 0 (T.localReference t) Y 0 V) n b b' X X' hn'
    have e₄ := hread (densityExcess T t x) n b b' X X' hn'
    have e₅ := secondDerivAtUniform_sum_three (g := fun _ Y V => interactionDensity true T.a T.ρA T.ballRadius
      T.lam x 0 T.p (T.localReference t) Y V +
      expansionDensity true T.a T.ρA T.ballRadius x 0 T.p (T.localReference t) Y V) rG rF (rE x hx) hn' (by
        funext V'
        unfold densityExcess
        ring) b b' X X'
    refine e₁.trans (e₅.trans ?_)
    rw [← e₂, ← e₃, ← e₄]
    rfl
  refine ⟨T.oneLoopCoeff t + 0 + vE, hasUnitPlaneValue_of_sum_three T.n₀ hb.curvatureForm_step.1
    hb.curvatureForm_minimizer.1 (LE x hx) hu hv hsE hsplit, ?_⟩
  have e : T.oneLoopCoeff t + 0 + vE - T.oneLoopCoeff t - T.secondCoeff t / x =
      vE - x⁻¹ * T.secondCoeff t := by
    rw [div_eq_inv_mul]
    ring
  rw [e]
  refine hdiff.trans ?_
  have h0 : 0 ≤ C₁ * x ^ (-(3 / 2 : ℝ)) := by positivity
  nlinarith
end YangMills.Construction.StepDensities
end
