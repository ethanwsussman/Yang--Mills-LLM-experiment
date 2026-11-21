import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsADensity
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfAFamily
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsCarried
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheFamilyAtTheLeastFieldIsAnalytic
import YangMills.Construction.SummableBoundsOfTheFlow.TheFamilyAtTheLeastFieldIsCarried
import YangMills.Construction.SummableBoundsOfTheFlow.TheOneLoopNumberIsHad
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevel
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsReadBelowAtItsLevel
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import YangMills.Construction.SummableBoundsOfTheFlow.TiltsReadBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TopFamilyHasANorm
import YangMills.Construction.SummableBoundsOfTheFlow.TransportOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps ReferenceDensity StepDensities ShareFamilies TopLevelSites StepCosts
  FamilyNorms Interpolation ColdStepAtMirrorFrames
namespace StepDensities
namespace NextLevel
section Calculus
variable {n k : ℕ}
private theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem torusDecayFactor_pos (L : ℕ) (δ s : ℝ) : 0 < torusDecayFactor L δ s := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
private theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
private theorem isCold_mono {s s' : ℝ} {V : TorusField n} (hs : s ≤ s') (hV : IsCold s V) : IsCold s' V :=
  fun x μ ν h => lt_of_lt_of_le (hV x μ ν h) hs
private theorem mixedDeriv_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
private theorem mixedDeriv_sub_const (G : TorusField n → ℝ) (a : ℝ) (W : TorusField n) (c : Fin (k + 1) → TorusBond n)
    (X : Fin (k + 1) → imaginaryQuaternions) : mixedDeriv (fun V => G V - a) W c X = mixedDeriv G W c X := by
  unfold mixedDeriv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have : (fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (perturb c X τ W) - a) =
      fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (perturb c X τ W) := by
    funext τ
    exact fderiv_sub_const _
  simp only [Function.comp, this]
private theorem bondDeriv_zero {F : BlockFrame} {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem bondDeriv_sub_const {F : BlockFrame} {j : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W : F.GaugeField j)
    (c : Fin (k + 1) → F.Site j × Fin 4) (X : Fin (k + 1) → imaginaryQuaternions) :
    bondDeriv (fun W' => G W' - a) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have : (fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) - a) =
      fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) := by
    funext τ
    exact fderiv_sub_const _
  simp only [Function.comp, this]
private theorem pathHolonomy_uniformField {F : BlockFrame} {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (ColdStepAtMirrorFrames.uniformField F j) x l = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.pathHolonomy_uniformField <;> assumption
private theorem isSmallCurvature_uniformField {F : BlockFrame} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (ColdStepAtMirrorFrames.uniformField F j) := by
  intro p _
  simpa [plaquetteDefect, plaquetteHolonomy, pathHolonomy_uniformField] using hs
abbrev _root_.YangMills.DeltaSharedProofs.p500582 := @isSmallCurvature_uniformField
abbrev _root_.YangMills.SharedProofs.p8038 := @isSmallCurvature_uniformField
private theorem mixedDeriv_add_add_smul {A B S : TorusField n → ℝ} {W : TorusField n} (b : ℝ)
    {c : Fin k → TorusBond n} {X : Fin k → imaginaryQuaternions}
    (hA : ContDiffAt ℝ k (fun τ : Fin k → ℝ => A (perturb c X τ W)) 0)
    (hB : ContDiffAt ℝ k (fun τ : Fin k → ℝ => B (perturb c X τ W)) 0)
    (hS : ContDiffAt ℝ k (fun τ : Fin k → ℝ => S (perturb c X τ W)) 0) :
    mixedDeriv (fun V => A V + B V + b * S V) W c X =
      mixedDeriv A W c X + mixedDeriv B W c X + b * mixedDeriv S W c X := by
  unfold mixedDeriv
  have h2 : (fun τ : Fin k → ℝ => A (perturb c X τ W) + B (perturb c X τ W) + b * S (perturb c X τ W)) =
      ((fun τ : Fin k → ℝ => A (perturb c X τ W)) + (fun τ : Fin k → ℝ => B (perturb c X τ W))) +
        b • (fun τ : Fin k → ℝ => S (perturb c X τ W)) := rfl
  have hAB : ContDiffAt ℝ k ((fun τ : Fin k → ℝ => A (perturb c X τ W)) +
      (fun τ : Fin k → ℝ => B (perturb c X τ W))) 0 :=
    hA.add hB
  have hbS : ContDiffAt ℝ k (b • fun τ : Fin k → ℝ => S (perturb c X τ W)) 0 := hS.const_smul b
  rw [h2, iteratedFDeriv_add_apply hAB hbS, iteratedFDeriv_add_apply hA hB, iteratedFDeriv_const_smul_apply hS]
  rfl
end Calculus
section TopLevel
variable {L t n : ℕ}
private theorem period_eq (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
private def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
private theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread (frameBonds L t c) X σ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.readAtLevel_perturb <;> assumption
private theorem mixedDeriv_readAtLevel [NeZero n] (G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ)
    {k : ℕ} (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V c X =
      bondDeriv G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (frameBonds L t c) X := by apply _root_.YangMills.Construction.TopFamilyEvaluations.mixedDeriv_readAtLevel <;> assumption
private theorem siteSupDist_torusSiteInFrame [NeZero n] (y z : TorusSite n) :
    siteSupDist (F := torusFrame L t n) (j := (torusFrame L t n).top)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) = TorusFields.supDist y z := by apply _root_.YangMills.Construction.TopFamilyEvaluations.siteSupDist_torusSiteInFrame <;> assumption
private theorem bondSpan_frameBonds [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n) :
    bondSpan (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) (frameBonds L t c) = supportDiam y c := by apply _root_.YangMills.Construction.TopFamilyEvaluations.bondSpan_frameBonds <;> assumption
private theorem isSmallCurvature_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
private theorem isCubicTopTorus_torusFrame [NeZero n] {n₀ : ℕ} (hn : n₀ ≤ n) :
    IsCubicTopTorus L t n₀ (torusFrame L t n) :=
  ⟨rfl, rfl, n, fun _ => rfl, hn⟩
end TopLevel
section WilsonWeightSeriesExpansion
variable {F : BlockFrame}
private def minimizerExpansion (a ρA : ℝ) (f : LocalFamily) : TopLevelFamily :=
  fun _ Y V => cellCentredExpansion true a ρA 0 f Y 0 V
private theorem coordsAboveFrame_radius (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρA m V η = coordsAboveFrame true a ρA 0 V η := by
  funext x i
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame]
private theorem cellCentredExpansion_eq_minimizerExpansion (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell) :
    cellCentredExpansion true a ρA m f Y 0 = minimizerExpansion a ρA f F Y := by
  funext V
  simp only [minimizerExpansion, cellCentredExpansion, centredExpansion, fieldAboveFrame, coordsAboveFrame_radius a ρA m V]
private theorem interpolatedBlockExpansion_zero (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell) :
    interpolatedBlockExpansion 0 a ρA m f Y 0 = minimizerExpansion a ρA f F Y := by
  funext V
  have e : interpolatedCoords 0 a ρA m V (0 : StepVariable (finiteCells F)) = coordsAboveFrame true a ρA 0 V 0 := by
    funext x i
    simp [interpolatedCoords, coordsAboveFrame, interpolatedFrame, ColdStepAtMirrorFrames.stepFrame]
  simp only [minimizerExpansion, cellCentredExpansion, centredExpansion, fieldAboveFrame, interpolatedBlockExpansion, interpolatedExpansion,
    interpolatedField, e]
private theorem expansionAtFrameFamily_eq (T : ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (f : LocalFamily) :
    expansionAtFrameFamily T true x f = minimizerExpansion T.a T.chainParams.ρA f := by
  funext F Y V
  exact congrFun (cellCentredExpansion_eq_minimizerExpansion T.a T.chainParams.ρA (frameRadius x) f Y) V
end WilsonWeightSeriesExpansion
private theorem isRegularFamily_mono {L t n₀ : ℕ} {σ δ E E₃ E' E₃' : ℝ} {f : LocalFamily}
    (h : IsRegularFamily L t n₀ σ δ E E₃ f) (hE : E ≤ E') (h₃ : E₃ ≤ E₃') : IsRegularFamily L t n₀ σ δ E' E₃' f := by
  refine ⟨h.smooth, h.gauge_invariant, h.translation_invariant, ?_, ?_, h.flat_limit⟩
  · intro F hF y W k c X hW h1 h3 hX
    refine (h.decay F hF y W k c X hW h1 h3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (torusDecayFactor_pos _ _ _).le
    split_ifs
    · exact h₃
    · exact hE
  · intro F F' hF hF' y y' W W' r k b X hW hW' hA hk hb hX
    refine (h.locality F F' hF hF' y y' W W' r k b X hW hW' hA hk hb hX).trans ?_
    exact div_le_div_of_nonneg_right hE (torusDecayFactor_pos _ _ _).le
private theorem localComparison_centeredFamily {ℓ : TorusLumps.StepParameters} {h : LocalDensity} {e : ℕ → ℝ}
    (hσ : 0 < ℓ.threshold) (hc : LocalComparison ℓ h e) :
    LocalComparison ℓ (centeredFamily h) fun m => 2 * e m := by
  intro n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
  have hfA : FieldsAgreeNear (trivialField n) (trivialField n') y y' m := fun _ _ => rfl
  rcases k with _ | k
  · have a₁ := hc n n' hn hn' y y' W W' m h1 h2 hW hW' hA 0 b X hk hb hX
    have a₂ := hc n n' hn hn' y y' (trivialField n) (trivialField n') m h1 h2 (isCold_trivialField hσ n)
      (isCold_trivialField hσ n') hfA 0 b X hk hb hX
    simp only [mixedDeriv_zero] at a₁ a₂ ⊢
    simp only [centeredFamily, centered]
    rw [abs_le] at a₁ a₂ ⊢
    constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]
  · have e₁ : mixedDeriv (centeredFamily h n y) W (fun l => bondFrom y (b l)) X =
        mixedDeriv (h n y) W (fun l => bondFrom y (b l)) X := mixedDeriv_sub_const _ _ _ _ _
    have e₂ : mixedDeriv (centeredFamily h n' y') W' (fun l => bondFrom y' (b l)) X =
        mixedDeriv (h n' y') W' (fun l => bondFrom y' (b l)) X := mixedDeriv_sub_const _ _ _ _ _
    rw [e₁, e₂]
    have a₁ := hc n n' hn hn' y y' W W' m h1 h2 hW hW' hA (k + 1) b X hk hb hX
    have e0 : 0 ≤ e m := (abs_nonneg _).trans a₁
    linarith
private theorem isCurvatureFamily_of_normBounded {ℓ : TorusLumps.StepParameters} {ε ε₃ : ℝ} {g : LocalDensity}
    (h : IsNormBoundedFamily ℓ ε ε₃ g) : IsCurvatureFamily ℓ (max ε ε₃) g := by
  refine ⟨h.admissible.smooth, h.admissible.gauge, h.admissible.translation, ?_, ?_⟩
  · intro n _ hn y W hW k c X h1 h3 hX
    refine (h.decay n hn y W hW k c X h1 h3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (weight_pos _ _).le
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  · intro n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
    refine (h.comparison n n' hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX).trans ?_
    exact div_le_div_of_nonneg_right (le_max_left _ _) (weight_pos _ _).le
private theorem sumInvariant_add {ℓ : TorusLumps.StepParameters} {h h' : LocalDensity}
    (a : SumInvariantUnderIsometries ℓ h) (b : SumInvariantUnderIsometries ℓ h') :
    SumInvariantUnderIsometries ℓ (h + h') := by
  intro n _ hn g W W' hW hW' hC
  have e : ∀ V : TorusField n, ∑ y, centered (h + h') n y V = ∑ y, centered h n y V + ∑ y, centered h' n y V := by
    intro V
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered, Pi.add_apply]
    ring
  rw [e, e, a n hn g W W' hW hW' hC, b n hn g W W' hW hW' hC]
private theorem sumInvariant_smul {ℓ : TorusLumps.StepParameters} {h : LocalDensity} (c : ℝ)
    (a : SumInvariantUnderIsometries ℓ h) : SumInvariantUnderIsometries ℓ (c • h) := by
  intro n _ hn g W W' hW hW' hC
  have e : ∀ V : TorusField n, ∑ y, centered (c • h) n y V = c * ∑ y, centered h n y V := by
    intro V
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, e, a n hn g W W' hW hW' hC]
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) : unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem curvaturePairing_unitPlane : curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
private theorem hasCurvatureForm_zero (hOne : InvariantFamilyCurvatureForm) {ℓ : TorusLumps.StepParameters}
    (hf : ℓ.Admissible) {C : ℝ} {h : LocalDensity} (hc : IsCurvatureFamily ℓ C h)
    (hcar : SumInvariantUnderIsometries ℓ h)
    (h0 : HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature) 0) : HasCurvatureForm h 0 := by
  obtain ⟨hlim, b, hb⟩ := hOne ℓ hf C h hc hcar
  have h1 : HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature)
      (b * curvaturePairing unitPlaneCurvature unitPlaneCurvature) :=
    hb unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  have hb0 : b = 0 := by
    have := h1.unique h0
    rwa [curvaturePairing_unitPlane, mul_one] at this
  refine ⟨fun c c' X X' => ⟨_, hlim c c' X X'⟩, fun A A' hA hA' => ?_⟩
  have := hb A A' hA hA'
  rw [hb0] at this
  exact this
private theorem runningMax_le {e : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (j : ℕ) (h : ∀ i, 1 ≤ i → i ≤ j → e i ≤ B) :
    runningMax e j ≤ B := by
  induction j with
  | zero => exact hB
  | succ j ih =>
    exact max_le (ih fun i h1 h2 => h i h1 (by omega)) (h _ (by omega) le_rfl)
private theorem runningMax_le_maxLowerOrderBounds {E₃ : ℝ} {Eh : ℕ → ℝ} (hE : 0 ≤ E₃) (hEh : ∀ k, 0 ≤ Eh k)
    {k : ℕ} (h4 : 4 ≤ k) (h6 : k ≤ 6) :
    runningMax (fun j => if j ≤ 3 then E₃ else Eh j) (k - 1) ≤ maxLowerOrderBounds E₃ Eh k ∧
      0 ≤ maxLowerOrderBounds E₃ Eh k := by
  have hk : k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk with rfl | rfl | rfl
  · have hb : maxLowerOrderBounds E₃ Eh 4 = E₃ := by simp [maxLowerOrderBounds]
    rw [hb]
    refine ⟨runningMax_le hE _ fun i _ h2 => ?_, hE⟩
    have : i ≤ 3 := by omega
    simp [this]
  · have hb : maxLowerOrderBounds E₃ Eh 5 = max E₃ (Eh 4) := by simp [maxLowerOrderBounds]
    rw [hb]
    have h0 : 0 ≤ max E₃ (Eh 4) := hE.trans (le_max_left _ _)
    refine ⟨runningMax_le h0 _ fun i _ h2 => ?_, h0⟩
    by_cases h3 : i ≤ 3
    · simp only [h3, if_true]
      exact le_max_left _ _
    · have : i = 4 := by omega
      subst this
      simp
  · have hb : maxLowerOrderBounds E₃ Eh 6 = max (max E₃ (Eh 4)) (Eh 5) := by simp [maxLowerOrderBounds]
    rw [hb]
    have h0 : 0 ≤ max (max E₃ (Eh 4)) (Eh 5) := (hE.trans (le_max_left _ _)).trans (le_max_left _ _)
    refine ⟨runningMax_le h0 _ fun i _ h2 => ?_, h0⟩
    by_cases h3 : i ≤ 3
    · simp only [h3, if_true]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · have : i = 4 ∨ i = 5 := by omega
      rcases this with rfl | rfl
      · simp
      · simp
private theorem eventually_Cs_nonneg : EventuallyInParameters fun T => 0 ≤ T.Cs := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun blk _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs hCs E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ =>
      ⟨0, fun y₁ _ => hCs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem minimizerExpansion_normBounded (hTop : topFamilyNormStatement) (T : ColdStepAtMirrorFrames.StepParameters)
    (ℓ : TorusLumps.StepParameters) (hm : T.Compatible ℓ) (hfits : ℓ.Admissible) (hσ : 0 < T.σ)
    (t : ℕ) (f : LocalFamily) (ε ε₃ : ℝ) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε₃) (m : ℕ)
    (hw : ∀ s : ℕ, torusDecayFactor T.L T.decayRate s = ℓ.weight s)
    (hden : IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) (minimizerExpansion T.a T.chainParams.ρA f))
    (htr : ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ExpansionTransportBounds true T.a T.chainParams.ρA T.ballRadius T.decayRate ε ε₃ T.L T.blockIndex m f V ∧
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
        IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        ExpansionLocalAboveFrame true T.a T.chainParams.ρA T.decayRate ε T.L m f V V' Y Y' r)
    (hρ : 0 < T.ballRadius) :
    IsNormBoundedFamily ℓ (2⁻¹ ^ 4 * ε) (2⁻¹ ^ 6 * ε₃)
      (densityOfTopFamily T.L t (minimizerExpansion T.a T.chainParams.ρA f)) := by
  have hdecay : DerivDecay T.L t T.n₀ (5 / 4 * T.σ) (minimizerExpansion T.a T.chainParams.ρA f)
      (fun k s => (if k = 3 then 2⁻¹ ^ 6 * ε₃ else 2⁻¹ ^ 6 * ε) / torusDecayFactor T.L T.decayRate s) := by
    intro F hF Y V k c X hV h1 h3 hX
    have H := (htr F V hF hV).1
    by_cases hk : k = 3
    · subst hk
      have h := H.thirdDeriv Y 0 c X (fun b => by simpa using hρ) hX
      rw [cellCentredExpansion_eq_minimizerExpansion] at h
      simpa using h
    · have h := H.lowDeriv Y k c X h1 (by omega) hX
      rw [cellCentredExpansion_eq_minimizerExpansion] at h
      simpa [hk] using h
  have hcmp : IsLocalOnTori T.L t T.n₀ (5 / 4 * T.σ) (centredFamily (minimizerExpansion T.a T.chainParams.ρA f))
      (fun r => 2 * (2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r)) := by
    intro F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb hX
    have hpos := torusDecayFactor_pos T.L T.decayRate r
    have hb0 : 0 ≤ 2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r := by positivity
    have hloc := (htr F V hF hV).2 F' V' Y Y' r hF' hV' hA
    rcases k with _ | k
    · have hflat : AgreeOnBall (finiteCells F) (ColdStepAtMirrorFrames.uniformField F F.top) (finiteCells F')
          (ColdStepAtMirrorFrames.uniformField F' F'.top) Y Y' r :=
        ⟨hA.1, hA.2.1, hA.2.2.1, fun _ _ => rfl⟩
      have hc5 : 0 < 5 / 4 * T.σ := by positivity
      have hloc' := (htr F _ hF (isSmallCurvature_uniformField hc5)).2 F' _ Y Y' r hF'
        (isSmallCurvature_uniformField hc5) hflat
      have a₁ := hloc 0 h X hk hb hX
      have a₂ := hloc' 0 h X hk hb hX
      simp only [cellCentredExpansion_eq_minimizerExpansion, bondDeriv_zero] at a₁ a₂ ⊢
      simp only [centredFamily]
      rw [abs_le] at a₁ a₂ ⊢
      constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]
    · have e₁ : bondDeriv (centredFamily (minimizerExpansion T.a T.chainParams.ρA f) F Y) V (bondsAt Y h) X =
          bondDeriv (minimizerExpansion T.a T.chainParams.ρA f F Y) V (bondsAt Y h) X := bondDeriv_sub_const _ _ _ _ _
      have e₂ : bondDeriv (centredFamily (minimizerExpansion T.a T.chainParams.ρA f) F' Y') V' (bondsAt Y' h) X =
          bondDeriv (minimizerExpansion T.a T.chainParams.ρA f F' Y') V' (bondsAt Y' h) X := bondDeriv_sub_const _ _ _ _ _
      have a₁ := hloc (k + 1) h X hk hb hX
      rw [cellCentredExpansion_eq_minimizerExpansion, cellCentredExpansion_eq_minimizerExpansion] at a₁
      rw [e₁, e₂]
      linarith
  have hg := (hTop ℓ hfits).1 t (5 / 4 * T.σ) (5 / 4 * T.σ) (2⁻¹ ^ 4 * ε) (2⁻¹ ^ 6 * ε₃)
    (minimizerExpansion T.a T.chainParams.ρA f)
    (fun k s => (if k = 3 then 2⁻¹ ^ 6 * ε₃ else 2⁻¹ ^ 6 * ε) / torusDecayFactor T.L T.decayRate s)
    (fun r => 2 * (2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r))
  rw [hm.side_eq, hm.n₀_eq] at hg
  have hs : ℓ.threshold ≤ 5 / 4 * T.σ := by
    rw [hm.threshold_eq]
    linarith
  refine hg hs hs hden hdecay hcmp ?_ ?_
  · intro k s _ _
    rw [hw]
    apply div_le_div_of_nonneg_right _ (weight_pos _ _).le
    split_ifs
    · exact le_rfl
    · have : (2 : ℝ)⁻¹ ^ 6 ≤ 2⁻¹ ^ 4 := by norm_num
      exact mul_le_mul_of_nonneg_right this hε
  · intro s
    rw [hw]
    apply le_of_eq
    ring
private theorem stepDensity_normBounded (T : ColdStepAtMirrorFrames.StepParameters) (ℓ : TorusLumps.StepParameters)
    (hfits : ℓ.Admissible) (hCs : 0 ≤ T.Cs) (hκ : 0 < T.κ) (G C : ℝ) (t : ℕ)
    (hcap : ∀ m : ℕ, Real.exp (-(T.κ / 2 ^ 9 * m)) ≤ G / ℓ.weight m) (hΓ : StepDensityBounds T ℓ C t) :
    IsNormBoundedFamily ℓ (2 * (T.Cs * G)) (2 * (T.Cs * G)) (T.stepDensity t) := by
  have hG0 : ∀ m : ℕ, 0 ≤ G / ℓ.weight m := fun m => (Real.exp_pos _).le.trans (hcap m)
  have hcs : ∀ m : ℕ, T.Cs * Real.exp (-(T.κ / 2 ^ 9 * m)) ≤ 2 * (T.Cs * G) / ℓ.weight m := by
    intro m
    have h1 := mul_le_mul_of_nonneg_left (hcap m) hCs
    have h2 : 2 * (T.Cs * G) / ℓ.weight m = 2 * (T.Cs * (G / ℓ.weight m)) := by ring
    have h3 := mul_nonneg hCs (hG0 m)
    rw [h2]
    linarith
  refine ⟨hΓ.admissible, ?_, ?_⟩
  · intro n _ hn y W hW k c X h1 h3 hX
    refine (hΓ.decay n hn y W hW k c X h1 h3 hX).trans ?_
    have he : Real.exp (-(T.κ / 2 ^ 6 * (supportDiam y c : ℕ))) ≤
        Real.exp (-(T.κ / 2 ^ 9 * (supportDiam y c : ℕ))) := by
      apply Real.exp_le_exp.mpr
      have h0 : (0 : ℝ) ≤ ((supportDiam y c : ℕ) : ℝ) := Nat.cast_nonneg _
      have := mul_nonneg hκ.le h0
      nlinarith
    have := (mul_le_mul_of_nonneg_left he hCs).trans (hcs _)
    simpa using this
  · have hc := localComparison_centeredFamily hfits.σ_pos hΓ.comparison
    intro n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
    refine (hc n n' hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX).trans ?_
    have h3 := mul_le_mul_of_nonneg_left (hcap m) hCs
    have h4 : 2 * (T.Cs * G) / ℓ.weight m = 2 * (T.Cs * (G / ℓ.weight m)) := by ring
    show 2 * (T.Cs * Real.exp (-(T.κ / 2 ^ 9 * (m : ℝ)))) ≤ 2 * (T.Cs * G) / ℓ.weight m
    rw [h4]
    linarith
private theorem normBounded_of_curvatureFamily (ℓ : TorusLumps.StepParameters) (C : ℝ) (h : LocalDensity)
    (hc : IsCurvatureFamily ℓ C h) : IsNormBoundedFamily ℓ C C h := by apply _root_.YangMills.SharedProofs.p9598 <;> assumption
private theorem size_margin {E E₃ Cs G Na B₀ b : ℝ} (hE : 0 ≤ E) (hE₃ : E ≤ E₃) (hG : 0 ≤ G) (hNa : 0 ≤ Na)
    (hB₀ : 0 ≤ B₀) (hb : |b| ≤ B₀) (hroom : 4 * (G * (2 * Cs + B₀ * Na) + B₀) ≤ E) :
    2 * (Cs * G) + 2⁻¹ ^ 4 * (E / 2) + |-b| * (G * Na) ≤ E / 2 ∧
      2 * (Cs * G) + 2⁻¹ ^ 6 * (E₃ / 2) + |-b| * (G * Na) ≤ E₃ / 2 := by
  rw [abs_neg]
  have h1 : |b| * (G * Na) ≤ B₀ * (G * Na) := mul_le_mul_of_nonneg_right hb (mul_nonneg hG hNa)
  have h2 : G * (2 * Cs + B₀ * Na) = 2 * (Cs * G) + B₀ * (G * Na) := by ring
  rw [h2] at hroom
  constructor <;> norm_num <;> linarith
private theorem abs_add_add_neg_mul_le {a r s β A Bq Q e lg bb w : ℝ} (hw : 0 < w) (ha : |a| ≤ A / w)
    (hr : |r| ≤ (1 / 4 * e + Q * lg) / w) (hs : |β| * |s| ≤ Bq / w) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hBq : 0 ≤ Bq)
    (hbb : 0 ≤ bb) (hlg : lg ≤ bb) :
    |a + r + -β * s| ≤ (e / 4 + (Q + A + Bq) * (1 + bb)) / w := by
  have h1 : |a + r + -β * s| ≤ |a| + |r| + |β| * |s| := by
    refine (abs_add_le _ _).trans ?_
    have := abs_add_le a r
    rw [abs_mul, abs_neg]
    linarith
  refine h1.trans ?_
  have h2 : |a| + |r| + |β| * |s| ≤ A / w + (1 / 4 * e + Q * lg) / w + Bq / w := by linarith
  refine h2.trans ?_
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ hw.le
  have e1 := mul_le_mul_of_nonneg_left hlg hQ
  have e2 := mul_nonneg hA hbb
  have e3 := mul_nonneg hBq hbb
  nlinarith
private theorem next_level_at (hTilt : vanishingFormLocalFamilyStatement) (hTop : topFamilyNormStatement)
    (hS : normBoundedFamilyClosureStatement) (hNu : curvatureValueLinearityStatement)
    (hOne : InvariantFamilyCurvatureForm) (hFin : PotentialSumsFinite) (hBelow : ReferenceBoundsBelow)
    (hDens : expansionAtFrameIsLocalDensityStatement) (T : ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered)
    (hCs : 0 ≤ T.Cs) (hTr : ∀ ε : ℝ, 0 < ε → TransportAtScale T ε) (hFl : FlatLimitOfFamilyAt T)
    (Cx : ℝ) (Ckx : ℕ → ℝ) (hCkx : ∀ k, 0 < Ckx k) (hX6 : TransportBoundsAt T Cx Ckx)
    (hRow : expansionTransportAt T) (hFr : FrameBoundsForParameters T) (Cg : ℝ)
    (hG : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t, StepDensityBounds T ℓ Cg t)
    (hGc : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t,
      SumInvariantUnderIsometries ℓ (T.stepDensity t))
    (hGn : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t : ℕ,
      HasCurvatureForm (T.stepDensity t) (T.oneLoopCoeff t) ∧ |T.oneLoopCoeff t| ≤ baseConstant T.Cs T.κ)
    (hSh : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t, ShareBounds T ℓ t)
    (hAn : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ (t : ℕ) (f : LocalDensity),
      (∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
        ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
          AnalyticAt ℝ (fun τ : Fin k → ℝ => f n y (perturb c X τ W)) 0) →
      ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
        ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
          AnalyticAt ℝ (fun τ : Fin k → ℝ => familyAtMinimizer T.a T.ρA T.L t f n y (perturb c X τ W)) 0)
    (hCa : ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ (t : ℕ) (f : LocalDensity),
      IsAdmissibleDensity ℓ f → SumInvariantUnderIsometries ℓ f →
        SumInvariantUnderIsometries ℓ (familyAtMinimizer T.a T.ρA T.L t f))
    (hroom : T.AdmitsReference) :
    ∃ Ck : ℕ → ℝ, (∀ k, 0 ≤ Ck k) ∧
      ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ (t : ℕ) (Eh : ℕ → ℝ), (∀ k, 0 ≤ Eh k) →
        ReferenceBoundsAtLevel T ℓ Eh t →
        HasCurvatureForm (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) 0 ∧
        ReferenceBoundsAtLevel T ℓ (fun k => Eh k / 4 + Ck k * (1 + maxLowerOrderBounds T.energyRatio Eh k)) (t + 1) := by
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  have hη := hT.η₃_pos
  have hE1 : (1 : ℝ) ≤ T.E := hT.one_le_E
  have hE0 : 0 < T.E := by linarith
  have hE₃E : T.E ≤ T.energyRatio := by
    unfold ColdStepAtMirrorFrames.StepParameters.energyRatio
    rw [le_div_iff₀ hη]
    nlinarith [hT.η₃_le_one]
  have hE₃0 : 0 < T.energyRatio := by linarith
  have hρ : 0 < T.ballRadius := by
    unfold ColdStepAtMirrorFrames.StepParameters.ballRadius
    positivity
  have hLpos : (0 : ℝ) < T.L := by exact_mod_cast hT.odd_L.pos
  obtain ⟨G, hGdef⟩ : ∃ G, G = weightGrowthSup T.κ ((T.L : ℝ) ^ (1 / 640 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B, B = baseConstant T.Cs T.κ := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, hsB, -, hG1⟩ := hFin T.κ ((T.L : ℝ) ^ (1 / 640 : ℝ)) hκ (Real.rpow_pos_of_pos hLpos _)
  rw [← hGdef] at hG1
  have hG0 : 0 ≤ G := by linarith
  have hB₀0 : 0 ≤ B₀ := by
    have h1 := mul_nonneg hCs hsB
    rw [hB₀]
    unfold baseConstant
    linarith
  have hN : ∀ k, 0 < T.chainParams.N k := hT.chain_admissible.positivity.2.2.2.2.2.1
  have hNa : 0 ≤ maxOfFirstFour T.chainParams.N :=
    (hN 0).le.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hroom₁ : 4 * (G * (2 * T.Cs + B₀ * maxOfFirstFour T.chainParams.N) + B₀) ≤ T.E := by
    have h := hroom.1
    unfold expansionConstant at h
    rw [← hB₀, ← hGdef] at h
    exact h
  refine ⟨fun k => Ckx k + |Cg| * G + B₀ * (G * T.chainParams.N k), fun k =>
    add_nonneg (add_nonneg (hCkx k).le (mul_nonneg (abs_nonneg _) hG0))
      (mul_nonneg hB₀0 (mul_nonneg hG0 (hN k).le)), ?_⟩
  intro ℓ hm hfits t Eh hEh R
  have hnL : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) := by rw [hm.n₁_eq, hm.side_eq]
  have hrate : ℓ.weightRate = T.decayRate := by
    unfold TorusLumps.StepParameters.weightRate ColdStepAtMirrorFrames.StepParameters.decayRate
    rw [hm.rt_eq]
  have hw : ∀ s : ℕ, torusDecayFactor T.L T.decayRate s = ℓ.weight s := by
    intro s
    unfold torusDecayFactor TorusLumps.StepParameters.weight
    rw [hnL, hm.side_eq, hrate]
  have eG : weightGrowthSup ℓ.rt ℓ.n₁ = G := by rw [hm.rt_eq, hm.n₁_eq, hGdef]
  have hcap : ∀ m : ℕ, Real.exp (-(T.κ / 2 ^ 9 * m)) ≤ G / ℓ.weight m := by
    intro m
    have h := (hTop ℓ hfits).2.2 m
    rwa [eG, hm.rt_eq] at h
  have hε : 0 < T.E / 2 := by positivity
  have hE3h : T.E / 2 / T.η₃ = T.energyRatio / 2 := by
    unfold ColdStepAtMirrorFrames.StepParameters.energyRatio
    ring
  have hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate (T.E / 2) (T.energyRatio / 2) (T.localReference t) := by
    have h1 := hTilt ℓ t _ _ _ hfits hnL R.family R.vanishing_curvatureForm
    rw [hm.side_eq, hm.n₀_eq, hm.threshold_eq, hrate] at h1
    exact h1
  have hrow' : IsRegularFamily T.L t T.n₀ T.σ T.decayRate (T.E / 2) (T.E / 2 / T.η₃) (T.localReference t) := by
    rw [hE3h]
    exact hrow
  have hrowE : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio (T.localReference t) :=
    isRegularFamily_mono hrow (by linarith) (by linarith)
  have hden : IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) (minimizerExpansion T.a T.chainParams.ρA (T.localReference t)) := by
    have h64 : 64 ≤ T.n₀ := by
      have h := hfits.n₀_ge
      rw [hm.n₀_eq] at h
      omega
    have hfs : ∀ (t : ℕ) (x : ℝ) (F : BlockFrame) (V : F.GaugeField F.top) (star : Bool), T.coupling ≤ x →
        IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → ∃ C : ℝ,
          FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk
            (frameRadius x) V := by
      obtain ⟨Cf, C, -, -, -, -, -, -, -, -, -, -, -, -, -, H⟩ := hFr
      exact fun t x F V star hx hF hV => ⟨C, (H t x F V hx hF hV).2.1 star⟩
    have h := hDens T hT h64 hRow hfs t T.coupling _ true le_rfl hrowE
    rw [expansionAtFrameFamily_eq] at h
    exact h
  have hRfam : IsNormBoundedFamily ℓ (2⁻¹ ^ 4 * (T.E / 2)) (2⁻¹ ^ 6 * (T.energyRatio / 2))
      (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) := by
    have h := minimizerExpansion_normBounded hTop T ℓ hm hfits hσ t (T.localReference t) (T.E / 2) (T.energyRatio / 2)
      hε.le (by linarith) (frameRadius T.coupling) hw hden (fun F V hF hV => by
        have h := hTr _ hε t T.coupling _ F V le_rfl hrow' hF hV true
        rw [hE3h] at h
        exact h) hρ
    exact h
  have hΓ := hG ℓ hm hfits t
  have hΓfam := stepDensity_normBounded T ℓ hfits hCs hκ G Cg t hcap hΓ
  have hSb := hSh ℓ hm hfits t
  have hSfam := normBounded_of_curvatureFamily ℓ _ _ hSb.family
  rw [eG] at hSfam
  obtain ⟨hGform, hbB⟩ := hGn ℓ hm hfits t
  rw [← hB₀] at hbB
  have hsum₁ := (hS ℓ).2.1 _ _ _ _ _ _ hΓfam hRfam
  have hsum₂ := (hS ℓ).2.2.1 (-T.oneLoopCoeff t) _ _ _ hSfam
  have hsum := (hS ℓ).2.1 _ _ _ _ _ _ hsum₁ hsum₂
  have hstep : T.referenceDensity (t + 1) = T.stepDensity t + familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t) +
      (-T.oneLoopCoeff t) • levelShareFamily T.a T.L (t + 1) := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  obtain ⟨hb₁, hb₂⟩ := size_margin hE0.le hE₃E hG0 hNa hB₀0 hbB hroom₁
  have hfam : IsNormBoundedFamily ℓ (T.E / 2) (T.energyRatio / 2) (T.referenceDensity (t + 1)) := by
    rw [hstep]
    exact (hS ℓ).1 _ _ _ _ _ hb₁ hb₂ hsum
  have hcarR : SumInvariantUnderIsometries ℓ (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) :=
    hCa ℓ hm hfits t _ R.family.admissible R.isometries
  have hread : HasCurvatureForm (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) 0 := by
    have hflat := (hFl t T.coupling (T.E / 2) (T.localReference t) le_rfl hε hrow').1
    rw [expansionAtFrameFamily_eq] at hflat
    have h2 := (hTop ℓ hfits).2.1 t (minimizerExpansion T.a T.chainParams.ρA (T.localReference t)) 0
    rw [hm.side_eq] at h2
    obtain ⟨v, hv, hv0⟩ := h2 hflat
    have hv' : v = 0 := abs_nonpos_iff.mp hv0
    rw [hv'] at hv
    exact hasCurvatureForm_zero hOne hfits (isCurvatureFamily_of_normBounded hRfam) hcarR hv.2
  have hno : HasVanishingCurvatureForm (T.referenceDensity (t + 1)) := by
    have h1 := (hNu ℓ hfits).2.2.1 _ _ _ _ hΓ.admissible hRfam.admissible hGform hread
    have h2 := (hNu ℓ hfits).2.2.2 (-T.oneLoopCoeff t) _ _ hSfam.admissible hSb.form
    have h3 := (hNu ℓ hfits).2.2.1 _ _ _ _ hsum₁.admissible hsum₂.admissible h1 h2
    have e : T.oneLoopCoeff t + 0 + -T.oneLoopCoeff t * 1 = 0 := by ring
    rw [e] at h3
    rw [hstep]
    exact h3
  have hAnR := hAn ℓ hm hfits t (T.referenceDensity t) R.analytic
  have hfun : ∀ (n : ℕ) (y : TorusSite n), T.referenceDensity (t + 1) n y = fun V => T.stepDensity t n y V +
      familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t) n y V +
      (-T.oneLoopCoeff t) * levelShareFamily T.a T.L (t + 1) n y V := by
    intro n y
    rw [hstep]
    rfl
  refine ⟨hread, hfam, hno, ?_, ?_, ?_⟩
  · intro n _ hn y W hW k c X
    rw [hfun]
    exact ((hΓ.analytic n hn y W hW k c X).add (hAnR n hn y W hW k c X)).add
      (analyticAt_const.mul (hSb.analytic n hn y W hW k c X))
  · rw [hstep]
    exact sumInvariant_add (sumInvariant_add (hGc ℓ hm hfits t) hcarR) (sumInvariant_smul _ hSb.invariant)
  · intro n _ hn y W hW k c X h4 h6 hXu
    have hWc : IsCold (5 / 4 * T.σ) W := isCold_mono (by linarith) hW
    have hder := hBelow T ℓ Eh t hT hm hfits R
    have hderk : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k
        (fun j => if j ≤ 3 then T.energyRatio else Eh j) (T.localReference t) :=
      ⟨fun F hF y W hW j c X => (hder.2.smooth F hF y W hW j c X).of_le (by exact_mod_cast h6),
        hder.2.gauge_invariant,
        fun F hF y W j c X hW h1 hj hX => hder.2.decay F hF y W j c X hW h1 (by omega) hX⟩
    have he : ∀ j, 0 ≤ (fun j => if j ≤ 3 then T.energyRatio else Eh j) j := by
      intro j
      show 0 ≤ if j ≤ 3 then T.energyRatio else Eh j
      split_ifs
      · exact hE₃0.le
      · exact hEh j
    have hIs := hX6 T.coupling t k _ (T.localReference t) (torusFrame T.L t n)
      (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) 0 0 le_rfl (by omega) h6 he hderk
      (isCubicTopTorus_torusFrame hn) (isSmallCurvature_readAtLevel hWc) le_rfl zero_le_one
      (fun b => by simpa using hρ.le)
    have hbd := hIs.blockDeriv_le (torusSiteInFrame (torusFrame T.L t n) (torusFrame T.L t n).top y)
      (frameBonds T.L t c) X hXu
    rw [interpolatedBlockExpansion_zero, bondSpan_frameBonds, hw] at hbd
    have e₁ : mixedDeriv (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t) n y) W c X =
        bondDeriv (minimizerExpansion T.a T.chainParams.ρA (T.localReference t) (torusFrame T.L t n)
          (torusSiteInFrame (torusFrame T.L t n) (torusFrame T.L t n).top y))
          (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) (frameBonds T.L t c) X :=
      mixedDeriv_readAtLevel (minimizerExpansion T.a T.chainParams.ρA (T.localReference t) (torusFrame T.L t n)
        (torusSiteInFrame (torusFrame T.L t n) (torusFrame T.L t n).top y)) W c X
    rw [← e₁] at hbd
    have ek : (if k ≤ 3 then T.energyRatio else Eh k) = Eh k := if_neg (by omega)
    simp only [ek] at hbd
    obtain ⟨hlg, hbb⟩ := runningMax_le_maxLowerOrderBounds hE₃0.le hEh h4 h6
    have hwp := weight_pos ℓ (supportDiam y c)
    rw [hfun, mixedDeriv_add_add_smul (-T.oneLoopCoeff t) (hΓ.analytic n hn y W hW k c X).contDiffAt
      (hAnR n hn y W hW k c X).contDiffAt (hSb.analytic n hn y W hW k c X).contDiffAt]
    have hga : |mixedDeriv (T.stepDensity t n y) W c X| ≤ |Cg| * G / ℓ.weight (supportDiam y c) := by
      refine (hΓ.higherDeriv_le n hn y W hW k c X h4 h6 hXu).trans ?_
      have h0 : (0 : ℝ) ≤ ((supportDiam y c : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : Real.exp (-(2 ^ 6 * T.κ * (supportDiam y c : ℕ))) ≤
          Real.exp (-(T.κ / 2 ^ 9 * (supportDiam y c : ℕ))) := by
        apply Real.exp_le_exp.mpr
        have := mul_nonneg hκ.le h0
        nlinarith
      have h2 := h1.trans (hcap _)
      have h3 : Cg * Real.exp (-(2 ^ 6 * T.κ * (supportDiam y c : ℕ))) ≤
          |Cg| * Real.exp (-(2 ^ 6 * T.κ * (supportDiam y c : ℕ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      have h4' := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cg)
      rw [mul_div_assoc]
      exact h3.trans h4'
    have hsh : |T.oneLoopCoeff t| * |mixedDeriv (levelShareFamily T.a T.L (t + 1) n y) W c X| ≤
        B₀ * (G * T.chainParams.N k) / ℓ.weight (supportDiam y c) := by
      have h1 := hSb.higherDeriv_le n hn y W hW k c X h4 h6 hXu
      rw [eG] at h1
      rw [mul_div_assoc]
      exact mul_le_mul hbB h1 (abs_nonneg _) hB₀0
    exact abs_add_add_neg_mul_le hwp hga hbd hsh (hCkx k).le (mul_nonneg (abs_nonneg _) hG0)
      (mul_nonneg hB₀0 (mul_nonneg hG0 (hN k).le)) hbb hlg
end NextLevel
open NextLevel in
theorem referenceNextLevel
    (hT : TransportAtEveryScale) (hF : flatLimitOfFamilyStatement) (hX : transportBoundsStatement)
    (hRow : expansionTransportStatement) (hFr : FrameBoundsEventually) (hDens : expansionAtFrameIsLocalDensityStatement)
    (hG : StepDensityIsSmooth) (hGc : StepDensitySumInvariant)
    (hGn : oneLoopCoeffBound) (hSh : SharesBoundedAlongParameters)
    (hAn : FamilyAtMinimizerAnalytic) (hCa : FamilyAtMinimizerInvariant)
    (hBelow : ReferenceBoundsBelow) (hTilt : vanishingFormLocalFamilyStatement)
    (hTop : topFamilyNormStatement) (hS : normBoundedFamilyClosureStatement) (hNu : curvatureValueLinearityStatement)
    (hOne : InvariantFamilyCurvatureForm) (hFin : PotentialSumsFinite) :
    referenceNextLevelStatement := by
  obtain ⟨Cx, Ckx, -, hCkx, gX⟩ := hX
  have J := EventuallyInParameters.and hT (EventuallyInParameters.and hF (EventuallyInParameters.and gX
    (EventuallyInParameters.and hRow (EventuallyInParameters.and hFr eventually_Cs_nonneg))))
  have D := EventuallyOrdered.and hG (EventuallyOrdered.and hGc (EventuallyOrdered.and hGn
    (EventuallyOrdered.and hSh (EventuallyOrdered.and hAn hCa))))
  unfold referenceNextLevelStatement EventuallyOrdered
  refine EventuallyInParameters.mono (EventuallyInParameters.and J D) ?_
  rintro T ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, d⟩ hdr hn hroom
  obtain ⟨⟨Cg, g₁⟩, g₂, g₃, g₄, g₅, g₆⟩ := d hdr hn
  exact next_level_at hTilt hTop hS hNu hOne hFin hBelow hDens T hdr a₆ a₁ a₂ _ _ (hCkx _) a₃ a₄ a₅ Cg
    g₁ g₂ g₃ g₄ g₅ g₆ hroom
end StepDensities
end YangMills.Construction
end
