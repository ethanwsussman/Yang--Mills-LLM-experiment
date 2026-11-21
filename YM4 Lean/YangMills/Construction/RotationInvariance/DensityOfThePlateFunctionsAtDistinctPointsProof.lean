import YangMills.Construction.TwoPoints.TranslatePairingIsAnalyticNearAPointProof
import YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts
import YangMills.Construction.Continuum.FromSmallSupportsToAllSupports
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.RotationInvariance.AnalyticityAlongTangentialMoves
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPoints
import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.PlaneDataAreDataOfTheTwoSettings
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import Mathlib
set_option autoImplicit false
open Complex (I)
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube MeasureTheory
open YangMills.Construction.Coordinates
open Filter Topology
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.HarmonicDensity
theorem scalarEquiv_apply (x : ℂ) (j : Fin 1) : scalarEquiv x j = x := rfl
theorem exists_finProdFinEquiv_eq {p : ℕ} (k : Fin (p * 2)) :
    ∃ i : Fin p, k = finProdFinEquiv (i, 0) ∨ k = finProdFinEquiv (i, 1) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  refine ⟨i, ?_⟩
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
def realCoords {p : ℕ} (y : Fin p → RealPlane) : ComplexCoordinates (p * 2) :=
  pairTupleEquiv p (embedPlaneTuple y)
theorem realCoords_fst {p : ℕ} (y : Fin p → RealPlane) (i : Fin p) :
    realCoords y (finProdFinEquiv (i, 0)) = ((y i 0 : ℝ) : ℂ) := by
  rw [realCoords, pairTupleEquiv_apply_fst]
  rfl
theorem realCoords_snd {p : ℕ} (y : Fin p → RealPlane) (i : Fin p) :
    realCoords y (finProdFinEquiv (i, 1)) = ((y i 1 : ℝ) : ℂ) := by
  rw [realCoords, pairTupleEquiv_apply_snd]
  rfl
theorem realCoords_add {p : ℕ} (y y' : Fin p → RealPlane) :
    realCoords (y + y') = realCoords y + realCoords y' := by
  funext k
  obtain ⟨i, rfl | rfl⟩ := exists_finProdFinEquiv_eq k
  · simp [realCoords_fst]
  · simp [realCoords_snd]
theorem realCoords_smul {p : ℕ} (r : ℝ) (y : Fin p → RealPlane) :
    realCoords (r • y) = (r : ℂ) • realCoords y := by
  funext k
  obtain ⟨i, rfl | rfl⟩ := exists_finProdFinEquiv_eq k
  · simp [realCoords_fst]
  · simp [realCoords_snd]
theorem continuous_realCoords (p : ℕ) :
    Continuous (realCoords : (Fin p → RealPlane) → ComplexCoordinates (p * 2)) := by
  refine continuous_pi fun k => ?_
  obtain ⟨i, rfl | rfl⟩ := exists_finProdFinEquiv_eq k
  · simp only [realCoords_fst]
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp (continuous_apply i))
  · simp only [realCoords_snd]
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp (continuous_apply i))
theorem realCoords_mem_realLocus {p : ℕ} (y : Fin p → RealPlane) :
    realCoords y ∈ ComplexCoordinates.realLocus (p * 2) := by
  intro k
  obtain ⟨i, rfl | rfl⟩ := exists_finProdFinEquiv_eq k
  · rw [realCoords_fst]; simp
  · rw [realCoords_snd]; simp
theorem tupleRe_realCoords {p : ℕ} (y : Fin p → RealPlane) :
    tupleRe ((pairTupleEquiv p).symm (realCoords y)) = y := by
  funext i
  simp [realCoords, tupleRe, embedPlaneTuple, vecRe_embedPlane]
theorem isRealAnalyticTupleFun_sum {p : ℕ} {O : Set (Fin p → RealPlane)} {ι : Type*}
    (hO : Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus (p * 2))
      (pairTupleEquiv p '' (embedPlaneTuple '' O)))
    (s : Finset ι) (f : ι → (Fin p → RealPlane) → ℂ)
    (hf : ∀ i ∈ s, IsRealAnalyticTupleFun O (f i)) :
    IsRealAnalyticTupleFun O fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨hO, fun a _ => ⟨fun _ => 0, Eventually.of_forall fun z => ?_⟩⟩
    have h0 : scalarEquiv (0 : ℂ) = 0 := by
      funext j
      simp [scalarEquiv_apply]
    simp only [Finset.sum_empty, h0, smul_zero]
    exact hasSum_zero
  | insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self i s)
    have h₂ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨hO, fun a ha => ?_⟩
    obtain ⟨c₁, hc₁⟩ := h₁.2 a ha
    obtain ⟨c₂, hc₂⟩ := h₂.2 a ha
    refine ⟨fun m => c₁ m + c₂ m, ?_⟩
    filter_upwards [hc₁, hc₂] with z hz₁ hz₂
    have hs := hz₁.add hz₂
    simp only [← smul_add] at hs
    have hd : ∀ u v : ℂ, scalarEquiv (u + v) = scalarEquiv u + scalarEquiv v := by
      intro u v
      funext j
      simp only [Pi.add_apply, scalarEquiv_apply]
    simp only [Finset.sum_insert hi, hd]
    exact hs
theorem exists_holomorphic_extension
    (hc : ∀ (k : ℕ), 1 ≤ k → ∀ (O : Set (ComplexCoordinates k)) (f : ComplexCoordinates k → ℂ),
      ComplexCoordinates.IsRealAnalyticIn (N' := 1) O (fun z _ => f z) →
      ∀ a ∈ O, ∃ (W : Set (ComplexCoordinates k)) (h : ComplexCoordinates k → ℂ),
        IsOpen W ∧ a ∈ W ∧ W ∩ ComplexCoordinates.realLocus k ⊆ O ∧
        ComplexCoordinates.IsHolomorphicIn (N' := 1) W (fun z _ => h z) ∧
        ∀ z ∈ W ∩ ComplexCoordinates.realLocus k, h z = f z)
    (hseries : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {p : ℕ} (hp : 1 ≤ p) {O : Set (Fin p → RealPlane)} {K : (Fin p → RealPlane) → ℂ}
    (hK : IsRealAnalyticTupleFun O K) {y₀ : Fin p → RealPlane} (hy₀ : y₀ ∈ O) :
    ∃ (W : Set (ComplexCoordinates (p * 2))) (G : ComplexCoordinates (p * 2) → ℂ),
      IsOpen W ∧ realCoords y₀ ∈ W ∧ (∀ b ∈ W, DifferentiableAt ℂ G b) ∧
      ∀ y, realCoords y ∈ W → G (realCoords y) = K y := by
  let f : ComplexCoordinates (p * 2) → ℂ := fun z => K (tupleRe ((pairTupleEquiv p).symm z))
  have hscalar : (fun (z : ComplexCoordinates (p * 2)) (_ : Fin 1) => f z) =
      fun z => scalarEquiv (f z) := by
    funext z i
    rw [scalarEquiv_apply]
  have hf : ComplexCoordinates.IsRealAnalyticIn (N' := 1)
      (pairTupleEquiv p '' (embedPlaneTuple '' O)) (fun z _ => f z) := by
    rw [hscalar]
    exact hK
  obtain ⟨W, h, hWo, hyW, -, hhol, heq⟩ := hc (p * 2) (by omega) _ f hf (realCoords y₀)
    ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩
  refine ⟨W, h, hWo, hyW, fun b hb => ?_, fun y hy => ?_⟩
  · obtain ⟨L, hL⟩ := ((hseries.1 _ W hWo).1 1 _ hhol).2.2.1 b hb
    have hd : DifferentiableAt ℂ (fun (z : ComplexCoordinates (p * 2)) (_ : Fin 1) => h z) b :=
      (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt
    exact differentiableAt_pi.1 hd 0
  · rw [heq _ ⟨hy, realCoords_mem_realLocus y⟩]
    simp only [f, tupleRe_realCoords]
section
variable {n : ℕ} {α : Fin n → RealPlane → ℂ}
theorem profileIntegrand_eq (α : Fin n → RealPlane → ℂ) (f : (Fin n → RealPlane) → ℂ) :
    profileIntegrand α f = fun y => (∏ i, α i (y i)) * f y := by
  funext y
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · exact Set.indicator_of_mem hy _
  · rw [profileIntegrand, Set.indicator_of_notMem hy]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    have h0 : α i (y i) = 0 := image_eq_zero_of_notMem_tsupport hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
theorem isCompact_pi_tsupport (hα : ∀ i, α i ∈ complexProfiles) :
    IsCompact (Set.univ.pi fun i => tsupport (α i)) :=
  isCompact_univ_pi fun i => (hα i).2
theorem continuous_prod_profiles (hα : ∀ i, α i ∈ complexProfiles) :
    Continuous fun y : Fin n → RealPlane => ∏ i, α i (y i) :=
  continuous_finset_prod _ fun i _ => (hα i).1.continuous.comp (continuous_apply i)
theorem pi_tsupport_subset_injective
    (hd : Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) :
    (Set.univ.pi fun i => tsupport (α i)) ⊆ injectivePointTuples n := by
  intro y hy i j e
  by_contra hij
  exact Set.disjoint_left.1 (hd hij) (hy i (Set.mem_univ i)) (e ▸ hy j (Set.mem_univ j))
theorem integrable_profileIntegrand (hα : ∀ i, α i ∈ complexProfiles)
    {K : (Fin n → RealPlane) → ℂ}
    {O : Set (Fin n → RealPlane)} (hK : ContinuousOn K O)
    (hsub : (Set.univ.pi fun i => tsupport (α i)) ⊆ O) :
    Integrable (profileIntegrand α K) := by
  have hC := isCompact_pi_tsupport hα
  have hc : ContinuousOn (fun y => (∏ i, α i (y i)) * K y) (Set.univ.pi fun i => tsupport (α i)) :=
    (continuous_prod_profiles hα).continuousOn.mul (hK.mono hsub)
  exact (hc.integrableOn_compact hC).integrable_indicator hC.measurableSet
end
section
variable {p : ℕ}
theorem differentiableOn_setIntegral_comp
    (H : YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts) {N : ℕ}
    {W : Set (ComplexCoordinates N)} {G : ComplexCoordinates N → ℂ}
    (hGd : ∀ b ∈ W, DifferentiableAt ℂ G b) {Kb : Set (ComplexCoordinates N)} (hKb : IsCompact Kb)
    (hKW : Kb ⊆ W) {C T : Set (Fin p → RealPlane)} (hC : IsCompact C) (hTm : MeasurableSet T)
    (hTC : T ⊆ C) {w : (Fin p → RealPlane) → ℂ} (hw : Continuous w)
    {A : ℂ → (Fin p → RealPlane) → ComplexCoordinates N}
    (hA : Continuous fun q : ℂ × (Fin p → RealPlane) => A q.1 q.2)
    (hAd : ∀ y ζ, DifferentiableAt ℂ (fun ζ => A ζ y) ζ) {Ob : Set ℂ} (hObo : IsOpen Ob)
    (hAK : ∀ ζ ∈ Ob, ∀ y ∈ T, A ζ y ∈ Kb) :
    DifferentiableOn ℂ (fun ζ => ∫ y in C, T.indicator (fun y => w y * G (A ζ y)) y) Ob := by
  classical
  have hGc : ContinuousOn G W := fun b hb => (hGd b hb).continuousAt.continuousWithinAt
  obtain ⟨BG, hBG⟩ := hKb.exists_bound_of_continuousOn (hGc.mono hKW)
  obtain ⟨Bw, hBw⟩ := hC.exists_bound_of_continuousOn hw.continuousOn
  let g : ℂ → (Fin p → RealPlane) → ℂ :=
    fun ζ y => T.indicator (fun y => w y * G (A ζ y)) y
  have hbound : ∃ b : ℝ, ∀ ζ ∈ Ob, ∀ y, ‖g ζ y‖ ≤ b := by
    refine ⟨|Bw| * |BG|, fun ζ hζ y => ?_⟩
    by_cases hy : y ∈ T
    · simp only [g, Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul ((hBw y (hTC hy)).trans (le_abs_self _))
        ((hBG _ (hAK ζ hζ y hy)).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
    · simp only [g, Set.indicator_of_notMem hy, norm_zero]
      positivity
  have hmeas : Measurable (fun q : Ob × (Fin p → RealPlane) => g q.1 q.2) := by
    let T' : Set (Ob × (Fin p → RealPlane)) := Prod.snd ⁻¹' T
    have hT' : MeasurableSet T' := measurable_snd hTm
    let F₁ : Ob × (Fin p → RealPlane) → ℂ := fun q => w q.2 * G (A q.1 q.2)
    have hF₁ : ContinuousOn F₁ T' := by
      refine (hw.comp continuous_snd).continuousOn.mul ?_
      have hcomp : Continuous fun q : Ob × (Fin p → RealPlane) => A q.1 q.2 :=
        hA.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      exact hGc.comp hcomp.continuousOn fun q hq => hKW (hAK q.1 q.1.2 q.2 hq)
    have hpw := ContinuousOn.measurable_piecewise hF₁
      (continuousOn_const (c := (0 : ℂ))) hT'
    have he : (fun q : Ob × (Fin p → RealPlane) => g q.1 q.2) =
        T'.piecewise F₁ fun _ => 0 := by
      funext q
      by_cases hq : q ∈ T'
      · have hq' : q.2 ∈ T := hq
        simp only [Set.piecewise_eq_of_mem _ _ _ hq, g, Set.indicator_of_mem hq', F₁]
      · have hq' : q.2 ∉ T := hq
        simp only [Set.piecewise_eq_of_notMem _ _ _ hq, g, Set.indicator_of_notMem hq']
    rw [he]
    exact hpw
  have hdiff : ∀ y, DifferentiableOn ℂ (fun ζ => g ζ y) Ob := by
    intro y
    by_cases hy : y ∈ T
    · intro ζ hζ
      have hd : DifferentiableAt ℂ (fun ζ => w y * G (A ζ y)) ζ :=
        ((hGd _ (hKW (hAK ζ hζ y hy))).comp ζ (hAd y ζ)).const_mul _
      have he : (fun ζ => g ζ y) = fun ζ => w y * G (A ζ y) := by
        funext ζ'
        simp only [g, Set.indicator_of_mem hy]
      rw [he]
      exact hd.differentiableWithinAt
    · have he : (fun ζ => g ζ y) = fun _ => 0 := by
        funext ζ
        simp only [g, Set.indicator_of_notMem hy]
      rw [he]
      exact differentiableOn_const 0
  have : IsFiniteMeasure (volume.restrict C) := ⟨by simpa using hC.measure_lt_top⟩
  exact H.1 (Fin p → RealPlane) (volume.restrict C) Ob g hObo hbound hmeas hdiff
theorem exists_local_holomorphic_integral
    (H : YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (hseries : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hp : 1 ≤ p) {O : Set (Fin p → RealPlane)} {K : (Fin p → RealPlane) → ℂ}
    (hKa : IsRealAnalyticTupleFun O K) {C : Set (Fin p → RealPlane)} (hC : IsCompact C)
    {w : (Fin p → RealPlane) → ℂ} (hw : Continuous w) (m : Fin p → RealPlane)
    {x : Fin p → RealPlane} (rs : ℝ) (hx : x + rs • m ∈ O) :
    ∃ M : Set (Fin p → RealPlane), IsOpen M ∧ x ∈ M ∧ ∀ B, MeasurableSet B → B ⊆ M →
      ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
        ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ →
          h r = ∫ y in B ∩ C, w y * K (y + r • m) := by
  obtain ⟨W, G, hWo, hcW, hGd, hGK⟩ := exists_holomorphic_extension H.2.2 hseries hp hKa hx
  set c := realCoords (x + rs • m) with hc_def
  obtain ⟨ε, hε, hεW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hWo.mem_nhds hcW)
  have hcont₀ : Continuous fun y : Fin p → RealPlane => realCoords (y + rs • m) :=
    (continuous_realCoords p).comp (continuous_id.add continuous_const)
  let M : Set (Fin p → RealPlane) :=
    (fun y => realCoords (y + rs • m)) ⁻¹' Metric.ball c (ε / 2)
  have hMo : IsOpen M := Metric.isOpen_ball.preimage hcont₀
  have hxM : x ∈ M := Metric.mem_ball_self (half_pos hε)
  refine ⟨M, hMo, hxM, fun B hB hBM => ?_⟩
  set v := realCoords m with hv_def
  let δ₀ : ℝ := ε / 2 / (‖v‖ + 1)
  have hδ₀ : 0 < δ₀ := div_pos (half_pos hε) (by positivity)
  let A : ℂ → (Fin p → RealPlane) → ComplexCoordinates (p * 2) :=
    fun ζ y => realCoords (y + rs • m) + (ζ - rs) • v
  have hA : Continuous fun q : ℂ × (Fin p → RealPlane) => A q.1 q.2 :=
    (hcont₀.comp continuous_snd).add
      ((continuous_fst.sub continuous_const).smul continuous_const)
  have hAd : ∀ y ζ, DifferentiableAt ℂ (fun ζ => A ζ y) ζ := by
    intro y ζ
    simp only [A]
    fun_prop
  have hAmem : ∀ ζ ∈ Metric.ball (rs : ℂ) δ₀, ∀ y ∈ M, A ζ y ∈ Metric.closedBall c ε := by
    intro ζ hζ y hy
    have h₁ : dist (realCoords (y + rs • m)) c < ε / 2 := hy
    have h₂ : ‖ζ - rs‖ < δ₀ := by simpa [dist_eq_norm] using hζ
    have h₃ : ‖(ζ - rs) • v‖ ≤ ε / 2 := by
      rw [norm_smul]
      have h₄ : ‖ζ - rs‖ * ‖v‖ ≤ δ₀ * (‖v‖ + 1) := by
        apply mul_le_mul h₂.le (by linarith) (norm_nonneg _) hδ₀.le
      have h₅ : δ₀ * (‖v‖ + 1) = ε / 2 := by
        simp only [δ₀]
        field_simp
      linarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h₆ : A ζ y - c = (realCoords (y + rs • m) - c) + (ζ - rs) • v := by
      simp only [A]
      abel
    rw [h₆]
    rw [dist_eq_norm] at h₁
    linarith [norm_add_le (realCoords (y + rs • m) - c) ((ζ - rs) • v)]
  have hAreal : ∀ (r : ℝ) y, A r y = realCoords (y + r • m) := by
    intro r y
    have e : y + r • m = (y + rs • m) + (r - rs) • m := by
      rw [sub_smul]
      abel
    rw [e, realCoords_add (y + rs • m), realCoords_smul]
    simp only [A, hv_def]
    push_cast
    rfl
  have hCm : MeasurableSet C := hC.measurableSet
  have hTm : MeasurableSet (B ∩ C) := hB.inter hCm
  have hhol := differentiableOn_setIntegral_comp H hGd (isCompact_closedBall c ε) hεW hC hTm
    Set.inter_subset_right hw hA hAd (Metric.isOpen_ball (x := (rs : ℂ)) (ε := δ₀))
    fun ζ hζ y hy => hAmem ζ hζ y (hBM hy.1)
  refine ⟨δ₀, hδ₀, _, hhol, fun r hr => ?_⟩
  have hpt : ∀ y, (B ∩ C).indicator (fun y => w y * G (A r y)) y =
      (B ∩ C).indicator (fun y => w y * K (y + r • m)) y := by
    intro y
    by_cases hy : y ∈ B ∩ C
    · simp only [Set.indicator_of_mem hy]
      have hin : realCoords (y + r • m) ∈ W := by
        rw [← hAreal r y]
        exact hεW (hAmem _ hr y (hBM hy.1))
      rw [hAreal r y, hGK _ hin]
    · simp only [Set.indicator_of_notMem hy]
  simp only [hpt]
  rw [setIntegral_indicator hTm]
  congr 2
  ext y
  simp only [Set.mem_inter_iff]
  tauto
theorem exists_holomorphic_integral_shift
    (H : YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (hseries : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hp : 1 ≤ p) {O : Set (Fin p → RealPlane)} {K : (Fin p → RealPlane) → ℂ}
    (hKa : IsRealAnalyticTupleFun O K) (hKc : ContinuousOn K O)
    {C : Set (Fin p → RealPlane)} (hC : IsCompact C)
    {w : (Fin p → RealPlane) → ℂ} (hw : Continuous w) (m : Fin p → RealPlane)
    (hm : ∀ r : ℝ, ∀ y ∈ C, y + r • m ∈ O) (rs : ℝ) :
    ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
      ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ →
        h r = ∫ y in C, w y * K (y + r • m) := by
  classical
  have hCm : MeasurableSet C := hC.measurableSet
  let F : ℝ → (Fin p → RealPlane) → ℂ := fun r y => w y * K (y + r • m)
  have hint : ∀ r : ℝ, IntegrableOn (F r) C := by
    intro r
    have hcont : Continuous fun y : Fin p → RealPlane => y + r • m :=
      continuous_id.add continuous_const
    have hc : ContinuousOn (F r) C :=
      hw.continuousOn.mul (hKc.comp hcont.continuousOn fun y hy => hm r y hy)
    exact hc.integrableOn_compact hC
  let P : Set (Fin p → RealPlane) → Prop := fun A =>
    ∃ M, MeasurableSet M ∧ A ⊆ M ∧ ∀ B, MeasurableSet B → B ⊆ M →
      ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
        ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ → h r = ∫ y in B ∩ C, F r y
  have hP : P C := by
    refine hC.induction_on (p := P) ?_ ?_ ?_ ?_
    · refine ⟨∅, MeasurableSet.empty, subset_rfl, fun B _ hB => ?_⟩
      refine ⟨1, one_pos, fun _ => 0, differentiableOn_const 0, fun r _ => ?_⟩
      have : B = ∅ := Set.subset_empty_iff.1 hB
      simp [this]
    · rintro s t hst ⟨M, hM, htM, hB⟩
      exact ⟨M, hM, hst.trans htM, hB⟩
    · rintro s t ⟨M₁, hM₁, hs₁, hB₁⟩ ⟨M₂, hM₂, hs₂, hB₂⟩
      refine ⟨M₁ ∪ M₂, hM₁.union hM₂, Set.union_subset_union hs₁ hs₂, fun B hB hBM => ?_⟩
      obtain ⟨ρ₁, hρ₁, g₁, hg₁, he₁⟩ := hB₁ (B ∩ M₁) (hB.inter hM₁) Set.inter_subset_right
      obtain ⟨ρ₂, hρ₂, g₂, hg₂, he₂⟩ := hB₂ (B \ M₁) (hB.diff hM₁) (by
        intro y hy
        exact (hBM hy.1).resolve_left hy.2)
      have hb₁ : Metric.ball (rs : ℂ) (min ρ₁ ρ₂) ⊆ Metric.ball (rs : ℂ) ρ₁ :=
        Metric.ball_subset_ball (min_le_left _ _)
      have hb₂ : Metric.ball (rs : ℂ) (min ρ₁ ρ₂) ⊆ Metric.ball (rs : ℂ) ρ₂ :=
        Metric.ball_subset_ball (min_le_right _ _)
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z => g₁ z + g₂ z,
        (hg₁.mono hb₁).add (hg₂.mono hb₂), fun r hr => ?_⟩
      have hsplit : B ∩ C = (B ∩ M₁ ∩ C) ∪ (B \ M₁ ∩ C) := by
        ext y
        by_cases h : y ∈ M₁ <;> simp [h]
      have hdisj : Disjoint (B ∩ M₁ ∩ C) (B \ M₁ ∩ C) := by
        refine Set.disjoint_left.2 fun y hy hy' => ?_
        exact hy'.1.2 hy.1.2
      rw [hsplit, setIntegral_union hdisj ((hB.diff hM₁).inter hCm)
        ((hint r).mono_set Set.inter_subset_right) ((hint r).mono_set Set.inter_subset_right)]
      show g₁ (r : ℂ) + g₂ (r : ℂ) = _
      rw [he₁ r (hb₁ hr), he₂ r (hb₂ hr)]
    · intro x hx
      obtain ⟨M, hMo, hxM, hB⟩ :=
        exists_local_holomorphic_integral H hseries hp hKa hC hw m rs (hm rs x hx)
      exact ⟨M, mem_nhdsWithin_of_mem_nhds (hMo.mem_nhds hxM), M, hMo.measurableSet, subset_rfl, hB⟩
  obtain ⟨M, hM, hCM, hB⟩ := hP
  obtain ⟨ρ, hρ, h, hh, he⟩ := hB M hM subset_rfl
  refine ⟨ρ, hρ, h, hh, fun r hr => ?_⟩
  rw [he r hr, Set.inter_eq_right.2 hCM]
end
section
open YangMills.Construction.EuclideanFunctionals.TranslationRules
open YangMills.Construction.EuclideanFunctionals.TangentialAnalyticity
open YangMills.Construction.EuclideanFunctionals.MomentSymmetry
variable {n : ℕ}
theorem differentiableAt_of_holomorphicOnComplex {O : Set ℂ} {G : ℂ → ℂ}
    (hG : HolomorphicOnComplex O G) {w : ℂ} (hw : w ∈ O) : DifferentiableAt ℂ G w := by apply _root_.YangMills.Construction.TwoPoints.ShiftPairingLocallyAnalytic.differentiableAt_of_isHolomorphicVia <;> assumption
theorem embedFour_smul_unitY (r : ℝ) :
    embedFour (r • unitY) = r • PeriodicLattice.coordVec 0 := by
  funext i
  fin_cases i <;> simp [embedFour, unitY, PeriodicLattice.coordVec]
def shiftedProfiles (J : Finset (Fin n)) (α : Fin n → RealPlane → ℂ) (r : ℝ) :
    Fin n → RealPlane → ℂ :=
  fun l => if l ∈ J then translateProfile (r • unitY) (α l) else α l
theorem disjoint_supp_productFunction {α β : RealPlane → ℂ} {φ ψ : realLabels}
    (hα : α ∈ complexProfiles) (hβ : β ∈ complexProfiles) (hP : ProductFunctionsInC1c)
    (h : Disjoint (tsupport α) (tsupport β)) :
    Disjoint (supp (productFunction α φ)) (supp (productFunction β ψ)) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact Set.disjoint_left.1 h ((hP α hα φ φ.2).2 hx).1 ((hP β hβ ψ ψ.2).2 hx').1
theorem complexFamily_productFunction (hP : ProductFunctionsInC1c) (hn : 1 ≤ n)
    {α : Fin n → RealPlane → ℂ} (φ : Fin n → realLabels) (hα : ∀ i, α i ∈ complexProfiles)
    (hd : Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) :
    ComplexComponents fun i => productFunction (α i) (φ i) :=
  ⟨hn, fun i => (hP _ (hα i) _ (φ i).2).1,
    fun _ _ hij => disjoint_supp_productFunction (hα _) (hα _) hP (hd hij)⟩
theorem centeredFnFree_comp_equiv {S : ConnFamily} (hsym : PermInvariant S) {N : ℕ} (hN : N = n)
    (hn : 2 ≤ n) (ς : Fin N ≃ Fin n) (h : Fin n → R4 → ℂ) (hh : ComplexComponents h) :
    centeredFnFree S (complexTuple (h ∘ ς)) =
      centeredFnFree S (complexTuple h) := by
  subst hN
  exact hsym N hn ς h hh
theorem exists_holomorphic_shifted_products {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) (hcone : σ.ConeCondition)
    (hsym : PermInvariant S) (hslide : TangentialAnalyticity.Holds)
    (hM : MotionsOnPlaneFactor) (hP : ProductFunctionsInC1c) (hn : 2 ≤ n) (J : Finset (Fin n))
    {α : Fin n → RealPlane → ℂ} (φ : Fin n → realLabels) (hα : ∀ i, α i ∈ complexProfiles)
    {c δ : ℝ} (hδ : 0 < δ) (hdm : ∀ r : ℝ, Pairwise fun i j =>
      Disjoint (tsupport (shiftedProfiles J α r i)) (tsupport (shiftedProfiles J α r j)))
    (hmm : ∀ (r : ℝ) (i : Fin n), shiftedProfiles J α r i ∈ complexProfiles)
    {i₁ i₂ : Fin n} (hi₁ : i₁ ∉ J) (hi₂ : i₂ ∈ J)
    (hlow : ∀ l, l ∉ J → ∀ y ∈ tsupport (α l), y 0 < c - δ)
    (hhigh : ∀ l, l ∈ J → ∀ y ∈ tsupport (α l), c + δ < y 0) (rs : ℝ) :
    ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
      ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ →
        h r = centeredFnAtProducts S (shiftedProfiles J α r) φ := by
  classical
  let P : Fin n → Prop := fun l => l ∉ J
  let eI : Fin (Fintype.card {l // P l}) ≃ {l // P l} := (Fintype.equivFin _).symm
  let eJ : Fin (Fintype.card {l // ¬P l}) ≃ {l // ¬P l} := (Fintype.equivFin _).symm
  let ς : Fin (Fintype.card {l // P l} + Fintype.card {l // ¬P l}) ≃ Fin n :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eI eJ).trans (Equiv.sumCompl P))
  have hcard : Fintype.card {l // P l} + Fintype.card {l // ¬P l} = n := by
    simpa using Fintype.card_congr ς
  have hp : 1 ≤ Fintype.card {l // P l} := Fintype.card_pos_iff.2 ⟨⟨i₁, hi₁⟩⟩
  have hp' : 1 ≤ Fintype.card {l // ¬P l} := Fintype.card_pos_iff.2 ⟨⟨i₂, not_not.2 hi₂⟩⟩
  let a : Fin (Fintype.card {l // P l}) → R4 → ℂ :=
    fun k => productFunction (α (eI k).1) (φ (eI k).1)
  let b : Fin (Fintype.card {l // ¬P l}) → R4 → ℂ :=
    fun k => productFunction (α (eJ k).1) (φ (eJ k).1)
  have hdisj0 : Pairwise fun i j => Disjoint (tsupport (shiftedProfiles J α 0 i))
      (tsupport (shiftedProfiles J α 0 j)) := hdm 0
  have hzero : shiftedProfiles J α 0 = α := by
    funext l y
    by_cases hl : l ∈ J <;> simp [shiftedProfiles, hl, translateProfile]
  rw [hzero] at hdisj0
  have ha : a ∈ disjointComplexTuples _ := by
    refine ⟨fun k => (hP _ (hα _) _ (φ _).2).1, fun k k' hkk => ?_⟩
    refine disjoint_supp_productFunction (hα _) (hα _) hP (hdisj0 fun e => hkk ?_)
    exact eI.injective (Subtype.ext e)
  have hb : b ∈ disjointComplexTuples _ := by
    refine ⟨fun k => (hP _ (hα _) _ (φ _).2).1, fun k k' hkk => ?_⟩
    refine disjoint_supp_productFunction (hα _) (hα _) hP (hdisj0 fun e => hkk ?_)
    exact eJ.injective (Subtype.ext e)
  have hla : ∀ k, supp (a k) ⊆ {x | x 3 < c - δ} := by
    intro k x hx
    have h := hlow _ (eI k).2 _ ((hP _ (hα _) _ (φ _).2).2 hx).1
    simpa [planeComponent] using h
  have hhb : ∀ k, supp (b k) ⊆ {x | c + δ < x 3} := by
    intro k x hx
    have h := hhigh _ (not_not.1 (eJ k).2) _ ((hP _ (hα _) _ (φ _).2).2 hx).1
    simpa [planeComponent] using h
  let u : R4 := PeriodicLattice.coordVec 0
  have hu : u 3 = 0 := by simp [u, PeriodicLattice.coordVec]
  obtain ⟨hcat, ⟨G, hG, hGr⟩, -, -⟩ := hslide m S σ hcone 3 c δ hδ _ _ hp hp' a ha b hb hla hhb u hu
  have hval : ∀ r : ℝ, valueAlongShift S a b u r =
      centeredFnAtProducts S (shiftedProfiles J α r) φ := by
    intro r
    rw [(hcat r).2.2]
    have hent : shiftedComponents a b u r =
        (fun l => productFunction (shiftedProfiles J α r l) (φ l)) ∘ ς := by
      funext k
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · have hk : ς (Fin.castAdd _ k) = (eI k).1 := by
          simp [ς, Equiv.sumCompl]
        simp only [shiftedComponents, Fin.append_left, Function.comp_apply, hk, a]
        have : (eI k).1 ∉ J := (eI k).2
        simp only [shiftedProfiles, if_neg this]
      · have hk : ς (Fin.natAdd _ k) = (eJ k).1 := by
          simp [ς, Equiv.sumCompl]
        simp only [shiftedComponents, Fin.append_right, Function.comp_apply, hk, b]
        have hJ : (eJ k).1 ∈ J := not_not.1 (eJ k).2
        simp only [shiftedProfiles, if_pos hJ]
        have h := (hM _ (hα (eJ k).1) _ (φ (eJ k).1).2 (r • unitY) 0).1
        rw [planeShift, embedFour_smul_unitY] at h
        exact h
    rw [hent]
    exact centeredFnFree_comp_equiv hsym hcard hn ς _
      (complexFamily_productFunction hP (by omega) φ (hmm r) (hdm r))
  have hstrip : IsOpen (stripOf δ (tangentialNorm 3 u)) :=
    isOpen_lt ((continuous_abs.comp Complex.continuous_im).mul continuous_const) continuous_const
  have hrs : (rs : ℂ) ∈ stripOf δ (tangentialNorm 3 u) := by
    simp [stripOf, hδ]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hstrip _ hrs
  refine ⟨ρ, hρ, G, fun w hw =>
    (differentiableAt_of_holomorphicOnComplex hG (hball hw)).differentiableWithinAt,
    fun r _ => ?_⟩
  rw [hGr r, hval r]
end
section
open YangMills.Construction.EuclideanFunctionals.TranslationRules
variable {n : ℕ}
def discrepancy (S : ConnFamily) (K : (Fin n → RealPlane) → ℂ) (φ : Fin n → realLabels)
    (α : Fin n → RealPlane → ℂ) : ℂ :=
  centeredFnAtProducts S α φ - profileIntegral α K
def DiscrepancyVanishesNear (S : ConnFamily) (K : (Fin n → RealPlane) → ℂ)
    (φ : Fin n → realLabels) (y : Fin n → RealPlane) : Prop :=
  ∃ ρ > 0, ∀ α : Fin n → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
    (Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) →
    (∀ i, tsupport (α i) ⊆ openDiscAt (y i) ρ) → discrepancy S K φ α = 0
open Classical in
def abscissaCoincidences (y : Fin n → RealPlane) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ y p.1 1 = y p.2 1
def shiftVector (J : Finset (Fin n)) : Fin n → RealPlane :=
  fun l => if l ∈ J then unitY else 0
theorem add_smul_shiftVector_of_mem {J : Finset (Fin n)} {l : Fin n} (hl : l ∈ J)
    (y : Fin n → RealPlane) (r : ℝ) : (y + r • shiftVector J) l = y l + r • unitY := by
  simp [shiftVector, hl]
theorem add_smul_shiftVector_of_notMem {J : Finset (Fin n)} {l : Fin n} (hl : l ∉ J)
    (y : Fin n → RealPlane) (r : ℝ) : (y + r • shiftVector J) l = y l := by
  simp [shiftVector, hl]
theorem add_smul_unitY_fst (r : ℝ) (a : RealPlane) : (a + r • unitY) 0 = a 0 := by
  simp [unitY]
theorem add_smul_unitY_snd (r : ℝ) (a : RealPlane) : (a + r • unitY) 1 = a 1 + r := by
  simp [unitY]
theorem sub_smul_unitY_fst (r : ℝ) (a : RealPlane) : (a - r • unitY) 0 = a 0 := by
  simp [unitY]
theorem norm_unitY : ‖unitY‖ = 1 := by
  simp [unitY, EuclideanSpace.norm_eq, Fin.sum_univ_two]
theorem ext_of_coords {a b : RealPlane} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
theorem abs_sub_coord_le_norm (a b : RealPlane) (k : Fin 2) : |a k - b k| ≤ ‖a - b‖ := by
  simpa using PiLp.norm_apply_le (a - b) k
theorem tsupport_translateProfile (u : RealPlane) (α : RealPlane → ℂ) :
    tsupport (translateProfile u α) = (fun y => y - u) ⁻¹' tsupport α := by
  have h : translateProfile u α = α ∘ (Homeomorph.addRight (-u)) := by
    funext y
    simp [translateProfile, sub_eq_add_neg]
  rw [h, tsupport_comp_eq_preimage]
  ext y
  simp [sub_eq_add_neg]
theorem mem_tsupport_shiftedProfiles_of_mem {J : Finset (Fin n)} {α : Fin n → RealPlane → ℂ}
    {r : ℝ} {l : Fin n} (hl : l ∈ J) (x : RealPlane) :
    x ∈ tsupport (shiftedProfiles J α r l) ↔ x - r • unitY ∈ tsupport (α l) := by
  simp only [shiftedProfiles, if_pos hl, tsupport_translateProfile, Set.mem_preimage]
theorem mem_tsupport_shiftedProfiles_of_notMem {J : Finset (Fin n)} {α : Fin n → RealPlane → ℂ}
    {r : ℝ} {l : Fin n} (hl : l ∉ J) (x : RealPlane) :
    x ∈ tsupport (shiftedProfiles J α r l) ↔ x ∈ tsupport (α l) := by
  simp only [shiftedProfiles, if_neg hl]
def ShiftedProductsExtend (S : ConnFamily) (φ : Fin n → realLabels) : Prop :=
  ∀ (J : Finset (Fin n)) (α : Fin n → RealPlane → ℂ), (∀ i, α i ∈ complexProfiles) →
    ∀ c δ : ℝ, 0 < δ → (∀ r : ℝ, Pairwise fun i j =>
      Disjoint (tsupport (shiftedProfiles J α r i)) (tsupport (shiftedProfiles J α r j))) →
    (∀ (r : ℝ) (i : Fin n), shiftedProfiles J α r i ∈ complexProfiles) →
    ∀ i₁ i₂ : Fin n, i₁ ∉ J → i₂ ∈ J →
    (∀ l, l ∉ J → ∀ y ∈ tsupport (α l), y 0 < c - δ) →
    (∀ l, l ∈ J → ∀ y ∈ tsupport (α l), c + δ < y 0) → ∀ rs : ℝ,
    ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
      ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ →
        h r = centeredFnAtProducts S (shiftedProfiles J α r) φ
def ShiftedIntegralsExtend (K : (Fin n → RealPlane) → ℂ) : Prop :=
  ∀ C : Set (Fin n → RealPlane), IsCompact C → ∀ w : (Fin n → RealPlane) → ℂ,
    Continuous w → ∀ v : Fin n → RealPlane,
    (∀ r : ℝ, ∀ y ∈ C, y + r • v ∈ injectivePointTuples n) → ∀ rs : ℝ,
    ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (rs : ℂ) ρ) ∧
      ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (rs : ℂ) ρ → h r = ∫ y in C, w y * K (y + r • v)
theorem discrepancyVanishesNear_of_injective {S : ConnFamily} {K : (Fin n → RealPlane) → ℂ}
    {φ : Fin n → realLabels}
    (hb : ∀ ψ : ℝ → ℂ,
      (∀ r₀ : ℝ, ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (r₀ : ℂ) ρ) ∧
        ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ρ → h r = ψ r) →
      (∃ a b : ℝ, a < b ∧ ∀ r ∈ Set.Ioo a b, ψ r = 0) → ∀ r, ψ r = 0)
    (hM : MotionsOnPlaneFactor)
    (hord : ∀ y : Fin n → RealPlane, Function.Injective (fun i => y i 1) →
      DiscrepancyVanishesNear S K φ y)
    (h1 : ShiftedProductsExtend S φ) (h2 : ShiftedIntegralsExtend K) :
    ∀ y ∈ injectivePointTuples n, DiscrepancyVanishesNear S K φ y := by
  classical
  have main : ∀ k : ℕ, ∀ y : Fin n → RealPlane, (abscissaCoincidences y).card = k →
      y ∈ injectivePointTuples n → DiscrepancyVanishesNear S K φ y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hk hy
    by_cases ht : Function.Injective fun i => y i 1
    · exact hord y ht
    obtain ⟨a, b, hab1, hab⟩ := Function.not_injective_iff.1 ht
    have hab1' : y a 1 = y b 1 := hab1
    have hne0 : y a 0 ≠ y b 0 := fun h0 => hab (hy (ext_of_coords h0 hab1'))
    obtain ⟨i, i', hlt, hii⟩ : ∃ i i', y i 0 < y i' 0 ∧ y i 1 = y i' 1 := by
      rcases lt_or_gt_of_ne hne0 with h | h
      · exact ⟨a, b, h, hab1'⟩
      · exact ⟨b, a, h, hab1'.symm⟩
    have hii' : i ≠ i' := fun e => by
      rw [e] at hlt
      exact lt_irrefl _ hlt
    let tp : ℝ := y i' 0
    let J : Finset (Fin n) := Finset.univ.filter fun l => tp ≤ y l 0
    have hJ : ∀ l, l ∈ J ↔ tp ≤ y l 0 := fun l => by simp [J]
    have hiJ : i ∉ J := fun h => absurd ((hJ i).1 h) (not_le.2 hlt)
    have hi'J : i' ∈ J := (hJ i').2 le_rfl
    obtain ⟨l₀, hl₀, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun l => y l 0 < tp)
      (fun l => y l 0) ⟨i, by simpa using hlt⟩
    let tm : ℝ := y l₀ 0
    have htm : tm < tp := by simpa using hl₀
    have hlowy : ∀ l, l ∉ J → y l 0 ≤ tm := fun l hl =>
      hmax l (by simpa using not_le.1 fun h => hl ((hJ l).2 h))
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, ∀ l l' : Fin n, r₀ ≠ y l 1 - y l' 1 := by
      obtain ⟨r₀, h⟩ := (Set.finite_range fun p : Fin n × Fin n =>
        y p.1 1 - y p.2 1).infinite_compl.nonempty
      exact ⟨r₀, fun l l' e => h ⟨(l, l'), e.symm⟩⟩
    let mv : Fin n → RealPlane := shiftVector J
    have hnew : y + r₀ • mv ∈ injectivePointTuples n := by
      intro a b e
      by_cases ha : a ∈ J <;> by_cases hb' : b ∈ J
      · rw [add_smul_shiftVector_of_mem ha, add_smul_shiftVector_of_mem hb'] at e
        exact hy (add_right_cancel e)
      · rw [add_smul_shiftVector_of_mem ha, add_smul_shiftVector_of_notMem hb'] at e
        have h0 := congrArg (fun v : RealPlane => v 0) e
        simp only [add_smul_unitY_fst] at h0
        have := (hJ a).1 ha
        have := hlowy b hb'
        linarith
      · rw [add_smul_shiftVector_of_notMem ha, add_smul_shiftVector_of_mem hb'] at e
        have h0 := congrArg (fun v : RealPlane => v 0) e
        simp only [add_smul_unitY_fst] at h0
        have := (hJ b).1 hb'
        have := hlowy a ha
        linarith
      · rw [add_smul_shiftVector_of_notMem ha, add_smul_shiftVector_of_notMem hb'] at e
        exact hy e
    have hcard : (abscissaCoincidences (y + r₀ • mv)).card < k := by
      rw [← hk]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨(i, i'), ?_, ?_⟩)
      · intro p hp
        simp only [abscissaCoincidences, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        refine ⟨hp.1, ?_⟩
        have e := hp.2
        by_cases ha : p.1 ∈ J <;> by_cases hb' : p.2 ∈ J
        · rw [add_smul_shiftVector_of_mem ha, add_smul_shiftVector_of_mem hb',
            add_smul_unitY_snd, add_smul_unitY_snd] at e
          linarith
        · rw [add_smul_shiftVector_of_mem ha, add_smul_shiftVector_of_notMem hb',
            add_smul_unitY_snd] at e
          exact absurd (by linarith) (hr₀ p.2 p.1)
        · rw [add_smul_shiftVector_of_notMem ha, add_smul_shiftVector_of_mem hb',
            add_smul_unitY_snd] at e
          exact absurd (by linarith) (hr₀ p.1 p.2)
        · rw [add_smul_shiftVector_of_notMem ha, add_smul_shiftVector_of_notMem hb'] at e
          exact e
      · simp only [abscissaCoincidences, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hii', hii⟩
      · simp only [abscissaCoincidences, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro _ e
        rw [add_smul_shiftVector_of_notMem hiJ, add_smul_shiftVector_of_mem hi'J,
          add_smul_unitY_snd] at e
        exact hr₀ i i (by linarith)
    obtain ⟨ρ₁, hρ₁, hv₁⟩ := ih _ hcard _ rfl hnew
    let gap : ℝ := tp - tm
    have hgap : 0 < gap := sub_pos.2 htm
    let ρ : ℝ := min (ρ₁ / 2) (gap / 4)
    have hρ : 0 < ρ := lt_min (half_pos hρ₁) (by positivity)
    have hρ₂ : ρ ≤ ρ₁ / 2 := min_le_left _ _
    have hρ₃ : ρ ≤ gap / 4 := min_le_right _ _
    let c : ℝ := (tm + tp) / 2
    let δ : ℝ := gap / 2 - ρ
    have hδ : 0 < δ := by
      simp only [δ]
      linarith
    have hc₁ : c - δ = tm + ρ := by
      simp only [c, δ, gap]
      ring
    have hc₂ : c + δ = tp - ρ := by
      simp only [c, δ, gap]
      ring
    refine ⟨ρ, hρ, fun α hα hd hs => ?_⟩
    have hdisc : ∀ l, ∀ x ∈ tsupport (α l), ‖x - y l‖ < ρ := fun l x hx => hs l hx
    have hlow : ∀ l, l ∉ J → ∀ x ∈ tsupport (α l), x 0 < c - δ := by
      intro l hl x hx
      have h₁ := abs_lt.1 (lt_of_le_of_lt (abs_sub_coord_le_norm x (y l) 0) (hdisc l x hx))
      have h₂ := hlowy l hl
      rw [hc₁]
      linarith [h₁.2]
    have hhigh : ∀ l, l ∈ J → ∀ x ∈ tsupport (α l), c + δ < x 0 := by
      intro l hl x hx
      have h₁ := abs_lt.1 (lt_of_le_of_lt (abs_sub_coord_le_norm x (y l) 0) (hdisc l x hx))
      have h₂ := (hJ l).1 hl
      rw [hc₂]
      linarith [h₁.1]
    let mp : ℝ → Fin n → RealPlane → ℂ := shiftedProfiles J α
    have hdm : ∀ r : ℝ, Pairwise fun i j => Disjoint (tsupport (mp r i)) (tsupport (mp r j)) := by
      intro r a b hab
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      by_cases ha : a ∈ J <;> by_cases hb' : b ∈ J
      · rw [mem_tsupport_shiftedProfiles_of_mem ha] at hx
        rw [mem_tsupport_shiftedProfiles_of_mem hb'] at hx'
        exact Set.disjoint_left.1 (hd hab) hx hx'
      · rw [mem_tsupport_shiftedProfiles_of_mem ha] at hx
        rw [mem_tsupport_shiftedProfiles_of_notMem hb'] at hx'
        have h₁ := hhigh a ha _ hx
        have h₂ := hlow b hb' _ hx'
        rw [sub_smul_unitY_fst] at h₁
        linarith
      · rw [mem_tsupport_shiftedProfiles_of_notMem ha] at hx
        rw [mem_tsupport_shiftedProfiles_of_mem hb'] at hx'
        have h₁ := hhigh b hb' _ hx'
        have h₂ := hlow a ha _ hx
        rw [sub_smul_unitY_fst] at h₁
        linarith
      · rw [mem_tsupport_shiftedProfiles_of_notMem ha] at hx
        rw [mem_tsupport_shiftedProfiles_of_notMem hb'] at hx'
        exact Set.disjoint_left.1 (hd hab) hx hx'
    have hmm : ∀ (r : ℝ) (l : Fin n), mp r l ∈ complexProfiles := by
      intro r l
      by_cases hl : l ∈ J
      · simp only [mp, shiftedProfiles, if_pos hl]
        exact (hM _ (hα l) _ (φ l).2 (r • unitY) 0).2.2.2.1
      · simp only [mp, shiftedProfiles, if_neg hl]
        exact hα l
    let C : Set (Fin n → RealPlane) := Set.univ.pi fun l => tsupport (α l)
    let w : (Fin n → RealPlane) → ℂ := fun y' => ∏ l, α l (y' l)
    have hC : IsCompact C := isCompact_pi_tsupport hα
    have hwc : Continuous w := continuous_prod_profiles hα
    have hval : ∀ (r : ℝ) (x : Fin n → RealPlane) (l : Fin n),
        mp r l ((x + r • mv) l) = α l (x l) := by
      intro r x l
      by_cases hl : l ∈ J
      · rw [add_smul_shiftVector_of_mem hl]
        simp only [mp, shiftedProfiles, if_pos hl, translateProfile, add_sub_cancel_right]
      · rw [add_smul_shiftVector_of_notMem hl]
        simp only [mp, shiftedProfiles, if_neg hl]
    have hCm : ∀ r : ℝ, ∀ x ∈ C, x + r • mv ∈ injectivePointTuples n := by
      intro r x hx
      refine pi_tsupport_subset_injective (hdm r) fun l _ => ?_
      by_cases hl : l ∈ J
      · show (x + r • mv) l ∈ tsupport (shiftedProfiles J α r l)
        rw [mem_tsupport_shiftedProfiles_of_mem hl, add_smul_shiftVector_of_mem hl,
          add_sub_cancel_right]
        exact hx l (Set.mem_univ l)
      · show (x + r • mv) l ∈ tsupport (shiftedProfiles J α r l)
        rw [mem_tsupport_shiftedProfiles_of_notMem hl, add_smul_shiftVector_of_notMem hl]
        exact hx l (Set.mem_univ l)
    have hsec : ∀ r : ℝ, profileIntegral (mp r) K = ∫ x in C, w x * K (x + r • mv) := by
      intro r
      rw [profileIntegral, profileIntegrand_eq, ← integral_add_right_eq_self _ (r • mv),
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [w]
        congr 1
        exact Finset.prod_congr rfl fun l _ => hval r x l
      · intro x hx
        simp only [C, Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] at hx
        obtain ⟨l, hl⟩ := hx
        have h0 : α l (x l) = 0 := image_eq_zero_of_notMem_tsupport hl
        simp only [w]
        rw [Finset.prod_eq_zero (Finset.mem_univ l) h0, zero_mul]
    let ψ : ℝ → ℂ := fun r => centeredFnAtProducts S (mp r) φ - profileIntegral (mp r) K
    have hψ : ∀ r' : ℝ, ∃ ρ' > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (r' : ℂ) ρ') ∧
        ∀ r : ℝ, (r : ℂ) ∈ Metric.ball (r' : ℂ) ρ' → h r = ψ r := by
      intro r'
      obtain ⟨ρa, hρa, ga, hga, hea⟩ := h1 J α hα c δ hδ hdm hmm i i' hiJ hi'J hlow hhigh r'
      obtain ⟨ρb, hρb, gb, hgb, heb⟩ := h2 C hC w hwc mv hCm r'
      have hb₁ : Metric.ball (r' : ℂ) (min ρa ρb) ⊆ Metric.ball (r' : ℂ) ρa :=
        Metric.ball_subset_ball (min_le_left _ _)
      have hb₂ : Metric.ball (r' : ℂ) (min ρa ρb) ⊆ Metric.ball (r' : ℂ) ρb :=
        Metric.ball_subset_ball (min_le_right _ _)
      refine ⟨min ρa ρb, lt_min hρa hρb, fun z => ga z - gb z,
        (hga.mono hb₁).sub (hgb.mono hb₂), fun r hr => ?_⟩
      simp only [ψ]
      rw [hea r (hb₁ hr), heb r (hb₂ hr), hsec r]
    have hzero : ∀ r ∈ Set.Ioo (r₀ - ρ) (r₀ + ρ), ψ r = 0 := by
      intro r hr
      refine hv₁ (mp r) (hmm r) (hdm r) fun l x hx => ?_
      have hrr : |r - r₀| < ρ := abs_lt.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩
      show ‖x - (y + r₀ • mv) l‖ < ρ₁
      by_cases hl : l ∈ J
      · have hx' : x - r • unitY ∈ tsupport (α l) :=
          (mem_tsupport_shiftedProfiles_of_mem hl x).1 hx
        have h₁ := hdisc l _ hx'
        rw [add_smul_shiftVector_of_mem hl]
        have e : x - (y l + r₀ • unitY) =
            (x - r • unitY - y l) + (r - r₀) • unitY := by
          rw [sub_smul]
          abel
        rw [e]
        have h₂ : ‖(r - r₀) • unitY‖ = |r - r₀| := by
          rw [norm_smul, norm_unitY, mul_one, Real.norm_eq_abs]
        linarith [norm_add_le (x - r • unitY - y l) ((r - r₀) • (unitY : RealPlane))]
      · have hx' : x ∈ tsupport (α l) := (mem_tsupport_shiftedProfiles_of_notMem hl x).1 hx
        rw [add_smul_shiftVector_of_notMem hl]
        linarith [hdisc l x hx']
    have hfin := hb ψ hψ ⟨r₀ - ρ, r₀ + ρ, by linarith, hzero⟩ 0
    have hz : mp 0 = α := by
      funext l x
      by_cases hl : l ∈ J <;> simp [mp, shiftedProfiles, hl, translateProfile]
    simpa only [ψ, hz, discrepancy] using hfin
  exact fun y hy => main _ y rfl hy
end
section
theorem continuous_embedPlaneTuple (p : ℕ) :
    Continuous (embedPlaneTuple : (Fin p → RealPlane) → Fin p → ℂ × ℂ) := by
  have h0 : Continuous fun y : RealPlane => y 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous
  have h1 : Continuous fun y : RealPlane => y 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
  have hp : Continuous embedPlane :=
    (Complex.continuous_ofReal.comp h0).prodMk (Complex.continuous_ofReal.comp h1)
  exact continuous_pi fun i => hp.comp (continuous_apply i)
theorem discrepancyVanishesNear_of_ordered {S : ConnFamily} {q : ℕ}
    {φ : Fin (q + 1) → realLabels} {K : (Fin (q + 1) → RealPlane) → ℂ}
    (hplates : ∀ (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))),
      UnionKernel.IntegralRepresentation S υ ς φ)
    (hopen : ∀ (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))),
      IsOpen (orderedTube υ ς))
    (hker : ExtendsOrderedKernels S φ (unionKernel S φ))
    (hK : ∀ y ∈ orderedRealTuples q, K y = tubeUnionFunction S φ (embedPlaneTuple y))
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ orderedRealTuples q) :
    DiscrepancyVanishesNear S K φ y := by
  obtain ⟨υ, ς, hz⟩ : ∃ (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))),
      embedPlaneTuple y ∈ orderedTube υ ς := by
    simpa [orderedRealTuples, orderedTubeUnion, Set.mem_iUnion] using hy
  have hU : IsOpen (embedPlaneTuple ⁻¹' orderedTube υ ς :
      Set (Fin (q + 1) → RealPlane)) := (hopen υ ς).preimage (continuous_embedPlaneTuple _)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU y hz
  refine ⟨ρ, hρ, fun α hα hd hs => ?_⟩
  have hin : ∀ y' : Fin (q + 1) → RealPlane, (∀ i, y' i ∈ tsupport (α i)) →
      embedPlaneTuple y' ∈ orderedTube υ ς := by
    intro y' hy'
    refine hball ((dist_pi_lt_iff hρ).2 fun i => ?_)
    have h := hs i (hy' i)
    simpa [dist_eq_norm, openDiscAt] using h
  have h := ((hplates υ ς α hα hin).2 hd).2
  rw [discrepancy, h, sub_eq_zero]
  have he : profileIntegrand α
      (fun y' => orderedFrameKernel S υ ς (embedPlaneTuple y') φ) =
      profileIntegrand α K := by
    refine Set.indicator_congr fun y' hy' => ?_
    have hz' := hin y' fun i => hy' i (Set.mem_univ i)
    have hm : y' ∈ orderedRealTuples q := by
      show embedPlaneTuple y' ∈ orderedTubeUnion q
      exact Set.mem_iUnion.2 ⟨υ, Set.mem_iUnion.2 ⟨ς, hz'⟩⟩
    rw [hK y' hm]
    show _ * _ = _ * unionKernel S φ (embedPlaneTuple y')
    rw [hker υ ς _ hz']
  simp only [profileIntegral, he]
end
section
open YangMills.Construction.DisjointTuples YangMills.Construction.EuclideanFunctionals.TranslationRules
variable {n : ℕ}
abbrev planeCoordEquiv : RealPlane ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
theorem comp_planeCoordEquiv_mem_complexProfiles {f : (Fin 2 → ℝ) → ℂ}
    (hf : f ∈ EuclideanBalls.compactC1 2 ℂ) : f ∘ planeCoordEquiv ∈ complexProfiles :=
  ⟨hf.1.comp planeCoordEquiv.contDiff, hf.2.comp_homeomorph planeCoordEquiv.toHomeomorph⟩
theorem comp_planeCoordEquiv_symm_mem_compactC1 {α : RealPlane → ℂ} (hα : α ∈ complexProfiles) :
    α ∘ planeCoordEquiv.symm ∈ EuclideanBalls.compactC1 2 ℂ :=
  ⟨hα.1.comp planeCoordEquiv.symm.contDiff,
    hα.2.comp_homeomorph planeCoordEquiv.symm.toHomeomorph⟩
theorem tsupport_comp_planeCoordEquiv (f : (Fin 2 → ℝ) → ℂ) :
    tsupport (f ∘ planeCoordEquiv) = planeCoordEquiv ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f planeCoordEquiv.toHomeomorph
theorem tsupport_comp_planeCoordEquiv_symm (α : RealPlane → ℂ) :
    tsupport (α ∘ planeCoordEquiv.symm) = planeCoordEquiv.symm ⁻¹' tsupport α :=
  tsupport_comp_eq_preimage α planeCoordEquiv.symm.toHomeomorph
theorem productFunction_add_smul (a b : RealPlane → ℂ) (c : ℂ) (φ : RealPlane → ℝ) :
    productFunction (a + c • b) φ = productFunction a φ + c • productFunction b φ := by
  funext x
  simp only [productFunction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem prod_update_add_smul (F : Fin n → RealPlane → ℂ) (G : RealPlane → ℂ) (i : Fin n)
    (lam : ℂ) (y : Fin n → RealPlane) :
    ∏ l, (Function.update F i (F i + lam • G)) l (y l) =
      ∏ l, F l (y l) + lam * ∏ l, (Function.update F i G) l (y l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => F l (y l)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => Function.update F i G l (y l))
      (Finset.mem_univ i)]
  have h₁ : ∏ l ∈ Finset.univ.erase i, (Function.update F i (F i + lam • G)) l (y l) =
      ∏ l ∈ Finset.univ.erase i, F l (y l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h₂ : ∏ l ∈ Finset.univ.erase i, (Function.update F i G) l (y l) =
      ∏ l ∈ Finset.univ.erase i, F l (y l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [h₁, h₂]
  simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem integrable_prod_mul {F : Fin n → RealPlane → ℂ} {K : (Fin n → RealPlane) → ℂ}
    (hKc : ContinuousOn K (injectivePointTuples n)) (hF : ∀ l, F l ∈ complexProfiles)
    (hd : Pairwise fun i j => Disjoint (tsupport (F i)) (tsupport (F j))) :
    Integrable fun y : Fin n → RealPlane => (∏ l, F l (y l)) * K y := by
  rw [← profileIntegrand_eq]
  exact integrable_profileIntegrand hF hKc (pi_tsupport_subset_injective hd)
theorem discrepancy_update_add_smul {S : ConnFamily}
    (hlin : OrthogonalInvariance.EntrywiseLinear S)
    (hP : ProductFunctionsInC1c) (hn : 1 ≤ n) {K : (Fin n → RealPlane) → ℂ}
    (hKc : ContinuousOn K (injectivePointTuples n)) (φ : Fin n → realLabels)
    {F : Fin n → RealPlane → ℂ} {G : RealPlane → ℂ} {i : Fin n} (lam : ℂ)
    (hF : ∀ l, F l ∈ complexProfiles)
    (hdF : Pairwise fun a b => Disjoint (tsupport (F a)) (tsupport (F b)))
    (hU : ∀ l, Function.update F i G l ∈ complexProfiles)
    (hdU : Pairwise fun a b => Disjoint (tsupport (Function.update F i G a))
      (tsupport (Function.update F i G b)))
    (hS : ∀ l, Function.update F i (F i + lam • G) l ∈ complexProfiles)
    (hdS : Pairwise fun a b => Disjoint (tsupport (Function.update F i (F i + lam • G) a))
      (tsupport (Function.update F i (F i + lam • G) b))) :
    discrepancy S K φ (Function.update F i (F i + lam • G)) =
      discrepancy S K φ F + lam * discrepancy S K φ (Function.update F i G) := by
  let h : Fin n → R4 → ℂ := fun l => productFunction (F l) (φ l)
  let gg : R4 → ℂ := productFunction G (φ i)
  have hh : h ∈ disjointComplexTuples n :=
    (mem_disjointComplexTuples_iff hn h).2 (complexFamily_productFunction hP hn φ hF hdF)
  have e₁ : Function.update h i gg = fun l => productFunction (Function.update F i G l) (φ l) := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [gg]
    · simp [h, Function.update_of_ne hl]
  have hu : Function.update h i gg ∈ disjointComplexTuples n := by
    rw [e₁]
    exact (mem_disjointComplexTuples_iff hn _).2 (complexFamily_productFunction hP hn φ hU hdU)
  have e₂ : Function.update h i (h i + lam • gg) =
      fun l => productFunction (Function.update F i (F i + lam • G) l) (φ l) := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp only [Function.update_self, h, gg]
      exact (productFunction_add_smul _ _ _ _).symm
    · simp [h, Function.update_of_ne hl]
  obtain ⟨-, hval⟩ := hlin n i lam h gg hh hu
  rw [e₁, e₂] at hval
  have hint : profileIntegral (Function.update F i (F i + lam • G)) K =
      profileIntegral F K + lam * profileIntegral (Function.update F i G) K := by
    simp only [profileIntegral, profileIntegrand_eq]
    rw [← integral_const_mul, ← integral_add (integrable_prod_mul hKc hF hdF)
      ((integrable_prod_mul hKc hU hdU).const_mul lam)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [prod_update_add_smul]
    ring
  simp only [discrepancy, centeredFnAtProducts]
  rw [hval, hint]
  simp only [h]
  ring
theorem discrepancy_eq_zero {S : ConnFamily} (hlin : OrthogonalInvariance.EntrywiseLinear S)
    (hP : ProductFunctionsInC1c) (hglobal : LocalVanishing.VanishingFromLocalVanishing)
    (hn : 2 ≤ n) {K : (Fin n → RealPlane) → ℂ} (hKc : ContinuousOn K (injectivePointTuples n))
    (φ : Fin n → realLabels) (hv : ∀ y ∈ injectivePointTuples n, DiscrepancyVanishesNear S K φ y)
    {α : Fin n → RealPlane → ℂ} (hα : ∀ i, α i ∈ complexProfiles)
    (hd : Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) :
    discrepancy S K φ α = 0 := by
  let tp : (Fin n → (Fin 2 → ℝ) → ℂ) → Fin n → RealPlane → ℂ :=
    fun f i => f i ∘ planeCoordEquiv
  have hmem : ∀ f ∈ disjointSupportTuples 2 n, (∀ i, tp f i ∈ complexProfiles) ∧
      Pairwise fun i j => Disjoint (tsupport (tp f i)) (tsupport (tp f j)) := by
    intro f hf
    refine ⟨fun i => comp_planeCoordEquiv_mem_complexProfiles (hf.1 i), fun i j hij => ?_⟩
    simp only [tp, tsupport_comp_planeCoordEquiv]
    exact (hf.2 hij).preimage _
  let D : disjointSupportTuples 2 n → ℂ := fun f => discrepancy S K φ (tp f.1)
  have hlinD : IsSeparatelyLinear D := by
    intro i lam f g hf hg
    have e₁ : tp (Function.update f i (f i + lam • g)) =
        Function.update (tp f) i (tp f i + lam • (g ∘ planeCoordEquiv)) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp only [tp, Function.update_self]
        rfl
      · simp [tp, Function.update_of_ne hl]
    have e₂ : tp (Function.update f i g) = Function.update (tp f) i (g ∘ planeCoordEquiv) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [tp]
      · simp [tp, Function.update_of_ne hl]
    have hS := hmem _ (update_add_smul_mem_disjointSupportTuples lam hf hg)
    have hU := hmem _ hg
    rw [e₁] at hS
    rw [e₂] at hU
    show discrepancy S K φ (tp (Function.update f i (f i + lam • g))) =
      discrepancy S K φ (tp f) + lam * discrepancy S K φ (tp (Function.update f i g))
    rw [e₁, e₂]
    exact discrepancy_update_add_smul hlin hP (by omega) hKc φ lam (hmem f hf).1 (hmem f hf).2
      hU.1 hU.2 hS.1 hS.2
  have hnear : ∀ x : TestFunctions.injectiveTuples (Fin 2 → ℝ) n, VanishesNearConfig D x := by
    intro x
    have hy : (fun i => planeCoordEquiv.symm (x.1 i)) ∈ injectivePointTuples n :=
      fun a b e => x.2 (planeCoordEquiv.symm.injective e)
    obtain ⟨ρ, hρ, hv'⟩ := hv _ hy
    refine ⟨ρ, hρ, fun f hf => ?_⟩
    refine hv' (tp f.1) (hmem f.1 f.2).1 (hmem f.1 f.2).2 fun i z hz => ?_
    have hz' : planeCoordEquiv z ∈ tsupport (f.1 i) := by
      have : z ∈ planeCoordEquiv ⁻¹' tsupport (f.1 i) := by
        rw [← tsupport_comp_planeCoordEquiv]
        exact hz
      exact this
    have h := hf i hz'
    simp only [EuclideanBalls.euclidBall, Set.mem_setOf_eq] at h
    show ‖z - planeCoordEquiv.symm (x.1 i)‖ < ρ
    rw [EuclideanSpace.norm_eq]
    convert h using 2
    simp [EuclideanCoords.sqrtSumSq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  let f₀ : Fin n → (Fin 2 → ℝ) → ℂ := fun i => α i ∘ planeCoordEquiv.symm
  have hf₀ : f₀ ∈ disjointSupportTuples 2 n := by
    refine ⟨fun i => comp_planeCoordEquiv_symm_mem_compactC1 (hα i), fun i j hij => ?_⟩
    simp only [f₀, tsupport_comp_planeCoordEquiv_symm]
    exact (hd hij).preimage _
  have hfin := (hglobal 2 (Or.inl rfl) n hn D hlinD).2 hnear ⟨f₀, hf₀⟩
  have hz : tp f₀ = α := by
    funext i y
    simp [tp, f₀]
  simpa only [D, hz] using hfin
end
theorem holds
    (hone : UnionKernel.Holds)
    (hharm : DistinctHarmonics.Holds)
    (hset : PlaneDataAsStandingData.ExistsStandingAndApertureData)
    (hslide : TangentialAnalyticity.Holds)
    (hglobal : LocalVanishing.VanishingFromLocalVanishing)
    (hthree : YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (hmom : OrthogonalInvariance.OrthogonalMapStatement)
    (hinv : MomentSymmetry.ReductionHolds)
    (hrules : TranslationRules.TranslationAndMotionFacts)
    (hseries : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Holds := by
  intro m S d φ₀ q hq φ
  obtain ⟨e, -, rfl⟩ := (hset m S d).2 φ₀
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hsym := (hinv m S d.fnl).1
  have hlin : OrthogonalInvariance.EntrywiseLinear S :=
    (hmom m S d.fnl 1).2.2.2.1
  obtain ⟨-, hMot, hPl, -⟩ := hrules
  have hh := fun h : ℤ => hharm m S e (q' + 1) hq h φ
  let K := harmonicSum S e.angle (q' + 1 + 1) φ
  have hKa : IsRealAnalyticTupleFun (injectivePointTuples (q' + 1 + 1)) K :=
    isRealAnalyticTupleFun_sum (hh 0).2.1.1.1 _ (fun h => distinctHarmonic S e.angle φ h)
      fun h _ => (hh h).2.1.1
  have hKc : ContinuousOn K (injectivePointTuples (q' + 1 + 1)) :=
    continuousOn_finset_sum _ fun h _ => (hh h).1.1.1
  have hsum : EqOnOrderedTuples S e.angle φ := (hh 0).2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hunion, -, hordf⟩ :=
    hone m S e (q' + 1) hq φ rightAngleZero rightAngleZero 1 1
  have hordv : ∀ y : Fin (q' + 1 + 1) → RealPlane, Function.Injective (fun i => y i 1) →
      DiscrepancyVanishesNear S K φ y := by
    intro y hy
    refine discrepancyVanishesNear_of_ordered
      (fun υ ς => (hone m S e (q' + 1) hq φ υ υ ς ς).2.2.2.1)
      (fun υ ς => (hone m S e (q' + 1) hq φ υ υ ς ς).2.1.1) hunion.1 hsum ?_
    rw [hordf.1]
    exact Or.inr hy
  have h1 : ShiftedProductsExtend S φ := fun J α hα c δ hδ hdm hmm i₁ i₂ h₁ h₂ hl hg rs =>
    exists_holomorphic_shifted_products d.fnl d.coneCond hsym hslide hMot hPl (by omega) J φ hα
      hδ hdm hmm h₁ h₂ hl hg rs
  have h2 : ShiftedIntegralsExtend K := fun C hC w hw v hv rs =>
    exists_holomorphic_integral_shift hthree hseries (by omega) hKa hKc hC hw v hv rs
  have hv := discrepancyVanishesNear_of_injective hthree.2.1 hMot hordv h1 h2
  refine ⟨hKa, hsum, fun α hα hd => ?_, fun y hy t => ?_⟩
  · refine ⟨integrable_profileIntegrand hα hKc (pi_tsupport_subset_injective hd), ?_⟩
    exact sub_eq_zero.1 (discrepancy_eq_zero hlin hPl hglobal (by omega) hKc φ hv hα hd)
  · refine Finset.sum_congr rfl fun h _ => ?_
    show distinctHarmonic S e.angle φ h _ =
      distinctHarmonic S e.angle φ h y * _
    rw [(hh h).2.2.2.2.1 y hy t, mul_comm]
end YangMills.Construction.EuclideanFunctionals.HarmonicDensity
end
