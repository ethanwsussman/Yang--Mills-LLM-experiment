import YangMills.Construction.Towers.CriticalBranchUnderTheDilation
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.NormaliserLogarithmIsInvariantUnderIsometriesProof
import YangMills.Construction.Towers.NormalisersUnderTheDilation
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace NormalisersScaling
theorem transportTotal_comp {X Y V : Type*} (e : X ≃ Y) (f : X → V) : transportTotal e f ∘ e = f := by apply _root_.YangMills.Construction.Tower.transportTotal_comp <;> assumption
open Matrices Conventions
theorem transportTotal_of_comp {X Y V : Type*} (e : X ≃ Y) (f : Y → V) :
    transportTotal e (f ∘ e) = f := by
  funext y
  simp [transportTotal]
theorem eventuallyNearIdentity_comp {ι ι' : Type} {P : Set (ι → ComplexMatrix2)}
    {P' : Set (ι' → ComplexMatrix2)} (e : ι ≃ ι')
    (h : PreservesOpenAndNhdsOfOne P P' (transportTotal e)) {Q : (ι → ComplexMatrix2) → Prop}
    (hQ : EventuallyNearIdentity P Q) : EventuallyNearIdentity P' fun W => Q (W ∘ e) := by
  have hS : EventuallyNearIdentity P (· ∈ {V | V ∈ P ∧ Q V}) := by
    unfold EventuallyNearIdentity at hQ ⊢
    filter_upwards [hQ, self_mem_nhdsWithin] with V h₁ h₂
    exact ⟨h₂, h₁⟩
  have hS' := ((h _ fun V hV => hV.1).2).1 hS
  unfold EventuallyNearIdentity at hS' ⊢
  filter_upwards [hS'] with W hW
  obtain ⟨V, hV, rfl⟩ := hW
  rw [transportTotal_comp]
  exact hV.2
theorem curveTangent_congr_eventually {L n k j : ℕ} {δ δ' : ℝ → Edge L n k j → ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), δ t = δ' t) : curveTangent δ = curveTangent δ' := by apply _root_.YangMills.Construction.Tower.SymmetryInvariance.curveTangent_congr <;> assumption
section Orientation
variable {L n k i L₂ n₂ k₂ i₂ : ℕ}
structure PreservesOrientation (e : Edge L n k i ≃ Edge L₂ n₂ k₂ i₂) : Prop where
  isPositivelyOriented_iff : ∀ b, (e b).IsPositivelyOriented ↔ b.IsPositivelyOriented
  map_opposite : ∀ b, e b.opposite = (e b).opposite
variable {e : Edge L n k i ≃ Edge L₂ n₂ k₂ i₂}
theorem PreservesOrientation.symm_isPositivelyOriented (h : PreservesOrientation e)
    (y : Edge L₂ n₂ k₂ i₂) :
    (e.symm y).IsPositivelyOriented ↔ y.IsPositivelyOriented := by
  rw [← h.isPositivelyOriented_iff, e.apply_symm_apply]
theorem PreservesOrientation.symm_opposite (h : PreservesOrientation e) (y : Edge L₂ n₂ k₂ i₂) :
    e.symm y.opposite = (e.symm y).opposite :=
  e.injective (by rw [h.map_opposite, e.apply_symm_apply, e.apply_symm_apply])
theorem PreservesOrientation.curveTangent_transport (h : PreservesOrientation e)
    (δ : ℝ → Edge L n k i → ComplexMatrix2) :
    curveTangent (fun t => transportTotal e (δ t)) = transportTotal e (curveTangent δ) := by
  funext y
  simp only [curveTangent, extendOddly, transportTotal, Function.comp]
  by_cases hy : y.IsPositivelyOriented
  · rw [if_pos hy, if_pos ((h.symm_isPositivelyOriented y).2 hy)]
  · rw [if_neg hy, if_neg (mt (h.symm_isPositivelyOriented y).1 hy), h.symm_opposite]
theorem PreservesOrientation.isDiffAtZeroPath_transport (h : PreservesOrientation e)
    (hmem : ∀ U ∈ fieldSpace L n k i, transportTotal e U ∈ fieldSpace L₂ n₂ k₂ i₂)
    {δ : ℝ → Edge L n k i → ComplexMatrix2} (hδ : IsDiffAtZeroPath δ) :
    IsDiffAtZeroPath (fun t => transportTotal e (δ t)) :=
  ⟨hδ.1.mono fun _ ht => hmem _ ht,
    fun c hc => hδ.2 (e.symm c) ((h.symm_isPositivelyOriented c).2 hc)⟩
theorem PreservesOrientation.isTwiceDiffCurve_transport (h : PreservesOrientation e)
    (hmem : ∀ U ∈ fieldSpace L n k i, transportTotal e U ∈ fieldSpace L₂ n₂ k₂ i₂)
    {I J : Set ℝ} {γ : ℝ → Edge L n k i → ComplexMatrix2}
    (hγ : (fieldCurveData L n k i).IsTwiceDiffCurve I γ)
    (hJ : IsOpenIntervalAroundZero J) (hJI : J ⊆ I) :
    (fieldCurveData L₂ n₂ k₂ i₂).IsTwiceDiffCurve J
      (fun t => transportTotal e (γ t)) := by
  obtain ⟨⟨-, hmaps, hdiff⟩, hdd⟩ := hγ
  exact ⟨⟨hJ, fun _ ht => hmem _ (hmaps (hJI ht)),
    fun c hc => (hdiff _ ((h.symm_isPositivelyOriented c).2 hc)).mono hJI⟩,
    fun c hc => (hdd _ ((h.symm_isPositivelyOriented c).2 hc)).mono hJI⟩
end Orientation
theorem preservesOrientation_scaleEdge {L n k j : ℕ} (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    PreservesOrientation (scaleEdge (n := n) hL hj i) where
  isPositivelyOriented_iff b := by
    constructor
    · rintro ⟨μ, hμ⟩
      refine ⟨μ, (scaleVertex (n := n) hL hj i).injective ?_⟩
      rw [map_sub, scaleVertex_unitStep]
      exact hμ
    · rintro ⟨μ, hμ⟩
      refine ⟨μ, ?_⟩
      have h := congrArg (scaleVertex (n := n) hL hj i) hμ
      rw [map_sub, scaleVertex_unitStep] at h
      exact h
  map_opposite _ := rfl
def FibreFormHolds (L n k i : ℕ) (W : Edge L n k (i + 1) → ComplexMatrix2) : Prop :=
  (fieldCurveData L n k i).IsCriticalOn (chosenLevelFibre L n k i W)
      (chosenGaugeFixedEnergy L n k i) (chosenProlong L n k i W) ∧
    Function.Surjective (constraintDifferential L n k i W) ∧
    (fieldCurveData L n k i).IsHessianFormAt (S := LinearMap.ker (constraintDifferential L n k i W))
      (fun B => B.1.1) (chosenLevelFibre L n k i W) (chosenGaugeFixedEnergy L n k i)
      (chosenProlong L n k i W) (fibreHessianForm L n k i W) ∧
    (∀ B : LinearMap.ker (constraintDifferential L n k i W),
      ∃ (I : Set ℝ) (γ : ℝ → Edge L n k i → ComplexMatrix2),
      (fieldCurveData L n k i).IsTwiceDiffCurve I γ ∧
        Set.MapsTo γ I (chosenLevelFibre L n k i W) ∧ γ 0 = chosenProlong L n k i W ∧
        (fieldCurveData L n k i).tangent γ = B.1.1) ∧
    (fibreHessianForm L n k i W).PosDef
theorem gaussianNormaliser_eq_of_transport {L n k n₂ k₂ i : ℕ}
    (hFixed : ChosenBranchIsCritical)
    (hGauss : ConstrainedGaussianIsometryInvariance)
    (hPaths : diffAtZeroPathsStatement)
    (hMaps : AnalyticMapsAlongCurves)
    (hs : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hn₂ : 0 < n₂) (hik : i + 1 ≤ k)
    (hik₂ : i + 1 ≤ k₂)
    (e : Edge L n k i ≃ Edge L n₂ k₂ i) (e' : Edge L n k (i + 1) ≃ Edge L n₂ k₂ (i + 1))
    (ho : PreservesOrientation e) (ho' : PreservesOrientation e')
    (hmem : ∀ U ∈ fieldSpace L n k i, transportTotal e U ∈ fieldSpace L n₂ k₂ i)
    (O : edgeFormSpace L n k i ≃ₗ[ℝ] edgeFormSpace L n₂ k₂ i)
    (hO : ∀ B : edgeFormSpace L n k i, (O B : Edge L n₂ k₂ i → ComplexMatrix2) =
      transportTotal e (B : Edge L n k i → ComplexMatrix2))
    (O' : edgeFormSpace L n k (i + 1) ≃ₗ[ℝ] edgeFormSpace L n₂ k₂ (i + 1))
    (hO' : ∀ B : edgeFormSpace L n k (i + 1), (O' B : Edge L n₂ k₂ (i + 1) → ComplexMatrix2) =
      transportTotal e' (B : Edge L n k (i + 1) → ComplexMatrix2))
    (hpair : ∀ B ∈ edgeFormSpace L n k i, ∀ B' ∈ edgeFormSpace L n k i,
      edgeFormPairing (transportTotal e B) (transportTotal e B') = edgeFormPairing B B')
    (hpair' : ∀ B ∈ edgeFormSpace L n k (i + 1), ∀ B' ∈ edgeFormSpace L n k (i + 1),
      edgeFormPairing (transportTotal e' B) (transportTotal e' B') = edgeFormPairing B B')
    (hAvg : ∀ V ∈ fieldSpace L n k i,
      transportTotal e' (smoothingStep L n k i V) = smoothingStep L n₂ k₂ i (transportTotal e V))
    (hGF : ∀ U : Edge L n k i → ComplexMatrix2, PeriodicLattice.HasOffCenterContours k i univ U →
      axialFunction L n k i U = axialFunction L n₂ k₂ i (transportTotal e U))
    (W : Edge L n₂ k₂ (i + 1) → ComplexMatrix2)
    (hfirst : FibreFormHolds L n k i (W ∘ e')) (hsecond : FibreFormHolds L n₂ k₂ i W)
    (hlift : chosenProlong L n₂ k₂ i W = transportTotal e (chosenProlong L n k i (W ∘ e')))
    (hnear : ∀ᶠ U in 𝓝[fieldSpace L n₂ k₂ i] (chosenProlong L n₂ k₂ i W),
      chosenEnergy L n k i (U ∘ e) = chosenEnergy L n₂ k₂ i U) :
    gaussianNormaliser L n₂ k₂ i W = gaussianNormaliser L n k i (W ∘ e') := by
  obtain ⟨hcrit, -, hhess, hcurves, -⟩ := hfirst
  obtain ⟨hcrit', -, hhess', -, -⟩ := hsecond
  have hU := (hFixed L n k hs hn).2 i hik
  have hU₂ := (hFixed L n₂ k₂ hs hn₂).2 i hik₂
  set V := chosenProlong L n k i (W ∘ e') with hVdef
  have hVN := hcrit.1
  have hV₂N : transportTotal e V ∈ chosenLevelFibre L n₂ k₂ i W := by
    rw [← hlift]
    exact hcrit'.1
  have hsub : chosenFibreNhd L n k i ⊆ fieldSpace L n k i :=
    hU.isOpenNhd.1.1
  have hVc : V ∈ fieldSpace L n k i := hsub hVN.1
  have hPaths₁ := hPaths L n k i hs hn (by omega)
  have hPaths₂ := hPaths L n₂ k₂ i hs hn₂ (by omega)
  have hm₁ := (hMaps L n k i (i + 1) hs hn (by omega) hik).1 _ _ hU.analytic_smoothing
  have hm₂ := (hMaps L n₂ k₂ i (i + 1) hs hn₂ (by omega) hik₂).1 _ _ hU₂.analytic_smoothing
  refine hGauss L n k i (i + 1) L n₂ k₂ i (i + 1) O O' ?_ ?_ _ _ ?_ _ _ ?_
  · intro B B'
    rw [hO, hO, hpair _ B.2 _ B'.2]
  · intro B B'
    rw [hO', hO', hpair' _ B.2 _ B'.2]
  · intro B
    apply Subtype.ext
    obtain ⟨hδp, hδ0, hδt⟩ := hPaths₁.2.2 V hVc B B.2
    set δ : ℝ → Edge L n k i → ComplexMatrix2 :=
      fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k i → ComplexMatrix2)) V
      with hδdef
    have hδ0' : δ 0 = V := hδ0
    have hsδ := ho.isDiffAtZeroPath_transport hmem hδp
    have hsδt := ho.curveTangent_transport δ
    obtain ⟨hspecV, hpathV⟩ := hm₁.2 V hVN.1
    obtain ⟨hspecV', hpathV'⟩ := hm₂.2 _ hV₂N.1
    obtain ⟨-, hMδt⟩ := hpathV δ hδp hδ0'
    have hsMδt := ho'.curveTangent_transport (fun t => smoothingStep L n k i (δ t))
    obtain ⟨-, hMsδt⟩ := hpathV' _ hsδ (by
      show transportTotal e (δ 0) = _
      rw [hδ0'])
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), smoothingStep L n₂ k₂ i (transportTotal e (δ t)) =
        transportTotal e' (smoothingStep L n k i (δ t)) :=
      hδp.1.mono fun t ht => (hAvg _ ht).symm
    have e1 : ((O B : edgeFormSpace L n₂ k₂ i) : Edge L n₂ k₂ i → ComplexMatrix2) =
        curveTangent (fun t => transportTotal e (δ t)) := by
      rw [hO, hsδt, hδt]
    have hcL : constraintDifferential L n₂ k₂ i W =
        leftDifferentialLinear (smoothingStep L n₂ k₂ i) (transportTotal e V) := by
      unfold constraintDifferential
      rw [hlift]
    have hcW : ((constraintDifferential L n k i (W ∘ e') B : edgeFormSpace L n k (i + 1)) :
        Edge L n k (i + 1) → ComplexMatrix2) = leftDifferential (smoothingStep L n k i) V B :=
      hspecV B
    rw [hcL, hspecV', e1, ← hMsδt, curveTangent_congr_eventually hev, hsMδt, hO', hMδt, hδt, hcW]
  · intro B B' hB
    obtain ⟨I, γ, htw, hmaps, h0, ht⟩ := hcurves B
    have hT₁ := hhess I γ B htw hmaps h0 ht
    have hI := htw.1.1
    have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hγ : IsDiffAtZeroPath γ :=
      ⟨Filter.eventually_of_mem hI0 fun t ht => htw.1.2.1 ht,
        fun b hb => (htw.1.2.2 b hb 0 hI.2.2).differentiableAt hI0⟩
    have hsγ := ho.isDiffAtZeroPath_transport hmem hγ
    have hsγt := ho.curveTangent_transport γ
    have hlim := (hPaths₂.1 _ hsγ).2
    have ev₁ : ∀ᶠ t in 𝓝 (0 : ℝ), transportTotal e (γ t) ∈ chosenFibreNhd L n₂ k₂ i := by
      refine hlim.eventually ?_
      show chosenFibreNhd L n₂ k₂ i ∈ 𝓝[fieldSpace L n₂ k₂ i] (transportTotal e (γ 0))
      rw [h0]
      exact hPaths₂.2.1 _ hU₂.isOpenNhd.1 _ hV₂N.1
    have ev₂ : ∀ᶠ t in 𝓝 (0 : ℝ), chosenEnergy L n k i (transportTotal e (γ t) ∘ e) =
        chosenEnergy L n₂ k₂ i (transportTotal e (γ t)) := by
      refine hlim.eventually (p := fun U => chosenEnergy L n k i (U ∘ e) =
        chosenEnergy L n₂ k₂ i U) ?_
      show ∀ᶠ U in 𝓝[fieldSpace L n₂ k₂ i] (transportTotal e (γ 0)), _
      rw [h0, ← hlift]
      exact hnear
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 ev₁
    have hJ : IsOpenIntervalAroundZero (I ∩ Metric.ball (0 : ℝ) ε) := by
      refine ⟨hI.1.inter Metric.isOpen_ball, ?_, hI.2.2, Metric.mem_ball_self hε⟩
      have hb : (Metric.ball (0 : ℝ) ε).OrdConnected := by
        rw [Real.ball_eq_Ioo]
        exact ordConnected_Ioo
      exact hI.2.1.inter hb
    have hcurve := ho.isTwiceDiffCurve_transport hmem htw hJ inter_subset_left
    have hmapsJ : MapsTo (fun t => transportTotal e (γ t)) (I ∩ Metric.ball (0 : ℝ) ε)
        (chosenLevelFibre L n₂ k₂ i W) := fun t ht' => by
      refine ⟨hball t ht'.2, ?_⟩
      rw [← hAvg _ (hsub (hmaps ht'.1).1), (hmaps ht'.1).2, transportTotal_of_comp]
    have hT₂ := hhess' _ _ B' hcurve hmapsJ (by
      show transportTotal e (γ 0) = _
      rw [h0, hlift]) (by
      show curveTangent _ = ((B'.1 : edgeFormSpace L n₂ k₂ i) : Edge L n₂ k₂ i → ComplexMatrix2)
      have ht' : curveTangent γ = ((B.1 : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) :=
        ht
      rw [hsγt, hB, hO, ht'])
    rw [hT₁, hT₂]
    have ev₃ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ chosenFibreNhd L n k i :=
      Filter.eventually_of_mem hI0 fun t ht => (hmaps ht).1
    have hev : (fun t => chosenGaugeFixedEnergy L n₂ k₂ i (transportTotal e (γ t))) =ᶠ[𝓝 0]
        fun t => chosenGaugeFixedEnergy L n k i (γ t) := by
      filter_upwards [ev₂, ev₃] with t h₂ h₃
      rw [transportTotal_comp] at h₂
      show (chosenCriticalBranch L n₂ k₂).gaugeFixedEnergy i _ =
        (chosenCriticalBranch L n k).gaugeFixedEnergy i _
      unfold CriticalBranchData.gaugeFixedEnergy
      rw [← hGF _ (hU.subset_domain h₃).2]
      exact congrArg (· + axialFunction L n k i (γ t)) h₂.symm
    exact hev.deriv.deriv_eq
theorem tendsto_chosenProlong {L n k i : ℕ}
    (hFixed : ChosenBranchIsCritical)
    (hPaths : diffAtZeroPathsStatement)
    (hMaps : AnalyticMapsAlongCurves)
    (hs : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hik : i + 1 ≤ k) :
    trivialField L n k (i + 1) ∈ fieldSpace L n k (i + 1) ∧
      Tendsto (chosenProlong L n k i) (𝓝[fieldSpace L n k (i + 1)] (fun _ => (1 : ComplexMatrix2)))
        (𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2))) := by
  obtain ⟨hb, -⟩ := hFixed L n k hs hn
  have hlt : i < k := hik
  obtain ⟨𝒲, h𝒲, hA⟩ := hb.analytic_prolong i hlt
  refine ⟨h𝒲.1.1 h𝒲.2, ?_⟩
  have hc := ((hMaps L n k (i + 1) i hs hn hik hlt.le).1 𝒲 _ hA).1 _ h𝒲.2
  have hnear := (hPaths L n k (i + 1) hs hn hik).2.1 𝒲 h𝒲.1 _ h𝒲.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.mem_of_superset hnear fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem hnear)
  rwa [hb.prolong_trivial i hlt] at h
end NormalisersScaling
open Matrices Conventions NormalisersScaling in
theorem normalisersScalingCompatible_proof
    (hForm : CriticalFibreHessianPosDef)
    (hFixed : ChosenBranchIsCritical)
    (hGauss : ConstrainedGaussianIsometryInvariance)
    (hPaths : diffAtZeroPathsStatement)
    (hMaps : AnalyticMapsAlongCurves)
    (hNear : ScalingNearTrivialField)
    (hBranch : ChosenBranchScaling)
    (hStep : ScalingPreservesStepsAtSide.Statement) :
    NormalisersScalingCompatible := by
  intro L n k j hL hj hs hn hj1
  have hn₂ : 0 < scaledExponent n k j := Nat.add_pos_left hn _
  obtain ⟨hS, hLift⟩ := hBranch L n k j hL hj hs hn hj1
  have hZ : ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
      transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (gaussianNormaliser L n k l) W =
        gaussianNormaliser L (scaledExponent n k j) j l W := by
    intro l hl
    have hlj : l + 1 ≤ j := hl
    have hlk : l + 1 ≤ k := hlj.trans hj
    obtain ⟨⟨hbij, -, -, ⟨O, hO⟩, hpair, -⟩, -, -⟩ := hNear L n k j l l hL hj hs hn hl.le hl.le
    obtain ⟨⟨-, -, -, ⟨O', hO'⟩, hpair', -⟩, ⟨hopen, -⟩, -⟩ :=
      hNear L n k j (l + 1) (l + 1) hL hj hs hn hlj hlj
    have hobj := hStep L hL hs k j hj hj1 l hl n hn
    obtain ⟨-, hTend⟩ := tendsto_chosenProlong (L := L) (n := scaledExponent n k j) (k := j)
      (i := l) hFixed hPaths hMaps hs hn₂ hlj
    have h₁ : EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
        FibreFormHolds L n k l (W ∘ scaleEdge (n := n) hL hj (l + 1)) :=
      eventuallyNearIdentity_comp _ hopen (hForm L n k hs hn l hlk)
    have h₂ : EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
        FibreFormHolds L (scaledExponent n k j) j l W := hForm L _ j hs hn₂ l hlj
    have h₄ := hTend.eventually (eventually_eventually_nhdsWithin.2 (hS l hl.le))
    unfold EventuallyNearIdentity at h₁ h₂ ⊢
    filter_upwards [h₁, h₂, hLift l hl, h₄] with W a₁ a₂ a₃ a₄
    exact (gaussianNormaliser_eq_of_transport hFixed hGauss hPaths hMaps hs hn hn₂ hlk hlj
      (scaleEdge hL hj l) (scaleEdge hL hj (l + 1))
      (preservesOrientation_scaleEdge hL hj l) (preservesOrientation_scaleEdge hL hj (l + 1))
      hbij.mapsTo O hO O' hO' hpair hpair' (fun V hV => hobj.smoothingStep_eq V hV)
      (fun U hU => hobj.axialFunction_eq U hU) W a₁ a₂ a₃.symm a₄).symm
  refine ⟨hZ, fun l hl => ?_⟩
  have hlj : l + 1 ≤ j := hl
  obtain ⟨hone, -⟩ := tendsto_chosenProlong (L := L) (n := scaledExponent n k j) (k := j) (i := l)
    hFixed hPaths hMaps hs hn₂ hlj
  have hZ1 : gaussianNormaliser L n k l (trivialField L n k (l + 1)) =
      gaussianNormaliser L (scaledExponent n k j) j l
        (trivialField L (scaledExponent n k j) j (l + 1)) := by
    exact show transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (gaussianNormaliser L n k l)
        (fun _ => (1 : ComplexMatrix2)) =
          gaussianNormaliser L (scaledExponent n k j) j l (fun _ => (1 : ComplexMatrix2)) from
      Filter.Eventually.self_of_nhdsWithin
        (p := fun W => transportTotalScalar (scaleEdge (n := n) hL hj (l + 1))
          (gaussianNormaliser L n k l) W = gaussianNormaliser L (scaledExponent n k j) j l W)
        (hZ l hl) hone
  have hZl := hZ l hl
  unfold EventuallyNearIdentity at hZl ⊢
  filter_upwards [hZl] with W hW
  have hW' : gaussianNormaliser L n k l (W ∘ scaleEdge (n := n) hL hj (l + 1)) =
      gaussianNormaliser L (scaledExponent n k j) j l W := hW
  show Real.log (gaussianNormaliser L n k l (W ∘ scaleEdge (n := n) hL hj (l + 1))) -
      Real.log (gaussianNormaliser L n k l (trivialField L n k (l + 1))) =
    Real.log (gaussianNormaliser L (scaledExponent n k j) j l W) -
      Real.log (gaussianNormaliser L (scaledExponent n k j) j l
        (trivialField L (scaledExponent n k j) j (l + 1)))
  rw [hW', hZ1]
end YangMills.Construction.Tower
end
