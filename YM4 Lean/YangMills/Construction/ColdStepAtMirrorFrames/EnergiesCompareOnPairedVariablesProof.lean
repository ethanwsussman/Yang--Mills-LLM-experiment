import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.EnergiesCompareOnPairedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.GradientOfANearFunction
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesCompareNearABox
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace PairedEnergies
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isOpen_openPolyball (R : ℝ) : IsOpen (openPolyball ι R) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.isOpen_ballProduct <;> assumption
theorem exists_norm_eq_one_smul (e : BondVector) : ∃ u : BondVector, ‖u‖ = 1 ∧ e = ‖e‖ • u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.exists_unit_smul <;> assumption
theorem bondVariation_smul (b : ι) (c : ℝ) (u : BondVector) :
    (bondVariation b (c • u) : BondField ι) = c • bondVariation b u := by apply _root_.YangMills.SharedProofs.p169 <;> assumption
theorem secondDerivAlong_smul_smul {f : BondField ι → ℝ} {p : BondField ι} (h : ContDiffAt ℝ 2 f p) (c d : ℝ)
    (u v : BondField ι) : secondDerivAlong f p (c • u) (d • v) = c * d * secondDerivAlong f p u v := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun ξ => fderiv ℝ f ξ u) p := h1.clm_apply (differentiableAt_const _)
  unfold secondDerivAlong
  have e : (fun ξ => fderiv ℝ f ξ (c • u)) = fun ξ => c * fderiv ℝ f ξ u := by
    funext ξ
    rw [map_smul, smul_eq_mul]
  rw [e, fderiv_const_mul h2, map_smul, smul_eq_mul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end PairedEnergies
open PairedEnergies in
theorem pairedEnergiesCompare_holds (hEn : ChartEnergyDerivBounds)
    (hSC : ChartSlopeBoundNearBall) (hEm : PushforwardFieldProperties)
    (hGr : BondPartialDiffBound) (hNV : PairedCoordinatesAgree)
    (hLC : ImaginaryCoordinatesIsometric) : PairedEnergiesCompare := by
  intro a L c ha hodd hL hc
  obtain ⟨Ce, hCe, hE⟩ := hEn a L c ha hodd hL hc
  obtain ⟨Cs, hCs, hS⟩ := hSC a L c ha hodd hL hc
  refine ⟨Cs + Ce, by positivity, ?_⟩
  intro F F' w w' V V' Y Y' r r₂ θ ρ₂ ι _ _ j j' hT hT' ht hθ hρ hr1 hr hs hs' inj1 inj2 hm hgood hgood' hag hnear
  classical
  obtain ⟨hFL, _⟩ := id hT
  obtain ⟨hFL', _⟩ := id hT'
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hs₀ : 0 < c.s₀ := hc.classical.1.2.2.1
  have hs₀σ : c.s₀ ≤ c.σA := by linarith [hc.inequalities.2.2.1]
  obtain ⟨_, _, hnorm, _, _, hm0, _⟩ := id hLC
  have mono : ∀ {F₀ : BlockFrame} {p : F₀.Site F₀.depth → Fin 4 → imaginaryQuaternions} {V₀ : F₀.GaugeField F₀.top},
      IsAdmissibleChartPoint L c.s₀ p V₀ → IsAdmissibleChartPoint L c.σA p V₀ := fun h =>
    ⟨h.coord_small, fun p hp => (h.small_curvature p hp).trans_le hs₀σ⟩
  obtain ⟨_, _, ea1, _, _, _, hc1⟩ := hEm _ _ _ inj1
  obtain ⟨_, _, ea2, _, _, _, hc2⟩ := hEm _ _ _ inj2
  have g1 : ∀ ξ ∈ openPolyball (ι) ρ₂, IsAdmissibleChartPoint L c.σA (shiftCoordinates w (pushforwardField j ξ)) V :=
    fun ξ hξ => by
    have h := hgood ξ hξ 0 (fun b => by simpa using hθ)
    rw [hm0] at h
    exact mono h
  have g2 : ∀ ξ ∈ openPolyball (ι) ρ₂, IsAdmissibleChartPoint L c.σA (shiftCoordinates w' (pushforwardField j' ξ)) V' :=
    fun ξ hξ => mono (hgood' ξ hξ)
  have E1 := fun ξ hξ => hE F w (pushforwardField j ξ) V hT (g1 ξ hξ)
  have E2 := fun ξ hξ => hE F' w' (pushforwardField j' ξ) V' hT' (g2 ξ hξ)
  have c1 : ∀ ξ ∈ openPolyball (ι) ρ₂, ContDiffAt ℝ 3 (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) ξ :=
    fun ξ hξ => (hc1 3 _ ξ (E1 ξ hξ).1).1
  have c2 : ∀ ξ ∈ openPolyball (ι) ρ₂, ContDiffAt ℝ 3 (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) ξ :=
    fun ξ hξ => (hc2 3 _ ξ (E2 ξ hξ).1).1
  have hslope1 : ∀ ξ ∈ openPolyball (ι) ρ₂, ∀ (k : ι) (u : BondVector),
      chartedSlope a (shiftCoordinates w (pushforwardField j ξ)) V (j k).1 (toImaginary u) = bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ξ u :=
    fun ξ hξ k u => by
    have h1 := (E1 ξ hξ).2.1 (j k) u
    have h2 := (hc1 3 _ ξ (E1 ξ hξ).1).2.1 (by norm_num) (bondVariation k u)
    rw [ea1] at h2
    exact h1.trans h2.symm
  have hslope2 : ∀ ξ ∈ openPolyball (ι) ρ₂, ∀ (k : ι) (u : BondVector),
      chartedSlope a (shiftCoordinates w' (pushforwardField j' ξ)) V' (j' k).1 (toImaginary u) =
        bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ξ u := fun ξ hξ k u => by
    have h1 := (E2 ξ hξ).2.1 (j' k) u
    have h2 := (hc2 3 _ ξ (E2 ξ hξ).1).2.1 (by norm_num) (bondVariation k u)
    rw [ea2] at h2
    exact h1.trans h2.symm
  have hsides : ∀ i, 2 * r₂ + 2 ≤ 2 * r + 2 := fun _ => by omega
  have hnearξ : ∀ ξ, CoordinatesCloseOnBall L Y Y' r₂ θ (shiftCoordinates w (pushforwardField j ξ)) (shiftCoordinates w' (pushforwardField j' ξ)) := by
    intro ξ h₁ o₁ i₁ hh₁ ho₁ hch
    have hh₁' : WithinRadius r h₁ := fun i => (hh₁ i).trans (by exact_mod_cast hr)
    have hco := (hNV F F' Y Y' r ι j j' ξ h₁ o₁ i₁ (hFL.trans hFL'.symm) hoddF hs hs' inj1 inj2 hm hh₁'
      (by rw [hFL]; exact ho₁)).2
    have := hnear h₁ o₁ i₁ hh₁ ho₁ hch
    simp only [shiftCoordinates]
    rw [hco]
    refine le_trans (le_of_eq ?_) this
    congr 1
    simp only [Submodule.coe_add]
    abel
  refine ⟨fun ξ hξ => (c1 ξ hξ).contDiffWithinAt, fun ξ hξ => (c2 ξ hξ).contDiffWithinAt, fun ξ hξ k u =>
    ⟨hslope1 ξ hξ k u, hslope2 ξ hξ k u⟩, ?_⟩
  intro ρ₁ hh hh0 hρ₁ hρ₁₂ ξ hξ k l h o i u u' hbox hk hek
  obtain ⟨û, hû, hue⟩ := exists_norm_eq_one_smul u
  obtain ⟨û', hû', hue'⟩ := exists_norm_eq_one_smul u'
  have ho := isOpen_openPolyball (ι := ι) ρ₂
  have P1 : ContDiffOn ℝ 2 (fun ζ => bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ζ û) (openPolyball _ ρ₂) :=
    fun ζ hζ => (((c1 ζ hζ).fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).contDiffWithinAt
  have P2 : ContDiffOn ℝ 2 (fun ζ => bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ζ û) (openPolyball _ ρ₂) :=
    fun ζ hζ => (((c2 ζ hζ).fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).contDiffWithinAt
  have hnearP : ∀ ζ ∈ openPolyball (ι) ρ₂,
      |bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ζ û - bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ζ û| ≤
        (Cs + Ce) * (θ + Real.exp (-(c.δ₂ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1)))) := fun ζ hζ => by
    have h1 := hS F F' (shiftCoordinates w (pushforwardField j ζ)) (shiftCoordinates w' (pushforwardField j' ζ)) V V' Y Y' r₂ θ hr1 hT hT' ht hθ
      (hgood ζ hζ) (hgood' ζ hζ) hag (hnearξ ζ) h o i (toImaginary û) hbox (by rw [hnorm, hû])
    rw [← hk, ← hek, hslope1 ζ hζ k û, hslope2 ζ hζ k û, abs_sub_comm] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hthird1 : ∀ ζ ∈ openPolyball (ι) ρ₂, ∀ (l' : ι) (v : BondVector), ‖v‖ = 1 →
      |secondDerivAlong (fun ζ => bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ζ û) ζ (bondVariation l' v) (bondVariation l' v)| ≤
        Cs + Ce := fun ζ hζ l' v hv => by
    have h1 := (hc1 3 _ ζ (E1 ζ hζ).1).2.2.2 (by norm_num) (bondVariation k û) (bondVariation l' v) (bondVariation l' v)
    rw [ea1, ea1] at h1
    have h2 := (E1 ζ hζ).2.2.2 (j k) (j l') (j l') û v v
    rw [hû, hv] at h2
    have h3 : |thirdDerivAlong (fun z => chartedEnergyAt a w V (pushforwardField j z)) ζ
        (bondVariation k û) (bondVariation l' v) (bondVariation l' v)| ≤ Ce * 1 * 1 * 1 := by
      rw [h1]
      exact h2
    refine le_trans (le_of_eq ?_) (h3.trans (by simp only [mul_one]; linarith))
    rfl
  have hthird2 : ∀ ζ ∈ openPolyball (ι) ρ₂, ∀ (l' : ι) (v : BondVector), ‖v‖ = 1 →
      |secondDerivAlong (fun ζ => bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ζ û) ζ (bondVariation l' v) (bondVariation l' v)| ≤
        Cs + Ce := fun ζ hζ l' v hv => by
    have h1 := (hc2 3 _ ζ (E2 ζ hζ).1).2.2.2 (by norm_num) (bondVariation k û) (bondVariation l' v) (bondVariation l' v)
    rw [ea2, ea2] at h1
    have h2 := (E2 ζ hζ).2.2.2 (j' k) (j' l') (j' l') û v v
    rw [hû, hv] at h2
    have h3 : |thirdDerivAlong (fun z => chartedEnergyAt a w' V' (pushforwardField j' z)) ζ
        (bondVariation k û) (bondVariation l' v) (bondVariation l' v)| ≤ Ce * 1 * 1 * 1 := by
      rw [h1]
      exact h2
    refine le_trans (le_of_eq ?_) (h3.trans (by simp only [mul_one]; linarith))
    rfl
  have key := hGr _ ρ₁ ρ₂ hh _ _ _ _ hh0 hρ₁ hρ₁₂ P2 P1 hnearP hthird2 hthird1 ξ hξ l û' hû'
  have hball : ξ ∈ openPolyball (ι) ρ₂ := fun b => (hξ b).trans (by linarith)
  have s1 := secondDerivAlong_smul_smul ((c1 ξ hball).of_le (by norm_num)) ‖u‖ ‖u'‖ (bondVariation k û) (bondVariation l û')
  have s2 := secondDerivAlong_smul_smul ((c2 ξ hball).of_le (by norm_num)) ‖u‖ ‖u'‖ (bondVariation k û) (bondVariation l û')
  rw [← bondVariation_smul, ← bondVariation_smul, ← hue, ← hue'] at s1 s2
  rw [s1, s2, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have hcancelled' : |secondDerivAlong (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) ξ (bondVariation k û) (bondVariation l û') -
      secondDerivAlong (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) ξ (bondVariation k û) (bondVariation l û')| ≤ _ := key
  calc _ ≤ ‖u‖ * ‖u'‖ * _ := mul_le_mul_of_nonneg_left hcancelled' (by positivity)
    _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
