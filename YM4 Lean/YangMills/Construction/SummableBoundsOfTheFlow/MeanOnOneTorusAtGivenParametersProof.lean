import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSizedSumsProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfADerivativeOfAnExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfAnExpansionIsInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorusAtGivenParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TopDerivativesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.Estimates YangMills.Construction.Cumulants YangMills.Construction.LawAtTop YangMills.Construction.ConvexObservables YangMills.Construction.FamilyNorms
open YangMills.Construction.BlockAverages hiding bondSpread
namespace YangMills.Construction.BlockMeans
variable {F : BlockFrame}
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
theorem bondDeriv_fin_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G V c X = G V := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.bondDeriv_zero <;> assumption
section Forms
variable {ι : Type} [Fintype ι]
theorem ballDensity_eq_zero_of_not_forall_lt {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {η : BondField ι}
    (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballDensity_eq_zero_of_not_mem <;> assumption
theorem ballDensity_congr_on_balls {ρ : ℝ} {p : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = Ψ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by apply _root_.YangMills.Construction.Cumulants.SizedSums.ballDensity_congr <;> assumption
theorem isPositiveUnitalForm_of_eqOn_balls {ρ : ℝ} {p : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (Fm : IsPositiveUnitalForm ρ p Ψ)
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = Ψ η) : IsPositiveUnitalForm ρ p Φ := by
  have e : ∀ f, ballExpectation (cutoffFactor ρ p) Φ f = ballExpectation (cutoffFactor ρ p) Ψ f := fun f => by
    simp only [ballExpectation, ballDensity_congr_on_balls h]
  refine ⟨?_, fun f g hfg => ?_, fun Ψ' f hΨ' => ?_, fun f g hf hg hfg => ?_, fun f g hf hg => ?_, fun c f => ?_⟩
  · rw [e]
    exact Fm.map_one
  · rw [e, e]
    exact Fm.congr_on f g hfg
  · rw [e]
    exact Fm.congr_potential Ψ' f fun η hη => by rw [← h η hη]; exact hΨ' η hη
  · rw [e, e]
    exact Fm.mono f g hf hg hfg
  · rw [e, e, e]
    exact Fm.map_add f g hf hg
  · rw [e, e]
    exact Fm.map_smul c f
theorem integrable_mul_ballDensity {ρ : ℝ} {p : ℝ → ℝ} {Φ f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f)
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Φ)) :
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Φ η := by
  classical
  obtain ⟨hc, D, hD⟩ := hf
  set U : Set (BondField ι) := openPolyball ι ρ with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU, openPolyball]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  set g : BondField ι → ℝ := U.indicator f with hg
  have hgm : AEStronglyMeasurable g volume :=
    (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr (hc.aestronglyMeasurable hUo.measurableSet)
  have hgb : ∀ η, ‖g η‖ ≤ |D| := fun η => by
    by_cases hη : η ∈ U
    · rw [hg, Set.indicator_of_mem hη, Real.norm_eq_abs]
      exact (hD η hη).trans (le_abs_self _)
    · rw [hg, Set.indicator_of_notMem hη, norm_zero]
      exact abs_nonneg _
  have hmul := hI.bdd_mul hgm (Filter.Eventually.of_forall hgb)
  refine hmul.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ U
  · simp only [hg, Set.indicator_of_mem hη]
  · simp only [hg, Set.indicator_of_notMem hη, zero_mul]
    have : ¬ ∀ b, ‖η b‖ < ρ := hη
    rw [ballDensity_eq_zero_of_not_forall_lt this, mul_zero]
end Forms
theorem runningMax_ite_le {ε ε₃ : ℝ} (h1 : ε ≤ ε₃) (h0 : 0 ≤ ε₃) (j : ℕ) :
    runningMax (fun j => if j = 3 then ε₃ else ε) j ≤ ε₃ := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    refine max_le ih ?_
    beta_reduce
    split_ifs
    · exact le_rfl
    · exact h1
theorem ballCovariance_sub_sum {ι α : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Φ f g₁ G : BondField ι → ℝ}
    {S : Finset α} {g₂ : α → BondField ι → ℝ} (Fm : IsPositiveUnitalForm ρ p Φ) (hf : IsBoundedContinuousOn ι ρ f)
    (h₁ : IsBoundedContinuousOn ι ρ g₁) (h₂ : ∀ y ∈ S, IsBoundedContinuousOn ι ρ (g₂ y))
    (hG : ∀ η ∈ openPolyball ι ρ, G η = g₁ η - ∑ y ∈ S, g₂ y η) :
    ballCovariance (cutoffFactor ρ p) Φ f G =
      ballCovariance (cutoffFactor ρ p) Φ f g₁ - ∑ y ∈ S, ballCovariance (cutoffFactor ρ p) Φ f (g₂ y) := by
  have hs : IsBoundedContinuousOn ι ρ (fun η => ∑ y ∈ S, g₂ y η) := IsBoundedContinuousOn.sum S g₂ h₂
  have hfs : IsBoundedContinuousOn ι ρ (fun η => ∑ y ∈ S, f η * g₂ y η) :=
    IsBoundedContinuousOn.sum S _ fun y hy => hf.mul (h₂ y hy)
  have m2 : ballExpectation (cutoffFactor ρ p) Φ G =
      ballExpectation (cutoffFactor ρ p) Φ g₁ - ∑ y ∈ S, ballExpectation (cutoffFactor ρ p) Φ (g₂ y) := by
    rw [Fm.congr_on G (fun η => g₁ η - ∑ y ∈ S, g₂ y η) hG, Fm.map_sub h₁ hs, Fm.map_sum S g₂ h₂]
  have m1 : ballExpectation (cutoffFactor ρ p) Φ (fun η => f η * G η) =
      ballExpectation (cutoffFactor ρ p) Φ (fun η => f η * g₁ η) -
        ∑ y ∈ S, ballExpectation (cutoffFactor ρ p) Φ (fun η => f η * g₂ y η) := by
    rw [Fm.congr_on (fun η => f η * G η) (fun η => f η * g₁ η - ∑ y ∈ S, f η * g₂ y η) (fun η hη => by
      rw [hG η hη, mul_sub, Finset.mul_sum]), Fm.map_sub (hf.mul h₁) hfs,
      Fm.map_sum S (fun y η => f η * g₂ y η) fun y hy => hf.mul (h₂ y hy)]
  unfold ballCovariance
  rw [m1, m2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
theorem singleTorusMeanConstant_bounds {Cs E η₃ B W Cg Cm Cth N₀ ε w CE : ℝ} (hCs : 0 ≤ Cs) (hE : 0 ≤ E)
    (hη : 0 < η₃) (hB : 0 ≤ B) (hW : 0 ≤ W) (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm) (hCth : 0 ≤ Cth) (hN₀ : 0 ≤ N₀)
    (hε : 0 < ε) (hw : 0 < w)
    (hK : singleTorusMeanConstant Cs E η₃ B W Cg Cm Cth N₀ ≤ CE) :
    N₀ * (Cg * (ε / η₃)) * W * (w / 2 + Cm * w ^ 2 / (2 * w)) +
        3 * (B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃)))) +
        B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃)) ^ 2) ≤ CE * ε * w ∧
    6 * (B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃)))) +
        (B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃))) + 2 * (Cs * Cth * (E / η₃) * (Cs * ε * w))) +
        6 * (B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃)) ^ 2)) +
        B * (Cs * (ε / η₃) * w * (Cs * (1 + E / η₃)) ^ 3) ≤ CE * ε * w := by
  set β := Cs * (1 + E / η₃) with hβ
  set a₀ := Cs / η₃ with ha₀
  set k₁ := N₀ * Cg * W * (1 + Cm) / (2 * η₃) with hk₁
  set k₅ := 2 * Cs ^ 2 * Cth * (E / η₃) with hk₅
  have hk₁0 : 0 ≤ k₁ := by positivity
  have hk₅0 : 0 ≤ k₅ := by positivity
  have u1 : 0 ≤ B * a₀ * β := by positivity
  have u2 : 0 ≤ B * a₀ * β ^ 2 := by positivity
  have u3 : 0 ≤ B * a₀ * β ^ 3 := by positivity
  have hKe : k₁ + k₅ + 7 * B * a₀ * β + 7 * B * a₀ * β ^ 2 + B * a₀ * β ^ 3 ≤ CE := hK
  have he : 0 < ε * w := by positivity
  have hh : w / 2 + Cm * w ^ 2 / (2 * w) = w * (1 + Cm) / 2 := by
    field_simp
  constructor
  · have e : N₀ * (Cg * (ε / η₃)) * W * (w / 2 + Cm * w ^ 2 / (2 * w)) +
        3 * (B * (Cs * (ε / η₃) * w * β)) + B * (Cs * (ε / η₃) * w * β ^ 2) =
        ε * w * (k₁ + 3 * (B * a₀ * β) + B * a₀ * β ^ 2) := by
      rw [hh, hk₁, ha₀]
      ring
    rw [e]
    calc ε * w * (k₁ + 3 * (B * a₀ * β) + B * a₀ * β ^ 2) ≤ ε * w * CE :=
          mul_le_mul_of_nonneg_left (by nlinarith) he.le
      _ = CE * ε * w := by ring
  · have e : 6 * (B * (Cs * (ε / η₃) * w * β)) + (B * (Cs * (ε / η₃) * w * β) + 2 * (Cs * Cth * (E / η₃) * (Cs * ε * w))) +
        6 * (B * (Cs * (ε / η₃) * w * β ^ 2)) + B * (Cs * (ε / η₃) * w * β ^ 3) =
        ε * w * (k₅ + 7 * (B * a₀ * β) + 6 * (B * a₀ * β ^ 2) + B * a₀ * β ^ 3) := by
      rw [hk₅, ha₀]
      ring
    rw [e]
    calc ε * w * (k₅ + 7 * (B * a₀ * β) + 6 * (B * a₀ * β ^ 2) + B * a₀ * β ^ 3) ≤ ε * w * CE :=
          mul_le_mul_of_nonneg_left (by nlinarith) he.le
      _ = CE * ε * w := by ring
theorem hasBoundedDerivatives_of_isNormBoundedLocalFamily {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
theorem exponentSum_eq_stepExponent {star : Bool} {a ρA ρ x κ C : ℝ} {m : ℕ} (φ : LocalFamily)
    {V : F.GaugeField F.top} (hB : CellExponentBounds star a ρA ρ x κ C m V)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    exponentSum star a ρA x m φ η V = stepExponent star a ρA x m φ 1 V η := by
  have h1 : stepExponent star a ρA x m φ 1 V η = stepExponent star a ρA x m (fun _ _ _ => 0) 0 V η -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m φ y η V := by
    simp [stepExponent]
  rw [h1, hB.sum_eq η hη]
  unfold exponentSum
  rw [Fintype.sum_sum_type]
  simp only [exponentTerm, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
  rw [Finset.sum_coe_sort (finiteCells F) (fun Y => cellExponent star a ρA x m Y V η),
    Finset.sum_coe_sort (sitesOfCells (finiteCells F) F.depth) (fun y => centredExpansion star a ρA m φ y η V)]
  ring
set_option maxHeartbeats 3000000 in
theorem singleTorusMeanAtSlots_holds (hLT : lawAtTopFromInterpolatedFrames)
    (hExpn : GibbsMeanExpansionInField) (hTop : meanAtTopStatement) (hInv : conditionalExpansionMeanInvariantStatement)
    (hExpansionM : meanFieldDerivNearValueStatement) (hTD : fieldDerivRegularityStatement)
    (hEnds : interpolationAtEndpoints) (hJ : JointlyContDiffOnBallsOfDisplacements)
    (hMeans : CutoffExpectationIsPositiveForm) (hRim : CutoffMeanIsGibbsMean)
    (hBW : GibbsMeanBounds) (hCh : chartEquivarianceStatement)
    (hSB : SiteDecomposition) (hLaw : normalizedBallLawIsProbabilityStatement) :
    singleTorusMeanAtSlotsStatement := by
  classical
  intro T Cq Cz Cr C Ck Cth B W CE hT hK t x φ h ε star hx hε hφ hr
  have hD := hT.ordered
  have hκ := hD.κ_pos
  have hσ := hD.σ_pos
  have hη₃ := hD.η₃_pos
  have hη₁ := hD.η₃_le_one
  have hE1 : 1 ≤ T.E := hD.one_le_E
  have hCs1 : 1 ≤ T.Cs := hT.one_le_Cs
  have hCs0 : 0 ≤ T.Cs := by linarith
  have hx1 : 1 ≤ x := hT.one_le_coupling.trans hx
  have hx0 : 0 < x := by linarith
  have hρ : 0 < T.σ / 64 := by positivity
  have hE0 : 0 < T.E := by linarith
  have hε₃ : 0 < ε / T.η₃ := by positivity
  have hE₃ : 0 < T.E / T.η₃ := by positivity
  have hεle : ε ≤ ε / T.η₃ := by
    rw [le_div_iff₀ hη₃]
    nlinarith
  have hh : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h :=
    ⟨hr.smooth, hr.gauge_invariant, hr.translation_invariant, hr.decay, hr.locality⟩
  set s : ℝ := segmentEnd star with hs
  have hs0 : 0 ≤ s := by
    simp only [hs, segmentEnd]
    split_ifs <;> norm_num
  have hs1 : s ≤ 1 := by
    simp only [hs, segmentEnd]
    split_ifs <;> norm_num
  set m := frameRadius x with hm
  set w := x ^ (-(1 / 2 : ℝ)) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hw2 : x⁻¹ = w ^ 2 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
    rw [Real.rpow_neg_one]
  set Cm := |Cq 1| with hCm
  set Cth' := 1 + ∑ q ∈ Finset.range 7, Cth q with hCth'
  have hCth0 : 0 ≤ Cth' := by
    have : 0 ≤ ∑ q ∈ Finset.range 7, Cth q := Finset.sum_nonneg fun q _ => hT.Cth_nonneg q
    linarith
  set N₀ : ℝ := ((centredCube T.L).card : ℝ) with hN₀
  have hN₀0 : 0 ≤ N₀ := Nat.cast_nonneg _
  obtain ⟨num1, num3⟩ := singleTorusMeanConstant_bounds hCs0 hE0.le hη₃ hT.B_nonneg hT.W_nonneg hT.C_pos.le
    (abs_nonneg _) hCth0 hN₀0 hε hw0 hK
  have hrowAll : ∀ (f : LocalFamily) (F : BlockFrame) (y : F.Site F.depth),
      interpolatedExpansion s T.a T.chainParams.ρA m f y = centredExpansion star T.a T.chainParams.ρA m f y := fun f F y => by
    funext η V'
    exact (hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.1 f y η
  have top : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V →
      HasConditionalMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h Y V ∧
      ContDiffThreeAlongBonds (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V ∧
      (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
        |bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V c X -
          bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA m h Y 0) V c X| ≤
          CE * ε * w * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))) ∧
      ∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
        |bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V c X| ≤
          2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
            CE * ε * w * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
    intro F hF Y V hV
    obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
    have hn2 : 2 ≤ n := hT.two_le.trans hn
    have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hside]
      exact hn2
    have hodd : Odd F.blockSide := by
      rw [hFL]
      exact hD.odd_L
    have hfin : Finite F.Cell := by
      have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
      have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
        rw [hper, hside]
        omega⟩
      exact Pi.finite
    obtain ⟨hL, hmom⟩ := hLT T Cq Cz Cr C Ck hT.toLawAtTopHypotheses t x ε φ h star F V hx hε hφ hh hF hV
    obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F (T.σ / 64) T.p hρ hD.cutoff
    have TD := hTD F (T.σ / 64) V
    have hμc : ∀ᵐ η ∂(cutoffLaw F (T.σ / 64) T.p), ∀ b, ‖η b‖ ≤ T.σ / 64 := by
      filter_upwards [hμb] with η hη b using (hη b).le
    have expansionJoint : ∀ {ε' ε₃' : ℝ} {f : LocalFamily}, IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε' ε₃' f →
        0 ≤ ε' → 0 ≤ ε₃' →
        ∀ y, JointlyContDiffOnBalls (T.σ / 64) V (centredExpansion star T.a T.chainParams.ρA m f y) := by
      intro ε' ε₃' f hf h0 h3 y
      refine hJ F (T.σ / 64) V _ fun η hη l j b u c X hu hX => ?_
      have tr := hT.transport x t 3 _ f F V s η hx le_rfl (by norm_num)
        (fun j => by split_ifs <;> assumption) (hasBoundedDerivatives_of_isNormBoundedLocalFamily hf) hF hV hs0 hs1 hη
      have h3' := tr.smooth y l j b u c X hu hX
      rw [hrowAll] at h3'
      exact_mod_cast h3'
    have expansionφ := expansionJoint hφ hE0.le hE₃.le
    have rowh := expansionJoint hh hε.le hε₃.le
    set A : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := exponentSum star T.a T.chainParams.ρA x m φ with hA
    set H : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := cellExpansionInField star T.a T.chainParams.ρA m h Y with hH
    have hAS : A = fun η V' => ∑ q ∈ Finset.univ, exponentTerm star T.a T.chainParams.ρA x m φ q η V' := rfl
    have hHS : H = fun η V' => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        centredExpansion star T.a T.chainParams.ρA m h y η V' := rfl
    have hAJ : JointlyContDiffOnBalls (T.σ / 64) V A := fun k c X η hη => by
      rw [hAS]
      exact ContDiffAt.sum fun q _ => hL.smooth_term q k c X η hη
    have hHJ : JointlyContDiffOnBalls (T.σ / 64) V H := fun k c X η hη => by
      rw [hHS]
      exact ContDiffAt.sum fun y _ => rowh y k c X η hη
    obtain ⟨hsmooth, hexp⟩ := hExpn F (T.σ / 64) (cutoffLaw F (T.σ / 64) T.p) V A H hfinμ hμ0 hμc hAJ hHJ
    have eqAt : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
        conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y V' =
          gibbsMeanAt (cutoffLaw F (T.σ / 64) T.p) A H V' := fun V' hV' => by
      have hB' := (hT.exponents t x F V' star hx hF hV').1
      unfold conditionalExpansionMean gibbsMeanAt
      rw [hμm]
      refine gibbsMean_congr_ae ?_ Filter.EventuallyEq.rfl
      filter_upwards [hμb] with η hη using (exponentSum_eq_stepExponent φ hB' hη).symm
    have evAt : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        (fun τ : Fin k → ℝ => conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y
            (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
          fun τ => gibbsMeanAt (cutoffLaw F (T.σ / 64) T.p) A H (leftTranslate (bondSpread c X τ) V) := fun k c X => by
      filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hV] with τ hτ using eqAt _ hτ
    have hder : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V c X =
          bondDeriv (gibbsMeanAt (cutoffLaw F (T.σ / 64) T.p) A H) V c X := fun k c X => by
      unfold bondDeriv
      rw [((evAt k c X).iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
    have hsmM : ContDiffThreeAlongBonds (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V :=
      fun k c X => (hsmooth k c X).congr_of_eventuallyEq (evAt k c X)
    have hmean : ∀ f, gibbsMean (cutoffLaw F (T.σ / 64) T.p) (fun η => A η V) f =
        ballExpectation (cutoffFactor (T.σ / 64) T.p) (fun η => A η V) f := fun f => (hμm _ f).symm
    obtain ⟨Ψ', K', hag, hconv, -⟩ := hL.convex
    have hcont' : Continuous Ψ' := hconv.smooth.continuous
    have Fm : IsPositiveUnitalForm (T.σ / 64) T.p (fun η => A η V) :=
      isPositiveUnitalForm_of_eqOn_balls (hMeans _ (T.σ / 64) T.p Ψ' hρ hD.cutoff hcont') hag
    have hH0 : (fun η => H η V) =
        fieldDeriv H V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) := by
      funext η
      unfold fieldDeriv
      rw [bondDeriv_fin_zero]
    have niceOf : ∀ {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
        (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        JointlyContDiffOnBalls (T.σ / 64) V G → k ≤ 3 →
        IsBoundedContinuousOn ↥(chordBonds (finiteCells F)) (T.σ / 64) (fieldDeriv G V c X) := fun G c X hG hk => by
      obtain ⟨Bd, hBd⟩ := TD.bounded G _ c X hG hk
      exact ⟨TD.continuousOn G _ c X hG hk, Bd, fun η hη => hBd η fun b => (hη b).le⟩
    have hNiceH : IsBoundedContinuousOn ↥(chordBonds (finiteCells F)) (T.σ / 64) (fun η => H η V) := by
      rw [hH0]
      exact niceOf H _ _ hHJ (by norm_num)
    have hIsMean : HasConditionalMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h Y V := by
      obtain ⟨-, -, -, -, -, -, hI, hP, -⟩ := hLaw _ (T.σ / 64) T.p Ψ' hρ hD.cutoff hcont'
      have hB' := (hT.exponents t x F V star hx hF hV).1
      have hd : ballDensity (cutoffFactor (T.σ / 64) T.p) (stepExponent star T.a T.chainParams.ρA x m φ 1 V) =
          ballDensity (cutoffFactor (T.σ / 64) T.p) Ψ' :=
        ballDensity_congr_on_balls fun η hη => (exponentSum_eq_stepExponent φ hB' hη).symm.trans (hag η hη)
      have hI' : Integrable (ballDensity (cutoffFactor (T.σ / 64) T.p) (stepExponent star T.a T.chainParams.ρA x m φ 1 V)) := by
        rw [hd]
        exact hI
      refine ⟨hI', ?_, integrable_mul_ballDensity hNiceH hI'⟩
      have : 0 < ∫ η, ballDensity (cutoffFactor (T.σ / 64) T.p) (stepExponent star T.a T.chainParams.ρA x m φ 1 V) η := by
        rw [hd]
        exact hP
      exact this
    set α := T.Cs * (ε / T.η₃) * w with hα
    set β := T.Cs * (1 + T.E / T.η₃) with hβ
    have hα0 : 0 ≤ α := by positivity
    have hβ0 : 0 ≤ β := by positivity
    have hsm := hT.cumulants F star x m α β φ h V hL Y
    have hCe : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4), Real.exp (-(T.κ / 16 * (bondSpan Y c : ℝ))) ≤
        Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := fun c => by
      refine Real.exp_le_exp.mpr ?_
      have h0 : (0 : ℝ) ≤ (bondSpan Y c : ℝ) := Nat.cast_nonneg _
      have : T.κ / 2 ^ 6 * (bondSpan Y c : ℝ) ≤ T.κ / 16 * (bondSpan Y c : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        norm_num
        linarith
      linarith
    have hSBF := hSB F hodd hs2
    have hcard : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤ N₀ := by
      have h1 : ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤
          (centredCube F.blockSide).card := by
        refine Finset.card_le_card_of_injOn cellOffset (fun y _ => (hSBF.2.1 y).2) ?_
        intro y hy y' hy' he
        have hy1 : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
        have hy2 : enclosingCell y' = Y := (Finset.mem_filter.mp hy').2
        have h3 := (hSBF.2.1 y).1
        have h4 := (hSBF.2.1 y').1
        rw [hy1, he] at h3
        rw [hy2] at h4
        exact h3.symm.trans h4
      rw [hFL] at h1
      rw [hN₀]
      exact_mod_cast h1
    have hgrad : ∀ (y : F.Site F.depth) (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
        (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        (∀ b, ‖ζ b‖ ≤ T.σ / 64) → ‖u‖ = 1 → k ≤ 2 → AreUnitVectors X →
        |jointMixedDeriv (centredExpansion star T.a T.chainParams.ρA m h y) ζ V ![b] ![u] c X| ≤ C * (ε / T.η₃) *
          Real.exp (-(2 ^ 7 * T.κ * cellSetDiameter (insert (enclosingCell y)
            (chordBondCells ![b] ∪ topBondCells c)))) := by
      intro y ζ b u k c X hζ hu hk hX
      have tr := hT.transport x t 3 _ h F V s ζ hx le_rfl (by norm_num)
        (fun j => by
          split_ifs
          · exact hε₃.le
          · exact hε.le) (hasBoundedDerivatives_of_isNormBoundedLocalFamily hh) hF hV hs0 hs1 hζ
      have g := tr.jointDeriv_le y 1 k ![b] ![u] c X (by omega) (by omega)
        (by intro i; fin_cases i; exact hu) hX
      rw [hrowAll] at g
      refine g.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_left (runningMax_ite_le hεle hε₃.le _) hT.C_pos.le
    have hmomB : ∀ b : ↥(chordBonds (finiteCells F)),
        ballExpectation (cutoffFactor (T.σ / 64) T.p) (fun η => A η V) (fun η => ‖η b‖ ^ 2) ≤ Cm * w ^ 2 := fun b => by
      refine (hmom b).trans ?_
      rw [hw2]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    have hnear : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        AreUnitVectors X →
        |gibbsMean (cutoffLaw F (T.σ / 64) T.p) (fun η => A η V) (fieldDeriv H V c X) - fieldDeriv H V c X 0| ≤
          N₀ * (C * (ε / T.η₃)) * W * (w / 2 + Cm * w ^ 2 / (2 * w)) *
            Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      intro k c X hk hX
      rw [hmean]
      exact hExpansionM F star T.a T.chainParams.ρA m (T.σ / 64) T.κ C (ε / T.η₃) W N₀ (Cm * w ^ 2) w T.p (fun η => A η V) h V Y
        hρ hκ hT.C_pos.le hε₃.le hw0 hT.W_nonneg hN₀0 (by positivity) rowh Fm hgrad hmomB (hT.weight_sum_le t F hF Y)
        hcard k c X hk hX
    have rt := ((hT.familyTransport ε hε) t x h F V hx hr hF hV star).1
    have hmid : ∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
        |gibbsMean (cutoffLaw F (T.σ / 64) T.p) (fun η => A η V) (fieldDeriv H V c X)| ≤
          2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
      intro c X hX
      have key : ∀ᵐ η ∂(cutoffLaw F (T.σ / 64) T.p), |fieldDeriv H V c X η| ≤
          2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
        filter_upwards [hμb] with η hη using rt.thirdDeriv Y η c X hη hX
      have h00 : 0 ≤ 2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
        (abs_nonneg _).trans (rt.thirdDeriv Y 0 c X (fun b => by
          rw [show ‖(0 : StepVariable (finiteCells F)) b‖ = 0 by simp]; exact hρ) hX)
      exact (hBW _ _ (fun η => A η V) _ _ _ _ _ _ _ _ h00 h00 h00 h00 key key key key).1
    have one := (hT.frames t x hx).one_torus F V s hF hV hs0 hs1
    obtain ⟨Th, hTh, -⟩ := one.variation
    have hCJ : JointlyContDiffOnBalls (T.σ / 64) V (cellExponentTotal star T.a T.chainParams.ρA x m φ) :=
      fun k c X η hη => by
      have e : (cellExponentTotal star T.a T.chainParams.ρA x m φ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
          fun η V' => ∑ Z ∈ (Finset.univ : Finset ↥(finiteCells F)),
            exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inl Z) η V' := rfl
      rw [e]
      exact ContDiffAt.sum fun Z _ => hL.smooth_term (Sum.inl Z) k c X η hη
    have hdF : ballDensity (cutoffFactor (T.σ / 64) T.p) (familyLawExponent s T.a T.chainParams.ρA x m φ V) =
        ballDensity (cutoffFactor (T.σ / 64) T.p) (fun η => A η V) := by
      have hB' := (hT.exponents t x F V star hx hF hV).1
      refine ballDensity_congr_on_balls fun η hη => ?_
      rw [(hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V).2.2.2.2.2.1 φ η]
      exact (exponentSum_eq_stepExponent φ hB' hη).symm
    have hblk : (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA m h Y η V) = fun η => H η V := by
      funext η
      simp only [hH, cellExpansionInField, interpolatedBlockExpansion, cellCentredExpansion, hrowAll]
    have hcov : ∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
        |ballCovariance (cutoffFactor (T.σ / 64) T.p) (fun η => A η V) (fun η => H η V) (fieldDeriv A V c X)| ≤
          (B * (α * β) + 2 * (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w))) *
            Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
      intro c X hX
      have hG : ∀ η ∈ openPolyball ↥(chordBonds (finiteCells F)) (T.σ / 64), fieldDeriv A V c X η =
          fieldDeriv (cellExponentTotal star T.a T.chainParams.ρA x m φ) V c X η -
            ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
              fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y) V c X η := fun η hη => by
        have hcl : ∀ b, ‖η b‖ ≤ T.σ / 64 := fun b => (hη b).le
        have e1 := TD.sum (TermPlace F) Finset.univ (exponentTerm star T.a T.chainParams.ρA x m φ) 3 c X η
          (fun q _ => hL.smooth_term q) le_rfl hcl
        have e2 := TD.sum ↥(finiteCells F) Finset.univ
          (fun Z => exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inl Z)) 3 c X η
          (fun Z _ => hL.smooth_term (Sum.inl Z)) le_rfl hcl
        have e3 : ∀ y : ↥(sitesOfCells (finiteCells F) F.depth),
            fieldDeriv (exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inr y)) V c X η =
              - fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y.1) V c X η := fun y => by
          unfold fieldDeriv bondDeriv
          have : (fun τ : Fin 3 → ℝ => exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inr y) η
                (leftTranslate (bondSpread c X τ) V)) =
              - fun τ : Fin 3 → ℝ => centredExpansion star T.a T.chainParams.ρA m φ y.1 η (leftTranslate (bondSpread c X τ) V) := rfl
          rw [this, iteratedFDeriv_neg_apply]
          rfl
        have e4 : fieldDeriv A V c X η = ∑ q, fieldDeriv (exponentTerm star T.a T.chainParams.ρA x m φ q) V c X η := e1
        have e5 : fieldDeriv (cellExponentTotal star T.a T.chainParams.ρA x m φ) V c X η =
            ∑ Z : ↥(finiteCells F), fieldDeriv (exponentTerm star T.a T.chainParams.ρA x m φ (Sum.inl Z)) V c X η := e2
        rw [e4, e5, Fintype.sum_sum_type]
        simp only [e3, Finset.sum_neg_distrib]
        rw [Finset.sum_coe_sort (sitesOfCells (finiteCells F) F.depth)
          (fun y => fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y) V c X η)]
        ring
      rw [ballCovariance_sub_sum Fm hNiceH (niceOf _ c X hCJ le_rfl) (fun y _ => niceOf _ c X (expansionφ y) le_rfl) hG]
      have c1 := hsm.cov_cellSum 0 3 3 Fin.elim0 Fin.elim0 c X c (by norm_num) (by norm_num) (fun l => l.elim0) hX
        (fun l => Or.inr ⟨l, rfl⟩)
      rw [← hH0] at c1
      have cl := hT.blockExpansion t x s ε φ h F V Y c X Th hx hs0 hs1 hε hφ hh hF hV hX hTh
      have hα' : 0 < T.Cs * ε * w := by positivity
      have th := hT.thirdOrder t x s (T.Cs * ε * w) (T.Cs * ε * w) φ φ F V Y c X Th _ hx hs0 hs1 hα' hα'.le hφ hφ hF hV hX
        hTh cl
      have hterm : ∀ y ∈ sitesOfCells (finiteCells F) F.depth,
          ballCovariance (cutoffFactor (T.σ / 64) T.p) (fun η => A η V) (fun η => H η V)
            (fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y) V c X) =
          ballCovariance (cutoffFactor T.ballRadius T.p) (familyLawExponent s T.a T.chainParams.ρA x m φ V)
            (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA m h Y η V)
            (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA m φ y η) V c X) := fun y _ => by
        have e6 : (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA m φ y η) V c X) =
            fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y) V c X := by
          funext η
          rw [hrowAll]
          rfl
        rw [e6, hblk]
        change _ = ballCovariance (cutoffFactor (T.σ / 64) T.p) _ _ _
        simp only [ballCovariance, ballExpectation, hdF]
      have h3 : |∑ y ∈ sitesOfCells (finiteCells F) F.depth, ballCovariance (cutoffFactor (T.σ / 64) T.p)
          (fun η => A η V) (fun η => H η V) (fieldDeriv (centredExpansion star T.a T.chainParams.ρA m φ y) V c X)| ≤
          2 * (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w)) * Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.sum_congr rfl fun y hy => by rw [hterm y hy]]
        refine th.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        have hw1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
        have hq : 0 ≤ T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w) := by positivity
        have e7 : T.Cs * (1 + ∑ q ∈ Finset.range 7, Cth q) * T.energyRatio *
            (T.Cs * ε * w + x ^ (-(1 / 2 : ℝ)) * (T.Cs * ε * w)) =
            (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w)) * (1 + w) := by
          simp only [StepParameters.energyRatio, hCth', hw]
          ring
        rw [e7]
        nlinarith
      have h4 : Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ))) ≤ Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := by
        refine Real.exp_le_exp.mpr ?_
        have h0 : (0 : ℝ) ≤ (bondSpan Y c : ℝ) := Nat.cast_nonneg _
        have : T.κ / 2 ^ 6 * (bondSpan Y c : ℝ) ≤ T.κ / 2 ^ 5 * (bondSpan Y c : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ h0
          norm_num
          linarith
        linarith
      have hB0 : 0 ≤ B * (α * β) := mul_nonneg hT.B_nonneg (mul_nonneg hα0 hβ0)
      have hk0 : 0 ≤ 2 * (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w)) := by positivity
      calc _ ≤ _ := abs_sub _ _
        _ ≤ B * (α * β) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) +
            2 * (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) :=
          add_le_add (c1.trans (mul_le_mul_of_nonneg_left (hCe c) hB0))
            (h3.trans (mul_le_mul_of_nonneg_left h4 hk0))
        _ = _ := by ring
    have hB2 : 0 ≤ B * (α * β) := mul_nonneg hT.B_nonneg (mul_nonneg hα0 hβ0)
    have hB3 : 0 ≤ B * (α * β ^ 2) := mul_nonneg hT.B_nonneg (mul_nonneg hα0 (by positivity))
    have hB4 : 0 ≤ B * (α * β ^ 3) := mul_nonneg hT.B_nonneg (mul_nonneg hα0 (by positivity))
    obtain ⟨r1, r3⟩ := hTop F star T.a T.chainParams.ρA x m (T.σ / 64) T.κ T.p φ h V Y (cutoffLaw F (T.σ / 64) T.p)
      (N₀ * (C * (ε / T.η₃)) * W * (w / 2 + Cm * w ^ 2 / (2 * w))) (B * (α * β)) (B * (α * β ^ 2)) (B * (α * β ^ 3))
      (B * (α * β) + 2 * (T.Cs * Cth' * (T.E / T.η₃) * (T.Cs * ε * w)))
      (fun n => 2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate n) hκ hB2 hB3 hB4 hexp hmean hsm hnear hmid hcov
    refine ⟨hIsMean, hsmM, fun k c X hk hX => ?_, fun c X hX => ?_⟩
    · rw [hder]
      exact (r1 k c X hk hX).trans (mul_le_mul_of_nonneg_right num1 (Real.exp_pos _).le)
    · rw [hder]
      exact (r3 c X hX).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right num3 (Real.exp_pos _).le))
  have lowOf : ∀ F : BlockFrame, IsCubicTopTorus T.L t T.n₀ F → IsCubicTorusAbove T.L t T.n₀ F := fun F hF => by
    obtain ⟨hFL, hFt, n, hside, hn⟩ := hF
    exact ⟨hFL, hFt, n, hside, le_trans hn (Nat.le_mul_of_pos_right n hD.odd_L.pos)⟩
  have hfrAll : ∀ (F : BlockFrame) (V' : F.GaugeField F.top) (b : F.Site F.depth × Fin 4),
      interpolatedFrame s T.a T.chainParams.ρA m b V' = stepFrame star T.a T.chainParams.ρA m b V' :=
    fun F V' b => (hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V').1 b
  have inv : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * T.σ) V →
      (∀ (γ : F.Cell → UnitQuaternion) (Y : F.Cell),
        (∀ b ∈ chordBonds (finiteCells F), stepFrame star T.a T.chainParams.ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star T.a T.chainParams.ρA m b V)) →
        conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
          conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y V) ∧
      ∀ (Y h' : F.Cell),
        (∀ b ∈ chordBonds (finiteCells F),
          stepFrame star T.a T.chainParams.ρA m (b.1 + cellCentre F.depth h', b.2) (translateField h' V) =
            stepFrame star T.a T.chainParams.ρA m b V) →
        conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F (Y + h') (translateField h' V) =
          conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y V :=
    fun F hF V hV => by
      obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
      have hn2 : 2 ≤ n := hT.two_le.trans hn
      have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
        rw [hside]
        exact hn2
      have hodd : Odd F.blockSide := by
        rw [hFL]
        exact hD.odd_L
      have hLow := lowOf F hF
      have one := (hT.frames t x hx).one_torus F V s hF hV hs0 hs1
      have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.σ / 64) →
          IsSmallCurvature T.σ (fieldAboveFrame star T.a T.chainParams.ρA m V η) := fun η hη q hq => by
        have h1 := one.small.small_curvature_nearby η (fun b => (hη b).le) q hq
        rw [(hEnds F star T.a T.chainParams.ρA T.chainParams.lam x 0 m V).2.2.1 η] at h1
        linarith
      exact hInv F star T.a T.chainParams.ρA x (T.σ / 64) m T.p φ h V T.σ (hCh F T.a hodd hs2) hcold hσ
        ⟨fun y W γ hW => hφ.gauge_invariant F hLow y W γ hW, fun y h' W hW => hφ.translation_invariant F hLow y h' W hW⟩
        ⟨fun y W γ hW => hh.gauge_invariant F hLow y W γ hW, fun y h' W hW => hh.translation_invariant F hLow y h' W hW⟩
  refine ⟨fun F hF Y V hV => (top F hF Y V hV).1, ⟨fun F hF Y V hV => (top F hF Y V hV).2.1,
    fun F hF Y V γ hV => ?_, fun F hF Y h' V hV => ?_⟩, fun F hF Y V k c X hV hk hX => (top F hF Y V hV).2.2.1 k c X hk hX,
    fun F hF Y V k c X hV h1 h3 hX => ?_⟩
  · refine (inv F hF V hV).1 γ Y fun b hb => Subtype.ext ?_
    have g := ((hT.frames t x hx).one_torus F V s hF hV hs0 hs1).small.gauge_covariant b hb γ
    rw [hfrAll, hfrAll] at g
    exact g
  · refine (inv F hF V hV).2 Y h' fun b hb => ?_
    have g := ((hT.frames t x hx).one_torus F V s hF hV hs0 hs1).small.translation_invariant b hb h'
    rw [hfrAll, hfrAll] at g
    exact g
  · beta_reduce
    by_cases hk3 : k = 3
    · subst hk3
      rw [if_pos rfl]
      exact (top F hF Y V hV).2.2.2 c X hX
    · rw [if_neg hk3]
      have hk2 : k ≤ 2 := by omega
      have nr := (top F hF Y V hV).2.2.1 k c X hk2 hX
      have rt := ((hT.familyTransport ε hε) t x h F V hx hr hF hV star).1
      have lw := rt.lowDeriv Y k c X h1 hk2 hX
      have tri := abs_sub_abs_le_abs_sub
        (bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x m T.p φ h F Y) V c X)
        (bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA m h Y 0) V c X)
      linarith
end YangMills.Construction.BlockMeans
end
