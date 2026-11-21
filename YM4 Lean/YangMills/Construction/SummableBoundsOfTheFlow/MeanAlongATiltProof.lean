import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfAFamilyAboveTheStar
import YangMills.Construction.SummableBoundsOfTheFlow.IntegralOfASmoothFamilyProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATilt
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnASegmentIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames MeasureTheory Topology
open BlockAverages hiding bondSpread
namespace BlockMeans
variable {F : BlockFrame}
namespace SegmentMean
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem isSmallCurvature_uniformField {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (ColdStepAtMirrorFrames.uniformField F F.top) := by
  intro p _
  simpa [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue,
    ColdStepAtMirrorFrames.uniformField] using hs
theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (s τ : Fin k → ℝ) :
    bondSpread c (fun l => s l • X l) τ = bondSpread c X (fun l => s l * τ l) := by apply _root_.YangMills.SharedProofs.p12456 <;> assumption
theorem exists_unitVectors_smul {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ Y : Fin k → imaginaryQuaternions, AreUnitVectors Y ∧ X = fun l => ‖X l‖ • Y l := by apply _root_.YangMills.SharedProofs.p4546 <;> assumption
theorem bondDeriv_smul {j k : ℕ} {G : F.GaugeField j → ℝ} {W : F.GaugeField j}
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (s : Fin k → ℝ)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv G W c (fun l => s l • X l) = (∏ l, s l) * bondDeriv G W c X := by
  classical
  set g : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) W) with hg
  set D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.pi fun l =>
    s l • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l with hD
  have hcomp : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c (fun l => s l • X l) τ) W)) =
      g ∘ D := by
    funext τ
    simp only [hg, Function.comp, bondSpread_smul]
    congr 3
  have hD0 : D 0 = 0 := map_zero D
  set U : Set (Fin k → ℝ) := {z | ContDiffAt ℝ k g z} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (show ContDiffAt ℝ k g z from hz).eventually (by simp)
  have hgU : ContDiffOn ℝ k g U := fun z hz => (show ContDiffAt ℝ k g z from hz).contDiffWithinAt
  have h0 : D 0 ∈ U := by
    rw [hD0]
    exact hG
  have hc := D.iteratedFDerivWithin_comp_right hgU hUo.uniqueDiffOn
    (hUo.preimage D.continuous).uniqueDiffOn h0 (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k (hUo.preimage D.continuous) h0,
    iteratedFDerivWithin_of_isOpen k hUo h0, hD0] at hc
  unfold bondDeriv
  rw [hcomp, hc, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hs : (fun l : Fin k => D (Pi.single l 1)) =
      fun l => s l • (Pi.single l (1 : ℝ) : Fin k → ℝ) := by
    funext l l'
    by_cases h : l' = l
    · subst h
      simp [hD]
    · simp [hD, h]
  show iteratedFDeriv ℝ k g 0 (fun l => D (Pi.single l 1)) = _
  rw [hs, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
theorem stepExponent_add_smul (a ρA x : ℝ) (m : ℕ) (φ h : LocalFamily) (θ : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρA x m (φ + θ • h) 1 V η =
      stepExponent true a ρA x m (fun _ _ _ => 0) 0 V η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m φ y η V -
        θ * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m h y η V := by
  have hrow : ∀ y : F.Site F.depth, centredExpansion true a ρA m (φ + θ • h) y η V =
      centredExpansion true a ρA m φ y η V + θ * centredExpansion true a ρA m h y η V := fun y => by
    simp only [centredExpansion, ColdStepAtMirrorFrames.subtractTrivial, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  simp only [stepExponent, hrow, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
theorem segmentIntegral_contDiffAt {a ρA ρ x κ C s : ℝ} {m k : ℕ} {p : ℝ → ℝ} {φ h : LocalFamily}
    {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hfin : Finite F.Cell)
    (hRim : CutoffMeanIsGibbsMean) (hSeg : GibbsInterpolation.InterpolatedGibbsMeanSmooth)
    (hE : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → CellExponentBounds true a ρA ρ x κ C m V')
    (hφ : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => centredExpansion true a ρA m φ y q.2
        (leftTranslate (bondSpread c X q.1) V)) (0, η))
    (hh : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => centredExpansion true a ρA m h y q.2
        (leftTranslate (bondSpread c X q.1) V)) (0, η))
    (hV : IsSmallCurvature s V) (Y : F.Cell) :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y
          (leftTranslate (bondSpread c X τ) V)) 0) ∧
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ∫ θ in (0 : ℝ)..1,
        Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y
          (leftTranslate (bondSpread c X τ) V)) 0 ∧
      ∀ j, j ≤ 3 → ∀ w : Fin j → Fin k → ℝ,
        ContinuousOn (fun θ => iteratedFDeriv ℝ j (fun τ : Fin k → ℝ =>
          Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y
            (leftTranslate (bondSpread c X τ) V)) 0 w)
          (Set.Icc (0 : ℝ) 1) ∧
        iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => ∫ θ in (0 : ℝ)..1,
          Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y
            (leftTranslate (bondSpread c X τ) V)) 0 w =
          ∫ θ in (0 : ℝ)..1, iteratedFDeriv ℝ j (fun τ : Fin k → ℝ =>
            Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y
              (leftTranslate (bondSpread c X τ) V)) 0 w := by
  classical
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  have := hfinμ
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  set A : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    (∑ Y' ∈ finiteCells F, cellExponent true a ρA x m Y' (Vt z.1) z.2) -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m φ y z.2 (Vt z.1) with hA
  set R : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m h y z.2 (Vt z.1) with hR
  set H : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    cellCentredExpansion true a ρA m h Y z.2 (Vt z.1) with hH
  have hEV := hE V hV
  have hsm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 A (0, η) ∧ ContDiffAt ℝ 3 R (0, η) ∧ ContDiffAt ℝ 3 H (0, η) := fun η hη => by
    refine ⟨ContDiffAt.sub (ContDiffAt.sum fun Y' _ => hEV.smooth Y' η k c X hη)
      (ContDiffAt.sum fun y _ => hφ y η hη), ContDiffAt.sum fun y _ => hh y η hη, ?_⟩
    have : H = fun z => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter
        (fun y => enclosingCell y = Y), centredExpansion true a ρA m h y z.2 (Vt z.1) := by
      funext z
      simp only [hH, cellCentredExpansion]
    rw [this]
    exact ContDiffAt.sum fun y _ => hh y η hη
  obtain ⟨hs₁, hs₂, hs₃⟩ := hSeg _ k ρ μ A R H hμ0 hμc hsm
  have heq : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ θ : ℝ,
      Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y (Vt τ) =
        GibbsInterpolation.interpolatedGibbsMean μ A R H θ τ := by
    filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hV] with τ hτ θ
    unfold Estimates.conditionalExpansionMean GibbsInterpolation.interpolatedGibbsMean
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      rw [stepExponent_add_smul, (hE (Vt τ) hτ).sum_eq η hη]
    · exact Filter.EventuallyEq.rfl
  have hev : ∀ θ : ℝ, (fun τ : Fin k → ℝ =>
      Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y (Vt τ)) =ᶠ[𝓝 0]
        GibbsInterpolation.interpolatedGibbsMean μ A R H θ :=
    fun θ => by
      filter_upwards [heq] with τ hτ using hτ θ
  have hint : (fun τ : Fin k → ℝ => ∫ θ in (0 : ℝ)..1,
      Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y (Vt τ)) =ᶠ[𝓝 0]
      fun τ => ∫ θ in (0 : ℝ)..1, GibbsInterpolation.interpolatedGibbsMean μ A R H θ τ := by
    filter_upwards [heq] with τ hτ
    simp only [hτ]
  refine ⟨fun θ hθ => (hs₁ θ hθ).congr_of_eventuallyEq (hev θ), hs₂.congr_of_eventuallyEq hint,
    fun j hj w => ?_⟩
  have hd : ∀ θ : ℝ, iteratedFDeriv ℝ j (fun τ : Fin k → ℝ =>
      Estimates.conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y (Vt τ)) 0 =
      iteratedFDeriv ℝ j (GibbsInterpolation.interpolatedGibbsMean μ A R H θ) 0 := fun θ =>
    (Filter.EventuallyEq.iteratedFDeriv ℝ (hev θ) j).eq_of_nhds
  obtain ⟨hc, hi⟩ := hs₃ j hj w
  constructor
  · exact hc.congr fun θ _ => congrArg (fun e => e w) (hd θ)
  · have h1 := congrArg (fun e => e w) (Filter.EventuallyEq.iteratedFDeriv ℝ hint j).eq_of_nhds
    refine h1.trans (hi.trans ?_)
    exact intervalIntegral.integral_congr fun θ _ => (congrArg (fun e => e w) (hd θ)).symm
theorem bondDeriv_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
theorem bondDeriv_sub_const {k : ℕ} {g : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (b : ℝ)
    (hg : ContDiffAt ℝ k (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (fun V' => g V' - b) V c X = bondDeriv g V c X - if k = 0 then b else 0 := by
  unfold bondDeriv
  have h1 : (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V) - b) =
      (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) - fun _ => b := rfl
  rw [h1, iteratedFDeriv_sub_apply hg contDiffAt_const, _root_.sub_apply]
  congr 1
  by_cases hk : k = 0
  · subst hk
    simp [iteratedFDeriv_zero_apply]
  · rw [iteratedFDeriv_const_of_ne hk]
    simp [hk]
def latticeSupNorm (z : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (z i).natAbs
theorem natAbs_le_latticeSupNorm (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ latticeSupNorm z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun z : Fin 4 → ℤ => ∏ i, r ^ (z i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
def latticeBondWeight (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  (1 + (latticeSupNorm b.1 : ℝ)) * Real.exp (-(c * latticeSupNorm b.1))
theorem latticeBondWeight_nonneg (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : 0 ≤ latticeBondWeight c b := by
  unfold latticeBondWeight
  positivity
theorem summable_latticeBondWeight {c : ℝ} (hc : 0 < c) : Summable (latticeBondWeight c) := by
  set K : ℝ := 2 / c + 1 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := Real.exp (-(c / 8)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith [show 0 < c / 8 by positivity]
  have hz : Summable fun z : Fin 4 → ℤ =>
      (1 + (latticeSupNorm z : ℝ)) * Real.exp (-(c * latticeSupNorm z)) := by
    refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
      ((summable_prod_pow_natAbs hr0 hr1).mul_left K)
    set s : ℝ := (latticeSupNorm z : ℝ) with hs
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    have h1 : 1 + s ≤ K * Real.exp (c / 2 * s) := by
      have h2 : 1 + c / 2 * s ≤ Real.exp (c / 2 * s) := by
        have := Real.add_one_le_exp (c / 2 * s)
        linarith
      have h3 : 1 + s ≤ K * (1 + c / 2 * s) := by
        have : K * (1 + c / 2 * s) = 2 / c + 1 + s + c / 2 * s := by
          rw [hK]
          field_simp
          ring
        rw [this]
        have : 0 < 2 / c := by positivity
        nlinarith [mul_nonneg hc.le hs0]
      exact h3.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
    have h3 : (∑ i, ((z i).natAbs : ℝ)) ≤ 4 * s := by
      have : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ((z i).natAbs : ℝ) ≤ s := fun i _ => by
        rw [hs]
        exact_mod_cast natAbs_le_latticeSupNorm z i
      simpa using Finset.sum_le_sum this
    have h4 : ∏ i, r ^ (z i).natAbs = Real.exp (-(c / 8) * ∑ i, ((z i).natAbs : ℝ)) := by
      rw [hr, Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h4]
    calc (1 + s) * Real.exp (-(c * s))
        ≤ (K * Real.exp (c / 2 * s)) * Real.exp (-(c * s)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = K * Real.exp (-(c / 2 * s)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ K * Real.exp (-(c / 8) * ∑ i, ((z i).natAbs : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0.le
          nlinarith
  have h := Summable.mul_of_nonneg hz ((hasSum_fintype fun _ : Fin 4 => (1 : ℝ)).summable)
    (fun z => by positivity) (fun _ => zero_le_one)
  have hw : latticeBondWeight c = fun b : (Fin 4 → ℤ) × Fin 4 =>
      (1 + (latticeSupNorm b.1 : ℝ)) * Real.exp (-(c * latticeSupNorm b.1)) * 1 := by
    funext b
    simp [latticeBondWeight]
  rw [hw]
  exact h
theorem exists_norm_le_linear_of_isLinearPotential {Fm : Fin 4 → Fin 4 → imaginaryQuaternions}
    {B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions} (hB : IsLinearPotential Fm B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b, ‖B b‖ ≤ K * (1 + (latticeSupNorm b.1 : ℝ)) := by
  obtain ⟨A, e, hA, -⟩ := hB
  refine ⟨∑ μ, (∑ ν, ‖A μ ν‖ + ‖e μ‖), by positivity, ?_⟩
  rintro ⟨z, μ⟩
  have h1 : ‖B (z, μ)‖ ≤ (∑ ν, ‖A μ ν‖ + ‖e μ‖) * (1 + (latticeSupNorm z : ℝ)) := by
    rw [hA]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ ν, (z ν : ℝ) • A μ ν‖ ≤ (∑ ν, ‖A μ ν‖) * (latticeSupNorm z : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun ν _ => ?_
      rw [norm_smul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := natAbs_le_latticeSupNorm z ν
      rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast this
    have h3 : 0 ≤ ∑ ν, ‖A μ ν‖ := by positivity
    nlinarith [norm_nonneg (e μ)]
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Finset.single_le_sum (f := fun μ => ∑ ν, ‖A μ ν‖ + ‖e μ‖) (fun _ _ => by positivity)
    (Finset.mem_univ μ)
theorem latticeSupNorm_le_siteSupDist {j : ℕ} (z : Fin 4 → ℤ)
    (hper : ∀ i, 2 * latticeSupNorm z < F.period j i) :
    latticeSupNorm z ≤ siteSupDist (0 : F.Site j) (0 + siteOfCoords j z) := by
  refine Finset.sup_le fun i _ => ?_
  unfold siteSupDist
  refine le_trans (le_of_eq ?_) (Finset.le_sup (Finset.mem_univ i))
  have hN := hper i
  have hz := natAbs_le_latticeSupNorm z i
  have : NeZero (F.period j i) := ⟨by omega⟩
  have h1 : ((z i : ℤ) : ZMod (F.period j i)).valMinAbs = z i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  have h2 : ((0 : F.Site j) i - (((0 : F.Site j) + siteOfCoords j z : F.Site j) i)) =
      -((z i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  show _ = ((((0 : F.Site j) i - (((0 : F.Site j) + siteOfCoords j z : F.Site j) i))).valMinAbs).natAbs
  rw [h2, ZMod.natAbs_valMinAbs_neg, h1]
theorem max_latticeSupNorm_le_bondSpan {j : ℕ} {b b' : (Fin 4 → ℤ) × Fin 4}
    (hper : ∀ i, 2 * max (latticeSupNorm b.1) (latticeSupNorm b'.1) < F.period j i) :
    max (latticeSupNorm b.1) (latticeSupNorm b'.1) ≤ bondSpan (0 : F.Site j) (bondsAt 0 ![b, b']) := by
  have h0 := latticeSupNorm_le_siteSupDist (F := F) (j := j) b.1 fun i =>
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (le_max_left _ _)) (hper i)
  have h1 := latticeSupNorm_le_siteSupDist (F := F) (j := j) b'.1 fun i =>
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (le_max_right _ _)) (hper i)
  have g0 := Finset.le_sup (f := fun l : Fin 2 => siteSupDist (0 : F.Site j) (bondsAt 0 ![b, b'] l).1)
    (Finset.mem_univ 0)
  have g1 := Finset.le_sup (f := fun l : Fin 2 => siteSupDist (0 : F.Site j) (bondsAt 0 ![b, b'] l).1)
    (Finset.mem_univ 1)
  refine le_max_of_le_left (max_le (h0.trans ?_) (h1.trans ?_))
  · exact g0
  · exact g1
theorem div_torusDecayFactor_add_le {L : ℕ} {δ κ' a b : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ κ') (n : ℕ) :
    a / torusDecayFactor L δ n + b * Real.exp (-(κ' * n)) ≤ (a + |b|) * Real.exp (-(δ * n)) := by
  have h1 : a / torusDecayFactor L δ n ≤ a * Real.exp (-(δ * n)) := by
    have hw : Real.exp (δ * n) ≤ torusDecayFactor L δ n := by
      unfold torusDecayFactor
      exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left ha (Real.exp_pos _) hw
  have h2 : b * Real.exp (-(κ' * n)) ≤ |b| * Real.exp (-(δ * n)) := by
    have h3 : Real.exp (-(κ' * n)) ≤ Real.exp (-(δ * n)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc b * Real.exp (-(κ' * n)) ≤ |b| * Real.exp (-(κ' * n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self b) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (abs_nonneg b)
  linarith
theorem mem_Icc_of_mem_uIoc_zero_one {θ : ℝ} (h : θ ∈ Set.uIoc (0 : ℝ) 1) :
    θ ∈ Set.Icc (0 : ℝ) 1 := by apply _root_.YangMills.Construction.IteratedDerivative.ParametricIntegral.mem_Icc_of_mem_uIoc <;> assumption
theorem mem_Icc_of_mem_uIcc_zero_one {θ : ℝ} (h : θ ∈ Set.uIcc (0 : ℝ) 1) :
    θ ∈ Set.Icc (0 : ℝ) 1 := by
  rwa [Set.uIcc_of_le zero_le_one] at h
theorem segmentMeanBoundsAt_of {T : StepParameters} (hT : T.IsOrdered) (h2 : 2 ≤ T.n₀)
    (hMean : ConditionalMeanBoundsAt T.a T.chainParams.ρA T.κ T.decayRate T.η₃ T.σ T.E T.CE T.coupling
      T.L T.n₀ T.p)
    (hXb : CellExponentsBoundedAt T) (hRows : CentredExpansionContDiff T)
    (hRim : CutoffMeanIsGibbsMean)
    (hSeg : GibbsInterpolation.InterpolatedGibbsMeanSmooth) : SegmentMeanBoundsAt T := by
  intro t x φ h ε hx hε hfam hh
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  have hη₃ := hT.η₃_pos
  have hE0 : 0 < T.E := lt_of_lt_of_le one_pos hT.one_le_E
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hφ0 : FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ := by
    have := hfam 0 le_rfl zero_le_one
    simpa using this
  have hh0 : FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h :=
    ⟨hh.smooth, hh.gauge_invariant, hh.translation_invariant, hh.decay, hh.locality⟩
  have hfinF : ∀ F : BlockFrame, IsCubicTopTorus T.L t T.n₀ F → Finite F.Cell := fun F hF => by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  set G : TopLevelFamily :=
    segmentAveragedMean T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h with hG
  set M : ℝ → TopLevelFamily := fun θ =>
    Estimates.conditionalExpansionMean true T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p
      (φ + θ • h) h with hM
  have hMθ : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ConditionalMeanBounds true T.a T.chainParams.ρA T.σ x T.κ
      T.decayRate ε (ε / T.η₃) T.CE T.L t T.n₀ (frameRadius x) T.p (φ + θ • h) h := fun θ hθ =>
    hMean t x _ h ε true hx hε (hfam θ hθ.1 hθ.2) hh
  have key := fun (F : BlockFrame) (hF : IsCubicTopTorus T.L t T.n₀ F) (Y : F.Cell)
      (V : F.GaugeField F.top) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) =>
    segmentIntegral_contDiffAt (a := T.a) (ρA := T.chainParams.ρA) (ρ := T.ballRadius) (x := x)
      (κ := T.κ) (C := T.Ct) (s := 5 / 4 * T.σ) (m := frameRadius x) (p := T.p) (φ := φ) (h := h)
      hρ hT.cutoff (hfinF F hF) hRim hSeg
      (fun V' hV' => (hXb t x F V' true hx hF hV').1)
      (fun y η hη => hRows t x _ _ φ F V k c X y η hx hE0.le (by positivity) hφ0 hF hV hη)
      (fun y η hη => hRows t x _ _ h F V k c X y η hx hε.le (by positivity) hh0 hF hV hη) hV Y
  have hderiv : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      k ≤ 3 → bondDeriv (G F Y) V c X = ∫ θ in (0 : ℝ)..1, bondDeriv (M θ F Y) V c X :=
    fun F hF Y V hV k c X hk => ((key F hF Y V hV k c X).2.2 k hk fun l => Pi.single l 1).2
  have hcont : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      k ≤ 3 → ContinuousOn (fun θ => bondDeriv (M θ F Y) V c X) (Set.Icc (0 : ℝ) 1) :=
    fun F hF Y V hV k c X hk => ((key F hF Y V hV k c X).2.2 k hk fun l => Pi.single l 1).1
  have hsmθ : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        M θ F Y (leftTranslate (bondSpread c X τ) V)) 0 :=
    fun F hF Y V hV k c X θ hθ => (key F hF Y V hV k c X).1 θ hθ
  have hsmG : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G F Y (leftTranslate (bondSpread c X τ) V)) 0 :=
    fun F hF Y V hV k c X => (key F hF Y V hV k c X).2.1
  have hcent : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      k ≤ 3 → bondDeriv (centredFamily G F Y) V c X =
          (∫ θ in (0 : ℝ)..1, bondDeriv (centredFamily (M θ) F Y) V c X) ∧
        ContinuousOn (fun θ => bondDeriv (centredFamily (M θ) F Y) V c X) (Set.Icc (0 : ℝ) 1) := by
    intro F hF Y V hV k c X hk
    have hkc : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
    have hflat : IsSmallCurvature (5 / 4 * T.σ) (ColdStepAtMirrorFrames.uniformField F F.top) :=
      isSmallCurvature_uniformField (by positivity)
    have hb : ContinuousOn (fun θ => M θ F Y (ColdStepAtMirrorFrames.uniformField F F.top))
        (Set.Icc (0 : ℝ) 1) := by
      have := hcont F hF Y _ hflat 0 Fin.elim0 Fin.elim0 (by norm_num)
      simpa only [bondDeriv_zero] using this
    have e1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, bondDeriv (centredFamily (M θ) F Y) V c X =
        bondDeriv (M θ F Y) V c X -
          if k = 0 then M θ F Y (ColdStepAtMirrorFrames.uniformField F F.top) else 0 := fun θ hθ =>
      bondDeriv_sub_const c X _ ((hsmθ F hF Y V hV k c X θ hθ).of_le hkc)
    have e2 : bondDeriv (centredFamily G F Y) V c X =
        bondDeriv (G F Y) V c X -
          if k = 0 then G F Y (ColdStepAtMirrorFrames.uniformField F F.top) else 0 :=
      bondDeriv_sub_const c X _ ((hsmG F hF Y V hV k c X).of_le hkc)
    have hb' : ContinuousOn (fun θ =>
        if k = 0 then M θ F Y (ColdStepAtMirrorFrames.uniformField F F.top) else 0)
        (Set.Icc (0 : ℝ) 1) := by
      by_cases hk0 : k = 0
      · simpa only [hk0, if_true] using hb
      · simpa only [hk0, if_false] using continuousOn_const
    have ha := hcont F hF Y V hV k c X hk
    constructor
    · rw [e2, hderiv F hF Y V hV k c X hk,
        intervalIntegral.integral_congr (fun θ hθ => e1 θ (mem_Icc_of_mem_uIcc_zero_one hθ)),
        intervalIntegral.integral_sub (ha.intervalIntegrable_of_Icc zero_le_one)
          (hb'.intervalIntegrable_of_Icc zero_le_one)]
      congr 1
      by_cases hk0 : k = 0
      · simp only [hk0, if_true]
        rfl
      · simp [hk0]
    · exact (ha.sub hb').congr e1
  have hcold : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := fun hV p hp => (hV p hp).trans_le (by linarith)
  refine ⟨⟨fun F hF Y V hV k c X => (key F hF Y V hV k c X).2.1, fun F hF Y V γ hV => ?_,
    fun F hF Y g V hV => ?_⟩, ?_, ?_, ?_⟩
  · exact intervalIntegral.integral_congr fun θ hθ =>
      (hMθ θ (mem_Icc_of_mem_uIcc_zero_one hθ)).density.gauge_invariant F hF Y V γ hV
  · exact intervalIntegral.integral_congr fun θ hθ =>
      (hMθ θ (mem_Icc_of_mem_uIcc_zero_one hθ)).density.translation_invariant F hF Y g V hV
  · intro F hF Y V k c X hV h1 h3 hX
    show |bondDeriv (G F Y) V c X| ≤ _
    rw [hderiv F hF Y V hV k c X h3]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun θ => bondDeriv (M θ F Y) V c X) (fun θ hθ =>
        (hMθ θ (mem_Icc_of_mem_uIoc_zero_one hθ)).decay F hF Y V k c X hV h1 h3 hX)
    simpa using this
  · intro F F' hF hF' Y Y' V V' r k hb X hV hV' hag hk hbox hX
    obtain ⟨e1, c1⟩ := hcent F hF Y V (hcold hV) k (bondsAt Y hb) X (by omega)
    obtain ⟨e2, c2⟩ := hcent F' hF' Y' V' (hcold hV') k (bondsAt Y' hb) X (by omega)
    rw [e1, e2, ← intervalIntegral.integral_sub (c1.intervalIntegrable_of_Icc zero_le_one)
      (c2.intervalIntegrable_of_Icc zero_le_one)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun θ => bondDeriv (centredFamily (M θ) F Y) V (bondsAt Y hb) X -
        bondDeriv (centredFamily (M θ) F' Y') V' (bondsAt Y' hb) X) (fun θ hθ =>
        (hMθ θ (mem_Icc_of_mem_uIoc_zero_one hθ)).locality F F' hF hF' Y Y' V V' r k hb X hV hV'
          hag hk hbox hX)
    simpa using this
  · have hδ : 0 < T.decayRate := by
      show 0 < T.κ / 2 ^ 10
      positivity
    have hδκ : T.decayRate ≤ T.κ / 2 ^ 6 := by
      show T.κ / 2 ^ 10 ≤ T.κ / 2 ^ 6
      have : (0 : ℝ) ≤ T.κ := hκ.le
      norm_num
      linarith
    set Cc : ℝ := 2⁻¹ ^ 6 * ε + |T.CE * ε * x ^ (-(1 / 2 : ℝ))| with hCc
    have hCc0 : 0 ≤ Cc := by positivity
    have hTor : ∀ n, T.n₀ ≤ n → IsCubicTopTorus T.L t T.n₀ (cubicTorusFrame T.L t n) := fun n hn =>
      ⟨rfl, rfl, n, fun _ => rfl, hn⟩
    have hfl : ∀ n, IsSmallCurvature (5 / 4 * T.σ)
        (ColdStepAtMirrorFrames.uniformField (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n).top) :=
      fun n => isSmallCurvature_uniformField (by positivity)
    have hsec : ∀ n, T.n₀ ≤ n → ∀ b b' X X', secondDerivAtUniform G T.L t n b b' X X' =
        ∫ θ in (0 : ℝ)..1, secondDerivAtUniform (M θ) T.L t n b b' X X' := fun n hn b b' X X' =>
      hderiv _ (hTor n hn) 0 _ (hfl n) 2 _ _ (by norm_num)
    have hcs : ∀ n, T.n₀ ≤ n → ∀ b b' X X', ContinuousOn (fun θ =>
        secondDerivAtUniform (M θ) T.L t n b b' X X') (Set.Icc (0 : ℝ) 1) := fun n hn b b' X X' =>
      hcont _ (hTor n hn) 0 _ (hfl n) 2 _ _ (by norm_num)
    have hbd : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ n, T.n₀ ≤ n → ∀ b b' X X',
        |secondDerivAtUniform (M θ) T.L t n b b' X X'| ≤ ‖X‖ * ‖X'‖ * (Cc * Real.exp (-(T.decayRate *
          bondSpan (0 : (cubicTorusFrame T.L t n).Site (cubicTorusFrame T.L t n).top)
            (bondsAt 0 ![b, b'])))) := by
      intro θ hθ n hn b b' X X'
      obtain ⟨Yu, hYu, hYe⟩ := exists_unitVectors_smul ![X, X']
      have hs := bondDeriv_smul (G := M θ (cubicTorusFrame T.L t n) 0)
        (W := ColdStepAtMirrorFrames.uniformField (cubicTorusFrame T.L t n)
          (cubicTorusFrame T.L t n).top)
        (bondsAt 0 ![b, b']) Yu (fun l => ‖(![X, X'] : Fin 2 → imaginaryQuaternions) l‖)
        ((hsmθ _ (hTor n hn) 0 _ (hfl n) 2 _ Yu θ hθ).of_le (by norm_num))
      rw [← hYe] at hs
      have hdec := (hMθ θ hθ).decay _ (hTor n hn) 0 _ 2 (bondsAt 0 ![b, b']) Yu (hfl n)
        (by norm_num) (by norm_num) hYu
      have hw := div_torusDecayFactor_add_le (L := T.L) (δ := T.decayRate) (κ' := T.κ / 2 ^ 6)
        (a := 2⁻¹ ^ 6 * ε) (b := T.CE * ε * x ^ (-(1 / 2 : ℝ))) (by positivity) hδκ
        (bondSpan (0 : (cubicTorusFrame T.L t n).Site (cubicTorusFrame T.L t n).top)
          (bondsAt 0 ![b, b']))
      have hdec' : |bondDeriv (M θ (cubicTorusFrame T.L t n) 0)
          (ColdStepAtMirrorFrames.uniformField (cubicTorusFrame T.L t n) (cubicTorusFrame T.L t n).top)
          (bondsAt 0 ![b, b']) Yu| ≤ Cc * Real.exp (-(T.decayRate *
            bondSpan (0 : (cubicTorusFrame T.L t n).Site (cubicTorusFrame T.L t n).top)
              (bondsAt 0 ![b, b']))) := by
        refine hdec.trans (le_trans (le_of_eq ?_) hw)
        have h23 : ¬ (2 : ℕ) = 3 := by norm_num
        simp only [h23, if_false]
      show |bondDeriv (M θ (cubicTorusFrame T.L t n) 0) _ _ ![X, X']| ≤ _
      rw [hs, abs_mul, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_mul, abs_norm]
      exact mul_le_mul_of_nonneg_left hdec' (by positivity)
    have hq : ∀ θ : ℝ, ∃ q : BondBilinearForm, θ ∈ Set.Icc (0 : ℝ) 1 →
        (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform (M θ) T.L t n b b' X X')
          Filter.atTop (𝓝 (q b b' X X'))) ∧
        ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
          ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
          ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
            q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) := fun θ => by
      by_cases hθ : θ ∈ Set.Icc (0 : ℝ) 1
      · obtain ⟨q, h1⟩ := (hMθ θ hθ).flat_form
        exact ⟨q, fun _ => h1⟩
      · exact ⟨0, fun h => absurd h hθ⟩
    choose q hq using hq
    have hqb : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ b b' X X', |q θ b b' X X'| ≤ ‖X‖ * ‖X'‖ *
        (Cc * Real.exp (-(T.decayRate * (max (latticeSupNorm b.1) (latticeSupNorm b'.1) : ℕ)))) := by
      intro θ hθ b b' X X'
      refine le_of_tendsto ((hq θ hθ).1 b b' X X').abs ?_
      filter_upwards [Filter.eventually_ge_atTop
        (max T.n₀ (2 * max (latticeSupNorm b.1) (latticeSupNorm b'.1) + 1))] with n hn
      have hn₀ : T.n₀ ≤ n := (le_max_left _ _).trans hn
      have hn₁ : 2 * max (latticeSupNorm b.1) (latticeSupNorm b'.1) + 1 ≤ n :=
        (le_max_right _ _).trans hn
      have hsp := max_latticeSupNorm_le_bondSpan (F := cubicTorusFrame T.L t n)
        (j := (cubicTorusFrame T.L t n).top) (b := b) (b' := b')
        (fun i => by
          have : (cubicTorusFrame T.L t n).period (cubicTorusFrame T.L t n).top i = n := by
            simp [BlockFrame.period, cubicTorusFrame]
          omega)
      refine (hbd θ hθ n hn₀ b b' X X').trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCc0) (by positivity)
      refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hδ.le))
      exact_mod_cast hsp
    refine ⟨fun b b' X X' => ∫ θ in (0 : ℝ)..1, q θ b b' X X', fun b b' X X' => ?_,
      fun X μ ν B hX hμν hB => ?_⟩
    · refine Filter.Tendsto.congr' ?_
        (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (fun _ => ‖X‖ * ‖X'‖ * Cc) ?_ ?_ intervalIntegrable_const
          (ae_of_all _ fun θ hθ => (hq θ (mem_Icc_of_mem_uIoc_zero_one hθ)).1 b b' X X'))
      · filter_upwards [Filter.eventually_ge_atTop T.n₀] with n hn
        exact (hsec n hn b b' X X').symm
      · filter_upwards [Filter.eventually_ge_atTop T.n₀] with n hn
        exact ((hcs n hn b b' X X').mono fun θ hθ =>
          mem_Icc_of_mem_uIoc_zero_one hθ).aestronglyMeasurable measurableSet_uIoc
      · filter_upwards [Filter.eventually_ge_atTop T.n₀] with n hn
        refine ae_of_all _ fun θ hθ => ?_
        refine (hbd θ (mem_Icc_of_mem_uIoc_zero_one hθ) n hn b b' X X').trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_of_le_one_right hCc0 (Real.exp_le_one_iff.mpr ?_)
        have : (0 : ℝ) ≤ T.decayRate *
            (bondSpan (0 : (cubicTorusFrame T.L t n).Site (cubicTorusFrame T.L t n).top)
              (bondsAt 0 ![b, b']) : ℕ) := by positivity
        linarith
    · obtain ⟨Kb, hKb0, hKb⟩ := exists_norm_le_linear_of_isLinearPotential hB
      have hv : ∀ θ : ℝ, ∃ v : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
            q θ e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) := fun θ => by
        by_cases hθ : θ ∈ Set.Icc (0 : ℝ) 1
        · obtain ⟨v, h1⟩ := (hq θ hθ).2 X μ ν B hX hμν hB
          exact ⟨v, fun _ => h1⟩
        · exact ⟨0, fun h => absurd h hθ⟩
      choose v hv using hv
      have hsum : Summable fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          Kb ^ 2 * Cc * (latticeBondWeight (T.decayRate / 2) e.1 *
            latticeBondWeight (T.decayRate / 2) e.2) :=
        (Summable.mul_of_nonneg (summable_latticeBondWeight (by positivity))
          (summable_latticeBondWeight (by positivity)) (latticeBondWeight_nonneg _)
          (latticeBondWeight_nonneg _)).mul_left _
      refine ⟨∫ θ in (0 : ℝ)..1, v θ, ?_, ?_⟩
      · refine intervalIntegral.hasSum_integral_of_dominated_convergence
          (fun e _ => Kb ^ 2 * Cc * (latticeBondWeight (T.decayRate / 2) e.1 *
            latticeBondWeight (T.decayRate / 2) e.2)) ?_ ?_
          (ae_of_all _ fun _ _ => hsum) intervalIntegrable_const
          (ae_of_all _ fun θ hθ => (hv θ (mem_Icc_of_mem_uIoc_zero_one hθ)).1)
        · intro e
          refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
            (f := fun n θ => secondDerivAtUniform (M θ) T.L t (n + T.n₀) e.1 e.2 (B e.1) (B e.2))
            (fun n => ?_) ?_
          · exact ((hcs (n + T.n₀) (by omega) e.1 e.2 (B e.1) (B e.2)).mono
              fun θ hθ => mem_Icc_of_mem_uIoc_zero_one hθ).aestronglyMeasurable measurableSet_uIoc
          · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun θ hθ => ?_)
            exact ((hq θ (mem_Icc_of_mem_uIoc_zero_one hθ)).1 e.1 e.2 (B e.1) (B e.2)).comp
              (Filter.tendsto_add_atTop_nat T.n₀)
        · intro e
          refine ae_of_all _ fun θ hθ => ?_
          have h1 := hqb θ (mem_Icc_of_mem_uIoc_zero_one hθ) e.1 e.2 (B e.1) (B e.2)
          refine h1.trans ?_
          set d₁ : ℝ := (latticeSupNorm e.1.1 : ℝ) with hd₁
          set d₂ : ℝ := (latticeSupNorm e.2.1 : ℝ) with hd₂
          have hm₁ : d₁ ≤ (max (latticeSupNorm e.1.1) (latticeSupNorm e.2.1) : ℕ) :=
            Nat.cast_le.mpr (le_max_left _ _)
          have hm₂ : d₂ ≤ (max (latticeSupNorm e.1.1) (latticeSupNorm e.2.1) : ℕ) :=
            Nat.cast_le.mpr (le_max_right _ _)
          have hexp : Real.exp (-(T.decayRate * (max (latticeSupNorm e.1.1) (latticeSupNorm e.2.1) : ℕ))) ≤
              Real.exp (-(T.decayRate / 2 * d₁)) * Real.exp (-(T.decayRate / 2 * d₂)) := by
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            nlinarith
          have hB₁ := hKb e.1
          have hB₂ := hKb e.2
          calc ‖B e.1‖ * ‖B e.2‖ * (Cc * Real.exp (-(T.decayRate *
                (max (latticeSupNorm e.1.1) (latticeSupNorm e.2.1) : ℕ))))
              ≤ (Kb * (1 + d₁)) * (Kb * (1 + d₂)) *
                  (Cc * (Real.exp (-(T.decayRate / 2 * d₁)) * Real.exp (-(T.decayRate / 2 * d₂)))) := by
                refine mul_le_mul (mul_le_mul hB₁ hB₂ (norm_nonneg _) (by positivity))
                  (mul_le_mul_of_nonneg_left hexp hCc0) (by positivity) (by positivity)
            _ = Kb ^ 2 * Cc * (latticeBondWeight (T.decayRate / 2) e.1 *
                latticeBondWeight (T.decayRate / 2) e.2) := by
                simp only [latticeBondWeight, hd₁, hd₂]
                ring
      · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
          (f := v) (C := T.CE * ε * x ^ (-(1 / 2 : ℝ))) (fun θ hθ =>
            (hv θ (mem_Icc_of_mem_uIoc_zero_one hθ)).2)
        simpa using this
end SegmentMean
open SegmentMean in
theorem segmentMeanStatement_proof (hJ : EventuallyInParametersCombines)
    (hM : conditionalMeanStatement) (hX : CellExponentsBounded)
    (hRows : centredExpansionContDiffStatement) (hRim : CutoffMeanIsGibbsMean)
    (hSeg : GibbsInterpolation.InterpolatedGibbsMeanSmooth) : segmentMeanStatement := by
  obtain ⟨join, weaken⟩ := hJ
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ (fun T hT h => ?_) (join _ _ h2 (join _ _ hM (join _ _ hX hRows)))
  obtain ⟨hn₂, hM, hX, hRows⟩ := h
  exact segmentMeanBoundsAt_of hT hn₂ hM hX hRows hRim hSeg
end BlockMeans
end YangMills.Construction
end
