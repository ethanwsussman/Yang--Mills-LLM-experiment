import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfALawOfTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStepProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative TorusFreezing
namespace Interpolation
variable {F : BlockFrame}
namespace PartsSmooth
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
def imaginaryUnit : imaginaryQuaternions := toImaginary (EuclideanSpace.single 0 1)
theorem norm_imaginaryUnit : ‖imaginaryUnit‖ = 1 := by
  unfold imaginaryUnit
  rw [norm_toImaginary]
  simp
open Classical in
def unitDirection (X : imaginaryQuaternions) : imaginaryQuaternions :=
  if X = 0 then imaginaryUnit else ‖X‖⁻¹ • X
theorem norm_unitDirection (X : imaginaryQuaternions) : ‖unitDirection X‖ = 1 := by
  unfold unitDirection
  split_ifs with h
  · exact norm_imaginaryUnit
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
theorem norm_smul_unitDirection (X : imaginaryQuaternions) : ‖X‖ • unitDirection X = X := by
  unfold unitDirection
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
def scaledParameters {k : ℕ} (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.cons 0 fun l => ‖X l‖ * τ l
theorem bondSpread_scaledParameters {j k : ℕ} (c₀ : F.Site j × Fin 4) (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    ColdStepAtMirrorFrames.bondSpread (Fin.cons c₀ c : Fin (k + 1) → F.Site j × Fin 4)
      (Fin.cons imaginaryUnit fun l => unitDirection (X l) : Fin (k + 1) → imaginaryQuaternions)
      (scaledParameters X τ) = ColdStepAtMirrorFrames.bondSpread c X τ := by
  funext y i
  unfold ColdStepAtMirrorFrames.bondSpread scaledParameters
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_smul, ite_self, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [mul_comm, ← smul_smul, norm_smul_unitDirection]
  · rfl
theorem contDiff_scaledParameters {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {k : ℕ}
    (X : Fin k → imaginaryQuaternions) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun q : (Fin k → ℝ) × Q =>
      ((q.2, scaledParameters X q.1) : Q × (Fin (k + 1) → ℝ))) := by
  refine contDiff_snd.prodMk (contDiff_pi.mpr fun i => ?_)
  refine Fin.cases ?_ (fun i' => ?_) i
  · simpa [scaledParameters] using contDiff_const
  · have h : ContDiff ℝ n (fun q : (Fin k → ℝ) × Q => ‖X i'‖ * q.1 i') :=
      contDiff_const.mul ((contDiff_apply ℝ ℝ i').comp contDiff_fst)
    simpa [scaledParameters] using h
theorem interpolatedBlockExponent_contDiffAt (hSm : interpolatedBlockExponentSmoothStatement)
    {s a ρA ρ x κ κ₂ δ₂ : ℝ} {m : ℕ} {Kf : ℕ → ℝ} {Dk : ℕ → ℕ → ℝ} {V : F.GaugeField F.top}
    (hne : Nonempty ↥(chordBonds (finiteCells F)))
    (hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      HasInterpolationKernels s a ρA κ κ₂ δ₂ x m Kf Dk V η)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ ((k + 3 : ℕ) : WithTop ℕ∞) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      interpolatedBlockExponent s a ρA x m Y
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2) (0, η) := by
  have hu : AreUnitVectors
      (Fin.cons imaginaryUnit fun l => unitDirection (X l) : Fin (k + 1) → imaginaryQuaternions) := by
    intro l
    refine Fin.cases ?_ (fun l' => ?_) l
    · simpa using norm_imaginaryUnit
    · simpa using norm_unitDirection (X l')
  have hS := hSm F s a ρA ρ x κ κ₂ δ₂ m Kf Dk V Y η (k + 1)
    (Fin.cons (0, 0) c : Fin (k + 1) → F.Site F.top × Fin 4)
    (Fin.cons imaginaryUnit fun l => unitDirection (X l)) hne hker hη hu
  have hz : scaledParameters X (0 : Fin k → ℝ) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [scaledParameters]
  have hS' : ContDiffAt ℝ ((k + 3 : ℕ) : WithTop ℕ∞)
      (rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V
        (Fin.cons (0, 0) c : Fin (k + 1) → F.Site F.top × Fin 4)
        (Fin.cons imaginaryUnit fun l => unitDirection (X l)))
      ((fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        ((q.2, scaledParameters X q.1) : StepVariable (finiteCells F) × (Fin (k + 1) → ℝ))) (0, η)) := by
    show ContDiffAt ℝ _ _ (η, scaledParameters X 0)
    rw [hz]
    exact_mod_cast hS
  have hc := ContDiffAt.comp (0, η) hS'
    (contDiff_scaledParameters (Q := StepVariable (finiteCells F)) X _).contDiffAt
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  show _ = interpolatedBlockExponent s a ρA x m Y
    (leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.cons (0, 0) c : Fin (k + 1) → F.Site F.top × Fin 4)
      (Fin.cons imaginaryUnit fun l => unitDirection (X l)) (scaledParameters X q.1)) V) q.2
  rw [bondSpread_scaledParameters]
theorem chordBonds_nonempty (hSites : SiteDecomposition) (hCh : chartEquivarianceStatement) (F : BlockFrame)
    (a : ℝ) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) :
    Nonempty ↥(chordBonds (finiteCells F)) := by
  obtain ⟨h1, -, h3, -⟩ := hSites F hodd hs
  have hM := hCh F a hodd hs
  obtain ⟨l, hl⟩ := hodd
  have hc : (fun _ : Fin 4 => ((F.blockSide : ℤ) - 1) / 2) ∈ centredCube F.blockSide := by
    have hL : (F.blockSide : ℤ) = 2 * l + 1 := by exact_mod_cast hl
    simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
    intro _
    constructor <;> omega
  have h2 := (h1 0 _ hc).2
  have hcross : IsCrossingBond
      ((cellCentre F.depth 0 + siteOfCoords F.depth fun _ : Fin 4 => ((F.blockSide : ℤ) - 1) / 2 :
        F.Site F.depth), (0 : Fin 4)) := by
    rw [h3, h2]
  exact ⟨⟨_, hM.mem_chordBonds_of_not_tree _ fun ht => ht.1 hcross⟩⟩
theorem interpolatedPartsSmoothAt_of (hSm : interpolatedBlockExponentSmoothStatement)
    (hSites : SiteDecomposition)
    (hCh : chartEquivarianceStatement) (T : StepParameters) (hT : T.IsOrdered) (h2 : 2 ≤ T.n₀)
    {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ} (hK : interpolationKernelBoundsAt T K D)
    (hP : StepLawLocalDecomposition T) : InterpolatedPartsSmoothAt T := by
  classical
  intro t x F V s hx hF hV h0 h1
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hT.odd_L
  have hside : ∀ i, 2 ≤ F.extent i := by
    obtain ⟨-, -, n, hs, hn⟩ := hF
    intro i
    rw [hs i]
    omega
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hs, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hs]
      omega⟩
    exact Pi.finite
  have hne := chordBonds_nonempty hSites hCh F T.a hodd hside
  have hker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels s T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x
        (frameRadius x) K D V η :=
    fun η hη => hK x t F V s η hx hF hV h0 h1 hη
  refine ⟨fun η hη => ?_, fun Y η k c X hη => ?_, fun Y c X η hη => ?_⟩
  · let _ : Fintype F.Cell := Fintype.ofFinite _
    obtain ⟨Ψ, e1, -, e3, -⟩ := hP t x s (.ofWeight 1) F V hx h0 h1 ⟨zero_le_one, le_rfl⟩ hF hV
    have a1 := e1 η hη
    have a3 := e3 η hη
    have hw : finiteCells F = Finset.univ := by
      unfold finiteCells
      rw [dif_pos hfin]
    rw [hw]
    have b1 : interpolatedExponent s T.a T.chainParams.ρA x (frameRadius x) V η = Ψ η := by
      rw [a1]
      simp [TorusComparison.StepLaw.exponent, weightLawExponent]
    rw [b1, a3]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [stepLawCellPart]
  · exact (interpolatedBlockExponent_contDiffAt hSm hne hker Y η c X hη).of_le
      (by exact_mod_cast (by omega : 3 ≤ k + 3))
  · exact (interpolatedBlockExponent_contDiffAt hSm hne hker Y η c X hη).of_le (by norm_num)
theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
end PartsSmooth
open PartsSmooth in
theorem interpolatedPartsSmooth (hPL : stepLawLocalDecomposition)
    (hK : interpolationKernelBoundsStatement) (hSm : interpolatedBlockExponentSmoothStatement)
    (hSites : SiteDecomposition) (hCh : chartEquivarianceStatement)
    (hJ : EventuallyInParametersCombines) : interpolatedPartsSmoothStatement := by
  obtain ⟨K, D, -, -, hk⟩ := hK
  exact hJ.2 _ _ (fun T hT h => interpolatedPartsSmoothAt_of hSm hSites hCh T hT h.1 h.2.1 h.2.2)
    (hJ.1 _ _ eventually_two_le_n₀ (hJ.1 _ _ hk hPL))
end Interpolation
end YangMills.Construction
end
