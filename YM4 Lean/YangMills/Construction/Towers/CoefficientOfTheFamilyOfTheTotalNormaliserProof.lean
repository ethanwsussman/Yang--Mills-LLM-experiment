import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.OneLoopLaw.HolomorphicFunctionsWithACubicDifference
import YangMills.Construction.Towers.ACommonWidthAndTheTransposedStraightAverage
import YangMills.Construction.Towers.CoefficientOfTheFamilyOfTheTotalNormaliser
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsAFunctional
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoice
import YangMills.Construction.Towers.TheFreePolarisationIsHolomorphicInThePolydisc
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheSecondDifferentialAtTheResponseSymbolsNearZero
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.NormaliserStiffness
open OneLoopLaw.TemperedStiffness (secondPartialAtZero)
open Coordinates.ConstancyOnConnected (IsHolomorphicScalarIn)
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec)
open ResponseProperties (euclidNorm)
open TorusMetric (euclidNormVec)
open FullSpace (freePolarizationEntry)
open FullSpace.BackgroundJets (stripHalfWidth stripHalfWidth_mem)
open FullSpace.BackgroundJets.RemainderJets (openPolydisc)
theorem isHolomorphicIn_of_subset {N N' : ℕ} {O O' : Set (Coordinates.ComplexCoordinates N)}
    {f : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (hs : O' ⊆ O) (ho : IsOpen O') : Coordinates.ComplexCoordinates.IsHolomorphicIn O' f :=
  ⟨ho, h.2.1.mono hs, fun a ha => h.2.2 a (hs ha)⟩
theorem euclidNorm_toComplexVec (p : AmbientSpace) :
    euclidNorm (toComplexVec p) = euclidNormVec p := by
  simp [euclidNorm, euclidNormVec, toComplexVec, Complex.norm_real, sq_abs]
theorem tendsto_toComplexVec_zero : Tendsto toComplexVec (𝓝 (0 : AmbientSpace)) (𝓝 0) := by
  have hc : Continuous toComplexVec :=
    continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  have h0 : toComplexVec 0 = 0 := by
    funext μ
    simp [toComplexVec]
  simpa [h0] using hc.tendsto (0 : AmbientSpace)
theorem stiffnessIsMixedPartial_of_claims
    (hWidth : FullSpace.JointWidthAndTransposeTheorem)
    (hNumbers : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hChoice : NormaliserSymbol.IsTemperedWitnessClaim)
    (hZero : ResponseSecondVariation.NearZeroCubicBound)
    (hHolomorphic : FullSpace.BackgroundJets.RemainderJets.FreePolarizationHolomorphic)
    (hFunctional : LogNormaliserIsFunctional.Claim)
    (hStiffness : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hCubic : OneLoopLaw.CubicAgreement.SecondPartialsAgree) : StiffnessIsMixedPartial := by
  intro L hL hs k hk
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hIoc, -, -⟩ := hNumbers
  have hwidth : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨δ₀, hδ₀⟩)) hδ₀
  have hcommon := (hWidth L hL hs k hk).1
  obtain ⟨π, e, hπ, hgiven⟩ := hChoice δ₀ hδ₀ L hL hs k hk _ hcommon
  obtain ⟨-, -, -, b, -, -, hformulas⟩ :=
    hStiffness L hL hs _ _ π e (hFunctional L hs k hk) hπ
  have hmixed := (hformulas 0 1 (by decide)).neg_secondPartial_mixed
  obtain ⟨C, N, hN, hNsub, hbound⟩ := hZero δ₀ hδ₀ L hL hs k hk _ hcommon
  obtain ⟨Oπ, hOπ, hholo⟩ := hπ.analytic
  have hf := (hholo 0 1).1
  have hg := hHolomorphic L hL hs k hk 0 1
  have hP : IsOpen (Oπ ∩ openPolydisc stripHalfWidth) := hf.1.inter hg.1
  have h0 : (0 : Fin 4 → ℂ) ∈ Oπ ∩ openPolydisc stripHalfWidth := by
    refine ⟨hOπ ?_, fun μ => ?_⟩
    · intro μ
      simpa using hπ.delta_pos.le
    · simpa [hwidth] using hIoc.1
  have hfP : IsHolomorphicScalarIn (Oπ ∩ openPolydisc stripHalfWidth) (π 0 1) := by
    have hline : (fun z => (Equiv.funUnique (Fin 1) ℂ).symm (π 0 1 z)) = fun z _ => π 0 1 z := by
      funext z i
      simp
    unfold IsHolomorphicScalarIn
    rw [hline]
    exact isHolomorphicIn_of_subset hf Set.inter_subset_left hP
  have hgP : IsHolomorphicScalarIn (Oπ ∩ openPolydisc stripHalfWidth)
      (freePolarizationEntry L k hL 0 1) :=
    isHolomorphicIn_of_subset hg Set.inter_subset_right hP
  have hcubic : (fun p : AmbientSpace => π 0 1 (toComplexVec p) -
      freePolarizationEntry L k hL 0 1 (toComplexVec p)) =O[𝓝 0]
      (fun p : AmbientSpace => euclidNormVec p ^ 3) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [tendsto_toComplexVec_zero hN] with p hp
    have hentry := (if_pos rfl).symm.trans (hgiven _ (hNsub hp) 2 2 0 1)
    have hnorm : ‖euclidNormVec p ^ 3‖ = euclidNorm (toComplexVec p) ^ 3 := by
      rw [euclidNorm_toComplexVec, Real.norm_of_nonneg]
      exact pow_nonneg (Real.sqrt_nonneg _) 3
    rw [hentry, hnorm]
    exact hbound _ hp 0 1
  have hequal := (hCubic _ _ _ hP h0 hfP hgP hcubic 0 1).2.2
  rw [← hmixed, hequal]
end YangMills.Construction.Tower.NormaliserStiffness
end
