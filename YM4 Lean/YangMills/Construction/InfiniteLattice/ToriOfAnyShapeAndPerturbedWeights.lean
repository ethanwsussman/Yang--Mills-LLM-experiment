import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.MeasuresOfATorusOfAnyShapeWithAndWithoutAnArray
import YangMills.Construction.InfiniteLattice.MirrorsOfTheSixteenFamiliesAndTheClassOfReflectionPositiveStates
import YangMills.Construction.InfiniteLattice.SeparatedLipschitzTuplesAndPartialFamilies
import YangMills.Construction.InfiniteLattice.SmearedDensityAndConnectedFunctionsOfAMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.LatticeConventions (NormalHyperplane)
open YangMills.Construction.LatticeConventions.NormalHyperplane (reflectSymmetry)
open YangMills.Construction.SeparatedFamilies (IsSeparatedLipschitzFamily)
def TiltedTorusLimits : Prop :=
  ∀ (L K : ℕ) (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L), 0 < K → ∀ β : ℝ, 0 < β →
    ∀ A : SingleGeneratorArray (refinedSpacing L K),
      (∀ (s : ℕ → ℝ) (ρ : ℕ → BorelProb (refinedSpacing L K)) (ν : BorelProb (refinedSpacing L K)),
        Tendsto s atTop (𝓝 0) →
        (∀ k, 1 ≤ k → A.IsTiltedGibbsState
          (YangMills.Construction.CutoffLattice.spacingAt_pos hL K) β (s k) (ρ k).1) →
        BorelProb.TendstoWeak ρ ν → IsGibbs β ν.1) ∧
      ∀ (t : ℝ) (Γ : ℕ → PeriodSublattice (refinedSpacing L K))
        (hΓ : ∀ i, 1 ≤ i → A.PeriodsWithin (Γ i)),
        Tendsto (fun i => minPeriodNorm (Γ i)) atTop atTop →
        (∀ i (hi : 1 ≤ i), IsProbabilityMeasure (A.liftedTiltMeasure (hΓ i hi) β t)) ∧
        ∀ ρ : ℕ → BorelProb (refinedSpacing L K),
          (∀ i (hi : 1 ≤ i), (ρ i).1 = A.liftedTiltMeasure (hΓ i hi) β t) →
          (∀ φ : ℕ → ℕ, StrictMono φ → (∀ k, 1 ≤ φ k) →
            ∃ ν, BorelProb.IsSubseqWeakLimit (ρ ∘ φ) ν) ∧
          {ν | BorelProb.IsSubseqWeakLimit ρ ν}.Nonempty ∧
          IsClosed {ν | BorelProb.IsSubseqWeakLimit ρ ν} ∧
          (∀ ν, BorelProb.IsSubseqWeakLimit ρ ν →
            A.IsTiltedGibbsState
              (YangMills.Construction.CutoffLattice.spacingAt_pos hL K) β t ν.1 ∧
            ∀ v ∈ A.sublattice, IsSymmetricUnder ν.1 (shift v)) ∧
          (∀ ρ₀ : ℕ → BorelProb (refinedSpacing L K),
            (∀ i, 1 ≤ i → (ρ₀ i).1 = (Γ i).liftedGibbsMeasure β) →
            ∀ ν, BorelProb.IsSubseqWeakLimit ρ₀ ν → IsGibbs β ν.1 ∧ IsShiftInvariant ν.1) ∧
          (∀ ν, BorelProb.TendstoWeak ρ ν →
            (∀ F ∈ continuousLocal (refinedSpacing L K),
              Tendsto (fun i => (ρ i).integral F) atTop (𝓝 (ν.integral F))) ∧
            (∀ f : AmbientSpace → ℂ, (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
              Bornology.IsBounded (Function.support f) →
              Tendsto (fun i => (ρ i).integral (plaquetteSmearing f)) atTop
                (𝓝 (ν.integral (plaquetteSmearing f)))) ∧
            ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), 2 ≤ n → IsSeparatedLipschitzFamily f →
              Tendsto (fun i => ursellFunctionOfMeasure (L := L) (K := K) (ρ i).1 f) atTop
                (𝓝 (ursellFunctionOfMeasure (L := L) (K := K) ν.1 f)) ∧
              ∀ (b : ℝ) (i₀ : ℕ),
                (∀ i, 1 ≤ i → i₀ ≤ i →
                  ‖ursellFunctionOfMeasure (L := L) (K := K) (ρ i).1 f‖ ≤ b) →
                ‖ursellFunctionOfMeasure (L := L) (K := K) ν.1 f‖ ≤ b) ∧
          (∀ (r : LatticeSymmetry (refinedSpacing L K)) (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace),
            IsLinearPart (refinedSpacing L K) r.toFun w →
            (∀ i, 1 ≤ i →
              w '' (Subtype.val '' ((Γ i).periods : Set (LatticePoint (refinedSpacing L K)))) =
                Subtype.val '' ((Γ i).periods : Set (LatticePoint (refinedSpacing L K)))) →
            (∀ i, 1 ≤ i → IsSymmetricUnder (ρ i).1 r) →
            ∀ ν, BorelProb.IsSubseqWeakLimit ρ ν → IsSymmetricUnder ν.1 r) ∧
          ∀ (P : NormalHyperplane) (hP : P.IsLatticeMirror (refinedSpacing L K)),
            (∀ F, Continuous F → F ∈ locallyMeasurableIn (refinedSpacing L K) P.upperHalfSpace →
              ∃ i₀ : ℕ, ∀ i, 1 ≤ i → i₀ ≤ i → 0 ≤ reflectedPairing hP (ρ i) F) →
            ∀ ν, BorelProb.IsSubseqWeakLimit ρ ν →
              (∀ F, Continuous F → F ∈ locallyMeasurableIn (refinedSpacing L K) P.upperHalfSpace →
                0 ≤ reflectedPairing hP ν F) ∧
              (IsSymmetricUnder ν.1 (reflectSymmetry hP) →
                IsFullyReflectionPositive hP ν)
end YangMills.Construction.GibbsAtFixedSpacing
