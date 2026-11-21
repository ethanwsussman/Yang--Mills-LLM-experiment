import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel)
def openPolydisc : Set (Fin 4 → ℂ) := {p | ∀ μ, ‖p μ‖ < stripHalfWidth}
def polarizationMinusMassive (L k : ℕ) (hL : 0 < L) (μp μm : Fin 4) (p : Fin 4 → ℂ) : ℂ :=
  freePolarizationEntry L k hL μp μm p - massiveLogFnSharp L k p μp μm
def remainderNorms (L : ℕ) : Set ℝ :=
  {x | ∃ hL : 0 < L, ∃ k : ℕ, 1 ≤ k ∧ ∃ μp μm : Fin 4, ∃ p ∈ openPolydisc,
    x = ‖polarizationMinusMassive L k hL μp μm p‖}
def remainderBound (L : ℕ) : ℝ := sSup (remainderNorms L)
def ResponseFormDefinedAt (L k : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) : Prop :=
  (∀ i, ApplySummableAt (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) i) ∧
    blochWave (colourEdges L k 0) q (backgroundResponseSymbol L k q (axisPauliElement μ 2)) =
      ((finestMesh L k : ℝ) : ℂ) •
        applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2))
def PolarizationDefinedAt (L k : ℕ) (hL : 0 < L) (μp μm : Fin 4) (p : Fin 4 → ℂ) : Prop :=
  p ∈ freePolarizationDomain L k hL ∧ ResponseFormDefinedAt L k p μp ∧
    ResponseFormDefinedAt L k (-p) μm
def mixedIndex : YangMills.Construction.PowerSeries.MultiIndex 4 := ![1, 1, 0, 0]
def massiveAtFirstPair (L k : ℕ) : (Fin 4 → ℂ) → ℂ :=
  fun p => massiveLogFnSharp L k p 0 1
def mixedPartialAtZero (L k : ℕ) : ℂ :=
  YangMills.Construction.ComplexVariables.partialOfIndex mixedIndex (massiveAtFirstPair L k) 0
structure LevelClaims (L k : ℕ) (hL : 0 < L) : Prop where
  invertibility_width : IsJointInvertibilityWidth L k hL stripHalfWidth
  defined : ∀ μp μm : Fin 4, ∀ p ∈ momentumPolydisc stripHalfWidth,
    PolarizationDefinedAt L k hL μp μm p
  holomorphic : ∀ μp μm : Fin 4,
    YangMills.Construction.ComplexVariables.IsHolomorphicScalar openPolydisc
      (polarizationMinusMassive L k hL μp μm)
  massive_holomorphic :
    YangMills.Construction.ComplexVariables.IsHolomorphicScalar openPolydisc (massiveAtFirstPair L k)
  has_mixed_partial :
    YangMills.Construction.ComplexVariables.HasPartialOfIndex openPolydisc mixedIndex
      (massiveAtFirstPair L k)
  has_stiffness :
    YangMills.Construction.OneLoopLaw.FunctionalStiffness.HasStiffnessConstant hL
      (logNormaliserFamily L k)
      (YangMills.Construction.OneLoopLaw.FunctionalStiffness.stiffnessConstant hL
        (logNormaliserFamily L k))
  stiffness_bound :
    ‖((YangMills.Construction.OneLoopLaw.FunctionalStiffness.stiffnessConstant hL
          (logNormaliserFamily L k) : ℝ) : ℂ) +
        mixedPartialAtZero L k‖ ≤ remainderBound L * stripHalfWidth ^ (-2 : ℤ)
def FreePolarizationRemainderBound : Prop :=
  stripHalfWidth ∈ FreeStrip.halfSupRate ∧
    (∀ (L : ℕ) (hL : 0 < L), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
      (∀ k : ℕ, 1 ≤ k → LevelClaims L k hL) ∧
        (∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ μp μm : Fin 4, ∀ p ∈ openPolydisc,
          ‖polarizationMinusMassive L k hL μp μm p‖ ≤ C) ∧
        IsLUB (remainderNorms L) (remainderBound L)) ∧
    ∀ (D : Type) (l : D → ℕ), IsRemainderConst l (fun d => remainderBound (l d))
end YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder
end
