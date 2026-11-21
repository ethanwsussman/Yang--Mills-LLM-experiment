import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.LimitTheorem.FunctionalDefs
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
structure ToriSequence (L : ℕ) where
  K : ℕ+ → ℕ+
  m : ℕ+ → ℕ+
  β : ℕ+ → ℝ
  β_pos : ∀ j, 0 < β j
  K_tendsto : Tendsto K atTop atTop
  m_tendsto : Tendsto m atTop atTop
namespace ToriSequence
variable {L : ℕ} (seq : ToriSequence L)
def HasCumulantLimit (S : LimitTheorem.CumulantFamily) : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (X : TestSpaces.SepTupleOfCard k),
    Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (seq.m j) (seq.K j) (seq.β j) X.1) atTop
      (𝓝 ((S k hk X : ℝ) : ℂ))
def HasBallwiseBound (c : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (j : ℕ+) (k : ℕ), 2 ≤ k → ∀ R d : ℝ, 0 < R → 0 < d →
    ∀ f : Fin k → PeriodicLattice.FourTorus L (seq.m j) → ℝ,
      (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)) →
      (∀ i, ∃ x, tsupport (f i) ⊆ TestFunctions.closedBallTorus x R) →
        TestFunctions.HasSeparatedSupportsTorus f d →
        ‖SchwingerFunctions.connectedSchwinger L (seq.m j) (seq.K j) (seq.β j) f‖ ≤
          c k d R * ∏ i, TestFunctions.sharpNormTorus 1 (f i)
end ToriSequence
structure LimitProperties (S : LimitTheorem.CumulantFamily) : Prop where
  symmetric : LimitTheorem.IsFamilySymmetric S
  invariant : ∀ r, LimitTheorem.IsHyperoctahedralMotion r → LimitTheorem.IsFamilyInvariant S r
  multilinear : ∀ (p : Conventions.StandingParameters) (k : ℕ) (hk : 2 ≤ k),
    AmbientPoints.IsTupleMultilinear fun Y : Continuum.SeparatedFourTuples.SepTupleLen p k =>
      S k hk (Continuum.SeparatedFourTuples.sepLenEquiv p k Y)
  reflectionPositive : LimitTheorem.IsReflectionPositiveAxial (LimitTheorem.centredOf S)
namespace ToriLimit
def Claim : Prop :=
  ∃ lowerBound : ℕ, ∀ L : ℕ, Odd L → lowerBound ≤ L → ∀ (seq : ToriSequence L) (c : ℕ → ℝ → ℝ → ℝ),
    (∀ k, 2 ≤ k → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c k d R) →
    (∀ k, 2 ≤ k → ∀ R : ℝ, 0 < R → AntitoneOn (fun d => c k d R) (Ioi 0)) →
    seq.HasBallwiseBound c → ∀ S : LimitTheorem.CumulantFamily, seq.HasCumulantLimit S → LimitProperties S
end ToriLimit
end YangMills.Construction.TotalDensities
end
