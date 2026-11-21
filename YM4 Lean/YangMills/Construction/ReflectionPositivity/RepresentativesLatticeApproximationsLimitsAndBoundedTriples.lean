import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.ApproximatingSequences
open InfiniteLattice (GaugeField RefinedGaugeField ElementaryPlaquette refinedSpacing
  faceEnergy)
structure LatticeApproximation (L : ℕ) where
  cutoff : ℕ+ → ℕ+
  tendsto_cutoff : Tendsto cutoff atTop atTop
  state : ∀ j, Measure (RefinedGaugeField L (cutoff j))
  isProbabilityMeasure_state : ∀ j, IsProbabilityMeasure (state j)
  offset : ℕ+ → ℝ
namespace LatticeApproximation
variable {L : ℕ} (T : LatticeApproximation L)
section Products
variable {𝕜 : Type*} [RCLike 𝕜]
def smearedField (j : ℕ+) (f : (Fin 4 → ℝ) → 𝕜) (U : RefinedGaugeField L (T.cutoff j)) : 𝕜 :=
  ∑ᶠ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
    f p.center * ((faceEnergy U p - T.offset j : ℝ) : 𝕜)
def latticeProduct (j : ℕ+) (X : List ((Fin 4 → ℝ) → 𝕜))
    (U : RefinedGaugeField L (T.cutoff j)) : 𝕜 :=
  (X.map fun f => T.smearedField j f U).prod
end Products
end LatticeApproximation
open AxisMirror in
def LatticeApproximation.IsUniformlyBounded (D : MirrorData) (T : LatticeApproximation D.L)
    (M : ℝ) (_hM : 1 ≤ M) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set (Fin 4 → ℝ), (∀ l, IsCompact (A l)) →
    Pairwise (Function.onFun Disjoint A) →
    ∃ C : ℝ, ∀ (j : ℕ+) (f : Fin k → (Fin 4 → ℝ) → ℝ),
      List.ofFn f ∈ Ambient.separatedN D .euclidean k →
      (∀ l, Ambient.closedSupport D .euclidean (f l) ⊆ A l) →
      |∫ U, T.latticeProduct j (List.ofFn f) U ∂T.state j| ≤
        C * ∏ l, TestFunctions.sharpNormR4 M (f l)
end ReflectionPositivity.ApproximatingSequences
end YangMills.Construction
