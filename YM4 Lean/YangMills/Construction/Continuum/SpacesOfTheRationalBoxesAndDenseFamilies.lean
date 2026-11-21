import YangMills.Construction.TorusOrFourSpace.AdicIsometriesInducedMapsAndActions
import Mathlib
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.RationalBoxesAndSaturatedFamilies
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.CanonicalDecomposition
open InfiniteLattice (AmbientSpace)
abbrev adicVecSet (L : ℕ) : Set AmbientSpace := PeriodicSpace.adicPoints4 L
end YangMills.Construction.CanonicalDecomposition
end
end

open Set
noncomputable section
namespace YangMills.Construction.Continuum.RationalBoxes
def IsCompleteSeparable (V : Type*) [NormedAddCommGroup V] : Prop :=
  CompleteSpace V ∧ TopologicalSpace.SeparableSpace V
def IsSeparableBanach (Q : Set (Fin 4 → ℝ)) : Prop :=
  ∃ (V : Submodule ℝ ((Fin 4 → ℝ) → ℝ)) (N : AddGroupNorm V),
    (V : Set ((Fin 4 → ℝ) → ℝ)) = c1Off Q ∧
    (∀ f : V, N f = YangMills.Construction.TestFunctions.c1NormR4 (f : (Fin 4 → ℝ) → ℝ)) ∧
    (∀ (a : ℝ) (f : V), N (a • f) = |a| * N f) ∧
    @IsCompleteSeparable V N.toNormedAddCommGroup
structure IsDenseInvariantFamily (s : YangMills.Construction.Conventions.StandingParameters)
    (D : boxUnions → Set ((Fin 4 → ℝ) → ℝ)) : Prop where
  sub : ∀ Q : boxUnions, D Q ⊆ c1Off Q
  countable : ∀ Q : boxUnions, (D Q).Countable
  dense : ∀ Q : boxUnions, ∀ f ∈ c1Off Q, ∀ ε : ℝ, 0 < ε →
    ∃ h ∈ D Q, YangMills.Construction.TestFunctions.c1NormR4 (f - h) < ε
  invariant_hyperoctahedral : ∀ w ∈ YangMills.Construction.InfiniteLattice.hyperoctahedralLinearGroup,
    ∀ f ∈ ⋃ Q, D Q, f ∘ w.symm ∈ ⋃ Q, D Q
  invariant_shift : ∀ v ∈ YangMills.Construction.CanonicalDecomposition.adicVecSet s.L, ∀ f ∈ ⋃ Q, D Q,
    YangMills.Construction.AmbientPoints.transportFn (YangMills.Construction.R4TupleForms.shiftEquiv s v) f ∈
      ⋃ Q, D Q
structure BoxSpaceProperties (s : YangMills.Construction.Conventions.StandingParameters) (M : ℝ) : Prop where
  boxes_countable : boxUnions.Countable
  separableBanach : ∀ Q ∈ boxUnions, IsSeparableBanach Q
  sharpNorm_le_c1Norm : ∀ Q ∈ boxUnions, ∀ f ∈ c1Off Q,
    YangMills.Construction.TestFunctions.sharpNormR4 M f ≤
      80 * M * YangMills.Construction.TestFunctions.c1NormR4 f
  exists_denseInvariant : ∃ D, IsDenseInvariantFamily s D
def BoxSpaceProperties.Claim : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (M : ℝ), 1 ≤ M → BoxSpaceProperties s M
end YangMills.Construction.Continuum.RationalBoxes
