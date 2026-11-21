import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.ConnectedAtCutoff
def MixedCumulantRealSymmLinear {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) {n : ℕ}
    (x : Fin n → Ω → ℝ) : Prop :=
  (Cumulants.mixedCumulant ν x).im = 0 ∧
    (∀ σ : Equiv.Perm (Fin n),
      Cumulants.mixedCumulant ν (fun i => x (σ i)) = Cumulants.mixedCumulant ν x) ∧
    ∀ (i : Fin n) (y z : Ω → ℝ) (s t : ℝ),
      Probability.IsBoundedRealRV y →
      Probability.IsBoundedRealRV z →
      Cumulants.mixedCumulant ν (Function.update x i (s • y + t • z)) =
        (s : ℂ) * Cumulants.mixedCumulant ν (Function.update x i y) +
          (t : ℂ) * Cumulants.mixedCumulant ν (Function.update x i z)
variable (D : MirrorData)
def ConnectedRealSymmLinearOnTorusTests (n : ℕ) : Prop :=
  ∀ f : Fin n → D.Torus → ℝ, SchwingerFunctions.IsTorusTestFamily f →
    (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f).im = 0 ∧
    (∀ σ : Equiv.Perm (Fin n),
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling (fun i => f (σ i)) =
        SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling f) ∧
    ∀ (i : Fin n) (g h : D.Torus → ℝ) (s t : ℝ),
      SchwingerFunctions.IsTorusTestFamily (Function.update f i g) →
      SchwingerFunctions.IsTorusTestFamily (Function.update f i h) →
      SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
          (Function.update f i (s • g + t • h)) =
        (s : ℂ) * SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
            (Function.update f i g) +
          (t : ℂ) * SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
            (Function.update f i h)
def connectedRe (n : ℕ)
    (X : LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n) : ℝ :=
  (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling X.1).re
def ConnectedRealSymmMultilinearOnLipTuples (n : ℕ) : Prop :=
  (∀ X : LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n,
    (SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling X.1).im = 0) ∧
  LimitSpaces.Ambient.periodic.IsPermInvariant D.toStandingParameters (connectedRe D n) ∧
  LimitSpaces.Ambient.periodic.IsMultilinearOn D.toStandingParameters (connectedRe D n)
def ConnectedOfPeriodizedIsRealForm {n : ℕ} (A : Fin n → Set (Fin 4 → ℝ)) : Prop :=
  ∃ (V : Fin n → Submodule ℝ ((Fin 4 → ℝ) → ℝ)) (Φ : MultilinearMap ℝ (fun i => V i) ℝ),
    (∀ i, (V i : Set ((Fin 4 → ℝ) → ℝ)) =
      LimitSpaces.Ambient.euclidean.lipWithin D.toStandingParameters (A i)) ∧
    ∀ h : (i : Fin n) → V i,
      ((Φ h : ℝ) : ℂ) =
        SchwingerFunctions.connectedSchwingerR4 D.L D.m D.K D.coupling
          fun i => (h i : (Fin 4 → ℝ) → ℝ)
def Statement : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ), 1 ≤ n →
    ∀ x : Fin n → Ω → ℝ, (∀ i, Probability.IsBoundedRealRV (x i)) →
      MixedCumulantRealSymmLinear ν x) ∧
  (∀ (D : MirrorData) (n : ℕ), 2 ≤ n →
    ConnectedRealSymmLinearOnTorusTests D n ∧
    ConnectedRealSymmMultilinearOnLipTuples D n ∧
    ∀ ν : Measure (InfiniteLattice.GaugeField (InfiniteLattice.refinedSpacing D.L D.K)),
      IsProbabilityMeasure ν →
      InfiniteLattice.CenteredIdentity.UrsellIsRealSymmetricMultilinear ν n) ∧
  (∀ (D : MirrorData) (q : ℕ)
    (Z : LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip q),
    ((D.gibbsFunctional Z.1 : ℝ) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
        SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
          fun k : Fin J.card => Z.1 (J.orderEmbOfFin rfl k)) ∧
  ∀ (D : MirrorData) (n : ℕ), 2 ≤ n → ∀ A : Fin n → Set (Fin 4 → ℝ),
    (Pairwise fun i j =>
      LimitSpaces.Ambient.euclidean.PositivelySeparated D.toStandingParameters (A i) (A j)) →
    TestFunctions.HasDiameterLE (⋃ i, A i) (PeriodicLattice.torusSide D.L D.m / 2) →
    ConnectedOfPeriodizedIsRealForm D A
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.ConnectedAtCutoff
end
