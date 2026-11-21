import YangMills.Construction.PassageToTheLimit.ModuliOfContinuityOfAFunctionOfClassC1
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimit
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
open Conventions
structure IsBanachFunctionSpace {X : Type*} (V : Set (X → ℝ)) (n : (X → ℝ) → ℝ) : Prop where
  zero_mem : (0 : X → ℝ) ∈ V
  lincomb_mem : ∀ f ∈ V, ∀ g ∈ V, ∀ a b : ℝ, a • f + b • g ∈ V
  norm_eq_zero_iff : ∀ f ∈ V, n f = 0 ↔ f = 0
  norm_smul : ∀ f ∈ V, ∀ a : ℝ, n (a • f) = |a| * n f
  norm_add_le : ∀ f ∈ V, ∀ g ∈ V, n (f + g) ≤ n f + n g
  cauchy_tendsto : ∀ u : ℕ → X → ℝ, (∀ k, u k ∈ V) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N, n (u a - u b) < ε) →
    ∃ f ∈ V, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, n (u a - f) < ε
namespace Ambient
abbrev C1ProductSpace (s : StandingParameters) (E : Ambient) {q : ℕ} (W : Fin q → Set (E.Carrier s)) :
    Type :=
  (l : Fin q) → E.c1Within s (W l)
section Forms
variable {s : StandingParameters} {E : Ambient} {q : ℕ} {W : Fin q → Set (E.Carrier s)}
def components (h : E.C1ProductSpace s W) : Fin q → E.Carrier s → ℝ := fun l => (h l).1
def IsMultilinearRealForm (Ψ : E.C1ProductSpace s W → ℝ) : Prop :=
  ∀ (i : Fin q) (a b : ℝ) (X Y Z : E.C1ProductSpace s W),
    (∀ l, l ≠ i → (Y l).1 = (X l).1) → (∀ l, l ≠ i → (Z l).1 = (X l).1) →
    (Z i).1 = a • (X i).1 + b • (Y i).1 → Ψ Z = a * Ψ X + b * Ψ Y
def operatorBound (Ψ : E.C1ProductSpace s W → ℝ) : ℝ≥0∞ :=
  ⨆ (h : E.C1ProductSpace s W) (_ : ∀ l, E.normC1 s (h l).1 ≤ 1), ENNReal.ofReal |Ψ h|
def IsBoundedMultilinear (Ψ : E.C1ProductSpace s W → ℝ) : Prop := operatorBound Ψ < ⊤
def UniformEstimate {J : Set ℕ+} (Ψ : J → E.C1ProductSpace s W → ℝ) (C : ℝ) : Prop :=
  ∀ (j : J) (h : E.C1ProductSpace s W), |Ψ j h| ≤ C * ∏ l, E.normC1 s (h l).1
def IsUniformlyBounded {J : Set ℕ+} (Ψ : J → E.C1ProductSpace s W → ℝ) : Prop :=
  (∃ C : ℝ, UniformEstimate Ψ C) ∧ (⨆ j, operatorBound (Ψ j)) < ⊤ ∧
    UniformEstimate Ψ (⨆ j, operatorBound (Ψ j)).toReal
def IsEquicontinuousFamily {J : Set ℕ+} (Ψ : J → E.C1ProductSpace s W → ℝ) : Prop :=
  ∀ C : ℝ, UniformEstimate Ψ C →
    (∀ (f g : E.C1ProductSpace s W) (j : J), |Ψ j f - Ψ j g| ≤
      C * ∑ l, E.normC1 s ((f l).1 - (g l).1) *
        ∏ l' ∈ Finset.univ.erase l, (E.normC1 s (f l').1 + E.normC1 s (g l').1)) ∧
    ∀ (u : J → E.C1ProductSpace s W) (h : E.C1ProductSpace s W),
      (∀ l, Tendsto (fun j => E.normC1 s ((u j l).1 - (h l).1)) (indexAtTop J) (𝓝 0)) →
      ∃ c : ℝ, Tendsto (fun j => Ψ j (u j)) (indexAtTop J) (𝓝 c) ∧
        Tendsto (fun j => Ψ j h) (indexAtTop J) (𝓝 c)
def ConvergesPointwise {J : Set ℕ+} (Ψ : J → E.C1ProductSpace s W → ℝ) : Prop :=
  ∀ h : E.C1ProductSpace s W, ∃ c : ℝ, Tendsto (fun j => Ψ j h) (indexAtTop J) (𝓝 c)
def IsRealFormBoundedBy (S : E.C1ProductSpace s W → ℂ) (b : ℝ) : Prop :=
  (∀ h, (S h).im = 0) ∧ IsMultilinearRealForm (fun h => (S h).re) ∧
    ∀ h, ‖S h‖ ≤ b * ∏ l, E.normC1 s (h l).1
end Forms
section Requirements
variable (s : StandingParameters) (E : Ambient) {q : ℕ}
def C1WithinIsBanach : Prop :=
  ∀ W : Set (E.Carrier s), E.IsCompactSubset s W →
    E.c1Within s W = {f | E.IsC1 s f ∧ E.closedSupport s f ⊆ W} ∧
    IsBanachFunctionSpace (E.c1Within s W) (E.normC1 s)
def ProductElementsAreSepTuples (W : Fin q → Set (E.Carrier s)) : Prop :=
  ∀ h : E.C1ProductSpace s W, E.IsSepC1Tuple s (⋃ l, W l) (components h)
def ConvergentBoundedFormsEquicontinuous (W : Fin q → Set (E.Carrier s)) : Prop :=
  ∀ (J : Set ℕ+) (Ψ : J → E.C1ProductSpace s W → ℝ), J.Infinite →
    (∀ j, IsMultilinearRealForm (Ψ j)) → (∀ j, IsBoundedMultilinear (Ψ j)) → ConvergesPointwise Ψ →
    IsUniformlyBounded Ψ ∧ IsEquicontinuousFamily Ψ
def TranslationContinuityC1 (M : SharpParameter) : Prop :=
  ∀ f : E.c1Compact s,
    (∀ u v : E.Carrier s,
      ENNReal.ofReal (E.normC1 s (E.translateFun s u f.1 - E.translateFun s v f.1)) ≤
          max (E.gradSup s f.1 * (E.pointDist s u v).toNNReal)
            (gradModulus f (E.pointDist s u v).toNNReal) ∧
        max (E.gradSup s f.1 * (E.pointDist s u v).toNNReal)
            (gradModulus f (E.pointDist s u v).toNNReal) ≤
          continuityModulus M f (E.pointDist s u v).toNNReal) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u v : E.Carrier s, E.pointDist s u v < δ →
      E.normC1 s (E.translateFun s u f.1 - E.translateFun s v f.1) < ε
variable {s E} {J : Set ℕ+} {Dom : J → Set (E.Carrier s)}
def coveringIndices (Dom : J → Set (E.Carrier s)) (W : Fin q → Set (E.Carrier s)) : Set ℕ+ :=
  {j | ∃ hj : j ∈ J, (⋃ l, W l) ⊆ Dom ⟨j, hj⟩}
def coveringIndex {W : Fin q → Set (E.Carrier s)} (j : coveringIndices Dom W) : J :=
  ⟨j.1, j.2.choose⟩
def restrictedCentred (Φ : (j : J) → E.TupleFunctionals s .lip (Dom j))
    {W : Fin q → Set (E.Carrier s)} (j : coveringIndices Dom W) (h : E.C1ProductSpace s W) : ℝ :=
  E.evalOrZero s (E.centredSum s (Φ (coveringIndex j)) (q := q)) (components h)
def CentredRestrictionsProperties (Φ : (j : J) → E.TupleFunctionals s .lip (Dom j))
    (W : Fin q → Set (E.Carrier s)) : Prop :=
  (∀ᶠ j in indexAtTop J, j.1 ∈ coveringIndices Dom W) ∧
  (∀ (j : coveringIndices Dom W) (h : E.C1ProductSpace s W),
    E.IsSepTuple s .lip (Dom (coveringIndex j)) (components h)) ∧
  (∀ h : E.C1ProductSpace s W, E.IsSepTuple s .cOne univ (components h)) ∧
  (∀ j : coveringIndices Dom W, IsMultilinearRealForm (restrictedCentred Φ j)) ∧
  (∀ h : E.C1ProductSpace s W, Tendsto (fun j => restrictedCentred Φ j h)
    (indexAtTop (coveringIndices Dom W))
    (𝓝 (E.evalOrZero s (E.centredSum s (E.limitFunctionals s Φ) (q := q)) (components h)))) ∧
  ((∀ j : coveringIndices Dom W, IsBoundedMultilinear (restrictedCentred Φ j)) →
    IsUniformlyBounded (restrictedCentred Φ (W := W)) ∧
      IsEquicontinuousFamily (restrictedCentred Φ (W := W)))
end Requirements
end Ambient
open Ambient ReflectionPositivity.CutoffMirrors
section Lattice
variable {q : ℕ}
def cutoffData (s : StandingParameters) (K : ℕ+) (β : ℝ) (hβ : 0 < β) : MirrorData :=
  { s with K := K, coupling := β, coupling_pos := hβ, dir := 0 }
def LatticeFunctionalBound (D : MirrorData) (q : ℕ) : Prop :=
  ∀ g : Fin q → D.Torus → ℝ, MirrorData.IsAdmissibleArg g →
    ‖D.truncatedFunctional g‖ ≤
        (4 * (D.faceCount : ℝ)) ^ q * ∏ l, TestFunctions.uniformNorm (g l) ∧
      (2 ≤ q → D.truncatedFunctional g =
        SchwingerFunctions.centredSchwinger D.L D.m D.K D.coupling g)
def torusForm (D : MirrorData) {W : Fin q → Set (Ambient.periodic.Carrier D.toStandingParameters)}
    (h : Ambient.periodic.C1ProductSpace D.toStandingParameters W) : ℂ :=
  D.truncatedFunctional (components h)
def periodizedForm (D : MirrorData) {s : StandingParameters}
    {W : Fin q → Set (Ambient.euclidean.Carrier s)} (h : Ambient.euclidean.C1ProductSpace s W) : ℂ :=
  D.truncatedFunctional fun l =>
    TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (h l).1
def TorusSideAdmissible (D : MirrorData) {s : StandingParameters}
    (W : Fin q → Set (Ambient.euclidean.Carrier s)) : Prop :=
  TestFunctions.HasDiameterLE (⋃ l, W l) (PeriodicLattice.torusSide D.L D.m / 2)
def PeriodizedFormBound (D : MirrorData) {s : StandingParameters}
    (W : Fin q → Set (Ambient.euclidean.Carrier s)) : Prop :=
  (∀ h ∈ Ambient.euclidean.lipWithin s (⋃ l, W l),
    TestFunctions.IsLipschitzFor D.torusDist
        (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) h) ∧
      TestFunctions.uniformNorm (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) h) =
        TestFunctions.uniformNorm h) ∧
  (∀ h ∈ Ambient.euclidean.lipWithin s (⋃ l, W l),
    ∀ h' ∈ Ambient.euclidean.lipWithin s (⋃ l, W l), ∀ a b : ℝ,
      TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (a • h + b • h') =
        a • TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) h +
          b • TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) h') ∧
  (∀ h : Ambient.euclidean.C1ProductSpace s W, MirrorData.PairwiseDisjointSupp (D := D)
    fun l => TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) (h l).1) ∧
  IsRealFormBoundedBy (periodizedForm D (W := W)) ((4 * (D.faceCount : ℝ)) ^ q)
def TorusSequencesEquicontinuous (s : StandingParameters)
    (W : Fin q → Set (Ambient.periodic.Carrier s)) : Prop :=
  ∀ (J : Set ℕ+) (K : J → ℕ+) (β : J → ℝ) (hβ : ∀ j, 0 < β j), J.Infinite →
    let Ψ : J → Ambient.periodic.C1ProductSpace s W → ℝ := fun j h =>
      ((cutoffData s (K j) (β j) (hβ j)).truncatedFunctional (components h)).re
    (∀ j, IsMultilinearRealForm (Ψ j) ∧ IsBoundedMultilinear (Ψ j)) ∧
      (ConvergesPointwise Ψ → IsUniformlyBounded Ψ ∧ IsEquicontinuousFamily Ψ)
def EuclideanSequencesEquicontinuous (s : StandingParameters)
    (W : Fin q → Set (Ambient.euclidean.Carrier s)) : Prop :=
  ∀ (J : Set ℕ+) (D : J → MirrorData), J.Infinite → (∀ j, (D j).L = s.L) →
    (∀ j, TorusSideAdmissible (D j) W) →
    let Ψ : J → Ambient.euclidean.C1ProductSpace s W → ℝ := fun j h =>
      (periodizedForm (D j) h).re
    (∀ j, IsMultilinearRealForm (Ψ j) ∧ IsBoundedMultilinear (Ψ j)) ∧
      (ConvergesPointwise Ψ → IsUniformlyBounded Ψ ∧ IsEquicontinuousFamily Ψ)
end Lattice
end LimitSpaces
end YangMills.Construction
end
