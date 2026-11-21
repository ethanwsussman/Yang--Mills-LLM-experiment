import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EmptySupremumPauliMatricesAndFormsOnFiniteSets
import YangMills.Construction.Lattice.KernelsAndWeightedRowAndColumnNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace Matrices.ComplexMatrix2
theorem pauli_mem_traceless (a : Fin 3) : pauli a ∈ traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
def pauliTraceless (a : Fin 3) : ↥traceless := ⟨pauli a, pauli_mem_traceless a⟩
def pauliCombination (c : Fin 3 → ℂ) : ComplexMatrix2 := ∑ a, c a • pauli a
end Matrices.ComplexMatrix2
namespace PeriodicLattice
def IsPairingAdjoint {S T : Type*} [Finite S] [Finite T] (s t : ℝ)
    (Φ : BondMaps.BondValued S →ₗ[ℂ] BondMaps.BondValued T)
    (Ψ : BondMaps.BondValued T →ₗ[ℂ] BondMaps.BondValued S) : Prop :=
  ∀ (u : BondMaps.BondValued S) (v : BondMaps.BondValued T),
    scaledPairingSum t (Φ u) v = scaledPairingSum s u (Ψ v)
variable {L m : ℕ} {j : ℤ}
abbrev ComplexBondForm (L m : ℕ) (j : ℤ) : Type :=
  {A : Bond L m j → Matrices.ComplexMatrix2 // IsBondForm complexLieAlgebra A}
abbrev ComplexPlaquetteForm (L m : ℕ) (j : ℤ) : Type :=
  {F : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2 // IsPlaquetteForm complexLieAlgebra F}
def ComplexBondForm.onPositive (A : ComplexBondForm L m j) (b : PositivelyOrientedBond L m j) :
    ↥Matrices.ComplexMatrix2.traceless :=
  ⟨A.1 b.1, A.2.1 b.1 b.2⟩
def ComplexPlaquetteForm.onPlaquettes (F : ComplexPlaquetteForm L m j) (p : Plaquette L m j) :
    ↥Matrices.ComplexMatrix2.traceless :=
  ⟨F.1 p.firstAxis p.secondAxis p.origin, F.2.1 _ _ _ p.firstAxis_lt_secondAxis⟩
def InnersAreScaledSums (L m : ℕ) (j : ℤ) (ξ : ℝ) [Finite (Site L m j)]
    [Finite (PositivelyOrientedBond L m j)] [Finite (Plaquette L m j)] : Prop :=
  Function.Bijective (ComplexBondForm.onPositive : ComplexBondForm L m j → _) ∧
    Function.Bijective (ComplexPlaquetteForm.onPlaquettes : ComplexPlaquetteForm L m j → _) ∧
    (∀ u v : BondMaps.BondValued (Site L m j),
      siteInner ξ (fun x => (u x : Matrices.ComplexMatrix2)) (fun x => (v x : Matrices.ComplexMatrix2)) =
        scaledPairingSum (ξ ^ 4) u v) ∧
    (∀ A B : ComplexBondForm L m j,
      bondFormInner ξ A.1 B.1 = scaledPairingSum (ξ ^ 4) A.onPositive B.onPositive) ∧
    ∀ F H : ComplexPlaquetteForm L m j,
      plaquetteFormInner ξ F.1 H.1 = scaledPairingSum (ξ ^ 4) F.onPlaquettes H.onPlaquettes
def CovDerivAdjointIsPairingAdjoint (L m : ℕ) (j : ℤ) (ξ : ℝ)
    [Finite (PositivelyOrientedBond L m j)] [Finite (Plaquette L m j)] : Prop :=
  ∀ U : Bond L m j → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
    ∃ (Φ : BondMaps.BondValued (PositivelyOrientedBond L m j) →ₗ[ℂ] BondMaps.BondValued (Plaquette L m j))
      (Ψ : BondMaps.BondValued (Plaquette L m j) →ₗ[ℂ] BondMaps.BondValued (PositivelyOrientedBond L m j)),
      IsPairingAdjoint (ξ ^ 4) (ξ ^ 4) Φ Ψ ∧
      (∀ (A : ComplexBondForm L m j) (p : Plaquette L m j),
        (Φ A.onPositive p : Matrices.ComplexMatrix2) =
          covExteriorDeriv ξ U A.1 p.firstAxis p.secondAxis p.origin) ∧
      (∀ (F : ComplexPlaquetteForm L m j) (b : PositivelyOrientedBond L m j),
        (Ψ F.onPlaquettes b : Matrices.ComplexMatrix2) = covExteriorDerivAdjoint ξ U F.1 b.1) ∧
      ∀ (F : ComplexPlaquetteForm L m j) (B : Bond L m j → Matrices.ComplexMatrix2),
        (IsBondForm complexLieAlgebra B ∧ ∀ A, IsBondForm complexLieAlgebra A →
          bondFormInner ξ B A = plaquetteFormInner ξ F.1 (covExteriorDeriv ξ U A)) ↔
        B = covExteriorDerivAdjoint ξ U F.1
end PeriodicLattice
namespace SeparatedSequence
namespace DepthChain
variable {L m : ℕ} {N : DepthParameters L m} (A : DepthChain N)
def siteEval (f : ↥(A.siteFields complexLieAlgebra)) (x : ↥A.baseSites) :
    ↥Matrices.ComplexMatrix2.traceless :=
  ⟨f.1 x.1, f.2.1 x.1⟩
def plaquetteEval (X : ↥(A.plaquetteForms complexLieAlgebra)) (p : ↥A.basePlaquettes) :
    ↥Matrices.ComplexMatrix2.traceless :=
  ⟨X.1 p.1, X.2.1 p.1⟩
def InnersAreScaledSums [Finite ↥A.baseSites] [Finite ↥A.orientedBaseBonds]
    [Finite ↥A.basePlaquettes] : Prop :=
  Function.Bijective A.siteEval ∧ Function.Bijective A.formEval ∧
    Function.Bijective A.plaquetteEval ∧
    (∀ f g : ↥(A.siteFields complexLieAlgebra),
      A.siteInner f.1 g.1 = scaledPairingSum (N.eta ^ 4) (A.siteEval f) (A.siteEval g)) ∧
    (∀ a a' : ↥A.formSpace,
      A.bondInner a.1 a'.1 = scaledPairingSum (N.eta ^ 4) (A.formEval a) (A.formEval a')) ∧
    ∀ X X' : ↥(A.plaquetteForms complexLieAlgebra),
      A.plaquetteInner X.1 X'.1 =
        scaledPairingSum (N.eta ^ 4) (A.plaquetteEval X) (A.plaquetteEval X')
def FormTransposeIsPairingAdjoint [Finite ↥A.orientedBaseBonds] : Prop :=
  ∀ (C : Type) [Finite C] (K : ↥A.formSpace →ₗ[ℂ] BondMaps.BondValued C),
    ∃ (Φ : BondMaps.BondValued ↥A.orientedBaseBonds →ₗ[ℂ] BondMaps.BondValued C)
      (Ψ : BondMaps.BondValued C →ₗ[ℂ] BondMaps.BondValued ↥A.orientedBaseBonds),
      IsPairingAdjoint (N.eta ^ 4) 1 Φ Ψ ∧
      (∀ a, Φ (A.formEval a) = K a) ∧
      (∀ w, A.formEval (A.formTranspose K w) = Ψ w) ∧
      ∀ (w : BondMaps.BondValued C) (B : ↥A.formSpace),
        (∀ a : ↥A.formSpace, plainInner (K a) w = A.bondInner a.1 B.1) ↔
        B = A.formTranspose K w
def CovDivergenceIsPairingAdjoint [Finite ↥A.baseSites] [Finite ↥A.orientedBaseBonds] : Prop :=
  ∀ U ∈ A.gaugeFields,
    ∃ (Φ : BondMaps.BondValued ↥A.baseSites →ₗ[ℂ] BondMaps.BondValued ↥A.orientedBaseBonds)
      (Ψ : BondMaps.BondValued ↥A.orientedBaseBonds →ₗ[ℂ] BondMaps.BondValued ↥A.baseSites),
      IsPairingAdjoint (N.eta ^ 4) (N.eta ^ 4) Φ Ψ ∧
      (∀ (f : ↥(A.siteFields complexLieAlgebra)) (b : ↥A.orientedBaseBonds),
        (Φ (A.siteEval f) b : Matrices.ComplexMatrix2) = A.covGradient U f.1 b.1) ∧
      (∀ (a : ↥A.formSpace) (x : ↥A.baseSites),
        (Ψ (A.formEval a) x : Matrices.ComplexMatrix2) = A.covDivergence complexLieAlgebra U a.1 x.1) ∧
      ∀ (a : ↥A.formSpace) (B : SiteAtLevel L m N.K 0 → Matrices.ComplexMatrix2),
        (B ∈ A.siteFields complexLieAlgebra ∧ ∀ f ∈ A.siteFields complexLieAlgebra,
          A.siteInner B f = A.bondInner a.1 (A.covGradient U f)) ↔
        B = A.covDivergence complexLieAlgebra U a.1
def CovCurlAdjointIsPairingAdjoint [Finite ↥A.orientedBaseBonds]
    [Finite ↥A.basePlaquettes] : Prop :=
  ∀ U ∈ A.gaugeFields,
    ∃ (Φ : BondMaps.BondValued ↥A.orientedBaseBonds →ₗ[ℂ] BondMaps.BondValued ↥A.basePlaquettes)
      (Ψ : BondMaps.BondValued ↥A.basePlaquettes →ₗ[ℂ] BondMaps.BondValued ↥A.orientedBaseBonds),
      IsPairingAdjoint (N.eta ^ 4) (N.eta ^ 4) Φ Ψ ∧
      (∀ (a : ↥A.formSpace) (p : ↥A.basePlaquettes),
        (Φ (A.formEval a) p : Matrices.ComplexMatrix2) = A.covCurl U a.1 p.1) ∧
      (∀ (X : ↥(A.plaquetteForms complexLieAlgebra)) (b : ↥A.orientedBaseBonds),
        (Ψ (A.plaquetteEval X) b : Matrices.ComplexMatrix2) =
          A.covCurlAdjoint complexLieAlgebra U X.1 b.1) ∧
      ∀ (X : ↥(A.plaquetteForms complexLieAlgebra)) (B : BondAtLevel L m N.K 0 → Matrices.ComplexMatrix2),
        (B ∈ A.bondForms complexLieAlgebra ∧ ∀ a ∈ A.bondForms complexLieAlgebra,
          A.bondInner B a = A.plaquetteInner X.1 (A.covCurl U a)) ↔
        B = A.covCurlAdjoint complexLieAlgebra U X.1
end DepthChain
end SeparatedSequence
namespace LieInnerProduct
open Matrices.ComplexMatrix2
def RealInnerProduct : Prop :=
  (∀ X ∈ hermitianTraceless, ∀ Y ∈ hermitianTraceless, (halfTracePairing X Y).im = 0) ∧
    (∀ Y ∈ hermitianTraceless, Y.conjTranspose * Y = Y ^ 2 ∧
      Y ^ 2 = halfTracePairing Y Y • (1 : Matrices.ComplexMatrix2) ∧
      ((operatorNorm Y ^ 2 : ℝ) : ℂ) = halfTracePairing Y Y) ∧
    (∀ X Y : LieElement, ((inner ℝ X Y : ℝ) : ℂ) = halfTracePairing X.toMatrix Y.toMatrix) ∧
    ∀ Y : LieElement, ‖Y‖ = operatorNorm Y.toMatrix
def PauliExpansion : Prop :=
  (∀ Y ∈ traceless, (∃! c : Fin 3 → ℂ, Y = pauliCombination c) ∧
      Y = pauliCombination fun a => halfTracePairing (pauli a) Y) ∧
    (∀ c, pauliCombination c ∈ traceless) ∧
    (∀ c, pauliCombination c ∈ hermitianTraceless ↔ ∀ a, (c a).im = 0) ∧
    (∀ c c', halfTracePairing (pauliCombination c) (pauliCombination c') = ∑ a, c a * c' a) ∧
    ∀ c, halfTrace ((pauliCombination c).conjTranspose * pauliCombination c) =
      ((∑ a, ‖c a‖ ^ 2 : ℝ) : ℂ)
def PairingNondegenerate : Prop :=
  ∀ (S : Type) [Finite S] (t : ℝ), 0 < t → ∀ u : BondMaps.BondValued S,
    (∀ v : BondMaps.BondValued S, (∀ s, (v s : Matrices.ComplexMatrix2) ∈ hermitianTraceless) →
      scaledPairingSum t v u = 0) → u = 0
def UniqueAdjointOfLinearMap : Prop :=
  ∀ (S T : Type) [Finite S] [Finite T] (s t : ℝ), 0 < s → 0 < t →
    ∀ Φ : BondMaps.BondValued S →ₗ[ℂ] BondMaps.BondValued T,
      (∃! Ψ : BondMaps.BondValued T →ₗ[ℂ] BondMaps.BondValued S, IsPairingAdjoint s t Φ Ψ) ∧
      ∀ (θ : ℂ) (r : ℝ), 0 < r → ∀ Ψ : BondMaps.BondValued T →ₗ[ℂ] BondMaps.BondValued S,
        IsPairingAdjoint s t Φ Ψ → IsPairingAdjoint (r * s) (r * t) (θ • Φ) (θ • Ψ)
def AdjointInPauliBasis : Prop :=
  ∀ (T : ↥traceless →ₗ[ℂ] ↥traceless) (τ : Matrix (Fin 3) (Fin 3) ℂ),
    (∀ b, T (pauliTraceless b) = ∑ a, τ a b • pauliTraceless a) →
    (∀ a, endTranspose T (pauliTraceless a) = ∑ b, τ a b • pauliTraceless b) ∧
    ∀ b, endTranspose T (pauliTraceless b) = ∑ a, τ.transpose a b • pauliTraceless a
def OnePointAndFiniteSetPairings : Prop :=
  (∀ (P : Type) [Unique P] (Y Y' : ↥traceless),
    halfTracePairing (Y : Matrices.ComplexMatrix2) (Y' : Matrices.ComplexMatrix2) =
      scaledPairingSum 1 (fun _ : P => Y) (fun _ : P => Y')) ∧
    (∀ (C : Type) [Finite C] (w w' : BondMaps.BondValued C),
      SeparatedSequence.DepthChain.plainInner w w' = scaledPairingSum 1 w w') ∧
    ∀ T : ↥traceless →ₗ[ℂ] ↥traceless,
      (∀ R : ↥traceless →ₗ[ℂ] ↥traceless,
        (∀ Y Y' : ↥traceless, halfTracePairing (T Y : Matrices.ComplexMatrix2) (Y' : Matrices.ComplexMatrix2) =
          halfTracePairing (Y : Matrices.ComplexMatrix2) (R Y' : Matrices.ComplexMatrix2)) ↔
        R = endTranspose T) ∧
      ∀ (P : Type) [Unique P], IsPairingAdjoint 1 1 (T.compLeft P) ((endTranspose T).compLeft P)
def BaseLatticePairings : Prop :=
  ∀ (L m : ℕ) (N : SeparatedSequence.DepthParameters L m) (A : SeparatedSequence.DepthChain N),
    ∃ (_ : Finite ↥A.baseSites) (_ : Finite ↥A.orientedBaseBonds) (_ : Finite ↥A.basePlaquettes),
      A.InnersAreScaledSums ∧ A.FormTransposeIsPairingAdjoint ∧
        A.CovDivergenceIsPairingAdjoint ∧ A.CovCurlAdjointIsPairingAdjoint
def PeriodicLatticePairings : Prop :=
  ∀ (L m : ℕ) (j : ℤ) (ξ : ℝ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → -(m : ℤ) < j → 0 < ξ →
    ∃ (_ : Finite (Site L m j)) (_ : Finite (PositivelyOrientedBond L m j)) (_ : Finite (Plaquette L m j)),
      PeriodicLattice.InnersAreScaledSums L m j ξ ∧ CovDerivAdjointIsPairingAdjoint L m j ξ
def Statement : Prop :=
  RealInnerProduct ∧ PauliExpansion ∧ PairingNondegenerate ∧
    UniqueAdjointOfLinearMap ∧ AdjointInPauliBasis ∧ OnePointAndFiniteSetPairings ∧
    BaseLatticePairings ∧ PeriodicLatticePairings
end LieInnerProduct
end YangMills.Construction
