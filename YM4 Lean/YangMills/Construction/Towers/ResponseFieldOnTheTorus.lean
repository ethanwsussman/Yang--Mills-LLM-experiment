import YangMills.Construction.Towers.NormaliserOfAStepOnTheTowerOfASide
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TorusResponseField
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.CriticalBranchResponse
open YangMills.Construction.PeriodicOperators.Tempered (UnitEdge realComponent imagComponent)
def responseField (L n k : ℕ) (B : Edge L n k k → ComplexMatrix2) : RealPeriodicField L n k :=
  (meshScaledResponse L n k B, crossingSmoothingTranspose L n k (periodicDefect L n k B),
    periodicDefect L n k B)
def linearizedField (L n k : ℕ) (B : Edge L n k k → ComplexMatrix2) : RealPeriodicField L n k :=
  Classical.epsilon fun r : RealPeriodicField L n k =>
    (r.1 : Edge L n k 0 → ComplexMatrix2) =
        leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B ∧
      r.2 = (responseField L n k B).2
def complexify {L n k : ℕ} (r : RealPeriodicField L n k) : PeriodicField L n k :=
  Classical.epsilon fun ζ : PeriodicField L n k => ζ.RealizedBy r
def topForm (L n k : ℕ) (B : UnitEdge L n → ComplexMatrix2) : Edge L n k k → ComplexMatrix2 :=
  B ∘ topEdgeEquivUnit L n k
def complexResponse (L n k : ℕ) (B : UnitEdge L n → ComplexMatrix2) : PeriodicField L n k :=
  complexify (responseField L n k (topForm L n k (realComponent B))) +
    Complex.I •
      complexify (responseField L n k (topForm L n k (imagComponent B)))
def blochWaveField (L n k : ℕ) (hL : 0 < L) (κ : Fin 4 → ℂ)
    (ε : (FullSpace.fieldPeriodicData L k hL).UnitQuot → ℂ) : PeriodicField L n k :=
  Classical.epsilon fun ζ : PeriodicField L n k =>
    ζ.pauliCoeffs hL = PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) κ ε
def constantFinestForm (L k : ℕ) (ξ : Fin 4 → ComplexMatrix2) : FullSpace.Edge L k 0 → ComplexMatrix2 :=
  open Classical in
  FullSpace.extendOddly fun b =>
    ∑ ρ, if b.terminal - b.initial = InfiniteLattice.axisStep (meshAt L k 0) ρ then ξ ρ else 0
def constantFieldAmplitude (L k : ℕ) (hL : 0 < L) (ξ : Fin 4 → ComplexMatrix2) :
    (FullSpace.fieldPeriodicData L k hL).UnitQuot → ℂ :=
  FullSpace.tripleAmplitude L k hL
    (PeriodicOperators.LogDetSecondDerivs.descendField
      (PeriodicOperators.colourEdges L k 0) 1
      ((FullSpace.edgePauliCoordinates L k 0).coeffs (constantFinestForm L k ξ))) 0 0
end YangMills.Construction.Tower.TorusResponseField
end
