import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperators
import YangMills.Construction.Towers.TheResponseInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
def waveAmplitude (I : PeriodicData) (κ : Fin 4 → ℂ) (f : I.Carrier → ℂ) : I.UnitQuot → ℂ :=
  Classical.epsilon fun φ => blochWave I κ φ = f
end PeriodicOperators
namespace Tower.FullSpace
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (descendField)
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel responseDefect)
def secondVariationSymbol (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ)
    (εPlus εMinus : (fieldPeriodicData L k hL).UnitQuot → ℂ) : ℂ :=
  -(1 / 2) * JetQuad.logNumber p (vectorJet L k hL p εPlus εMinus) +
    JetQuad.logNumber p (ghostJet L k hL p εPlus εMinus)
def constantEdgeForm (L k : ℕ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    Edge L k k → Matrices.ComplexMatrix2 :=
  open Classical in
  extendOddly fun b =>
    ∑ ρ, if b.terminal - b.initial = InfiniteLattice.axisStep (meshAt L k k) ρ then ε ρ else 0
def constantFormAmplitude (L k : ℕ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k k).UnitQuot → ℂ :=
  descendField (colourEdges L k k) 1 ((edgePauliCoordinates L k k).coeffs (constantEdgeForm L k ε))
def planeWaveOfConstant (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k k).Carrier → ℂ :=
  blochWave (colourEdges L k k) p (constantFormAmplitude L k ε)
def defectOfWave (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k k).Carrier → ℂ :=
  applyKernel (responseDefect L k) (planeWaveOfConstant L k p ε)
def backgroundResponseSymbol (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k 0).UnitQuot → ℂ :=
  waveAmplitude (colourEdges L k 0) p
    (((finestMesh L k : ℝ) : ℂ) • applyKernel (responseKernel L k) (planeWaveOfConstant L k p ε))
def sourceResponseSymbol (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k 0).UnitQuot → ℂ :=
  waveAmplitude (colourEdges L k 0) p (crossingSmoothingTranspose L k (defectOfWave L k p ε))
def coarseResponseSymbol (L k : ℕ) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k k).UnitQuot → ℂ :=
  waveAmplitude (colourEdges L k k) p (defectOfWave L k p ε)
def tripleIndexFunction (L k : ℕ) (hL : 0 < L) (a j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) : LocalKernels.FieldIdx L k hL → ℂ
  | ⟨.background, ι⟩ => a ((colourEdges L k 0).mkQuot 1 ι)
  | ⟨.source, ι⟩ => j ((colourEdges L k 0).mkQuot 1 ι)
  | ⟨.coarse, ι⟩ => m ((colourEdges L k k).mkQuot 1 ι)
def tripleAmplitude (L k : ℕ) (hL : 0 < L) (a j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) : (fieldPeriodicData L k hL).UnitQuot → ℂ :=
  descendField (fieldPeriodicData L k hL) 1 (tripleIndexFunction L k hL a j m)
def responseSymbol (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ) (ε : Fin 4 → Matrices.ComplexMatrix2) :
    (fieldPeriodicData L k hL).UnitQuot → ℂ :=
  tripleAmplitude L k hL (backgroundResponseSymbol L k p ε) (sourceResponseSymbol L k p ε)
    (coarseResponseSymbol L k p ε)
def axisPauliElement (μ : Fin 4) (a : Fin 3) : Fin 4 → Matrices.ComplexMatrix2 :=
  Pi.single μ (Matrices.ComplexMatrix2.pauliFamily a)
def freePolarizationEntry (L k : ℕ) (hL : 0 < L) (μ ν : Fin 4) (p : Fin 4 → ℂ) : ℂ :=
  secondVariationSymbol L k hL p
    (tripleAmplitude L k hL (backgroundResponseSymbol L k p (axisPauliElement μ 2)) 0 0)
    (tripleAmplitude L k hL (backgroundResponseSymbol L k (-p) (axisPauliElement ν 2)) 0 0)
def freePolarizationDomain (L k : ℕ) (hL : 0 < L) : Set (Fin 4 → ℂ) :=
  {p | ∃ δ, IsJointInvertibilityWidth L k hL δ ∧ p ∈ imStrip δ ∧
    ∃ δ₀ ∈ FreeStrip.halfSupRate, p ∈ imStrip (2 * δ₀)}
def freePolarizationMatrix (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun μ ν => freePolarizationEntry L k hL μ ν p
end Tower.FullSpace
end YangMills.Construction
end
