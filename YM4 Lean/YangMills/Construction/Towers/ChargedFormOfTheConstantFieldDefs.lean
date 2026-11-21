import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open Tower.UnitLatticeL2 Tower.UnitaryCombinations
namespace Tower.ConstantFieldSymbols
open MagneticWeyl
def trigMatrixSum {ι : Type} [Fintype ι] (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) (q : AmbientSpace) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ k, (Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) * fourierChar (n k) q) • M k
structure WeylTerm where
  offset : Fin 4 → ℤ
  comp : Fin 4
  coeff : ℂ
  freq : ℝ
def WeylTerm.eval (l : WeylTerm) (L : ℕ) (φ : ℝ) (w : VectorL2 L 4) : ScalarL2 L :=
  (l.coeff * Complex.exp (Complex.I * ((l.freq * φ : ℝ) : ℂ))) •
    magneticWeyl L φ l.offset (coord w l.comp)
structure TermPair where
  conjTerm : WeylTerm
  term : WeylTerm
  coeff : ℂ
  freq : ℝ
def TermPair.totalFreq (P : TermPair) : ℝ :=
  P.freq + P.term.freq - P.conjTerm.freq + (symplecticForm (-P.conjTerm.offset) P.term.offset : ℝ) / 2
def TermPair.offset (P : TermPair) : Fin 4 → ℤ := P.term.offset - P.conjTerm.offset
def TermPair.coeffMatrix (P : TermPair) : Matrix (Fin 4) (Fin 4) ℂ :=
  (P.coeff * conj P.conjTerm.coeff * P.term.coeff) • Matrix.single P.conjTerm.comp P.term.comp 1
def pairsSymbol {ι : Type} [Fintype ι] (P : ι → TermPair) : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ :=
  trigMatrixSum (fun k => (P k).totalFreq) (fun k => (P k).offset) (fun k => (P k).coeffMatrix)
def pairsForm {ι : Type} [Fintype ι] (P : ι → TermPair) (L : ℕ) (φ : ℝ)
    (w : VectorL2 L 4) : ℂ :=
  ∑ k, ((P k).coeff * Complex.exp (Complex.I * (((P k).freq * φ : ℝ) : ℂ))) *
    inner ℂ ((P k).conjTerm.eval L φ w) ((P k).term.eval L φ w)
def basisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
def faceTerm (μ ν : Fin 4) (ε : ℝ) : Fin 4 → WeylTerm :=
  ![⟨0, μ, 1, 0⟩, ⟨basisVec μ, ν, 1, 0⟩, ⟨basisVec ν, μ, -1, ε⟩, ⟨0, ν, -1, ε⟩]
def vertexTerm (μ : Fin 4) (s : Bool) : WeylTerm :=
  if s then ⟨-basisVec μ, μ, 1, 0⟩ else ⟨0, μ, -1, 0⟩
def fluxWeight (μ ν : Fin 4) : ℝ := if μ = 0 ∧ ν = 1 then 1 else 0
def phaseWeight (i j : Fin 4) (s : Bool) : ℂ :=
  if i = j then 1 / 2 else if (i < j ∧ s = false) ∨ (j < i ∧ s = true) then 1 else 0
abbrev ChargedIdx : Type :=
  ({d : Fin 4 × Fin 4 // d.1 < d.2} × Fin 4 × Fin 4 × Bool) ⊕ ((Fin 4 × Bool) × (Fin 4 × Bool))
def chargedTermPair : ChargedIdx → TermPair
  | Sum.inl (d, i, j, s) =>
    ⟨faceTerm d.1.1 d.1.2 (fluxWeight d.1.1 d.1.2) i,
      faceTerm d.1.1 d.1.2 (fluxWeight d.1.1 d.1.2) j, phaseWeight i j s,
      fluxWeight d.1.1 d.1.2 * (if s then 1 / 2 else -1 / 2)⟩
  | Sum.inr (a, b) => ⟨vertexTerm a.1 a.2, vertexTerm b.1 b.2, 1, 0⟩
def chargedSymbolExplicit : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ := pairsSymbol chargedTermPair
def IsLieFormOf {L : ℕ} (w : VectorL2 L 4) (B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop :=
  B ∈ FullSpace.edgeFormSpace (meshAt L 0 0) ∧
    ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = w x μ • raisingPauli + conj (w x μ) • loweringPauli
end Tower.ConstantFieldSymbols
end YangMills.Construction
end
