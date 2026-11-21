import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation Estimates
namespace LawAtTop
variable {F : BlockFrame}
abbrev TermPlace (F : BlockFrame) : Type := ↥(finiteCells F) ⊕ ↥(sitesOfCells (finiteCells F) F.depth)
def termCell : TermPlace F → F.Cell := Sum.elim (fun Y => Y.1) (fun y => enclosingCell y.1)
def exponentTerm (star : Bool) (a ρA x : ℝ) (m : ℕ) (φ : LocalFamily) :
    TermPlace F → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  Sum.elim (fun Y η V => cellExponent star a ρA x m Y.1 V η) (fun y η V => - centredExpansion star a ρA m φ y.1 η V)
def exponentSum (star : Bool) (a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ q, exponentTerm star a ρA x m φ q η V
def seriesExpansionTerm (star : Bool) (a ρA : ℝ) (m : ℕ) (h : LocalFamily) :
    TermPlace F → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  Sum.elim (fun _ _ _ => 0) (fun y η V => centredExpansion star a ρA m h y.1 η V)
def termDecayWeight {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) : TermPlace F → ℝ :=
  Sum.elim (fun Y => 2 * (bondSpan Y.1 c : ℝ)) (fun y => (bondSpan (enclosingCell y.1) c : ℝ))
structure LawAtTop (star : Bool) (a ρA x : ℝ) (m : ℕ) (ρ lam κ α β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (N N' : ℕ)
    (φ h : LocalFamily) (V : F.GaugeField F.top) : Prop where
  ρ_pos : 0 < ρ
  x_pos : 0 < x
  κ_pos : 0 < κ
  lam_pos : 0 < lam
  cutoff : IsCutoff ρ p
  α_nonneg : 0 ≤ α
  β_nonneg : 0 ≤ β
  Cq_nonneg : ∀ q, 0 ≤ Cq q
  convex : ∃ (Ψ : StepVariable (finiteCells F) → ℝ) (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → exponentSum star a ρA x m φ η V = Ψ η) ∧
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) Ψ K ∧
    ∀ (b : ↥(chordBonds (finiteCells F))) (u : BondVector), |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (x * lam / 4) * ‖u‖
  integrable : Integrable (ballDensity (cutoffFactor ρ p) fun η => exponentSum star a ρA x m φ η V)
  card_bonds_le : ∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N
  card_places_le : ∀ u : F.Cell, (Finset.univ.filter fun q : TermPlace F => termCell q = u).card ≤ N'
  mem_cells : ∀ Y : F.Cell, Y ∈ finiteCells F
  cell_nonempty : ∀ Y : F.Cell, ∃ y : ↥(sitesOfCells (finiteCells F) F.depth), enclosingCell y.1 = Y
  smooth_term : ∀ q, JointlyContDiffOnBalls ρ V (exponentTerm star a ρA x m φ q)
  smooth_expansion : ∀ q, JointlyContDiffOnBalls ρ V (seriesExpansionTerm star a ρA m h q)
  third_term : ∀ (Y : ↥(finiteCells F)) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    ContDiffOn ℝ 1 (fieldDeriv (exponentTerm star a ρA x m φ (Sum.inl Y)) V c X) {η | ∀ b, ‖η b‖ < ρ}
  size_cell : ∀ (Y : ↥(finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) (fun η => exponentSum star a ρA x m φ η V) Cq x κ
      (β * Real.exp (-(2 ^ 4 * κ * termDecayWeight c (Sum.inl Y))))
      (fun b => (cellSupDist (enclosingCell b.1.1) Y.1 : ℝ)) (fieldDeriv (exponentTerm star a ρA x m φ (Sum.inl Y)) V c X)
  size_site : ∀ (y : ↥(sitesOfCells (finiteCells F) F.depth)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
    AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) (fun η => exponentSum star a ρA x m φ η V) Cq x κ
      (β * Real.exp (-(2 ^ 4 * κ * termDecayWeight c (Sum.inr y))))
      (fun b => (cellSupDist (enclosingCell b.1.1) (enclosingCell y.1) : ℝ))
      (fieldDeriv (exponentTerm star a ρA x m φ (Sum.inr y)) V c X)
  size_expansion : ∀ (y : ↥(sitesOfCells (finiteCells F) F.depth)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
    AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) (fun η => exponentSum star a ρA x m φ η V) Cq x κ
      (α * Real.exp (-(2 ^ 4 * κ * (bondSpan (enclosingCell y.1) c : ℝ))))
      (fun b => (cellSupDist (enclosingCell b.1.1) (enclosingCell y.1) : ℝ))
      (fieldDeriv (seriesExpansionTerm star a ρA m h (Sum.inr y)) V c X)
end LawAtTop
end YangMills.Construction
end
