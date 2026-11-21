import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsInTheLawAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation LawAtTop Estimates
variable {F : BlockFrame}
def interpolatedExponentTerm (s a ρA x : ℝ) (m : ℕ) (φ : LocalFamily) :
    TermPlace F → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  Sum.elim (fun Y η V => interpolatedBlockExponent s a ρA x m Y.1 V η)
    (fun y η V => - interpolatedExpansion s a ρA m φ y.1 η V)
def interpolatedExponentOfTerms (s a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ q, interpolatedExponentTerm s a ρA x m φ q η V
def interpolatedCellExponent (s a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ Z : ↥(finiteCells F), interpolatedBlockExponent s a ρA x m Z.1 V η
structure InterpolatedLawAtTop (s a ρA x : ℝ) (m : ℕ) (ρ lam κ β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (N N' : ℕ)
    (φ : LocalFamily) (V : F.GaugeField F.top) : Prop where
  ρ_pos : 0 < ρ
  x_pos : 0 < x
  κ_pos : 0 < κ
  lam_pos : 0 < lam
  cutoff : IsCutoff ρ p
  β_nonneg : 0 ≤ β
  Cq_nonneg : ∀ q, 0 ≤ Cq q
  convex : ∃ (Ψ : StepVariable (finiteCells F) → ℝ) (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → interpolatedExponentOfTerms s a ρA x m φ η V = Ψ η) ∧
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) Ψ K ∧
    ∀ (b : ↥(chordBonds (finiteCells F))) (v : BondVector), |bondPartialDeriv Ψ b 0 v| ≤ Real.sqrt (x * lam / 4) * ‖v‖
  integrable : Integrable (ballDensity (cutoffFactor ρ p) fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
  card_bonds_le : ∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N
  card_places_le : ∀ w : F.Cell, (Finset.univ.filter fun q : TermPlace F => termCell q = w).card ≤ N'
  mem_cells : ∀ Y : F.Cell, Y ∈ finiteCells F
  smooth_term : ∀ q, JointlyContDiffOnBalls ρ V (interpolatedExponentTerm s a ρA x m φ q)
  third_term : ∀ (Y : ↥(finiteCells F)) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    ContDiffOn ℝ 1 (fieldDeriv (interpolatedExponentTerm s a ρA x m φ (Sum.inl Y)) V c X) {η | ∀ b, ‖η b‖ < ρ}
  size_cell : ∀ (Y : ↥(finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) Cq x κ
      (β * Real.exp (-(2 ^ 4 * κ * termDecayWeight c (Sum.inl Y))))
      (fun b => (cellSupDist (enclosingCell b.1.1) Y.1 : ℝ)) (fieldDeriv (interpolatedExponentTerm s a ρA x m φ (Sum.inl Y)) V c X)
  size_site : ∀ (y : ↥(sitesOfCells (finiteCells F) F.depth)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
    AreUnitVectors X →
    HasLocalSize ρ (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) Cq x κ
      (β * Real.exp (-(2 ^ 4 * κ * termDecayWeight c (Sum.inr y))))
      (fun b => (cellSupDist (enclosingCell b.1.1) (enclosingCell y.1) : ℝ))
      (fieldDeriv (interpolatedExponentTerm s a ρA x m φ (Sum.inr y)) V c X)
structure CutoffSlopeBoundAtCell (s a ρA x : ℝ) (m : ℕ) (ρ κ α : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (Y : F.Cell) {j : ℕ} (c₀ : Fin j → F.Site F.top × Fin 4)
    (H : StepVariable (finiteCells F) → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ}
  size : HasLocalSize ρ (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) Cq x κ
    (α * Real.exp (-(2 ^ 4 * κ * (bondSpan Y c₀ : ℝ)))) (fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) H
def cumulantSlotTerms {M : ℕ} (Y : F.Cell) (i₀ : Fin M) (only : Fin M → Prop) (i : Fin M) (q : TermPlace F) : Prop :=
  (i = i₀ ∧ termCell q = Y ∧ ∃ Z : ↥(finiteCells F), q = Sum.inl Z) ∨
    (i ≠ i₀ ∧ (only i → ∃ Z : ↥(finiteCells F), q = Sum.inl Z))
open Classical in
def slopeCumulantDecay : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ) (M : ℕ), 0 < κ → 0 < lam → 2 ≤ M → M ≤ 9 →
    ∃ B : (ℕ → ℝ) → ℝ, (∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B Cq) ∧
      ∀ (F : BlockFrame) (s a ρA x : ℝ) (m : ℕ) (ρ α β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (φ : LocalFamily)
        (V : F.GaugeField F.top), InterpolatedLawAtTop s a ρA x m ρ lam κ β p Cq N N' φ V → 0 ≤ α →
        ∀ (Y : F.Cell) (i₀ : Fin M) (j : Fin M → ℕ) (cc : ∀ i, Fin (j i) → F.Site F.top × Fin 4)
          (XX : ∀ i, Fin (j i) → imaginaryQuaternions) (only : Fin M → Prop) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
          (H : StepVariable (finiteCells F) → ℝ),
          CutoffSlopeBoundAtCell s a ρA x m ρ κ α p Cq φ V Y (cc i₀) H →
          (∀ i, i ≠ i₀ → AreUnitVectors (XX i)) → (∀ i, i ≠ i₀ → j i ≤ 2 ∨ (j i ≤ 3 ∧ only i)) →
          (∀ l, ∃ i a, cc i a = c l) →
          |cumulantFromMoments (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) fun i η =>
              if i = i₀ then H η else
                ∑ q ∈ Finset.univ.filter (cumulantSlotTerms Y i₀ only i),
                  fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V (cc i) (XX i) η| ≤
            B Cq * (∏ i, if i = i₀ then α else β) * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
end YangMills.Construction.Cumulants
end
