import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsInTheLawAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Estimates
variable {F : BlockFrame}
def jointSlotPlaces {M : ℕ} (Y : F.Cell) (i₀ : Fin M) (cellsOnly : Fin M → Prop) (i : Fin M)
    (q : LawAtTop.TermPlace F) : Prop :=
  (i = i₀ ∧ ∃ y : ↥(sitesOfCells (finiteCells F) F.depth), q = Sum.inr y ∧ enclosingCell y.1 = Y) ∨
    (i ≠ i₀ ∧ (cellsOnly i → ∃ Z : ↥(finiteCells F), q = Sum.inl Z))
def jointSlotTerm {M : ℕ} (star : Bool) (a ρA x : ℝ) (m : ℕ) (φ h : LocalFamily) (i₀ i : Fin M)
    (q : LawAtTop.TermPlace F) : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  if i = i₀ then LawAtTop.seriesExpansionTerm star a ρA m h q else LawAtTop.exponentTerm star a ρA x m φ q
open Classical in
def expansionExponentCumulantBound : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ) (M : ℕ), 0 < κ → 0 < lam → 2 ≤ M → M ≤ 9 →
    ∃ B : (ℕ → ℝ) → ℝ, (∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B Cq) ∧
      ∀ (F : BlockFrame) (star : Bool) (a ρA x : ℝ) (m : ℕ) (ρ α β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ)
        (φ h : LocalFamily) (V : F.GaugeField F.top),
        LawAtTop.LawAtTop star a ρA x m ρ lam κ α β p Cq N N' φ h V →
        ∀ (Y : F.Cell) (i₀ : Fin M) (j : Fin M → ℕ) (cc : ∀ i, Fin (j i) → F.Site F.top × Fin 4)
          (XX : ∀ i, Fin (j i) → imaginaryQuaternions) (cellsOnly : Fin M → Prop) (k : ℕ)
          (c : Fin k → F.Site F.top × Fin 4),
          (∀ i, AreUnitVectors (XX i)) → (∀ i, j i ≤ 2 ∨ (j i ≤ 3 ∧ i ≠ i₀ ∧ cellsOnly i)) →
          (∀ l, ∃ i a, cc i a = c l) →
          |cumulantFromMoments (cutoffFactor ρ p)
              (fun η => LawAtTop.exponentSum star a ρA x m φ η V) fun i η =>
              ∑ q ∈ Finset.univ.filter (jointSlotPlaces Y i₀ cellsOnly i),
                fieldDeriv (jointSlotTerm star a ρA x m φ h i₀ i q) V (cc i) (XX i) η| ≤
            B Cq * (∏ i, if i = i₀ then α else β) * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
end YangMills.Construction.Cumulants
end
