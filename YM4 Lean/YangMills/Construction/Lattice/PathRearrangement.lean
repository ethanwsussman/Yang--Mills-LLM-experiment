import YangMills.Construction.Lattice.StepSequencePaths
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
structure AdjacentSwap (L m : ℕ) (j : ℤ) where
  pre : StepWord L m j
  fst : UnitStepVec L m j
  snd : UnitStepVec L m j
  post : StepWord L m j
namespace AdjacentSwap
def original (e : AdjacentSwap L m j) : StepWord L m j :=
  e.pre ++ e.fst :: e.snd :: e.post
def swapped (e : AdjacentSwap L m j) : StepWord L m j :=
  e.pre ++ e.snd :: e.fst :: e.post
def IsCollinear (e : AdjacentSwap L m j) : Prop :=
  (e.snd : Site L m j) = e.fst ∨ (e.snd : Site L m j) = -(e.fst : Site L m j)
def cornerSite (e : AdjacentSwap L m j) (z : Site L m j) : Site L m j :=
  z + (e.pre.map fun s => (s : Site L m j)).sum
def SpansPlaquette (e : AdjacentSwap L m j) (z : Site L m j) (p : Plaquette L m j) : Prop :=
  p.vertices = {e.cornerSite z, e.cornerSite z + e.fst, e.cornerSite z + e.snd,
    e.cornerSite z + e.fst + e.snd}
end AdjacentSwap
open Classical in
def PathRearrangementBound : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ j : ℤ, -(m : ℤ) ≤ j →
    ∀ (ℬ : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2),
      IsReversalClosed ℬ → IsGaugeField compactGaugeGroup ℬ U → ∀ z : Site L m j,
      (∀ e : AdjacentSwap L m j,
        (∀ b ∈ pathOfWord z e.original, b ∈ ℬ) → (∀ b ∈ pathOfWord z e.swapped, b ∈ ℬ) →
        (e.IsCollinear → wordHolonomy U z e.original = wordHolonomy U z e.swapped) ∧
        (¬ e.IsCollinear →
          (∃ p : Plaquette L m j, e.SpansPlaquette z p) ∧
          ∀ p : Plaquette L m j, e.SpansPlaquette z p → (∀ b ∈ p.boundaryBonds, b ∈ ℬ) →
            ∃ T ∈ compactGaugeGroup, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
              wordHolonomy U z e.original * (wordHolonomy U z e.swapped)⁻¹ =
                T * plaquetteHolonomy U p ^ ε * T⁻¹)) ∧
      (∀ (N : ℕ) (σ : Fin (N + 1) → StepWord L m j) (e : Fin N → AdjacentSwap L m j)
          (p : Fin N → Plaquette L m j),
        (∀ l : Fin N, (e l).original = σ l.castSucc ∧ (e l).swapped = σ l.succ) →
        (∀ l : Fin (N + 1), ∀ b ∈ pathOfWord z (σ l), b ∈ ℬ) →
        (∀ l : Fin N, ¬ (e l).IsCollinear →
          (e l).SpansPlaquette z (p l) ∧ ∀ b ∈ (p l).boundaryBonds, b ∈ ℬ) →
        ComplexMatrix2.rotationAngle
            (wordHolonomy U z (σ 0) * (wordHolonomy U z (σ (Fin.last N)))⁻¹) ≤
            ∑ l ∈ Finset.univ.filter (fun l : Fin N => ¬ (e l).IsCollinear),
              ComplexMatrix2.rotationAngle (plaquetteHolonomy U (p l)) ∧
          ComplexMatrix2.operatorNorm
              (wordHolonomy U z (σ 0) - wordHolonomy U z (σ (Fin.last N))) ≤
            ∑ l ∈ Finset.univ.filter (fun l : Fin N => ¬ (e l).IsCollinear),
              ComplexMatrix2.operatorNorm (plaquetteHolonomy U (p l) - 1))
end YangMills.Construction.PeriodicLattice
