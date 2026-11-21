import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation FamilyNorms
namespace TorusComparison
variable {F F' : BlockFrame}
inductive StepLaw : Type
  | ofFamily (φ : LocalFamily)
  | ofWeight (τ : ℝ)
def StepLaw.exponent (l : StepLaw) (s a ρA lam x : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    StepVariable (finiteCells F) → ℝ :=
  match l with
  | .ofFamily φ => familyLawExponent s a ρA x m φ V
  | .ofWeight τ => weightLawExponent s a ρA lam x m τ V
def StepLaw.IsAdmissible (l : StepLaw) (L t n₀ : ℕ) (σ δ E E₃ : ℝ) : Prop :=
  match l with
  | .ofFamily φ => IsNormBoundedLocalFamily L t n₀ σ δ E E₃ φ
  | .ofWeight τ => 0 ≤ τ ∧ τ ≤ 1
def StepLaw.amplitude (l : StepLaw) (E₃ : ℝ) : ℝ :=
  match l with
  | .ofFamily _ => 1 + E₃
  | .ofWeight _ => 1
def bondDistToCell (Y : F.Cell) (b : ↥(chordBonds (finiteCells F))) : ℝ :=
  cellSupDist (enclosingCell b.1.1) Y
def bondsNearCell (Y : F.Cell) (q : ℕ) : Finset ↥(chordBonds (finiteCells F)) :=
  Finset.univ.filter fun b => 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q
def freezeOutside (Λ : Finset ↥(chordBonds (finiteCells F))) (η : StepVariable (finiteCells F)) :
    StepVariable (finiteCells F) :=
  extendByZero id Λ η
def freezingHomotopy (lam x : ℝ) (Λ : Finset ↥(chordBonds (finiteCells F)))
    (Ψ : StepVariable (finiteCells F) → ℝ) (v : ℝ) (η : StepVariable (finiteCells F)) : ℝ :=
  v * Ψ η + (1 - v) * frozenExponent lam x id Λ Ψ η
structure IsBoxPairing (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) {ι : Type}
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) : Prop where
  injective_left : Function.Injective j
  injective_right : Function.Injective j'
  mem_left_iff : ∀ b, b ∈ bondsNearCell Y q ↔ ∃ i, j i = b
  mem_right_iff : ∀ b, b ∈ bondsNearCell Y' q ↔ ∃ i, j' i = b
  offset_eq : ∀ i, ∃ (h o : Fin 4 → ℤ) (k : Fin 4), o ∈ centredCube F.blockSide ∧
    (j i).1 = fineBondAt Y h o k ∧ (j' i).1 = fineBondAt Y' h o k
def toTorus {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (ζ : BondField ι) : StepVariable (finiteCells F) :=
  extendByZero j Finset.univ ζ
def pairingHomotopy {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) (Ψ : StepVariable (finiteCells F) → ℝ)
    (Ψ' : StepVariable (finiteCells F') → ℝ) (θ : ℝ) (ζ : BondField ι) : ℝ :=
  θ * Ψ (toTorus j ζ) + (1 - θ) * Ψ' (toTorus j' ζ)
end TorusComparison
end YangMills.Construction
end
