import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def axialGaugePotential (y : F.Site F.depth) (Fm : Fin 4 → Fin 4 → ℝ) : LevelForm F F.depth :=
  fun x i => ∑ l : Fin 4, if i < l then (siteOffset y x l : ℝ) * Fm l i else 0
def bondPairing (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ)
    (A A' : LevelForm F F.depth) : ℝ :=
  ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, q b b' * A b.1 b.2 * A' b'.1 b'.2
def BilinearResponseBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ del : ℝ, 0 < del ∧ ∃ L₀ : ℕ, ∀ (F : BlockFrame) (δ E : ℝ) (Y : F.Cell)
    (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F) (W : Fin 2 → LevelForm F F.depth)
    (q : F.Site F.depth → F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ),
    Odd F.blockSide → L₀ ≤ F.blockSide →
    IsLargeCubicTorus F → 0 < δ → δ ≤ del / 64 → 0 ≤ E → (∀ i, IsFlatChain a (c i) (B i)) →
    (∀ i, IsAxialResponse (c i) (B i) (W i)) →
    (∀ y (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing (q y) (addGradient (fun _ _ => 0) φ) A = 0 ∧
      bondPairing (q y) A (addGradient (fun _ _ => 0) φ) = 0) →
    (∀ y b b', |q y b b'| ≤ E / torusDecayFactor F.blockSide δ (bondSpan y ![b, b'])) →
    (∀ y (Fm Fm' : Fin 4 → Fin 4 → ℝ), (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
      |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
          q y b b' * axialGaugePotential y Fm b.1 b.2 * axialGaugePotential y Fm' b'.1 b'.2| ≤
        (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|) →
    |∑ y ∈ blockFineSites Y, bondPairing (q y) (W 0) (W 1)| ≤
      (F.blockSide : ℝ) ^ (-(1 / 4 : ℝ)) * E / torusDecayFactor F.blockSide δ (bondSpan Y c)
end YangMills.Construction.ColdStepAtMirrorFrames
end
