import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridInTheOtherParts
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.MultipleReflections
namespace Setup.Grid
variable {D : Setup} (G : D.Grid)
def boxTileFinset : Finset (Fin 4 → ℤ) := (InfiniteLattice.ReflectionGrid.torusTileIndices_finite G D.m).toFinset
def CopyRules : Prop :=
  ∀ (i j l : Fin 4 → ℤ) (A B : D.GaugeField → ℂ) (z : ℂ),
    A ∈ G.tileAlgebra i → B ∈ G.tileAlgebra i →
      G.reflectedCopy j l (G.reflectedCopy i j A) = G.reflectedCopy i l A ∧
      G.reflectedCopy i j (A * B) = G.reflectedCopy i j A * G.reflectedCopy i j B ∧
      G.reflectedCopy i j (A + B) = G.reflectedCopy i j A + G.reflectedCopy i j B ∧
      (tileSign i j = 1 → G.reflectedCopy i j (fun U => z * A U) = fun U => z * G.reflectedCopy i j A U) ∧
      (tileSign i j = -1 →
        G.reflectedCopy i j (fun U => z * A U) = fun U => conj z * G.reflectedCopy i j A U)
def SignsBalanced : Prop :=
  ∀ (i : Fin 4 → ℤ) (s : ℤˣ),
    (({j | j ∈ G.boxTileIndices ∧ tileSign i j = s} : Set (Fin 4 → ℤ)).ncard : ℝ) =
      G.tilesPerSide ^ 4 / 2
def CopiesCommuteWithPeriods : Prop :=
  ∀ (i j : Fin 4 → ℤ) (A : D.GaugeField → ℂ), A ∈ G.tileAlgebra i →
    ∀ v : InfiniteLattice.LatticePoint D.mesh,
      (∃ n : Fin 4 → ℤ, (v : InfiniteLattice.AmbientSpace) = D.side • fun μ => (n μ : ℝ)) →
      ∃ l : Fin 4 → ℤ,
        G.tile l = (fun x : InfiniteLattice.AmbientSpace => x + (v : InfiniteLattice.AmbientSpace)) '' G.tile j ∧
        G.reflectedCopy i l A = (InfiniteLattice.shift v).actOn (G.reflectedCopy i j A) ∧
        D.pullbackObs (G.reflectedCopy i l A) = D.pullbackObs (G.reflectedCopy i j A)
def ChessboardBoundOnBox : Prop :=
  ∀ A : (Fin 4 → ℤ) → D.GaugeField → ℂ, (∀ i ∈ G.boxTileIndices, A i ∈ G.tileAlgebra i) →
    ‖D.torusExpectation fun U => ∏ i ∈ G.boxTileFinset, A i U‖ ≤
      ∏ i ∈ G.boxTileFinset, G.chessboardNorm i (A i)
def ChessboardBoundOnTransversal : Prop :=
  ∀ C : Set (Fin 4 → ℤ), (∀ i, ∃! j, j ∈ C ∧ G.AreCongruent (G.tile i) (G.tile j)) →
    ∀ A : (Fin 4 → ℤ) → D.GaugeField → ℂ, (∀ i ∈ C, A i ∈ G.tileAlgebra i) →
      ‖D.torusExpectation fun U => ∏ᶠ i ∈ C, A i U‖ ≤ ∏ᶠ i ∈ C, G.chessboardNorm i (A i)
def ChessboardNormRules : Prop :=
  ∀ (i j : Fin 4 → ℤ) (A : D.GaugeField → ℂ) (z : ℂ), A ∈ G.tileAlgebra i →
    G.chessboardNorm j (G.reflectedCopy i j A) = G.chessboardNorm i A ∧
    G.chessboardNorm i (fun _ => 1) = 1 ∧
    G.chessboardNorm i A ≤ InfiniteLattice.observableSupNorm A ∧
    G.chessboardNorm i (fun U => z * A U) = ‖z‖ * G.chessboardNorm i A
def CoarseTileProductBound : Prop :=
  ∀ (k₀ : ℕ) (H : D.Grid), H.edge = (D.L : ℝ) ^ k₀ * G.edge → 2 * H.edge ≤ D.side →
    (∀ (α : Fin 4) (n : ℤ), G.IsWall (H.wall α n)) →
    ∀ (q : Fin 4 → ℤ) (O : Set (Fin 4 → ℤ)), (∀ i ∈ O, G.tile i ⊆ H.tile q) →
    ∀ (o : Fin 4 → ℤ) (E : D.GaugeField → ℂ), E ∈ G.tileAlgebra o →
      (fun U => ∏ᶠ i ∈ O, G.reflectedCopy o i E U) ∈ H.tileAlgebra q ∧
      H.chessboardNorm q (fun U => ∏ᶠ i ∈ O, G.reflectedCopy o i E U) ≤
        G.chessboardNorm o E ^ O.ncard
end Setup.Grid
def ChessboardBoundAndRules : Prop :=
  ∀ (D : Setup) (G : D.Grid), 2 * G.edge ≤ D.side →
    G.CopyRules ∧ G.SignsBalanced ∧
    G.CopiesCommuteWithPeriods ∧ G.LiftsCommuteWithCopies ∧
    G.ChessboardBoundOnBox ∧ G.ChessboardBoundOnTransversal ∧
    G.ChessboardNormRules ∧ G.CoarseTileProductBound
end YangMills.Construction.MultipleReflections
end
