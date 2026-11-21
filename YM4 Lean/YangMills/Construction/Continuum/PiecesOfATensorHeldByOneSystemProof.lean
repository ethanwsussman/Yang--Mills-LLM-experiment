import YangMills.Construction.Continuum.CompactSetsMeetFinitelyManyPieces
import YangMills.Construction.Continuum.ComplexExtensionIsUniqueAndBounded
import YangMills.Construction.Continuum.ConsistencyOfTheLocalFunctionals
import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuples
import YangMills.Construction.Continuum.LocalFunctionalsLinearBoundedAndValueOnTensors
import YangMills.Construction.Continuum.PiecesOfATensorHeldByOneSystem
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.PieceProducts.SeparatedBoxSum
open ConfigSpace ShellPieces
variable {n : ℕ}
theorem localPairing_zero (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) :
    localPairing T Q 0 = 0 := by
  simp [localPairing, PointSystem.fourierCoeff]
theorem box_subset_midBox (Q : PointSystem n) (i : Fin n) : Q.box i ⊆ Q.midBox i := by
  intro y hy
  have hs := Q.scale_pos
  have hy' : EuclideanCoords.supCoord (y - Q.base i) ≤ Q.scale / 2 := hy
  show EuclideanCoords.supCoord (y - Q.base i) ≤ 3 / 2 * Q.scale / 2
  linarith
theorem pieceSumOnSeparatedBoxes_of
    (hCpt : PieceFiniteness.CompactMeetsFinitelyMany)
    (hProd : PieceProducts.ProductBounds)
    (hPair : ConfigSpace.LocalPairingProps.LocalPairingProperties)
    (hCons : ConfigSpace.LocalPairingConsistent)
    (hCx : ConfigSpace.complexifyUniqueAndBounded)
    (hBasic : ConfigSpace.TupleFacts.BasicFacts) :
    PieceProducts.PieceSumOnSeparatedBoxes := by
  classical
  intro n c a G T hB Q φ hQ hsupp
  have hn : 2 ≤ n := hB.1
  obtain ⟨⟨V, hV⟩, hLin, -, -, -, hVal⟩ := hPair n c a G T Q hB hQ
  obtain ⟨hTest, hTensSupp⟩ := (hBasic n hn).2.1.2.1 φ.1 φ.2
  obtain ⟨hmem, -, hv⟩ := hVal φ.1 (fun i => φ.2.2 i)
    (fun i => (hsupp i).trans (box_subset_midBox Q i))
  have hT : localPairing T Q (tensorProd φ.1) = (T φ : ℂ) :=
    hv.trans ((hCx n hn T hB.2.2.2.1).1.2.2.1 φ)
  have hΨ : tsupport (tensorProd φ.1) ⊆ cylinderSet Q.box :=
    hTensSupp.trans fun x hx i => hsupp i (hx i)
  generalize tensorProd φ.1 = Ψ at hTest hT hΨ ⊢
  have hEach : ∀ p : activeIndices n,
      ContDiff ℝ ∞ (PieceProducts.pieceMul p.1.1 p.1.2 Ψ) ∧
        tsupport (PieceProducts.pieceMul p.1.1 p.1.2 Ψ) ⊆
          cylinderSet Q.box ∩ cylinderSet (pieceBoxSystem p).box ∧
        (pieceBoxSystem p).IsSeparated := by
    rintro ⟨⟨j, z⟩, hp⟩
    obtain ⟨⟨hsep, -, -, -, -, hmul⟩, -⟩ := hProd n hn j z hp
    obtain ⟨hsmooth, hsub, -⟩ := hmul Ψ hTest.1
    exact ⟨hsmooth, fun x hx => ⟨hΨ (hsub hx).1, (hsub hx).2⟩, hsep⟩
  have hIn : ∀ p : activeIndices n, PieceFiniteness.pieceMul p.1 Ψ ∈ Q.supportedClass := fun p =>
    ⟨(hEach p).1, fun x hx i => box_subset_midBox Q i (((hEach p).2.1 hx).1 i)⟩
  obtain ⟨hfin, hEq⟩ := (hCpt n hn).2 Ψ hTest
  have hF : ∀ p ∈ hfin.toFinset, p ∈ activeIndices n := fun p hp =>
    (hfin.mem_toFinset.1 hp).1
  have hAdd : ∀ s : Finset (ℕ × LatticePt n), (∀ p ∈ s, p ∈ activeIndices n) →
      (∑ p ∈ s, PieceFiniteness.pieceMul p Ψ) ∈ Q.supportedClass ∧
        localPairing T Q (∑ p ∈ s, PieceFiniteness.pieceMul p Ψ) =
          ∑ p ∈ s, localPairing T Q (PieceFiniteness.pieceMul p Ψ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨?_, by simpa using localPairing_zero T Q⟩
      rw [Finset.sum_empty, ← hV]
      exact V.zero_mem
    | insert p s hp ih =>
      intro hs
      obtain ⟨ih₁, ih₂⟩ := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hpc := hIn ⟨p, hs p (Finset.mem_insert_self p s)⟩
      rw [Finset.sum_insert hp, Finset.sum_insert hp]
      refine ⟨?_, ?_⟩
      · rw [← hV] at hpc ih₁ ⊢
        exact V.add_mem hpc ih₁
      · rw [hLin.1 _ hpc _ ih₁, ih₂]
  calc
    ∑' p : activeIndices n, localPairing T (pieceBoxSystem p) (PieceProducts.pieceMul p.1.1 p.1.2 Ψ)
        = ∑' p : activeIndices n, localPairing T Q (PieceFiniteness.pieceMul p.1 Ψ) :=
      tsum_congr fun p => (hCons n c a G T hB Q (pieceBoxSystem p) hQ (hEach p).2.2
        _ (hEach p).1 (hEach p).2.1).symm
    _ = ∑ p ∈ hfin.toFinset.subtype (· ∈ activeIndices n),
          localPairing T Q (PieceFiniteness.pieceMul p.1 Ψ) := by
      refine tsum_eq_sum fun p hp => ?_
      have hz : PieceFiniteness.pieceMul p.1 Ψ = 0 := by
        by_contra hne
        exact hp (Finset.mem_subtype.2 (hfin.mem_toFinset.2 ⟨p.2, hne⟩))
      rw [hz, localPairing_zero]
    _ = ∑ p ∈ hfin.toFinset, localPairing T Q (PieceFiniteness.pieceMul p Ψ) :=
      Finset.sum_subtype_of_mem (fun p => localPairing T Q (PieceFiniteness.pieceMul p Ψ)) hF
    _ = localPairing T Q (∑ p ∈ hfin.toFinset, PieceFiniteness.pieceMul p Ψ) := (hAdd _ hF).2.symm
    _ = localPairing T Q Ψ := congrArg (localPairing T Q) hEq.symm
    _ = (T φ : ℂ) := hT
end YangMills.Construction.PieceProducts.SeparatedBoxSum
