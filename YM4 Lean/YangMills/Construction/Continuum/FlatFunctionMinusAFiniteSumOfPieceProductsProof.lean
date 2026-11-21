import YangMills.Construction.ConfigSpace.IteratedPartialRules
import YangMills.Construction.Continuum.CompactSetsMeetFinitelyManyPieces
import YangMills.Construction.Continuum.FlatFunctionMinusAFiniteSumOfPieceProducts
import YangMills.Construction.Continuum.LeastSupDistanceOfPointsOfPowersOfFourSpace
import YangMills.Construction.Continuum.PiecesOfTheShellsAndTheirBounds
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace.FlatMinusPieceSum
open PieceProducts ShellPieces
theorem flatMinusPieceSumBound_of
    (hProd : PieceProducts.ProductBounds)
    (hRules : ConfigSpace.IteratedPartialRules)
    (hSep : MinSeparation.mainClaim)
    (hShell : ShellPieceBounds.ShellPiecesBound)
    (hCpt : PieceFiniteness.CompactMeetsFinitelyMany) :
    ConfigSpace.FlatMinusPieceSumBound := by
  classical
  intro n hn f hf k l F
  obtain ⟨-, -, hAdd, -, hLoc, -⟩ := hRules n
  obtain ⟨-, hBasic, hPart, -⟩ := hShell n (by omega)
  obtain ⟨-, -, hDiag, hOpenSet⟩ := hSep.1 n hn
  have hMeets := (hCpt n hn).1
  have hCD : ∀ p : activeIndices n, ContDiff ℝ ∞ (PieceProducts.pieceMul p.1.1 p.1.2 f) := fun p =>
    ((hProd n hn p.1.1 p.1.2 p.2).1.2.2.2.2.2 f hf.1.1).1
  have hVanish : ∀ (p : activeIndices n) (x : Config n), x ∈ diagonalSet n →
      PieceProducts.pieceMul p.1.1 p.1.2 f =ᶠ[𝓝 x] 0 := by
    intro p x hx
    have hout : x ∉ tsupport (piece p.1.1 p.1.2) := by
      intro hmem
      have hd := (hBasic p.1.1 p.1.2).2.2.2.2.2.2.1 hmem
      rw [← hDiag] at hd
      exact hd hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hout] with y hy
    have hy' : piece p.1.1 p.1.2 y = 0 := hy
    simp [PieceProducts.pieceMul, hy']
  have hEach : ∀ (p : activeIndices n) (α : MultiIndex n), α.order ≤ l → ∀ x : Config n,
      ENNReal.ofReal ((1 + euclidNorm x) ^ k *
          ‖iteratedPartial α (PieceProducts.pieceMul p.1.1 p.1.2 f) x‖) ≤
        decaySeminorm k l (PieceProducts.pieceMul p.1.1 p.1.2 f) := by
    intro p α hα x
    exact le_iSup₂_of_le (f := fun (β : MultiIndex n) (_ : β.order ≤ l) =>
      ⨆ y, ENNReal.ofReal ((1 + euclidNorm y) ^ k *
        ‖iteratedPartial β (PieceProducts.pieceMul p.1.1 p.1.2 f) y‖)) α hα
      (le_iSup (fun y => ENNReal.ofReal ((1 + euclidNorm y) ^ k *
        ‖iteratedPartial α (PieceProducts.pieceMul p.1.1 p.1.2 f) y‖)) x)
  rw [decaySeminorm]
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  by_cases hx : x ∈ diagonalSet n
  · have hev : (f - ∑ p ∈ F, PieceProducts.pieceMul p.1.1 p.1.2 f) =ᶠ[𝓝 x] f := by
      filter_upwards [(Filter.eventually_all_finset F).2 fun p _ => hVanish p x hx] with y hy
      have hz : (∑ p ∈ F, PieceProducts.pieceMul p.1.1 p.1.2 f) y = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun p hp => hy p hp
      simp [hz]
    rw [hLoc α _ _ x hev, hf.2 α x hx]
    simp
  · have hxi : x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
      rw [← hDiag]
      exact hx
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hOpenSet.mem_nhds hxi)
    have hfin : {p : activeIndices n |
        ∃ y ∈ Metric.closedBall x r, piece p.1.1 p.1.2 y ≠ 0}.Finite := by
      refine ((hMeets _ hsub (isCompact_closedBall x r)).preimage
        Subtype.val_injective.injOn).subset ?_
      rintro p ⟨y, hy, hne⟩
      exact ⟨p.2, y, hy, hne⟩
    obtain ⟨S, hS⟩ : ∃ S : Finset (activeIndices n), S = hfin.toFinset ∪ F := ⟨_, rfl⟩
    have hFS : F ⊆ S := hS ▸ Finset.subset_union_right
    have hfS : ∀ y ∈ Metric.closedBall x r,
        ∑ p ∈ S, PieceProducts.pieceMul p.1.1 p.1.2 f y = f y := by
      intro y hy
      have hone : ∑ p ∈ S, piece p.1.1 p.1.2 y = 1 := by
        rw [← (hPart y (hsub hy)).2]
        refine (tsum_eq_sum fun p hp => ?_).symm
        by_contra hne
        exact hp (hS ▸ Finset.mem_union_left _ (hfin.mem_toFinset.2 ⟨y, hy, hne⟩))
      have hC : ∑ p ∈ S, (piece p.1.1 p.1.2 y : ℂ) = 1 := by
        rw [← Complex.ofReal_sum, hone, Complex.ofReal_one]
      simp only [PieceProducts.pieceMul]
      rw [← Finset.sum_mul, hC, one_mul]
    have hev : (f - ∑ p ∈ F, PieceProducts.pieceMul p.1.1 p.1.2 f) =ᶠ[𝓝 x]
        ∑ p ∈ S \ F, PieceProducts.pieceMul p.1.1 p.1.2 f := by
      filter_upwards [Metric.closedBall_mem_nhds x hr] with y hy
      have hsplit := Finset.sum_sdiff (f := fun p : activeIndices n =>
        PieceProducts.pieceMul p.1.1 p.1.2 f y) hFS
      have hy' := hfS y hy
      simp only [Pi.sub_apply, Finset.sum_apply]
      linear_combination -hsplit - hy'
    rw [hLoc α _ _ x hev, hAdd _ (S \ F) (fun p => PieceProducts.pieceMul p.1.1 p.1.2 f) α
      (fun p _ => hCD p), Finset.sum_apply]
    have hw : (0 : ℝ) ≤ (1 + euclidNorm x) ^ k :=
      pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) k
    calc ENNReal.ofReal ((1 + euclidNorm x) ^ k *
            ‖∑ p ∈ S \ F, iteratedPartial α (PieceProducts.pieceMul p.1.1 p.1.2 f) x‖)
        ≤ ENNReal.ofReal (∑ p ∈ S \ F, (1 + euclidNorm x) ^ k *
            ‖iteratedPartial α (PieceProducts.pieceMul p.1.1 p.1.2 f) x‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
      _ = ∑ p ∈ S \ F, ENNReal.ofReal ((1 + euclidNorm x) ^ k *
            ‖iteratedPartial α (PieceProducts.pieceMul p.1.1 p.1.2 f) x‖) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg hw (norm_nonneg _)
      _ ≤ ∑ p ∈ S \ F, decaySeminorm k l (PieceProducts.pieceMul p.1.1 p.1.2 f) :=
          Finset.sum_le_sum fun p _ => hEach p α hα x
      _ = ∑ p ∈ (S \ F).subtype (fun p => p ∉ F),
            decaySeminorm k l (PieceProducts.pieceMul p.1.1.1 p.1.1.2 f) :=
          (Finset.sum_subtype_of_mem (fun p : activeIndices n =>
            decaySeminorm k l (PieceProducts.pieceMul p.1.1 p.1.2 f))
            fun p hp => (Finset.mem_sdiff.1 hp).2).symm
      _ ≤ ∑' p : {p : activeIndices n // p ∉ F},
            decaySeminorm k l (PieceProducts.pieceMul p.1.1.1 p.1.1.2 f) :=
          ENNReal.sum_le_tsum _
end YangMills.Construction.ConfigSpace.FlatMinusPieceSum
end
