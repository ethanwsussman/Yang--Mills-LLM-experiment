import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureOfAGrid
import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPicture
import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.LengtheningATorusInOneDirection
import YangMills.Construction.ChessboardTori.ThreeConsequencesOfTheTraceFormula
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace TorusStretchBound
open InfiniteLattice (AmbientSpace)
variable (O : CoupledGrid)
def translates (S : Set AmbientSpace) (F : O.toChessboardSetup.GaugeField → ℂ) :
    (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ :=
  fun k => O.grid.transportTo S (O.grid.cell k) F
theorem transportTo_rules (hG : GridBasicProperties.Statement) {S S' S'' : Set AmbientSpace}
    (hS : S ∈ O.grid.cellSet) (hS' : S' ∈ O.grid.cellSet) (hS'' : S'' ∈ O.grid.cellSet)
    {F : O.toChessboardSetup.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.grid.transportTo S S' F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S' ∧
      O.grid.transportTo S' S'' (O.grid.transportTo S S' F) = O.grid.transportTo S S'' F := by
  obtain ⟨-, -, -, hC, hR, -, -⟩ := hG O.toChessboardSetup O.grid
  obtain ⟨r, hr, -⟩ := hC.2.2.2.2.2.2.1 S hS S' hS'
  obtain ⟨h1, -, h3, -⟩ := hR S hS S' hS' S'' hS'' r hr F hF F hF 0
  exact ⟨h1, h3⟩
theorem translates_isCellFamily (hG : GridBasicProperties.Statement) (n : EvenIndexVector)
    {S : Set AmbientSpace} (hS : S ∈ O.grid.cellSet) {F : O.toChessboardSetup.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.IsCellFamily n (translates O S F) :=
  fun k _ => (transportTo_rules O hG hS ⟨k, rfl⟩ ⟨k, rfl⟩ hF).1
theorem chessboardPartitionOn_eq_alternating
    (hFam : CellFamiliesInTransferSetup.Statement)
    (hAs : GridTransferAssertions.Statement)
    (hG : GridBasicProperties.Statement) (P : O.EvenTransverseSection) (m : SlabCount)
    (hm : Even (m : ℕ)) {S : Set AmbientSpace} (hS : S ∈ O.grid.cellSet)
    {F : O.toChessboardSetup.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S) :
    O.chessboardPartitionOn (P.cellCounts m hm) S F =
        P.transferSetup.alternatingSlabIntegral m hm
          (P.transferSetup.layerFunction m 0 (translates O S F)) ∧
      P.transferSetup.IsBoundedMeasurable
        (P.transferSetup.layerFunction m 0 (translates O S F)) := by
  obtain ⟨hLay, hRefl, -, -⟩ := (hFam O).1 P m hm _ (translates_isCellFamily O hG _ hS hF)
  have hzero : (0 : ℤ) ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ) := by
    rw [Finset.mem_Ico]
    omega
  have hΦ : P.transferSetup.IsBoundedMeasurable
      (P.transferSetup.layerFunction m 0 (translates O S F)) :=
    (hLay.1 0 hzero).2.2.1
  refine ⟨?_, hΦ⟩
  have hinvol : P.transferSetup.reflectConj
      (P.transferSetup.reflectConj (P.transferSetup.layerFunction m 0 (translates O S F))) =
      P.transferSetup.layerFunction m 0 (translates O S F) :=
    (((hAs O.toChessboardSetup P.transferSetup O.isCoarse m).2.2.2.2.1).2.2.2 _ _ hΦ hΦ).2.1
  have hlayer : ∀ i : ℕ, i < (m : ℕ) →
      P.transferSetup.layerFunction m (i : ℤ) (translates O S F) =
        if Even i then P.transferSetup.layerFunction m 0 (translates O S F)
        else P.transferSetup.reflectConj (P.transferSetup.layerFunction m 0 (translates O S F)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hr := hRefl (i : ℤ) (by positivity) (by omega)
        (fun k' _ => (transportTo_rules O hG hS ⟨k', rfl⟩ ⟨_, rfl⟩ hF).2.symm)
      have hcast : (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 := by push_cast; rfl
      rw [hcast, hr, ih (by omega)]
      by_cases hev : Even i
      · have hodd : ¬ Even (i + 1) := by simpa [Nat.even_add_one] using hev
        rw [if_pos hev, if_neg hodd]
      · have hodd : Even (i + 1) := by simpa [Nat.even_add_one] using hev
        rw [if_neg hev, if_pos hodd, hinvol]
  show O.cellFamilyIntegral (P.cellCounts m hm) (translates O S F) = _
  refine hLay.2.trans ?_
  unfold TransferSetup.alternatingSlabIntegral
  congr 1
  funext c
  exact hlayer c.val (ZMod.val_lt c)
theorem stretch_cellCounts (P : O.EvenTransverseSection) (m : SlabCount) (hm : Even (m : ℕ))
    {j : ℕ} (hj : 1 ≤ j) :
    (P.cellCounts m hm).stretch P.axis hj =
      P.cellCounts (SlabCount.scale j hj m) (SlabCount.even_scale j hj hm) := by
  have hcoord : ∀ e e' : EvenIndexVector, e.coord = e'.coord → e = e' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    cases h
    rfl
  refine hcoord _ _ (funext fun ν => ?_)
  change Function.update (P.transferSetup.cellCounts m) P.axis
      ((j : ℤ) * P.transferSetup.cellCounts m P.axis) ν =
    P.transferSetup.cellCounts (SlabCount.scale j hj m) ν
  by_cases h : ν = P.axis
  · subst h
    have hax : P.transferSetup.axis = P.axis := rfl
    simp [TransferSetup.cellCounts, SlabCount.scale, hax]
  · have hax : P.transferSetup.axis = P.axis := rfl
    simp [TransferSetup.cellCounts, hax, h]
theorem re_pow_eq_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (j : ℕ) : (z ^ j).re = z.re ^ j := by
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = x := ⟨z.re, Complex.ext (by simp) (by simp [hz])⟩
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]
end TorusStretchBound
open TorusStretchBound in
theorem TorusStretchBound.proof (hSub : PartitionFunctionSubmultiplicativity.Statement)
    (hFam : CellFamiliesInTransferSetup.Statement)
    (hAs : GridTransferAssertions.Statement)
    (hTr : TraceFormulaConsequences.Statement)
    (hG : GridBasicProperties.Statement) :
    TorusStretchBound.Statement := by
  intro O n μ j hj
  refine ⟨fun W hW => ((hSub O.toChessboardSetup O.grid W hW).2.1 n.coord n.two_le n.even).2 μ j hj, ?_⟩
  intro S hS F hF
  obtain ⟨P, m, hm, rfl, -, rfl⟩ := O.exists_cellCounts_eq n μ
  rw [stretch_cellCounts O P m hm hj]
  have hm' := SlabCount.even_scale j hj hm
  obtain ⟨e1, b1⟩ := chessboardPartitionOn_eq_alternating O hFam hAs hG P m hm hS hF
  obtain ⟨e2, -⟩ := chessboardPartitionOn_eq_alternating O hFam hAs hG P _ hm' hS hF
  have hsame : P.transferSetup.layerFunction (SlabCount.scale j hj m) 0 (translates O S F) =
      P.transferSetup.layerFunction m 0 (translates O S F) :=
    ((hFam O).1 P m hm _ (translates_isCellFamily O hG _ hS hF)).2.2.1 _ hm' _
      (translates_isCellFamily O hG _ hS hF) (fun _ _ => rfl)
  rw [e1, e2, hsame]
  obtain ⟨ht1, -, ht3⟩ := hTr O.toChessboardSetup P.transferSetup m hm
  have hnonneg := (ht1 _ b1).2.2.1
  obtain ⟨-, hj0, hj1, hj2, hj3⟩ := ht3 _ b1 j hj
  have hle := hj1.le.trans (hj2.trans hj3.le)
  have him : (P.transferSetup.alternatingSlabIntegral m hm
      (P.transferSetup.layerFunction m 0 (translates O S F))).im = 0 :=
    ((Complex.le_def.1 hnonneg).2).symm
  have him' := ((Complex.le_def.1 hj0).2).symm
  refine ⟨him, him', (Complex.le_def.1 hj0).1, ?_⟩
  have := (Complex.le_def.1 hle).1
  rwa [re_pow_eq_of_im_eq_zero him] at this
end YangMills.Construction.ChessboardTori
end
