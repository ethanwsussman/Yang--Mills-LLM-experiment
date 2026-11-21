import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.InequalityOnMirroredCopies.ArrayMeanIsTheMeanOnTheTorus
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LawInAState.DominationOnTheLeastTorusProof
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace TiledMeanProof
variable {D : ChessboardSetup}
private theorem isBoundedObservable_of_mem_cellObservables {S : Set AmbientSpace}
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_of_mem_cellObservables <;> assumption
private theorem isBoundedObservable_finset_prod {a : ℝ} {ι : Type*} (s : Finset ι)
    (A : ι → InfiniteLattice.GaugeField a → ℂ)
    (h : ∀ i ∈ s, InfiniteLattice.IsBoundedObservable (A i)) :
    InfiniteLattice.IsBoundedObservable fun U => ∏ i ∈ s, A i U := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_finset_prod <;> assumption
private theorem cellSide_pos_aux (g : ReflectionGrid D) : 0 < g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.cellSide_pos <;> assumption
private theorem toNat_sub_eq {g : ReflectionGrid D} {j : ℕ}
    (hj : PeriodicLattice.torusSide D.L D.m = 2 * (D.L : ℝ) ^ j * g.cellSide) :
    (((D.m : ℕ) : ℤ) - g.q).toNat = j := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have h : (D.L : ℝ) ^ (((D.m : ℕ) : ℤ)) = (D.L : ℝ) ^ ((j : ℤ) + g.q) := by
    have h1 : (2 : ℝ) * (D.L : ℝ) ^ (D.m : ℕ) = 2 * (D.L : ℝ) ^ j * (D.L : ℝ) ^ g.q := hj
    rw [zpow_add₀ hL0, zpow_natCast, zpow_natCast]
    linarith
  have := zpow_right_injective₀ (by linarith) hL.ne' h
  omega
private theorem periodSubgroup_ext (P Q : PeriodSubgroup D) (h : P.mult = Q.mult) : P = Q := by
  obtain ⟨s, _⟩ := P
  obtain ⟨s', _⟩ := Q
  obtain rfl : s = s' := h
  rfl
abbrev _root_.YangMills.SharedProofs.p50270 := @periodSubgroup_ext
private theorem cell_injective_aux (g : ReflectionGrid D) : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
private theorem periodicExpectation_cellProduct_eq
    (hFrom : TorusReduction.Statement)
    (hArith : ReflectionGridArithmetic.Statement)
    (hSide : PeriodExpectation.Statement)
    (hCells : CellsBlocksAndSigns.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hG : MirrorGridsAllSides.ReflectionGridProperties)
    (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) {j : ℕ}
    (hj : PeriodicLattice.torusSide D.L D.m = 2 * (D.L : ℝ) ^ j * g.cellSide) :
    D.periodicExpectation (g.cellProduct (D.proj '' S) (D.liftedObservable F)) =
      tiledMean g (cubicCounts D j) S F := by
  classical
  have hs := cellSide_pos_aux g
  have hLj : (1 : ℝ) ≤ (D.L : ℝ) ^ j := one_le_pow₀ D.one_lt_factor.le
  have hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m := by
    rw [hj]
    nlinarith
  obtain ⟨⟨-, -, -, hn, hgrp, -⟩, hBox⟩ := ((hArith D).2.2.2 g).2 hside
  have hcas : g.cellsPerTorusSide = 2 * (D.L : ℤ) ^ j := by
    simp only [ReflectionGrid.cellsPerTorusSide, toNat_sub_eq hj]
  have hP : gridPeriods g (cubicCounts D j) = D.cubicPeriod := by
    rw [← hgrp]
    refine periodSubgroup_ext _ _ ?_
    funext μ
    show 2 * (D.L : ℤ) ^ j * g.cellRatio = g.cellsPerTorusSide * g.cellRatio
    rw [hcas]
  obtain ⟨Z, hZ0, hEx⟩ := hSide D _ hP
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  obtain ⟨-, -, -, -, -, hrules, -, -, -⟩ := hG D g hg
  obtain ⟨-, hcopy, hexp, -⟩ := hFrom D g hside
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, hprob, hnull, -⟩ := hW D.L D.m D.K D.β hL D.m.pos D.K.pos
  have hreal : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := ae_iff.2 hnull
  set w := cubicCounts D j with hwdef
  have hidx : g.blockIndices 0 = (w.indexBox : Set (Fin 4 → ℤ)) := by
    ext k
    simp only [ReflectionGrid.blockIndices, EvenIndexVector.indexBox, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico, Pi.zero_apply]
    have he : ∀ κ, w.coord κ = g.cellsPerTorusSide := fun κ => hcas.symm ▸ rfl
    constructor
    · intro h μ
      have := h μ
      rw [he]
      omega
    · intro h μ
      have := h μ
      rw [he] at this
      omega
  have hbij := ((((hCells D g).2 hside).2 (g.block 0) ⟨0, rfl⟩).1).2
  have hprod : ∀ e : Set D.Torus → ℂ, ∏ᶠ C' ∈ g.torusCellSet, e C' =
      ∏ k ∈ w.indexBox, e (D.proj '' g.cell k) := by
    intro e
    rw [← hbij.image_eq, finprod_mem_image hbij.injOn, (hBox 0).2.1, hidx,
      finprod_mem_image (cell_injective_aux g).injOn, finprod_mem_coe_finset]
  have hcell : ∀ k, g.cell k ∈ g.cellSet := fun k => ⟨k, rfl⟩
  have hcopymem : ∀ k, g.transportTo S (g.cell k) F ∈
      ReflectionGrid.cellObservables (D := D) (g.cell k) :=
    fun k => (hrules S hS _ (hcell k) _ (hcell k) F hF).1
  have hobs : InfiniteLattice.IsBoundedObservable fun U =>
      ∏ k ∈ w.indexBox, g.transportTo S (g.cell k) F U :=
    isBoundedObservable_finset_prod w.indexBox _ fun k _ =>
      isBoundedObservable_of_mem_cellObservables (hcopymem k)
  have harray : D.periodicExpectation (g.cellProduct (D.proj '' S) (D.liftedObservable F)) =
      D.periodicExpectation
        (D.liftedObservable fun U => ∏ k ∈ w.indexBox, g.transportTo S (g.cell k) F U) := by
    refine integral_congr_ae (hreal.mono fun U hU => ?_)
    show ∏ᶠ C' ∈ g.torusCellSet, g.torusTransportTo (D.proj '' S) C' (D.liftedObservable F) U =
      ∏ k ∈ w.indexBox, g.transportTo S (g.cell k) F (D.liftField U)
    rw [hprod fun C' => g.torusTransportTo (D.proj '' S) C' (D.liftedObservable F) U]
    exact Finset.prod_congr rfl fun k _ => (hcopy S hS _ (hcell k) F hF U hU).symm
  have hobs1 : InfiniteLattice.IsBoundedObservable (fun _ : D.GaugeField => (1 : ℂ)) :=
    ⟨measurable_const, 1, by simp⟩
  have hone : D.liftedExpectation (fun _ => 1) = 1 := by
    rw [hexp _ hobs1]
    show ∫ U, (1 : ℂ) ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β = 1
    have := hprob
    simp
  have hpart : (∫ U, (1 : ℂ) * Complex.exp (-(D.β : ℂ) *
      (((gridPeriods g w).wilsonAction U : ℝ) : ℂ))
      ∂(gridPeriods g w).haarMeasure) = (torusPartition g w : ℂ) := by
    unfold torusPartition
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    push_cast
    simp
  have hZ : (Z : ℂ) = (torusPartition g w : ℂ) := by
    have h := hEx (fun _ => 1) hobs1
    beta_reduce at h
    rw [hone, hpart, eq_div_iff hZc, one_mul] at h
    exact h
  rw [harray, ← hexp _ hobs, hEx _ hobs, tiledMean, hZ]
  rfl
private theorem cellCount_cubicCounts_cast {j : ℕ} :
    (cellCount (cubicCounts D j) : ℝ) = (2 * (D.L : ℝ) ^ j) ^ 4 := by apply _root_.YangMills.SharedProofs.p78545 <;> assumption
end TiledMeanProof
theorem tiledMeanIsPeriodicExpectation_of
    (hFrom : TorusReduction.Statement)
    (hArith : ReflectionGridArithmetic.Statement)
    (hSide : PeriodExpectation.Statement)
    (hCells : CellsBlocksAndSigns.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) :
    TiledMeanIsPeriodicExpectation := by
  intro D g hg S hS F hF m' j hj
  have h1 : (D.withExponent m').periodicExpectation ((g.withExponent m').cellProduct
      ((D.withExponent m').proj '' S) ((D.withExponent m').liftedObservable F)) =
      tiledMean g (cubicCounts D j) S F :=
    TiledMeanProof.periodicExpectation_cellProduct_eq (D := D.withExponent m') hFrom hArith
      hSide hCells hW hG (g.withExponent m') hg hS hF hj
  refine ⟨h1, ?_⟩
  have hs : g.cellSide ≠ 0 := (TiledMeanProof.cellSide_pos_aux g).ne'
  have hcount : (g.withExponent m').cellNumber = (cellCount (cubicCounts D j) : ℝ) := by
    rw [TiledMeanProof.cellCount_cubicCounts_cast]
    show (PeriodicLattice.torusSide D.L m' / g.cellSide) ^ 4 = _
    rw [hj, mul_div_cancel_right₀ _ hs]
  show ‖(D.withExponent m').periodicExpectation ((g.withExponent m').cellProduct
      ((D.withExponent m').proj '' S) ((D.withExponent m').liftedObservable F))‖ ^
    (1 / (g.withExponent m').cellNumber) = _
  rw [h1, hcount]
end YangMills.Construction.ReflectedCopies
end
