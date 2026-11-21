import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.ChessboardValueAtAGrid
import YangMills.Construction.ChessboardTori.GibbsStateAgainstTheTorusOnABox
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboard
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace JensenChessboardBound
open InfiniteLattice (AmbientSpace)
variable {a : ℝ}
theorem isRegionMeasurable_mono {S S' : Set AmbientSpace} (hSS : S ⊆ S')
    {A : InfiniteLattice.GaugeField a → ℂ} (hA : InfiniteLattice.IsRegionMeasurable S A) :
    InfiniteLattice.IsRegionMeasurable S' A := by
  refine Measurable.mono hA ?_ le_rfl
  exact biSup_mono fun b hb => ⟨hSS hb.1, hSS hb.2⟩
theorem isBoundedObservable_sum {ι : Type*} (F : Finset ι)
    (f : ι → InfiniteLattice.GaugeField a → ℂ)
    (hf : ∀ i ∈ F, InfiniteLattice.IsBoundedObservable (f i)) :
    InfiniteLattice.IsBoundedObservable fun U => ∑ i ∈ F, f i U := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simp⟩
  | insert i F hi ih =>
    obtain ⟨hm, C, hC⟩ := hf i (Finset.mem_insert_self i F)
    obtain ⟨hm', C', hC'⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨?_, C + C', fun U => ?_⟩
    · simp only [Finset.sum_insert hi]
      exact hm.add hm'
    · show ‖∑ i ∈ insert i F, f i U‖ ≤ C + C'
      rw [Finset.sum_insert hi]
      exact (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))
theorem isRegionMeasurable_sum {ι : Type*} {S : Set AmbientSpace} (F : Finset ι)
    (f : ι → InfiniteLattice.GaugeField a → ℂ)
    (hf : ∀ i ∈ F, InfiniteLattice.IsRegionMeasurable S (f i)) :
    InfiniteLattice.IsRegionMeasurable S fun U => ∑ i ∈ F, f i U := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact measurable_const
  | insert i F hi ih =>
    simp only [Finset.sum_insert hi]
    exact Measurable.add (hf i (Finset.mem_insert_self i F))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
theorem integrable_of_isBoundedObservable {ν : Measure (InfiniteLattice.GaugeField a)}
    [IsFiniteMeasure ν] {A : InfiniteLattice.GaugeField a → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) : Integrable A ν := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem bound_at_fixed_exponent
    (hbox : GibbsBoundByTorusOnBlock.Statement)
    (hdep : MeasurableObservablesAndLifts.Statement)
    (hgrp : ReflectionGroupAndTransport.Statement)
    (hpar : CellsBlocksAndSigns.Statement)
    (hval : GridChessboardNorm.Statement)
    (D : ChessboardSetup) (g : ReflectionGrid D) (hg : g.IsCoarse)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (ν : Measure D.GaugeField) (hν : InfiniteLattice.IsGibbs D.β ν)
    (hinv : ∀ r : g.reflectionGroup, InfiniteLattice.IsSymmetricUnder ν (g.toLatticeSym r))
    (H : D.GaugeField → ℝ)
    (hH : ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) g.baseCell) :
    Real.exp (-InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) ≤
        g.chessboardNorm g.baseCell (ReflectionGrid.expOfReal H) ∧
      g.chessboardNorm g.baseCell (ReflectionGrid.expOfReal H) ≤
        Real.exp (InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) ∧
      ∫ U, H U ∂ν ≤
        Real.log (g.chessboardNorm g.baseCell (ReflectionGrid.expOfReal H)) +
          (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
            (D.mesh ^ 3 * PeriodicLattice.torusSide D.L D.m) := by
  classical
  have : IsProbabilityMeasure ν := hν.1
  have hS : g.baseCell ∈ g.cellSet := ⟨0, rfl⟩
  have hB : g.fundamentalBlock ∈ g.blocks := g.fundamentalBlock_mem_blocks
  obtain ⟨-, hcopy, hvalue, hlow, hup⟩ := (hval D g hg hside _ hB).2.2.2 _ hS H hH
  obtain ⟨-, hone, -, hcop, -⟩ := hgrp D g hg
  obtain ⟨-, -, hcell, -⟩ := hdep D
  have hcount : ((g.cellsWithin g.fundamentalBlock).ncard : ℝ) = g.cellsAcross ^ 4 :=
    ((((hpar D g).2 hside).2 _ hB).2 _ hS).2.1
  have hsidepos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
  have hl : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  have hn : 0 < g.cellsAcross := div_pos hl hsidepos
  have hn4 : 0 < g.cellsAcross ^ 4 := pow_pos hn 4
  have hncard : 0 < (g.cellsWithin g.fundamentalBlock).ncard := by
    have h0 : (0 : ℝ) < ((g.cellsWithin g.fundamentalBlock).ncard : ℝ) := hcount ▸ hn4
    exact_mod_cast h0
  have hT : (g.cellsWithin g.fundamentalBlock).Finite := Set.finite_of_ncard_pos hncard
  have hHobs : InfiniteLattice.IsBoundedObservable (ReflectionGrid.ofRealFn H) := by
    have h0 := hH
    rw [hcell g hg _ hS] at h0
    exact h0.1
  have hfacts : ∀ S' ∈ g.cellsWithin g.fundamentalBlock,
      InfiniteLattice.IsBoundedObservable (g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H)) ∧
      InfiniteLattice.IsRegionMeasurable g.fundamentalBlockInterior
        (g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H)) ∧
      (∀ U, (g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U).im = 0) ∧
      ∫ U, g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U ∂ν =
        ∫ U, ReflectionGrid.ofRealFn H U ∂ν := by
    intro S' hS'
    have hS'c : S' ∈ g.cellSet := hS'.1
    have hmem := (hcop.1 _ hS _ hS'c _ hS'c _ hH _ hH).1
    rw [hcell g hg _ hS'c] at hmem
    obtain ⟨r, hr, -⟩ := hone _ hS _ hS'c
    have hc : g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) =
        ReflectionGrid.ofRealFn ((g.toLatticeSym r).actOn H) := by
      have h0 := (hcopy r).1
      rw [hr] at h0
      exact h0
    refine ⟨hmem.1, isRegionMeasurable_mono (interior_mono hS'.2) hmem.2, fun U => ?_, ?_⟩
    · rw [hc]
      simp [ReflectionGrid.ofRealFn]
    · rw [hc]
      exact hinv r _ hHobs
  have hsum : ∀ U, (∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
      g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U) =
      ∑ S' ∈ hT.toFinset, g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U :=
    fun U => finsum_mem_eq_finite_toFinset_sum _ hT
  have hsum' : (fun U => ∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
      g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U) =
      fun U => ∑ S' ∈ hT.toFinset, g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U :=
    funext hsum
  have hobs : InfiniteLattice.IsBoundedObservable fun U => ∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
      g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U := by
    rw [hsum']
    exact isBoundedObservable_sum _ _ fun S' h => (hfacts S' (hT.mem_toFinset.1 h)).1
  have hmeas : InfiniteLattice.IsRegionMeasurable g.fundamentalBlockInterior fun U =>
      ∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
        g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U := by
    rw [hsum']
    exact isRegionMeasurable_sum _ _ fun S' h => (hfacts S' (hT.mem_toFinset.1 h)).2.1
  have him : ∀ U, (∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
      g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U).im = 0 := by
    intro U
    rw [hsum, Complex.im_sum]
    exact Finset.sum_eq_zero fun S' h => (hfacts S' (hT.mem_toFinset.1 h)).2.2.1 U
  have hint : (∫ U, ∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
      g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U ∂ν).re =
      g.cellsAcross ^ 4 * ∫ U, H U ∂ν := by
    have h0 : (∫ U, ∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
        g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U ∂ν) =
        ∫ U, ∑ S' ∈ hT.toFinset, g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U ∂ν :=
      congrArg (fun f => ∫ U, f U ∂ν) hsum'
    have hreal : ∫ U, ReflectionGrid.ofRealFn H U ∂ν = ((∫ U, H U ∂ν : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [h0, integral_finsetSum _ fun S' h =>
      integrable_of_isBoundedObservable (hfacts S' (hT.mem_toFinset.1 h)).1,
      Finset.sum_congr rfl fun S' h => (hfacts S' (hT.mem_toFinset.1 h)).2.2.2,
      Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hT, hreal,
      ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re, hcount]
  have hexpect : (D.periodicExpectation (D.liftedObservable fun U => Complex.exp
      (∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
        g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U))).re =
      g.chessboardNorm g.baseCell (ReflectionGrid.expOfReal H) ^ (g.cellsAcross ^ 4) := by
    have h2 : g.liftedExpSumExpectation g.baseCell g.fundamentalBlock H =
        D.periodicExpectation (D.liftedObservable fun U => Complex.exp
          (∑ᶠ S' ∈ g.cellsWithin g.fundamentalBlock,
            g.transportTo g.baseCell S' (ReflectionGrid.ofRealFn H) U)) := rfl
    rw [← h2, ← hvalue, Complex.ofReal_re]
  have hvpos : 0 < g.chessboardNorm g.baseCell (ReflectionGrid.expOfReal H) :=
    lt_of_lt_of_le (Real.exp_pos _) hlow
  have main := hbox D g hg hside ν hν _ hobs him hmeas
  rw [hint, hexpect, Real.log_rpow hvpos] at main
  refine ⟨hlow, hup, ?_⟩
  have ha : 0 < D.mesh := D.mesh_pos
  have hid : (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
      (D.mesh ^ 3 * PeriodicLattice.torusSide D.L D.m) =
      (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
        (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 / g.cellsAcross ^ 4 := by
    unfold ReflectionGrid.cellsAcross
    field_simp
  rw [hid, ← sub_le_iff_le_add', le_div_iff₀ hn4]
  linarith
end JensenChessboardBound
open JensenChessboardBound in
theorem JensenChessboardBound.proof
    (hbox : GibbsBoundByTorusOnBlock.Statement)
    (hdep : MeasurableObservablesAndLifts.Statement)
    (hgrp : ReflectionGroupAndTransport.Statement)
    (hpar : CellsBlocksAndSigns.Statement)
    (hval : GridChessboardNorm.Statement) :
    JensenChessboardBound.Statement := by
  intro D g hg ν hν hinv H hH
  have key : ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
      Real.exp (-InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn (D := D) H)) ≤
          g.normAtExponent m' g.baseCell (fun U => Complex.exp (H U)) ∧
        g.normAtExponent m' g.baseCell (fun U => Complex.exp (H U)) ≤
          Real.exp (InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn (D := D) H)) ∧
        ∫ U, H U ∂ν ≤ Real.log (g.normAtExponent m' g.baseCell fun U => Complex.exp (H U)) +
          (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
            (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m') :=
    fun m' hm => bound_at_fixed_exponent hbox hdep hgrp hpar hval (D.withExponent m')
      (g.withExponent m') hg hm ν hν (fun r => hinv r) H hH
  refine ⟨fun m' hm => (key m' hm).2.2, ?_⟩
  have htop : Tendsto (fun m' : ℕ+ => PeriodicLattice.torusSide D.L m') atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (D.L : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt D.one_lt_factor
    exact (h1.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_PNat_val_atTop_atTop
  have hev := htop.eventually_ge_atTop (2 * g.cellSide)
  have hε : Tendsto (fun m' : ℕ+ => (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
      g.cellSide ^ 4 / (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m')) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (htop.const_mul_atTop (pow_pos D.mesh_pos 3))
  have hlim : Tendsto (fun m' : ℕ+ => Real.exp (∫ U, H U ∂ν -
      (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
        (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m'))) atTop
      (𝓝 (Real.exp (∫ U, H U ∂ν))) := by
    have h0 := (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds (x := ∫ U, H U ∂ν)).sub hε)
    simpa [Function.comp_def] using h0
  have hle : (fun m' : ℕ+ => Real.exp (∫ U, H U ∂ν -
      (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
        (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m'))) ≤ᶠ[atTop]
      fun m' => g.normAtExponent m' (g.cell 0) fun U => Complex.exp (H U) := by
    filter_upwards [hev] with m' hm
    obtain ⟨h1, -, h3⟩ := key m' hm
    have hx : 0 < g.normAtExponent m' g.baseCell fun U => Complex.exp (H U) :=
      lt_of_lt_of_le (Real.exp_pos _) h1
    calc _ ≤ Real.exp (Real.log (g.normAtExponent m' g.baseCell fun U => Complex.exp (H U))) :=
          Real.exp_le_exp.2 (by linarith)
      _ = _ := Real.exp_log hx
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun m' => g.normAtExponent m' (g.cell 0) fun U => Complex.exp (H U)) :=
    isBoundedUnder_of_eventually_le
      (a := Real.exp (InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn (D := D) H)))
      (hev.mono fun m' hm => (key m' hm).2.1)
  have hmain : Real.exp (∫ U, H U ∂ν) ≤ g.limChessboardNorm fun U => Complex.exp (H U) := by
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup hle hlim.isBoundedUnder_ge.isCoboundedUnder_le hbdd
  calc ∫ U, H U ∂ν = Real.log (Real.exp (∫ U, H U ∂ν)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hmain
end YangMills.Construction.ChessboardTori
end
