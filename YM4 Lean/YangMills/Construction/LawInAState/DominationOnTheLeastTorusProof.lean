import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPicture
import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity
import YangMills.Construction.ChessboardTori.DominationInOneCell
import YangMills.Construction.InequalityOnMirroredCopies.ChessboardValueFallsToTheLeastTorus
import YangMills.Construction.InequalityOnMirroredCopies.TheRatioIsBounded
import YangMills.Construction.LawInAState.DominationOnTheLeastTorus
import YangMills.Construction.LawInAState.MeanOnATorusByThePeriodGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.LawInAState.LeastTorusDomination
open ChessboardTori ReflectedCopies
open InfiniteLattice (AmbientSpace)
variable {D : ChessboardSetup}
private theorem cellSide_eq_one_of_q_eq_zero (g : ReflectionGrid D) (hq : g.q = 0) : g.cellSide = 1 := by
  simp [ReflectionGrid.cellSide, hq]
private theorem hasAdmissibleSide_of_q_eq_zero (g : ReflectionGrid D) (hq : g.q = 0) (hK : 2 ≤ (D.K : ℕ)) :
    g.HasAdmissibleSide := by
  have hL := D.one_lt_factor
  have h : D.mesh ≤ (D.L : ℝ) ^ (-2 : ℤ) := by
    have e : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
    rw [e]
    exact zpow_le_zpow_right₀ hL.le (by omega)
  show D.IsAdmissibleSide g.cellSide
  rw [cellSide_eq_one_of_q_eq_zero g hq]
  exact D.isAdmissibleSide_one h
abbrev _root_.YangMills.SharedProofs.p72971 := @hasAdmissibleSide_of_q_eq_zero
private theorem mem_cellObservables_of_mem_openCellAlgebra {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ D.openCellAlgebra S) : F ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨Φ, hΦ, ⟨C, hC⟩, e⟩ := hF
  refine ⟨fun u => Φ fun b => u ⟨b.1, b.2.2⟩, ?_, ⟨C, fun u => hC _⟩, ?_⟩
  · exact hΦ.comp (measurable_pi_iff.mpr fun b => measurable_pi_apply _)
  · funext U
    exact e U
private theorem const_one_mem_cellObservables (S : Set AmbientSpace) :
    (fun _ => 1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.one_mem_cellObservables <;> assumption
private theorem transportTo_const_one (g : ReflectionGrid D) (S S' : Set AmbientSpace) :
    g.transportTo S S' (fun _ => 1) = fun _ => 1 := by
  funext U
  show Conventions.signedConj _ (1 : ℂ) = 1
  unfold Conventions.signedConj
  split_ifs <;> simp
private theorem tiledIntegral_const_one (g : ReflectionGrid D) (n : EvenIndexVector) (S : Set AmbientSpace) :
    tiledIntegral g n S (fun _ => 1) = (torusPartition g n : ℂ) := by
  rw [tiledIntegral, torusPartition, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp [transportTo_const_one]
abbrev _root_.YangMills.SharedProofs.p27906 := @tiledIntegral_const_one
private theorem cubicCounts_coord_pos (D : ChessboardSetup) (e : ℕ) (κ : Fin 4) :
    0 < (cubicCounts D e).coord κ := by
  have := (cubicCounts D e).two_le κ
  omega
private theorem zero_mem_indexBox (D : ChessboardSetup) (e : ℕ) :
    (0 : Fin 4 → ℤ) ∈ (cubicCounts D e).indexBox := by
  rw [EvenIndexVector.indexBox, Fintype.mem_piFinset]
  intro κ
  simpa using cubicCounts_coord_pos D e κ
private theorem cellCount_cubicCounts (D : ChessboardSetup) (e : ℕ) :
    ((cellCount (cubicCounts D e) : ℕ) : ℝ) = (2 * (D.L : ℝ) ^ e) ^ 4 := by
  have h : ((cubicCounts D e).indexBox).card = ((2 * D.L ^ e) ^ 4 : ℕ) := by
    rw [EvenIndexVector.indexBox, Fintype.card_piFinset]
    simp only [Int.card_Ico, sub_zero, cubicCounts, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
  rw [cellCount, h]
  push_cast
  rfl
abbrev _root_.YangMills.SharedProofs.p78545 := @cellCount_cubicCounts
private theorem prod_coord_cubicCounts (D : ChessboardSetup) (e : ℕ) :
    ((∏ κ, (cubicCounts D e).coord κ : ℤ) : ℝ) = (cellCount (cubicCounts D e) : ℝ) := by
  rw [cellCount_cubicCounts]
  simp only [cubicCounts, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring
private theorem cellCount_cubicCounts_pos (D : ChessboardSetup) (e : ℕ) : 0 < cellCount (cubicCounts D e) :=
  Finset.card_pos.mpr ⟨_, zero_mem_indexBox D e⟩
private theorem norm_integral_le_root_tiledMean (hFam : CellFamiliesInTransferSetup.Statement)
    (hLaw : LawInAState.TorusMeanViaPeriods.Statement) (g : ReflectionGrid D) (hq : g.q = 0)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0))
    (hO : InfiniteLattice.IsBoundedObservable F) (e : ℕ) :
    ‖∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β‖ ≤
      ‖tiledMean g (cubicCounts D e) (g.cell 0) F‖ ^
        (1 / (cellCount (cubicCounts D e) : ℝ)) := by
  classical
  set n := cubicCounts D e with hn
  obtain ⟨hZ, hmean⟩ := hLaw D g hq e
  rw [← hn] at hZ hmean
  have hgrid : g.IsCoarse := by
    show 0 ≤ g.q
    omega
  let O : CoupledGrid := ⟨D, g, hgrid⟩
  obtain ⟨hnn, hest⟩ := (hFam O).2 n
  let fam : (Fin 4 → ℤ) → D.GaugeField → ℂ := fun k => if k = 0 then F else fun _ => 1
  have hfam : O.IsCellFamily n fam := by
    intro k _
    by_cases h : k = 0
    · subst h
      simpa [fam] using hF
    · simpa [fam, h] using const_one_mem_cellObservables (D := D) (g.cell k)
  have hb := hest fam hfam
  unfold CoupledGrid.ChessboardBoundForFamily at hb
  have h0 : (0 : Fin 4 → ℤ) ∈ n.indexBox := zero_mem_indexBox D e
  have hJ : O.cellFamilyIntegral n fam =
      (∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β) * (torusPartition g n : ℂ) := by
    rw [hmean F hO]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    have : ∏ k ∈ n.indexBox, fam k ((O.periodSubgroupOf n).liftGaugeField U) =
        F ((O.periodSubgroupOf n).liftGaugeField U) := by
      rw [Finset.prod_eq_single_of_mem (0 : Fin 4 → ℤ) h0]
      · simp [fam]
      · intro k _ hk
        simp [fam, hk]
    exact congrArg (· * _) this
  set P : ℝ := (cellCount n : ℝ) with hP
  have hPpos : 0 < P := by
    have := cellCount_cubicCounts_pos D e
    rw [hP, hn]
    exact_mod_cast this
  set X : ℝ := (tiledIntegral g n (g.cell 0) F).re with hX
  obtain ⟨hXim, hXnn⟩ : (tiledIntegral g n (g.cell 0) F).im = 0 ∧ 0 ≤ X := hnn (g.cell 0) ⟨0, rfl⟩ F hF
  set Z : ℝ := torusPartition g n with hZdef
  have hone : ∀ k, k ≠ 0 → (O.chessboardPartitionOn n (O.grid.cell k) (fam k)).re = Z := by
    intro k hk
    have e1 : fam k = fun _ => 1 := by simp [fam, hk]
    rw [e1]
    have e2 := tiledIntegral_const_one g n (g.cell k)
    show (tiledIntegral g n (g.cell k) (fun _ => 1)).re = Z
    rw [e2]
    simp [hZdef]
  have hprod : ∏ k ∈ n.indexBox, (O.chessboardPartitionOn n (O.grid.cell k) (fam k)).re ^
      (1 / ((∏ κ, n.coord κ : ℤ) : ℝ)) =
      X ^ (1 / P) * (Z ^ (1 / P)) ^ (n.indexBox.card - 1) := by
    rw [hn, prod_coord_cubicCounts D e, ← hn, ← Finset.mul_prod_erase _ _ h0]
    have e0 : (O.chessboardPartitionOn n (O.grid.cell 0) (fam 0)).re = X := by
      have : fam 0 = F := by simp [fam]
      rw [this]
      rfl
    rw [e0, Finset.prod_congr rfl fun k hk => by rw [hone k (Finset.ne_of_mem_erase hk)],
      Finset.prod_const, Finset.card_erase_of_mem h0]
  rw [hprod, hJ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ] at hb
  set w : ℝ := Z ^ (1 / P) with hw
  have hwpos : 0 < w := Real.rpow_pos_of_pos hZ _
  have hcard : (n.indexBox.card : ℝ) = P := rfl
  have hwc : w ^ n.indexBox.card = Z := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hZ.le, hcard, one_div, inv_mul_cancel₀ hPpos.ne',
      Real.rpow_one]
  obtain ⟨c, hc⟩ : ∃ c, n.indexBox.card = c + 1 := ⟨n.indexBox.card - 1, by
    have := Finset.card_pos.mpr ⟨_, h0⟩
    omega⟩
  rw [hc, Nat.add_sub_cancel] at hb
  rw [hc, pow_succ] at hwc
  rw [← hwc, ← mul_assoc] at hb
  have hb1 : ‖∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β‖ * w * w ^ c ≤
      X ^ (1 / P) * w ^ c := by
    have e1 : ‖∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β‖ * w * w ^ c =
        ‖∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β‖ * w ^ c * w := by ring
    rw [e1]
    exact hb
  have hb2 := le_of_mul_le_mul_right hb1 (pow_pos hwpos c)
  have hnorm : ‖tiledMean g n (g.cell 0) F‖ = X / Z := by
    have e1 : tiledIntegral g n (g.cell 0) F = (X : ℂ) := Complex.ext rfl (by simpa using hXim)
    rw [tiledMean, e1, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hXnn, abs_of_pos hZ]
  rw [hnorm, Real.div_rpow hXnn hZ.le, le_div_iff₀ hwpos]
  exact hb2
private theorem normAtExponent_eq_root_tiledMean (hEst : ChessboardTori.ChessboardEstimateAndSubadditivity.Statement)
    (hLaw : LawInAState.TorusMeanViaPeriods.Statement) (g : ReflectionGrid D) (hq : g.q = 0)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0)) (m' : ℕ+) :
    g.normAtExponent m' (g.cell 0) F =
      ‖tiledMean g (cubicCounts D m') (g.cell 0) F‖ ^
        (1 / (cellCount (cubicCounts D m') : ℝ)) := by
  have hgrid : g.IsCoarse := by
    show 0 ≤ g.q
    omega
  let O : CoupledGrid := CoupledGrid.withExponent ⟨D, g, hgrid⟩ m'
  have hL := D.one_lt_factor
  have hLp : (1 : ℝ) ≤ (D.L : ℝ) ^ (m' : ℕ) := one_le_pow₀ hL.le
  have hsideL : PeriodicLattice.torusSide D.L m' = 2 * (D.L : ℝ) ^ (m' : ℕ) := rfl
  have hs1 : O.cellSide = 1 := cellSide_eq_one_of_q_eq_zero (g.withExponent m') hq
  have hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m := by
    rw [hs1]
    show 2 * 1 ≤ PeriodicLattice.torusSide D.L m'
    rw [hsideL]
    linarith
  obtain ⟨hN, -, hS⟩ := hEst O hside
  have hsub := hS m' le_rfl hside
  have hc0 : g.cell 0 ∈ O.grid.cellSet := ⟨0, rfl⟩
  obtain ⟨⟨h1, hone⟩, hall⟩ := hN (g.cell 0) hc0
  have hA := (hsub.2.1 (g.cell 0) hc0 ⟨F, hF⟩).1
  have hB := (hsub.2.1 (g.cell 0) hc0 ⟨_, h1⟩).1
  set n := cubicCounts D m' with hn
  have hsq : O.diagonalCounts = n := by
    have hcoord : ∀ (a b : EvenIndexVector), a.coord = b.coord → a = b := by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      cases h
      rfl
    refine hcoord _ _ (funext fun _ => ?_)
    show 2 * (D.L : ℤ) ^ (((m' : ℕ) : ℤ) - g.q).toNat = 2 * (D.L : ℤ) ^ (m' : ℕ)
    rw [hq, sub_zero, Int.toNat_natCast]
  have hI : ∀ F' : D.GaugeField → ℂ,
      O.chessboardPartition (g.cell 0) F' = tiledIntegral g n (g.cell 0) F' := by
    intro F'
    show tiledIntegral (g.withExponent m') O.diagonalCounts (g.cell 0) F' = _
    rw [hsq]
    rfl
  obtain ⟨hZ, -⟩ := hLaw D g hq m'
  rw [← hn] at hZ
  rw [hI] at hA
  rw [hone, Real.one_rpow, Complex.ofReal_one, mul_one] at hB
  have hB' : tiledIntegral g n (g.cell 0) (fun _ => 1) = O.partitionFunction 0 := (hI _).symm.trans hB
  rw [tiledIntegral_const_one] at hB'
  rw [← hB'] at hA
  have hval : g.normAtExponent m' (g.cell 0) F = O.cellChessboardSeminorm hside hc0 ⟨F, hF⟩ := rfl
  have hsem : 0 ≤ O.cellChessboardSeminorm hside hc0 ⟨F, hF⟩ :=
    Real.rpow_nonneg ((hall ⟨F, hF⟩).1 _ ⟨0, rfl⟩).2.2.1 _
  set s := O.cellChessboardSeminorm hside hc0 ⟨F, hF⟩ with hs
  have hcps : O.grid.cellsAcross ^ 4 = (cellCount n : ℝ) := by
    have e1 : O.grid.cellsAcross = 2 * (D.L : ℝ) ^ (m' : ℕ) := by
      show PeriodicLattice.torusSide D.L m' / (g.withExponent m').cellSide = _
      rw [cellSide_eq_one_of_q_eq_zero (g.withExponent m') hq, div_one, hsideL]
    rw [e1, hn, cellCount_cubicCounts]
  have hmean : tiledMean g n (g.cell 0) F = ((s ^ (cellCount n : ℝ) : ℝ) : ℂ) := by
    rw [tiledMean, hA, hcps, mul_div_cancel_left₀ _ (by exact_mod_cast hZ.ne')]
  have hNpos : (cellCount n : ℝ) ≠ 0 := by
    have := cellCount_cubicCounts_pos D m'
    rw [← hn] at this
    exact_mod_cast this.ne'
  rw [hval, hmean, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsem _),
    ← Real.rpow_mul hsem, mul_one_div_cancel hNpos, Real.rpow_one]
private theorem root_tiledMean_le (hFall : ReflectedCopies.ChessboardNormBoundedByMinimalTorus)
    (g : ReflectionGrid D) (hq : g.q = 0) (hs : g.HasAdmissibleSide) {b₁ : ℝ}
    (hR : ReflectedCopies.TorusRatioBound D b₁) {G : D.GaugeField → ℝ}
    (hG : (fun U => (G U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0)) (j : ℕ) :
    ‖tiledMean g (cubicCounts D j) (g.cell 0) fun U => (G U : ℂ)‖ ^
        (1 / (cellCount (cubicCounts D j) : ℝ)) ≤ Real.exp b₁ * CellAverages.reflectionNorm g G := by
  have h1 := (hFall D g hs j).2 (g.cell 0) ⟨0, rfl⟩ _ hG
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
  have h2 := hR g hs j
  rw [cellSide_eq_one_of_q_eq_zero g hq] at h2
  have e0 : TorusBound.logPos (1 / 1) = 0 := by
    simp [TorusBound.logPos]
  rw [e0, Real.zero_rpow (by norm_num)] at h2
  simpa using h2
theorem cellDominationStatement_holds (hOne : ChessboardTori.CellDomination.Statement)
    (hEst : ChessboardTori.ChessboardEstimateAndSubadditivity.Statement)
    (hFam : ChessboardTori.CellFamiliesInTransferSetup.Statement)
    (hFall : ReflectedCopies.ChessboardNormBoundedByMinimalTorus)
    (hRatio : ReflectedCopies.TorusRatioBoundedStatement)
    (hLaw : LawInAState.TorusMeanViaPeriods.Statement) : StateLaws.cellDominationStatement := by
  intro a _
  obtain ⟨rt₀, hrt, h⟩ := hRatio
  refine ⟨0, rt₀, 0, hrt, ?_⟩
  intro L _ _ T _ _ hD hC _ hle _
  obtain ⟨y₀, hy⟩ := h T hD hC hle
  refine ⟨y₀, fun y hy0 hret hw Xi _ => ?_⟩
  obtain ⟨b₁, hb, hB⟩ := hy y hy0 ⟨hret, hw⟩ Xi
  refine ⟨Real.exp b₁, Real.one_le_exp hb, ?_⟩
  intro D hDL hdat g hq G hG μ hμ
  have hs : g.HasAdmissibleSide := hasAdmissibleSide_of_q_eq_zero g hq hdat.two_le
  have hR : ReflectedCopies.TorusRatioBound D b₁ := hB D ⟨hDL, hdat.le_coupling, hdat.coupling_le_top⟩
  have hC' : (fun U => (G U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0) :=
    mem_cellObservables_of_mem_openCellAlgebra hG
  have hO : InfiniteLattice.IsBoundedObservable fun U => (G U : ℂ) :=
    D.isBoundedObservable_of_mem_linkAlgebra hG
  have hnorm : |∫ U, G U ∂μ| = ‖∫ U, (G U : ℂ) ∂μ‖ := by
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hgrid : g.IsCoarse := by
    show 0 ≤ g.q
    omega
  have hbound := fun j => root_tiledMean_le hFall g hq hs hR hC' j
  rcases hμ with hμ | ⟨e, rfl⟩
  · refine ((hOne D g hgrid _ hC').2 μ hμ).trans ?_
    have hv : ∀ m' : ℕ+, g.normAtExponent m' (g.cell 0) (fun U => (G U : ℂ)) ≤
        Real.exp b₁ * CellAverages.reflectionNorm g G := fun m' => by
      rw [normAtExponent_eq_root_tiledMean hEst hLaw g hq hC' m']
      exact hbound m'
    refine limsup_le_of_le ?_ (Eventually.of_forall hv)
    have hbu : IsBoundedUnder (· ≥ ·) (atTop : Filter ℕ+)
        (fun m' => g.normAtExponent m' (g.cell 0) (fun U => (G U : ℂ))) :=
      isBoundedUnder_of ⟨0, fun m' => by
        rw [normAtExponent_eq_root_tiledMean hEst hLaw g hq hC' m']
        exact Real.rpow_nonneg (norm_nonneg _) _⟩
    exact hbu.isCoboundedUnder_le
  · exact (norm_integral_le_root_tiledMean hFam hLaw g hq hC' hO e).trans (hbound e)
end YangMills.Construction.LawInAState.LeastTorusDomination
end
