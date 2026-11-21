import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.InequalityOnMirroredCopies.ArrayMeanIsTheMeanOnTheTorus
import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
import YangMills.Construction.InequalityOnMirroredCopies.ObservableOffTheFacesIsInTheCell
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.MirrorGridsOfEverySide.DominationByTheChessboard
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ReflectedCopies
open YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.MirrorGridsAllSides.GridSetup (integralOf periodicGibbs)
def CopyCentreBound : Prop :=
  ∀ (D : ChessboardSetup) (A b : ℝ), 0 ≤ A → 0 ≤ b → CopyInequality D A b →
    ∀ (c : GridCell D) (ϱ : ℝ) (h : AmbientSpace → ℝ), SupportedInCell c ϱ h →
      ∃ κ : ℝ,
        (∀ m' : ℕ+, 2 * c.side ≤ YangMills.Construction.PeriodicLattice.torusSide D.L m' →
          (c.grid.withExponent m').chessboardNormOfCell c.cell (centredSmeared D h κ) ≤
              copyBound A b c.side ϱ h ∧
            ‖torusAverage D m'
                (YangMills.Construction.ReflectionsAndOneInsertion.complexSmeared D h) - (κ : ℂ)‖ ≤
              copyBound A b c.side ϱ h) ∧
        ∀ ν ∈ periodicGibbs D,
          ‖integralOf D ν (YangMills.Construction.ReflectionsAndOneInsertion.complexSmeared D h) -
              (κ : ℂ)‖ ≤
            copyBound A b c.side ϱ h
end YangMills.Construction.ReflectedCopies
end

open Filter MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
open ReflectionsAndOneInsertion (complexSmeared)
open MirrorGridsAllSides.GridSetup (integralOf periodicGibbs)
variable {D : ChessboardSetup}
private theorem sub_const_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (z : ℂ) :
    (fun U => F U - z) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨fun u => f u - z, hf.sub_const z, ⟨C + ‖z‖, fun u => ?_⟩, rfl⟩
  exact (norm_sub_le _ _).trans (by linarith [hC u])
abbrev _root_.YangMills.SharedProofs.p60740 := @sub_const_mem_cellObservables
private theorem isBoundedObservable_of_mem_cellObservables {S : Set AmbientSpace}
    {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_of_mem_cellObservables <;> assumption
private theorem copyBound_nonneg {A b l ϱ : ℝ} (hA : 0 ≤ A) (h : AmbientSpace → ℝ) :
    0 ≤ copyBound A b l ϱ h :=
  mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
    (le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _))
private theorem cellCount_ne_zero (n : EvenIndexVector) : cellCount n ≠ 0 := by
  refine Finset.card_ne_zero.mpr ⟨0, ?_⟩
  simp only [EvenIndexVector.indexBox, Fintype.mem_piFinset, Finset.mem_Ico, Pi.zero_apply,
    le_refl, true_and]
  exact fun κ => by linarith [n.two_le κ]
private theorem exists_torusSide_eq_cubic (g : ReflectionGrid D) {m' : ℕ+}
    (h2 : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m') :
    ∃ j : ℕ, PeriodicLattice.torusSide D.L m' = 2 * (D.L : ℝ) ^ j * g.cellSide := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have h3 : (D.L : ℝ) ^ g.q ≤ (D.L : ℝ) ^ (((m' : ℕ) : ℤ)) := by
    have h4 : (2 : ℝ) * (D.L : ℝ) ^ g.q ≤ 2 * (D.L : ℝ) ^ (m' : ℕ) := h2
    rw [zpow_natCast]
    linarith
  have h5 : g.q ≤ ((m' : ℕ) : ℤ) := (zpow_le_zpow_iff_right₀ hL).mp h3
  refine ⟨(((m' : ℕ) : ℤ) - g.q).toNat, ?_⟩
  have h6 : (D.L : ℝ) ^ (m' : ℕ) =
      (D.L : ℝ) ^ (((m' : ℕ) : ℤ) - g.q).toNat * (D.L : ℝ) ^ g.q := by
    rw [← zpow_natCast (D.L : ℝ) (((m' : ℕ) : ℤ) - g.q).toNat, Int.toNat_of_nonneg (by omega),
      ← zpow_add₀ hL0, sub_add_cancel, zpow_natCast]
  show (2 : ℝ) * (D.L : ℝ) ^ (m' : ℕ) = 2 * _ * (D.L : ℝ) ^ g.q
  rw [h6]
  ring
private theorem norm_periodicExpectation_le_chessboardNorm
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) (g : ReflectionGrid D)
    (hg : g.HasAdmissibleSide)
    (h2 : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    ‖D.periodicExpectation (D.liftedObservable F)‖ ≤ g.chessboardNormOfCell S F := by
  classical
  obtain ⟨⟨hest, -⟩, hii, -⟩ := hC D g hg h2
  obtain ⟨-, -, -, -, -, -, htor, -, -⟩ := hG D g hg
  obtain ⟨-, -, -, -, -, hread, -⟩ := htor h2
  have hR := (hread S hS F hF).1
  have hcell : D.proj '' S ∈ g.torusCellSet := ⟨S, hS, rfl⟩
  let C₀ : g.torusCellSet := ⟨_, hcell⟩
  let fam : g.torusCellSet → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    Function.update (fun _ _ => 1) C₀ (D.liftedObservable F)
  have hself : fam C₀ = D.liftedObservable F := Function.update_self _ _ _
  have hother : ∀ C, C ≠ C₀ → fam C = fun _ => 1 := fun C hC' =>
    Function.update_of_ne hC' _ _
  have hmem : ∀ C, fam C ∈ g.torusCellObservables C.1 := fun C => by
    by_cases hCC : C = C₀
    · subst hCC
      rw [hself]
      exact hR
    · rw [hother C hCC]
      exact (hii C.1 C.2).2.1
  have hb := hest fam hmem
  have hl : (fun U => ∏ᶠ C, fam C U) = D.liftedObservable F := by
    funext U
    rw [finprod_eq_single _ C₀ fun C hCC => by rw [hother C hCC], hself]
  have hr : ∏ᶠ C : g.torusCellSet, g.cellChessboardSeminorm C.1 (fam C) =
      g.cellChessboardSeminorm C₀.1 (D.liftedObservable F) := by
    rw [finprod_eq_single _ C₀ fun C hCC => by rw [hother C hCC]; exact (hii C.1 C.2).2.2,
      hself]
  rw [hl, hr] at hb
  exact hb
private theorem integral_sub_const_of_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {G : Ω → ℂ} (hm : Measurable G) {C : ℝ} (hb : ∀ U, ‖G U‖ ≤ C)
    (z : ℂ) : ∫ U, (G U - z) ∂μ = (∫ U, G U ∂μ) - z := by
  have hI : Integrable G μ := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
  rw [integral_sub hI (integrable_const z)]
  simp
theorem copyCentreBound_holds
    (hAM : TiledMeanIsPeriodicExpectation)
    (hO : SmearedMemCellObservables)
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hG : MirrorGridsAllSides.ReflectionGridProperties)
    (hDom : MirrorGridsAllSides.ChessboardDomination.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    CopyCentreBound := by
  intro D A b hA hb hI c ϱ h hh
  obtain ⟨κ, hκ⟩ := hI c ϱ h hh
  set q := copyBound A b c.side ϱ h with hq
  have hq0 : 0 ≤ q := copyBound_nonneg hA h
  have hobs := hO D c ϱ h hh
  have hF : centredSmeared D h κ ∈ ReflectionGrid.cellObservables (D := D) c.cell :=
    sub_const_mem_cellObservables hobs (κ : ℂ)
  have hOobs := isBoundedObservable_of_mem_cellObservables hobs
  have hval : ∀ m' : ℕ+, 2 * c.side ≤ PeriodicLattice.torusSide D.L m' →
      (c.grid.withExponent m').chessboardNormOfCell c.cell (centredSmeared D h κ) ≤ q := by
    intro m' hm'
    obtain ⟨j, hj⟩ := exists_torusSide_eq_cubic c.grid hm'
    obtain ⟨-, hfun⟩ := hAM D c.grid c.hasAdmissibleSide c.cell c.cell_mem_cellSet _ hF m' j hj
    obtain ⟨him, hre0, hreq⟩ := hκ j
    set z := tiledMean c.grid (cubicCounts D j) c.cell (centredSmeared D h κ) with hz
    have hnorm : ‖z‖ = z.re := by
      have hzz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
      rw [hzz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using hre0)]
      simp
    have hN := cellCount_ne_zero (cubicCounts D j)
    rw [hfun, hnorm]
    calc z.re ^ (1 / (cellCount (cubicCounts D j) : ℝ))
        ≤ (q ^ cellCount (cubicCounts D j)) ^
            (1 / (cellCount (cubicCounts D j) : ℝ)) :=
          Real.rpow_le_rpow hre0 hreq (by positivity)
      _ = q := by
          rw [one_div]
          exact Real.pow_rpow_inv_natCast hq0 hN
  have hLg : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  refine ⟨κ, fun m' hm' => ⟨hval m' hm', ?_⟩, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, hprob, -, -⟩ := hW D.L m' D.K D.β hLg m'.pos D.K.pos
    have hmeas : Measurable ((D.withExponent m').liftedObservable (complexSmeared D h)) :=
      hOobs.1.comp (InfiniteLattice.measurable_liftField D.L m' ((D.K : ℕ) : ℤ))
    obtain ⟨Cb, hCb⟩ := hOobs.2
    have hsub : (D.withExponent m').periodicExpectation
          ((D.withExponent m').liftedObservable (centredSmeared D h κ)) =
        torusAverage D m' (complexSmeared D h) - (κ : ℂ) :=
      integral_sub_const_of_bounded (PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β) hmeas
        (fun U => hCb _) (κ : ℂ)
    rw [← hsub]
    exact (norm_periodicExpectation_le_chessboardNorm (D := D.withExponent m') hC hG
      (c.grid.withExponent m') c.hasAdmissibleSide hm' c.cell_mem_cellSet hF).trans (hval m' hm')
  · intro ν hν
    have hprob : IsProbabilityMeasure ν :=
      (show InfiniteLattice.IsPeriodicGibbs D.β ν from hν).1.1
    obtain ⟨Cb, hCb⟩ := hOobs.2
    have hsub : integralOf D ν (centredSmeared D h κ) =
        integralOf D ν (complexSmeared D h) - (κ : ℂ) :=
      integral_sub_const_of_bounded ν hOobs.1 hCb (κ : ℂ)
    rw [← hsub]
    classical
    have hsides : Tendsto (fun k : ℕ+ => PeriodicLattice.torusSide D.L (id k : ℕ+)) atTop atTop := by
      have hp : Tendsto (fun n : ℕ => (2 : ℝ) * (D.L : ℝ) ^ n) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt D.one_lt_factor).const_mul_atTop (by norm_num)
      exact hp.comp tendsto_PNat_val_atTop_atTop
    have hlarge : ∀ᶠ k : ℕ+ in atTop, 2 * c.side ≤ PeriodicLattice.torusSide D.L (id k : ℕ+) :=
      hsides.eventually_ge_atTop _
    by_cases hG1 : centredSmeared D h κ = 1
    · obtain ⟨k, hk⟩ := hlarge.exists
      have hv := hval (id k) hk
      obtain ⟨-, hii, -⟩ := hC (D.withExponent (id k)) (c.grid.withExponent (id k))
        c.hasAdmissibleSide hk
      have hcell : (D.withExponent (id k)).proj '' c.cell ∈
          (c.grid.withExponent (id k)).torusCellSet :=
        ⟨c.cell, c.cell_mem_cellSet, rfl⟩
      have h1 : (c.grid.withExponent (id k)).chessboardNormOfCell c.cell
          (centredSmeared D h κ) = 1 := by
        rw [hG1]
        exact (hii _ hcell).2.2
      have hone : integralOf D ν (centredSmeared D h κ) = 1 := by
        rw [hG1]
        show ∫ U, (1 : ℂ) ∂ν = 1
        simp
      rw [hone, norm_one]
      linarith
    · let S₀ : c.grid.cellSet := ⟨c.cell, c.cell_mem_cellSet⟩
      let fam : c.grid.cellSet → D.GaugeField → ℂ :=
        Function.update (fun _ => 1) S₀ (centredSmeared D h κ)
      have hself : fam S₀ = centredSmeared D h κ := Function.update_self _ _ _
      have hother : ∀ S, S ≠ S₀ → fam S = 1 := fun S hS => Function.update_of_ne hS _ _
      have hfam : ∀ S, fam S ∈ ReflectionGrid.cellObservables (D := D) S.1 := fun S => by
        by_cases hS : S = S₀
        · subst hS
          rw [hself]
          exact hF
        · rw [hother S hS]
          exact ⟨fun _ => 1, measurable_const, ⟨1, by simp⟩, rfl⟩
      have hfin : {S | fam S ≠ 1}.Finite :=
        (Set.finite_singleton S₀).subset fun S hS => by_contra fun hne => hS (hother S hne)
      have hfs : hfin.toFinset = {S₀} := by
        ext S
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
        constructor
        · exact fun hS => by_contra fun hne => hS (hother S hne)
        · rintro rfl
          rw [hself]
          exact hG1
      have hdom := (hDom D ν hν c.grid c.hasAdmissibleSide id hsides fam hfam hfin).1
      rw [hfs] at hdom
      simp only [Finset.prod_singleton, hself] at hdom
      refine hdom.trans (liminf_le_of_frequently_le ?_ ?_)
      · exact (hlarge.mono fun k hk => hval (id k) hk).frequently
      · exact isBoundedUnder_of_eventually_ge (a := 0)
          (Eventually.of_forall fun k => Real.rpow_nonneg (norm_nonneg _) _)
end YangMills.Construction.ReflectedCopies
end
