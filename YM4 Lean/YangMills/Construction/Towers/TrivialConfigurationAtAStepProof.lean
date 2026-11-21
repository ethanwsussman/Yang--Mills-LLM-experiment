import YangMills.Construction.Lattice.AveragesAndContourVariablesOfTheIdentityConfigurationProof
import YangMills.Construction.Averaging.MeanOfTheConstantFamily
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Tower.TrivialFieldProof
open PeriodicLattice Matrices Averaging
variable {L m : ℕ} {j j' : ℤ}
private theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
private theorem pathHolonomy_one (Γ : List (PeriodicLattice.Bond L m j')) :
    pathHolonomy (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p500861 <;> assumption
abbrev _root_.YangMills.SharedProofs.p14112 := @pathHolonomy_one
private theorem isLogMean_const_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    ComplexMatrix2.IsLogMean compactGaugeGroup (fun _ : ι => (1 : ComplexMatrix2)) =
      ComplexMatrix2.IsLogMean compactGaugeGroup (identityFamily (Fintype.card ι)) := by
  have : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, Fintype.card_pos⟩⟩
  funext W
  apply propext
  simp [identityFamily, ComplexMatrix2.IsLogMean]
private theorem axisOrdering_nonempty (y : PeriodicLattice.Site L m j)
    (x : PeriodicLattice.Site L m j') : Nonempty (AxisOrdering y x) :=
  ⟨(Finset.equivFin _).symm⟩
private theorem contourHolonomies_one (y : PeriodicLattice.Site L m j)
    (x : PeriodicLattice.Site L m j') :
    contourHolonomies (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) y x = fun _ => 1 :=
  funext fun _ => pathHolonomy_one _
private theorem hasContourMean_one (h : IdentityFamilyMeanIsOne) (y : PeriodicLattice.Site L m j)
    (x : PeriodicLattice.Site L m j') :
    HasContourMean (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) y x := by
  have := axisOrdering_nonempty y x
  have hn : 1 ≤ Fintype.card (AxisOrdering y x) := Fintype.card_pos
  unfold HasContourMean ComplexMatrix2.HasUniqueLogMean
  rw [contourHolonomies_one, isLogMean_const_one]
  exact ((h _ hn).2.1 compactGaugeGroup (Or.inl rfl)).2.1
private theorem meanContourHolonomy_one (h : IdentityFamilyMeanIsOne) (y : PeriodicLattice.Site L m j)
    (x : PeriodicLattice.Site L m j') :
    meanContourHolonomy (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) y x = 1 := by
  have := axisOrdering_nonempty y x
  have hn : 1 ≤ Fintype.card (AxisOrdering y x) := Fintype.card_pos
  unfold meanContourHolonomy ComplexMatrix2.logMean
  rw [contourHolonomies_one, isLogMean_const_one]
  exact ((h _ hn).2.1 compactGaugeGroup (Or.inl rfl)).2.2
private theorem crossingDefect_one (h : IdentityFamilyMeanIsOne) (c : PeriodicLattice.Bond L m j)
    (x : PeriodicLattice.Site L m j') :
    crossingDefect (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) c x = 1 := by
  simp [crossingDefect, meanContourHolonomy_one h, parallelTransport, pathHolonomy_one]
private theorem isRegularAveragingCase_one (h : IdentityFamilyMeanIsOne) {ω : ℝ} (hω : 0 < ω)
    (c : PeriodicLattice.Bond L m j) :
    IsRegularAveragingCase ω (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) c := by
  refine ⟨fun p _ => ?_, fun x _ => hasContourMean_one h _ x,
    fun x _ => hasContourMean_one h _ x, fun x _ => ?_⟩
  · simpa [plaquetteHolonomy, pathHolonomy_one, ComplexMatrix2.operatorNorm] using hω
  · simp [crossingDefect_one h, ComplexMatrix2.operatorNorm]
private theorem blockAverageOnPositive_one (h : IdentityFamilyMeanIsOne) {ω : ℝ}
    (hω : 0 < ω) (c : PeriodicLattice.Bond L m j) :
    blockAverageOnPositive ω (fun _ : PeriodicLattice.Bond L m j' => (1 : ComplexMatrix2)) c = 1 := by
  unfold blockAverageOnPositive
  rw [if_pos (isRegularAveragingCase_one h hω c)]
  simp [regularAverageValue, crossingDefect_one h, logSeries_one, parallelTransport, pathHolonomy_one,
    ComplexMatrix2.matExp]
theorem trivialFieldAtStep_holds (h : IdentityFamilyMeanIsOne) : TrivialFieldAtStep := by
  intro L n k i hL _ hi
  have hω : 0 < smoothingRadius L := (isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  refine ⟨fun y x _ => meanContourHolonomy_one h y x, ?_, ⟨⟨hi, ?_, fun y _ x _ =>
    hasContourMean_one h y x⟩, fun y _ x _ _ => meanContourHolonomy_one h y x⟩⟩
  · funext c
    change blockAverage (smoothingRadius L) (fun _ => (1 : ComplexMatrix2)) c = 1
    unfold blockAverage
    split_ifs
    · exact blockAverageOnPositive_one h hω c
    · rw [blockAverageOnPositive_one h hω c.opposite]
      simp
  · exact ⟨fun _ _ => (1 : ComplexMatrix2.specialUnitary).2, fun _ _ => by simp⟩
end YangMills.Construction.Tower.TrivialFieldProof
