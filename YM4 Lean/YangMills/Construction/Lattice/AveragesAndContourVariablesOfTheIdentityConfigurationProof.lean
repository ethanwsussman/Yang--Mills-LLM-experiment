import YangMills.Construction.Averaging.MeanOfTheConstantFamily
import YangMills.Construction.Lattice.AveragesAndContourVariablesOfTheIdentityConfiguration
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.PeriodicLattice.TrivialFieldAverages
variable {L m : ℕ} {j j' : ℤ}
private theorem logSeries_one : Matrices.ComplexMatrix2.logSeries 1 = 0 := by
  simp [Matrices.ComplexMatrix2.logSeries]
private theorem pathHolonomy_trivial (γ : List (Bond L m j')) :
    pathHolonomy trivialGaugeField γ = 1 := by
  induction γ with
  | nil => rfl
  | cons b γ ih => simpa [pathHolonomy, trivialGaugeField] using ih
abbrev _root_.YangMills.DeltaSharedProofs.p500861 := @pathHolonomy_trivial
abbrev _root_.YangMills.SharedProofs.p62034 := @pathHolonomy_trivial
private theorem complexLogMean_const (hMean : Averaging.IdentityFamilyMeanIsOne) {ι : Type*}
    [Fintype ι] [Nonempty ι] :
    complexLogMean (fun _ : ι => (1 : Matrices.ComplexMatrix2)) = 1 := by
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, hn⟩⟩
  refine Eq.trans ?_ (hMean _ hn).2.2
  unfold complexLogMean
  congr 1
  funext W
  apply propext
  simp [Averaging.identityFamily, Matrices.ComplexMatrix2.IsLogMean]
abbrev _root_.YangMills.SharedProofs.p63807 := @complexLogMean_const
private theorem axisOrdering_nonempty (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(Finset.equivFin _).symm⟩
private theorem contourHolonomies_trivial (y : Site L m j) (x : Site L m j') :
    contourHolonomies trivialGaugeField y x = fun _ => 1 :=
  funext fun _ => pathHolonomy_trivial _
private theorem contourHolonomy_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) (y : Site L m j) (x : Site L m j') :
    contourHolonomy s trivialGaugeField y x = 1 := by
  cases s
  · have := axisOrdering_nonempty y x
    change complexLogMean (contourHolonomies trivialGaugeField y x) = 1
    rw [contourHolonomies_trivial]
    exact complexLogMean_const hMean
  · exact pathHolonomy_trivial _
private theorem isGaugeField_trivial (B : Set (Bond L m j')) :
    IsGaugeField complexGaugeGroup B trivialGaugeField :=
  ⟨fun _ _ => Matrix.det_one, fun _ _ => by simp [trivialGaugeField]⟩
private theorem isContourHolonomyDefined_trivial (s : AveragingScheme) (y : Site L m j)
    (x : Site L m j') (hx : x ∈ sitesInBlock j' y) :
    IsContourHolonomyDefined s trivialGaugeField y x := by
  refine ⟨hx, isGaugeField_trivial _, ?_⟩
  cases s
  · have := axisOrdering_nonempty y x
    change Matrices.ComplexMatrix2.familyDiameter (contourHolonomies trivialGaugeField y x) <
      Averaging.centreOfMassDiameter
    rw [contourHolonomies_trivial]
    simp [Matrices.ComplexMatrix2.familyDiameter, Averaging.centreOfMassDiameter]
  · trivial
private theorem localDefect_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) (c : Bond L m j) (x : Site L m j') :
    localDefect s trivialGaugeField c x = 1 := by
  simp [localDefect, baseTransport, contourHolonomy_trivial hMean, pathHolonomy_trivial]
private theorem isSchemeAverageDefined_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) (c : Bond L m j) :
    IsSchemeAverageDefined (j' := j') s trivialGaugeField c := by
  refine ⟨isGaugeField_trivial _, ⟨fun x hx => isContourHolonomyDefined_trivial s _ x hx,
    fun x hx => isContourHolonomyDefined_trivial s _ x hx⟩, fun x _ => ?_⟩
  simp [localDefect_trivial hMean]
private theorem positiveBondAverage_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) (c : Bond L m j) :
    positiveBondAverage (j' := j') s trivialGaugeField c = 1 := by
  have hsum : ∑ᶠ x ∈ sitesInBlock j' c.source,
      Matrices.ComplexMatrix2.logSeries (localDefect s trivialGaugeField c x) = 0 := by
    simp [localDefect_trivial hMean, logSeries_one]
  simp [positiveBondAverage, baseTransport, pathHolonomy_trivial, hsum]
private theorem schemeBlockAverage_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (s : AveragingScheme) :
    (schemeBlockAverage s (trivialGaugeField : Bond L m j' → Matrices.ComplexMatrix2) :
        Bond L m j → Matrices.ComplexMatrix2) = trivialGaugeField := by
  funext c
  by_cases hc : c.IsPositivelyOriented
  · simp [schemeBlockAverage, hc, positiveBondAverage_trivial hMean, trivialGaugeField]
  · simp [schemeBlockAverage, hc, positiveBondAverage_trivial hMean, trivialGaugeField]
private theorem iteratedAverage_trivial (hMean : Averaging.IdentityFamilyMeanIsOne) (K : ℕ)
    (s : AveragingScheme) (n : ℕ) :
    iteratedAverage (L := L) (m := m) (K := K) s n trivialGaugeField = trivialGaugeField := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change schemeBlockAverage s (iteratedAverage s n trivialGaugeField) = _
    rw [ih]
    exact schemeBlockAverage_trivial hMean s
private theorem isBareIterateDefined_trivial (hMean : Averaging.IdentityFamilyMeanIsOne)
    (K : ℕ) (s : AveragingScheme) (n : ℕ) (c : BondAtLevel L m K n) :
    IsBareIterateDefined s trivialGaugeField n c := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨fun b _ => ih b, ?_⟩
    rw [iteratedAverage_trivial hMean K s n]
    exact isSchemeAverageDefined_trivial hMean s _
theorem trivialGaugeField_averages (hMean : Averaging.IdentityFamilyMeanIsOne) :
    TrivialFieldAverages.Statement := by
  intro L _ m K _ s
  refine ⟨fun j _ c => ⟨isBareIterateDefined_trivial hMean K s j c, ?_⟩,
    fun j _ y x hx => ?_⟩
  · rw [iteratedAverage_trivial hMean K s j]
    rfl
  · rw [iteratedAverage_trivial hMean K s j]
    exact ⟨isContourHolonomyDefined_trivial s y x hx, contourHolonomy_trivial hMean s y x⟩
end YangMills.Construction.PeriodicLattice.TrivialFieldAverages
