import YangMills.Construction.Lattice.AveragesAndIteratesAreConfigurationsProof
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Averaging Conventions
namespace PeriodicLattice
namespace ComplexGroupLog
theorem trace_logSeries_one_sub (A : ComplexMatrix2) (hdet : (1 - A).det = 1) (hA : ‖A‖ < 1) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.logSeries (1 - A)) = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.GaugeFieldMembership.fullTrace_logSeries_one_sub <;> assumption
theorem trace_logSeries_eq_zero {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup)
    (hnear : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.logSeries X) = 0 := by
  have hdet : X.det = 1 := hX
  have h := trace_logSeries_one_sub (1 - X) (by simpa using hdet)
    (by rw [norm_sub_rev]; exact hnear)
  simpa using h
theorem logSeries_mem_traceless {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup)
    (hnear : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.logSeries X ∈ ComplexMatrix2.traceless :=
  trace_logSeries_eq_zero hX hnear
theorem mul_mem {P Q : ComplexMatrix2} (hP : P ∈ complexGaugeGroup) (hQ : Q ∈ complexGaugeGroup) :
    P * Q ∈ complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
theorem inv_mem {P : ComplexMatrix2} (hP : P ∈ complexGaugeGroup) : P⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem matExp_mem (hExp : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) : ComplexMatrix2.matExp Y ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.matExp_mem <;> assumption
theorem pathHolonomy_mem {L m : ℕ} {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    {γ : List (Bond L m j)} (hU : ∀ b ∈ γ, U b ∈ complexGaugeGroup) :
    pathHolonomy U γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem complexLogMean_mem (hMean : ComplexLogMeanOfSmallFamilies) {ι : Type*} [Fintype ι]
    [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < centreOfMassDiameter) :
    complexLogMean V ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.GaugeFieldMembership.complexLogMean_mem <;> assumption
instance {L m : ℕ} {j j' : ℤ} (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(Finset.equivFin _).symm⟩
section Averages
variable {L m K n : ℕ}
theorem contourHolonomy_mem (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) {W : BondAtLevel L m K n → ComplexMatrix2} {y : SiteAtLevel L m K (n + 1)}
    {x : SiteAtLevel L m K n} (h : IsContourHolonomyDefined .centred W y x) :
    contourHolonomy .centred W y x ∈ complexGaugeGroup := by
  obtain ⟨hx, hcfg, hd⟩ := h
  have hp := ((hS L hL m K n hm hn .centred).1 y x hx).1.contour_within
  exact complexLogMean_mem hMean _
    (fun σ => pathHolonomy_mem fun b hb => hcfg.1 b ((hp σ).2 b hb)) hd
theorem complexBlockAverage_mem (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hDouble : DoubleBlockStructure.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented)
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → ComplexMatrix2))) :
    complexBlockAverage W c ∈ complexGaugeGroup := by
  obtain ⟨⟨hCfg, hSrc, hTgt⟩, hNear⟩ := hW
  have hCross := (hDouble L m K n hL hm hn c).2.2.1.1
  have hBase := ((hS L hL m K n hm hn .centred).2.1 c hc).1.base_within
  have hSrcCfg : IsGaugeField complexGaugeGroup (bondsInside (unitBlock c.source)) W :=
    ⟨fun b hb => hCfg.1 b ⟨Or.inl hb.1, Or.inl hb.2⟩,
      fun b hb => hCfg.2 b ⟨Or.inl hb.1, Or.inl hb.2⟩⟩
  have hTgtCfg : IsGaugeField complexGaugeGroup (bondsInside (unitBlock c.target)) W :=
    ⟨fun b hb => hCfg.1 b ⟨Or.inr hb.1, Or.inr hb.2⟩,
      fun b hb => hCfg.2 b ⟨Or.inr hb.1, Or.inr hb.2⟩⟩
  have hT : parallelTransport W c ∈ complexGaugeGroup :=
    pathHolonomy_mem fun b hb => hCfg.1 b (hBase.2 b hb)
  have hElem : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      complexCrossingDefect W c x ∈ complexGaugeGroup := by
    intro x hx
    have h1 : complexMeanContourHolonomy W c.source x ∈ complexGaugeGroup :=
      contourHolonomy_mem hS hMean hL hm hn ⟨hx, hSrcCfg, hSrc x hx⟩
    have hx' : shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := (hCross x hx).1
    have h2 : complexMeanContourHolonomy W c.target (shiftAcross c x) ∈ complexGaugeGroup :=
      contourHolonomy_mem hS hMean hL hm hn ⟨hx', hTgtCfg, hTgt _ hx'⟩
    have h3 : pathHolonomy W (crossingPath c x) ∈ complexGaugeGroup :=
      pathHolonomy_mem fun b hb => hCfg.1 b ((hCross x hx).2.2.2.2 b hb)
    exact mul_mem (mul_mem (mul_mem h1 h3) (inv_mem h2)) (inv_mem hT)
  have hSum : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.logSeries (complexCrossingDefect W c x)) ∈ ComplexMatrix2.traceless :=
    finsum_mem_induction (fun M : ComplexMatrix2 => M ∈ ComplexMatrix2.traceless)
      ComplexMatrix2.traceless.zero_mem
      (fun _ _ hA hB => ComplexMatrix2.traceless.add_mem hA hB)
      (fun x hx => logSeries_mem_traceless (hElem x hx) (hNear x hx))
  simp only [complexBlockAverage, if_pos hc]
  exact mul_mem (matExp_mem hExp (ComplexMatrix2.traceless.smul_mem _ hSum)) hT
theorem stepRatio_mem (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) {c : BondAtLevel L m K (n + 1)} {a : LieBondField (doubleBlockSymmetricSet c)}
    {W₀ : BondAtLevel L m K n → ComplexMatrix2} {y : SiteAtLevel L m K (n + 1)}
    {x : SiteAtLevel L m K n} (h : StepLogDefinedAt .centred c a W₀ y x) :
    stepRatio .centred c a W₀ y x ∈ complexGaugeGroup :=
  mul_mem (contourHolonomy_mem hS hMean hL hm hn h.1)
    (inv_mem (contourHolonomy_mem hS hMean hL hm hn h.2.1))
theorem stepLog_mem (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) {c : BondAtLevel L m K (n + 1)} {a : LieBondField (doubleBlockSymmetricSet c)}
    {W₀ : BondAtLevel L m K n → ComplexMatrix2} {y : SiteAtLevel L m K (n + 1)}
    {x : SiteAtLevel L m K n} (h : StepLogDefinedAt .centred c a W₀ y x) :
    stepLog .centred c a W₀ y x ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.smul_mem _
    (logSeries_mem_traceless (stepRatio_mem hS hMean hL hm hn h) h.2.2)
theorem stepGauge_mem (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} {a : LieBondField (doubleBlockSymmetricSet c)}
    {W₀ : BondAtLevel L m K n → ComplexMatrix2} {y : SiteAtLevel L m K (n + 1)}
    (h : StepGaugeDefinedAt .centred c a W₀ y) :
    stepGauge .centred c a W₀ y ∈ complexGaugeGroup := by
  have hSum : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog .centred c a W₀ y x) ∈
      ComplexMatrix2.traceless :=
    finsum_mem_induction (fun M : ComplexMatrix2 => M ∈ ComplexMatrix2.traceless)
      ComplexMatrix2.traceless.zero_mem
      (fun _ _ hA hB => ComplexMatrix2.traceless.add_mem hA hB)
      (fun x hx => stepLog_mem hS hMean hL hm hn (h x hx))
  exact matExp_mem hExp
    (ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ hSum))
end Averages
end ComplexGroupLog
open ComplexGroupLog in
theorem logSeriesInComplexGroup_holds (hS : AveragingSchemeProperties)
    (hMean : ComplexLogMeanOfSmallFamilies) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hDouble : DoubleBlockStructure.Statement) :
    LogSeriesInComplexGroupStatement := by
  refine ⟨fun X hX hnear => ⟨trace_logSeries_eq_zero hX hnear, logSeries_mem_traceless hX hnear⟩, ?_⟩
  intro L hL m K n hm hn c hc
  refine ⟨fun W hW => complexBlockAverage_mem hS hMean hExp hDouble hL hm hn hc hW, ?_⟩
  intro W₀ a _
  refine ⟨fun y _ => ⟨fun x _ h => stepLog_mem hS hMean hL hm hn h,
    fun h => stepGauge_mem hS hMean hExp hL hm hn h⟩, ?_⟩
  rintro ⟨⟨hcv, hcv₀, hnS, hnT⟩, hA, hA₀, hnP⟩
  have hgS : stepGauge .centred c a W₀ c.source ∈ complexGaugeGroup :=
    stepGauge_mem hS hMean hExp hL hm hn fun x hx => ⟨hcv.1 x hx, hcv₀.1 x hx, hnS x hx⟩
  have hgT : stepGauge .centred c a W₀ c.target ∈ complexGaugeGroup :=
    stepGauge_mem hS hMean hExp hL hm hn fun x hx => ⟨hcv.2 x hx, hcv₀.2 x hx, hnT x hx⟩
  have hM := ((hS L hL m K n hm hn .centred).2.1 c hc).2.2.1
  have hAvg : ∀ W : BondAtLevel L m K n → ComplexMatrix2, IsSchemeAverageDefined .centred W c →
      schemeBlockAverage .centred W c ∈ complexGaugeGroup := by
    intro W hW
    have hd : W ∈ (schemeHolomorphyDomain .centred c : Set (BondAtLevel L m K n → ComplexMatrix2)) :=
      hW
    rw [hM.average_eq W hd]
    exact complexBlockAverage_mem hS hMean hExp hDouble hL hm hn hc (hM.domain_eq ▸ hd)
  have hP : stepProduct .centred c a W₀ ∈ complexGaugeGroup :=
    mul_mem (mul_mem (mul_mem (inv_mem hgS) (hAvg _ hA)) hgT) (inv_mem (hAvg _ hA₀))
  exact ComplexMatrix2.traceless.smul_mem _ (logSeries_mem_traceless hP hnP)
end PeriodicLattice
end YangMills.Construction
