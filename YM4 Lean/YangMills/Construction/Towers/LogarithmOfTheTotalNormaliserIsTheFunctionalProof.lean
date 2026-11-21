import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalytic
import YangMills.Construction.Towers.LogarithmOfTheNormaliserLessTheFunctionalIsConstant
import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserIsTheFunctional
import YangMills.Construction.Towers.RealAnalyticFunctionsConstantWhereTheCovariantDifferenceIsInjective
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctions
import YangMills.Construction.Towers.TotalNormaliserIsAProduct
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.LogTotalNormaliser
variable {L n k : ℕ}
theorem fieldSpace_isRelativelyOpen (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰 : Set (Edge L n k k → Matrices.ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k k) 𝒰 :=
  (((hE L hL k k le_rfl).1 n hn).2.2.2.2.2.2.2.2.1 𝒰 h.1).2 h.2
theorem isOpenFieldSet_inter (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰₁ 𝒰₂ : Set (Edge L n k k → Matrices.ComplexMatrix2)}
    (h₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₁)
    (h₂ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₂) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ 𝒰₂) := by
  have A := ((hE L hL k k le_rfl).1 n hn).2.2.2.2.2.2.2.2.1
  have hsub : 𝒰₁ ∩ 𝒰₂ ⊆ fieldSpace L n k k := fun V hV => h₁.1 hV.1
  obtain ⟨O₁, hO₁, e₁⟩ := fieldSpace_isRelativelyOpen hE hL hn h₁
  obtain ⟨O₂, hO₂, e₂⟩ := fieldSpace_isRelativelyOpen hE hL hn h₂
  refine ⟨hsub, (A _ hsub).1 ⟨O₁ ∩ O₂, hO₁.inter hO₂, ?_⟩⟩
  rw [e₁, e₂]
  ext V
  simp only [mem_inter_iff]
  tauto
theorem mem_nhdsWithin_of_isOpenNhdOfOne (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰 : Set (Edge L n k k → Matrices.ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    𝒰 ∈ 𝓝[fieldSpace L n k k] (fun _ => (1 : Matrices.ComplexMatrix2)) := by
  obtain ⟨O, hO, e⟩ := fieldSpace_isRelativelyOpen hE hL hn h.1
  have h1 : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ O := by
    have := h.2
    rw [e] at this
    simp only [mem_inter_iff] at this
    tauto
  refine mem_nhdsWithin.2 ⟨O, hO, h1, fun V hV => ?_⟩
  rw [e]
  simp only [mem_inter_iff] at hV ⊢
  tauto
theorem logTotalNormaliserEqFunctional_holds (hA : BackgroundFunctionalAlongBranchAnalytic)
    (hB : LogNormaliserSubBackgroundConst)
    (hC : IdentityPrincipleNearOneStatement)
    (hP : TotalNormaliserFactorises)
    (hR : LogTotalNormaliserAnalytic)
    (hS : AnalyticFieldFunctionsClosed)
    (hE : BondSetFields.ProductStructureHolds) : LogTotalNormaliserEqFunctional := by
  intro L n k hL hn hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨𝒰₁, F, h𝒰₁, hFan, hF, hF1⟩ := hA L n (k + 1) hL hn hk
  obtain ⟨𝒰₂, h𝒰₂, hΨan⟩ := hR L n k hL hn
  obtain ⟨C, hCnear⟩ := hB L n (k + 1) hL hn hk
  obtain ⟨hconst, hsum, hsub, -, -⟩ := hS L n (k + 1) (k + 1) (k + 1) hL hn le_rfl le_rfl
  have hopen : IsOpenNhdOfOne (𝒰₁ ∩ 𝒰₂) :=
    ⟨isOpenFieldSet_inter hE hL hn h𝒰₁.1 h𝒰₂.1, h𝒰₁.2, h𝒰₂.2⟩
  have hFan' := hsub 𝒰₁ _ F hFan hopen.1 inter_subset_left
  have hΨan' := hsub 𝒰₂ _ _ hΨan hopen.1 inter_subset_right
  have hnegF := (hsum _ (fun _ => (-1 : ℝ)) F (hconst _ (-1) hopen.1) hFan').2
  have hfan := (hsum _ _ _ hΨan' hnegF).1
  have hmem := mem_nhdsWithin_of_isOpenNhdOfOne hE hL hn hopen
  have h1c : trivialField L n (k + 1) (k + 1) ∈ fieldSpace L n (k + 1) (k + 1) :=
    hopen.1.1 hopen.2
  have hprod := hP L n (k + 1) hL hn hk
  unfold EventuallyNearIdentity at hprod hCnear
  have h1formed : TotalNormaliserWellDefined (trivialField L n (k + 1) (k + 1)) :=
    (hprod.self_of_nhdsWithin h1c).1
  have hnear := hC L n (k + 1) hL hn hk _ _
    (C - Real.log (totalGaussianNormaliser L n (k + 1) (trivialField L n (k + 1) (k + 1))))
    hopen hfan (by
      unfold EventuallyNearIdentity
      filter_upwards [hCnear, hmem] with W hW hWm hfree
      obtain ⟨J, μ, hJ, hμ, -, hFW⟩ := hF W hWm.1
      have e := hW hfree J μ hJ hμ
      simp only [logTotalNormaliserRatio, Nat.succ_ne_zero, if_false, hFW]
      linarith)
  unfold EventuallyNearIdentity at hnear ⊢
  have hone := hnear.self_of_nhdsWithin h1c
  simp only [logTotalNormaliserRatio, Nat.succ_ne_zero, if_false, hF1, sub_self] at hone
  filter_upwards [hnear, hmem, hprod] with W hW hWm hWp
  obtain ⟨J, μ, hJ, hμ, hform, hFW⟩ := hF W hWm.1
  refine ⟨Or.inr ⟨hWp.1, h1formed⟩, J, μ, hJ, hμ, hform, ?_⟩
  rw [hFW] at hW
  linarith
end YangMills.Construction.Tower.LogTotalNormaliser
end
