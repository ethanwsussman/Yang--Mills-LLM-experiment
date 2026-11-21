import YangMills.Construction.Towers.PartialSumsOfTheGaugeFixingFunctionsProof
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOneProof
import YangMills.Construction.Towers.SmallNeighbourhoodsForThePartialSums
import YangMills.Construction.Towers.TheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
namespace PartialGaugedNhds
open Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
variable {L n k a b : ℕ}
theorem fieldOfPositiveValues_restrict {V : Edge L n k a → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k a) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem trivialField_mem_fieldSpace (j : ℕ) :
    trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
abbrev OpenFieldSetsAreRelative (L n k a : ℕ) : Prop :=
  ∀ 𝒰 : Set (Edge L n k a → ComplexMatrix2), IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
    𝒰 ⊆ fieldSpace L n k a ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k a) 𝒰
theorem openFieldSetsAreRelative (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (ha : a ≤ k) :
    OpenFieldSetsAreRelative L n k a := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem exists_openNhd_of_eventually (hop : OpenFieldSetsAreRelative L n k a)
    {P : (Edge L n k a → ComplexMatrix2) → Prop} (hP : EventuallyNearIdentity (fieldSpace L n k a) P) :
    ∃ 𝒰 : Set (Edge L n k a → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ ∀ V ∈ 𝒰, P V := by apply _root_.YangMills.Construction.Tower.PartialGaugedActionProof.exists_isOpenNhdOfOne_of_eventually <;> assumption
theorem isOpenNhdOfOne_inter (hop : OpenFieldSetsAreRelative L n k a)
    {𝒰₁ 𝒰₂ : Set (Edge L n k a → ComplexMatrix2)} (h₁ : IsOpenNhdOfOne 𝒰₁)
    (h₂ : IsOpenNhdOfOne 𝒰₂) : IsOpenNhdOfOne (𝒰₁ ∩ 𝒰₂) := by apply _root_.YangMills.Construction.Tower.PartialGaugedActionProof.isOpenNhdOfOne_inter <;> assumption
theorem isAnalyticFieldMap_mono (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldMap 𝒰' m := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.isAnalyticFieldMap_mono <;> assumption
theorem isAnalyticFieldFunction_mono (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k a → ComplexMatrix2)} {F : (Edge L n k a → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldFunction 𝒰' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem isAnalyticFieldFunction_add (hS : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)} {F₁ F₂ : (Edge L n k a → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction 𝒰 F₁) (h₂ : IsAnalyticFieldFunction 𝒰 F₂) :
    IsAnalyticFieldFunction 𝒰 fun V => F₁ V + F₂ V := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_add <;> assumption
theorem isAnalyticFieldFunction_congr {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {F F' : (Edge L n k a → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction 𝒰 F)
    (hFF : EqOn F F' 𝒰) : IsAnalyticFieldFunction 𝒰 F' := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_congr <;> assumption
theorem isSubspaceAnalyticToCoords_congr {S R : Type} [Fintype S] [Fintype R] {l : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l} (h𝒲 : 𝒲 = 𝒲')
    (hfg : EqOn f g 𝒲) (hf : IsSubspaceAnalyticToCoords E 𝒲 f) :
    IsSubspaceAnalyticToCoords E 𝒲' g := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isSubspaceAnalyticToCoords_congr <;> assumption
theorem continuousOn_of_isAnalyticFieldMap (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem isOpenNhdOfOne_inter_preimage (hK : AnalyticCalculus.AnalyticCalculusStatement)
    (hopa : OpenFieldSetsAreRelative L n k a) (hopb : OpenFieldSetsAreRelative L n k b)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2} (h₁ : IsOpenNhdOfOne 𝒰₁)
    (hm : IsAnalyticFieldMap 𝒰₁ m) (hone : m (trivialField L n k a) = trivialField L n k b)
    (h₂ : IsOpenNhdOfOne 𝒰₂) : IsOpenNhdOfOne (𝒰₁ ∩ m ⁻¹' 𝒰₂) := by apply _root_.YangMills.Construction.Tower.PartialGaugedActionProof.isOpenNhdOfOne_compositeDomain <;> assumption
theorem isAnalyticFieldFunction_comp (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰₁ : Set (Edge L n k a → ComplexMatrix2)} {𝒰₂ : Set (Edge L n k b → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    {g : (Edge L n k b → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldMap 𝒰₁ m) (h₂ : IsAnalyticFieldFunction 𝒰₂ g)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ m ⁻¹' 𝒰₂)) :
    IsAnalyticFieldFunction (𝒰₁ ∩ m ⁻¹' 𝒰₂) (g ∘ m) := by apply _root_.YangMills.Construction.Tower.PartialGaugedActionProof.isAnalyticFieldFunction_comp <;> assumption
structure Hypotheses : Prop where
  criticalBranch : CriticalBranchExists
  smoothingFibres : SmoothingFibres
  axialFacts : AxialFunctionFacts.statement
  productStructure : BondSetFields.ProductStructureHolds
  calculus : AnalyticCalculus.AnalyticCalculusStatement
  localAnalyticity : LocalAnalyticity.LocalAnalyticityStatement
theorem smoothingIter_trivialField (Y : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ j, j ≤ k → smoothingIter L n k j (trivialField L n k 0) = trivialField L n k j
  | 0, _ => rfl
  | j + 1, h => by
    change smoothingStep L n k j (smoothingIter L n k j _) = _
    rw [smoothingIter_trivialField Y hL hn j (by omega)]
    exact (Y.axialFacts L n k j hL hn (by omega)).smoothingStep_trivial
theorem analytic_axial_comp_smoothingIter (Y : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j < k → ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldFunction 𝒰 fun U => axialFunction L n k j (smoothingIter L n k j U)
  | 0, h => by
    obtain ⟨𝒰, h1, -, h2⟩ := (Y.axialFacts L n k 0 hL hn h).analytic_near_identity
    exact ⟨𝒰, h1, h2⟩
  | j + 1, h => by
    obtain ⟨𝒰g, hg1, -, hg3⟩ := (Y.axialFacts L n k (j + 1) hL hn h).analytic_near_identity
    obtain ⟨-, -, -, -, ⟨𝒰m, hm1, -, hm3, -⟩, -, -⟩ := Y.smoothingFibres L n k j hL hn (by omega)
    have hd := isOpenNhdOfOne_inter_preimage Y.calculus
      (openFieldSetsAreRelative Y.productStructure hL hn (Nat.zero_le k))
      (openFieldSetsAreRelative Y.productStructure hL hn h.le) hm1 hm3
      (smoothingIter_trivialField Y hL hn (j + 1) h.le) hg1
    exact ⟨_, hd, isAnalyticFieldFunction_comp Y.calculus hm3 hg3 hd.1⟩
theorem analytic_partialGaugedActions (Y : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      ∀ i ≤ j, IsAnalyticFieldFunction 𝒰 (partialGaugedAction L n k i)
  | 0, _ => by
    obtain ⟨b, hb⟩ := Y.criticalBranch L n k hL hn
    have hop := openFieldSetsAreRelative (k := k) (a := 0) Y.productStructure hL hn (Nat.zero_le k)
    obtain ⟨𝒰s, hs1, hs2⟩ := hb.analytic_energy 0 (Nat.zero_le k)
    obtain ⟨𝒵, h𝒵, hz⟩ := exists_openNhd_of_eventually hop hb.energy_bottom
    have h𝒲 := isOpenNhdOfOne_inter hop hs1 h𝒵
    refine ⟨_, h𝒲, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    exact isAnalyticFieldFunction_congr
      (isAnalyticFieldFunction_mono Y.localAnalyticity hs2 h𝒲.1 inter_subset_left)
      fun V hV => hz V hV.2
  | j + 1, h => by
    have hop := openFieldSetsAreRelative (k := k) (a := 0) Y.productStructure hL hn (Nat.zero_le k)
    obtain ⟨𝒰F, hF1, hF2⟩ := analytic_partialGaugedActions Y hL hn j (by omega)
    obtain ⟨𝒰g, hg1, hg2⟩ := analytic_axial_comp_smoothingIter (k := k) Y hL hn j (by omega)
    have h𝒲 := isOpenNhdOfOne_inter hop hF1 hg1
    refine ⟨_, h𝒲, fun i hi => ?_⟩
    rcases Nat.lt_or_ge j i with hj | hj
    · obtain rfl : i = j + 1 := by omega
      exact isAnalyticFieldFunction_add Y.localAnalyticity
        (isAnalyticFieldFunction_mono Y.localAnalyticity (hF2 j le_rfl) h𝒲.1 inter_subset_left)
        (isAnalyticFieldFunction_mono Y.localAnalyticity hg2 h𝒲.1 inter_subset_right)
    · exact isAnalyticFieldFunction_mono Y.localAnalyticity (hF2 i hj) h𝒲.1 inter_subset_left
end PartialGaugedNhds
open PartialGaugedNhds Matrices.GroupLieProduct.Subspaces in
theorem smallNhdsForPartialGaugedActions_holds (hBranch : CriticalBranchExists)
    (hFibres : SmoothingFibres)
    (hAxial : AxialFunctionFacts.statement)
    (hProduct : BondSetFields.ProductStructureHolds)
    (hCalculus : AnalyticCalculus.AnalyticCalculusStatement)
    (hLocal : LocalAnalyticity.LocalAnalyticityStatement) :
    SmallNhdsForPartialGaugedActions := by
  have Y : Hypotheses := ⟨hBranch, hFibres, hAxial, hProduct, hCalculus, hLocal⟩
  intro L n k hL hn hk 𝒰₀ h₀
  have hop := openFieldSetsAreRelative (k := k) (a := 0) hProduct hL hn (Nat.zero_le k)
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨𝒰F, hF1, hF2⟩ := analytic_partialGaugedActions (k := i + 1) Y hL hn (i + 1) le_rfl
  obtain ⟨-, -, -, -, ⟨𝒰m, hm1, -, hm3, hm4⟩, -, -⟩ := hFibres L n (i + 1) i hL hn (by omega)
  have h𝒳 := isOpenNhdOfOne_inter hop hF1 hm1
  have h𝒲 := isOpenNhdOfOne_inter hop h₀ h𝒳
  refine ⟨_, h𝒲, inter_subset_left, fun j hj => ?_, ?_, fun V hV => hm4 V hV.2.2⟩
  · exact isAnalyticFieldFunction_mono hLocal (hF2 j hj) h𝒲.1
      fun V hV => hV.2.1
  · exact isAnalyticFieldMap_mono hLocal hm3 h𝒲.1 fun V hV => hV.2.2
end Tower
end YangMills.Construction
end
