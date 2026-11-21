import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalyticProof
import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserAlongAStep
import YangMills.Construction.Towers.NormalisersOfTheCriticalBranch
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctionsProof
import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.AnalyticNearIdentity
open YangMills.Construction YangMills.Construction.Tower YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
variable {L n k j j' : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (U : Set (Edge L n k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ↔
      U ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) U := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem isOpenFieldSet_inter (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {U₁ U₂ : Set (Edge L n k j → ComplexMatrix2)} (h₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U₁)
    (h₂ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U₂) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (U₁ ∩ U₂) := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.isOpenFieldSet_inter <;> assumption
theorem isAnalyticFieldFunction_congr {U : Set (Edge L n k j → ComplexMatrix2)}
    {F G : (Edge L n k j → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction U F) (e : EqOn F G U) :
    IsAnalyticFieldFunction U G := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_congr <;> assumption
theorem isAnalyticFieldFunction_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {U U' : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction U F) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup U')
    (hsub : U' ⊆ U) : IsAnalyticFieldFunction U' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem isAnalyticFieldFunction_add (H : LocalAnalyticity.LocalAnalyticityStatement)
    {U : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction U F₁) (h₂ : IsAnalyticFieldFunction U F₂) :
    IsAnalyticFieldFunction U fun V => F₁ V + F₂ V := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_add <;> assumption
theorem isAnalyticFieldFunction_comp (H : AnalyticCalculus.AnalyticCalculusStatement)
    {U : Set (Edge L n k j → ComplexMatrix2)} {D : Set (Edge L n k j' → ComplexMatrix2)}
    {f : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {G : (Edge L n k j' → ComplexMatrix2) → ℝ}
    (hf : IsAnalyticFieldMap U f) (hG : IsAnalyticFieldFunction D G) :
    IsAnalyticFieldFunction (U ∩ f ⁻¹' D) (G ∘ f) := by apply _root_.YangMills.Construction.Tower.AnalyticFieldFunctions.analytic_comp_map <;> assumption
theorem exists_analytic_of_eventually_eq (hE : BondSetFields.ProductStructureHolds)
    (H : LocalAnalyticity.LocalAnalyticityStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {U₀ : Set (Edge L n k j → ComplexMatrix2)}
    {F Ψ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h : IsOpenNhdOfOne U₀) (hF : IsAnalyticFieldFunction U₀ F)
    (hne : EventuallyNearIdentity (fieldSpace L n k j) fun W => Ψ W = F W) :
    ∃ U : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne U ∧ IsAnalyticFieldFunction U Ψ := by
  have hop := isOpenFieldSet_iff (n := n) (k := k) (j := j) hE hL hn hj
  obtain ⟨-, O₀, hO₀, e₀⟩ := (hop U₀).1 h.1
  have hne' : {W | Ψ W = F W} ∈ 𝓝[fieldSpace L n k j] (trivialField L n k j) := hne
  obtain ⟨O, hO, h1O, hOs⟩ := mem_nhdsWithin.1 hne'
  have hU : IsOpenFieldSet PeriodicLattice.compactGaugeGroup ((O ∩ O₀) ∩ fieldSpace L n k j) :=
    (hop _).2 ⟨inter_subset_right, O ∩ O₀, hO.inter hO₀, rfl⟩
  have hsub : (O ∩ O₀) ∩ fieldSpace L n k j ⊆ U₀ := fun V hV => by
    rw [e₀]
    exact ⟨hV.1.2, hV.2⟩
  have h2 : trivialField L n k j ∈ O₀ ∩ fieldSpace L n k j := by
    rw [← e₀]
    exact h.2
  refine ⟨_, ⟨hU, ⟨⟨h1O, h2.1⟩, h2.2⟩⟩, isAnalyticFieldFunction_congr
    (isAnalyticFieldFunction_mono H hF hU hsub) fun V hV => ?_⟩
  exact (hOs ⟨hV.1.1, hV.2⟩).symm
theorem logLevelNormaliserRatio_analytic (H : ScalingNearTrivialField)
    (h : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) (hn : 0 < n)
    {U' : Set (Edge L (scaledExponent n (k + 1 + 1) (k + 1)) (k + 1) (k + 1) → ComplexMatrix2)}
    (hU : IsOpenNhdOfOne U')
    (hA : IsAnalyticFieldFunction U'
      (logTotalNormaliserRatio L (scaledExponent n (k + 1 + 1) (k + 1)) (k + 1))) :
    ∃ D : Set (Edge L n (k + 1 + 1) (k + 1) → ComplexMatrix2), IsOpenNhdOfOne D ∧
      IsAnalyticFieldFunction D (logLevelNormaliserRatio hL (Nat.le_succ (k + 1))) := by
  obtain ⟨hc, ho, hr⟩ := H L n (k + 1 + 1) (k + 1) (k + 1) (k + 1) hL (Nat.le_succ (k + 1)) h hn
    le_rfl le_rfl
  have himg : transportTotal (scaleEdge (n := n) hL (Nat.le_succ (k + 1)) (k + 1)) ''
      (fieldSpace L n (k + 1 + 1) (k + 1) ∩
        transportTotal (scaleEdge (n := n) hL (Nat.le_succ (k + 1)) (k + 1)) ⁻¹' U') = U' := by
    ext V
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact hW.2
    · intro hV
      obtain ⟨W, hW, rfl⟩ := hc.1.2.2 (hU.1.1 hV)
      exact ⟨W, ⟨hW, hV⟩, rfl⟩
  have hD : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (fieldSpace L n (k + 1 + 1) (k + 1) ∩
      transportTotal (scaleEdge (n := n) hL (Nat.le_succ (k + 1)) (k + 1)) ⁻¹' U') :=
    (ho.2.1 _ inter_subset_left).2 (by rw [himg]; exact hU.1)
  have hone : trivialField L n (k + 1 + 1) (k + 1) ∈ fieldSpace L n (k + 1 + 1) (k + 1) := by
    obtain ⟨W, hW, hWe⟩ := hc.1.2.2 (hU.1.1 hU.2)
    have : W = trivialField L n (k + 1 + 1) (k + 1) := by
      funext b
      have := congrFun hWe (scaleEdge (n := n) hL (Nat.le_succ (k + 1)) (k + 1) b)
      simpa [transportTotal] using this
    exact this ▸ hW
  have hval : transportTotalScalar (scaleEdge (n := n) hL (Nat.le_succ (k + 1)) (k + 1))
      (logLevelNormaliserRatio hL (Nat.le_succ (k + 1))) =
      logTotalNormaliserRatio L (scaledExponent n (k + 1 + 1) (k + 1)) (k + 1) := by
    funext F
    change logTotalNormaliserRatio L _ (k + 1) (transportTotal _ (F ∘ _)) = _
    congr 1
    funext b
    simp [transportTotal]
  refine ⟨_, ⟨hD, hone, ?_⟩, ((hr _ hD).1 _).2 ?_⟩
  · change transportTotal _ _ ∈ U'
    rw [hc.2.1]
    exact hU.2
  · rw [himg, hval]
    exact hA
end YangMills.Construction.Tower.AnalyticNearIdentity
namespace YangMills.Construction.Tower
open AnalyticNearIdentity in
theorem logTotalNormaliserAnalytic_holds
    (h₁ : LogTotalNormaliserStep.Statement)
    (h₂ : NormalisersHold)
    (h₃ : CriticalBranchExists)
    (h₄ : ScalingNearTrivialField)
    (h₅ : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement)
    (h₆ : Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.LocalAnalyticityStatement)
    (h₇ : BondSetFields.ProductStructureHolds) :
    LogTotalNormaliserAnalytic := by
  intro L n k hL hn
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  induction k generalizing n with
  | zero =>
    obtain ⟨U₀, ho, ha⟩ := (h₂ L n 1 hL hn 0 le_rfl).logRatio_analytic
    refine exists_analytic_of_eventually_eq h₇ h₆ hL hn le_rfl ho ha ?_
    filter_upwards [h₁ L n 0 hL hn hL0] with W hW
    rw [hW.2.2]
    simp [logLevelNormaliserRatio, logTotalNormaliserRatio]
  | succ k ih =>
    obtain ⟨U', ho', ha'⟩ := ih (scaledExponent n (k + 1 + 1) (k + 1))
      (by simp only [scaledExponent]; omega)
    obtain ⟨D, hD, hG⟩ := logLevelNormaliserRatio_analytic h₄ hL hL0 hn ho' ha'
    have hb : (chosenCriticalBranch L n (k + 1 + 1)).IsCritical :=
      Classical.epsilon_spec (h₃ L n (k + 1 + 1) hL hn)
    obtain ⟨Up, hop, hap⟩ := hb.analytic_prolong (k + 1) (Nat.lt_succ_self _)
    have hone := hb.prolong_trivial (k + 1) (Nat.lt_succ_self _)
    have hcomp := isAnalyticFieldFunction_comp h₅ hap hG
    obtain ⟨UΦ, hoΦ, haΦ⟩ := (h₂ L n (k + 1 + 1) hL hn (k + 1) le_rfl).logRatio_analytic
    have hinter := isOpenFieldSet_inter h₇ hL hn le_rfl hoΦ.1 hcomp.1
    have hsum := isAnalyticFieldFunction_add h₆
      (isAnalyticFieldFunction_mono h₆ haΦ hinter inter_subset_left)
      (isAnalyticFieldFunction_mono h₆ hcomp hinter inter_subset_right)
    have h1 : trivialField L n (k + 1 + 1) (k + 1 + 1) ∈ UΦ ∩
        (Up ∩ (chosenCriticalBranch L n (k + 1 + 1)).prolong (k + 1) ⁻¹' D) := by
      refine ⟨hoΦ.2, hop.2, ?_⟩
      change (chosenCriticalBranch L n (k + 1 + 1)).prolong (k + 1) _ ∈ D
      rw [hone]
      exact hD.2
    refine exists_analytic_of_eventually_eq h₇ h₆ hL hn le_rfl ⟨hinter, h1⟩ hsum ?_
    filter_upwards [h₁ L n (k + 1) hL hn hL0] with W hW
    exact hW.2.2
end YangMills.Construction.Tower
end
