import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalytic
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsRealAnalyticNearOne
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.RealAnalyticMapsNearAConfiguration
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctions
import YangMills.Construction.Towers.TaylorCoefficientsInTheLeftChartAreRealAnalyticProof
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AlongBranchAnalyticity
open YangMills.Construction.Conventions
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.LocalAnalyticity
section Reindexing
variable {S R S' R' S'' R'' : Type} [Fintype S] [Fintype R]
theorem isRealAnalyticToProduct_reindex {E : Submodule ℝ (S → ComplexMatrix2)}
    {E' : Submodule ℝ (S' → ComplexMatrix2)}
    {E'' : Submodule ℝ (S'' → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2}
    (h : IsSubspaceAnalyticToProduct E E' 𝒲 f)
    (a : R'' → R') (c : S'' → S') (hE'' : E'' ≤ hermitianTracelessFunctions S'')
    (hm : ∀ q ∈ 𝒲, ofParts (fun r => f q (.inl (a r))) (fun s => f q (.inr (c s))) ∈
      subspaceTimesGroup E'' R'') :
    IsSubspaceAnalyticToProduct E E'' 𝒲
      fun q => ofParts (fun r => f q (.inl (a r))) (fun s => f q (.inr (c s))) := by
  obtain ⟨h1, -, -, h4⟩ := h
  refine ⟨h1, hE'', hm, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, ho, hs, Ψ, hΨ, hE⟩ := h4 p hp
  refine ⟨𝒳, hp𝒳, ho, hs,
    fun q => ofParts (fun r => Ψ q (.inl (a r))) (fun s => Ψ q (.inr (c s))),
    fun b => ⟨(hΨ b).1, fun i => (hΨ b).2.1 (a i), fun k => (hΨ b).2.2 (c k)⟩, fun q hq => ?_⟩
  have e := hE hq
  funext i
  rcases i with r | s
  · exact congrFun e (.inl (a r))
  · exact congrFun e (.inr (c s))
end Reindexing
theorem exists_orthonormal_expansion {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (c : InnerProductSpace.Core ℝ V) :
    ∃ (d : ℕ) (e : Fin d → V), ∀ x : V, x = ∑ a, c.inner x (e a) • e a := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  refine ⟨_, stdOrthonormalBasis ℝ V, fun x => ?_⟩
  refine ((stdOrthonormalBasis ℝ V).sum_repr' x).symm.trans (Finset.sum_congr rfl fun a _ => ?_)
  congr 1
  exact real_inner_comm _ _
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite {m : ℕ} {i : ℤ} (b : PeriodicLattice.Bond L m i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem edgeFormOfPositiveValues_restrict {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) :
    edgeFormOfPositiveValues (restrictToPositiveEdges B) = B := by
  funext b
  unfold edgeFormOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, restrictToPositiveEdges]
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [hb, hr, dite_false, dite_true, restrictToPositiveEdges]
    have := hB.2 b
    rw [this, neg_neg]
theorem restrict_mem_hermitianTraceless {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) :
    restrictToPositiveEdges B ∈ hermitianTracelessFunctions (PositiveEdge L n k j) := by apply _root_.YangMills.Construction.Tower.LeftChartTaylor.restrictToPositiveEdges_mem <;> assumption
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (𝒰 : Set (Edge L n k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) 𝒰 := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem isOpenFieldSet_inter (hE : BondSetFields.ProductStructureHolds)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰₁ 𝒰₂ : Set (Edge L n k j → ComplexMatrix2)}
    (h₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₁)
    (h₂ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₂) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ 𝒰₂) := by
  have hop := isOpenFieldSet_iff hE hL hn hj
  obtain ⟨-, O₁, hO₁, e₁⟩ := (hop 𝒰₁).1 h₁
  obtain ⟨-, O₂, hO₂, e₂⟩ := (hop 𝒰₂).1 h₂
  refine (hop _).2 ⟨fun V hV => ((hop 𝒰₁).1 h₁).1 hV.1, O₁ ∩ O₂, hO₁.inter hO₂, ?_⟩
  rw [e₁, e₂]
  ext V
  simp only [mem_inter_iff]
  tauto
theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k j)]
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k j) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by apply _root_.YangMills.SharedProofs.p979 <;> assumption
theorem isOpenFieldSet_of_isRelativelyOpen {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (hc : 𝒰 ⊆ fieldSpace L n k j)
    (h : ComplexMatrix2.IsRelativelyOpen
      (subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (PositiveEdge L n k j))
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰}) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 := by
  obtain ⟨O, hO, heq⟩ := h
  have hpt : Continuous fun w : PositiveEdge L n k j → ComplexMatrix2 =>
      (ofParts w Empty.elim : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) := by
    refine continuous_pi fun r => ?_
    rcases r with r | e
    · exact continuous_apply _
    · exact e.elim
  refine ⟨hc, _, hO.preimage hpt, ?_⟩
  ext w
  constructor
  · rintro ⟨V, hV, rfl⟩
    have h1 : (ofParts (restrictToPositiveEdges V) Empty.elim :
        PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) ∈
        {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      change fieldOfPositiveValues (restrictToPositiveEdges V) ∈ 𝒰
      rw [fieldOfPositiveValues_restrict (hc hV)]
      exact hV
    rw [heq] at h1
    exact ⟨h1.1, fun b => (hc hV).1 b.1 (mem_univ _)⟩
  · rintro ⟨h1, h2⟩
    have h3 : (ofParts w Empty.elim : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) ∈
        {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      rw [heq]
      exact ⟨h1, Subsingleton.elim _ _, h2⟩
    exact ⟨_, h3, restrict_fieldOfPositiveValues _⟩
theorem leftGradient_spec (hA : AnalyticMapsAlongCurves)
    (hP : diffAtZeroPathsStatement)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    [Finite (PositiveEdge L n k j)] {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {S : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hS : IsAnalyticFieldFunction 𝒰 S) {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ 𝒰) :
    IsLeftGradient (fieldSpace L n k j) (fun V => (S V : ℂ)) W
        (leftGradient (fieldSpace L n k j) (fun V => (S V : ℂ)) W) ∧
      ∀ B ∈ edgeFormSpace L n k j,
        edgeFormPairing (leftGradient (fieldSpace L n k j) (fun V => (S V : ℂ)) W) B =
          ((leftDeriv S W B : ℝ) : ℂ) := by
  obtain ⟨X, hX, hder⟩ := (hA L n k j j hL hn hj hj).2 𝒰 S hS W hW
  have hWc : W ∈ fieldSpace L n k j := hS.1.1 hW
  have hline : ∀ B ∈ edgeFormSpace L n k j,
      HasDerivAt (fun t : ℝ => S (PeriodicLattice.expTwist ((t : ℂ) • B) W))
        (edgeFormPairing X B).re 0 := by
    intro B hB
    obtain ⟨h₁, h₂, h₃⟩ := (hP L n k j hL hn hj).2.2 W hWc B hB
    have h := hder _ h₁ h₂
    rwa [h₃] at h
  have hreal : ∀ B ∈ edgeFormSpace L n k j,
      edgeFormPairing X B = (((edgeFormPairing X B).re : ℝ) : ℂ) := by
    intro B hB
    have h := hc ⟨X, hX⟩ ⟨B, hB⟩
    change edgeFormPairing X B = _ at h
    rw [h, Complex.ofReal_re]
  have hIs : IsLeftGradient (fieldSpace L n k j) (fun V => (S V : ℂ)) W X := by
    refine ⟨⟨fun b hb => (hX.1 b hb).2, hX.2⟩, fun _ => hX, fun B hB _ => ?_⟩
    rw [hreal B hB]
    exact (hline B hB).ofReal_comp.deriv.symm
  have hspec := Classical.epsilon_spec (⟨X, hIs⟩ : ∃ X, IsLeftGradient (fieldSpace L n k j)
    (fun V => (S V : ℂ)) W X)
  refine ⟨hspec, fun B hB => ?_⟩
  refine (hspec.2.2 B hB (Set.toFinite _)).trans ?_
  rw [← hIs.2.2 B hB (Set.toFinite _), hreal B hB]
  congr 1
  exact (hline B hB).deriv.symm
theorem finset_sum_analytic (hSm : AnalyticFieldFunctionsClosed)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {𝒰 : Set (Edge L n k k → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) {ι : Type} (s : Finset ι)
    (f : ι → (Edge L n k k → ComplexMatrix2) → ℝ) (h : ∀ i ∈ s, IsAnalyticFieldFunction 𝒰 (f i)) :
    IsAnalyticFieldFunction 𝒰 fun W => ∑ i ∈ s, f i W := by
  classical
  have hs := hSm L n k k k hL hn le_rfl le_rfl
  induction s using Finset.induction_on with
  | empty => simpa using hs.1 𝒰 0 h𝒰
  | insert a s ha ih =>
    have h₁ := h a (Finset.mem_insert_self _ _)
    have h₂ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using (hs.2.1 𝒰 _ _ h₁ h₂).1
theorem formValued_analytic (hK : AnalyticCalculusStatement)
    (hSm : AnalyticFieldFunctionsClosed)
    (hS : FiniteSideFormSpaces)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    [i₁ : Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k j)]
    {𝒰 : Set (Edge L n k k → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {g : (Edge L n k k → ComplexMatrix2) → Edge L n k j → ComplexMatrix2}
    (hg : ∀ W ∈ 𝒰, g W ∈ edgeFormSpace L n k j)
    (hB : ∀ B ∈ edgeFormSpace L n k j,
      IsAnalyticFieldFunction 𝒰 fun W => (edgeFormPairing (g W) B).re) :
    IsSubspaceAnalyticToProduct (R := PositiveEdge L n k k) (S := Empty) (R' := Empty)
      ⊥ (hermitianTracelessFunctions (PositiveEdge L n k j))
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰}
      fun q => ofParts Empty.elim
        (restrictToPositiveEdges (g (fieldOfPositiveValues (groupComponent q)))) := by
  obtain ⟨-, hfd, -, core, hcore⟩ := hS L n k j hL hn hj
  obtain ⟨d, e, he⟩ := exists_orthonormal_expansion core
  have : FiniteDimensional ℝ (hermitianTracelessFunctions (PositiveEdge L n k j)) :=
    (hK (PositiveEdge L n k j) Empty (PositiveEdge L n k j) Empty).1 _ le_rfl
  let bs := Module.finBasis ℝ (hermitianTracelessFunctions (PositiveEdge L n k j))
  let ρ : edgeFormSpace L n k j →ₗ[ℝ] hermitianTracelessFunctions (PositiveEdge L n k j) :=
    { toFun := fun X => ⟨restrictToPositiveEdges (X : Edge L n k j → ComplexMatrix2),
        restrict_mem_hermitianTraceless X.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let F : Fin (Module.finrank ℝ (hermitianTracelessFunctions (PositiveEdge L n k j))) →
      (Edge L n k k → ComplexMatrix2) → ℝ :=
    fun i W => ∑ a, (edgeFormPairing (g W) (e a : Edge L n k j → ComplexMatrix2)).re *
      bs.coord i (ρ (e a))
  have hs := hSm L n k k k hL hn le_rfl le_rfl
  have hF : ∀ i, IsAnalyticFieldFunction 𝒰 (F i) := fun i =>
    finset_sum_analytic hSm hL hn h𝒰 Finset.univ _ fun a _ =>
      (hs.2.1 𝒰 _ _ (hB _ (e a).2) (hs.1 𝒰 _ h𝒰)).2
  have hexp : ∀ W ∈ 𝒰, restrictToPositiveEdges (g W) =
      ∑ i, F i W • ((bs i : hermitianTracelessFunctions (PositiveEdge L n k j)) :
        PositiveEdge L n k j → ComplexMatrix2) := by
    intro W hW
    have hx : ∀ a, (edgeFormPairing (g W) (e a : Edge L n k j → ComplexMatrix2)).re =
        core.inner ⟨g W, hg W hW⟩ (e a) := by
      intro a
      have := hcore ⟨g W, hg W hW⟩ (e a)
      change edgeFormPairing (g W) _ = _ at this
      rw [this, Complex.ofReal_re]
    have h1 : ρ ⟨g W, hg W hW⟩ = ∑ i, F i W • bs i := by
      conv_lhs => rw [← bs.sum_repr (ρ ⟨g W, hg W hW⟩)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have h2 := congrArg (fun y => bs.coord i (ρ y)) (he ⟨g W, hg W hW⟩)
      simp only [map_sum, map_smul, smul_eq_mul] at h2
      simp only [F, hx]
      simpa using h2
    have h3 : restrictToPositiveEdges (g W) = ((∑ i, F i W • bs i :
        hermitianTracelessFunctions (PositiveEdge L n k j)) :
          PositiveEdge L n k j → ComplexMatrix2) :=
      congrArg Subtype.val h1
    rw [h3]
    simp
  have hbase := ((hK Empty (PositiveEdge L n k k) (PositiveEdge L n k j) Empty).2.2.2 ⊥
    (hermitianTracelessFunctions (PositiveEdge L n k j)) bot_le le_rfl).2.2.1 _
    (isOpenInSubspaceTimesGroup_of_isOpenFieldSet h𝒰)
  refine (hbase.2.2.2 _ bs _ (fun i p => F i (fieldOfPositiveValues (groupComponent p)))
    (fun p hp => hexp _ hp)).2 fun i => ?_
  obtain ⟨-, i₀, a⟩ := hF i
  obtain rfl := Subsingleton.elim i₀ i₁
  exact a
theorem prolongComp_trivial {b : CriticalBranchData L n k} (hb : b.IsCritical) :
    ∀ j ≤ k, b.prolongComp j (trivialField L n k j) = trivialField L n k 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    change b.prolongComp i (b.prolong i _) = _
    rw [hb.prolong_trivial i (by omega)]
    exact ih (by omega)
theorem prolongComp_analytic (hM : AnalyticNearField.CompositionAndExpTwist)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {b : CriticalBranchData L n k}
    (hb : b.IsCritical) (j : ℕ) (hj : 1 ≤ j) :
    j ≤ k → ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldMap 𝒰 (b.prolongComp j) := by
  induction j, hj using Nat.le_induction with
  | base => intro hk; exact hb.analytic_prolong 0 (by omega)
  | succ i hi ih =>
    intro hk
    obtain ⟨𝒰', h𝒰', ha'⟩ := ih (by omega)
    obtain ⟨𝒰, h𝒰, ha⟩ := hb.analytic_prolong i (by omega)
    have h := ((hM L n k (i + 1) i 0 hL hn hk (by omega) (by omega)).1 𝒰 𝒰' (b.prolong i) ha).2
      (b.prolongComp i) ha'
    refine ⟨_, ⟨h.1, h𝒰.2, ?_⟩, h.2⟩
    change b.prolong i _ ∈ 𝒰'
    rw [hb.prolong_trivial i (by omega)]
    exact h𝒰'.2
def branchPoint (L n k : ℕ) (W : Edge L n k k → ComplexMatrix2) : ProductPoint L n k :=
  ofParts (restrictToPositiveEdges (chosenProlongComp L n k k W))
    (Sum.elim
      (restrictToPositiveEdges (leftGradient (fieldSpace L n k 0)
        (fun U => (plaquetteAction L n k U : ℂ)) (chosenProlongComp L n k k W)))
      (restrictToPositiveEdges ((chosenCriticalBranch L n k).energyGradient k W)))
theorem exists_analytic_at_side (hFun : BackgroundFunctionalAnalyticNearIdentityAtEverySide)
    (hFix : ChosenBranchIsCritical)
    (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves)
    (hE : BondSetFields.ProductStructureHolds)
    (hT : LeftChartTaylorCoefficientsAnalytic)
    (hW : WilsonActionAnalytic)
    (hSm : AnalyticFieldFunctionsClosed)
    (hM : AnalyticNearField.CompositionAndExpTwist)
    (hK : AnalyticCalculusStatement)
    (hR : LocalAnalyticityStatement)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    [i₀ : Fintype (PositiveEdge L n k 0)] [i₁ : Fintype (PositiveEdge L n k k)] :
    ∃ (𝒰 : Set (Edge L n k k → ComplexMatrix2)) (f : (Edge L n k k → ComplexMatrix2) → ℝ),
      IsOpenNhdOfOne 𝒰 ∧ IsAnalyticFieldFunction 𝒰 f ∧
        (∀ W ∈ 𝒰, ∃ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
          (J : Edge L n k 0 → ComplexMatrix2) =
              leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
                (chosenProlongComp L n k k W) ∧
            (μ : Edge L n k k → ComplexMatrix2) = (chosenCriticalBranch L n k).energyGradient k W ∧
            BackgroundFunctionalWellDefined (chosenProlongComp L n k k W) J μ ∧
            f W = backgroundFunctional (chosenProlongComp L n k k W) J μ) ∧
        f (trivialField L n k k) = backgroundFunctional (trivialField L n k 0) 0 0 := by
  have hb : (chosenCriticalBranch L n k).IsCritical := (hFix L n k hL hn).1
  obtain ⟨𝒰c, h𝒰c, hc⟩ := prolongComp_analytic hM hL hn hb k hk le_rfl
  obtain ⟨𝒰s, h𝒰s, hs⟩ := hb.analytic_energy k le_rfl
  obtain ⟨-, -, -, core₀, hcore₀⟩ := hS L n k 0 hL hn (Nat.zero_le k)
  obtain ⟨-, -, -, core₁, hcore₁⟩ := hS L n k k hL hn le_rfl
  have hAct := hW L n k hL hn
  have hcf : ∀ W ∈ 𝒰c, chosenProlongComp L n k k W ∈ fieldSpace L n k 0 :=
    fun W h => hc.2.1 h
  have h𝒰₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰c ∩ 𝒰s) :=
    isOpenFieldSet_inter hE hL hn le_rfl h𝒰c.1 h𝒰s.1
  have hgA : ∀ W ∈ 𝒰c ∩ 𝒰s, leftGradient (fieldSpace L n k 0)
      (fun U => (plaquetteAction L n k U : ℂ)) (chosenProlongComp L n k k W) ∈
        edgeFormSpace L n k 0 := fun W h =>
    (leftGradient_spec hA hP hL hn (Nat.zero_le k) hcore₀ hAct (hcf W h.1)).1.2.1
      fun V _ => Complex.ofReal_im _
  have hgS : ∀ W ∈ 𝒰c ∩ 𝒰s, (chosenCriticalBranch L n k).energyGradient k W ∈
      edgeFormSpace L n k k :=
    fun W h => (leftGradient_spec hA hP hL hn le_rfl hcore₁ hs h.2).1.2.1
      fun V _ => Complex.ofReal_im _
  have hs₀ := hSm L n k k 0 hL hn le_rfl (Nat.zero_le k)
  have hs₁ := hSm L n k k k hL hn le_rfl le_rfl
  have hpA : ∀ B ∈ edgeFormSpace L n k 0, IsAnalyticFieldFunction (𝒰c ∩ 𝒰s) fun W =>
      (edgeFormPairing (leftGradient (fieldSpace L n k 0)
        (fun U => (plaquetteAction L n k U : ℂ)) (chosenProlongComp L n k k W)) B).re := by
    intro B hB
    have h₁ := ((hT L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k)).1 _ _ hAct B hB).1
    have h₂ := hs₀.2.2.2.2 𝒰c _ (chosenProlongComp L n k k) _ hc h₁
    have h₃ := hs₁.2.2.1 _ (𝒰c ∩ 𝒰s) _ h₂ h𝒰₁ fun W h => ⟨h.1, hcf W h.1⟩
    refine hs₁.2.2.2.1 _ _ _ h₃ fun W h => ?_
    have := (leftGradient_spec hA hP hL hn (Nat.zero_le k) hcore₀ hAct (hcf W h.1)).2 B hB
    simp only [this, Complex.ofReal_re, Function.comp]
  have hpS : ∀ B ∈ edgeFormSpace L n k k, IsAnalyticFieldFunction (𝒰c ∩ 𝒰s) fun W =>
      (edgeFormPairing ((chosenCriticalBranch L n k).energyGradient k W) B).re := by
    intro B hB
    have h₁ := ((hT L n k k k hL hn le_rfl le_rfl).1 _ _ hs B hB).1
    have h₃ := hs₁.2.2.1 _ (𝒰c ∩ 𝒰s) _ h₁ h𝒰₁ fun W h => h.2
    refine hs₁.2.2.2.1 _ _ _ h₃ fun W h => ?_
    have := (leftGradient_spec hA hP hL hn le_rfl hcore₁ hs h.2).2 B hB
    change leftDeriv _ W B = (edgeFormPairing (leftGradient _ _ W) B).re
    rw [this, Complex.ofReal_re]
  have hop₁ := isOpenInSubspaceTimesGroup_of_isOpenFieldSet h𝒰₁
  obtain ⟨-, -, j₀, j₁, hcan⟩ := hc
  obtain rfl := Subsingleton.elim i₁ j₀
  obtain rfl := Subsingleton.elim i₀ j₁
  have hr₁ := ((hR Empty (PositiveEdge L n k k) Empty (PositiveEdge L n k 0) ⊥ ⊥ bot_le bot_le _
    hcan.1).1 _ (fun q h => h.1) hop₁.2).2 _ hcan
  have h₂ := formValued_analytic hK hSm hS hL hn (Nat.zero_le k) h𝒰₁ hgA hpA
  have h₃ := formValued_analytic hK hSm hS hL hn le_rfl h𝒰₁ hgS hpS
  have hpairs :=
    ((hK Empty (PositiveEdge L n k k) Empty Empty).2.2.2 ⊥ ⊥ bot_le bot_le).2.2.1 _ hop₁
  have h₂₃ := hpairs.2.1 (PositiveEdge L n k 0) (PositiveEdge L n k k) Empty Empty _ _ _ _ h₂ h₃
  have h₁₂₃ := hpairs.2.1 Empty (PositiveEdge L n k 0 ⊕ PositiveEdge L n k k)
    (PositiveEdge L n k 0) (Empty ⊕ Empty) _ _ _ _ hr₁ h₂₃
  have hQm : ∀ W ∈ 𝒰c ∩ 𝒰s, branchPoint L n k W ∈
      subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k))
        (PositiveEdge L n k 0) := by
    intro W h
    refine ⟨?_, fun b => (hcf W h.1).1 b.1 (mem_univ _)⟩
    simp only [hermitianTracelessFunctions, Submodule.mem_pi]
    rintro (b | b) _
    · exact (hgA W h).1 b.1 b.2
    · exact (hgS W h).1 b.1 b.2
  have hq : IsSubspaceAnalyticToProduct (R := PositiveEdge L n k k) (S := Empty)
      (R' := PositiveEdge L n k 0) (S' := SourceEdge L n k) ⊥
      (hermitianTracelessFunctions (SourceEdge L n k))
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰c ∩ 𝒰s}
      fun q => branchPoint L n k (fieldOfPositiveValues (groupComponent q)) :=
    isRealAnalyticToProduct_reindex h₁₂₃ Sum.inl Sum.inr le_rfl fun q h => hQm _ h
  obtain ⟨j₂, j₃, 𝒲, h𝒲, hformed, hra⟩ := hFun L n k hL hn hk
  obtain rfl := Subsingleton.elim i₀ j₂
  obtain rfl := Subsingleton.elim i₁ j₃
  have hcomp := ((((hK Empty (PositiveEdge L n k k) (SourceEdge L n k)
    (PositiveEdge L n k 0)).2.2.2 ⊥ (hermitianTracelessFunctions (SourceEdge L n k)) bot_le
    le_rfl).2.2.1 _ hop₁).2.2.1 _ hq).2 𝒲 hra.1
  have hsub : {W | W ∈ 𝒰c ∩ 𝒰s ∧ branchPoint L n k W ∈ 𝒲} ⊆ fieldSpace L n k k :=
    fun W h => h𝒰₁.1 h.1
  have hop := isOpenFieldSet_of_isRelativelyOpen hsub hcomp.1
  have han : IsAnalyticFieldFunction {W | W ∈ 𝒰c ∩ 𝒰s ∧ branchPoint L n k W ∈ 𝒲}
      fun W => backgroundFunctionalAt (branchPoint L n k W) :=
    ⟨hop, i₁, hcomp.2.1 1 _ hra⟩
  have hclause : ∀ W ∈ {W | W ∈ 𝒰c ∩ 𝒰s ∧ branchPoint L n k W ∈ 𝒲},
      ∃ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
        (J : Edge L n k 0 → ComplexMatrix2) =
            leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
              (chosenProlongComp L n k k W) ∧
          (μ : Edge L n k k → ComplexMatrix2) = (chosenCriticalBranch L n k).energyGradient k W ∧
          BackgroundFunctionalWellDefined (chosenProlongComp L n k k W) J μ ∧
          backgroundFunctionalAt (branchPoint L n k W) =
            backgroundFunctional (chosenProlongComp L n k k W) J μ := by
    rintro W ⟨hW₁, hW₂⟩
    obtain ⟨J, μ, hJ, hμ, hf⟩ := hformed _ hW₂
    have e₁ : sourceOfProductPoint (branchPoint L n k W) =
        leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
          (chosenProlongComp L n k k W) :=
      edgeFormOfPositiveValues_restrict (hgA W hW₁)
    have e₂ : multiplierOfProductPoint (branchPoint L n k W) =
        (chosenCriticalBranch L n k).energyGradient k W :=
      edgeFormOfPositiveValues_restrict (hgS W hW₁)
    have e₃ : fieldOfProductPoint (branchPoint L n k W) = chosenProlongComp L n k k W :=
      fieldOfPositiveValues_restrict (hcf W hW₁.1)
    rw [e₃] at hf
    refine ⟨J, μ, hJ.trans e₁, hμ.trans e₂, hf, ?_⟩
    have hmem : sourceOfProductPoint (branchPoint L n k W) ∈ edgeFormSpace L n k 0 ∧
        multiplierOfProductPoint (branchPoint L n k W) ∈ edgeFormSpace L n k k :=
      ⟨hJ ▸ J.2, hμ ▸ μ.2⟩
    have eJ : (⟨_, hmem.1⟩ : edgeFormSpace L n k 0) = J := Subtype.ext hJ.symm
    have eμ : (⟨_, hmem.2⟩ : edgeFormSpace L n k k) = μ := Subtype.ext hμ.symm
    rw [backgroundFunctionalAt, dif_pos hmem, eJ, eμ, e₃]
  have hone : trivialField L n k k ∈ fieldSpace L n k k := h𝒰s.1.1 h𝒰s.2
  have hc₁ : chosenProlongComp L n k k (trivialField L n k k) = trivialField L n k 0 :=
    prolongComp_trivial hb k le_rfl
  have hgS₁ : (chosenCriticalBranch L n k).energyGradient k (trivialField L n k k) = 0 :=
    hb.gradient_trivial k le_rfl
  have hgA₁ : leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
      (chosenProlongComp L n k k (trivialField L n k k)) = 0 := by
    obtain ⟨-, -, g, hg, hgT⟩ :=
      Filter.Eventually.self_of_nhdsWithin (hb.prolongComp_section k le_rfl) hone
    have hg₀ : g = 0 := Subtype.ext (hg.trans hgS₁)
    rw [hg₀] at hgT
    exact hgT.symm.trans (congrArg Subtype.val (LinearMap.map_zero _))
  have hQ₁ : branchPoint L n k (trivialField L n k k) = identityProductPoint L n k := by
    unfold branchPoint identityProductPoint
    rw [hgA₁, hgS₁, hc₁]
    funext i
    rcases i with r | b | b <;> rfl
  have hmem₁ : trivialField L n k k ∈ {W | W ∈ 𝒰c ∩ 𝒰s ∧ branchPoint L n k W ∈ 𝒲} :=
    ⟨⟨h𝒰c.2, h𝒰s.2⟩, hQ₁ ▸ h𝒲⟩
  refine ⟨_, _, ⟨hop, hmem₁⟩, han, hclause, ?_⟩
  obtain ⟨J, μ, hJ, hμ, -, hv⟩ := hclause _ hmem₁
  have hJ₀ : J = 0 := Subtype.ext (hJ.trans hgA₁)
  have hμ₀ : μ = 0 := Subtype.ext (hμ.trans hgS₁)
  rw [hv, hJ₀, hμ₀, hc₁]
theorem backgroundFunctionalAlongBranchAnalytic_holds
    (hFun : BackgroundFunctionalAnalyticNearIdentityAtEverySide)
    (hFix : ChosenBranchIsCritical)
    (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves)
    (hE : BondSetFields.ProductStructureHolds)
    (hT : LeftChartTaylorCoefficientsAnalytic)
    (hW : WilsonActionAnalytic)
    (hSm : AnalyticFieldFunctionsClosed)
    (hM : AnalyticNearField.CompositionAndExpTwist)
    (hK : AnalyticCalculusStatement)
    (hR : LocalAnalyticityStatement) : BackgroundFunctionalAlongBranchAnalytic := by
  intro L n k hL hn hk
  have f₀ := (hS L n k 0 hL hn (Nat.zero_le k)).1
  have f₁ := (hS L n k k hL hn le_rfl).1
  letI := Fintype.ofFinite (PositiveEdge L n k 0)
  letI := Fintype.ofFinite (PositiveEdge L n k k)
  exact exists_analytic_at_side hFun hFix hS hP hA hE hT hW hSm hM hK hR hL hn hk
end YangMills.Construction.Tower.AlongBranchAnalyticity
