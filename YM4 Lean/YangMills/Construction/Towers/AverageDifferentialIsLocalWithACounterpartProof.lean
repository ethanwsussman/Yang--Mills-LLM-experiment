import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.AverageDifferentialIsLocalWithACounterpart
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.PeriodicExtensionsOfFunctionsOfCells
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurations
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.SmoothingDerivLocality
theorem fullSpace_positive_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem fullSpace_not_opposite_positive {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem periodic_opposite_opposite {L m : ℕ} {j : ℤ} (b : PeriodicLattice.Bond L m j) :
    b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem fullSpace_extendOddly_opposite {a : ℝ} (ha : 0 < a)
    (g : InfiniteLattice.Link a → Matrices.ComplexMatrix2) (b : InfiniteLattice.Link a) :
    Tower.FullSpace.extendOddly g b.opposite = -Tower.FullSpace.extendOddly g b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem eventually_defined_smul {β : Type} {Positive : β → Prop}
    {P : Submodule ℂ (β → Matrices.ComplexMatrix2)}
    {IsDefined : (β → Matrices.ComplexMatrix2) → Prop}
    {a v : (β → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hR : Tower.AsDifferentials.IsLocallyHolomorphicLog Positive P IsDefined a v)
    {B : β → Matrices.ComplexMatrix2} (hB : B ∈ P)
    (hpos : ∀ b, Positive b → B b ∈ Matrices.ComplexMatrix2.traceless) :
    ∀ᶠ t : ℂ in 𝓝 0, IsDefined (t • B) := by
  obtain ⟨F, O, h, hne, hF, h0, hhol, -, hall⟩ := hR
  obtain ⟨-, hopen⟩ := (hhol OneLoop.pauliBasis).1
  obtain ⟨s, hs, hball⟩ := hopen 0 h0
  have : Nonempty F := hne.to_subtype
  have hnn : ∀ b : F, 0 ≤ Matrices.ComplexMatrix2.operatorNorm (B b) := fun b => norm_nonneg _
  set M : ℝ := ∑ b : F, Matrices.ComplexMatrix2.operatorNorm (B b) + 1 with hMdef
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun (b : F) (_ : b ∈ Finset.univ) => hnn b
    linarith
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (div_pos hs hM)] with t ht
  have ht' : ‖t‖ * M < s := by
    have : ‖t‖ < s / M := by simpa using ht
    exact (lt_div_iff₀ hM).1 this
  have hmem : (fun b : F => (t • B) b) ∈ O := by
    refine hball _ (fun b => ?_) ?_
    · exact Matrices.ComplexMatrix2.traceless.smul_mem t (hpos _ (hF _ b.2))
    · have hle : ∀ b : F,
          Matrices.ComplexMatrix2.operatorNorm (((fun b : F => (t • B) b) - 0) b) ≤ ‖t‖ * M := by
        intro b
        have h1 : Matrices.ComplexMatrix2.operatorNorm (B b) ≤ M := by
          have := Finset.single_le_sum
            (f := fun b : F => Matrices.ComplexMatrix2.operatorNorm (B b))
            (fun b _ => hnn b) (Finset.mem_univ b)
          linarith
        have h2 : Matrices.ComplexMatrix2.operatorNorm (t • B b.1) ≤
            ‖t‖ * Matrices.ComplexMatrix2.operatorNorm (B b) := norm_smul_le _ _
        simpa using h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg t))
      exact (ciSup_le hle).trans_lt ht'
  exact (hall _ (P.smul_mem t hB) hmem).1
section Step
variable {L n k : ℕ}
theorem complexBlockAverage_of_positive {m : ℕ} {j j' : ℤ}
    (U : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {c : PeriodicLattice.Bond L m j} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage U c = PeriodicLattice.complexBlockAverageOnPositive U c :=
  if_pos hc
theorem complexSmoothing_eq_of_values (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (c : Tower.FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented)
    {W : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hW : W ∈ Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c)
    {T : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hT : ∀ b ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c,
      T (Tower.FullSpace.projEdge L n k j b) = W b) :
    Tower.FullSpace.complexSmoothing L W c =
      PeriodicLattice.complexBlockAverage T (Tower.FullSpace.projEdge L n k (j + 1) c) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have hρ := (h₆.1 L hL).2.2
  have hcfg := h₂ L hL0 hL k hk n hn j hj c hc
  have hsets := (h₃ L hL0 hL k hk n hn).2 j hj c hc
  have hdom := (hρ.fullSpace k j hj c hc).subset_complexDomain hW
  have hcpos : (Tower.FullSpace.projEdge L n k (j + 1) c).IsPositivelyOriented :=
    ((h₁ L n k (j + 1) hL hn hj).1 c).2.2.1 hc
  have hagree : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock
      (Tower.FullSpace.projEdge L n k (j + 1) c) : Set (Tower.Edge L n k j)),
      Tower.FullSpace.projField L n k j
          (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c) W b =
        T b := by
    intro b hb
    rw [← hsets.doubleCubeLinks_image] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    rw [(hcfg.projField_spec _ hW.1).1 b' hb', hT b' hb']
  have e₂ := (h₈ L n k j hL.1 hL.2 hn hj _ hcpos).average_eq _ _ hagree
  rw [hcfg.complexSmoothing_eq _ hdom, complexBlockAverage_of_positive _ hcpos,
    complexBlockAverage_of_positive _ hcpos, e₂]
theorem expTwist_lift (h₁ : Tower.EdgeProjectionProperties)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) {j : ℕ} (hj : j ≤ k)
    (ha : 0 < Tower.meshAt L k j) (B V : Tower.Edge L n k j → Matrices.ComplexMatrix2)
    (b : Tower.FullSpace.Edge L k j) :
    PeriodicLattice.expTwist B V (Tower.FullSpace.projEdge L n k j b) =
      Tower.FullSpace.expTwist (fun b => B (Tower.FullSpace.projEdge L n k j b))
        (liftGaugeField L n k j V) b := by
  have hq := h₁ L n k j hL hn hj
  rcases fullSpace_positive_or_opposite b with hb | hr
  · have hbq : (Tower.FullSpace.projEdge L n k j b).IsPositivelyOriented := (hq.1 b).2.2.1 hb
    simp only [PeriodicLattice.expTwist, Tower.FullSpace.expTwist, if_pos hb, if_pos hbq]
    rfl
  · have hb : ¬ b.IsPositivelyOriented := fun hb => fullSpace_not_opposite_positive ha hb hr
    have hrq : (Tower.FullSpace.projEdge L n k j b).opposite.IsPositivelyOriented := by
      rw [(hq.1 b).2.2.2]
      exact (hq.1 b.opposite).2.2.1 hr
    have hnq : ¬(Tower.FullSpace.projEdge L n k j b).IsPositivelyOriented := by
      rcases h₉ L n k hL hn hk j hj (Tower.FullSpace.projEdge L n k j b) with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hrq h
      · exact h
    simp only [PeriodicLattice.expTwist, Tower.FullSpace.expTwist, if_neg hb, if_neg hnq,
      (hq.1 b).2.2.2]
    rfl
theorem extendOddly_opposite (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) {j : ℕ} (hj : j ≤ k)
    (g : Tower.Edge L n k j → Matrices.ComplexMatrix2) (b : Tower.Edge L n k j) :
    Tower.extendOddly g b.opposite = -Tower.extendOddly g b := by
  simp only [Tower.extendOddly]
  rcases h₉ L n k hL hn hk j hj b with ⟨hb, hr⟩ | ⟨hr, hb⟩
  · rw [if_neg hr, if_pos hb, periodic_opposite_opposite]
  · rw [if_pos hr, if_neg hb, neg_neg]
theorem supNormVec_le_of_mem_doubleCube (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    (c : Tower.FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented)
    {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ Tower.FullSpace.doubleCube L (Tower.meshAt L k j) c) :
    TorusMetric.supNormVec (x - (c.initial : InfiniteLattice.AmbientSpace)) ≤
      3 * Tower.meshAt L k (j + 1) / 2 := by
  have hS := (hZ L hL k 1 (j + 1) hk (by omega) hj).2.2.2.2.2.1
  obtain ⟨ν, rfl, hν⟩ := hS.sites_near c hc x hx
  refine Finset.sup'_le _ _ fun ρ _ => ?_
  have e : (Tower.FullSpace.offsetPoint (Tower.meshAt L k (j + 1 - 1))
      (c.initial : InfiniteLattice.AmbientSpace) ν -
      (c.initial : InfiniteLattice.AmbientSpace)) ρ =
        (ν ρ : ℝ) * Tower.meshAt L k (j + 1 - 1) := by
    simp [Tower.FullSpace.offsetPoint, Finset.sum_apply, Pi.single_apply]
  rw [e]
  have := hν ρ
  linarith
theorem complexSmoothing_eq_of_agree (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (c : Tower.FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented)
    {W W' : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hW : W ∈ Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c)
    (hW' : W' ∈ Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c)
    (hag : ∀ b ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c, W b = W' b) :
    Tower.FullSpace.complexSmoothing L W c = Tower.FullSpace.complexSmoothing L W' c := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hcfg := h₂ L hL0 hL k (by omega) n hn j hj c hc
  have hT := (hcfg.projField_spec _ hW.1).1
  rw [complexSmoothing_eq_of_values (n := n) h₁ h₂ h₃ h₆ h₈ hL hn hj c hc hW hT,
    complexSmoothing_eq_of_values (n := n) h₁ h₂ h₃ h₆ h₈ hL hn hj c hc hW'
      (fun b hb => (hT b hb).trans (hag b hb))]
end Step
theorem smoothingDerivIsLocalWithCounterpart_holds (h₁ : Tower.EdgeProjectionProperties)
    (h₂ : Tower.FullSpace.ProjPreservesFieldsEverywhere)
    (h₃ : Tower.ProjectionCarriesSetsStatement)
    (h₆ : Tower.SmoothingNearIdentity)
    (h₈ : PeriodicLattice.ComplexAverageIsLocal)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hD : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hI : IterMeansOfLift.Claim)
    (hE : PeriodicLift.LiftProperties) : SmoothingDerivIsLocalWithCounterpart := by
  intro L hL k n hn U hU j h
  have hj : j < k := h
  have hk : 1 ≤ k := by omega
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨hiff, hblock⟩ := hI L hL k n hn hk U hU.1
  have hU' := hiff.1 hU
  have hfield := hblock hU j hj.le
  have hV := hU.2 j hj
  have hV' : liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U) ∈
      Tower.FullSpace.smallComplexFields L k j := by
    rw [← hfield]
    exact hU'.2 j hj
  have hS := ((hD L hL k hk).1 n hn).1 j hj _ hV U hU
  have hW := (hD L hL k hk).2.1 j hj _ hV' _ hU'
  have hext := hE L hL k n hn (Periodisation.CellClass.edgeClass k j hj.le)
  have ha : 0 < Tower.meshAt L k (j + 1) := by
    unfold Tower.meshAt
    positivity
  have ha0 : 0 < Tower.meshAt L k j := by
    unfold Tower.meshAt
    positivity
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    exact ⟨fun b hb => hW.mem_mean b hb f hf,
      fun b => by
        unfold Tower.FullSpace.complexSmoothingDeriv Tower.FullSpace.holLeftDifferential
        exact fullSpace_extendOddly_opposite ha _ b⟩
  · intro f hf g hg
    exact (hW.linear_mean f hf g hg 0).1
  · intro z f hf
    exact (hW.linear_mean f hf f hf z).2
  · intro f₀ hf₀ g₀ hg₀ c' hag
    let f : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2 := f₀
    let g : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2 := g₀
    have hf : f ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j) := hf₀
    have hg : g ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j) := hg₀
    have hf' : Tower.FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra f := hf
    have hg' : Tower.FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra g := hg
    let c : PeriodicOperators.PosEdge L k (j + 1) := c'
    have key : ∀ b : Tower.FullSpace.Edge L k j, b.IsPositivelyOriented →
        (b.initial : InfiniteLattice.AmbientSpace) ∈
          Tower.FullSpace.doubleCube L (Tower.meshAt L k j) c.1 →
        f b = g b := by
      intro b hp ht
      exact hag (show PeriodicOperators.PosEdge L k j from ⟨b, hp⟩)
        (supNormVec_le_of_mem_doubleCube hZ hL hk hj c.1 c.2 ht)
    have hpair : ∀ (t : ℂ), ∀ b ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c.1,
        Tower.FullSpace.expTwist (t • f) (liftGaugeField L n k j
          (PeriodicLattice.complexBlockFieldAtLevel j U)) b =
        Tower.FullSpace.expTwist (t • g) (liftGaugeField L n k j
          (PeriodicLattice.complexBlockFieldAtLevel j U)) b := by
      intro t b hb
      simp only [Tower.FullSpace.expTwist]
      by_cases hp : b.IsPositivelyOriented
      · have e : (t • f) b = (t • g) b := congrArg (t • ·) (key b hp hb.1)
        rw [if_pos hp, if_pos hp, e]
      · have hr := (fullSpace_positive_or_opposite b).resolve_left hp
        have e : (t • f) b.opposite = (t • g) b.opposite :=
          congrArg (t • ·) (key b.opposite hr hb.2)
        rw [if_neg hp, if_neg hp, e]
    have hev : (fun t : ℂ => Tower.FullSpace.AsDifferentials.meanLogRatio
          (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) c.1
          (t • f)) =ᶠ[𝓝 0]
        fun t : ℂ => Tower.FullSpace.AsDifferentials.meanLogRatio
          (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) c.1
          (t • g) := by
      filter_upwards [eventually_defined_smul (hW.local_mean c.1 c.2) hf hf'.1,
        eventually_defined_smul (hW.local_mean c.1 c.2) hg hg'.1] with t e₁ e₂
      simp only [Tower.FullSpace.AsDifferentials.meanLogRatio,
        Tower.FullSpace.AsDifferentials.meanRatio]
      rw [complexSmoothing_eq_of_agree (n := n) h₁ h₂ h₃ h₆ h₈ hL hn hj c.1 c.2 e₁ e₂ (hpair t)]
    exact ((hW.deriv_mean c.1 c.2 g hg).congr_of_eventuallyEq hev).unique
      (hW.deriv_mean c.1 c.2 f hf) |>.symm
  · intro f hf
    exact ⟨fun b hb => hS.mem_mean b hb f hf,
      fun b => by
        unfold Tower.complexSmoothingDeriv Tower.holLeftDifferential
        exact extendOddly_opposite h₉ hL hn (by omega) h _ b⟩
  · intro f hf g hg
    exact (hS.linear_mean f hf g hg 0).1
  · intro z f hf
    exact (hS.linear_mean f hf f hf z).2
  · intro f hf c'
    let c : PeriodicOperators.PosEdge L k (j + 1) := c'
    let fT : Tower.Edge L n k j → Matrices.ComplexMatrix2 := f
    let e : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2 :=
      fun b => fT (Tower.FullSpace.projEdge L n k j b)
    have hfT : fT ∈ Tower.complexEdgeForms L n k j := hf
    have hcq := ((h₁ L n k (j + 1) hL hn h).1 c.1).2.2.1 c.2
    have hx : e ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j) := hext.1 f hf
    have hx' : Tower.FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra e := hx
    have hquo : (projPositiveEdge L n k (j + 1) c).1 =
        Tower.FullSpace.projEdge L n k (j + 1) c.1 :=
      Classical.epsilon_spec (p := fun d : Tower.PositiveEdge L n k (j + 1) =>
        d.1 = Tower.FullSpace.projEdge L n k (j + 1) c.1) ⟨⟨_, hcq⟩, rfl⟩
    have hpoly : liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U) ∈
        Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c.1 :=
      ⟨⟨fun b _ => hV'.1.1 b, fun b _ => hV'.1.2 b⟩, fun b _ => hV'.2 b⟩
    have hev : (fun t : ℂ => Tower.FullSpace.AsDifferentials.meanLogRatio
          (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) c.1
          (t • e)) =ᶠ[𝓝 0]
        fun t : ℂ => Tower.AsDifferentials.meanLogRatio
          (PeriodicLattice.complexBlockFieldAtLevel j U)
          (Tower.FullSpace.projEdge L n k (j + 1) c.1) (t • fT) := by
      filter_upwards [eventually_defined_smul (hW.local_mean c.1 c.2) hx hx'.1] with t e₁
      have E₁ : Tower.FullSpace.complexSmoothing L (Tower.FullSpace.expTwist (t • e)
            (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U))) c.1 =
          PeriodicLattice.complexBlockAverage
            (PeriodicLattice.expTwist (t • fT) (PeriodicLattice.complexBlockFieldAtLevel j U))
            (Tower.FullSpace.projEdge L n k (j + 1) c.1) :=
        complexSmoothing_eq_of_values (n := n) h₁ h₂ h₃ h₆ h₈ hL hn hj c.1 c.2 e₁
          (fun b _ => expTwist_lift h₁ h₉ hL hn (by omega) hj.le ha0 _ _ b)
      have E₀ : Tower.FullSpace.complexSmoothing L
            (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)) c.1 =
          PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
            (Tower.FullSpace.projEdge L n k (j + 1) c.1) :=
        complexSmoothing_eq_of_values (n := n) h₁ h₂ h₃ h₆ h₈ hL hn hj c.1 c.2 hpoly
          (fun _ _ => rfl)
      simp only [Tower.FullSpace.AsDifferentials.meanLogRatio,
        Tower.FullSpace.AsDifferentials.meanRatio,
        Tower.AsDifferentials.meanLogRatio,
        Tower.AsDifferentials.meanRatio]
      rw [E₁, E₀]
    have eq := ((hS.deriv_mean _ hcq fT hfT).congr_of_eventuallyEq hev).unique
      (hW.deriv_mean c.1 c.2 e hx)
    show Tower.FullSpace.complexSmoothingDeriv _ e c.1 =
      Tower.complexSmoothingDeriv _ fT (projPositiveEdge L n k (j + 1) c).1
    rw [hquo, eq]
end YangMills.Construction.LocalKernels.SmoothingDerivLocality
end
