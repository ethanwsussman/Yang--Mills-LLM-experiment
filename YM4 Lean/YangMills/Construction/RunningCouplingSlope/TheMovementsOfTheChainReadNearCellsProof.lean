import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.RunningCouplingSlope.CellsOfABlockAreNearProof
import YangMills.Construction.RunningCouplingSlope.TheMovementAndTheDriftReadNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheMovementsOfTheChainReadNearCells
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Set Filter Metric
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace TransportLocality
open Matrices Tower PeriodicOperators TorusMetric
open Tower.LeftChartFields (CurveLogDerivative)
section Germs
variable {P X Y : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
private def AnalyticGerm (S : Set P) (p₀ : P) (g : P → X) : Prop :=
  ∃ H : P → X, AnalyticAt ℂ H p₀ ∧ ∀ᶠ p in 𝓝[S] p₀, g p = H p
variable {S : Set P} {p₀ : P} {g g' : P → X}
private theorem AnalyticGerm.congr (h : AnalyticGerm S p₀ g) (he : ∀ᶠ p in 𝓝[S] p₀, g p = g' p) :
    AnalyticGerm S p₀ g' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.congr_eventually <;> assumption
private theorem AnalyticGerm.const (x : X) : AnalyticGerm S p₀ fun _ => x := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.const <;> assumption
private theorem AnalyticGerm.add (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p + g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.add <;> assumption
private theorem AnalyticGerm.neg (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => -g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.neg <;> assumption
private theorem AnalyticGerm.sub (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p - g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sub <;> assumption
private theorem AnalyticGerm.clm (T : X →L[ℂ] Y) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => T (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.map_clm <;> assumption
private theorem AnalyticGerm.finset_sum {α : Type} (s : Finset α) {f : α → P → X}
    (h : ∀ a ∈ s, AnalyticGerm S p₀ (f a)) : AnalyticGerm S p₀ fun p => ∑ a ∈ s, f a p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sum <;> assumption
private theorem AnalyticGerm.value_eq (hp : p₀ ∈ S) {H : P → X} (hev : ∀ᶠ p in 𝓝[S] p₀, g p = H p) :
    g p₀ = H p₀ :=
  hev.self_of_nhdsWithin hp
private theorem AnalyticGerm.tendsto (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    Tendsto g (𝓝[S] p₀) (𝓝 (g p₀)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.tendsto_self <;> assumption
private theorem AnalyticGerm.comp (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) {f : X → Y}
    (hf : AnalyticAt ℂ f (g p₀)) : AnalyticGerm S p₀ fun p => f (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_analytic <;> assumption
private theorem AnalyticGerm.comp_family {τ : Type} [Fintype τ] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (hp : p₀ ∈ S)
    {Ψ : P → τ → E} (hΨ : ∀ i, AnalyticGerm S p₀ fun p => Ψ p i) {D : Set (τ → E)}
    (hD : ∀ᶠ p in 𝓝[S] p₀, Ψ p ∈ D) {φ : (τ → E) → Y} {G : (τ → E) → Y}
    (hG : AnalyticAt ℂ G (Ψ p₀)) (hGev : ∀ᶠ y in 𝓝[D] (Ψ p₀), φ y = G y) :
    AnalyticGerm S p₀ fun p => φ (Ψ p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_tuple <;> assumption
end Germs
section Scalars
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P}
private theorem AnalyticGerm.smul {f : P → ℂ} {g : P → X} (hf : AnalyticGerm S p₀ f)
    (hg : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => f p • g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.smul <;> assumption
private theorem AnalyticGerm.inv_scalar (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ≠ 0) : AnalyticGerm S p₀ fun p => (f p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.inv_complex <;> assumption
private theorem AnalyticGerm.root (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ∈ Complex.slitPlane) : AnalyticGerm S p₀ fun p => (f p) ^ (1 / 2 : ℂ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sqrt <;> assumption
end Scalars
section MatrixGerms
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
variable {S : Set P} {p₀ : P} {g g' : P → ComplexMatrix2}
private theorem AnalyticGerm.mul (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p * g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matMul <;> assumption
private def entryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)
private theorem AnalyticGerm.entry (h : AnalyticGerm S p₀ g) (r s : Fin 2) :
    AnalyticGerm S p₀ fun p => g p r s := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matEntry <;> assumption
private theorem AnalyticGerm.det (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => (g p).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.det <;> assumption
private def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] }
private theorem AnalyticGerm.inv (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) (h0 : (g p₀).det ≠ 0) :
    AnalyticGerm S p₀ fun p => (g p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matInv <;> assumption
private theorem AnalyticGerm.list_prod {α : Type} (V : P → α → ComplexMatrix2)
    (hV : ∀ a, AnalyticGerm S p₀ fun p => V p a)
    (l : List α) : AnalyticGerm S p₀ fun p => (l.map (V p)).prod := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.listProd <;> assumption
private theorem AnalyticGerm.exp (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => ComplexMatrix2.matExp (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matExp <;> assumption
end MatrixGerms
section Derivative
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {S : Set P} {p₀ : P} {g : P × ℂ → X}
private theorem eventually_curry_zero {q : P × ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ), q z) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ᶠ t in 𝓝 (0 : ℂ), q (p, t) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.eventually_curry_prod_zero <;> assumption
private theorem AnalyticGerm.along (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    ∀ᶠ p in 𝓝[S] p₀, DifferentiableAt ℂ (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.differentiable_slice <;> assumption
private theorem AnalyticGerm.deriv_zero (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => deriv (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.deriv_slice <;> assumption
end Derivative
section Pairs
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P} {g : P → X}
private theorem tendsto_fst_slice :
    Tendsto (Prod.fst : P × ℂ → P) (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) (𝓝[S] p₀) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_fst_prod_zero <;> assumption
private theorem tendsto_pair_zero : Tendsto (fun p : P => ((p, 0) : P × ℂ)) (𝓝[S] p₀)
    (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_pair_zero <;> assumption
private theorem AnalyticGerm.fst (h : AnalyticGerm S p₀ g) :
    AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => g z.1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_fst <;> assumption
private theorem analyticGerm_snd : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => z.2 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.analyticGerm_snd <;> assumption
private theorem AnalyticGerm.at_zero {g : P × ℂ → X}
    (h : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => g (p, 0) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.restrict_zero <;> assumption
end Pairs
private theorem mem_slitPlane_of_sqrt_near_one {z : ℂ} (h : ‖z ^ (1 / 2 : ℂ) - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.mem_slitPlane_of_sqrt_near_one <;> assumption
section TwistedFields
variable {L n k j : ℕ}
private theorem expTwist_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_mem_unitDeterminant (hE : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.traceless) : ComplexMatrix2.matExp Z ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p27134 <;> assumption
private theorem expTwist_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.expTwist_mem_fieldsIn <;> assumption
end TwistedFields
section Level
variable {L n k j : ℕ}
private theorem expTwist_zero {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (A : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • A) U = U := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.expTwist_zero_smul <;> assumption
private structure StepFacts (L n k j : ℕ) (r : ℝ) : Prop where
  bonds : Finite (Edge L n k j)
  sites : Finite (Vertex L n k j)
  xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  exp : ComplexMatrix2.ExpLogEstimates
  xor_next : ∀ b : Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  L_pos : 0 < L
  card : ∀ y : Vertex L n k (j + 1),
    Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)) = L ^ 4
  real_curves : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  near_unit : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented → ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2
  average_reads : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ W W' : Edge L n k j → ComplexMatrix2,
    (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), W b = W' b) →
      normalizedMean W c = normalizedMean W' c
  curves : ∀ s : ℝ, 0 < s → CurveLogDerivative ℂ (Metric.ball 0 s)
    PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  near_one : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  le_radius : r ≤ polydiscRadius L
  serve : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  reads : ∀ (y : Vertex L n k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) →
    ∀ W : Edge L n k j → ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W →
    (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < polydiscRadius L) →
    ∀ W' : Edge L n k j → ComplexMatrix2,
      (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) →
        PeriodicLattice.complexMeanContourHolonomy W' y x =
          PeriodicLattice.complexMeanContourHolonomy W y x
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
private structure RegularFamily (r : ℝ) (S : Set P) (p₀ : P) (V : P → Edge L n k j → ComplexMatrix2) :
    Prop where
  mem : p₀ ∈ S
  germ : ∀ b, AnalyticGerm S p₀ fun p => V p b
  conf : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  near : ∀ b, ComplexMatrix2.operatorNorm (V p₀ b - 1) < r
variable {V : P → Edge L n k j → ComplexMatrix2}
private theorem RegularFamily.self_conf (hV : RegularFamily r S p₀ V) :
    V p₀ ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  hV.conf.self_of_nhdsWithin hV.mem
private theorem RegularFamily.det_eq (hV : RegularFamily r S p₀ V) (b : Edge L n k j) :
    (V p₀ b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p₀) from
    hV.self_conf).1 b (mem_univ b)
private theorem RegularFamily.eventually_near (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < r := by
  have := T.bonds
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝[S] p₀) (𝓝 ‖V p₀ b - 1‖) :=
    (((hV.germ b).tendsto hV.mem).sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near b)
private theorem det_pathHolonomy {U : Edge L n k j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (l : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy U l).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.det_pathHolonomy <;> assumption
private theorem RegularFamily.holonomyGerm (hV : RegularFamily r S p₀ V) (l : List (Edge L n k j)) :
    AnalyticGerm S p₀ fun p => PeriodicLattice.pathHolonomy (V p) l :=
  AnalyticGerm.list_prod V hV.germ l
private theorem RegularFamily.contourHolonomyGerm (hV : RegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    AnalyticGerm S p₀ fun p => contourHolonomy (V p) c x π := by
  refine ((hV.holonomyGerm _).mul (hV.holonomyGerm _)).mul ((hV.holonomyGerm _).inv hV.mem ?_)
  rw [det_pathHolonomy hV.det_eq]
  exact one_ne_zero
private theorem RegularFamily.meanGerm (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) : AnalyticGerm S p₀ fun p => contourMean (V p) c := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold contourMean
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x _ =>
    AnalyticGerm.finset_sum _ fun π _ => hV.contourHolonomyGerm c x π)
private theorem RegularFamily.averageGerm (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    AnalyticGerm S p₀ (fun p => normalizedMean (V p) c) ∧
      ∀ᶠ p in 𝓝[S] p₀, normalizedMean (V p) c ∈ PeriodicLattice.complexGaugeGroup := by
  have hn := T.near_one _ hV.self_conf hV.near c hc
  have hm := hV.meanGerm T c
  have hs : (Matrix.det (contourMean (V p₀) c)) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hn.1
  have hl : AnalyticGerm S p₀ fun p => meanRadius (V p) c := hm.det.root hV.mem hs
  have hl0 : meanRadius (V p₀) c ≠ 0 := by
    intro h
    have := hn.1
    rw [h] at this
    norm_num at this
  refine ⟨(hl.inv_scalar hV.mem hl0).smul hm, ?_⟩
  filter_upwards [hV.conf, hV.eventually_near T] with p h₁ h₂
  exact (T.near_one _ h₁ h₂ c hc).2
private theorem extendFromPositive_agrees {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, W b.opposite = (W b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
private theorem RegularFamily.contour (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    AnalyticGerm S p₀ (fun p => PeriodicLattice.complexMeanContourHolonomy (V p) y x) ∧
      ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy (V p) y x ∈
        PeriodicLattice.complexGaugeGroup := by
  classical
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  set c := PeriodicLattice.Bond.forwardFrom y 0 with hcdef
  have hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hserve := T.serve c hc
  obtain ⟨inst, hol⟩ := (hserve.holomorphic_contourMean y hy x hx).1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hpoly : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r) →
        W ∈ nearIdentityPolydisc (polydiscRadius L) c := by
    intro W hW hn
    have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
    exact ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩,
      fun b _ => (hn b).trans_le T.le_radius⟩
  have hD : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p) ∈
      PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc (polydiscRadius L) c := by
    filter_upwards [hV.conf, hV.eventually_near T] with p h₁ h₂
    exact ⟨_, hpoly _ h₁ h₂, rfl⟩
  have h0 := hD.self_of_nhdsWithin hV.mem
  obtain ⟨G, hG, hGev⟩ := hol.2.2 _ h0
  have hfam := AnalyticGerm.comp_family hV.mem
    (Ψ := fun p => PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))
    (fun i => hV.germ i.1) hD hG hGev
  have hone := hfam.clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ())
  have hread : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))) y x =
      PeriodicLattice.complexMeanContourHolonomy (V p) y x := by
    filter_upwards [hV.conf, hV.eventually_near T] with p h₁ h₂
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p) := h₁
    exact T.reads y x hx c hc hy _ h₁' (fun b => (h₂ b).trans_le T.le_radius) _
      fun b hb => extendFromPositive_agrees hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
  refine ⟨hone.congr hread, ?_⟩
  filter_upwards [hD, hread] with p h₁ h₂
  have h := hol.2.1 h₁ ()
  rw [← h₂]
  exact h
end Level
section Motion
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
private theorem RegularFamily.expTwist (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) :
    RegularFamily r (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z => PeriodicLattice.expTwist (z.2 • B z.1) (V z.1) := by
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.mem, mem_univ _⟩
  have hval : ∀ b, AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z : P × ℂ => ComplexMatrix2.matExp (Complex.I • (z.2 • B z.1) b) * V z.1 b := fun b =>
    (AnalyticGerm.exp hmem ((AnalyticGerm.const Complex.I).smul
      (analyticGerm_snd.smul (hB b).fst))).mul (hV.germ b).fst
  refine ⟨hmem, fun b => ?_, ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun z => (expTwist_positive hb).symm)
    · refine ((hval b.opposite).inv hmem ?_).congr
        (Eventually.of_forall fun z => (expTwist_not_positive hb).symm)
      have h0 : ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) = 1 := by
        simp [ComplexMatrix2.matExp]
      show (ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) *
        V p₀ b.opposite).det ≠ 0
      rw [h0, one_mul, hV.det_eq]
      exact one_ne_zero
  · refine (tendsto_fst_slice.eventually (hV.conf.and hBf)).mono fun z h => ?_
    exact expTwist_mem T.exp T.xor (Submodule.smul_mem _ z.2 h.2) h.1
  · show ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist ((0 : ℂ) • B p₀) (V p₀) b - 1) < r
    rw [expTwist_zero hV.self_conf]
    exact hV.near b
private theorem RegularFamily.logDerivGerm (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ)
        (fun z => Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1))) ∧
      ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ),
        Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1)) ∈ PeriodicLattice.complexGaugeGroup) :
    AnalyticGerm S p₀ (fun p => Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p)) ∧
      ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) ∈
          ComplexMatrix2.traceless := by
  obtain ⟨hg, hgrp⟩ := hΦ
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.mem, mem_univ _⟩
  have hD := hg.deriv_zero
  have h0 := hg.at_zero
  have hdet : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det ≠ 0 := by
    have h : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det = 1 := hgrp.self_of_nhdsWithin hmem
    rw [h]
    exact one_ne_zero
  have hinv := h0.inv hV.mem hdet
  have hmain := (AnalyticGerm.const (S := S) (p₀ := p₀) Complex.I⁻¹).smul (hD.mul hinv)
  have hall : ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) =
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∧
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∈ ComplexMatrix2.traceless := by
    filter_upwards [eventually_curry_zero hgrp, hg.along, hV.conf] with p h₁ h₂ h₃
    obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.1 h₁
    have hc := T.curves s hs (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p)))
      (fun t ht => hball t ht) h₂
    obtain ⟨-, -, heq, hm⟩ := hc
    refine ⟨?_, hm⟩
    have e : Φ (V p) = Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)) := by
      rw [expTwist_zero h₃]
    rw [← heq, e]
    rfl
  refine ⟨hmain.congr (hall.mono fun p h => h.1.symm), hall.mono fun p h => ?_⟩
  rw [h.1]
  exact h.2
end Motion
section StepGerms
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
private theorem AnalyticGerm.extendOddly {f : P → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → AnalyticGerm S p₀ fun p => f p c)
    (c : Edge L n k j) :
    AnalyticGerm S p₀ fun p => Tower.extendOddly (f p) c := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.extendOddly <;> assumption
private theorem RegularFamily.meanDifferential (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => holLeftDifferential normalizedMean (V p) (B p) c := by
  refine AnalyticGerm.extendOddly (fun c hc => ?_) c
  exact (hV.logDerivGerm T (Φ := fun W => normalizedMean W c)
    ((hV.expTwist T hB hBf).averageGerm T hc)).1
private theorem RegularFamily.drift (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => contourLogDrift (V p) (B p) y := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold contourLogDrift
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x hx => ?_)
  have hx' := hfin.mem_toFinset.1 hx
  exact (hV.logDerivGerm T
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((hV.expTwist T hB hBf).contour T y hx')).1
private theorem AnalyticGerm.conjugateBy (hp : p₀ ∈ S) {g g' : P → ComplexMatrix2}
    (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g')
    (h0 : (g p₀).det ≠ 0) : AnalyticGerm S p₀ fun p => ComplexMatrix2.conjugateBy (g p) (g' p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.conjugateBy <;> assumption
private theorem RegularFamily.adjoint (T : StepFacts L n k j r) (hV : RegularFamily r S p₀ V)
    {l : P → Vertex L n k j → ComplexMatrix2} (hl : ∀ x, AnalyticGerm S p₀ fun p => l p x)
    (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => adjointCubeAverage (V p) (l p) y := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold adjointCubeAverage
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x hx => ?_)
  obtain ⟨h₁, h₂⟩ := hV.contour T y (hfin.mem_toFinset.1 hx)
  refine AnalyticGerm.conjugateBy hV.mem h₁ (hl x) ?_
  have h : (PeriodicLattice.complexMeanContourHolonomy (V p₀) y x).det = 1 :=
    h₂.self_of_nhdsWithin hV.mem
  rw [h]
  exact one_ne_zero
end StepGerms
private theorem conjugateBy_mem_traceless' {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
section OddForms
variable {L n k j : ℕ}
private theorem extendOddly_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
private theorem extendOddly_not_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_not_pos <;> assumption
private theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.StepMapsComplexLinear.extendOddly_mem <;> assumption
end OddForms
section Cells
variable {L n k : ℕ}
private theorem meshSize_le_one (hL : 1 ≤ (L : ℝ)) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) ≤ 1 := by
  simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
  exact zpow_le_one_of_nonpos₀ hL (by omega)
private theorem cellDist_le_of_near (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j j' : ℕ} (x : Vertex L n k j)
    (x' : Vertex L n k j') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) - (x' : PeriodicLattice.FourTorus L n)) μ‖ ≤ t) :
    cellDist (levelVertexCell x) (levelVertexCell x') ≤ 2 * (t + 1) := by apply _root_.YangMills.SharedProofs.p26872 <;> assumption
private theorem edge_ends_near (hL : 1 ≤ (L : ℝ)) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) (ν : Fin 4) :
    ‖((b.target : PeriodicLattice.FourTorus L n) - (b.source : PeriodicLattice.FourTorus L n)) ν‖ ≤ 1 := by
  have hη := meshSize_le_one (k := k) hL hj
  have hη0 : 0 ≤ PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) := by
    unfold PeriodicLattice.meshSize
    positivity
  have hstep : ∀ μ, ‖((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) :
        PeriodicLattice.FourTorus L n) ν‖ ≤ 1 := by
    intro μ
    by_cases h : ν = μ
    · subst h
      simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
      exact (addCircle_norm_coe_le_abs _).trans (by rwa [abs_of_nonneg hη0])
    · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · have e := congrArg (fun s : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j) =>
      (s : PeriodicLattice.FourTorus L n) ν) h
    simp only [AddSubgroup.coe_sub, Pi.sub_apply] at e ⊢
    rw [e]
    exact hstep μ
  · have e := congrArg (fun s : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j) =>
      (s : PeriodicLattice.FourTorus L n) ν) h
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg, Pi.sub_apply, Pi.neg_apply] at e ⊢
    rw [e, norm_neg]
    exact hstep μ
abbrev _root_.YangMills.SharedProofs.p39837 := @edge_ends_near
private theorem doubleBlock_source_near (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {b : Edge L n k j} (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) :
    cellDist (levelVertexCell b.source) (levelVertexCell c.source) ≤ 5 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hη := meshSize_le_one (k := k) hL1 (Nat.succ_le_of_lt hj)
  have blockNear : ∀ y : Vertex L n k (j + 1),
      (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y → ∀ μ,
      ‖((b.source : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ‖ ≤ 1 / 2 := by
    intro y hy μ
    have h := hy.1
    change torusSupNorm _ ≤ _ at h
    rw [SeparatedSequence.torusSupNorm_le_iff] at h
    have := h μ
    linarith
  have key : ∀ μ, ‖((b.source : PeriodicLattice.FourTorus L n) -
      (c.source : PeriodicLattice.FourTorus L n)) μ‖ ≤ 3 / 2 := by
    intro μ
    rcases hb.1 with h | h
    · have := blockNear _ h μ
      linarith
    · have h1 := blockNear _ h μ
      have h2 := edge_ends_near hL1 (Nat.succ_le_of_lt hj) c μ
      have e : ((b.source : PeriodicLattice.FourTorus L n) - (c.source : PeriodicLattice.FourTorus L n)) μ =
          ((b.source : PeriodicLattice.FourTorus L n) - (c.target : PeriodicLattice.FourTorus L n)) μ +
            ((c.target : PeriodicLattice.FourTorus L n) - (c.source : PeriodicLattice.FourTorus L n)) μ := by
        simp only [Pi.sub_apply]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      linarith
  have := cellDist_le_of_near hC hL b.source c.source (t := 3 / 2) (by norm_num) key
  linarith
abbrev _root_.YangMills.SharedProofs.p40516 := @doubleBlock_source_near
end Cells
section NearIdentity
private theorem norm_le_of_sub_one_le {A : ComplexMatrix2} (h : ‖A - 1‖ ≤ 1 / 2) : ‖A‖ ≤ 3 / 2 := by
  have := norm_add_le (A - 1) (1 : ComplexMatrix2)
  simp only [sub_add_cancel, norm_one] at this
  linarith
private theorem inv_sub_one_le {M : ComplexMatrix2} (hM : Matrix.det M = 1) (h : ‖M - 1‖ ≤ 1 / 2) :
    ‖M⁻¹ - 1‖ ≤ 2 * ‖M - 1‖ := by apply _root_.YangMills.SharedProofs.p71492 <;> assumption
private theorem norm_inv_le_two {M : ComplexMatrix2} (hM : Matrix.det M = 1) (h : ‖M - 1‖ ≤ 1 / 2) :
    ‖M⁻¹‖ ≤ 2 := by apply _root_.YangMills.SharedProofs.p24015 <;> assumption
private theorem mul_sub_one_le {A B : ComplexMatrix2} {s t : ℝ} (hA : ‖A - 1‖ ≤ s) (hB : ‖B - 1‖ ≤ t)
    (hB' : ‖B - 1‖ ≤ 1 / 2) : ‖A * B - 1‖ ≤ 3 / 2 * s + t := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by noncomm_ring
  have h2 : ‖B‖ ≤ 3 / 2 := norm_le_of_sub_one_le hB'
  have hs : 0 ≤ s := (norm_nonneg _).trans hA
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans ?_) hB)
  calc ‖A - 1‖ * ‖B‖ ≤ s * (3 / 2) := mul_le_mul hA h2 (norm_nonneg _) hs
    _ = 3 / 2 * s := by ring
abbrev _root_.YangMills.SharedProofs.p8624 := @mul_sub_one_le
private theorem norm_conjugateBy_le {A X : ComplexMatrix2} {a a' m : ℝ} (h : ‖A‖ ≤ a) (h' : ‖A⁻¹‖ ≤ a')
    (hX : ‖X‖ ≤ m) : ‖ComplexMatrix2.conjugateBy A X‖ ≤ a * m * a' := by
  have ha : 0 ≤ a := (norm_nonneg _).trans h
  have hm : 0 ≤ m := (norm_nonneg _).trans hX
  unfold ComplexMatrix2.conjugateBy
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul h hX (norm_nonneg _) ha)) h'
    (norm_nonneg _) (by positivity)
private theorem matExp_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Z : ComplexMatrix2, ‖Z‖ < δ → ‖ComplexMatrix2.matExp Z - 1‖ < ε := by apply _root_.YangMills.SharedProofs.p35343 <;> assumption
end NearIdentity
section OpenGerms
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
private theorem analyticAt_of_germ {S : Set P} {p : P} {g : P → X} (hS : IsOpen S) (hp : p ∈ S)
    (h : AnalyticGerm S p g) : AnalyticAt ℂ g p := by
  obtain ⟨H, hH, hev⟩ := h
  rw [hS.nhdsWithin_eq hp] at hev
  exact hH.congr (hev.mono fun _ h => h.symm)
private theorem germ_of_analyticAt {S : Set P} {p : P} {g : P → X} (h : AnalyticAt ℂ g p) :
    AnalyticGerm S p g :=
  ⟨g, h, Eventually.of_forall fun _ => rfl⟩
private theorem analyticGerm_id {S : Set ℂ} {p : ℂ} : AnalyticGerm S p fun t : ℂ => t :=
  ⟨fun t => t, analyticAt_id, Eventually.of_forall fun _ => rfl⟩
end OpenGerms
section Disc
variable {L n k j : ℕ} {r δ M : ℝ}
private structure DiscRadii (r δ : ℝ) : Prop where
  pos : 0 < r
  half : r ≤ 1 / 2
  dpos : 0 < δ
  exp : ∀ Z : ComplexMatrix2, ‖Z‖ < δ → ‖ComplexMatrix2.matExp Z - 1‖ < r / 8
private structure SmallPair (r M : ℝ) (V B : Edge L n k j → ComplexMatrix2) : Prop where
  conf : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  near : ∀ b, ‖V b - 1‖ ≤ r / 4
  form : B ∈ complexEdgeForms L n k j
  bound : ∀ b, ‖B b‖ ≤ M
private theorem SmallPair.det_eq {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B)
    (b : Edge L n k j) : (V b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V from h.conf).1 b
    (mem_univ b)
private theorem SmallPair.lt (R : DiscRadii r δ) {V B : Edge L n k j → ComplexMatrix2}
    (h : SmallPair r M V B) (b : Edge L n k j) : ComplexMatrix2.operatorNorm (V b - 1) < r := by
  have h₁ : ‖V b - 1‖ ≤ r / 4 := h.near b
  have h₂ := R.pos
  show ‖V b - 1‖ < r
  linarith
private theorem twisted_det (T : StepFacts L n k j r) {V B : Edge L n k j → ComplexMatrix2}
    (h : SmallPair r M V B) (t : ℂ) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    (ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b).det = 1 := by
  have hm : Complex.I • (t • B) b ∈ ComplexMatrix2.traceless := by
    show Complex.I • (t • B b) ∈ ComplexMatrix2.traceless
    exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ (h.form.1 b hb))
  have hd : (ComplexMatrix2.matExp (Complex.I • (t • B) b)).det = 1 :=
    matExp_mem_unitDeterminant T.exp hm
  rw [Matrix.det_mul, hd, h.det_eq, one_mul]
private theorem twisted_near (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) (δ / (M + 1))) (b : Edge L n k j) :
    ‖PeriodicLattice.expTwist (t • B) V b - 1‖ < r := by
  have hr := R.pos
  have hr2 := R.half
  have ht' : ‖t‖ * (M + 1) < δ := by
    have := mem_ball_zero_iff.1 ht
    rwa [lt_div_iff₀ (by linarith)] at this
  have hpos : ∀ b' : Edge L n k j,
      ‖ComplexMatrix2.matExp (Complex.I • (t • B) b') * V b' - 1‖ ≤ 7 * r / 16 := by
    intro b'
    have hZ : ‖Complex.I • (t • B) b'‖ < δ := by
      rw [Pi.smul_apply, norm_smul, norm_smul, Complex.norm_I, one_mul]
      have := mul_le_mul_of_nonneg_left (h.bound b') (norm_nonneg t)
      nlinarith [norm_nonneg t]
    have h1 := R.exp _ hZ
    have h2 := h.near b'
    have := mul_sub_one_le h1.le h2 (by linarith)
    linarith
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_positive hb]
    linarith [hpos b]
  · rw [expTwist_not_positive hb]
    have hr' := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
    have h1 := hpos b.opposite
    have := inv_sub_one_le (twisted_det T h t hr') (by linarith)
    linarith
private theorem twisted_conf (T : StepFacts L n k j r) {V B : Edge L n k j → ComplexMatrix2}
    (h : SmallPair r M V B) (t : ℂ) :
    PeriodicLattice.expTwist (t • B) V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  expTwist_mem T.exp T.xor (Submodule.smul_mem _ t h.form) h.conf
private theorem regularFamily_disc (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) {t₀ : ℂ}
    (ht : t₀ ∈ ball (0 : ℂ) (δ / (M + 1))) :
    RegularFamily r (ball (0 : ℂ) (δ / (M + 1))) t₀
      fun t => PeriodicLattice.expTwist (t • B) V := by
  have hval : ∀ b, AnalyticGerm (ball (0 : ℂ) (δ / (M + 1))) t₀
      fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b := fun b =>
    (AnalyticGerm.exp ht ((AnalyticGerm.const Complex.I).smul
      (analyticGerm_id.smul (AnalyticGerm.const (B b))))).mul (AnalyticGerm.const (V b))
  refine ⟨ht, fun b => ?_, ?_, fun b => twisted_near R T hM h ht b⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun z => (expTwist_positive hb).symm)
    · have hr' := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      refine ((hval b.opposite).inv ht ?_).congr
        (Eventually.of_forall fun z => (expTwist_not_positive hb).symm)
      rw [twisted_det T h t₀ hr']
      exact one_ne_zero
  · exact Eventually.of_forall fun t => twisted_conf T h t
private theorem differentiableOn_of_germs {s : ℝ} {g : ℂ → ComplexMatrix2}
    (h : ∀ t₀ ∈ ball (0 : ℂ) s, AnalyticGerm (ball (0 : ℂ) s) t₀ g) :
    DifferentiableOn ℂ g (ball (0 : ℂ) s) := fun t ht =>
  (analyticAt_of_germ isOpen_ball ht (h t ht)).differentiableAt.differentiableWithinAt
private theorem logDirectionalDeriv_facts (T : StepFacts L n k j r) {s : ℝ} (hs : 0 < s)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hg : ∀ t₀ ∈ ball (0 : ℂ) s, AnalyticGerm (ball (0 : ℂ) s) t₀
      fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B) V))
    (hgrp : ∀ t ∈ ball (0 : ℂ) s, Φ (PeriodicLattice.expTwist (t • B) V) ∈
      PeriodicLattice.complexGaugeGroup)
    (hn : ∀ t ∈ ball (0 : ℂ) s, ‖Φ (PeriodicLattice.expTwist (t • B) V) - 1‖ ≤ 1 / 2) :
    Tower.logDirectionalDeriv ℝ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
        Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B ∧
      Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B ∈
        ComplexMatrix2.traceless ∧
      ‖Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B‖ ≤
        6 / s := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ComplexMatrix2, g = fun t => Φ (PeriodicLattice.expTwist (t • B) V) :=
    ⟨_, rfl⟩
  have hz : (0 : ℂ) ∈ ball (0 : ℂ) s := mem_ball_self hs
  have h0 : g 0 = Φ V := by
    rw [hgdef]
    show Φ (PeriodicLattice.expTwist ((0 : ℂ) • B) V) = _
    rw [expTwist_zero hV]
  have hdiff : DifferentiableOn ℂ g (ball 0 s) := by
    rw [hgdef]
    exact differentiableOn_of_germs hg
  have hd0 : DifferentiableAt ℂ g 0 := hdiff.differentiableAt (ball_mem_nhds _ hs)
  have hgrp' : MapsTo g (ball 0 s) PeriodicLattice.complexGaugeGroup := by
    rw [hgdef]
    exact hgrp
  obtain ⟨-, -, heq, hm⟩ := T.curves s hs g hgrp' hd0
  have hI : IsOpenIntervalAroundZero (Set.Ioo (-s) s) :=
    ⟨isOpen_Ioo, Set.ordConnected_Ioo, by simp [hs]⟩
  have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have hreal : HasDerivAt (fun t : ℝ => g t) (deriv g 0) 0 := by
    have h₁ : HasDerivAt g (deriv g 0) (((0 : ℝ) : ℂ)) := by
      simpa using hd0.hasDerivAt
    have h₂ := HasDerivAt.scomp (0 : ℝ) h₁ hof
    rw [one_smul] at h₂
    exact h₂
  have hmaps : MapsTo (fun t : ℝ => g t) (Set.Ioo (-s) s) PeriodicLattice.complexGaugeGroup := by
    intro t ht
    refine hgrp' ?_
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ht
  obtain ⟨-, -, heqR, -⟩ := T.real_curves _ hI (fun t : ℝ => g t) hmaps hreal.differentiableAt
  have e₁ : Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
      Complex.I⁻¹ • (deriv g 0 * (g 0)⁻¹) := by
    rw [← heq, h0, hgdef]
    rfl
  have e₂ : Tower.logDirectionalDeriv ℝ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
      Complex.I⁻¹ • (deriv g 0 * (g 0)⁻¹) := by
    have hc0 : g ((0 : ℝ) : ℂ) = Φ V := by simpa using h0
    rw [hreal.deriv, hc0] at heqR
    rw [h0, ← heqR, hgdef]
    rfl
  refine ⟨by rw [e₁, e₂], by rw [e₁]; exact hm, ?_⟩
  have hc : ‖deriv g 0‖ ≤ (3 / 2) / (s / 2) := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hdiff.diffContOnCl_ball (closedBall_subset_ball (by linarith))) fun t ht => ?_
    have ht' : t ∈ ball (0 : ℂ) s := by
      rw [mem_sphere_zero_iff_norm] at ht
      rw [mem_ball_zero_iff, ht]
      linarith
    rw [hgdef]
    exact norm_le_of_sub_one_le (hn t ht')
  have hdet : (g 0).det = 1 := hgrp' hz
  have hn0 : ‖g 0 - 1‖ ≤ 1 / 2 := by
    rw [hgdef]
    exact hn 0 hz
  have hinv : ‖(g 0)⁻¹‖ ≤ 2 := norm_inv_le_two hdet hn0
  rw [e₁, norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
  refine (norm_mul_le _ _).trans ?_
  calc ‖deriv g 0‖ * ‖(g 0)⁻¹‖ ≤ (3 / 2) / (s / 2) * 2 :=
        mul_le_mul hc hinv (norm_nonneg _) (by positivity)
    _ = 6 / s := by
        field_simp
        ring
private theorem mean_differential_facts (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    leftDifferential normalizedMean V B c = holLeftDifferential normalizedMean V B c ∧
      leftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless ∧
      ‖leftDifferential normalizedMean V B c‖ ≤ 6 / (δ / (M + 1)) := by
  have hs : 0 < δ / (M + 1) := div_pos R.dpos (by linarith)
  obtain ⟨e, hm, hb⟩ := logDirectionalDeriv_facts T hs h.conf (Φ := fun W => normalizedMean W c)
    (fun t₀ ht => ((regularFamily_disc R T hM h ht).averageGerm T hc).1)
    (fun t ht => ((regularFamily_disc R T hM h ht).averageGerm T hc).2.self_of_nhdsWithin ht)
    (fun t ht => le_of_lt (T.near_unit _ (twisted_conf T h t)
      (fun b => twisted_near R T hM h ht b) c hc))
  have e₁ : leftDifferential normalizedMean V B c = Tower.logDirectionalDeriv ℝ
      (fun X => normalizedMean (PeriodicLattice.expTwist X V) c) (normalizedMean V c) B :=
    extendOddly_positive hc
  have e₂ : holLeftDifferential normalizedMean V B c = Tower.logDirectionalDeriv ℂ
      (fun X => normalizedMean (PeriodicLattice.expTwist X V) c) (normalizedMean V c) B :=
    extendOddly_positive hc
  rw [e₁, e₂]
  exact ⟨e, e ▸ hm, e ▸ hb⟩
private theorem forwardFrom_positive (y : Vertex L n k (j + 1)) :
    (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented := ⟨0, add_sub_cancel_left _ _⟩
private theorem contourHolonomy_near (T : StepFacts L n k j r) {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hn : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    ‖PeriodicLattice.complexMeanContourHolonomy W y x - 1‖ ≤ 1 / 2 ∧
      (PeriodicLattice.complexMeanContourHolonomy W y x).det = 1 := by
  have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
  have hreg : RegularFamily r (univ : Set ℂ) (0 : ℂ) fun _ => W :=
    ⟨mem_univ _, fun b => AnalyticGerm.const _, Eventually.of_forall fun _ => hW, hn⟩
  refine ⟨le_of_lt ((T.serve _ (forwardFrom_positive y)).contourMean_near_one W
    ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩,
      fun b _ => (hn b).trans_le T.le_radius⟩ y (Or.inl rfl) x hx), ?_⟩
  exact (hreg.contour T y hx).2.self_of_nhdsWithin (mem_univ _)
private theorem contour_logDeriv_le (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    ‖Tower.logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
      (PeriodicLattice.complexMeanContourHolonomy V y x) B‖ ≤ 6 / (δ / (M + 1)) := by
  have hs : 0 < δ / (M + 1) := div_pos R.dpos (by linarith)
  exact (logDirectionalDeriv_facts T hs h.conf
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    (fun t₀ ht => ((regularFamily_disc R T hM h ht).contour T y hx).1)
    (fun t ht => ((regularFamily_disc R T hM h ht).contour T y hx).2.self_of_nhdsWithin ht)
    (fun t ht => (contourHolonomy_near T (twisted_conf T h t)
      (fun b => twisted_near R T hM h ht b) y hx).1)).2.2
private theorem norm_weighted_sum_le (T : StepFacts L n k j r) (y : Vertex L n k (j + 1))
    {f : Vertex L n k j → ComplexMatrix2} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, ‖f x‖ ≤ K) :
    ‖PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, f x‖ ≤ K := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, norm_smul]
  have h1 : ‖∑ x ∈ hfin.toFinset, f x‖ ≤ hfin.toFinset.card * K := by
    refine (norm_sum_le _ _).trans ?_
    have h := Finset.sum_le_card_nsmul hfin.toFinset (fun x => ‖f x‖) K
      (fun x hx => hf x (hfin.mem_toFinset.1 hx))
    simpa [nsmul_eq_mul] using h
  have h2 : hfin.toFinset.card = L ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
    exact T.card y
  have hL : (0 : ℝ) < L := by exact_mod_cast T.L_pos
  have h3 : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    unfold PeriodicLattice.inverseFourthPowerWeight
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [zpow_neg]
    norm_cast
  rw [h3]
  rw [h2] at h1
  push_cast at h1
  calc ((L : ℝ) ^ 4)⁻¹ * ‖∑ x ∈ hfin.toFinset, f x‖ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * K) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K := by
        field_simp
end Disc
section Locality
variable {L n k j : ℕ} {r δ M : ℝ}
private theorem doubleBlock_opposite_closed (c : Edge L n k (j + 1)) :
    ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  fun b hb => ⟨hb.2, hb.1⟩
private theorem expTwist_congr_on {D : Set (Edge L n k j)} (hD : ∀ b ∈ D, b.opposite ∈ D)
    {A A' U U' : Edge L n k j → ComplexMatrix2} (hA : ∀ b ∈ D, A b = A' b)
    (hU : ∀ b ∈ D, U b = U' b) {b : Edge L n k j} (hb : b ∈ D) :
    PeriodicLattice.expTwist A U b = PeriodicLattice.expTwist A' U' b := by
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_positive hp, expTwist_positive hp, hA b hb, hU b hb]
  · rw [expTwist_not_positive hp, expTwist_not_positive hp, hA _ (hD b hb), hU _ (hD b hb)]
private theorem expTwist_eq_of_vanish {D : Set (Edge L n k j)} (hD : ∀ b ∈ D, b.opposite ∈ D)
    {B V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : ∀ b ∈ D, B b = 0) (t : ℂ) {b : Edge L n k j} (hb : b ∈ D) :
    PeriodicLattice.expTwist (t • B) V b = V b := by
  have h := expTwist_congr_on hD (A := t • B) (A' := (0 : ℂ) • B) (U := V) (U' := V)
    (fun b hb => by simp [hB b hb]) (fun _ _ => rfl) hb
  rw [h, expTwist_zero hV]
private theorem leftDifferential_congr (T : StepFacts L n k j r) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' B B' : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), V b = V' b)
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), B b = B' b) :
    leftDifferential normalizedMean V B c = leftDifferential normalizedMean V' B' c := by
  have e₁ : leftDifferential normalizedMean V B c = Tower.logDirectionalDeriv ℝ
      (fun X => normalizedMean (PeriodicLattice.expTwist X V) c) (normalizedMean V c) B :=
    extendOddly_positive hc
  have e₂ : leftDifferential normalizedMean V' B' c = Tower.logDirectionalDeriv ℝ
      (fun X => normalizedMean (PeriodicLattice.expTwist X V') c) (normalizedMean V' c) B' :=
    extendOddly_positive hc
  have e : ∀ t : ℂ, normalizedMean (PeriodicLattice.expTwist (t • B) V) c =
      normalizedMean (PeriodicLattice.expTwist (t • B') V') c := fun t =>
    T.average_reads c hc _ _ fun b hb =>
      expTwist_congr_on (doubleBlock_opposite_closed c) (fun b hb => by simp [hB b hb]) hV hb
  rw [e₁, e₂]
  unfold Tower.logDirectionalDeriv
  simp only [e, T.average_reads c hc V V' hV]
private theorem leftDifferential_eq_zero (T : StepFacts L n k j r) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), B b = 0) :
    leftDifferential normalizedMean V B c = 0 := by
  have e₁ : leftDifferential normalizedMean V B c = Tower.logDirectionalDeriv ℝ
      (fun X => normalizedMean (PeriodicLattice.expTwist X V) c) (normalizedMean V c) B :=
    extendOddly_positive hc
  have e : ∀ t : ℂ, normalizedMean (PeriodicLattice.expTwist (t • B) V) c = normalizedMean V c :=
    fun t => T.average_reads c hc _ _ fun b hb =>
      expTwist_eq_of_vanish (doubleBlock_opposite_closed c) hV hB t hb
  rw [e₁]
  unfold Tower.logDirectionalDeriv
  simp only [e, deriv_const, smul_zero]
private theorem contourHolonomy_local (T : StepFacts L n k j r) {W W' : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hn : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (h : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), W' b = W b) :
    PeriodicLattice.complexMeanContourHolonomy W' y x =
      PeriodicLattice.complexMeanContourHolonomy W y x :=
  T.reads y x hx _ (forwardFrom_positive y) (Or.inl rfl) W hW
    (fun b => (hn b).trans_le T.le_radius) W' h
private theorem contourLogDrift_congr (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B V' B' : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) (y : Vertex L n k (j + 1))
    (hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), V' b = V b)
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), B' b = B b) :
    contourLogDrift V' B' y = contourLogDrift V B y := by
  have hs : 0 < δ / (M + 1) := div_pos R.dpos (by linarith)
  unfold contourLogDrift
  refine congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
    (finsum_mem_congr rfl fun x hx => ?_)
  have e : ∀ t ∈ ball (0 : ℂ) (δ / (M + 1)),
      PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B') V') y x =
        PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x :=
    fun t ht => contourHolonomy_local T (twisted_conf T h t) (fun b => twisted_near R T hM h ht b) y hx
      fun b hb => expTwist_congr_on (doubleBlock_opposite_closed _)
        (fun b hb => by simp [hB b hb]) hV hb
  have e0 := contourHolonomy_local T h.conf (h.lt R) y hx hV
  unfold Tower.logDirectionalDeriv
  refine congrArg (Complex.I⁻¹ • ·) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [ball_mem_nhds (0 : ℂ) hs] with t ht
  show ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.expTwist (t • B') V') y x *
      (PeriodicLattice.complexMeanContourHolonomy V' y x)⁻¹) = ComplexMatrix2.logSeries
    (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x *
      (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹)
  rw [e t ht, e0]
private theorem contourLogDrift_eq_zero (R : DiscRadii r δ) (T : StepFacts L n k j r)
    {V B B₀ : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B₀) (y : Vertex L n k (j + 1))
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), B b = 0) :
    contourLogDrift V B y = 0 := by
  have e : ∀ (t : ℂ) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x =
        PeriodicLattice.complexMeanContourHolonomy V y x :=
    fun t x hx => contourHolonomy_local T h.conf (h.lt R) y hx fun b hb =>
      expTwist_eq_of_vanish (doubleBlock_opposite_closed _) h.conf hB t hb
  unfold contourLogDrift
  have hz : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Tower.logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B = 0 := fun x hx => by
    unfold Tower.logDirectionalDeriv
    have e' : ∀ t : ℂ, PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) V) y x =
        PeriodicLattice.complexMeanContourHolonomy V y x := fun t => e t x hx
    simp only [e', deriv_const, smul_zero]
  rw [finsum_mem_congr rfl hz]
  simp
private theorem adjointCubeAverage_congr (R : DiscRadii r δ) (T : StepFacts L n k j r)
    {V B V' : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B)
    {l l' : Vertex L n k j → ComplexMatrix2} (y : Vertex L n k (j + 1))
    (hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), V' b = V b)
    (hl : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, l' x = l x) :
    adjointCubeAverage V' l' y = adjointCubeAverage V l y := by
  unfold adjointCubeAverage
  refine congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
    (finsum_mem_congr rfl fun x hx => ?_)
  rw [contourHolonomy_local T h.conf (h.lt R) y hx hV, hl x hx]
private theorem adjointCubeAverage_eq_zero {V : Edge L n k j → ComplexMatrix2}
    {l : Vertex L n k j → ComplexMatrix2} (y : Vertex L n k (j + 1))
    (hl : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, l x = 0) :
    adjointCubeAverage V l y = 0 := by
  unfold adjointCubeAverage
  have hz : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) = 0 :=
    fun x hx => by
      rw [hl x hx]
      simp [ComplexMatrix2.conjugateBy]
  rw [finsum_mem_congr rfl hz]
  simp
private theorem contourLogDrift_le (R : DiscRadii r δ) (T : StepFacts L n k j r) (hM : 0 ≤ M)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) (y : Vertex L n k (j + 1)) :
    ‖contourLogDrift V B y‖ ≤ 6 / (δ / (M + 1)) := by
  have hs : 0 < δ / (M + 1) := div_pos R.dpos (by linarith)
  exact norm_weighted_sum_le T y (by positivity) fun x hx => contour_logDeriv_le R T hM h y hx
private theorem adjointCubeAverage_le (R : DiscRadii r δ) (T : StepFacts L n k j r)
    {V B : Edge L n k j → ComplexMatrix2} (h : SmallPair r M V B) {l : Vertex L n k j → ComplexMatrix2}
    {m : ℝ} (hm : 0 ≤ m) (hl : ∀ x, ‖l x‖ ≤ m) (y : Vertex L n k (j + 1)) :
    ‖adjointCubeAverage V l y‖ ≤ 3 * m := by
  refine norm_weighted_sum_le T y (by positivity) fun x hx => ?_
  obtain ⟨h₁, h₂⟩ := contourHolonomy_near T h.conf (h.lt R) y hx
  have := norm_conjugateBy_le (norm_le_of_sub_one_le h₁) (norm_inv_le_two h₂ h₁) (hl x)
  linarith
end Locality
section Chain
variable {L n k : ℕ}
private theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
private theorem levelField_positive (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by
  rw [levelField_succ X h]
  simp [fieldOfPositiveValues, hb]
abbrev _root_.YangMills.SharedProofs.p325 := @levelField_positive
private theorem tangentTransport_positive (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b = ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by
  simp only [tangentTransport, dif_pos h, extendOddly, if_pos hb, dif_pos hb]
abbrev _root_.YangMills.SharedProofs.p457 := @tangentTransport_positive
private theorem tangentTransport_negative (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b = -tangentTransport X ξ (j + 1) b.opposite := by
  have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
  rw [tangentTransport_positive X ξ h hr]
  simp only [tangentTransport, dif_pos h, extendOddly, if_neg hb, dif_pos hr]
variable {I : Type} [Fintype I]
private structure ChainSetting (X : (I → ℂ) → ChainPoint L n k) (e : I → Vertex L n k k)
    (r δ ρ rF : ℝ) : Prop where
  radii : DiscRadii r δ
  facts : ∀ j < k, StepFacts L n k j r
  conf : ∀ j ≤ k, ∀ z ∈ ball (0 : I → ℂ) ρ,
    levelField (X z) j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  an : ∀ j ≤ k, ∀ b : Edge L n k j,
    AnalyticOnNhd ℂ (fun z => levelField (X z) j b) (ball (0 : I → ℂ) ρ)
  near : ∀ j ≤ k, ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ b : Edge L n k j,
    ‖levelField (X z) j b - 1‖ ≤ r / 4
  reads : ∀ j ≤ k, ∀ b : Edge L n k j, ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ z' ∈ ball (0 : I → ℂ) ρ,
    (∀ i, cellDist (e i) (levelVertexCell b.source) ≤ rF → z i = z' i) →
      levelField (X z) j b = levelField (X z') j b
  rF_nonneg : 0 ≤ rF
  tri : ∀ y y' y'' : Vertex L n k k, cellDist y y'' ≤ cellDist y y' + cellDist y' y''
  symm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  double : ∀ j < k, ∀ (c : Edge L n k (j + 1)) (b : Edge L n k j),
    b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) →
      cellDist (levelVertexCell b.source) (levelVertexCell c.source) ≤ 5
  site : ∀ j < k, ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      cellDist (levelVertexCell x) (levelVertexCell y) ≤ 3
  ends : ∀ j ≤ k, ∀ b : Edge L n k j,
    cellDist (levelVertexCell b.target) (levelVertexCell b.source) ≤ 4
private structure BasisFormFacts (ξ : LevelForms L n k) (y₀ : Vertex L n k k) (C₀ : ℝ) : Prop where
  first_bound : ∀ b : Edge L n k 0, ‖(ξ.1 : Edge L n k 0 → ComplexMatrix2) b‖ ≤ C₀
  first_far : ∀ b : Edge L n k 0, 4 < cellDist (levelVertexCell b.source) y₀ →
    (ξ.1 : Edge L n k 0 → ComplexMatrix2) b = 0
  level_bound : ∀ (i : Fin k) (c : Edge L n k (i + 1)), c.IsPositivelyOriented →
    ‖(ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c‖ ≤ C₀
  level_far : ∀ (i : Fin k) (c : Edge L n k (i + 1)), c.IsPositivelyOriented →
    2 < cellDist (levelVertexCell c.source) y₀ → (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c = 0
private structure LevelControl (X : (I → ℂ) → ChainPoint L n k) (e : I → Vertex L n k k) (ρ : ℝ)
    (ξ : LevelForms L n k) (y₀ : Vertex L n k k) (j : ℕ) (M R : ℝ) : Prop where
  an : ∀ b : Edge L n k j,
    AnalyticOnNhd ℂ (fun z => tangentTransport (X z) ξ j b) (ball (0 : I → ℂ) ρ)
  form : ∀ z ∈ ball (0 : I → ℂ) ρ, tangentTransport (X z) ξ j ∈ complexEdgeForms L n k j
  bound : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ b, ‖tangentTransport (X z) ξ j b‖ ≤ M
  reads : ∀ b : Edge L n k j, ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ z' ∈ ball (0 : I → ℂ) ρ,
    (∀ i, cellDist (e i) (levelVertexCell b.source) ≤ R → z i = z' i) →
      tangentTransport (X z) ξ j b = tangentTransport (X z') ξ j b
  far : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ b : Edge L n k j,
    R < cellDist (levelVertexCell b.source) y₀ → tangentTransport (X z) ξ j b = 0
  san : ∀ y : Vertex L n k j,
    AnalyticOnNhd ℂ (fun z => chainDrift (X z) ξ j y) (ball (0 : I → ℂ) ρ)
  sbound : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ y, ‖chainDrift (X z) ξ j y‖ ≤ M
  sreads : ∀ y : Vertex L n k j, ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ z' ∈ ball (0 : I → ℂ) ρ,
    (∀ i, cellDist (e i) (levelVertexCell y) ≤ R → z i = z' i) →
      chainDrift (X z) ξ j y = chainDrift (X z') ξ j y
  sfar : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ y : Vertex L n k j,
    R < cellDist (levelVertexCell y) y₀ → chainDrift (X z) ξ j y = 0
variable {X : (I → ℂ) → ChainPoint L n k} {e : I → Vertex L n k k} {r δ ρ rF : ℝ}
  {ξ : LevelForms L n k} {y₀ : Vertex L n k k} {C₀ : ℝ}
private theorem noise_facts (S : ChainSetting X e r δ ρ rF) {j : ℕ} (hj : j < k)
    {z : I → ℂ} (hz : z ∈ ball (0 : I → ℂ) ρ) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    (X z).noise ⟨j, hj⟩ ⟨c, hc⟩ =
        levelField (X z) (j + 1) c * (normalizedMean (levelField (X z) j) c)⁻¹ ∧
      ‖(X z).noise ⟨j, hj⟩ ⟨c, hc⟩‖ ≤ 3 ∧ ‖((X z).noise ⟨j, hj⟩ ⟨c, hc⟩)⁻¹‖ ≤ 3 ∧
      ((X z).noise ⟨j, hj⟩ ⟨c, hc⟩).det = 1 := by
  have T := S.facts j hj
  have R := S.radii
  have hr := R.pos
  have hr2 := R.half
  have hnj := S.near j hj.le z hz
  have hnear : ∀ b, ComplexMatrix2.operatorNorm (levelField (X z) j b - 1) < r := fun b => by
    have h₁ := hnj b
    show ‖levelField (X z) j b - 1‖ < r
    linarith
  have hu₁ : ‖normalizedMean (levelField (X z) j) c - 1‖ ≤ 1 / 2 :=
    le_of_lt (T.near_unit _ (S.conf j hj.le z hz) hnear c hc)
  have hu₂ : (normalizedMean (levelField (X z) j) c).det = 1 :=
    (T.near_one _ (S.conf j hj.le z hz) hnear c hc).2
  have hW₁ : ‖levelField (X z) (j + 1) c - 1‖ ≤ 1 / 2 := by
    have := S.near (j + 1) hj z hz c
    linarith
  have hW₂ : (levelField (X z) (j + 1) c).det = 1 :=
    (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ
      (levelField (X z) (j + 1)) from S.conf (j + 1) hj z hz).1 c (mem_univ c)
  have huu : IsUnit (normalizedMean (levelField (X z) j) c).det := by rw [hu₂]; exact isUnit_one
  have hWu : IsUnit (levelField (X z) (j + 1) c).det := by rw [hW₂]; exact isUnit_one
  have e₁ : (X z).noise ⟨j, hj⟩ ⟨c, hc⟩ =
      levelField (X z) (j + 1) c * (normalizedMean (levelField (X z) j) c)⁻¹ := by
    rw [levelField_positive _ hj hc, mul_assoc, Matrix.mul_nonsing_inv _ huu, mul_one]
  have hdet : ((X z).noise ⟨j, hj⟩ ⟨c, hc⟩).det = 1 := by
    have h := congrArg Matrix.det (levelField_positive (X z) hj hc)
    rw [Matrix.det_mul, hW₂, hu₂, mul_one] at h
    exact h.symm
  refine ⟨e₁, ?_, ?_, hdet⟩
  · rw [e₁]
    refine (norm_mul_le _ _).trans ?_
    have h₁ := norm_le_of_sub_one_le hW₁
    have h₂ := norm_inv_le_two hu₂ hu₁
    calc _ ≤ 3 / 2 * 2 := mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  · rw [e₁, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ huu]
    refine (norm_mul_le _ _).trans ?_
    have h₁ := norm_le_of_sub_one_le hu₁
    have h₂ := norm_inv_le_two hW₂ hW₁
    calc _ ≤ 3 / 2 * 2 := mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)
      _ = 3 := by norm_num
private theorem levelControl_zero (S : ChainSetting X e r δ ρ rF) (hξ : BasisFormFacts ξ y₀ C₀)
    (hC : 0 ≤ C₀) : LevelControl X e ρ ξ y₀ 0 C₀ 4 := by
  refine ⟨fun b z _ => analyticAt_const, fun z _ => ⟨fun b hb => (ξ.1.2.1 b hb).2, ξ.1.2.2⟩,
    fun z _ b => hξ.first_bound b, fun b z _ z' _ _ => rfl, fun z _ b h => hξ.first_far b h,
    fun y z _ => analyticAt_const, fun z _ y => ?_, fun y z _ z' _ _ => rfl, fun z _ y _ => rfl⟩
  show ‖(0 : ComplexMatrix2)‖ ≤ C₀
  simpa using hC
private theorem levelControl_succ (S : ChainSetting X e r δ ρ rF) (hξ : BasisFormFacts ξ y₀ C₀)
    {j : ℕ} (hj : j < k) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hC : 0 ≤ C₀)
    (G : LevelControl X e ρ ξ y₀ j M R) :
    LevelControl X e ρ ξ y₀ (j + 1) (9 * (6 / (δ / (M + 1))) + C₀ + 3 * M) (R + rF + 9) := by
  have T := S.facts j hj
  have Rd := S.radii
  have hjl : j ≤ k := hj.le
  have hj1 : j + 1 ≤ k := hj
  have hrF := S.rF_nonneg
  have hs : 0 < δ / (M + 1) := div_pos Rd.dpos (by linarith)
  have hK : 0 ≤ 6 / (δ / (M + 1)) := by positivity
  have sm : ∀ z ∈ ball (0 : I → ℂ) ρ,
      SmallPair r M (levelField (X z) j) (tangentTransport (X z) ξ j) :=
    fun z hz => ⟨S.conf j hjl z hz, S.near j hjl z hz, G.form z hz, G.bound z hz⟩
  have reg : ∀ z₀ ∈ ball (0 : I → ℂ) ρ,
      RegularFamily r (ball (0 : I → ℂ) ρ) z₀ fun z => levelField (X z) j := fun z₀ hz₀ =>
    ⟨hz₀, fun b => germ_of_analyticAt (S.an j hjl b z₀ hz₀),
      by filter_upwards [self_mem_nhdsWithin] with z hz using S.conf j hjl z hz,
      (sm z₀ hz₀).lt Rd⟩
  have bg : ∀ z₀ ∈ ball (0 : I → ℂ) ρ, ∀ b,
      AnalyticGerm (ball (0 : I → ℂ) ρ) z₀ fun z => tangentTransport (X z) ξ j b :=
    fun z₀ hz₀ b => germ_of_analyticAt (G.an b z₀ hz₀)
  have bf : ∀ z₀, ∀ᶠ p in 𝓝[ball (0 : I → ℂ) ρ] z₀,
      tangentTransport (X p) ξ j ∈ complexEdgeForms L n k j :=
    fun z₀ => by filter_upwards [self_mem_nhdsWithin] with z hz using G.form z hz
  have pos_an : ∀ (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
      AnalyticOnNhd ℂ (fun z => tangentTransport (X z) ξ (j + 1) c) (ball (0 : I → ℂ) ρ) := by
    intro c hc z₀ hz₀
    have hV := reg z₀ hz₀
    have hd : AnalyticGerm (ball (0 : I → ℂ) ρ) z₀ fun z =>
        leftDifferential normalizedMean (levelField (X z) j) (tangentTransport (X z) ξ j) c :=
      (hV.meanDifferential T (bg z₀ hz₀) (bf z₀) c).congr (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (mean_differential_facts Rd T hM (sm z hz) hc).1.symm)
    obtain ⟨h₁, h₂⟩ := hV.averageGerm T hc
    have hdu : (normalizedMean (levelField (X z₀) j) c).det ≠ 0 := by
      have h : (normalizedMean (levelField (X z₀) j) c).det = 1 := h₂.self_of_nhdsWithin hz₀
      rw [h]
      exact one_ne_zero
    have hW : AnalyticGerm (ball (0 : I → ℂ) ρ) z₀ fun z => levelField (X z) (j + 1) c :=
      germ_of_analyticAt (S.an (j + 1) hj1 c z₀ hz₀)
    have hn : AnalyticGerm (ball (0 : I → ℂ) ρ) z₀ fun z => (X z).noise ⟨j, hj⟩ ⟨c, hc⟩ :=
      (hW.mul (h₁.inv hz₀ hdu)).congr (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (noise_facts S hj hz hc).1.symm)
    have hnd : ((X z₀).noise ⟨j, hj⟩ ⟨c, hc⟩).det ≠ 0 := by
      rw [(noise_facts S hj hz₀ hc).2.2.2]
      exact one_ne_zero
    exact analyticAt_of_germ isOpen_ball hz₀
      (((AnalyticGerm.conjugateBy hz₀ hn hd hnd).add (AnalyticGerm.const _)).congr
        (Eventually.of_forall fun z => (tangentTransport_positive _ ξ hj hc).symm))
  have pos_val : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      tangentTransport (X z) ξ (j + 1) c ∈ ComplexMatrix2.traceless ∧
        ‖tangentTransport (X z) ξ (j + 1) c‖ ≤ 9 * (6 / (δ / (M + 1))) + C₀ := by
    intro z hz c hc
    obtain ⟨-, hm, hb⟩ := mean_differential_facts Rd T hM (sm z hz) hc
    obtain ⟨-, n₁, n₂, nd⟩ := noise_facts S hj hz hc
    rw [tangentTransport_positive _ ξ hj hc]
    refine ⟨Submodule.add_mem _ (conjugateBy_mem_traceless' nd hm)
      (((ξ.2 ⟨j, hj⟩).2.1 c hc).2), ?_⟩
    refine (norm_add_le _ _).trans (add_le_add ?_ (hξ.level_bound ⟨j, hj⟩ c hc))
    have := norm_conjugateBy_le n₁ n₂ hb
    linarith
  have pos_reads : ∀ (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
      ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ z' ∈ ball (0 : I → ℂ) ρ,
      (∀ i, cellDist (e i) (levelVertexCell c.source) ≤ R + rF + 5 → z i = z' i) →
      tangentTransport (X z) ξ (j + 1) c = tangentTransport (X z') ξ (j + 1) c := by
    intro c hc z hz z' hz' h
    have agW : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        levelField (X z) j b = levelField (X z') j b := fun b hb =>
      S.reads j hjl b z hz z' hz' fun i hi => h i (by
        have h₁ := S.tri (e i) (levelVertexCell b.source) (levelVertexCell c.source)
        have h₂ := S.double j hj c b hb
        linarith)
    have agB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        tangentTransport (X z) ξ j b = tangentTransport (X z') ξ j b := fun b hb =>
      G.reads b z hz z' hz' fun i hi => h i (by
        have h₁ := S.tri (e i) (levelVertexCell b.source) (levelVertexCell c.source)
        have h₂ := S.double j hj c b hb
        linarith)
    have hW : levelField (X z) (j + 1) c = levelField (X z') (j + 1) c :=
      S.reads (j + 1) hj1 c z hz z' hz' fun i hi => h i (by linarith)
    have hn : (X z).noise ⟨j, hj⟩ ⟨c, hc⟩ = (X z').noise ⟨j, hj⟩ ⟨c, hc⟩ := by
      rw [(noise_facts S hj hz hc).1, (noise_facts S hj hz' hc).1, hW, T.average_reads c hc _ _ agW]
    rw [tangentTransport_positive _ ξ hj hc, tangentTransport_positive _ ξ hj hc, hn,
      leftDifferential_congr T hc agW agB]
  have pos_far : ∀ z ∈ ball (0 : I → ℂ) ρ, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      R + 5 < cellDist (levelVertexCell c.source) y₀ → tangentTransport (X z) ξ (j + 1) c = 0 := by
    intro z hz c hc hf
    have hd : leftDifferential normalizedMean (levelField (X z) j) (tangentTransport (X z) ξ j) c = 0 :=
      leftDifferential_eq_zero T hc (S.conf j hjl z hz) fun b hb => G.far z hz b (by
        have h₁ := S.tri (levelVertexCell c.source) (levelVertexCell b.source) y₀
        have h₂ := S.double j hj c b hb
        have h₃ := S.symm (levelVertexCell c.source) (levelVertexCell b.source)
        linarith)
    rw [tangentTransport_positive _ ξ hj hc, hd, hξ.level_far ⟨j, hj⟩ c hc (by linarith)]
    simp [ComplexMatrix2.conjugateBy]
  have fwd : ∀ (y : Vertex L n k (j + 1)) (b : Edge L n k j),
      b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)) →
      cellDist (levelVertexCell b.source) (levelVertexCell y) ≤ 5 := fun y b hb => by
    have h := S.double j hj (PeriodicLattice.Bond.forwardFrom y 0) b hb
    have ey : (PeriodicLattice.Bond.forwardFrom y 0).source = y := rfl
    rwa [ey] at h
  have rev_pos : ∀ {c : Edge L n k (j + 1)}, ¬c.IsPositivelyOriented →
      c.opposite.IsPositivelyOriented := fun {c} hc =>
    (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
  refine ⟨fun c => ?_, fun z hz => ?_, fun z hz c => ?_, fun c z hz z' hz' h => ?_,
    fun z hz c hf => ?_, fun y z₀ hz₀ => ?_, fun z hz y => ?_, fun y z hz z' hz' h => ?_,
    fun z hz y hf => ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · exact pos_an c hc
    · have e₁ : (fun z => tangentTransport (X z) ξ (j + 1) c) =
          fun z => -tangentTransport (X z) ξ (j + 1) c.opposite :=
        funext fun z => tangentTransport_negative _ ξ hj hc
      rw [e₁]
      exact fun z hz => (pos_an _ (rev_pos hc) z hz).neg
  · have e₁ : tangentTransport (X z) ξ (j + 1) = extendOddly (tangentTransport (X z) ξ (j + 1)) := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · rw [extendOddly_positive hc]
      · rw [extendOddly_not_positive hc, tangentTransport_negative _ ξ hj hc]
    rw [e₁]
    exact extendOddly_mem T.xor_next fun b hb => (pos_val z hz b hb).1
  · have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ‖tangentTransport (X z) ξ (j + 1) c‖ ≤ 9 * (6 / (δ / (M + 1))) + C₀ + 3 * M := fun c hc => by
      have := (pos_val z hz c hc).2
      linarith
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · rw [tangentTransport_negative _ ξ hj hc, norm_neg]
      exact hpos _ (rev_pos hc)
  · by_cases hc : c.IsPositivelyOriented
    · exact pos_reads c hc z hz z' hz' fun i hi => h i (by linarith)
    · rw [tangentTransport_negative _ ξ hj hc, tangentTransport_negative _ ξ hj hc,
        pos_reads _ (rev_pos hc) z hz z' hz' fun i hi => h i (by
          have h₁ := S.tri (e i) (levelVertexCell c.target) (levelVertexCell c.source)
          have h₂ := S.ends (j + 1) hj1 c
          have h₃ : cellDist (e i) (levelVertexCell c.target) ≤ R + rF + 5 := hi
          linarith)]
  · by_cases hc : c.IsPositivelyOriented
    · exact pos_far z hz c hc (by linarith)
    · rw [tangentTransport_negative _ ξ hj hc, pos_far z hz _ (rev_pos hc) (by
          have h₁ := S.tri (levelVertexCell c.source) (levelVertexCell c.target) y₀
          have h₂ := S.ends (j + 1) hj1 c
          have h₃ := S.symm (levelVertexCell c.source) (levelVertexCell c.target)
          show R + 5 < cellDist (levelVertexCell c.target) y₀
          linarith), neg_zero]
  · have hV := reg z₀ hz₀
    have h₁ := hV.adjoint T (fun x => germ_of_analyticAt (G.san x z₀ hz₀)) y
    have h₂ := hV.drift T (bg z₀ hz₀) (bf z₀) y
    exact analyticAt_of_germ isOpen_ball hz₀ (h₁.add h₂)
  · show ‖adjointCubeAverage (levelField (X z) j) (chainDrift (X z) ξ j) y +
      contourLogDrift (levelField (X z) j) (tangentTransport (X z) ξ j) y‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    have h₁ := adjointCubeAverage_le Rd T (sm z hz) hM (G.sbound z hz) y
    have h₂ := contourLogDrift_le Rd T hM (sm z hz) y
    linarith
  · have hd : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)), ∀ i, cellDist (e i) (levelVertexCell b.source) ≤ R + rF →
        cellDist (e i) (levelVertexCell y) ≤ R + rF + 9 := fun b hb i hi => by
      have h₁ := S.tri (e i) (levelVertexCell b.source) (levelVertexCell y)
      have h₂ := fwd y b hb
      linarith
    have agW : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)), levelField (X z') j b = levelField (X z) j b := fun b hb =>
      (S.reads j hjl b z hz z' hz' fun i hi => h i (hd b hb i (by linarith))).symm
    have agB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)), tangentTransport (X z') ξ j b = tangentTransport (X z) ξ j b :=
      fun b hb => (G.reads b z hz z' hz' fun i hi => h i (hd b hb i (by linarith))).symm
    have agl : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        chainDrift (X z') ξ j x = chainDrift (X z) ξ j x := fun x hx =>
      (G.sreads x z hz z' hz' fun i hi => h i (by
        have h₁ := S.tri (e i) (levelVertexCell x) (levelVertexCell y)
        have h₂ := S.site j hj y x hx
        linarith)).symm
    show adjointCubeAverage (levelField (X z) j) (chainDrift (X z) ξ j) y +
        contourLogDrift (levelField (X z) j) (tangentTransport (X z) ξ j) y =
      adjointCubeAverage (levelField (X z') j) (chainDrift (X z') ξ j) y +
        contourLogDrift (levelField (X z') j) (tangentTransport (X z') ξ j) y
    rw [adjointCubeAverage_congr Rd T (sm z hz) y agW agl,
      contourLogDrift_congr Rd T hM (sm z hz) y agW agB]
  · show adjointCubeAverage (levelField (X z) j) (chainDrift (X z) ξ j) y +
        contourLogDrift (levelField (X z) j) (tangentTransport (X z) ξ j) y = 0
    have h₁ : adjointCubeAverage (levelField (X z) j) (chainDrift (X z) ξ j) y = 0 :=
      adjointCubeAverage_eq_zero y fun x hx => G.sfar z hz x (by
        have h₁ := S.tri (levelVertexCell y) (levelVertexCell x) y₀
        have h₂ := S.site j hj y x hx
        have h₃ := S.symm (levelVertexCell y) (levelVertexCell x)
        linarith)
    have h₂ : contourLogDrift (levelField (X z) j) (tangentTransport (X z) ξ j) y = 0 :=
      contourLogDrift_eq_zero Rd T (sm z hz) y fun b hb => G.far z hz b (by
        have h₁ := S.tri (levelVertexCell y) (levelVertexCell b.source) y₀
        have h₂ := fwd y b hb
        have h₃ := S.symm (levelVertexCell y) (levelVertexCell b.source)
        linarith)
    rw [h₁, h₂, add_zero]
private def transportBound (δ C₀ : ℝ) : ℕ → ℝ
  | 0 => C₀
  | j + 1 => 9 * (6 / (δ / (transportBound δ C₀ j + 1))) + C₀ + 3 * transportBound δ C₀ j
private def transportRange (rF : ℝ) (j : ℕ) : ℝ := 4 + j * (rF + 9)
private theorem transportBound_nonneg {δ C₀ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C₀) (j : ℕ) :
    0 ≤ transportBound δ C₀ j := by
  induction j with
  | zero => exact hC
  | succ j ih =>
    have : 0 < δ / (transportBound δ C₀ j + 1) := div_pos hδ (by linarith)
    show 0 ≤ 9 * (6 / (δ / (transportBound δ C₀ j + 1))) + C₀ + 3 * transportBound δ C₀ j
    positivity
private theorem transportBound_mono {δ C₀ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C₀) :
    Monotone (transportBound δ C₀) := by
  refine monotone_nat_of_le_succ fun j => ?_
  have h₀ := transportBound_nonneg hδ hC j
  have : 0 < δ / (transportBound δ C₀ j + 1) := div_pos hδ (by linarith)
  have h₁ : 0 ≤ 6 / (δ / (transportBound δ C₀ j + 1)) := by positivity
  show transportBound δ C₀ j ≤
    9 * (6 / (δ / (transportBound δ C₀ j + 1))) + C₀ + 3 * transportBound δ C₀ j
  linarith
private theorem transportRange_mono {rF : ℝ} (h : 0 ≤ rF) {j j' : ℕ} (hj : j ≤ j') :
    transportRange rF j ≤ transportRange rF j' := by
  have : (j : ℝ) ≤ j' := by exact_mod_cast hj
  unfold transportRange
  nlinarith
private theorem levelControl_all (S : ChainSetting X e r δ ρ rF) (hξ : BasisFormFacts ξ y₀ C₀)
    (hC : 0 ≤ C₀) :
    ∀ j ≤ k, LevelControl X e ρ ξ y₀ j (transportBound δ C₀ j) (transportRange rF j) := by
  have hδ := S.radii.dpos
  have hrF := S.rF_nonneg
  intro j
  induction j with
  | zero =>
    intro _
    have h := levelControl_zero S hξ hC
    simpa [transportRange, transportBound] using h
  | succ j ih =>
    intro hj
    have h := levelControl_succ S hξ hj (transportBound_nonneg hδ hC j)
      (by unfold transportRange; positivity) hC (ih (Nat.le_of_succ_le hj))
    have e₁ : transportRange rF j + rF + 9 = transportRange rF (j + 1) := by
      unfold transportRange
      push_cast
      ring
    rw [e₁] at h
    exact h
end Chain
section PauliExpansion
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem norm_le_of_pauliCoeff {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    {x : Fin 3 → ℝ} (hc : ∀ a, pauliCoeff a X = (x a : ℂ)) (hx : ∀ a, |x a| ≤ 1) :
    ‖X‖ ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := by
  rw [← sum_pauliCoeff_smul h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, hc, Complex.norm_real, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_right (hx a) (norm_nonneg (ComplexMatrix2.pauliFamily a))
  linarith
private theorem eq_zero_of_pauliCoeff {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (hc : ∀ a, pauliCoeff a X = 0) : X = 0 := by
  rw [← sum_pauliCoeff_smul h]
  simp [hc]
end PauliExpansion
section BasisForms
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private theorem coordBasisForm_facts (P : PauliCoordinates L n k) (q : LevelFormIndex L n k)
    (self0 : ∀ {j : ℕ} (x : Vertex L n k j),
      cellDist (levelVertexCell x) (levelVertexCell x) ≤ 2)
    (he : ∀ b : Edge L n k 0, cellDist (levelVertexCell b.source) (levelVertexCell b.target) ≤ 4) :
    BasisFormFacts (coordBasisForm P q) (levelFormIndexCell q)
      (∑ a, ‖ComplexMatrix2.pauliFamily a‖) := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = coordBasisForm P q := ⟨_, rfl⟩
  rw [← hξ]
  have hco : ∀ p, P.formCoords ξ p = (Pi.single q 1 : LevelFormIndex L n k → ℝ) p := fun p => by
    rw [hξ]
    unfold coordBasisForm
    rw [LinearEquiv.apply_symm_apply]
  have c₀ : ∀ (b : Edge L n k 0) (hb : b.IsPositivelyOriented) (a : Fin 3),
      pauliCoeff a ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) =
        (((Pi.single q 1 : LevelFormIndex L n k → ℝ) (.inl (a, ⟨b, hb⟩)) : ℝ) : ℂ) :=
    fun b hb a => by
      have h := P.formCoords_base ξ (a, ⟨b, hb⟩)
      rw [hco] at h
      exact h
  have c₁ : ∀ (i : Fin k) (c : Edge L n k (i + 1)) (hc : c.IsPositivelyOriented) (a : Fin 3),
      pauliCoeff a ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c) =
        (((Pi.single q 1 : LevelFormIndex L n k → ℝ) (.inr ⟨i, (a, ⟨c, hc⟩)⟩) : ℝ) : ℂ) :=
    fun i c hc a => by
      have h := P.formCoords_level ξ i (a, ⟨c, hc⟩)
      rw [hco] at h
      exact h
  have hs : ∀ p, |(Pi.single q 1 : LevelFormIndex L n k → ℝ) p| ≤ 1 := fun p => by
    by_cases h : p = q
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hneg : ∀ {b : Edge L n k 0}, (ξ.1 : Edge L n k 0 → ComplexMatrix2) b =
      -(ξ.1 : Edge L n k 0 → ComplexMatrix2) b.opposite := fun {b} => by
    have h := ξ.1.2.2 b.opposite
    rw [PeriodicLattice.Bond.opposite_opposite] at h
    exact h
  have pos₀ : ∀ (b : Edge L n k 0), b.IsPositivelyOriented →
      ‖(ξ.1 : Edge L n k 0 → ComplexMatrix2) b‖ ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := fun b hb =>
    norm_le_of_pauliCoeff (ξ.1.2.1 b hb).2 (c₀ b hb) fun a => hs _
  have far₀ : ∀ (b : Edge L n k 0) (hb : b.IsPositivelyOriented),
      levelVertexCell b.source ≠ levelFormIndexCell q →
        (ξ.1 : Edge L n k 0 → ComplexMatrix2) b = 0 :=
    fun b hb hn => eq_zero_of_pauliCoeff (ξ.1.2.1 b hb).2 fun a => by
      rw [c₀ b hb a, Pi.single_eq_of_ne]
      · simp
      · intro e
        exact hn (by rw [← e]; rfl)
  refine ⟨fun b => ?_, fun b hf => ?_,
    fun i c hc => norm_le_of_pauliCoeff ((ξ.2 i).2.1 c hc).2 (c₁ i c hc) fun a => hs _,
    fun i c hc hf => eq_zero_of_pauliCoeff ((ξ.2 i).2.1 c hc).2 fun a => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact pos₀ b hb
    · rw [hneg, norm_neg]
      exact pos₀ _ ((PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb)
  · by_cases hb : b.IsPositivelyOriented
    · refine far₀ b hb fun e => ?_
      have h := self0 b.source
      rw [← e] at hf
      have h' := self0 b.source
      nth_rewrite 2 [e] at h'
      linarith
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      rw [hneg, far₀ _ hr, neg_zero]
      intro e
      have h := he b
      have e' : levelVertexCell b.target = levelFormIndexCell q := e
      rw [e'] at h
      linarith
  · rw [c₁ i c hc a, Pi.single_eq_of_ne]
    · simp
    · intro e
      have h := self0 c.source
      have e' : levelFormIndexCell q = levelVertexCell c.source := by rw [← e]; rfl
      rw [e'] at hf
      linarith
end BasisForms
section BlockVertices
variable {L n k : ℕ}
private theorem blockVertex_cell_near (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j < k) (y : Vertex L n k (j + 1))
    (x : Vertex L n k j) (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    cellDist (levelVertexCell x) (levelVertexCell y) ≤ 3 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hη := meshSize_le_one (k := k) hL1 (Nat.succ_le_of_lt hj)
  have key : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) -
      (y : PeriodicLattice.FourTorus L n)) μ‖ ≤ 1 / 2 := by
    intro μ
    have h := hx.1
    change torusSupNorm _ ≤ _ at h
    rw [SeparatedSequence.torusSupNorm_le_iff] at h
    have := h μ
    linarith
  have := cellDist_le_of_near hC hL x y (t := 1 / 2) (by norm_num) key
  linarith
end BlockVertices
end TransportLocality
open Matrices Tower TransportLocality in
theorem basisTransportAndDriftAreLocal_holds
    (hF : LevelFieldsHolomorphicAndLocal)
    (hN : NormalizedMeanNearOne)
    (hRd : NormalizedMeanLocal)
    (hC : NeighbouringFineVertexCells)
    (hAvg : Tower.SmoothingNearIdentity)
    (hCont : Tower.PairContourIndependence.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hChart : Tower.LeftChartFields.Claim)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    BasisTransportAndDriftAreLocal := by
  intro L hL k hk
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : 0 < L := by omega
  have : NeZero L := ⟨by omega⟩
  obtain ⟨ρF, CF, rF, hρF, hCF, hrF, HF⟩ := hF L hL k hk
  obtain ⟨ρ₂, hρ₂, hnear⟩ := hN L hL
  have hrad := (hAvg.1 L hL).2.2
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = min (min (polydiscRadius L) ρ₂) (1 / 2) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hrd]
    exact lt_min (lt_min hrad.pos hρ₂) (by norm_num)
  have hr₀ : r ≤ polydiscRadius L := by
    rw [hrd]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hr₂ : r ≤ ρ₂ := by
    rw [hrd]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hr₃ : r ≤ 1 / 2 := by
    rw [hrd]
    exact min_le_right _ _
  obtain ⟨δ, hδ, hexp⟩ := matExp_near_one (ε := r / 8) (by positivity)
  have Rd : DiscRadii r δ := ⟨hr, hr₃, hδ, hexp⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = min ρF (r / (4 * (CF + 1))) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρd]
    exact lt_min hρF (by positivity)
  have hρ₁ : ρ ≤ ρF := by
    rw [hρd]
    exact min_le_left _ _
  have hρ₃ : ρ ≤ r / (4 * (CF + 1)) := by
    rw [hρd]
    exact min_le_right _ _
  have hC₀ : 0 ≤ ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨ρ, transportBound δ (∑ a, ‖ComplexMatrix2.pauliFamily a‖) k, transportRange rF k, hρ,
    transportBound_nonneg hδ hC₀ k, ?_, ?_⟩
  · unfold transportRange
    positivity
  filter_upwards [HF, Filter.eventually_gt_atTop 0] with n hFn hn
  intro _ _ _ _ _ _ _ _ _ P q
  obtain ⟨-, hconf, hval, -⟩ := hFn P
  have sb : Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ ⊆ Metric.ball 0 ρF :=
    Metric.ball_subset_ball hρ₁
  have F : ∀ j < k, StepFacts L n k j r := fun j hj =>
    { bonds := PeriodicLattice.instFiniteBond _
      sites := SeparatedSequences.BaseParameters.site_finite (by omega) n _
      xor := fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
        (by simp only [PeriodicLattice.levelDepth]; omega) b
      exp := hE
      xor_next := fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
        (by simp only [PeriodicLattice.levelDepth]; omega) b
      L_pos := hL0
      card := fun y => ((hb L hL n k hn).1 j hj (PeriodicLattice.Bond.forwardFrom y 0)
        (forwardFrom_positive y)).1
      real_curves := fun I hI => (hChart.1 I hI).2
      near_unit := fun V hV hn' c hc =>
        (hnear n k j hn hj V hV (fun b => (hn' b).trans_le hr₂) c hc).2.2.1
      average_reads := fun c hc W W' h => (hRd L hL n k j hn hj c hc W W' h).2.2
      curves := hChart.2.1
      near_one := fun V hV hn' c hc => by
        have h := hnear n k j hn hj V hV (fun b => (hn' b).trans_le hr₂) c hc
        exact ⟨h.2.1, h.2.2.2.1⟩
      le_radius := hr₀
      serve := fun c hc => hrad.periodic n k j hn hj c hc
      reads := fun y x hx c hc hy W hW hWn W' hr' =>
        ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
          (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2 }
  have ends : ∀ j ≤ k, ∀ b : Edge L n k j,
      cellDist (levelVertexCell b.target) (levelVertexCell b.source) ≤ 4 := fun j hj b => by
    have := cellDist_le_of_near hC hL b.target b.source (t := 1) zero_le_one (edge_ends_near hL1 hj b)
    linarith
  have self0 : ∀ {j : ℕ} (x : Vertex L n k j),
      cellDist (levelVertexCell x) (levelVertexCell x) ≤ 2 := fun {j} x => by
    have := cellDist_le_of_near hC hL x x (t := 0) le_rfl (fun μ => by simp)
    linarith
  have S : ChainSetting (I := TripleCoordIndex L n k) complexChainPoint tripleCoordIndexCell
      r δ ρ rF :=
    { radii := Rd
      facts := F
      conf := fun j hj z hz => hconf j hj z (sb hz)
      an := fun j hj b => (hval j hj b).1.mono sb
      near := fun j hj z hz b => by
        have h₁ : ‖levelField (complexChainPoint z) j b - 1‖ ≤ CF * ‖z‖ :=
          (hval j hj b).2.1 z (sb hz)
        have h₂ : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
        have h₃ : ‖z‖ < r / (4 * (CF + 1)) := h₂.trans_le hρ₃
        rw [lt_div_iff₀ (by positivity)] at h₃
        nlinarith [norm_nonneg z]
      reads := fun j hj b z hz z' hz' h => (hval j hj b).2.2 z (sb hz) z' (sb hz') h
      rF_nonneg := hrF
      tri := (hC L hL n k).2.1
      symm := (hC L hL n k).1
      double := fun j hj c b hb' => doubleBlock_source_near hC hL hj c hb'
      site := fun j hj y x hx => blockVertex_cell_near hC hL hj y x hx
      ends := ends }
  have hξ := coordBasisForm_facts P q self0 fun b => by
    have h₁ := ends 0 (Nat.zero_le k) b
    rw [(hC L hL n k).1] at h₁
    exact h₁
  have G := levelControl_all S hξ hC₀
  have hM : ∀ j ≤ k, transportBound δ (∑ a, ‖ComplexMatrix2.pauliFamily a‖) j ≤
      transportBound δ (∑ a, ‖ComplexMatrix2.pauliFamily a‖) k :=
    fun j hj => transportBound_mono hδ hC₀ hj
  have hRg : ∀ j ≤ k, transportRange rF j ≤ transportRange rF k :=
    fun j hj => transportRange_mono hrF hj
  refine ⟨fun j hj b => ⟨⟨(G j hj).an b, fun z hz => ((G j hj).bound z hz b).trans (hM j hj),
      fun z hz z' hz' h => (G j hj).reads b z hz z' hz' fun i hi => h i (hi.trans (hRg j hj))⟩,
      fun hf z hz => (G j hj).far z hz b ((hRg j hj).trans_lt hf)⟩,
    fun j hj y => ⟨⟨(G j hj).san y, fun z hz => ((G j hj).sbound z hz y).trans (hM j hj),
      fun z hz z' hz' h => (G j hj).sreads y z hz z' hz' fun i hi => h i (hi.trans (hRg j hj))⟩,
      fun hf z hz => (G j hj).sfar z hz y ((hRg j hj).trans_lt hf)⟩⟩
end YangMills.Construction.RunningCouplingSlope
end
