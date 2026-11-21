import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Matrices.ConjugationInvariantForms
import YangMills.Construction.RunningCouplingSlope.CellsOfABlockAreNear
import YangMills.Construction.RunningCouplingSlope.PlainAverageReadsTheDoubleBlock
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.RunningCouplingSlope.TheFieldsOfTheChainReadNearCells
import YangMills.Construction.RunningCouplingSlope.TheMovementAndTheDriftReadNearCells
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace TransportDriftLocality
open Matrices
open Tower
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
private def matrixEntryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
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
private theorem eventually_prod_zero_curry {q : P × ℂ → Prop}
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
private theorem tendsto_fst_prodZero :
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
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem mul_mem_unitDet {g g' : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant)
    (hg' : g' ∈ ComplexMatrix2.unitDeterminant) : g * g' ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
private theorem matExp_mem_unitDet (hE : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp Z ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p27134 <;> assumption
private theorem expTwist_mem_fields (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.expTwist_mem_fieldsIn <;> assumption
end TwistedFields
section Level
variable {L n k j : ℕ}
private theorem expTwist_zero_smul {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (A : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • A) U = U := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.expTwist_zero_smul <;> assumption
private structure StepHypotheses (L n k j : ℕ) (r : ℝ) : Prop where
  bonds : Finite (Edge L n k j)
  sites : Finite (Vertex L n k j)
  xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  exp : ComplexMatrix2.ExpLogEstimates
  curves : ∀ s : ℝ, 0 < s → CurveLogDerivative ℂ (Metric.ball 0 s)
    PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  near_one : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
        ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2
  le_radius : r ≤ polydiscRadius L
  pos : 0 < L
  count : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).ncard ≤ L ^ 4
  reads_average : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ W W' : Edge L n k j → ComplexMatrix2,
    (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), W b = W' b) →
      normalizedMean W c = normalizedMean W' c
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
private structure RegularFamily (r : ℝ) (S : Set P) (p₀ : P)
    (V : P → Edge L n k j → ComplexMatrix2) : Prop where
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
private theorem RegularFamily.eventually_near (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < r := by
  have := T.bonds
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝[S] p₀) (𝓝 ‖V p₀ b - 1‖) :=
    (((hV.germ b).tendsto hV.mem).sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near b)
private theorem det_pathHolonomy {U : Edge L n k j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (l : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy U l).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.det_pathHolonomy <;> assumption
private theorem RegularFamily.holonomy_germ (hV : RegularFamily r S p₀ V) (l : List (Edge L n k j)) :
    AnalyticGerm S p₀ fun p => PeriodicLattice.pathHolonomy (V p) l :=
  AnalyticGerm.list_prod V hV.germ l
private theorem RegularFamily.contourHolonomy_germ (hV : RegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    AnalyticGerm S p₀ fun p => contourHolonomy (V p) c x π := by
  refine ((hV.holonomy_germ _).mul (hV.holonomy_germ _)).mul ((hV.holonomy_germ _).inv hV.mem ?_)
  rw [det_pathHolonomy hV.det_eq]
  exact one_ne_zero
private theorem RegularFamily.contourMean_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => contourMean (V p) c := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold contourMean
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x _ =>
    AnalyticGerm.finset_sum _ fun π _ => hV.contourHolonomy_germ c x π)
private theorem RegularFamily.normalizedMean_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    AnalyticGerm S p₀ (fun p => normalizedMean (V p) c) ∧
      ∀ᶠ p in 𝓝[S] p₀, normalizedMean (V p) c ∈ PeriodicLattice.complexGaugeGroup := by
  have hn := T.near_one _ hV.self_conf hV.near c hc
  have hm := hV.contourMean_germ T c
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
  exact (T.near_one _ h₁ h₂ c hc).2.1
private theorem extendFromPositive_restrict {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, W b.opposite = (W b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
private theorem RegularFamily.contour_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
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
      fun b hb => extendFromPositive_restrict hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
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
private theorem RegularFamily.twist (T : StepHypotheses L n k j r) (hV : RegularFamily r S p₀ V)
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
    · exact (hval b).congr (Eventually.of_forall fun z => (expTwist_of_pos hb).symm)
    · refine ((hval b.opposite).inv hmem ?_).congr
        (Eventually.of_forall fun z => (expTwist_of_not_pos hb).symm)
      have h0 : ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) = 1 := by
        simp [ComplexMatrix2.matExp]
      show (ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) *
        V p₀ b.opposite).det ≠ 0
      rw [h0, one_mul, hV.det_eq]
      exact one_ne_zero
  · refine (tendsto_fst_prodZero.eventually (hV.conf.and hBf)).mono fun z h => ?_
    exact expTwist_mem_fields T.exp T.xor (Submodule.smul_mem _ z.2 h.2) h.1
  · show ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist ((0 : ℂ) • B p₀) (V p₀) b - 1) < r
    rw [expTwist_zero_smul hV.self_conf]
    exact hV.near b
private theorem RegularFamily.logDeriv_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
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
    filter_upwards [eventually_prod_zero_curry hgrp, hg.along, hV.conf] with p h₁ h₂ h₃
    obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.1 h₁
    have hc := T.curves s hs (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p)))
      (fun t ht => hball t ht) h₂
    obtain ⟨-, -, heq, hm⟩ := hc
    refine ⟨?_, hm⟩
    have e : Φ (V p) = Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)) := by
      rw [expTwist_zero_smul h₃]
    rw [← heq, e]
    rfl
  refine ⟨hmain.congr (hall.mono fun p h => h.1.symm), hall.mono fun p h => ?_⟩
  rw [h.1]
  exact h.2
end Motion
section Step
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
private theorem AnalyticGerm.extendOddly {f : P → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → AnalyticGerm S p₀ fun p => f p c)
    (c : Edge L n k j) :
    AnalyticGerm S p₀ fun p => Tower.extendOddly (f p) c := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.extendOddly <;> assumption
private theorem RegularFamily.meanDifferential_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V) (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => holLeftDifferential normalizedMean (V p) (B p) c := by
  refine AnalyticGerm.extendOddly (fun c hc => ?_) c
  exact (hV.logDeriv_germ T (Φ := fun W => normalizedMean W c)
    ((hV.twist T hB hBf).normalizedMean_germ T hc)).1
private theorem RegularFamily.drift_germ (T : StepHypotheses L n k j r) (hV : RegularFamily r S p₀ V)
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
  exact (hV.logDeriv_germ T
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((hV.twist T hB hBf).contour_germ T y hx')).1
private theorem AnalyticGerm.conj (hp : p₀ ∈ S) {g g' : P → ComplexMatrix2}
    (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g')
    (h0 : (g p₀).det ≠ 0) : AnalyticGerm S p₀ fun p => ComplexMatrix2.conjugateBy (g p) (g' p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.conjugateBy <;> assumption
private theorem RegularFamily.adjointAverage_germ (T : StepHypotheses L n k j r)
    (hV : RegularFamily r S p₀ V)
    {l : P → Vertex L n k j → ComplexMatrix2} (hl : ∀ x, AnalyticGerm S p₀ fun p => l p x)
    (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => adjointCubeAverage (V p) (l p) y := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold adjointCubeAverage
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x hx => ?_)
  obtain ⟨h₁, h₂⟩ := hV.contour_germ T y (hfin.mem_toFinset.1 hx)
  refine AnalyticGerm.conj hV.mem h₁ (hl x) ?_
  have h : (PeriodicLattice.complexMeanContourHolonomy (V p₀) y x).det = 1 :=
    h₂.self_of_nhdsWithin hV.mem
  rw [h]
  exact one_ne_zero
end Step
section Forms
variable {L n k i j : ℕ}
private structure OrientedLevels (L n k : ℕ) : Prop where
  orientation : ∀ i ≤ k, ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
private theorem edge_opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem OrientedLevels.opposite_pos (T : OrientedLevels L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
private theorem OrientedLevels.not_opposite_pos (T : OrientedLevels L n k) (hi : i ≤ k)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact h.2
  · exact absurd hb h.2
private theorem extendOddly_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
private theorem extendOddly_neg {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
private theorem extendOddly_opposite (T : OrientedLevels L n k) (hi : i ≤ k)
    (g : Edge L n k i → ComplexMatrix2) (b : Edge L n k i) :
    extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_neg (T.not_opposite_pos hi hb), extendOddly_pos hb, edge_opposite_opposite]
  · rw [extendOddly_pos (T.opposite_pos hi hb), extendOddly_neg hb, neg_neg]
private theorem transport_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) (h : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by
  simp only [tangentTransport, dif_pos h]
  rw [extendOddly_pos hc, dif_pos hc]
private theorem transport_opposite (T : OrientedLevels L n k) (X : ChainPoint L n k)
    (ξ : LevelForms L n k) (h : j < k) (b : Edge L n k (j + 1)) :
    tangentTransport X ξ (j + 1) b.opposite = -tangentTransport X ξ (j + 1) b := by
  simp only [tangentTransport, dif_pos h]
  exact extendOddly_opposite T h _ b
end Forms
section Norms
private theorem norm_one_matrix : ‖(1 : ComplexMatrix2)‖ = 1 := norm_one
private theorem norm_inv_le_two {g : ComplexMatrix2} (hg : g.det = 1) (h : ‖g - 1‖ ≤ 1 / 2) :
    ‖g⁻¹‖ ≤ 2 := by
  have hu : IsUnit g.det := by
    rw [hg]
    exact isUnit_one
  have e : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hu
  have e3 : g⁻¹ = 1 + (1 - g) * g⁻¹ := by
    have : (1 - g) * g⁻¹ = g⁻¹ - 1 := by rw [sub_mul, one_mul, e]
    rw [this]
    abel
  have h1 : ‖(1 - g) * g⁻¹‖ ≤ 1 / 2 * ‖g⁻¹‖ := by
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    exact h
  have h2 : ‖g⁻¹‖ ≤ 1 + 1 / 2 * ‖g⁻¹‖ := by
    calc ‖g⁻¹‖ = ‖1 + (1 - g) * g⁻¹‖ := congrArg norm e3
      _ ≤ ‖(1 : ComplexMatrix2)‖ + ‖(1 - g) * g⁻¹‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 2 * ‖g⁻¹‖ := by
        rw [norm_one_matrix]
        linarith
  linarith
abbrev _root_.YangMills.SharedProofs.p24015 := @norm_inv_le_two
private theorem norm_inv_sub_one_le {g : ComplexMatrix2} (hg : g.det = 1) (h : ‖g - 1‖ ≤ 1 / 2) :
    ‖g⁻¹ - 1‖ ≤ 2 * ‖g - 1‖ := by
  have hu : IsUnit g.det := by
    rw [hg]
    exact isUnit_one
  have e : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hu
  have e2 : g⁻¹ - 1 = -(g⁻¹ * (g - 1)) := by
    rw [mul_sub, e, mul_one]
    abel
  rw [e2, norm_neg]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_inv_le_two hg h) (norm_nonneg _))
abbrev _root_.YangMills.SharedProofs.p71492 := @norm_inv_sub_one_le
private theorem norm_le_three_halves {g : ComplexMatrix2} (h : ‖g - 1‖ ≤ 1 / 2) : ‖g‖ ≤ 3 / 2 := by
  have e : g = (g - 1) + 1 := by abel
  calc ‖g‖ = ‖(g - 1) + 1‖ := congrArg norm e
    _ ≤ ‖g - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
    _ ≤ 3 / 2 := by
      rw [norm_one_matrix]
      linarith
private theorem norm_conj_le {g : ComplexMatrix2} (hg : g.det = 1) (h : ‖g - 1‖ ≤ 1 / 2)
    (X : ComplexMatrix2) : ‖ComplexMatrix2.conjugateBy g X‖ ≤ 3 * ‖X‖ := by
  unfold ComplexMatrix2.conjugateBy
  have h1 := norm_le_three_halves h
  have h2 := norm_inv_le_two hg h
  calc ‖g * X * g⁻¹‖ ≤ ‖g‖ * ‖X‖ * ‖g⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 3 / 2 * ‖X‖ * 2 := by gcongr
    _ = 3 * ‖X‖ := by ring
private theorem conj_mem_traceless {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
private theorem matExp_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X : ComplexMatrix2, ‖X‖ < δ → ‖ComplexMatrix2.matExp X - 1‖ < ε := by
  have hc : ContinuousAt (fun X : ComplexMatrix2 => ComplexMatrix2.matExp X) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (0 : ComplexMatrix2)).continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc ε hε
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := h (x := X) (by simpa [dist_eq_norm] using hX)
  simpa [dist_eq_norm, ComplexMatrix2.matExp, NormedSpace.exp_zero] using this
abbrev _root_.YangMills.SharedProofs.p35343 := @matExp_near_one
private theorem norm_deriv_le_of_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℂ → E} {R C : ℝ} (hR : 0 < R) (hd : ∀ w, ‖w‖ < R → DifferentiableAt ℂ g w)
    (hb : ∀ w, ‖w‖ < R → ‖g w‖ ≤ C) : ‖deriv g 0‖ ≤ 2 * C / R := by
  have h2 : 0 < R / 2 := by positivity
  have hh : ∀ z ∈ Metric.closedBall (0 : ℂ) (R / 2), ‖z‖ < R := by
    intro z hz
    have : ‖z‖ ≤ R / 2 := by simpa [dist_eq_norm] using hz
    linarith
  have hdc : DiffContOnCl ℂ g (Metric.ball 0 (R / 2)) :=
    DifferentiableOn.diffContOnCl_ball
      (fun z hz => (hd z (hh z hz)).differentiableWithinAt) subset_rfl
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le h2 hdc
    fun z hz => hb z (hh z (Metric.sphere_subset_closedBall hz))
  calc ‖deriv g 0‖ ≤ C / (R / 2) := this
    _ = 2 * C / R := by field_simp
end Norms
section Line
variable {L n k j : ℕ} {r δ β : ℝ}
private def ExpSmallBelow (r δ : ℝ) : Prop :=
  ∀ X : ComplexMatrix2, ‖X‖ < δ → ‖ComplexMatrix2.matExp X - 1‖ < r / 8
private theorem det_of_mem_fields {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    (V b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V from hV).1 b (mem_univ b)
private theorem twisted_value_near (hr0 : 0 < r) (hr1 : r ≤ 1) (hδ : ExpSmallBelow r δ)
    {X g : ComplexMatrix2} (hX : ‖X‖ < δ) (hg : ‖g - 1‖ < r / 4) :
    ‖ComplexMatrix2.matExp (Complex.I • X) * g - 1‖ < r / 2 := by
  have h1 : ‖ComplexMatrix2.matExp (Complex.I • X) - 1‖ < r / 8 := by
    refine hδ _ ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    exact hX
  have h2 : ‖g‖ ≤ 3 / 2 := norm_le_three_halves (by linarith)
  have e : ComplexMatrix2.matExp (Complex.I • X) * g - 1 =
      (ComplexMatrix2.matExp (Complex.I • X) - 1) * g + (g - 1) := by
    rw [sub_mul, one_mul]
    abel
  rw [e]
  calc ‖(ComplexMatrix2.matExp (Complex.I • X) - 1) * g + (g - 1)‖
      ≤ ‖ComplexMatrix2.matExp (Complex.I • X) - 1‖ * ‖g‖ + ‖g - 1‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
    _ ≤ r / 8 * (3 / 2) + ‖g - 1‖ := by
        gcongr
    _ < r / 2 := by linarith
private theorem expTwist_near (hE : ComplexMatrix2.ExpLogEstimates) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hδ : ExpSmallBelow r δ) {A V : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n k j)
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV1 : ∀ b, ‖V b - 1‖ < r / 4) (hAb : ∀ b, ‖A b‖ < δ) (b : Edge L n k j) :
    ‖PeriodicLattice.expTwist A V b - 1‖ < r := by
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_pos hb]
    have := twisted_value_near hr0 hr1 hδ (hAb b) (hV1 b)
    linarith
  · rw [expTwist_of_not_pos hb]
    have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
    have h1 := twisted_value_near hr0 hr1 hδ (hAb b.opposite) (hV1 b.opposite)
    have hdet : (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite).det = 1 :=
      mul_mem_unitDet (matExp_mem_unitDet hE (ComplexMatrix2.traceless.smul_mem _ (hA.1 _ hr)))
        (det_of_mem_fields hV _)
    have := norm_inv_sub_one_le hdet (by linarith)
    linarith
private theorem analyticGerm_id {S : Set ℂ} {t₀ : ℂ} : AnalyticGerm S t₀ fun t : ℂ => t :=
  ⟨fun t => t, analyticAt_id, Eventually.of_forall fun _ => rfl⟩
private theorem norm_smul_form_lt (hβ : 0 < β) {B : Edge L n k j → ComplexMatrix2}
    (hBb : ∀ b, ‖B b‖ ≤ β) {t : ℂ} (ht : ‖t‖ < δ / β) (b : Edge L n k j) : ‖(t • B) b‖ < δ := by
  have h1 : ‖t‖ * β < δ := (lt_div_iff₀ hβ).1 ht
  calc ‖(t • B) b‖ = ‖t • B b‖ := rfl
    _ = ‖t‖ * ‖B b‖ := norm_smul _ _
    _ ≤ ‖t‖ * β := mul_le_mul_of_nonneg_left (hBb b) (norm_nonneg _)
    _ < δ := h1
private theorem line_regularFamily (T : StepHypotheses L n k j r) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hδ : ExpSmallBelow r δ) (hβ : 0 < β) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV1 : ∀ b, ‖V b - 1‖ < r / 4) (hB : B ∈ complexEdgeForms L n k j) (hBb : ∀ b, ‖B b‖ ≤ β)
    {t₀ : ℂ} (ht : ‖t₀‖ < δ / β) :
    RegularFamily r (Metric.ball 0 (δ / β)) t₀ fun t => PeriodicLattice.expTwist (t • B) V := by
  have hmem : t₀ ∈ Metric.ball (0 : ℂ) (δ / β) := by simpa using ht
  have hval : ∀ b, AnalyticGerm (Metric.ball (0 : ℂ) (δ / β)) t₀
      fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b := fun b =>
    (AnalyticGerm.exp hmem ((AnalyticGerm.const Complex.I).smul
      (analyticGerm_id.smul (AnalyticGerm.const (B b))))).mul (AnalyticGerm.const (V b))
  refine ⟨hmem, fun b => ?_, ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun z => (expTwist_of_pos hb).symm)
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      refine ((hval b.opposite).inv hmem ?_).congr
        (Eventually.of_forall fun z => (expTwist_of_not_pos hb).symm)
      have h : (ComplexMatrix2.matExp (Complex.I • (t₀ • B) b.opposite) * V b.opposite).det = 1 :=
        mul_mem_unitDet (matExp_mem_unitDet T.exp (ComplexMatrix2.traceless.smul_mem _
          (((complexEdgeForms L n k j).smul_mem t₀ hB).1 _ hr))) (det_of_mem_fields hV _)
      rw [h]
      exact one_ne_zero
  · exact Eventually.of_forall fun t =>
      expTwist_mem_fields T.exp T.xor ((complexEdgeForms L n k j).smul_mem t hB) hV
  · exact expTwist_near T.exp hr0 hr1 hδ ((complexEdgeForms L n k j).smul_mem t₀ hB) hV hV1
      (norm_smul_form_lt hβ hBb ht) b
private structure NearOneFunctional (r : ℝ) (Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2) :
    Prop where
  germ : ∀ {S : Set ℂ} {t₀ : ℂ} {U : ℂ → Edge L n k j → ComplexMatrix2}, RegularFamily r S t₀ U →
    AnalyticGerm S t₀ fun t => Φ (U t)
  near : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, (∀ b, ‖W b - 1‖ < r) →
    Φ W ∈ PeriodicLattice.complexGaugeGroup ∧ ‖Φ W - 1‖ < 1 / 2
private theorem AnalyticGerm.differentiableAt_of_open {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {S : Set ℂ} (hS : IsOpen S) {t₀ : ℂ} (ht : t₀ ∈ S) {g : ℂ → X}
    (h : AnalyticGerm S t₀ g) : DifferentiableAt ℂ g t₀ := by
  obtain ⟨H, hH, hev⟩ := h
  rw [hS.nhdsWithin_eq ht] at hev
  exact hH.differentiableAt.congr_of_eventuallyEq hev
private theorem logDeriv_facts (T : StepHypotheses L n k j r) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hδ0 : 0 < δ) (hδ : ExpSmallBelow r δ) (hβ : 0 < β)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hS : NearOneFunctional r Φ) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV1 : ∀ b, ‖V b - 1‖ < r / 4) (hB : B ∈ complexEdgeForms L n k j) (hBb : ∀ b, ‖B b‖ ≤ β) :
    ‖Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B‖ ≤
        2 / δ * β ∧
      Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B ∈
        ComplexMatrix2.traceless ∧
      Tower.logDirectionalDeriv ℝ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
        Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B := by
  have hs : 0 < δ / β := div_pos hδ0 hβ
  set f : ℂ → ComplexMatrix2 := fun t => Φ (PeriodicLattice.expTwist (t • B) V) with hf
  have hfd : ∀ t, ‖t‖ < δ / β → DifferentiableAt ℂ f t := fun t ht =>
    AnalyticGerm.differentiableAt_of_open Metric.isOpen_ball (by simpa using ht)
      (hS.germ (line_regularFamily T hr0 hr1 hδ hβ hV hV1 hB hBb ht))
  have hnear : ∀ t, ‖t‖ < δ / β →
      f t ∈ PeriodicLattice.complexGaugeGroup ∧ ‖f t - 1‖ < 1 / 2 := fun t ht =>
    hS.near _ (expTwist_mem_fields T.exp T.xor ((complexEdgeForms L n k j).smul_mem t hB) hV)
      (expTwist_near T.exp hr0 hr1 hδ ((complexEdgeForms L n k j).smul_mem t hB) hV hV1
        (norm_smul_form_lt hβ hBb ht))
  have f0 : Φ V = f 0 := by
    simp only [hf]
    rw [expTwist_zero_smul hV]
  have h00 : ‖(0 : ℂ)‖ < δ / β := by simpa using hs
  obtain ⟨-, hdl, heq, hm⟩ := T.curves (δ / β) hs f
    (fun t ht => (hnear t (by simpa using ht)).1) (hfd 0 h00)
  have key : Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
      Complex.I⁻¹ • (deriv f 0 * (f 0)⁻¹) := by
    rw [← heq, f0]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [key, norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
    have h1 : ‖deriv f 0‖ ≤ β / δ := by
      have e : deriv f 0 = deriv (fun t => f t - 1) 0 :=
        (deriv_sub_const (f := f) (1 : ComplexMatrix2)).symm
      rw [e]
      have h2 := norm_deriv_le_of_bound (g := fun t => f t - 1) (C := 1 / 2) hs
        (fun w hw => (hfd w hw).sub_const 1) (fun w hw => (hnear w hw).2.le)
      refine h2.trans (le_of_eq ?_)
      field_simp
    have h3 : ‖(f 0)⁻¹‖ ≤ 2 := norm_inv_le_two (hnear 0 h00).1 (hnear 0 h00).2.le
    calc ‖deriv f 0 * (f 0)⁻¹‖ ≤ ‖deriv f 0‖ * ‖(f 0)⁻¹‖ := norm_mul_le _ _
      _ ≤ β / δ * 2 := by gcongr
      _ = 2 / δ * β := by ring
  · rw [key]
    exact hm
  · set h : ℂ → ComplexMatrix2 := fun t => ComplexMatrix2.logSeries (f t * (f 0)⁻¹) with hh
    have h1 : HasDerivAt h (deriv h 0) 0 := hdl.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have h3 : HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h 0) 0 := by
      have := HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℂ) (h := fun t : ℝ => (t : ℂ)) (g₁ := h)
        (g₁' := deriv h 0) (h' := 1) (x := 0) (by simpa using h1) h2
      rw [one_smul] at this
      exact this
    have e1 : Tower.logDirectionalDeriv ℝ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
        Complex.I⁻¹ • deriv (fun t : ℝ => h (t : ℂ)) 0 := by
      rw [f0]
      rfl
    have e2 : Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
        Complex.I⁻¹ • deriv h 0 := by
      rw [f0]
      rfl
    rw [e1, e2, h3.deriv]
end Line
section Maps
variable {L n k j : ℕ} {r δ β : ℝ}
private theorem nearOne_mean (T : StepHypotheses L n k j r) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    NearOneFunctional r (fun W : Edge L n k j → ComplexMatrix2 => normalizedMean W c) where
  germ := fun hU => (hU.normalizedMean_germ T hc).1
  near := fun W hW hn => by
    have h := T.near_one W hW hn c hc
    exact ⟨h.2.1, h.2.2⟩
private theorem nearOne_contour (T : StepHypotheses L n k j r) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    NearOneFunctional r
      (fun W : Edge L n k j → ComplexMatrix2 => PeriodicLattice.complexMeanContourHolonomy W y x) where
  germ := fun hU => (hU.contour_germ T y hx).1
  near := fun W hW hn => by
    have hR : RegularFamily r (univ : Set ℂ) (0 : ℂ) (fun _ => W) :=
      ⟨mem_univ _, fun b => AnalyticGerm.const _, Eventually.of_forall fun _ => hW, hn⟩
    refine ⟨(hR.contour_germ T y hx).2.self_of_nhdsWithin (mem_univ _), ?_⟩
    have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
      ⟨0, add_sub_cancel_left _ _⟩
    have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
    exact (T.serve _ hc).contourMean_near_one W
      ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩,
        fun b _ => (hn b).trans_le T.le_radius⟩ y (Or.inl rfl) x hx
private theorem blockSum_norm_le (T : StepHypotheses L n k j r) (y : Vertex L n k (j + 1))
    {f : Vertex L n k j → ComplexMatrix2} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, ‖f x‖ ≤ K) :
    ‖PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, f x‖ ≤ K := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, norm_smul]
  have hc : (hfin.toFinset.card : ℝ) ≤ (L : ℝ) ^ 4 := by
    have h := T.count y
    rw [Set.ncard_eq_toFinset_card _ hfin] at h
    exact_mod_cast h
  have hL : (0 : ℝ) < L := by exact_mod_cast T.pos
  have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have e : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    unfold PeriodicLattice.inverseFourthPowerWeight
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos hL _), e]
  have hs : ‖∑ x ∈ hfin.toFinset, f x‖ ≤ (L : ℝ) ^ 4 * K := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x ∈ hfin.toFinset, ‖f x‖ ≤ ∑ _x ∈ hfin.toFinset, K :=
          Finset.sum_le_sum fun x hx => hf x (hfin.mem_toFinset.1 hx)
      _ = (hfin.toFinset.card : ℝ) * K := by simp
      _ ≤ (L : ℝ) ^ 4 * K := mul_le_mul_of_nonneg_right hc hK
  rw [hw]
  calc ((L : ℝ) ^ 4)⁻¹ * ‖∑ x ∈ hfin.toFinset, f x‖ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * K) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = K := by field_simp
private theorem blockSum_mem_traceless (T : StepHypotheses L n k j r) (y : Vertex L n k (j + 1))
    {f : Vertex L n k j → ComplexMatrix2}
    (hf : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      f x ∈ ComplexMatrix2.traceless) :
    PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, f x ∈
        ComplexMatrix2.traceless := by
  have := T.sites
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact ComplexMatrix2.traceless.smul_mem _
    (Submodule.sum_mem _ fun x hx => hf x (hfin.mem_toFinset.1 hx))
private theorem expTwist_congr {P : Set (Edge L n k j)} (hP : ∀ b ∈ P, b.opposite ∈ P)
    {A A' V V' : Edge L n k j → ComplexMatrix2} (hA : ∀ b ∈ P, A b = A' b)
    (hV : ∀ b ∈ P, V b = V' b) {b : Edge L n k j} (hb : b ∈ P) :
    PeriodicLattice.expTwist A V b = PeriodicLattice.expTwist A' V' b := by
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_of_pos hp, expTwist_of_pos hp, hA b hb, hV b hb]
  · rw [expTwist_of_not_pos hp, expTwist_of_not_pos hp, hA _ (hP b hb), hV _ (hP b hb)]
private theorem doubleBlock_opposite (c : Edge L n k (j + 1)) :
    ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  fun b hb => ⟨hb.2, hb.1⟩
private theorem smul_congr {P : Set (Edge L n k j)} {B B' : Edge L n k j → ComplexMatrix2} (t : ℂ)
    (h : ∀ b ∈ P, B b = B' b) : ∀ b ∈ P, (t • B) b = (t • B') b := fun b hb => by
  show t • B b = t • B' b
  rw [h b hb]
private theorem mean_logDeriv_congr (T : StepHypotheses L n k j r) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' B B' : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), V b = V' b)
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), B b = B' b) :
    Tower.logDirectionalDeriv ℂ
        (fun X => normalizedMean (PeriodicLattice.expTwist X V) c)
        (normalizedMean V c) B =
      Tower.logDirectionalDeriv ℂ
        (fun X => normalizedMean (PeriodicLattice.expTwist X V') c)
        (normalizedMean V' c) B' := by
  have h0 := T.reads_average c hc V V' hV
  have e : (fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean
        (PeriodicLattice.expTwist (t • B) V) c * (normalizedMean V c)⁻¹)) =
      fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean
        (PeriodicLattice.expTwist (t • B') V') c * (normalizedMean V' c)⁻¹) := by
    funext t
    rw [T.reads_average c hc _ (PeriodicLattice.expTwist (t • B') V')
      fun b hb => expTwist_congr (doubleBlock_opposite c) (smul_congr _ hB) hV hb, h0]
  show Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean
        (PeriodicLattice.expTwist (t • B) V) c * (normalizedMean V c)⁻¹)) 0 =
      Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries (normalizedMean
        (PeriodicLattice.expTwist (t • B') V') c * (normalizedMean V' c)⁻¹)) 0
  rw [e]
private theorem contour_logDeriv_congr (T : StepHypotheses L n k j r) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hδ0 : 0 < δ) (hδ : ExpSmallBelow r δ) (hβ : 0 < β) (y : Vertex L n k (j + 1))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V V' B B' : Edge L n k j → ComplexMatrix2}
    (hV0 : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV1 : ∀ b, ‖V b - 1‖ < r / 4) (hB0 : B ∈ complexEdgeForms L n k j) (hBb : ∀ b, ‖B b‖ ≤ β)
    (hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), V b = V' b)
    (hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
      Set (Edge L n k j)), B b = B' b) :
    Tower.logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B =
      Tower.logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V') y x)
        (PeriodicLattice.complexMeanContourHolonomy V' y x) B' := by
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
      (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hR : r ≤ polydiscRadius L := T.le_radius
  have e0 : PeriodicLattice.complexMeanContourHolonomy V' y x =
      PeriodicLattice.complexMeanContourHolonomy V y x :=
    T.reads y x hx _ hc hy V hV0 (fun b => by have := hV1 b; linarith) V'
      fun b hb => (hV b hb).symm
  have hs : 0 < δ / β := div_pos hδ0 hβ
  have e : (fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist (t • B) V) y x *
          (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹)) =ᶠ[𝓝 0]
      fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist (t • B') V') y x *
          (PeriodicLattice.complexMeanContourHolonomy V' y x)⁻¹) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hs] with t ht
    have ht' : ‖t‖ < δ / β := by simpa using ht
    have hconf := expTwist_mem_fields T.exp T.xor ((complexEdgeForms L n k j).smul_mem t hB0) hV0
    have hnear := expTwist_near T.exp hr0 hr1 hδ ((complexEdgeForms L n k j).smul_mem t hB0) hV0
      hV1 (norm_smul_form_lt hβ hBb ht')
    have e1 : PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B') V') y x =
        PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x :=
      T.reads y x hx _ hc hy _ hconf (fun b => (hnear b).trans_le hR) _
        fun b hb => (expTwist_congr (doubleBlock_opposite _) (smul_congr t hB) hV hb).symm
    rw [e1, e0]
  show Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries
        (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x *
          (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹)) 0 =
      Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries
        (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B') V') y x *
          (PeriodicLattice.complexMeanContourHolonomy V' y x)⁻¹)) 0
  rw [e.deriv_eq]
private theorem logDeriv_zero_form (T : StepHypotheses L n k j r) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hδ0 : 0 < δ) (hδ : ExpSmallBelow r δ) {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hS : NearOneFunctional r Φ) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hV1 : ∀ b, ‖V b - 1‖ < r / 4) :
    Tower.logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) 0 = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have h := (logDeriv_facts T hr0 hr1 hδ0 hδ (β := ε * δ / 2) (by positivity) hS hV hV1
    (complexEdgeForms L n k j).zero_mem (fun b => by
      have : 0 ≤ ε * δ / 2 := by positivity
      simpa using this)).1
  have e : 2 / δ * (ε * δ / 2) = ε := by field_simp
  rw [e] at h
  linarith
end Maps
section Numbers
private def transportBound (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => c * transportBound c j + 1
private def driftBound (c c' : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => 3 * driftBound c c' j + c' * transportBound c j
private def readRadius (s : ℝ) : ℕ → ℝ
  | 0 => 4
  | j + 1 => readRadius s j + s + 11
private theorem transportBound_pos {c : ℝ} (hc : 0 ≤ c) (j : ℕ) : 0 < transportBound c j := by
  induction j with
  | zero => exact one_pos
  | succ j ih =>
    have : 0 ≤ c * transportBound c j := mul_nonneg hc ih.le
    simp only [transportBound]
    linarith
private theorem driftBound_nonneg {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (j : ℕ) :
    0 ≤ driftBound c c' j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have : 0 ≤ c' * transportBound c j := mul_nonneg hc' (transportBound_pos hc j).le
    simp only [driftBound]
    linarith
private theorem readRadius_nonneg {s : ℝ} (hs : 0 ≤ s) (j : ℕ) : 0 ≤ readRadius s j := by
  induction j with
  | zero => simp [readRadius]
  | succ j ih =>
    simp only [readRadius]
    linarith
private theorem readRadius_mono {s : ℝ} (hs : 0 ≤ s) {j j' : ℕ} (h : j ≤ j') :
    readRadius s j ≤ readRadius s j' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    simp only [readRadius]
    linarith
end Numbers
section Main
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private structure InductionSetup (L n k : ℕ) [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (r δ ρ s : ℝ) : Prop where
  r0 : 0 < r
  r1 : r ≤ 1
  δ0 : 0 < δ
  exp : ExpSmallBelow r δ
  s0 : 0 ≤ s
  tower : OrientedLevels L n k
  level : ∀ j < k, StepHypotheses L n k j r
  conf : ∀ j ≤ k, ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    levelField (complexChainPoint z) j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  analytic : ∀ j ≤ k, ∀ b : Edge L n k j,
    AnalyticOnNhd ℂ (fun z => levelField (complexChainPoint z) j b) (Metric.ball 0 ρ)
  small : ∀ j ≤ k, ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ b : Edge L n k j,
    ‖levelField (complexChainPoint z) j b - 1‖ < r / 4
  reads : ∀ j ≤ k, ∀ b : Edge L n k j, ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    ∀ z' ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell b.source) ≤ s → z i = z' i) →
      levelField (complexChainPoint z) j b = levelField (complexChainPoint z') j b
  noise_analytic : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
    AnalyticOnNhd ℂ (fun z => (complexChainPoint z).noise i c) (Metric.ball 0 ρ)
  noise_det : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ (i : Fin k)
    (c : PositiveEdge L n k (i + 1)), ((complexChainPoint z).noise i c).det = 1
  noise_small : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ (i : Fin k)
    (c : PositiveEdge L n k (i + 1)), ‖(complexChainPoint z).noise i c - 1‖ ≤ 1 / 2
  noise_reads : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)) (z z' : TripleCoordIndex L n k → ℂ),
    (∀ a : Fin 3, z (.inl (.inr ⟨i, (a, c)⟩)) = z' (.inl (.inr ⟨i, (a, c)⟩))) →
      (complexChainPoint z).noise i c = (complexChainPoint z').noise i c
  dzero : ∀ y : Vertex L n k k, cellDist y y = 0
  dsymm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  dtri : ∀ y y' y'' : Vertex L n k k, cellDist y y'' ≤ cellDist y y' + cellDist y' y''
  dblock : ∀ j < k, ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
    (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
      cellDist (levelVertexCell x) (levelVertexCell y) ≤ 3
  dbond : ∀ j ≤ k, ∀ b : Edge L n k j,
    cellDist (levelVertexCell b.source) (levelVertexCell b.target) ≤ 4
variable {r δ ρ s : ℝ}
private theorem localValue_mono {g : (TripleCoordIndex L n k → ℂ) → ComplexMatrix2} {K K' R R' : ℝ}
    {y y₀ : Vertex L n k k} (h : IsLocalValueNearCell g ρ K R y y₀) (hK : K ≤ K') (hR : R ≤ R') :
    IsLocalValueNearCell g ρ K' R' y y₀ where
  holomorphic := h.holomorphic
  traceless := h.traceless
  norm_le := fun z hz => (h.norm_le z hz).trans hK
  depends_near := fun z hz z' hz' a => h.depends_near z hz z' hz' fun i hi => a i (hi.trans hR)
  eq_zero_of_far := fun hy => h.eq_zero_of_far (hR.trans_lt hy)
private theorem localValue_neg (D : InductionSetup L n k r δ ρ s)
    {g : (TripleCoordIndex L n k → ℂ) → ComplexMatrix2} {K R : ℝ}
    {y y' y₀ : Vertex L n k k} (h : IsLocalValueNearCell g ρ K R y y₀)
    (hd : cellDist y' y ≤ 4) :
    IsLocalValueNearCell (fun z => -g z) ρ K (R + 4) y' y₀ where
  holomorphic := fun z hz => (h.holomorphic z hz).neg
  traceless := fun z hz => ComplexMatrix2.traceless.neg_mem (h.traceless z hz)
  norm_le := fun z hz => by
    show ‖-g z‖ ≤ K
    rw [norm_neg]
    exact h.norm_le z hz
  depends_near := fun z hz z' hz' a => by
    show -g z = -g z'
    rw [h.depends_near z hz z' hz' fun i hi => a i ?_]
    have h1 := D.dtri (tripleCoordIndexCell i) y y'
    rw [D.dsymm y y'] at h1
    linarith
  eq_zero_of_far := fun hy z hz => by
    show -g z = 0
    rw [h.eq_zero_of_far ?_ z hz, neg_zero]
    have h1 := D.dtri y' y y₀
    linarith
private theorem analyticGerm_of_analyticOnNhd {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : (TripleCoordIndex L n k → ℂ) → X} (h : AnalyticOnNhd ℂ g (Metric.ball 0 ρ))
    {p₀ : TripleCoordIndex L n k → ℂ} (hp : p₀ ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) :
    AnalyticGerm (Metric.ball 0 ρ) p₀ g :=
  ⟨g, h p₀ hp, Eventually.of_forall fun _ => rfl⟩
private theorem analyticOnNhd_of_germ {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : (TripleCoordIndex L n k → ℂ) → X}
    (h : ∀ p₀ ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, AnalyticGerm (Metric.ball 0 ρ) p₀ g) :
    AnalyticOnNhd ℂ g (Metric.ball 0 ρ) := fun p₀ hp => by
  obtain ⟨H, hH, hev⟩ := h p₀ hp
  rw [Metric.isOpen_ball.nhdsWithin_eq hp] at hev
  exact hH.congr (hev.mono fun _ h => h.symm)
private theorem eventually_of_ball {p₀ : TripleCoordIndex L n k → ℂ}
    {q : (TripleCoordIndex L n k → ℂ) → Prop}
    (h : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, q z) :
    ∀ᶠ z in 𝓝[Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ] p₀, q z := by
  filter_upwards [self_mem_nhdsWithin] with z hz using h z hz
private theorem InductionSetup.regularFamily (D : InductionSetup L n k r δ ρ s) {j : ℕ} (h : j < k)
    {p₀ : TripleCoordIndex L n k → ℂ} (hp : p₀ ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) :
    RegularFamily r (Metric.ball 0 ρ) p₀ fun z => levelField (complexChainPoint z) j where
  mem := hp
  germ := fun b => analyticGerm_of_analyticOnNhd (D.analytic j h.le b) hp
  conf := eventually_of_ball (D.conf j h.le)
  near := fun b => by
    have := D.small j h.le p₀ hp b
    have := D.r0
    show ‖_‖ < r
    linarith
private theorem cellDist_doubleBlock_le (D : InductionSetup L n k r δ ρ s) {j : ℕ} (h : j < k)
    {c : Edge L n k (j + 1)}
    {b : Edge L n k j} (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) :
    cellDist (levelVertexCell b.source) (levelVertexCell c.source) ≤ 7 := by
  rcases hb.1 with h1 | h1
  · have := D.dblock j h c.source b.source h1
    linarith
  · have h2 := D.dblock j h c.target b.source h1
    have h3 := D.dbond (j + 1) h c
    rw [D.dsymm] at h3
    have h4 := D.dtri (levelVertexCell b.source) (levelVertexCell c.target) (levelVertexCell c.source)
    linarith
private theorem transport_odd (T : OrientedLevels L n k) (X : ChainPoint L n k) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    tangentTransport X ξ j b.opposite = -tangentTransport X ξ j b := by
  cases j with
  | zero => exact (ξ.1).2.2 b
  | succ j => exact transport_opposite T X ξ hj b
variable {ξ : LevelForms L n k} {y₀ : Vertex L n k k} {β K Kd R : ℝ} {j : ℕ}
private theorem transport_mem_forms (D : InductionSetup L n k r δ ρ s) (hj : j ≤ k)
    (IH : ∀ b : Edge L n k j,
      IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ j b)
      ρ K R (levelVertexCell b.source) y₀)
    {z : TripleCoordIndex L n k → ℂ} (hz : z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) :
    tangentTransport (complexChainPoint z) ξ j ∈ complexEdgeForms L n k j :=
  ⟨fun b _ => (IH b).traceless z hz, fun b => transport_odd D.tower _ ξ hj b⟩
private theorem transport_step (D : InductionSetup L n k r δ ρ s) (hK : 0 < K) (hR : 0 ≤ R)
    (hcar : LevelFormsSupportedInCell y₀ ξ) (hbd : LevelFormsBounded β ξ) (h : j < k)
    (IH : ∀ b : Edge L n k j,
      IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ j b)
      ρ K R (levelVertexCell b.source) y₀)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ (j + 1) c) ρ
      (3 * (2 / δ * K) + β) (R + s + 7) (levelVertexCell c.source) y₀ := by
  have T := D.level j h
  have hS := nearOne_mean T hc
  have hs0 := D.s0
  have hlog := fun (z : TripleCoordIndex L n k → ℂ)
      (hz : z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) =>
    logDeriv_facts T D.r0 D.r1 D.δ0 D.exp hK hS (D.conf j h.le z hz) (D.small j h.le z hz)
      (transport_mem_forms D h.le IH hz) (fun b => (IH b).norm_le z hz)
  have hval : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      tangentTransport (complexChainPoint z) ξ (j + 1) c =
        ComplexMatrix2.conjugateBy ((complexChainPoint z).noise ⟨j, h⟩ ⟨c, hc⟩)
          (Tower.logDirectionalDeriv ℂ
            (fun X => normalizedMean
              (PeriodicLattice.expTwist X (levelField (complexChainPoint z) j)) c)
            (normalizedMean (levelField (complexChainPoint z) j) c)
            (tangentTransport (complexChainPoint z) ξ j)) +
          (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := fun z hz => by
    rw [transport_pos _ _ h hc]
    congr 2
    exact (extendOddly_pos hc).trans (hlog z hz).2.2
  have hdetn := fun (z : TripleCoordIndex L n k → ℂ)
      (hz : z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) => D.noise_det z hz ⟨j, h⟩ ⟨c, hc⟩
  refine ⟨analyticOnNhd_of_germ fun p₀ hp => ?_, fun z hz => ?_, fun z hz => ?_,
    fun z hz z' hz' a => ?_, fun hy z hz => ?_⟩
  · have hV := D.regularFamily h hp
    have h₁ := hV.meanDifferential_germ T
      (fun b => analyticGerm_of_analyticOnNhd (IH b).holomorphic hp)
      (eventually_of_ball fun z hz => transport_mem_forms D h.le IH hz) c
    have h₂ := AnalyticGerm.conj hp
      (analyticGerm_of_analyticOnNhd (D.noise_analytic ⟨j, h⟩ ⟨c, hc⟩) hp) h₁ (by
      rw [hdetn p₀ hp]
      exact one_ne_zero)
    refine (h₂.add (AnalyticGerm.const ((ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c))).congr
      (eventually_of_ball fun z hz => ?_)
    rw [hval z hz]
    congr 2
    exact extendOddly_pos hc
  · show tangentTransport (complexChainPoint z) ξ (j + 1) c ∈ ComplexMatrix2.traceless
    rw [hval z hz]
    exact ComplexMatrix2.traceless.add_mem (conj_mem_traceless (hdetn z hz) (hlog z hz).2.1)
      ((ξ.2 ⟨j, h⟩).2.1 c hc).2
  · show ‖tangentTransport (complexChainPoint z) ξ (j + 1) c‖ ≤ _
    rw [hval z hz]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hbd.level_le ⟨j, h⟩ c))
    refine (norm_conj_le (hdetn z hz) (D.noise_small z hz _ _) _).trans ?_
    have := (hlog z hz).1
    linarith
  · show tangentTransport (complexChainPoint z) ξ (j + 1) c =
      tangentTransport (complexChainPoint z') ξ (j + 1) c
    have hn := D.noise_reads ⟨j, h⟩ ⟨c, hc⟩ z z' fun aa =>
      a (.inl (.inr ⟨⟨j, h⟩, (aa, ⟨c, hc⟩)⟩)) (by
        show cellDist (levelVertexCell c.source) (levelVertexCell c.source) ≤ _
        rw [D.dzero]
        linarith)
    have hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        levelField (complexChainPoint z) j b = levelField (complexChainPoint z') j b := fun b hb =>
      D.reads j h.le b z hz z' hz' fun i hi => a i (by
        have h1 := cellDist_doubleBlock_le D h hb
        have h2 := D.dtri (tripleCoordIndexCell i) (levelVertexCell b.source)
          (levelVertexCell c.source)
        linarith)
    have hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        tangentTransport (complexChainPoint z) ξ j b =
          tangentTransport (complexChainPoint z') ξ j b := fun b hb =>
      (IH b).depends_near z hz z' hz' fun i hi => a i (by
        have h1 := cellDist_doubleBlock_le D h hb
        have h2 := D.dtri (tripleCoordIndexCell i) (levelVertexCell b.source)
          (levelVertexCell c.source)
        linarith)
    rw [hval z hz, hval z' hz', hn, mean_logDeriv_congr T hc hV hB]
  · show tangentTransport (complexChainPoint z) ξ (j + 1) c = 0
    have hne : levelVertexCell c.source ≠ y₀ := fun e => by
      rw [e, D.dzero] at hy
      linarith
    have hxc : (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c = 0 :=
      hcar.2 ⟨j, h⟩ ⟨c, hc⟩ hne
    have hB0 : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        tangentTransport (complexChainPoint z) ξ j b = (0 : Edge L n k j → ComplexMatrix2) b :=
      fun b hb =>
      (IH b).eq_zero_of_far (by
        have h1 := cellDist_doubleBlock_le D h hb
        rw [D.dsymm] at h1
        have h2 := D.dtri (levelVertexCell c.source) (levelVertexCell b.source) y₀
        linarith) z hz
    rw [hval z hz, mean_logDeriv_congr T hc (fun _ _ => rfl) hB0,
      logDeriv_zero_form T D.r0 D.r1 D.δ0 D.exp hS (D.conf j h.le z hz) (D.small j h.le z hz), hxc]
    simp [ComplexMatrix2.conjugateBy]
end Main
section Drift
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
variable {r δ ρ s : ℝ} {ξ : LevelForms L n k} {y₀ : Vertex L n k k} {β K Kd R : ℝ} {j : ℕ}
private theorem cellDist_forward_doubleBlock_le (D : InductionSetup L n k r δ ρ s) (h : j < k)
    {y : Vertex L n k (j + 1)}
    {b : Edge L n k j} (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock
      (PeriodicLattice.Bond.forwardFrom y 0) : Set (Edge L n k j))) :
    cellDist (levelVertexCell b.source) (levelVertexCell y) ≤ 7 := by
  have h1 := cellDist_doubleBlock_le D h hb
  have e : (PeriodicLattice.Bond.forwardFrom y 0).source = y := rfl
  rwa [e] at h1
private theorem chainDrift_succ (X : ChainPoint L n k) (ξ : LevelForms L n k) (j : ℕ)
    (y : Vertex L n k (j + 1)) :
    chainDrift X ξ (j + 1) y = adjointCubeAverage (levelField X j) (chainDrift X ξ j) y +
      contourLogDrift (levelField X j) (tangentTransport X ξ j) y := rfl
set_option maxHeartbeats 1000000 in
private theorem drift_step (D : InductionSetup L n k r δ ρ s) (hK : 0 < K) (hKd : 0 ≤ Kd)
    (hR : 0 ≤ R) (h : j < k)
    (IM : ∀ b : Edge L n k j,
      IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ j b)
      ρ K R (levelVertexCell b.source) y₀)
    (ID : ∀ x : Vertex L n k j,
      IsLocalValueNearCell (fun z => chainDrift (complexChainPoint z) ξ j x)
      ρ Kd R (levelVertexCell x) y₀)
    (y : Vertex L n k (j + 1)) :
    IsLocalValueNearCell (fun z => chainDrift (complexChainPoint z) ξ (j + 1) y) ρ
      (3 * Kd + 2 / δ * K) (R + s + 7) (levelVertexCell y) y₀ := by
  have T := D.level j h
  have hs0 := D.s0
  have hr0 := D.r0
  have hδ0 := D.δ0
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
      (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hlog := fun (z : TripleCoordIndex L n k → ℂ)
      (hz : z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) (x : Vertex L n k j)
      (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) =>
    logDeriv_facts T D.r0 D.r1 D.δ0 D.exp hK (nearOne_contour T y hx) (D.conf j h.le z hz)
      (D.small j h.le z hz) (transport_mem_forms D h.le IM hz) (fun b => (IM b).norm_le z hz)
  have hnear := fun (z : TripleCoordIndex L n k → ℂ)
      (hz : z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ) (x : Vertex L n k j)
      (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) =>
    (nearOne_contour T y hx).near _ (D.conf j h.le z hz) (fun b => by
      have := D.small j h.le z hz b
      linarith)
  refine ⟨analyticOnNhd_of_germ fun p₀ hp => ?_, fun z hz => ?_, fun z hz => ?_,
    fun z hz z' hz' a => ?_, fun hy' z hz => ?_⟩
  · have hV := D.regularFamily h hp
    exact ((hV.adjointAverage_germ T
      (fun x => analyticGerm_of_analyticOnNhd (ID x).holomorphic hp) y).add
      (hV.drift_germ T (fun b => analyticGerm_of_analyticOnNhd (IM b).holomorphic hp)
        (eventually_of_ball fun z hz => transport_mem_forms D h.le IM hz) y)).congr
      (Eventually.of_forall fun z => (chainDrift_succ _ ξ j y).symm)
  · show chainDrift (complexChainPoint z) ξ (j + 1) y ∈ ComplexMatrix2.traceless
    rw [chainDrift_succ]
    exact ComplexMatrix2.traceless.add_mem
      (blockSum_mem_traceless T y fun x hx =>
        conj_mem_traceless (hnear z hz x hx).1 ((ID x).traceless z hz))
      (blockSum_mem_traceless T y fun x hx => (hlog z hz x hx).2.1)
  · show ‖chainDrift (complexChainPoint z) ξ (j + 1) y‖ ≤ _
    rw [chainDrift_succ]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine blockSum_norm_le T y (by positivity) fun x hx => ?_
      refine (norm_conj_le (hnear z hz x hx).1 (hnear z hz x hx).2.le _).trans ?_
      have := (ID x).norm_le z hz
      linarith
    · exact blockSum_norm_le T y (by positivity) fun x hx => (hlog z hz x hx).1
  · have hV : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)),
        levelField (complexChainPoint z) j b = levelField (complexChainPoint z') j b := fun b hb =>
      D.reads j h.le b z hz z' hz' fun i hi => a i (by
        have h1 := cellDist_forward_doubleBlock_le D h hb
        have h2 := D.dtri (tripleCoordIndexCell i) (levelVertexCell b.source) (levelVertexCell y)
        linarith)
    have hB : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)),
        tangentTransport (complexChainPoint z) ξ j b =
          tangentTransport (complexChainPoint z') ξ j b := fun b hb =>
      (IM b).depends_near z hz z' hz' fun i hi => a i (by
        have h1 := cellDist_forward_doubleBlock_le D h hb
        have h2 := D.dtri (tripleCoordIndexCell i) (levelVertexCell b.source) (levelVertexCell y)
        linarith)
    have hL : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        chainDrift (complexChainPoint z) ξ j x = chainDrift (complexChainPoint z') ξ j x :=
      fun x hx =>
      (ID x).depends_near z hz z' hz' fun i hi => a i (by
        have h1 := D.dblock j h y x hx
        have h2 := D.dtri (tripleCoordIndexCell i) (levelVertexCell x) (levelVertexCell y)
        linarith)
    have hC : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.complexMeanContourHolonomy (levelField (complexChainPoint z) j) y x =
          PeriodicLattice.complexMeanContourHolonomy (levelField (complexChainPoint z') j) y x :=
      fun x hx =>
      T.reads y x hx _ hc hy _ (D.conf j h.le z' hz') (fun b => by
        have := D.small j h.le z' hz' b
        have h3 := T.le_radius
        show ‖_‖ < _
        linarith) _ fun b hb => hV b hb
    show chainDrift (complexChainPoint z) ξ (j + 1) y = chainDrift (complexChainPoint z') ξ (j + 1) y
    rw [chainDrift_succ, chainDrift_succ]
    have e1 : adjointCubeAverage (levelField (complexChainPoint z) j)
        (chainDrift (complexChainPoint z) ξ j) y =
        adjointCubeAverage (levelField (complexChainPoint z') j)
          (chainDrift (complexChainPoint z') ξ j) y := by
      unfold adjointCubeAverage
      refine congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
        (finsum_mem_congr rfl fun x hx => ?_)
      rw [hC x hx, hL x hx]
    have e2 : contourLogDrift (levelField (complexChainPoint z) j)
        (tangentTransport (complexChainPoint z) ξ j) y =
        contourLogDrift (levelField (complexChainPoint z') j)
          (tangentTransport (complexChainPoint z') ξ j) y := by
      unfold contourLogDrift
      refine congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
        (finsum_mem_congr rfl fun x hx => ?_)
      exact contour_logDeriv_congr T D.r0 D.r1 D.δ0 D.exp hK y hx (D.conf j h.le z hz)
        (D.small j h.le z hz) (transport_mem_forms D h.le IM hz) (fun b => (IM b).norm_le z hz) hV hB
    rw [e1, e2]
  · have hL : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        chainDrift (complexChainPoint z) ξ j x = 0 := fun x hx =>
      (ID x).eq_zero_of_far (by
        have h1 := D.dblock j h y x hx
        rw [D.dsymm] at h1
        have h2 := D.dtri (levelVertexCell y) (levelVertexCell x) y₀
        linarith) z hz
    have hB0 : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock (PeriodicLattice.Bond.forwardFrom y 0) :
        Set (Edge L n k j)),
        tangentTransport (complexChainPoint z) ξ j b = (0 : Edge L n k j → ComplexMatrix2) b :=
      fun b hb =>
      (IM b).eq_zero_of_far (by
        have h1 := cellDist_forward_doubleBlock_le D h hb
        rw [D.dsymm] at h1
        have h2 := D.dtri (levelVertexCell y) (levelVertexCell b.source) y₀
        linarith) z hz
    show chainDrift (complexChainPoint z) ξ (j + 1) y = 0
    rw [chainDrift_succ]
    have e1 : adjointCubeAverage (levelField (complexChainPoint z) j)
        (chainDrift (complexChainPoint z) ξ j) y = 0 := by
      unfold adjointCubeAverage
      rw [finsum_mem_congr rfl fun x hx => (by
        rw [hL x hx]
        simp [ComplexMatrix2.conjugateBy] :
        ComplexMatrix2.conjugateBy
          (PeriodicLattice.complexMeanContourHolonomy (levelField (complexChainPoint z) j) y x)
          (chainDrift (complexChainPoint z) ξ j x) = 0)]
      simp
    have e2 : contourLogDrift (levelField (complexChainPoint z) j)
        (tangentTransport (complexChainPoint z) ξ j) y = 0 := by
      unfold contourLogDrift
      rw [finsum_mem_congr rfl fun x hx => (by
        rw [contour_logDeriv_congr T D.r0 D.r1 D.δ0 D.exp hK y hx (D.conf j h.le z hz)
          (D.small j h.le z hz) (transport_mem_forms D h.le IM hz) (fun b => (IM b).norm_le z hz)
          (fun _ _ => rfl) hB0]
        exact logDeriv_zero_form T D.r0 D.r1 D.δ0 D.exp (nearOne_contour T y hx)
          (D.conf j h.le z hz) (D.small j h.le z hz) :
        Tower.logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy
            (PeriodicLattice.expTwist X (levelField (complexChainPoint z) j)) y x)
          (PeriodicLattice.complexMeanContourHolonomy (levelField (complexChainPoint z) j) y x)
          (tangentTransport (complexChainPoint z) ξ j) = 0)]
      simp
    rw [e1, e2, add_zero]
private theorem transport_zero (D : InductionSetup L n k r δ ρ s)
    (hcar : LevelFormsSupportedInCell y₀ ξ)
    (hbd : LevelFormsBounded β ξ) (b : Edge L n k 0) :
    IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ 0 b) ρ β 4
      (levelVertexCell b.source) y₀ := by
  have hval : ∀ X : ChainPoint L n k,
      tangentTransport X ξ 0 b = (ξ.1 : Edge L n k 0 → ComplexMatrix2) b :=
    fun _ => rfl
  refine ⟨fun z _ => ?_, fun z _ => ?_, fun z _ => ?_, fun z _ z' _ _ => ?_, fun hy z _ => ?_⟩
  · exact (analyticAt_const (v := (ξ.1 : Edge L n k 0 → ComplexMatrix2) b)).congr
      (Eventually.of_forall fun z => (hval _).symm)
  · show tangentTransport _ ξ 0 b ∈ ComplexMatrix2.traceless
    rw [hval]
    by_cases hb : b.IsPositivelyOriented
    · exact ((ξ.1).2.1 b hb).2
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      have e := (ξ.1).2.2 b.opposite
      rw [PeriodicLattice.Bond.opposite_opposite] at e
      rw [e]
      exact ComplexMatrix2.traceless.neg_mem ((ξ.1).2.1 _ hr).2
  · show ‖tangentTransport _ ξ 0 b‖ ≤ β
    rw [hval]
    exact hbd.bottom_le b
  · show tangentTransport _ ξ 0 b = tangentTransport _ ξ 0 b
    rw [hval, hval]
  · show tangentTransport _ ξ 0 b = 0
    rw [hval]
    have hd := D.dbond 0 (Nat.zero_le k) b
    by_cases hb : b.IsPositivelyOriented
    · refine hcar.1 ⟨b, hb⟩ fun e => ?_
      have e' : levelVertexCell b.source = y₀ := e
      rw [e', D.dzero] at hy
      norm_num at hy
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
      have e := (ξ.1).2.2 b.opposite
      rw [PeriodicLattice.Bond.opposite_opposite] at e
      rw [e, neg_eq_zero]
      refine hcar.1 ⟨b.opposite, hr⟩ fun e₁ => ?_
      have e' : levelVertexCell b.target = y₀ := e₁
      rw [e'] at hd
      linarith
private theorem levelInduction (D : InductionSetup L n k r δ ρ s) (hβ : 0 < β)
    (hcar : LevelFormsSupportedInCell y₀ ξ) (hbd : LevelFormsBounded β ξ) : ∀ j ≤ k,
    (∀ b : Edge L n k j,
      IsLocalValueNearCell (fun z => tangentTransport (complexChainPoint z) ξ j b) ρ
      (transportBound (3 * (2 / δ)) j * β) (readRadius s j) (levelVertexCell b.source) y₀) ∧
    ∀ y : Vertex L n k j,
      IsLocalValueNearCell (fun z => chainDrift (complexChainPoint z) ξ j y) ρ
      (driftBound (3 * (2 / δ)) (2 / δ) j * β) (readRadius s j) (levelVertexCell y) y₀ := by
  have hδ0 := D.δ0
  have hs0 := D.s0
  have hc₁ : 0 ≤ 3 * (2 / δ) := by positivity
  have hc₂ : 0 ≤ 2 / δ := by positivity
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun b => ?_, fun y => ?_⟩
    · have := transport_zero D hcar hbd b
      simpa [transportBound, readRadius] using this
    · have hval : ∀ X : ChainPoint L n k, chainDrift X ξ 0 y = 0 := fun _ => rfl
      refine ⟨fun z _ => ?_, fun z _ => ?_, fun z _ => ?_, fun z _ z' _ _ => ?_, fun _ z _ => ?_⟩
      · exact (analyticAt_const (v := (0 : ComplexMatrix2))).congr
          (Eventually.of_forall fun z => (hval _).symm)
      · show chainDrift _ ξ 0 y ∈ ComplexMatrix2.traceless
        rw [hval]
        exact ComplexMatrix2.traceless.zero_mem
      · show ‖chainDrift _ ξ 0 y‖ ≤ _
        rw [hval]
        simp [driftBound]
      · show chainDrift _ ξ 0 y = chainDrift _ ξ 0 y
        rw [hval, hval]
      · exact hval _
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨IM, ID⟩ := ih h.le
    have hm := transportBound_pos hc₁ j
    have hK : 0 < transportBound (3 * (2 / δ)) j * β := mul_pos hm hβ
    have hKd : 0 ≤ driftBound (3 * (2 / δ)) (2 / δ) j * β :=
      mul_nonneg (driftBound_nonneg hc₁ hc₂ j) hβ.le
    have hR := readRadius_nonneg hs0 j
    have eK : 3 * (2 / δ * (transportBound (3 * (2 / δ)) j * β)) + β =
        transportBound (3 * (2 / δ)) (j + 1) * β := by
      simp only [transportBound]
      ring
    refine ⟨fun b => ?_, fun y => ?_⟩
    · by_cases hb : b.IsPositivelyOriented
      · have := transport_step D hK hR hcar hbd h IM hb
        rw [eK] at this
        exact localValue_mono this le_rfl (by simp only [readRadius]; linarith)
      · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
        have h1 := transport_step D hK hR hcar hbd h IM hr
        rw [eK] at h1
        have h2 := localValue_neg D h1 (y' := levelVertexCell b.source) (D.dbond (j + 1) hj b)
        have e : (fun z => tangentTransport (complexChainPoint z) ξ (j + 1) b) =
            fun z => -tangentTransport (complexChainPoint z) ξ (j + 1) b.opposite := by
          funext z
          have e₁ := transport_odd D.tower (complexChainPoint z) ξ hj b.opposite
          rw [PeriodicLattice.Bond.opposite_opposite] at e₁
          exact e₁
        rw [e]
        refine localValue_mono h2 le_rfl (le_of_eq ?_)
        simp only [readRadius]
        ring
    · have h1 := drift_step D hK hKd hR h IM ID y
      have eK' : 3 * (driftBound (3 * (2 / δ)) (2 / δ) j * β) +
          2 / δ * (transportBound (3 * (2 / δ)) j * β) =
          driftBound (3 * (2 / δ)) (2 / δ) (j + 1) * β := by
        simp only [driftBound]
        ring
      rw [eK'] at h1
      exact localValue_mono h1 le_rfl (by simp only [readRadius]; linarith)
end Drift
section Noise
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private def noiseGenerator (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (z : TripleCoordIndex L n k → ℂ) : ComplexMatrix2 :=
  Complex.I • ∑ a, z (.inl (.inr ⟨i, (a, c)⟩)) • ComplexMatrix2.pauliFamily a
private theorem noise_eq (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (z : TripleCoordIndex L n k → ℂ) :
    (complexChainPoint z).noise i c = ComplexMatrix2.matExp (noiseGenerator i c z) := by
  show ComplexMatrix2.matExp (Complex.I • complexLevelValues z i c) * 1 = _
  rw [mul_one]
  rfl
private theorem noise_analyticOnNhd (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (s : Set (TripleCoordIndex L n k → ℂ)) :
    AnalyticOnNhd ℂ (fun z => (complexChainPoint z).noise i c) s := fun z _ => by
  let T : (TripleCoordIndex L n k → ℂ) →L[ℂ] ComplexMatrix2 := ∑ a : Fin 3,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : TripleCoordIndex L n k => ℂ)
      (.inl (.inr ⟨i, (a, c)⟩))).smulRight (Complex.I • ComplexMatrix2.pauliFamily a)
  have hT : ∀ z, noiseGenerator i c z = T z := fun z => by
    simp only [noiseGenerator, T, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm]
  have h : AnalyticAt ℂ (fun z => ComplexMatrix2.matExp (T z)) z :=
    AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℂ) _)
      (T.analyticAt z)
  refine h.congr (Eventually.of_forall fun z' => ?_)
  show _ = (complexChainPoint z').noise i c
  rw [noise_eq, hT]
private theorem noise_det_eq_one (hE : ComplexMatrix2.ExpLogEstimates) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) (z : TripleCoordIndex L n k → ℂ) :
    ((complexChainPoint z).noise i c).det = 1 := by
  rw [noise_eq]
  refine matExp_mem_unitDet hE (ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (ConjugationInvariants.pauliFamily_mem_traceless a)))
private theorem noise_near_one {δ₂ τ : ℝ} (hτ : τ = ∑ a, ‖ComplexMatrix2.pauliFamily a‖)
    (hδ₂ : ∀ X : ComplexMatrix2, ‖X‖ < δ₂ → ‖ComplexMatrix2.matExp X - 1‖ < 1 / 2) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) {z : TripleCoordIndex L n k → ℂ} (hz : τ * ‖z‖ < δ₂) :
    ‖(complexChainPoint z).noise i c - 1‖ ≤ 1 / 2 := by
  rw [noise_eq]
  refine (hδ₂ _ ?_).le
  refine lt_of_le_of_lt ?_ hz
  unfold noiseGenerator
  rw [norm_smul, Complex.norm_I, one_mul, hτ, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z _) (norm_nonneg _)
private theorem noise_depends (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (z z' : TripleCoordIndex L n k → ℂ)
    (h : ∀ a : Fin 3, z (.inl (.inr ⟨i, (a, c)⟩)) = z' (.inl (.inr ⟨i, (a, c)⟩))) :
    (complexChainPoint z).noise i c = (complexChainPoint z').noise i c := by
  rw [noise_eq, noise_eq]
  unfold noiseGenerator
  simp only [h]
end Noise
end TransportDriftLocality
open TransportDriftLocality Tower Matrices in
theorem TransportAndDriftAreLocal.holds
    (hF : LevelFieldsHolomorphicAndLocal)
    (hNear : NormalizedMeanNearOne)
    (hAvg : Tower.SmoothingNearIdentity)
    (hCont : Tower.PairContourIndependence.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hChart : Tower.LeftChartFields.Claim)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hRead : NormalizedMeanLocal)
    (hBlocks : Tower.BlockStructure)
    (hCells : CellDistBlockBounds) :
    TransportAndDriftAreLocal := by
  intro L hL k hk
  obtain ⟨ρ₀, C₀, s, hρ₀, hC₀, hs, H⟩ := hF L hL k hk
  obtain ⟨ρ₂, hρ₂, hnear⟩ := hNear L hL
  have hrad := (hAvg.1 L hL).2.2
  obtain ⟨r, hr, hr₀, hr₂, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ polydiscRadius L ∧ r ≤ ρ₂ ∧
      r ≤ 1 :=
    ⟨min (min (polydiscRadius L) ρ₂) 1, lt_min (lt_min hrad.pos hρ₂) one_pos,
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  obtain ⟨δ, hδ0, hδ⟩ := matExp_near_one (ε := r / 8) (by positivity)
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := matExp_near_one (ε := 1 / 2) (by norm_num)
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = ∑ a, ‖ComplexMatrix2.pauliFamily a‖ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact Finset.sum_nonneg fun a _ => norm_nonneg _
  obtain ⟨ρ, hρ, hρ₁, hρ₃, hρ₄⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ C₀ * ρ < r / 4 ∧ τ * ρ < δ₂ := by
    refine ⟨min ρ₀ (min (r / (8 * (C₀ + 1))) (δ₂ / (2 * (τ + 1)))), by positivity,
      min_le_left _ _, ?_, ?_⟩
    · have h1 : min ρ₀ (min (r / (8 * (C₀ + 1))) (δ₂ / (2 * (τ + 1)))) ≤ r / (8 * (C₀ + 1)) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have h2 : C₀ * (r / (8 * (C₀ + 1))) ≤ r / 8 := by
        rw [show C₀ * (r / (8 * (C₀ + 1))) = r / 8 * (C₀ / (C₀ + 1)) by field_simp]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]
        linarith
      have h3 := mul_le_mul_of_nonneg_left h1 hC₀
      linarith
    · have h1 : min ρ₀ (min (r / (8 * (C₀ + 1))) (δ₂ / (2 * (τ + 1)))) ≤ δ₂ / (2 * (τ + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h2 : τ * (δ₂ / (2 * (τ + 1))) ≤ δ₂ / 2 := by
        rw [show τ * (δ₂ / (2 * (τ + 1))) = δ₂ / 2 * (τ / (τ + 1)) by field_simp]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]
        linarith
      have h3 := mul_le_mul_of_nonneg_left h1 hτ0
      linarith
  have hc₁ : 0 ≤ 3 * (2 / δ) := by positivity
  have hc₂ : 0 ≤ 2 / δ := by positivity
  have hsum : ∀ j ≤ k, transportBound (3 * (2 / δ)) j + driftBound (3 * (2 / δ)) (2 / δ) j ≤
      ∑ i ∈ Finset.range (k + 1),
        (transportBound (3 * (2 / δ)) i + driftBound (3 * (2 / δ)) (2 / δ) i) :=
    fun j hj => Finset.single_le_sum (f := fun i =>
      transportBound (3 * (2 / δ)) i + driftBound (3 * (2 / δ)) (2 / δ) i)
      (fun i _ => add_nonneg (transportBound_pos hc₁ i).le (driftBound_nonneg hc₁ hc₂ i))
      (Finset.mem_range.2 (by omega))
  refine ⟨ρ, ∑ i ∈ Finset.range (k + 1),
      (transportBound (3 * (2 / δ)) i + driftBound (3 * (2 / δ)) (2 / δ) i),
    readRadius s k, hρ, Finset.sum_nonneg fun i _ => add_nonneg (transportBound_pos hc₁ i).le
      (driftBound_nonneg hc₁ hc₂ i), readRadius_nonneg hs k, ?_⟩
  filter_upwards [H, eventually_gt_atTop 0] with n Hn hn
  intro _ _ _ _ _ _ _ _ _ P y₀ ξ β hβ hcar hbd j hj
  obtain ⟨-, f2, f3, -⟩ := Hn P
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hbonds : ∀ j, Finite (Edge L n k j) := fun j => PeriodicLattice.instFiniteBond _
  have hsites : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite (by omega) n _
  have hxor : ∀ j ≤ k, ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun j hj b => hO L n k hL hn hk j hj b
  have hsub : Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ ⊆ Metric.ball 0 ρ₀ :=
    Metric.ball_subset_ball hρ₁
  have hnorm : ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, ‖z‖ < ρ := fun z hz => by
    simpa using hz
  obtain ⟨dn, dz, ds, dt, db, dbb⟩ := hCells L hL n k hn hk
  have D : InductionSetup L n k r δ ρ s :=
    { r0 := hr
      r1 := hr1
      δ0 := hδ0
      exp := hδ
      s0 := hs
      tower := ⟨hxor⟩
      level := fun j hj =>
        { bonds := hbonds j
          sites := hsites j
          xor := hxor j hj.le
          exp := hE
          curves := hChart.2.1
          near_one := fun V hV hb c hc => by
            have h := hnear n k j hn hj V hV (fun b => (hb b).trans_le hr₂) c hc
            exact ⟨h.2.1, h.2.2.2.1, h.2.2.1⟩
          le_radius := hr₀
          pos := by omega
          count := fun y => by
            have hb := ((hBlocks L k (j + 1) hL hk (by omega) (by omega)).1 n hn).1 y
            have hc := hb.2.2.1
            have hfin : (PeriodicLattice.unitBlock y : Set (PeriodicLattice.FourTorus L n)).Finite :=
              Set.finite_of_ncard_pos (by
                rw [hc]
                positivity)
            rw [← hc, ← Set.ncard_image_of_injective _ Subtype.val_injective]
            exact Set.ncard_le_ncard (by
              rintro _ ⟨x, hx, rfl⟩
              exact hx) hfin
          reads_average := fun c hc W W' h => (hRead L hL n k j hn hj c hc W W' h).2.2
          serve := fun c hc => hrad.periodic n k j hn hj c hc
          reads := fun y x hx c hc hy W hW hWn W' hr' =>
            ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
              (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2 }
      conf := fun j hj z hz => f2 j hj z (hsub hz)
      analytic := fun j hj b => (f3 j hj b).1.mono hsub
      small := fun j hj z hz b => by
        have h1 := (f3 j hj b).2.1 z (hsub hz)
        have h2 : C₀ * ‖z‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hnorm z hz).le hC₀
        exact lt_of_le_of_lt (h1.trans h2) hρ₃
      reads := fun j hj b z hz z' hz' a => (f3 j hj b).2.2 z (hsub hz) z' (hsub hz') a
      noise_analytic := fun i c => noise_analyticOnNhd i c _
      noise_det := fun z _ i c => noise_det_eq_one hE i c z
      noise_small := fun z hz i c => noise_near_one hτ hδ₂ i c (by
        have h2 : τ * ‖z‖ ≤ τ * ρ := mul_le_mul_of_nonneg_left (hnorm z hz).le hτ0
        linarith)
      noise_reads := noise_depends
      dzero := dz
      dsymm := ds
      dtri := dt
      dblock := db
      dbond := dbb }
  obtain ⟨IM, ID⟩ := levelInduction D hβ hcar hbd j hj
  have hrs := readRadius_mono hs hj
  have hm := hsum j hj
  have hd := driftBound_nonneg hc₁ hc₂ j
  have hm0 := (transportBound_pos hc₁ j).le
  exact ⟨fun b => localValue_mono (IM b) (mul_le_mul_of_nonneg_right (by linarith) hβ.le) hrs,
    fun y => localValue_mono (ID y) (mul_le_mul_of_nonneg_right (by linarith) hβ.le) hrs⟩
end YangMills.Construction.RunningCouplingSlope
end
