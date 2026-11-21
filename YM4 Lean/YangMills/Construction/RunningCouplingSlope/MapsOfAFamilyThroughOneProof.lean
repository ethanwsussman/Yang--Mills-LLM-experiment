import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.RunningCouplingSlope.CovarianceOfTheFunctionOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.MapsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FamilyThroughUnit
open Tower
open Matrices
section Germs
variable {P X Y : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
private def GermOn (S : Set P) (p₀ : P) (g : P → X) : Prop :=
  ∃ H : P → X, AnalyticAt ℂ H p₀ ∧ ∀ᶠ p in 𝓝[S] p₀, g p = H p
variable {S : Set P} {p₀ : P} {g g' : P → X}
private theorem GermOn.congr (h : GermOn S p₀ g) (he : ∀ᶠ p in 𝓝[S] p₀, g p = g' p) : GermOn S p₀ g' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.congr_eventually <;> assumption
private theorem GermOn.const (x : X) : GermOn S p₀ fun _ => x := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.const <;> assumption
private theorem GermOn.add (h : GermOn S p₀ g) (h' : GermOn S p₀ g') : GermOn S p₀ fun p => g p + g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.add <;> assumption
private theorem GermOn.neg (h : GermOn S p₀ g) : GermOn S p₀ fun p => -g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.neg <;> assumption
private theorem GermOn.sub (h : GermOn S p₀ g) (h' : GermOn S p₀ g') : GermOn S p₀ fun p => g p - g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sub <;> assumption
private theorem GermOn.clm (T : X →L[ℂ] Y) (h : GermOn S p₀ g) : GermOn S p₀ fun p => T (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.map_clm <;> assumption
private theorem GermOn.finset_sum {α : Type} (s : Finset α) {f : α → P → X}
    (h : ∀ a ∈ s, GermOn S p₀ (f a)) : GermOn S p₀ fun p => ∑ a ∈ s, f a p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sum <;> assumption
private theorem GermOn.value_eq (hp : p₀ ∈ S) {H : P → X} (hev : ∀ᶠ p in 𝓝[S] p₀, g p = H p) : g p₀ = H p₀ :=
  hev.self_of_nhdsWithin hp
private theorem GermOn.tendsto (hp : p₀ ∈ S) (h : GermOn S p₀ g) : Tendsto g (𝓝[S] p₀) (𝓝 (g p₀)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.tendsto_self <;> assumption
private theorem GermOn.comp (hp : p₀ ∈ S) (h : GermOn S p₀ g) {f : X → Y} (hf : AnalyticAt ℂ f (g p₀)) :
    GermOn S p₀ fun p => f (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_analytic <;> assumption
private theorem GermOn.comp_family {τ : Type} [Fintype τ] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hp : p₀ ∈ S)
    {Ψ : P → τ → E} (hΨ : ∀ i, GermOn S p₀ fun p => Ψ p i) {D : Set (τ → E)}
    (hD : ∀ᶠ p in 𝓝[S] p₀, Ψ p ∈ D) {φ : (τ → E) → Y} {G : (τ → E) → Y}
    (hG : AnalyticAt ℂ G (Ψ p₀)) (hGev : ∀ᶠ y in 𝓝[D] (Ψ p₀), φ y = G y) :
    GermOn S p₀ fun p => φ (Ψ p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_tuple <;> assumption
end Germs
section Scalars
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P}
private theorem GermOn.smul {f : P → ℂ} {g : P → X} (hf : GermOn S p₀ f) (hg : GermOn S p₀ g) :
    GermOn S p₀ fun p => f p • g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.smul <;> assumption
private theorem GermOn.inv_scalar (hp : p₀ ∈ S) {f : P → ℂ} (hf : GermOn S p₀ f) (h0 : f p₀ ≠ 0) :
    GermOn S p₀ fun p => (f p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.inv_complex <;> assumption
private theorem GermOn.sqrt (hp : p₀ ∈ S) {f : P → ℂ} (hf : GermOn S p₀ f) (h0 : f p₀ ∈ Complex.slitPlane) :
    GermOn S p₀ fun p => (f p) ^ (1 / 2 : ℂ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sqrt <;> assumption
end Scalars
section Matrices
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
variable {S : Set P} {p₀ : P} {g g' : P → ComplexMatrix2}
private theorem GermOn.mul (h : GermOn S p₀ g) (h' : GermOn S p₀ g') : GermOn S p₀ fun p => g p * g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matMul <;> assumption
private def matrixEntryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)
private theorem GermOn.entry (h : GermOn S p₀ g) (r s : Fin 2) : GermOn S p₀ fun p => g p r s := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matEntry <;> assumption
private theorem GermOn.det (h : GermOn S p₀ g) : GermOn S p₀ fun p => (g p).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.det <;> assumption
private def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] }
private theorem GermOn.inv (hp : p₀ ∈ S) (h : GermOn S p₀ g) (h0 : (g p₀).det ≠ 0) :
    GermOn S p₀ fun p => (g p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matInv <;> assumption
private theorem GermOn.list_prod {α : Type} (V : P → α → ComplexMatrix2) (hV : ∀ a, GermOn S p₀ fun p => V p a)
    (l : List α) : GermOn S p₀ fun p => (l.map (V p)).prod := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.listProd <;> assumption
private theorem GermOn.matExp (hp : p₀ ∈ S) (h : GermOn S p₀ g) :
    GermOn S p₀ fun p => ComplexMatrix2.matExp (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matExp <;> assumption
end Matrices
section Derivative
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {S : Set P} {p₀ : P} {g : P × ℂ → X}
private theorem eventually_slice_of_prod {q : P × ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ), q z) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ᶠ t in 𝓝 (0 : ℂ), q (p, t) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.eventually_curry_prod_zero <;> assumption
private theorem GermOn.differentiableAt_slice (hg : GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    ∀ᶠ p in 𝓝[S] p₀, DifferentiableAt ℂ (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.differentiable_slice <;> assumption
private theorem GermOn.deriv_slice (hg : GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    GermOn S p₀ fun p => deriv (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.deriv_slice <;> assumption
end Derivative
section Pairs
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P} {g : P → X}
private theorem tendsto_fst_prodWithin :
    Tendsto (Prod.fst : P × ℂ → P) (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) (𝓝[S] p₀) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_fst_prod_zero <;> assumption
private theorem tendsto_pair_zero : Tendsto (fun p : P => ((p, 0) : P × ℂ)) (𝓝[S] p₀)
    (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_pair_zero <;> assumption
private theorem GermOn.lift_fst (h : GermOn S p₀ g) :
    GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => g z.1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_fst <;> assumption
private theorem germOn_snd : GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => z.2 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.analyticGerm_snd <;> assumption
private theorem GermOn.restrict_zero {g : P × ℂ → X} (h : GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    GermOn S p₀ fun p => g (p, 0) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.restrict_zero <;> assumption
end Pairs
private theorem mem_slitPlane_of_sqrt_near_one {z : ℂ} (h : ‖z ^ (1 / 2 : ℂ) - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.mem_slitPlane_of_sqrt_near_one <;> assumption
section ExpTwist
variable {L n k j : ℕ}
private theorem expTwist_of_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem expTwist_mem_fieldsIn (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.expTwist_mem_fieldsIn <;> assumption
end ExpTwist
section Level
variable {L n k j : ℕ}
private theorem expTwist_zero_smul {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (A : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • A) U = U := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.expTwist_zero_smul <;> assumption
private structure LevelInputs (L n k j : ℕ) (r : ℝ) : Prop where
  edge_finite : Finite (Edge L n k j)
  vertex_finite : Finite (Vertex L n k j)
  orientation : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  expLog : ComplexMatrix2.ExpLogEstimates
  curveLog : ∀ s : ℝ, 0 < s → LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 s)
    PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  mean_near : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  le_polydisc : r ≤ polydiscRadius L
  admissible : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → PolydiscIsAdmissible (polydiscRadius L) c
  local_contour : ∀ (y : Vertex L n k (j + 1)),
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
  germ : ∀ b, GermOn S p₀ fun p => V p b
  fields : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  near : ∀ b, ComplexMatrix2.operatorNorm (V p₀ b - 1) < r
variable {V : P → Edge L n k j → ComplexMatrix2}
private theorem RegularFamily.fields_self (hV : RegularFamily r S p₀ V) :
    V p₀ ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  hV.fields.self_of_nhdsWithin hV.mem
private theorem RegularFamily.det_eq (hV : RegularFamily r S p₀ V) (b : Edge L n k j) :
    (V p₀ b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p₀) from
    hV.fields_self).1 b (mem_univ b)
private theorem RegularFamily.eventually_near (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < r := by
  have := T.edge_finite
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝[S] p₀) (𝓝 ‖V p₀ b - 1‖) :=
    (((hV.germ b).tendsto hV.mem).sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near b)
private theorem det_pathHolonomy {U : Edge L n k j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (l : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy U l).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.det_pathHolonomy <;> assumption
private theorem RegularFamily.holonomy_germ (hV : RegularFamily r S p₀ V) (l : List (Edge L n k j)) :
    GermOn S p₀ fun p => PeriodicLattice.pathHolonomy (V p) l :=
  GermOn.list_prod V hV.germ l
private theorem RegularFamily.contourHolonomy_germ (hV : RegularFamily r S p₀ V) (c : Edge L n k (j + 1))
    (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    GermOn S p₀ fun p => contourHolonomy (V p) c x π := by
  refine ((hV.holonomy_germ _).mul (hV.holonomy_germ _)).mul ((hV.holonomy_germ _).inv hV.mem ?_)
  rw [det_pathHolonomy hV.det_eq]
  exact one_ne_zero
private theorem RegularFamily.contourMean_germ (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) : GermOn S p₀ fun p => contourMean (V p) c := by
  have := T.vertex_finite
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold RunningCouplingSlope.contourMean
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact (GermOn.const _).smul (GermOn.finset_sum _ fun x _ => GermOn.finset_sum _ fun π _ =>
    hV.contourHolonomy_germ c x π)
private theorem RegularFamily.normalizedMean_germ (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    GermOn S p₀ (fun p => normalizedMean (V p) c) ∧
      ∀ᶠ p in 𝓝[S] p₀, normalizedMean (V p) c ∈ PeriodicLattice.complexGaugeGroup := by
  have hn := T.mean_near _ hV.fields_self hV.near c hc
  have hm := hV.contourMean_germ T c
  have hs : (Matrix.det (RunningCouplingSlope.contourMean (V p₀) c)) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hn.1
  have hl : GermOn S p₀ fun p => meanRadius (V p) c := hm.det.sqrt hV.mem hs
  have hl0 : meanRadius (V p₀) c ≠ 0 := by
    intro h
    have := hn.1
    rw [h] at this
    norm_num at this
  refine ⟨(hl.inv_scalar hV.mem hl0).smul hm, ?_⟩
  filter_upwards [hV.fields, hV.eventually_near T] with p h₁ h₂
  exact (T.mean_near _ h₁ h₂ c hc).2
private theorem extendFromPositive_restrict {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, W b.opposite = (W b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
private theorem RegularFamily.complexContour_germ (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    GermOn S p₀ (fun p => PeriodicLattice.complexMeanContourHolonomy (V p) y x) ∧
      ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy (V p) y x ∈
        PeriodicLattice.complexGaugeGroup := by
  classical
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented := ⟨0, add_sub_cancel_left _ _⟩
  set c := PeriodicLattice.Bond.forwardFrom y 0 with hcdef
  have hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hadm := T.admissible c hc
  obtain ⟨inst, hol⟩ := (hadm.holomorphic_contourMean y hy x hx).1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hpoly : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r) →
        W ∈ nearIdentityPolydisc (polydiscRadius L) c := by
    intro W hW hn
    have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
    exact ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩,
      fun b _ => (hn b).trans_le T.le_polydisc⟩
  have hD : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p) ∈
      PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc (polydiscRadius L) c := by
    filter_upwards [hV.fields, hV.eventually_near T] with p h₁ h₂
    exact ⟨_, hpoly _ h₁ h₂, rfl⟩
  have h0 := hD.self_of_nhdsWithin hV.mem
  obtain ⟨G, hG, hGev⟩ := hol.2.2 _ h0
  have hfam := GermOn.comp_family hV.mem
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
    filter_upwards [hV.fields, hV.eventually_near T] with p h₁ h₂
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p) := h₁
    exact T.local_contour y x hx c hc hy _ h₁' (fun b => (h₂ b).trans_le T.le_polydisc) _
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
private theorem RegularFamily.expTwist_family (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, GermOn S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) :
    RegularFamily r (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z => PeriodicLattice.expTwist (z.2 • B z.1) (V z.1) := by
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.mem, mem_univ _⟩
  have hval : ∀ b, GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z : P × ℂ => ComplexMatrix2.matExp (Complex.I • (z.2 • B z.1) b) * V z.1 b := fun b =>
    (GermOn.matExp hmem ((GermOn.const Complex.I).smul (germOn_snd.smul (hB b).lift_fst))).mul
      (hV.germ b).lift_fst
  refine ⟨hmem, fun b => ?_, ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun z => (expTwist_of_positive hb).symm)
    · refine ((hval b.opposite).inv hmem ?_).congr
        (Eventually.of_forall fun z => (expTwist_of_not_positive hb).symm)
      have h0 : ComplexMatrix2.matExp
          (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) = 1 := by
        simp [ComplexMatrix2.matExp]
      show (ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) *
        V p₀ b.opposite).det ≠ 0
      rw [h0, one_mul, hV.det_eq]
      exact one_ne_zero
  · refine (tendsto_fst_prodWithin.eventually (hV.fields.and hBf)).mono fun z h => ?_
    exact expTwist_mem_fieldsIn T.expLog T.orientation (Submodule.smul_mem _ z.2 h.2) h.1
  · show ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist ((0 : ℂ) • B p₀) (V p₀) b - 1) < r
    rw [expTwist_zero_smul hV.fields_self]
    exact hV.near b
private theorem RegularFamily.logDeriv_germ (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : GermOn (S ×ˢ univ) ((p₀, 0) : P × ℂ)
        (fun z => Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1))) ∧
      ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ),
        Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1)) ∈ PeriodicLattice.complexGaugeGroup) :
    GermOn S p₀ (fun p => Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p)) ∧
      ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) ∈ ComplexMatrix2.traceless := by
  obtain ⟨hg, hgrp⟩ := hΦ
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.mem, mem_univ _⟩
  have hD := hg.deriv_slice
  have h0 := hg.restrict_zero
  have hdet : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det ≠ 0 := by
    have h : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det = 1 := hgrp.self_of_nhdsWithin hmem
    rw [h]
    exact one_ne_zero
  have hinv := h0.inv hV.mem hdet
  have hmain := (GermOn.const (S := S) (p₀ := p₀) Complex.I⁻¹).smul (hD.mul hinv)
  have hall : ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) =
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∧
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∈ ComplexMatrix2.traceless := by
    filter_upwards [eventually_slice_of_prod hgrp, hg.differentiableAt_slice, hV.fields] with p h₁ h₂ h₃
    obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.1 h₁
    have hc := T.curveLog s hs (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p)))
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
private theorem GermOn.extendOddly {f : P → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → GermOn S p₀ fun p => f p c) (c : Edge L n k j) :
    GermOn S p₀ fun p => Tower.extendOddly (f p) c := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.extendOddly <;> assumption
private theorem RegularFamily.holLeftDifferential_germ (T : LevelInputs L n k j r)
    (hV : RegularFamily r S p₀ V) (hB : ∀ b, GermOn S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    GermOn S p₀ fun p => holLeftDifferential normalizedMean (V p) (B p) c := by
  refine GermOn.extendOddly (fun c hc => ?_) c
  exact (hV.logDeriv_germ T (Φ := fun W => RunningCouplingSlope.normalizedMean W c)
    ((hV.expTwist_family T hB hBf).normalizedMean_germ T hc)).1
private theorem RegularFamily.contourLogDrift_germ (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, GermOn S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (y : Vertex L n k (j + 1)) :
    GermOn S p₀ fun p => contourLogDrift (V p) (B p) y := by
  have := T.vertex_finite
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold contourLogDrift
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (GermOn.const _).smul (GermOn.finset_sum _ fun x hx => ?_)
  have hx' := hfin.mem_toFinset.1 hx
  exact (hV.logDeriv_germ T
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((hV.expTwist_family T hB hBf).complexContour_germ T y hx')).1
private theorem GermOn.conjugateBy (hp : p₀ ∈ S) {g g' : P → ComplexMatrix2} (h : GermOn S p₀ g)
    (h' : GermOn S p₀ g') (h0 : (g p₀).det ≠ 0) :
    GermOn S p₀ fun p => ComplexMatrix2.conjugateBy (g p) (g' p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.conjugateBy <;> assumption
private theorem RegularFamily.adjointCubeAverage_germ (T : LevelInputs L n k j r)
    (hV : RegularFamily r S p₀ V)
    {l : P → Vertex L n k j → ComplexMatrix2} (hl : ∀ x, GermOn S p₀ fun p => l p x)
    (y : Vertex L n k (j + 1)) :
    GermOn S p₀ fun p => adjointCubeAverage (V p) (l p) y := by
  have := T.vertex_finite
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold adjointCubeAverage
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (GermOn.const _).smul (GermOn.finset_sum _ fun x hx => ?_)
  obtain ⟨h₁, h₂⟩ := hV.complexContour_germ T y (hfin.mem_toFinset.1 hx)
  refine GermOn.conjugateBy hV.mem h₁ (hl x) ?_
  have h : (PeriodicLattice.complexMeanContourHolonomy (V p₀) y x).det = 1 :=
    h₂.self_of_nhdsWithin hV.mem
  rw [h]
  exact one_ne_zero
end Step
section Forms
variable {L n k i j : ℕ}
private structure OrientedTower (L n k : ℕ) : Prop where
  orientation : ∀ i ≤ k, ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
private theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) = ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conjugateBy_real_smul (g : ComplexMatrix2) (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
private theorem isUnit_det_of_compact {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem inv_mem_compact {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem edge_opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem OrientedTower.opposite_positive (T : OrientedTower L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
private theorem OrientedTower.not_opposite_positive (T : OrientedTower L n k) (hi : i ≤ k)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact h.2
  · exact absurd hb h.2
private theorem extendOddly_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
private theorem extendOddly_neg {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
private theorem extendOddly_opposite (T : OrientedTower L n k) (hi : i ≤ k) (g : Edge L n k i → ComplexMatrix2)
    (b : Edge L n k i) : extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_neg (T.not_opposite_positive hi hb), extendOddly_pos hb, edge_opposite_opposite]
  · rw [extendOddly_pos (T.opposite_positive hi hb), extendOddly_neg hb, neg_neg]
private theorem levelField_succ (X : ChainPoint L n k) (h : j < k) :
    levelField X (j + 1) = fieldOfPositiveValues fun c =>
      X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp only [levelField, dif_pos h]
private theorem odd_ext (T : OrientedTower L n k) (hi : j ≤ k) {B B' : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b.opposite = -B b) (hB' : ∀ b, B' b.opposite = -B' b)
    (h : ∀ b, b.IsPositivelyOriented → B b = B' b) : B = B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := T.opposite_positive hi hb
    have e₁ := hB b.opposite
    have e₂ := hB' b.opposite
    rw [edge_opposite_opposite] at e₁ e₂
    rw [e₁, e₂, h _ hr]
private theorem tangentTransport_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) (h : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by
  simp only [tangentTransport, dif_pos h]
  rw [extendOddly_pos hc, dif_pos hc]
private theorem tangentTransport_opposite (T : OrientedTower L n k) (X : ChainPoint L n k)
    (ξ : LevelForms L n k) (h : j < k) (b : Edge L n k (j + 1)) :
    tangentTransport X ξ (j + 1) b.opposite = -tangentTransport X ξ (j + 1) b := by
  simp only [tangentTransport, dif_pos h]
  exact extendOddly_opposite T h _ b
private theorem gaugeOrbitValues_snd (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (i : Fin k) :
    (gaugeOrbitValues X l).2 i = extendOddly fun c =>
      open Classical in
        if hc : c.IsPositivelyOriented then
          ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) l c.source) -
            restrictVertexFunction (i + 1) l c.source
        else 0 := rfl
private theorem edgeForm_mem_complex {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j) :
    B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
private structure GoodAtStep (V : Edge L n k j → ComplexMatrix2) : Prop where
  small : V ∈ smallComplexFields L n k j
  compact : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup
  differential : ∃ P : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k (j + 1),
    ∀ B : edgeFormSpace L n k j,
    (P B : Edge L n k (j + 1) → ComplexMatrix2) =
      holLeftDifferential normalizedMean V (B : Edge L n k j → ComplexMatrix2)
  real_eq : ∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
    leftDifferential normalizedMean V B c = holLeftDifferential normalizedMean V B c
  drift : ∃ T : edgeFormSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1),
    ∀ B : edgeFormSpace L n k j,
    (T B : Vertex L n k (j + 1) → ComplexMatrix2) = contourLogDrift V (B : Edge L n k j → ComplexMatrix2)
  average : ∃ T : vertexFunctionSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1),
    ∀ l : vertexFunctionSpace L n k j,
    (T l : Vertex L n k (j + 1) → ComplexMatrix2) =
      adjointCubeAverage V (l : Vertex L n k j → ComplexMatrix2)
private theorem eventually_goodAtStep (hS : MeanDerivOnForms.Claim)
    (hY : RealLinearMaps.RealLinearMapsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) :
    EventuallyNearIdentity (fieldSpace L n k j) (GoodAtStep (L := L) (n := n) (k := k)) := by
  have hAt := (hY L n k hL hn (by omega)).1 j hj
  show ∀ᶠ V in 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)), GoodAtStep V
  filter_upwards [hS L hL n k j hn hj, hAt.contourLogDrift_isLinear, hAt.adjointCubeAverage_isLinear]
    with V h₁ h₂ h₃
  obtain ⟨hsm, hre, hcf, hlin, hfm, hsame, -⟩ := h₁
  have hc : ∀ B : edgeFormSpace L n k j, (B : Edge L n k j → ComplexMatrix2) ∈ complexEdgeForms L n k j :=
    fun B => edgeForm_mem_complex B.2
  have h0 : holLeftDifferential normalizedMean V 0 = 0 := by
    have := hlin 0 (complexEdgeForms L n k j).zero_mem 0 (complexEdgeForms L n k j).zero_mem (-1)
    simpa using this
  have hadd : ∀ B B' : edgeFormSpace L n k j, holLeftDifferential normalizedMean V
      ((B + B' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) =
      holLeftDifferential normalizedMean V B +
        holLeftDifferential normalizedMean V B' := fun B B' => by
    have := hlin B (hc B) B' (hc B') 1
    simpa using this
  have hsmul : ∀ (r : ℝ) (B : edgeFormSpace L n k j), holLeftDifferential normalizedMean V
      ((r • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) =
      r • holLeftDifferential normalizedMean V B := fun r B => by
    have := hlin B (hc B) 0 (complexEdgeForms L n k j).zero_mem (r : ℂ)
    rw [add_zero, h0, add_zero] at this
    simpa [algebraMap_smul] using this
  exact
    { small := hsm
      compact := fun c hc => (hre c hc).2.2
      differential := ⟨⟨⟨fun B => ⟨_, hfm B B.2⟩, fun B B' => Subtype.ext (hadd B B')⟩,
        fun r B => Subtype.ext (hsmul r B)⟩, fun _ => rfl⟩
      real_eq := hsame
      drift := h₂
      average := h₃ }
private theorem exists_linear_oddExtension {E : Type*} [AddCommGroup E] [Module ℝ E] (T : OrientedTower L n k)
    (hj : j ≤ k) (f : E → Edge L n k j → ComplexMatrix2)
    (hmem : ∀ x b, b.IsPositivelyOriented → f x b ∈ ComplexMatrix2.hermitianTraceless)
    (hadd : ∀ x y b, b.IsPositivelyOriented → f (x + y) b = f x b + f y b)
    (hsmul : ∀ (r : ℝ) x b, b.IsPositivelyOriented → f (r • x) b = r • f x b) :
    ∃ T' : E →ₗ[ℝ] edgeFormSpace L n k j, ∀ x,
      (T' x : Edge L n k j → ComplexMatrix2) = extendOddly (f x) := by
  have hm : ∀ x, extendOddly (f x) ∈ edgeFormSpace L n k j := fun x =>
    ⟨fun b hb => by rw [extendOddly_pos hb]; exact hmem x b hb, fun b => extendOddly_opposite T hj _ b⟩
  have ha : ∀ x y, extendOddly (f (x + y)) = extendOddly (f x) + extendOddly (f y) := fun x y =>
    odd_ext T hj (extendOddly_opposite T hj _)
      (fun b => by
        simp only [Pi.add_apply, extendOddly_opposite T hj]
        abel)
      fun b hb => by
        simp only [Pi.add_apply, extendOddly_pos hb]
        exact hadd x y b hb
  have hs : ∀ (r : ℝ) x, extendOddly (f (r • x)) = r • extendOddly (f x) := fun r x =>
    odd_ext T hj (extendOddly_opposite T hj _)
      (fun b => by simp only [Pi.smul_apply, extendOddly_opposite T hj, smul_neg])
      fun b hb => by
        simp only [Pi.smul_apply, extendOddly_pos hb]
        exact hsmul r x b hb
  exact ⟨⟨⟨fun x => ⟨_, hm x⟩, fun x y => Subtype.ext (ha x y)⟩,
    fun r x => Subtype.ext (hs r x)⟩, fun _ => rfl⟩
private theorem exists_conjugation_linear (T : OrientedTower L n k) (hj : j ≤ k)
    (m : PositiveEdge L n k j → ComplexMatrix2) (hm : ∀ c, m c ∈ PeriodicLattice.compactGaugeGroup) :
    ∃ T' : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j, ∀ (B : edgeFormSpace L n k j)
      {c : Edge L n k j} (hc : c.IsPositivelyOriented), (T' B : Edge L n k j → ComplexMatrix2) c =
        ComplexMatrix2.conjugateBy (m ⟨c, hc⟩) ((B : Edge L n k j → ComplexMatrix2) c) := by
  classical
  obtain ⟨T', hT⟩ := exists_linear_oddExtension T hj
    (fun (B : edgeFormSpace L n k j) (c : Edge L n k j) =>
      if hc : c.IsPositivelyOriented then
        ComplexMatrix2.conjugateBy (m ⟨c, hc⟩) ((B : Edge L n k j → ComplexMatrix2) c) else 0)
    (fun B b hb => by
      simp only [dif_pos hb]
      exact ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hm _) _ (B.2.1 b hb))
    (fun B B' b hb => by
      simp only [dif_pos hb]
      exact conjugateBy_add _ _ _)
    (fun r B b hb => by
      simp only [dif_pos hb]
      exact conjugateBy_real_smul _ _ _)
  refine ⟨T', fun B c hc => ?_⟩
  rw [hT, extendOddly_pos hc, dif_pos hc]
private structure GoodPoint (X : ChainPoint L n k) : Prop where
  compact_noise : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup
  fields : ∀ j ≤ k, levelField X j ∈ fieldSpace L n k j
  good : ∀ j < k, GoodAtStep (levelField X j)
variable {X : ChainPoint L n k}
private theorem tangentTransport_linear (T : OrientedTower L n k) (hP : GoodPoint X) :
    ∀ j ≤ k, ∃ M : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k j, ∀ ξ,
      (M ξ : Edge L n k j → ComplexMatrix2) = tangentTransport X ξ j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨LinearMap.fst ℝ _ _, fun _ => rfl⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨M, hM⟩ := ih h.le
    obtain ⟨P, hPv⟩ := (hP.good j h).differential
    obtain ⟨W, hW⟩ := exists_conjugation_linear T hj (fun c => X.noise ⟨j, h⟩ c) (hP.compact_noise ⟨j, h⟩)
    let pr : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k (j + 1) :=
      (LinearMap.proj (φ := fun i : Fin k => edgeFormSpace L n k (i + 1)) ⟨j, h⟩) ∘ₗ LinearMap.snd ℝ _ _
    refine ⟨W ∘ₗ P ∘ₗ M + pr, fun ξ => ?_⟩
    refine odd_ext T hj (W (P (M ξ)) + pr ξ).2.2 (tangentTransport_opposite T _ _ h) fun c hc => ?_
    rw [tangentTransport_pos _ _ h hc, (hP.good j h).real_eq _ _ hc, ← hM, ← hPv]
    exact congrArg₂ (· + ·) (hW _ hc) rfl
private theorem chainDrift_linear (T : OrientedTower L n k) (hP : GoodPoint X) :
    ∀ j ≤ k, ∃ D : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k j, ∀ ξ,
      (D ξ : Vertex L n k j → ComplexMatrix2) = chainDrift X ξ j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨0, fun _ => rfl⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨D, hD⟩ := ih h.le
    obtain ⟨M, hM⟩ := tangentTransport_linear T hP j h.le
    obtain ⟨A, hA⟩ := (hP.good j h).average
    obtain ⟨C, hC⟩ := (hP.good j h).drift
    refine ⟨A ∘ₗ D + C ∘ₗ M, fun ξ => ?_⟩
    show ((A (D ξ) : Vertex L n k (j + 1) → ComplexMatrix2) +
      (C (M ξ) : Vertex L n k (j + 1) → ComplexMatrix2)) = _
    rw [hA, hC, hD, hM]
    rfl
private theorem extendByZero_linear :
    ∃ E : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0, ∀ g : vertexFunctionSpace L n k k,
      (E g : Vertex L n k 0 → ComplexMatrix2) = _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p44528 <;> assumption
private theorem gaugeOrbit_linear (T : OrientedTower L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : GoodPoint X) :
    ∃ O : vertexFunctionSpace L n k 0 →ₗ[ℝ] LevelForms L n k, ∀ l : vertexFunctionSpace L n k 0,
      formValues (O l) = gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2) := by
  obtain ⟨D₀, hD₀⟩ := hY.covDiff_isLinear 0 (Nat.zero_le k) X.fine (hP.fields 0 (Nat.zero_le k))
  have hN : ∀ i : Fin k, ∃ N : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k (i + 1),
      ∀ l : vertexFunctionSpace L n k 0, (N l : Edge L n k (i + 1) → ComplexMatrix2) =
        (gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2)).2 i := by
    classical
    intro i
    have hi : (i : ℕ) + 1 ≤ k := i.2
    obtain ⟨N, hN⟩ := exists_linear_oddExtension T hi
      (fun (l : vertexFunctionSpace L n k 0) (c : Edge L n k (i + 1)) =>
        if hc : c.IsPositivelyOriented then
          ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩)
              (restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.source) -
            restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.source
        else 0)
      (fun l b hb => by
        simp only [dif_pos hb]
        exact ComplexMatrix2.hermitianTraceless.sub_mem
          (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hP.compact_noise _ _) _ (l.2 _ (mem_univ _)))
          (l.2 _ (mem_univ _)))
      (fun l l' b hb => by
        simp only [dif_pos hb]
        show ComplexMatrix2.conjugateBy _ (restrictVertexFunction _ _ _ + restrictVertexFunction _ _ _) -
          (restrictVertexFunction _ _ _ + restrictVertexFunction _ _ _) = _
        rw [conjugateBy_add]
        abel)
      (fun r l b hb => by
        simp only [dif_pos hb]
        show ComplexMatrix2.conjugateBy _ (r • restrictVertexFunction _ _ _) -
          r • restrictVertexFunction _ _ _ = _
        rw [conjugateBy_real_smul, smul_sub])
    refine ⟨N, fun l => ?_⟩
    rw [hN, gaugeOrbitValues_snd]
  choose N hN using hN
  exact ⟨D₀.prod (LinearMap.pi N), fun l =>
    Prod.ext (hD₀ l) (funext fun i => hN i l)⟩
private theorem formValues_add (ξ η : LevelForms L n k) :
    formValues (ξ + η) = formValues ξ + formValues η := rfl
private theorem shiftedGaugeMap_spec (T : OrientedTower L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : GoodPoint X) : IsShiftedGaugeMap X (shiftedGaugeMap X) := by
  obtain ⟨M, hM⟩ := tangentTransport_linear T hP k le_rfl
  obtain ⟨D, hD⟩ := chainDrift_linear T hP k le_rfl
  obtain ⟨C, hC⟩ := hY.covDiff_isLinear k le_rfl _ (hP.fields k le_rfl)
  refine Classical.epsilon_spec (p := IsShiftedGaugeMap X) ⟨M + C ∘ₗ D, fun ξ => ?_⟩
  show (M ξ : Edge L n k k → ComplexMatrix2) + (C (D ξ) : Edge L n k k → ComplexMatrix2) = _
  rw [hM, hC, hD]
  rfl
private theorem gaugeTransform_spec (T : OrientedTower L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : GoodPoint X) : IsGaugeTransform X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X) := by
  obtain ⟨D, hD⟩ := chainDrift_linear T hP k le_rfl
  obtain ⟨E, hE⟩ := extendByZero_linear (L := L) (n := n) (k := k)
  obtain ⟨O, hO⟩ := gaugeOrbit_linear T hY hP
  refine Classical.epsilon_spec (p := IsGaugeTransform X) ⟨LinearMap.id + O ∘ₗ E ∘ₗ D, fun ξ => ?_⟩
  show formValues (ξ + O (E (D ξ))) = _
  rw [formValues_add, hO, hE, hD]
  rfl
private theorem one_mem_fieldSpace : (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => one_mem _, fun _ _ => (Matrix.inv_eq_right_inv (mul_one 1)).symm⟩
private theorem fieldOfPositiveValues_mem (T : OrientedTower L n k) (hj : j ≤ k)
    {w : PositiveEdge L n k j → ComplexMatrix2} (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [fieldOfPositiveValues, dif_pos hb]
      exact hw _
    · have hr := T.opposite_positive hj hb
      simp only [fieldOfPositiveValues, dif_neg hb, dif_pos hr]
      exact inv_mem_compact (hw _)
  · by_cases hb : b.IsPositivelyOriented
    · have hr := T.not_opposite_positive hj hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := by
        rw [edge_opposite_opposite]
        exact hb
      have e : (⟨b.opposite.opposite, hrr⟩ : PositiveEdge L n k j) = ⟨b, hb⟩ :=
        Subtype.ext (edge_opposite_opposite b)
      simp only [fieldOfPositiveValues, dif_neg hr, dif_pos hrr, dif_pos hb, e]
    · have hr := T.opposite_positive hj hb
      simp only [fieldOfPositiveValues, dif_neg hb, dif_pos hr]
      exact (Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hw _))).symm
private theorem levelField_pos (X : ChainPoint L n k) (h : j < k) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, h⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by
  rw [levelField_succ _ h]
  simp only [fieldOfPositiveValues, dif_pos hc]
private theorem levelField_neg (X : ChainPoint L n k) (h : j < k) {c : Edge L n k (j + 1)}
    (hc : ¬c.IsPositivelyOriented) (hr : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, h⟩ ⟨c.opposite, hr⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by
  rw [levelField_succ _ h]
  simp only [fieldOfPositiveValues, dif_neg hc, dif_pos hr]
end Forms
section Family
variable {L n k j : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
  {r : ℝ} {Z : P → ChainPoint L n k}
private structure GermFamily (S : Set P) (p₀ : P) (Z : P → ChainPoint L n k) : Prop where
  mem : p₀ ∈ S
  eq_unit : Z p₀ = unitPoint L n k
  fine : ∀ b, GermOn S p₀ fun p => (Z p).fine b
  noise : ∀ i c, GermOn S p₀ fun p => (Z p).noise i c
  compact : ∀ᶠ p in 𝓝[S] p₀, (Z p).fine ∈ fieldSpace L n k 0 ∧
    ∀ i c, (Z p).noise i c ∈ PeriodicLattice.compactGaugeGroup
private structure StepFacts (L n k : ℕ) (r : ℝ) : Prop where
  oriented : OrientedTower L n k
  inputs : ∀ j < k, LevelInputs L n k j r
  good : ∀ j < k, EventuallyNearIdentity (fieldSpace L n k j)
    (GoodAtStep (L := L) (n := n) (k := k) (j := j))
  mean_one : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  pos : 0 < r
private theorem levelField_unitPoint (D : StepFacts L n k r) :
    ∀ j ≤ k, levelField (unitPoint L n k) j = fun _ => (1 : ComplexMatrix2) := by
  intro j
  induction j with
  | zero =>
    intro _
    rfl
  | succ j ih =>
    intro hj
    have h : j < k := hj
    funext b
    by_cases hb : b.IsPositivelyOriented
    · rw [levelField_pos _ h hb, ih h.le, D.mean_one j h b hb]
      exact one_mul 1
    · have hr := D.oriented.opposite_positive hj hb
      rw [levelField_neg _ h hb hr, ih h.le, D.mean_one j h _ hr]
      show ((1 : ComplexMatrix2) * 1)⁻¹ = 1
      simp
private theorem tendsto_fieldSpace {V : P → Edge L n k j → ComplexMatrix2} (hp : p₀ ∈ S)
    (hg : ∀ b, GermOn S p₀ fun p => V p b) (h1 : V p₀ = fun _ => (1 : ComplexMatrix2))
    (hc : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldSpace L n k j) :
    Tendsto V (𝓝[S] p₀) (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, hc⟩
  have h : Tendsto (fun p => V p b) (𝓝[S] p₀) (𝓝 (V p₀ b)) := (hg b).tendsto hp
  rw [h1] at h
  exact h
private theorem regular_of_germs (D : StepFacts L n k r) (hj : j < k) {V : P → Edge L n k j → ComplexMatrix2}
    (hp : p₀ ∈ S) (hg : ∀ b, GermOn S p₀ fun p => V p b) (h1 : V p₀ = fun _ => (1 : ComplexMatrix2))
    (hc : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldSpace L n k j) :
    RegularFamily r S p₀ V ∧ ∀ᶠ p in 𝓝[S] p₀, GoodAtStep (k := k) (V p) := by
  have hs := (tendsto_fieldSpace hp hg h1 hc).eventually (D.good j hj)
  refine ⟨⟨hp, hg, hs.mono fun p h => h.small.1, fun b => ?_⟩, hs⟩
  rw [h1]
  show ‖(1 : ComplexMatrix2) - 1‖ < r
  simpa using D.pos
private theorem levelField_germs (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z) :
    ∀ j ≤ k, (∀ b, GermOn S p₀ fun p => levelField (Z p) j b) ∧
      ∀ᶠ p in 𝓝[S] p₀, levelField (Z p) j ∈ fieldSpace L n k j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hZ.fine, hZ.compact.mono fun p h => h.1⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨hg, hc⟩ := ih h.le
    have h1 : levelField (Z p₀) j = fun _ => (1 : ComplexMatrix2) := by
      rw [hZ.eq_unit]
      exact levelField_unitPoint D j h.le
    obtain ⟨hV, hs⟩ := regular_of_germs D h hZ.mem hg h1 hc
    have hpos : ∀ (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented), GermOn S p₀ fun p =>
        (Z p).noise ⟨j, h⟩ ⟨c, hc⟩ * normalizedMean (levelField (Z p) j) c := fun c hc =>
      (hZ.noise _ _).mul (hV.normalizedMean_germ (D.inputs j h) hc).1
    refine ⟨fun b => ?_, ?_⟩
    · by_cases hb : b.IsPositivelyOriented
      · exact (hpos b hb).congr (Eventually.of_forall fun p => (levelField_pos _ h hb).symm)
      · have hr := D.oriented.opposite_positive hj hb
        refine ((hpos _ hr).inv hZ.mem ?_).congr
          (Eventually.of_forall fun p => (levelField_neg _ h hb hr).symm)
        rw [h1, D.mean_one j h _ hr, hZ.eq_unit]
        show ((1 : ComplexMatrix2) * 1).det ≠ 0
        simp
    · filter_upwards [hZ.compact, hs] with p h₁ h₂
      rw [levelField_succ _ h]
      exact fieldOfPositiveValues_mem D.oriented hj fun c =>
        Submonoid.mul_mem _ (h₁.2 _ _) (h₂.compact c.1 c.2)
private theorem regular_levelField (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z) (h : j < k) :
    RegularFamily r S p₀ (fun p => levelField (Z p) j) ∧
      ∀ᶠ p in 𝓝[S] p₀, GoodAtStep (k := k) (levelField (Z p) j) := by
  obtain ⟨hg, hc⟩ := levelField_germs D hZ j h.le
  refine regular_of_germs D h hZ.mem hg ?_ hc
  rw [hZ.eq_unit]
  exact levelField_unitPoint D j h.le
private theorem eventually_goodPoint (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z) :
    ∀ᶠ p in 𝓝[S] p₀, GoodPoint (Z p) := by
  have hc : ∀ᶠ p in 𝓝[S] p₀, ∀ j ∈ Finset.range (k + 1),
      levelField (Z p) j ∈ fieldSpace L n k j ∧ (j < k → GoodAtStep (k := k) (levelField (Z p) j)) := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hjk : j ≤ k := by
      have := Finset.mem_range.1 hj
      omega
    obtain ⟨-, hcj⟩ := levelField_germs D hZ j hjk
    rcases Nat.lt_or_ge j k with h | h
    · filter_upwards [hcj, (regular_levelField D hZ h).2] with p h₁ h₂
      exact ⟨h₁, fun _ => h₂⟩
    · filter_upwards [hcj] with p h₁
      exact ⟨h₁, fun h' => absurd h' (by omega)⟩
  filter_upwards [hc, hZ.compact] with p h₁ h₂
  exact
    { compact_noise := h₂.2
      fields := fun j hj => (h₁ j (Finset.mem_range.2 (by omega))).1
      good := fun j hj => (h₁ j (Finset.mem_range.2 (by omega))).2 hj }
private theorem tangentTransport_complex (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z)
    (ξ : LevelForms L n k) (hj : j ≤ k) :
    ∀ᶠ p in 𝓝[S] p₀, tangentTransport (Z p) ξ j ∈ complexEdgeForms L n k j := by
  filter_upwards [eventually_goodPoint D hZ] with p hp
  obtain ⟨M, hM⟩ := tangentTransport_linear D.oriented hp j hj
  rw [← hM]
  exact edgeForm_mem_complex (M ξ).2
private theorem tangentTransport_germ (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z) (ξ : LevelForms L n k) :
    ∀ j ≤ k, ∀ b, GermOn S p₀ fun p => tangentTransport (Z p) ξ j b := by
  intro j
  induction j with
  | zero =>
    intro _ b
    exact (GermOn.const ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b)).congr
      (Eventually.of_forall fun p => rfl)
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨hV, -⟩ := regular_levelField D hZ h
    have hBf := tangentTransport_complex D hZ ξ h.le
    have hpos : ∀ (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
        GermOn S p₀ fun p => tangentTransport (Z p) ξ (j + 1) c := by
      intro c hc
      have h₁ := hV.holLeftDifferential_germ (D.inputs j h) (ih h.le) hBf c
      have h₂ := GermOn.conjugateBy hZ.mem (hZ.noise ⟨j, h⟩ ⟨c, hc⟩) h₁ (by
        rw [hZ.eq_unit]
        show (1 : ComplexMatrix2).det ≠ 0
        simp)
      refine (h₂.add (GermOn.const ((ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c))).congr ?_
      filter_upwards [eventually_goodPoint D hZ] with p hp
      rw [tangentTransport_pos _ _ h hc, (hp.good j h).real_eq _ _ hc]
    intro b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hr := D.oriented.opposite_positive hj hb
      refine (hpos _ hr).neg.congr (Eventually.of_forall fun p => ?_)
      have e := tangentTransport_opposite D.oriented (Z p) ξ h b.opposite
      rw [edge_opposite_opposite] at e
      exact e.symm
private theorem chainDrift_germ (D : StepFacts L n k r) (hZ : GermFamily S p₀ Z) (ξ : LevelForms L n k) :
    ∀ j ≤ k, ∀ y, GermOn S p₀ fun p => chainDrift (Z p) ξ j y := by
  intro j
  induction j with
  | zero =>
    intro _ y
    exact (GermOn.const (0 : ComplexMatrix2)).congr (Eventually.of_forall fun p => rfl)
  | succ j ih =>
    intro hj y
    have h : j < k := hj
    obtain ⟨hV, -⟩ := regular_levelField D hZ h
    exact ((hV.adjointCubeAverage_germ (D.inputs j h) (ih h.le) y).add
      (hV.contourLogDrift_germ (D.inputs j h) (tangentTransport_germ D hZ ξ j h.le)
        (tangentTransport_complex D hZ ξ h.le) y)).congr
      (Eventually.of_forall fun p => rfl)
end Family
section Values
variable {L n k : ℕ}
private abbrev PointValues (L n k : ℕ) : Type :=
  (Edge L n k 0 → ComplexMatrix2) × ((i : Fin k) → PositiveEdge L n k (i + 1) → ComplexMatrix2)
private def pointOfValues (y : PointValues L n k) : ChainPoint L n k := ⟨y.1, y.2⟩
private def compactValues (L n k : ℕ) : Set (PointValues L n k) :=
  {y | y.1 ∈ fieldSpace L n k 0 ∧ ∀ i c, y.2 i c ∈ PeriodicLattice.compactGaugeGroup}
private def unitValues (L n k : ℕ) : PointValues L n k := (fun _ => 1, fun _ _ => 1)
private theorem germFamily_values [Fintype (Edge L n k 0)]
    [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))] :
    GermFamily (compactValues L n k) (unitValues L n k) (pointOfValues (L := L) (n := n) (k := k)) where
  mem := ⟨one_mem_fieldSpace, fun _ _ => one_mem _⟩
  eq_unit := rfl
  fine := fun b => by
    let T : PointValues L n k →L[ℂ] ComplexMatrix2 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Edge L n k 0 => ComplexMatrix2) b).comp
        (ContinuousLinearMap.fst ℂ (Edge L n k 0 → ComplexMatrix2)
          ((i : Fin k) → PositiveEdge L n k (i + 1) → ComplexMatrix2))
    exact ⟨T, T.analyticAt _, Eventually.of_forall fun _ => rfl⟩
  noise := fun i c => by
    let T : PointValues L n k →L[ℂ] ComplexMatrix2 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : PositiveEdge L n k (i + 1) => ComplexMatrix2) c).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun i : Fin k => PositiveEdge L n k (i + 1) → ComplexMatrix2) i)).comp
        (ContinuousLinearMap.snd ℂ (Edge L n k 0 → ComplexMatrix2)
          ((i : Fin k) → PositiveEdge L n k (i + 1) → ComplexMatrix2))
    exact ⟨T, T.analyticAt _, Eventually.of_forall fun _ => rfl⟩
  compact := by
    filter_upwards [self_mem_nhdsWithin] with y hy using hy
end Values
section Real
variable {E P X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedSpace ℝ P] [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
  {S : Set P} {p₀ : P} {q₀ : E}
private theorem GermOn.analyticAt_real_comp {g : P → X} {φ : E → P} (h : GermOn S p₀ g)
    (hφ : AnalyticAt ℝ φ q₀) (h0 : φ q₀ = p₀) (ht : Tendsto φ (𝓝 q₀) (𝓝[S] p₀)) :
    AnalyticAt ℝ (fun q => g (φ q)) q₀ := by
  obtain ⟨H, hH, hev⟩ := h
  have hH' : AnalyticAt ℝ H (φ q₀) := by
    rw [h0]
    exact hH.restrictScalars
  refine (hH'.comp hφ).congr ?_
  filter_upwards [ht.eventually hev] with q hq
  exact hq.symm
end Real
end FamilyThroughUnit
open FamilyThroughUnit Tower Matrices in
theorem analyticFamilyTransportAndGauge_holds
    (hNear : NormalizedMeanNearOne)
    (hAvg : SmoothingNearIdentity)
    (hCont : PairContourIndependence.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hChart : LeftChartFields.Claim)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hS : MeanDerivOnForms.Claim)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hD : NormalizedMeanAtOne) :
    AnalyticFamilyTransportAndGauge := by
  intro L hL k n hk hn E _ _ X p₀ hX
  obtain ⟨ρ₂, hρ₂, hnear⟩ := hNear L hL
  have hrad := (hAvg.1 L hL).2.2
  obtain ⟨r, hr, hr₀, hr₂⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ polydiscRadius L ∧ r ≤ ρ₂ :=
    ⟨min (polydiscRadius L) ρ₂, lt_min hrad.pos hρ₂, min_le_left _ _, min_le_right _ _⟩
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hbonds : ∀ j, Finite (Edge L n k j) := fun j => PeriodicLattice.instFiniteBond _
  have hsites : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite (by omega) n _
  have hxor : ∀ j ≤ k, ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun j hj b => hO L n k hL hn hk j hj b
  have T : OrientedTower L n k := ⟨hxor⟩
  have F : ∀ j < k, LevelInputs L n k j r := fun j hj =>
    { edge_finite := hbonds j
      vertex_finite := hsites j
      orientation := hxor j hj.le
      expLog := hE
      curveLog := hChart.2.1
      mean_near := fun V hV hb c hc => by
        have h := hnear n k j hn hj V hV (fun b => (hb b).trans_le hr₂) c hc
        exact ⟨h.2.1, h.2.2.2.1⟩
      le_polydisc := hr₀
      admissible := fun c hc => hrad.periodic n k j hn hj c hc
      local_contour := fun y x hx c hc hy W hW hWn W' hr' =>
        ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
          (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2 }
  have D : StepFacts L n k r :=
    { oriented := T
      inputs := F
      good := fun j hj => eventually_goodAtStep hS hY hL hn hj
      mean_one := fun j hj c hc =>
        (hD L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
      pos := hr }
  have hYt := (hY L n k hL hn hk).2
  have hb₀ := hbonds 0
  let _ : Fintype (Edge L n k 0) := Fintype.ofFinite _
  let _ : ∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1)) := fun i =>
    have := hbonds (i + 1)
    Fintype.ofFinite _
  have hF := germFamily_values (L := L) (n := n) (k := k)
  let φ : E → PointValues L n k := fun p => ((X p).fine, (X p).noise)
  have hφ : AnalyticAt ℝ φ p₀ :=
    AnalyticAt.prod (AnalyticAt.pi hX.analyticAt_fine)
      (AnalyticAt.pi fun i => AnalyticAt.pi fun c => hX.analyticAt_noise i c)
  have h0 : φ p₀ = unitValues L n k := by
    simp only [φ, hX.eq_unit]
    rfl
  have ht : Tendsto φ (𝓝 p₀) (𝓝[compactValues L n k] unitValues L n k) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hX.eventually_compact⟩
    have h := hφ.continuousAt.tendsto
    rwa [h0] at h
  refine ⟨fun ξ j hj => ⟨fun b => ?_, fun y => ?_⟩, ?_⟩
  · exact GermOn.analyticAt_real_comp (tangentTransport_germ D hF ξ j hj b) hφ h0 ht
  · exact GermOn.analyticAt_real_comp (chainDrift_germ D hF ξ j hj y) hφ h0 ht
  · filter_upwards [ht.eventually (eventually_goodPoint D hF)] with p hp
    have hp' : GoodPoint (X p) := hp
    refine ⟨shiftedGaugeMap_spec T hYt hp', gaugeTransform_spec T hYt hp', ?_⟩
    obtain ⟨Dr, hDr⟩ := chainDrift_linear T hp' k le_rfl
    obtain ⟨Ex, hEx⟩ := extendByZero_linear (L := L) (n := n) (k := k)
    refine ⟨Ex ∘ₗ Dr, fun ξ => ?_⟩
    show (Ex (Dr ξ) : Vertex L n k 0 → ComplexMatrix2) = _
    rw [hEx, hDr]
    rfl
end YangMills.Construction.RunningCouplingSlope
end
