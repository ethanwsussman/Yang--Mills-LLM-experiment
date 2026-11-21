import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.RunningCouplingSlope.NoiseAndStepKernelsAtARadius
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.KernelGerms
open Matrices Tower PeriodicOperators
open Tower.LeftChartFields (CurveLogDerivative)
section Germs
variable {P X Y : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
def AnalyticGerm (S : Set P) (p₀ : P) (g : P → X) : Prop :=
  ∃ H : P → X, AnalyticAt ℂ H p₀ ∧ ∀ᶠ p in 𝓝[S] p₀, g p = H p
variable {S : Set P} {p₀ : P} {g g' : P → X}
theorem AnalyticGerm.congr_eventually (h : AnalyticGerm S p₀ g) (he : ∀ᶠ p in 𝓝[S] p₀, g p = g' p) :
    AnalyticGerm S p₀ g' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.congr_eventually <;> assumption
theorem AnalyticGerm.const (x : X) : AnalyticGerm S p₀ fun _ => x := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.const <;> assumption
theorem AnalyticGerm.add (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p + g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.add <;> assumption
theorem AnalyticGerm.neg (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => -g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.neg <;> assumption
theorem AnalyticGerm.sub (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p - g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sub <;> assumption
theorem AnalyticGerm.map_clm (T : X →L[ℂ] Y) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => T (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.map_clm <;> assumption
theorem AnalyticGerm.finset_sum {α : Type} (s : Finset α) {f : α → P → X}
    (h : ∀ a ∈ s, AnalyticGerm S p₀ (f a)) : AnalyticGerm S p₀ fun p => ∑ a ∈ s, f a p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sum <;> assumption
theorem AnalyticGerm.tendsto (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    Tendsto g (𝓝[S] p₀) (𝓝 (g p₀)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.tendsto_self <;> assumption
theorem AnalyticGerm.comp_pi {τ : Type} [Fintype τ] {E : Type} [NormedAddCommGroup E]
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
theorem AnalyticGerm.smul {f : P → ℂ} {g : P → X} (hf : AnalyticGerm S p₀ f)
    (hg : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => f p • g p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.smul <;> assumption
theorem AnalyticGerm.scalar_mul {f f' : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (hg : AnalyticGerm S p₀ f') : AnalyticGerm S p₀ fun p => f p * f' p := hf.smul hg
theorem AnalyticGerm.scalar_inv (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ≠ 0) : AnalyticGerm S p₀ fun p => (f p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.inv_complex <;> assumption
theorem AnalyticGerm.sqrt (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ∈ Complex.slitPlane) : AnalyticGerm S p₀ fun p => (f p) ^ (1 / 2 : ℂ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.sqrt <;> assumption
end Scalars
section MatrixGerms
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
variable {S : Set P} {p₀ : P} {g g' : P → ComplexMatrix2}
theorem AnalyticGerm.matrix_mul (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p * g' p := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matMul <;> assumption
def matrixEntryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)
theorem AnalyticGerm.matrix_det (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => (g p).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.det <;> assumption
def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] }
theorem AnalyticGerm.matrix_inv (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) (h0 : (g p₀).det ≠ 0) :
    AnalyticGerm S p₀ fun p => (g p)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matInv <;> assumption
theorem AnalyticGerm.list_map_prod {α : Type} (V : P → α → ComplexMatrix2)
    (hV : ∀ a, AnalyticGerm S p₀ fun p => V p a) (l : List α) :
    AnalyticGerm S p₀ fun p => (l.map (V p)).prod := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.listProd <;> assumption
theorem AnalyticGerm.matExp (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => ComplexMatrix2.matExp (g p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.matExp <;> assumption
end MatrixGerms
section SliceDerivative
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {S : Set P} {p₀ : P} {g : P × ℂ → X}
theorem eventually_fiberwise_of_prod {q : P × ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ), q z) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ᶠ t in 𝓝 (0 : ℂ), q (p, t) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.eventually_curry_prod_zero <;> assumption
theorem AnalyticGerm.differentiableAt_slice (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    ∀ᶠ p in 𝓝[S] p₀, DifferentiableAt ℂ (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.differentiable_slice <;> assumption
theorem AnalyticGerm.deriv_slice_zero (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => deriv (fun t => g (p, t)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.deriv_slice <;> assumption
end SliceDerivative
section PointAndParameter
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P} {g : P → X}
theorem tendsto_fst_prod_univ :
    Tendsto (Prod.fst : P × ℂ → P) (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) (𝓝[S] p₀) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_fst_prod_zero <;> assumption
theorem tendsto_pair_zero : Tendsto (fun p : P => ((p, 0) : P × ℂ)) (𝓝[S] p₀)
    (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.tendsto_pair_zero <;> assumption
theorem AnalyticGerm.comp_fst (h : AnalyticGerm S p₀ g) :
    AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => g z.1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.comp_fst <;> assumption
theorem AnalyticGerm.snd : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => z.2 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.analyticGerm_snd <;> assumption
theorem AnalyticGerm.restrict_zero {g : P × ℂ → X}
    (h : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => g (p, 0) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.restrict_zero <;> assumption
end PointAndParameter
theorem mem_slitPlane_of_sqrt_near_one {z : ℂ} (h : ‖z ^ (1 / 2 : ℂ) - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.mem_slitPlane_of_sqrt_near_one <;> assumption
section TwistedFields
variable {L n k j : ℕ}
theorem expTwist_of_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
theorem expTwist_mem_fieldsIn (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.expTwist_mem_fieldsIn <;> assumption
end TwistedFields
section LevelFamilies
variable {L n k j : ℕ}
theorem expTwist_zero_smul {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (A : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • A) U = U := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.expTwist_zero_smul <;> assumption
structure LevelInputs (L n k j : ℕ) (r : ℝ) : Prop where
  edge_finite : Finite (Edge L n k j)
  vertex_finite : Finite (Vertex L n k j)
  orientation_xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  expLog : ComplexMatrix2.ExpLogEstimates
  curveLogs : ∀ s : ℝ, 0 < s → CurveLogDerivative ℂ (Metric.ball 0 s)
    PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  mean_near_one : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  le_polydisc : r ≤ polydiscRadius L
  admissible : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  contour_local : ∀ (y : Vertex L n k (j + 1)),
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
structure RegularFamily (r : ℝ) (S : Set P) (p₀ : P) (V : P → Edge L n k j → ComplexMatrix2) :
    Prop where
  mem : p₀ ∈ S
  analytic : ∀ b, AnalyticGerm S p₀ fun p => V p b
  eventually_mem : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  near_one : ∀ b, ComplexMatrix2.operatorNorm (V p₀ b - 1) < r
variable {V : P → Edge L n k j → ComplexMatrix2}
theorem RegularFamily.mem_at_base (hV : RegularFamily r S p₀ V) :
    V p₀ ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  hV.eventually_mem.self_of_nhdsWithin hV.mem
theorem RegularFamily.det_base (hV : RegularFamily r S p₀ V) (b : Edge L n k j) :
    (V p₀ b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p₀) from
    hV.mem_at_base).1 b (mem_univ b)
theorem RegularFamily.eventually_near_one (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < r := by
  have := T.edge_finite
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝[S] p₀) (𝓝 ‖V p₀ b - 1‖) :=
    (((hV.analytic b).tendsto hV.mem).sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near_one b)
theorem det_pathHolonomy {U : Edge L n k j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (l : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy U l).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.det_pathHolonomy <;> assumption
theorem RegularFamily.pathHolonomy (hV : RegularFamily r S p₀ V) (l : List (Edge L n k j)) :
    AnalyticGerm S p₀ fun p => PeriodicLattice.pathHolonomy (V p) l :=
  AnalyticGerm.list_map_prod V hV.analytic l
theorem RegularFamily.contourHolonomy (hV : RegularFamily r S p₀ V) (c : Edge L n k (j + 1))
    (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    AnalyticGerm S p₀ fun p => contourHolonomy (V p) c x π := by
  refine ((hV.pathHolonomy _).matrix_mul (hV.pathHolonomy _)).matrix_mul
    ((hV.pathHolonomy _).matrix_inv hV.mem ?_)
  rw [det_pathHolonomy hV.det_base]
  exact one_ne_zero
theorem RegularFamily.contourMean (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) : AnalyticGerm S p₀ fun p => contourMean (V p) c := by
  have := T.vertex_finite
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold RunningCouplingSlope.contourMean
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x _ =>
    AnalyticGerm.finset_sum _ fun π _ => hV.contourHolonomy c x π)
theorem RegularFamily.normalizedMean (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    AnalyticGerm S p₀ (fun p => normalizedMean (V p) c) ∧
      ∀ᶠ p in 𝓝[S] p₀, normalizedMean (V p) c ∈ PeriodicLattice.complexGaugeGroup := by
  have hn := T.mean_near_one _ hV.mem_at_base hV.near_one c hc
  have hm := hV.contourMean T c
  have hs : (Matrix.det (RunningCouplingSlope.contourMean (V p₀) c)) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hn.1
  have hl : AnalyticGerm S p₀ fun p => meanRadius (V p) c := hm.matrix_det.sqrt hV.mem hs
  have hl0 : meanRadius (V p₀) c ≠ 0 := by
    intro h
    have := hn.1
    rw [h] at this
    norm_num at this
  refine ⟨(hl.scalar_inv hV.mem hl0).smul hm, ?_⟩
  filter_upwards [hV.eventually_mem, hV.eventually_near_one T] with p h₁ h₂
  exact (T.mean_near_one _ h₁ h₂ c hc).2
theorem extendFromPositive_restrict_eq {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, W b.opposite = (W b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
theorem RegularFamily.complexContour (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
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
    filter_upwards [hV.eventually_mem, hV.eventually_near_one T] with p h₁ h₂
    exact ⟨_, hpoly _ h₁ h₂, rfl⟩
  have h0 := hD.self_of_nhdsWithin hV.mem
  obtain ⟨G, hG, hGev⟩ := hol.2.2 _ h0
  have hfam := AnalyticGerm.comp_pi hV.mem
    (Ψ := fun p => PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))
    (fun i => hV.analytic i.1) hD hG hGev
  have hone := hfam.map_clm
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ())
  have hread : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))) y x =
      PeriodicLattice.complexMeanContourHolonomy (V p) y x := by
    filter_upwards [hV.eventually_mem, hV.eventually_near_one T] with p h₁ h₂
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p) := h₁
    exact T.contour_local y x hx c hc hy _ h₁' (fun b => (h₂ b).trans_le T.le_polydisc) _
      fun b hb => extendFromPositive_restrict_eq hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
  refine ⟨hone.congr_eventually hread, ?_⟩
  filter_upwards [hD, hread] with p h₁ h₂
  have h := hol.2.1 h₁ ()
  rw [← h₂]
  exact h
end LevelFamilies
section TwistedFamilies
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
theorem RegularFamily.expTwist (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) :
    RegularFamily r (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z => PeriodicLattice.expTwist (z.2 • B z.1) (V z.1) := by
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.mem, mem_univ _⟩
  have hval : ∀ b, AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z : P × ℂ => ComplexMatrix2.matExp (Complex.I • (z.2 • B z.1) b) * V z.1 b := fun b =>
    (AnalyticGerm.matExp hmem ((AnalyticGerm.const Complex.I).smul
      (AnalyticGerm.snd.smul (hB b).comp_fst))).matrix_mul (hV.analytic b).comp_fst
  refine ⟨hmem, fun b => ?_, ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr_eventually
        (Eventually.of_forall fun z => (expTwist_of_positive hb).symm)
    · refine ((hval b.opposite).matrix_inv hmem ?_).congr_eventually
        (Eventually.of_forall fun z => (expTwist_of_not_positive hb).symm)
      have h0 : ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) = 1 := by
        simp [ComplexMatrix2.matExp]
      show (ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) *
        V p₀ b.opposite).det ≠ 0
      rw [h0, one_mul, hV.det_base]
      exact one_ne_zero
  · refine (tendsto_fst_prod_univ.eventually (hV.eventually_mem.and hBf)).mono fun z h => ?_
    exact expTwist_mem_fieldsIn T.expLog T.orientation_xor (Submodule.smul_mem _ z.2 h.2) h.1
  · show ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist ((0 : ℂ) • B p₀) (V p₀) b - 1) < r
    rw [expTwist_zero_smul hV.mem_at_base]
    exact hV.near_one b
theorem RegularFamily.logDeriv (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
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
  have hD := hg.deriv_slice_zero
  have h0 := hg.restrict_zero
  have hdet : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det ≠ 0 := by
    have h : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det = 1 := hgrp.self_of_nhdsWithin hmem
    rw [h]
    exact one_ne_zero
  have hinv := h0.matrix_inv hV.mem hdet
  have hmain := (AnalyticGerm.const (S := S) (p₀ := p₀) Complex.I⁻¹).smul (hD.matrix_mul hinv)
  have hall : ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) =
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∧
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∈ ComplexMatrix2.traceless := by
    filter_upwards [eventually_fiberwise_of_prod hgrp, hg.differentiableAt_slice,
      hV.eventually_mem] with p h₁ h₂ h₃
    obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.1 h₁
    have hc := T.curveLogs s hs (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p)))
      (fun t ht => hball t ht) h₂
    obtain ⟨-, -, heq, hm⟩ := hc
    refine ⟨?_, hm⟩
    have e : Φ (V p) = Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)) := by
      rw [expTwist_zero_smul h₃]
    rw [← heq, e]
    rfl
  refine ⟨hmain.congr_eventually (hall.mono fun p h => h.1.symm), hall.mono fun p h => ?_⟩
  rw [h.1]
  exact h.2
end TwistedFamilies
section StepFamilies
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
theorem AnalyticGerm.extendOddly {f : P → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → AnalyticGerm S p₀ fun p => f p c)
    (c : Edge L n k j) :
    AnalyticGerm S p₀ fun p => Tower.extendOddly (f p) c := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.extendOddly <;> assumption
theorem RegularFamily.holDifferential (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => holLeftDifferential RunningCouplingSlope.normalizedMean (V p) (B p) c := by
  refine AnalyticGerm.extendOddly (fun c hc => ?_) c
  exact (hV.logDeriv T (Φ := fun W => RunningCouplingSlope.normalizedMean W c)
    ((hV.expTwist T hB hBf).normalizedMean T hc)).1
theorem RegularFamily.contourLogDrift (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => Tower.contourLogDrift (V p) (B p) y := by
  have := T.vertex_finite
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold Tower.contourLogDrift
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.finset_sum _ fun x hx => ?_)
  have hx' := hfin.mem_toFinset.1 hx
  exact (hV.logDeriv T
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((hV.expTwist T hB hBf).complexContour T y hx')).1
theorem AnalyticGerm.conjugateBy (hp : p₀ ∈ S) {g g' : P → ComplexMatrix2}
    (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') (h0 : (g p₀).det ≠ 0) :
    AnalyticGerm S p₀ fun p => ComplexMatrix2.conjugateBy (g p) (g' p) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.AnalyticGerm.conjugateBy <;> assumption
theorem RegularFamily.covariantStep (T : LevelInputs L n k j r) (hV : RegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => meanCovariantStep (V p) (B p) c := by
  refine (hV.holDifferential T hB hBf c).add (AnalyticGerm.extendOddly (fun b hb => ?_) c)
  obtain ⟨h₁, h₂⟩ := hV.normalizedMean T hb
  have hdet : (RunningCouplingSlope.normalizedMean (V p₀) b).det ≠ 0 := by
    have h : (RunningCouplingSlope.normalizedMean (V p₀) b).det = 1 := h₂.self_of_nhdsWithin hV.mem
    rw [h]
    exact one_ne_zero
  exact (AnalyticGerm.conjugateBy hV.mem h₁ (hV.contourLogDrift T hB hBf _) hdet).sub
    (hV.contourLogDrift T hB hBf _)
end StepFamilies
section PauliCoefficients
theorem exists_pauliCoeff_clm (a : Fin 3) :
    ∃ T : ComplexMatrix2 →L[ℂ] ℂ, ∀ X ∈ ComplexMatrix2.traceless, T X = pauliCoeff a X := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.exists_clm_pauliCoeff <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end PauliCoefficients
section FiniteKernels
variable {N N' : Type}
theorem kernelOfMap_apply [Fintype N] [DecidableEq N] {M : (N → ℂ) → N' → ℂ}
    (hM : ∀ (z : ℂ) (f f' : N → ℂ), M (z • f + f') = z • M f + M f') (ι : N) (ι' : N') :
    kernelOfMap M ι' ι = M (Pi.single ι 1) ι' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.kernelOfMap_apply <;> assumption
end FiniteKernels
section StepLinearity
variable {L n k j : ℕ} {r : ℝ}
theorem conjugateBy_mem_traceless_of_det_one {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem extendOddly_of_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_not_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.StepMapsComplexLinear.extendOddly_mem <;> assumption
theorem covDiff_linear (U : Edge L n k j → ComplexMatrix2) (z : ℂ)
    (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff U (z • l + l') = z • covDiff U l + covDiff U l' := by apply _root_.YangMills.Construction.Tower.CovDiffStep.covDiff_smul_add <;> assumption
structure StepLinearInputs (L n k j : ℕ) (r : ℝ) : Prop where
  le_polydisc : r ≤ polydiscRadius L
  orientation_xor : ∀ b : Edge L n k (j + 1),
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  mean_mem : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented → normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  holDifferential : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) →
      (∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
        holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless) ∧
      ∀ (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
        holLeftDifferential normalizedMean V (z • B + B') =
          z • holLeftDifferential normalizedMean V B +
            holLeftDifferential normalizedMean V B'
  drift_adjoint : ∀ V ∈ smallComplexFields L n k j,
      (∀ B ∈ complexEdgeForms L n k j, ∀ y, contourLogDrift V B y ∈ ComplexMatrix2.traceless) ∧
      (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j, ∀ c : ℂ,
        contourLogDrift V (c • B + B') = c • contourLogDrift V B + contourLogDrift V B') ∧
      (∀ l : Vertex L n k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) → ∀ y,
        adjointCubeAverage V l y ∈ ComplexMatrix2.traceless) ∧
      ∀ l l' : Vertex L n k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ c : ℂ,
        adjointCubeAverage V (c • l + l') =
          c • adjointCubeAverage V l + adjointCubeAverage V l'
variable {V : Edge L n k j → ComplexMatrix2}
def IsNearOneField (r : ℝ) (V : Edge L n k j → ComplexMatrix2) : Prop :=
  V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
    ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r
theorem StepLinearInputs.mem_small (T : StepLinearInputs L n k j r) (hV : IsNearOneField r V) :
    V ∈ smallComplexFields L n k j :=
  ⟨hV.1, fun b => (hV.2 b).trans_le T.le_polydisc⟩
theorem covariantStep_mem (T : StepLinearInputs L n k j r) (hV : IsNearOneField r V)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V B ∈ complexEdgeForms L n k (j + 1) := by
  refine Submodule.add_mem _ (extendOddly_mem T.orientation_xor fun b hb => ?_)
    (extendOddly_mem T.orientation_xor fun b hb => ?_)
  · have h := (T.holDifferential V hV.1 hV.2).1 B b hb
    unfold holLeftDifferential at h
    rw [extendOddly_of_positive hb] at h
    exact h
  · have hl := (T.drift_adjoint V (T.mem_small hV)).1 B hB
    exact Submodule.sub_mem _
      (conjugateBy_mem_traceless_of_det_one (T.mean_mem V hV.1 hV.2 b hb) (hl _)) (hl _)
theorem covariantStep_linear (T : StepLinearInputs L n k j r) (hV : IsNearOneField r V)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) (z : ℂ) :
    meanCovariantStep V (z • B + B') = z • meanCovariantStep V B + meanCovariantStep V B' := by
  unfold meanCovariantStep
  rw [(T.holDifferential V hV.1 hV.2).2, (T.drift_adjoint V (T.mem_small hV)).2.1 B hB B' hB',
    covDiff_linear, smul_add]
  abel
end StepLinearity
section MeanIterates
variable {L n k : ℕ} {r : ℝ}
theorem meanIterate_succ_of_positive (U : Edge L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanIterate U (j + 1) c = normalizedMean (meanIterate U j) c := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.meanIterate_succ_of_positive <;> assumption
theorem meanIterate_succ_of_not_positive (U : Edge L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : ¬ c.IsPositivelyOriented)
    (hr : c.opposite.IsPositivelyOriented) :
    meanIterate U (j + 1) c = (normalizedMean (meanIterate U j) c.opposite)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.meanIterate_succ_of_not_positive <;> assumption
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
variable {U : P → Edge L n k 0 → ComplexMatrix2}
theorem regularFamily_meanIterate (hp : p₀ ∈ S)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOneField r (meanIterate (U p) j)) {j : ℕ} (hj : j < k)
    (hg : ∀ b, AnalyticGerm S p₀ fun p => meanIterate (U p) j b) :
    RegularFamily r S p₀ fun p => meanIterate (U p) j :=
  ⟨hp, hg, by filter_upwards [self_mem_nhdsWithin] with p h using (hs p h j hj).1,
    (hs p₀ hp j hj).2⟩
theorem meanIterate_germ (F : ∀ j < k, LevelInputs L n k j r) (hp : p₀ ∈ S)
    (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOneField r (meanIterate (U p) j)) :
    ∀ j ≤ k, ∀ b, AnalyticGerm S p₀ fun p => meanIterate (U p) j b := by
  intro j
  induction j with
  | zero => exact fun _ b => hU b
  | succ j ih =>
    intro hj c
    have hjk : j < k := hj
    have hV := regularFamily_meanIterate hp hs hjk (ih hjk.le)
    by_cases hc : c.IsPositivelyOriented
    · exact (hV.normalizedMean (F j hjk) hc).1.congr_eventually
        (Eventually.of_forall fun p => (meanIterate_succ_of_positive (U p) hjk hc).symm)
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
      obtain ⟨h₁, h₂⟩ := hV.normalizedMean (F j hjk) hr
      have hdet : (normalizedMean (meanIterate (U p₀) j) c.opposite).det = 1 :=
        h₂.self_of_nhdsWithin hp
      exact (h₁.matrix_inv hp (by rw [hdet]; exact one_ne_zero)).congr_eventually
        (Eventually.of_forall fun p => (meanIterate_succ_of_not_positive (U p) hjk hc hr).symm)
end MeanIterates
section KernelEntries
variable {L n k j : ℕ} {r : ℝ}
theorem real_smul_eq_complex_smul (η : ℝ) (X : ComplexMatrix2) : η • X = (η : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
open Classical in
def pauliEdgeForm (f : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0
theorem pauliEdgeForm_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Fin 3 × PositiveEdge L n k j → ℂ) : pauliEdgeForm f ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_mem <;> assumption
theorem pauliEdgeForm_linear (z : ℂ) (f f' : Fin 3 × PositiveEdge L n k j → ℂ) :
    pauliEdgeForm (z • f + f') = z • pauliEdgeForm f + pauliEdgeForm f' := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_smul_add <;> assumption
def stepCoeffMap (V : Edge L n k j → ComplexMatrix2) (f : Fin 3 × PositiveEdge L n k j → ℂ) :
    Fin 3 × PositiveEdge L n k (j + 1) → ℂ :=
  fun κ => pauliCoeff κ.1 (((L : ℝ)⁻¹ • meanCovariantStep V (pauliEdgeForm f)) κ.2.1)
theorem meanStepKernel_eq (U : Edge L n k 0 → ComplexMatrix2) (j : ℕ) :
    meanStepKernel L n k U j = kernelOfMap (stepCoeffMap (meanIterate U j)) := rfl
theorem stepCoeffMap_linear (T : StepLinearInputs L n k j r)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {V : Edge L n k j → ComplexMatrix2} (hV : IsNearOneField r V) (z : ℂ)
    (f f' : Fin 3 × PositiveEdge L n k j → ℂ) :
    stepCoeffMap V (z • f + f') = z • stepCoeffMap V f + stepCoeffMap V f' := by
  funext κ
  obtain ⟨P, hP⟩ := exists_pauliCoeff_clm κ.1
  have hmem : ∀ g, meanCovariantStep V (pauliEdgeForm g) κ.2.1 ∈ ComplexMatrix2.traceless :=
    fun g => (covariantStep_mem T hV (pauliEdgeForm_mem hx g)).1 κ.2.1 κ.2.2
  have hsm : ∀ g, ((L : ℝ)⁻¹ • meanCovariantStep V (pauliEdgeForm g)) κ.2.1 ∈
      ComplexMatrix2.traceless :=
    fun g => by
      rw [Pi.smul_apply, real_smul_eq_complex_smul]
      exact Submodule.smul_mem _ _ (hmem g)
  show pauliCoeff κ.1 (((L : ℝ)⁻¹ • meanCovariantStep V (pauliEdgeForm (z • f + f'))) κ.2.1) =
    z * pauliCoeff κ.1 (((L : ℝ)⁻¹ • meanCovariantStep V (pauliEdgeForm f)) κ.2.1) +
    pauliCoeff κ.1 (((L : ℝ)⁻¹ • meanCovariantStep V (pauliEdgeForm f')) κ.2.1)
  rw [← hP _ (hsm _), ← hP _ (hsm _), ← hP _ (hsm _), pauliEdgeForm_linear,
    covariantStep_linear T hV (pauliEdgeForm_mem hx f) (pauliEdgeForm_mem hx f') z]
  simp only [Pi.smul_apply, Pi.add_apply, real_smul_eq_complex_smul, map_add, map_smul,
    smul_eq_mul, smul_add]
  ring
theorem covariantStep_zero (T : StepLinearInputs L n k j r) {V : Edge L n k j → ComplexMatrix2}
    (hV : IsNearOneField r V) : meanCovariantStep V 0 = 0 := by
  have h := covariantStep_linear T hV (Submodule.zero_mem (complexEdgeForms L n k j))
    (Submodule.zero_mem (complexEdgeForms L n k j)) 1
  rw [one_smul, one_smul, add_zero] at h
  exact left_eq_add.1 h
open Classical in
theorem meanStepKernel_apply [Finite (PositiveEdge L n k j)] (T : StepLinearInputs L n k j r)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U : Edge L n k 0 → ComplexMatrix2} (hV : IsNearOneField r (meanIterate U j))
    (ι' : Fin 3 × PositiveEdge L n k (j + 1)) (ι : Fin 3 × PositiveEdge L n k j) :
    meanStepKernel L n k U j ι' ι = pauliCoeff ι'.1
      (((L : ℝ)⁻¹ • meanCovariantStep (meanIterate U j) (unitCoeffForm L n k j ι)) ι'.2.1) := by
  let _ := Fintype.ofFinite (PositiveEdge L n k j)
  have e₀ : ∀ i₁ i₂ : DecidableEq (Fin 3 × PositiveEdge L n k j),
      @Pi.single _ (fun _ => ℂ) _ i₁ ι 1 = @Pi.single _ (fun _ => ℂ) _ i₂ ι 1 :=
    fun i₁ i₂ => by rw [Subsingleton.elim i₁ i₂]
  have e : pauliEdgeForm (Pi.single ι 1) = unitCoeffForm L n k j ι :=
    congrArg pauliEdgeForm (e₀ _ _)
  rw [meanStepKernel_eq, kernelOfMap_apply (stepCoeffMap_linear T hx hV) ι ι']
  unfold stepCoeffMap
  rw [e]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
theorem RegularFamily.meanRadius {V : P → Edge L n k j → ComplexMatrix2} (T : LevelInputs L n k j r)
    (hV : RegularFamily r S p₀ V) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    (AnalyticGerm S p₀ fun p => meanRadius (V p) c) ∧ meanRadius (V p₀) c ≠ 0 := by
  have hn := T.mean_near_one _ hV.mem_at_base hV.near_one c hc
  have hm := hV.contourMean T c
  have hs : (Matrix.det (RunningCouplingSlope.contourMean (V p₀) c)) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hn.1
  refine ⟨hm.matrix_det.sqrt hV.mem hs, fun h => ?_⟩
  have := hn.1
  rw [h] at this
  norm_num at this
variable {U : P → Edge L n k 0 → ComplexMatrix2}
theorem meanStepKernel_germ [Finite (PositiveEdge L n k j)] (T : LevelInputs L n k j r)
    (G : StepLinearInputs L n k j r)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hV : RegularFamily r S p₀ fun p => meanIterate (U p) j)
    (hs : ∀ p ∈ S, IsNearOneField r (meanIterate (U p) j))
    (ι' : Fin 3 × PositiveEdge L n k (j + 1)) (ι : Fin 3 × PositiveEdge L n k j) :
    AnalyticGerm S p₀ fun p => meanStepKernel L n k (U p) j ι' ι := by
  classical
  obtain ⟨Pm, hP⟩ := exists_pauliCoeff_clm ι'.1
  have hB : unitCoeffForm L n k j ι ∈ complexEdgeForms L n k j := pauliEdgeForm_mem hx _
  have hg := ((AnalyticGerm.const (S := S) (p₀ := p₀) (((L : ℝ)⁻¹ : ℝ) : ℂ)).smul
    (hV.covariantStep T (B := fun _ => unitCoeffForm L n k j ι) (fun _ => AnalyticGerm.const _)
      (Eventually.of_forall fun _ => hB) ι'.2.1)).map_clm Pm
  refine hg.congr_eventually ?_
  filter_upwards [self_mem_nhdsWithin] with p h
  rw [meanStepKernel_apply G hx (hs p h) ι' ι, Pi.smul_apply, real_smul_eq_complex_smul, hP]
  exact Submodule.smul_mem _ _ ((covariantStep_mem G (hs p h) hB).1 ι'.2.1 ι'.2.2)
theorem noiseCovariance_germ {k : ℕ} {U : P → Edge L n k 0 → ComplexMatrix2}
    (F : ∀ j < k, LevelInputs L n k j r)
    (G : ∀ j < k, StepLinearInputs L n k j r)
    (hx : ∀ j ≤ k, ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hp : p₀ ∈ S) (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOneField r (meanIterate (U p) j))
    (hfin : ∀ j, Finite (PositiveEdge L n k j)) (a : ℝ) :
    ∀ j ≤ k, ∀ ι' ι, AnalyticGerm S p₀ fun p => noiseCovariance a L n k (U p) j ι' ι := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ ι' ι
    exact AnalyticGerm.const (0 : ℂ)
  | succ j ih =>
    intro hj ι' ι
    have hjk : j < k := hj
    have := hfin j
    have := hfin (j + 1)
    let _ := Fintype.ofFinite (PositiveEdge L n k j)
    let _ := Fintype.ofFinite (PositiveEdge L n k (j + 1))
    have hV := regularFamily_meanIterate hp hs hjk (meanIterate_germ F hp hU hs j hjk.le)
    have hS := meanStepKernel_germ (F j hjk) (G j hjk) (hx j hjk.le) hV (fun p h => hs p h j hjk)
    have hlen : AnalyticGerm S p₀ fun p => invRadiusDiag (U p) j ι' ι := by
      by_cases h : ι' = ι
      · obtain ⟨hg, h0⟩ := hV.meanRadius (F j hjk) ι.2.2
        refine (hg.scalar_inv hp h0).congr_eventually (Eventually.of_forall fun p => ?_)
        simp only [invRadiusDiag]
        rw [if_pos h]
      · refine (AnalyticGerm.const (0 : ℂ)).congr_eventually (Eventually.of_forall fun p => ?_)
        simp only [invRadiusDiag]
        rw [if_neg h]
    have hprod : AnalyticGerm S p₀ fun p => PeriodicOperators.compKernel
        (PeriodicOperators.compKernel (meanStepKernel L n k (U p) j)
          (noiseCovariance a L n k (U p) j))
        (meshTranspose (meshAt L k j) (meshAt L k (j + 1))
          (meanStepKernel L n k (U p) j)) ι' ι := by
      simp only [PeriodicOperators.compKernel, tsum_fintype, meshTranspose,
        PeriodicOperators.wTranspose]
      exact AnalyticGerm.finset_sum _ fun x _ => (AnalyticGerm.finset_sum _ fun y _ =>
        (hS ι' y).scalar_mul (ih hjk.le y x)).scalar_mul
          ((AnalyticGerm.const _).scalar_mul (hS ι x))
    exact ((AnalyticGerm.const _).smul hlen).add ((AnalyticGerm.const _).smul hprod)
end KernelEntries
section MatrixFamilies
variable {σ : Type} [Fintype σ]
theorem operatorNorm_le_supNorm (A : σ → ComplexMatrix2) (i : σ) :
    ComplexMatrix2.operatorNorm (A i) ≤ GroupLieProduct.supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem isOpen_supNorm_lt {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen {A : σ → ComplexMatrix2 | GroupLieProduct.supNorm A < ρ} := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isOpen_supNorm_lt <;> assumption
theorem isSupOpen_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    GroupLieProduct.IsSupOpen (GroupLieProduct.supBall σ ρ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isSupOpen_supBall <;> assumption
def tupleOfCoordsLinear (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    Coordinates.ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → ComplexMatrix2) where
  toFun := GroupLieProduct.tupleOfCoords e ν
  map_add' w w' := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, add_smul,
      Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, mul_smul,
      Finset.smul_sum]
theorem tupleOfCoords_mem (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    GroupLieProduct.tupleOfCoords e ν w ∈ GroupLieProduct.tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem isHolomorphicOnTraceless_of_germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (c : E ≃ Coordinates.ComplexCoordinates l)
    (Tc : E →L[ℂ] Coordinates.ComplexCoordinates l) (hTc : ∀ x, Tc x = c x)
    {ρ : ℝ} (hρ : 0 < ρ) (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {f : (σ → ComplexMatrix2) → E}
    (hf : ∀ A₀ ∈ GroupLieProduct.supBall σ ρ, AnalyticGerm (GroupLieProduct.supBall σ ρ) A₀ f) :
    GroupLieProduct.IsHolomorphicOnTraceless e c (GroupLieProduct.supBall σ ρ) f := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isHolomorphicOnTraceless_of_analyticGerm <;> assumption
def scalarCoordsCLM : ℂ →L[ℂ] Coordinates.ComplexCoordinates 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := Tower.LeftChartFields.scalarCoords
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
end MatrixFamilies
section AntisymmetrizedForms
variable {L n k : ℕ} {F : Finset (Edge L n k 0)}
def antisymmetrizedForm (hF : ∀ b, b ∈ F) (A : F → ComplexMatrix2) : Edge L n k 0 → ComplexMatrix2 :=
  fun b => (1 / 2 : ℂ) • (A ⟨b, hF b⟩ - A ⟨b.opposite, hF _⟩)
theorem antisymmetrizedForm_values (hF : ∀ b, b ∈ F) {a : Edge L n k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) : antisymmetrizedForm hF (fun b => a b) = a := by
  funext b
  have h : a b.opposite = -a b := ha.2 b
  simp only [antisymmetrizedForm, h, sub_neg_eq_add]
  rw [← two_smul ℂ (a b), smul_smul]
  norm_num
theorem antisymmetrizedForm_mem (hF : ∀ b, b ∈ F) {ρ : ℝ} {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) :
    antisymmetrizedForm hF A ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hA.1 _) (hA.1 _))
  · simp only [antisymmetrizedForm, PeriodicLattice.Bond.opposite_opposite]
    rw [← smul_neg, neg_sub]
theorem antisymmetrizedForm_maxOperatorNorm_lt (hF : ∀ b, b ∈ F) {ρ : ℝ} (hρ : 0 < ρ)
    {A : F → ComplexMatrix2} (hA : A ∈ GroupLieProduct.supBall F ρ) :
    maxOperatorNorm (antisymmetrizedForm hF A) < ENNReal.ofReal ρ := by
  have hle : maxOperatorNorm (antisymmetrizedForm hF A) ≤
      ENNReal.ofReal (GroupLieProduct.supNorm A) := by
    refine iSup_le fun b => ENNReal.ofReal_le_ofReal ?_
    have h₁ := operatorNorm_le_supNorm A ⟨b, hF b⟩
    have h₂ := operatorNorm_le_supNorm A ⟨b.opposite, hF _⟩
    have h₃ := norm_sub_le (A ⟨b, hF b⟩) (A ⟨b.opposite, hF _⟩)
    simp only [ComplexMatrix2.operatorNorm, antisymmetrizedForm, norm_smul] at h₁ h₂ ⊢
    norm_num
    linarith
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2)
def exponentCLM (hF : ∀ b, b ∈ F) (b : Edge L n k 0) : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2 :=
  (Complex.I * (finestMesh L k : ℂ) * (1 / 2 : ℂ)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => ComplexMatrix2) ⟨b, hF b⟩ -
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => ComplexMatrix2) ⟨b.opposite, hF _⟩)
theorem exponentCLM_apply (hF : ∀ b, b ∈ F) (b : Edge L n k 0) (A : F → ComplexMatrix2) :
    exponentCLM hF b A = Complex.I • scaledRemainderForm (antisymmetrizedForm hF A) b := by
  ext r s
  simp [exponentCLM, scaledRemainderForm, antisymmetrizedForm, Matrix.smul_apply]
  ring
theorem remainderGaugeField_germ (hF : ∀ b, b ∈ F) {ρ : ℝ} (b : Edge L n k 0)
    (A₀ : F → ComplexMatrix2) : AnalyticGerm (GroupLieProduct.supBall F ρ) A₀
      fun A => remainderGaugeField (antisymmetrizedForm hF A) b := by
  refine ⟨fun A => ComplexMatrix2.matExp (exponentCLM hF b A),
    AnalyticAt.comp (f := exponentCLM hF b)
      (NormedSpace.exp_analytic (𝕂 := ℂ) _) (ContinuousLinearMap.analyticAt _ _), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with A hA
  change IdentityExpChart.expForm
    (scaledRemainderForm (antisymmetrizedForm hF A)) b = _
  have hrev : scaledRemainderForm (antisymmetrizedForm hF A) b.opposite =
      -scaledRemainderForm (antisymmetrizedForm hF A) b := by
    have h : antisymmetrizedForm hF A b.opposite = -antisymmetrizedForm hF A b :=
      (antisymmetrizedForm_mem hF hA).2 b
    simp only [scaledRemainderForm, Pi.smul_apply, h, smul_neg]
  unfold IdentityExpChart.expForm PeriodicLattice.expTwist
  rw [exponentCLM_apply]
  split_ifs with hb
  · simp
  · rw [Pi.one_apply, mul_one, hrev, smul_neg]
    have h := Matrix.exp_neg (-(Complex.I • scaledRemainderForm (antisymmetrizedForm hF A) b))
    rw [neg_neg] at h
    exact h.symm
end AntisymmetrizedForms
theorem stepAndNoiseKernelsNearIdentity (hNear : RunningCouplingSlope.NormalizedMeanNearOne)
    (hDiff : RunningCouplingSlope.HolDifferentialLinear)
    (hAvg : Tower.SmoothingNearIdentity)
    (hCont : Tower.PairContourIndependence.Statement)
    (hLin : Tower.StepMapsComplexLinear.Claim)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hChart : Tower.LeftChartFields.Claim)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement) :
    RunningCouplingSlope.StepAndNoiseKernelsNearIdentity := by
  intro L hL
  obtain ⟨ρ₂, hρ₂, hnear⟩ := hNear L hL
  obtain ⟨ρ₃, hρ₃, hdiff⟩ := hDiff L hL
  have hrad := (hAvg.1 L hL).2.2
  obtain ⟨r, hr, hr₀, hr₂, hr₃⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ polydiscRadius L ∧ r ≤ ρ₂ ∧ r ≤ ρ₃ :=
    ⟨min (polydiscRadius L) (min ρ₂ ρ₃), lt_min hrad.pos (lt_min hρ₂ hρ₃), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨r, hr, fun n k hn hk => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hsites : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite hLpos n _
  have hbonds : ∀ j, Finite (Edge L n k j) := fun j =>
    have := hsites j
    Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hxor : ∀ j ≤ k, ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun j hj b =>
    ((hO ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  have hsmallNear : ∀ j < k, ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) → ∀ c : Edge L n k (j + 1),
        c.IsPositivelyOriented →
        ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro j hj V hV hb c hc
    have h := hnear n k j hn hj V hV (fun b => (hb b).trans_le hr₂) c hc
    exact ⟨h.2.1, h.2.2.2.1⟩
  have F : ∀ j < k, LevelInputs L n k j r := fun j hj =>
    { edge_finite := hbonds j
      vertex_finite := hsites j
      orientation_xor := hxor j hj.le
      expLog := hE
      curveLogs := hChart.2.1
      mean_near_one := hsmallNear j hj
      le_polydisc := hr₀
      admissible := fun c hc => hrad.periodic n k j hn hj c hc
      contour_local := fun y x hx c hc hy W hW hWn W' hr' =>
        ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
          (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2 }
  have G : ∀ j < k, StepLinearInputs L n k j r := fun j hj =>
    { le_polydisc := hr₀
      orientation_xor := hxor (j + 1) hj
      mean_mem := fun V hV hb c hc => (hsmallNear j hj V hV hb c hc).2
      holDifferential := fun V hV hb => hdiff n k j hn hj V hV fun b => (hb b).trans_le hr₃
      drift_adjoint := fun V hV => by
        have h := hLin L hL n k j hn hj V hV
        exact ⟨fun B hB => (h.1 B hB).2, fun B hB B' hB' c => (h.2.1 B hB B' hB' c).2,
          fun l hl => (h.2.2.1 l hl).2, fun l l' hl hl' c => (h.2.2.2 l l' hl hl' c).2⟩ }
  have hPfin : ∀ j, Finite (PositiveEdge L n k j) := fun j =>
    have := hbonds j
    Subtype.finite
  refine ⟨fun U hU j hj => ?_, fun ρ hρ hprem a j hj ι' ι => ?_⟩
  · have := hPfin j
    exact ⟨covariantStep_zero (G j hj) (hU j hj),
      fun ι' ι => meanStepKernel_apply (G j hj) (hxor j hj.le) (hU j hj) ι' ι⟩
  · have := hbonds 0
    let _ := Fintype.ofFinite (Edge L n k 0)
    have hF : ∀ b : Edge L n k 0, b ∈ (Finset.univ : Finset (Edge L n k 0)) := Finset.mem_univ
    have hsm : ∀ A ∈ GroupLieProduct.supBall (Finset.univ : Finset (Edge L n k 0)) ρ, ∀ j < k,
        IsNearOneField r (meanIterate (remainderGaugeField (antisymmetrizedForm hF A)) j) :=
      fun A hA j hj => hprem _ (antisymmetrizedForm_mem hF hA)
        (antisymmetrizedForm_maxOperatorNorm_lt hF hρ hA) j hj
    have hvalues : ∀ a ∈ complexEdgeForms L n k 0,
        remainderGaugeField (antisymmetrizedForm hF fun b => a b) = remainderGaugeField a := by
      intro a ha
      rw [antisymmetrizedForm_values hF ha]
    exact ⟨Finset.univ,
      fun A => noiseCovariance a L n k (remainderGaugeField (antisymmetrizedForm hF A)) j ι' ι,
      fun e => isHolomorphicOnTraceless_of_germ _ scalarCoordsCLM (fun _ => rfl) hρ e
        fun A₀ hA₀ => noiseCovariance_germ F G hxor hA₀
          (fun b => remainderGaugeField_germ hF b A₀) hsm hPfin a j hj ι' ι,
      fun w hw _ => by
        beta_reduce
        rw [hvalues w hw]⟩
end YangMills.Construction.RunningCouplingSlope.KernelGerms
end
