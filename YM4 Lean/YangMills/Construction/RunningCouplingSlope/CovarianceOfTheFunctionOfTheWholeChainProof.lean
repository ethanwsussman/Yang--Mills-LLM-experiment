import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.EntriesOfTheFunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheForms
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsGaugeInvariantProof
set_option autoImplicit false

section
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ChainFunctionGaugeCovariance : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k),
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
        ∀ v : Vertex L n k 0 → Matrices.ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) →
          ((∀ x, Matrices.ComplexMatrix2.operatorNorm (v x - 1) < δ) ∨ ∀ x y, v x = v y) →
          ∀ (J' : LevelForms L n k) (μ' : edgeFormSpace L n k k),
            IsConjugatedCurrent v (e w).2.1 J' →
            (μ' : Edge L n k k → Matrices.ComplexMatrix2) =
              adjointForm (restrictVertexFunction k v)
                ((e w).2.2 : Edge L n k k → Matrices.ComplexMatrix2) →
            logRadiusSum (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) =
              logRadiusSum (expMove (e w).1 (unitPoint L n k)) ∧
            (∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ, q ξ =
              gaugedRightValue a (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) J' μ' ξ) ∧
            ∃ (A : LevelForms L n k ≃ₗ[ℝ] LevelForms L n k)
              (F : edgeFormSpace L n k k ≃ₗ[ℝ] edgeFormSpace L n k k)
              (G₀ : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] vertexFunctionSpace L n k 0)
              (Gk : vertexFunctionSpace L n k k ≃ₗ[ℝ] vertexFunctionSpace L n k k),
              (∀ ξ, IsConjugatedCurrent v ξ (A ξ)) ∧
              (∀ C : edgeFormSpace L n k k, (F C : Edge L n k k → Matrices.ComplexMatrix2) =
                adjointForm (restrictVertexFunction k v) (C : Edge L n k k → Matrices.ComplexMatrix2)) ∧
              (∀ l : vertexFunctionSpace L n k 0, (G₀ l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
                adjointVertexFn v (l : Vertex L n k 0 → Matrices.ComplexMatrix2)) ∧
              (∀ g : vertexFunctionSpace L n k k, (Gk g : Vertex L n k k → Matrices.ComplexMatrix2) =
                adjointVertexFn (restrictVertexFunction k v) (g : Vertex L n k k → Matrices.ComplexMatrix2)) ∧
              (∀ ξ ξ', levelPairing (formValues (A ξ)) (formValues (A ξ')) =
                levelPairing (formValues ξ) (formValues ξ')) ∧
              (∀ C C' : edgeFormSpace L n k k,
                (edgeFormPairing (F C : Edge L n k k → Matrices.ComplexMatrix2)
                    (F C' : Edge L n k k → Matrices.ComplexMatrix2)).re =
                  (edgeFormPairing (C : Edge L n k k → Matrices.ComplexMatrix2)
                    (C' : Edge L n k k → Matrices.ComplexMatrix2)).re) ∧
              (∀ ξ, gaugedRightValue a (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) J' μ' (A ξ) =
                gaugedRightValue a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2 ξ) ∧
              (∀ ξ, shiftedGaugeMap (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) (A ξ) =
                F (shiftedGaugeMap (expMove (e w).1 (unitPoint L n k)) ξ)) ∧
              ∀ y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k,
                ghostBlockOperator (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) (G₀ y.1, Gk y.2) =
                  (G₀ (ghostBlockOperator (expMove (e w).1 (unitPoint L n k)) y).1,
                    Gk (ghostBlockOperator (expMove (e w).1 (unitPoint L n k)) y).2)
end YangMills.Construction.RunningCouplingSlope
end
end

open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace RunningCouplingSlope
namespace ChainCovarianceProof
open YangMills.Construction.Tower
section InnerCores
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
private theorem transpose_comm_of_isometry (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ W)
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W) (hb : ∀ x y, c'.inner (b x) (b y) = c'.inner x y)
    (ha : ∀ x y, c.inner (a x) (a y) = c.inner x y)
    {T T' : V →ₗ[ℝ] W} {S S' : W →ₗ[ℝ] V} (hT : ∀ x, T' (a x) = b (T x))
    (hS : ∀ y x, c.inner (S y) x = c'.inner y (T x))
    (hS' : ∀ y x, c.inner (S' y) x = c'.inner y (T' x)) (y : W) :
    S' (b y) = a (S y) := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.adjoint_intertwine <;> assumption
end InnerCores
section MatrixFacts
private theorem inv_mul_cancel_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [h]; exact isUnit_one)
private theorem mul_inv_cancel_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V * V⁻¹ = 1 :=
  Matrix.mul_nonsing_inv V (by rw [h]; exact isUnit_one)
private theorem inv_inv_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [h]; exact isUnit_one)
private theorem det_eq_one_of_mem_compact {V : ComplexMatrix2}
    (h : V ∈ PeriodicLattice.compactGaugeGroup) : V.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem det_inv_of_det_one {g : ComplexMatrix2} (hg : g.det = 1) : (g⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
private theorem conj_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) = ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conj_sub (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X - Y) = ComplexMatrix2.conjugateBy g X - ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
private theorem conj_smul (g : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
private theorem conj_real_smul (g : ComplexMatrix2) (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
private theorem conj_zero (g : ComplexMatrix2) : ComplexMatrix2.conjugateBy g 0 = 0 := by
  simp only [ComplexMatrix2.conjugateBy, mul_zero, zero_mul]
private theorem conj_mul_conj {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g Y = ComplexMatrix2.conjugateBy g (X * Y) := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.conjugateBy_mul <;> assumption
private theorem conj_lie {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g ⁅X, Y⁆ = ⁅ComplexMatrix2.conjugateBy g X, ComplexMatrix2.conjugateBy g Y⁆ := by
  simp only [Ring.lie_def, conj_mul_conj hg, conj_sub]
private theorem halfTrace_conj_mul {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g Y) =
      ComplexMatrix2.halfTrace (X * Y) := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.halfTrace_conjugateBy <;> assumption
private theorem conj_conj_gauge {g h : ComplexMatrix2} (X A : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (g * X * h⁻¹) (ComplexMatrix2.conjugateBy h A) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy X A) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_conjugateBy_gauge <;> assumption
private def conjEquiv {g : ComplexMatrix2} (hg : g.det = 1) : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2 :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.mul ℂ ComplexMatrix2 g).comp ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip g⁻¹))
    ((ContinuousLinearMap.mul ℂ ComplexMatrix2 g⁻¹).comp ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip g))
    (fun Y => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
        ContinuousLinearMap.flip_apply]
      calc g⁻¹ * (g * (Y * g⁻¹) * g) = (g⁻¹ * g) * Y * (g⁻¹ * g) := by simp only [mul_assoc]
        _ = Y := by rw [inv_mul_cancel_of_det_one hg, one_mul, mul_one])
    (fun Y => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
        ContinuousLinearMap.flip_apply]
      calc g * (g⁻¹ * (Y * g) * g⁻¹) = (g * g⁻¹) * Y * (g * g⁻¹) := by simp only [mul_assoc]
        _ = Y := by rw [mul_inv_cancel_of_det_one hg, one_mul, mul_one])
private theorem conjEquiv_apply {g : ComplexMatrix2} (hg : g.det = 1) (Y : ComplexMatrix2) :
    conjEquiv hg Y = ComplexMatrix2.conjugateBy g Y := by
  change g * (Y * g⁻¹) = g * Y * g⁻¹
  rw [mul_assoc]
private theorem logSeries_conj {g : ComplexMatrix2} (hg : g.det = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.logSeries (g * X * g⁻¹) = ComplexMatrix2.conjugateBy g (ComplexMatrix2.logSeries X) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.logSeries_conj <;> assumption
private theorem gauge_mul_inv_gauge {g h W W₀ : ComplexMatrix2} (hh : h.det = 1) :
    (g * W * h⁻¹) * (g * W₀ * h⁻¹)⁻¹ = g * (W * W₀⁻¹) * g⁻¹ := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.mul_inv_gauge_conj <;> assumption
private theorem gauge_inv {g h X : ComplexMatrix2} (hh : h.det = 1) :
    (g * X * h⁻¹)⁻¹ = h * X⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_one hh, mul_assoc]
private theorem isUnit_det_of_compact {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem inv_mem_compact {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem norm_gauge_sub_one_le {a c X : ComplexMatrix2} (ha : a ∈ PeriodicLattice.compactGaugeGroup)
    (hc : c ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * c⁻¹ - 1‖ ≤ ‖X - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by apply _root_.YangMills.SharedProofs.p32758 <;> assumption
private theorem norm_conj_sub_one_of_compact {a X : ComplexMatrix2}
    (ha : a ∈ PeriodicLattice.compactGaugeGroup) : ‖a * X * a⁻¹ - 1‖ = ‖X - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_conj_sub_one_of_mem <;> assumption
private theorem conj_finsum_mem {ι : Type*} {g : ComplexMatrix2} (hg : g.det = 1) (S : Set ι)
    (f : ι → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (∑ᶠ x ∈ S, f x) = ∑ᶠ x ∈ S, ComplexMatrix2.conjugateBy g (f x) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_finsum_mem <;> assumption
private theorem logDirectionalDeriv_conj {α β : Type*} {g : ComplexMatrix2} (hg : g.det = 1)
    {φ : (α → ComplexMatrix2) → ComplexMatrix2} {ψ : (β → ComplexMatrix2) → ComplexMatrix2}
    {W W' : ComplexMatrix2} {A : α → ComplexMatrix2} {A' : β → ComplexMatrix2}
    (h : ∀ᶠ t : ℂ in 𝓝 0, ψ (t • A') * W'⁻¹ = g * (φ (t • A) * W⁻¹) * g⁻¹) :
    logDirectionalDeriv ℂ ψ W' A' = ComplexMatrix2.conjugateBy g (logDirectionalDeriv ℂ φ W A) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.logDirectionalDeriv_conj <;> assumption
end MatrixFacts
section SmallSets
private theorem isOpen_near_one_ball {ι : Type*} [Finite ι] (δ : ℝ) :
    IsOpen {V : ι → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < δ} := by apply _root_.YangMills.SharedProofs.p24342 <;> assumption
private theorem eventually_near_one {ι : Type*} [Finite ι] {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in 𝓝 (fun _ : ι => (1 : ComplexMatrix2)), ∀ b, ‖V b - 1‖ < δ :=
  (isOpen_near_one_ball δ).mem_nhds fun b => by simpa using hδ
private theorem exists_radius_of_nearOne {ι : Type*} [Finite ι] {D : Set (ι → ComplexMatrix2)}
    {P : (ι → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity D P) : ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ D, (∀ b, ‖V b - 1‖ < δ) → P V := by apply _root_.YangMills.SharedProofs.p388 <;> assumption
end SmallSets
section TowerFacts
variable {L n k i : ℕ}
private structure TowerData (L n k : ℕ) : Prop where
  side_pos : 0 < L
  xor_positive : ∀ i ≤ k, ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  polydisc_ok : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  mem_polydisc : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ smallComplexFields L n k i, V ∈ nearIdentityPolydisc (polydiscRadius L) c
  isOpen_nearOne : ∀ i < k, IsOpenFieldSet PeriodicLattice.complexGaugeGroup
    (MeanStableFields.fieldsNearOne L n k i)
  gauge_forms : ∀ i ≤ k, LeftChartFacts.GaugeEquivarianceForms L n k i
  left_chart : ∀ i ≤ k, ∀ V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup,
    ∀ B ∈ complexEdgeForms L n k i, ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b ∈ PeriodicLattice.complexGaugeGroup) ∧
        HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b)
          (Complex.I • B b * V b) 0
  left_chart_real : ∀ i ≤ k, ∀ V ∈ fieldSpace L n k i, ∀ B ∈ edgeFormSpace L n k i, ∀ b : Edge L n k i,
    b.IsPositivelyOriented → ComplexMatrix2.matExp (Complex.I • B b) * V b ∈ PeriodicLattice.compactGaugeGroup
  action_invariant : ∀ U ∈ fieldSpace L n k 0, ∀ u ∈ gaugeGroupAt L n k 0,
    plaquetteAction L n k (PeriodicLattice.gaugeTransform u U) = plaquetteAction L n k U
  mean_covariant : ∀ j < k, ∀ (V : Edge L n k j → ComplexMatrix2) (v : Vertex L n k j → ComplexMatrix2),
    (∀ x, (v x).det = 1) → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      contourMean (PeriodicLattice.gaugeTransform v V) c =
        v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourMean V c *
          (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹
private theorem bond_opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem TowerData.opposite_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases T.xor_positive i hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
private theorem TowerData.opposite_not_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases T.xor_positive i hi b with h | h
  · exact h.2
  · exact absurd hb h.2
private theorem extendOddly_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
private theorem extendOddly_neg {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
private theorem extendOddly_congr (T : TowerData L n k) (hi : i ≤ k) {g g' : Edge L n k i → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → g b = g' b) : extendOddly g = extendOddly g' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_pos hb, extendOddly_pos hb, h b hb]
  · rw [extendOddly_neg hb, extendOddly_neg hb, h _ (T.opposite_pos hi hb)]
private theorem extendOddly_opposite (T : TowerData L n k) (hi : i ≤ k) (g : Edge L n k i → ComplexMatrix2)
    (b : Edge L n k i) : extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_neg (T.opposite_not_pos hi hb), extendOddly_pos hb, bond_opposite_opposite]
  · rw [extendOddly_pos (T.opposite_pos hi hb), extendOddly_neg hb, neg_neg]
private theorem adjointForm_pos (u : Vertex L n k i → ComplexMatrix2) (B : Edge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) :=
  extendOddly_pos hb
private theorem adjointForm_add (u : Vertex L n k i → ComplexMatrix2) (B B' : Edge L n k i → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.adjointForm_add <;> assumption
private theorem smul_adjointForm (u : Vertex L n k i → ComplexMatrix2) (t : ℂ) (B : Edge L n k i → ComplexMatrix2) :
    t • adjointForm u B = adjointForm u (t • B) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.smul_adjointForm <;> assumption
private theorem adjointVertexFn_add (u l l' : Vertex L n k i → ComplexMatrix2) :
    adjointVertexFn u (l + l') = adjointVertexFn u l + adjointVertexFn u l' :=
  funext fun _ => conj_add _ _ _
private theorem covDiff_gauge (T : TowerData L n k) (hi : i ≤ k) {u : Vertex L n k i → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) (U : Edge L n k i → ComplexMatrix2) (l : Vertex L n k i → ComplexMatrix2) :
    covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
      adjointForm u (covDiff U l) := by
  unfold adjointForm
  refine (extendOddly_congr T hi fun b hb => ?_ :
    extendOddly (fun b => ComplexMatrix2.conjugateBy (PeriodicLattice.gaugeTransform u U b)
      (adjointVertexFn u l b.target) - adjointVertexFn u l b.source) = _)
  have hD : covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source := extendOddly_pos hb
  change ComplexMatrix2.conjugateBy (u b.source * U b * (u b.target)⁻¹)
      (ComplexMatrix2.conjugateBy (u b.target) (l b.target)) -
    ComplexMatrix2.conjugateBy (u b.source) (l b.source) =
      ComplexMatrix2.conjugateBy (u b.source) (covDiff U l b)
  rw [hD, conj_conj_gauge _ _ (hu _), conj_sub]
private theorem expTwist_pos {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b := if_pos hb
private theorem expTwist_neg {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b = (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem expTwist_mem (T : TowerData L n k) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) :
    PeriodicLattice.expTwist B V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  have hp : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • B b) * V b).det = 1 := fun b hb => by
    have := (T.left_chart i hi V hV B hB b hb).1 1
    rwa [one_smul] at this
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_pos hb]
      exact hp b hb
    · rw [expTwist_neg hb]
      exact det_inv_of_det_one (hp _ (T.opposite_pos hi hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_neg (T.opposite_not_pos hi hb), expTwist_pos hb, bond_opposite_opposite]
    · have hr := T.opposite_pos hi hb
      rw [expTwist_pos hr, expTwist_neg hb, inv_inv_of_det_one (hp _ hr)]
private theorem expTwist_zero_smul (T : TowerData L n k) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_pos hb]
    simp [ComplexMatrix2.matExp]
  · have hr := T.opposite_pos hi hb
    rw [expTwist_neg hb]
    have := hV.2 b.opposite (mem_univ _)
    rw [bond_opposite_opposite] at this
    simp [ComplexMatrix2.matExp, this]
private theorem eq_of_restrict_eq (T : TowerData L n k) (hi : i ≤ k) {V V' : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hV' : V' ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (h : restrictToPositiveEdges V = restrictToPositiveEdges V') : V = V' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact congrFun h ⟨b, hb⟩
  · have hr := T.opposite_pos hi hb
    have h₁ := hV.2 b.opposite (mem_univ _)
    have h₂ := hV'.2 b.opposite (mem_univ _)
    rw [bond_opposite_opposite] at h₁ h₂
    rw [h₁, h₂, show V b.opposite = V' b.opposite from congrFun h ⟨b.opposite, hr⟩]
private theorem eventually_expTwist_small (T : TowerData L n k) (hj : i < k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k i) (hB : B ∈ complexEdgeForms L n k i) :
    ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • B) V ∈ smallComplexFields L n k i := by
  obtain ⟨-, O, hO, himg⟩ := T.isOpen_nearOne i hj
  have hV0 : restrictToPositiveEdges V ∈ O := by
    have : restrictToPositiveEdges V ∈ restrictToPositiveEdges ''
        MeanStableFields.fieldsNearOne L n k i :=
      mem_image_of_mem _ hV
    rw [himg] at this
    exact this.1
  have hcont : ContinuousAt
      (fun t : ℂ => restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V)) 0 := by
    refine continuousAt_pi.2 fun b => ?_
    have hd := (T.left_chart i hj.le V hV.1 B hB b.1 b.2).2.continuousAt
    refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
    change _ = PeriodicLattice.expTwist (t • B) V b.1
    rw [expTwist_pos b.2]
    rfl
  have h0 : restrictToPositiveEdges (PeriodicLattice.expTwist ((0 : ℂ) • B) V) = restrictToPositiveEdges V := by
    rw [expTwist_zero_smul T hj.le hV.1]
  have hev : ∀ᶠ t : ℂ in 𝓝 0, restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈ O :=
    hcont.eventually_mem (by rw [h0]; exact hO.mem_nhds hV0)
  filter_upwards [hev] with t ht
  have hm := expTwist_mem T hj.le hV.1 ((complexEdgeForms L n k i).smul_mem t hB)
  have hmem : restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈ restrictToPositiveEdges ''
      MeanStableFields.fieldsNearOne L n k i := by
    rw [himg]
    exact ⟨ht, fun b => hm.1 _ (mem_univ _)⟩
  obtain ⟨W, hW, he⟩ := hmem
  have : W = PeriodicLattice.expTwist (t • B) V := eq_of_restrict_eq T hj.le hW.1 hm he
  exact this ▸ hW
end TowerFacts
section StepMaps
variable {L n k i : ℕ} {V : Edge L n k i → ComplexMatrix2} {u : Vertex L n k i → ComplexMatrix2}
private theorem det_of_gauge (hu : u ∈ gaugeGroupAt L n k i) (x : Vertex L n k i) : (u x).det = 1 :=
  det_eq_one_of_mem_compact (hu x)
private theorem expTwist_smul_gauge (T : TowerData L n k) (hi : i ≤ k)
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hu : u ∈ gaugeGroupAt L n k i) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) (t : ℂ) :
    PeriodicLattice.expTwist (t • adjointForm u B) (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist (t • B) V) := by
  rw [smul_adjointForm]
  exact (T.gauge_forms i hi u (fun x => det_of_gauge hu x)).1 V hV (t • B)
    ((complexEdgeForms L n k i).smul_mem t hB)
private theorem contour_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x =
      u (y.toSublattice (PeriodicLattice.levelDepth k i)) *
        PeriodicLattice.complexMeanContourHolonomy V y x * (u x)⁻¹ := by
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  exact ((T.polydisc_ok i hi _ hc).gauge_covariant V (T.mem_polydisc i hi _ hc V hV) u hu).2.2 y
    (Or.inl rfl) x hx
private theorem adjointCubeAverage_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i)
    (l : Vertex L n k i → ComplexMatrix2) :
    adjointCubeAverage (PeriodicLattice.gaugeTransform u V) (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction (i + 1) u) (adjointCubeAverage V l) := by
  funext y
  have hg : (u (y.toSublattice (PeriodicLattice.levelDepth k i))).det = 1 := det_of_gauge hu _
  change PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      ComplexMatrix2.conjugateBy
        (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x)
        (ComplexMatrix2.conjugateBy (u x) (l x)) =
    ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i)))
      (PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x))
  rw [conj_smul, conj_finsum_mem hg]
  congr 1
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [contour_gauge T hi hV hu y hx, conj_conj_gauge _ _ (det_of_gauge hu x)]
private theorem logDeriv_summand_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
    {B : Edge L n k i → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k i) :
    logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy
          (PeriodicLattice.expTwist X (PeriodicLattice.gaugeTransform u V)) y x)
        (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x)
        (adjointForm u B) =
      ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i)))
        (logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
          (PeriodicLattice.complexMeanContourHolonomy V y x) B) := by
  refine logDirectionalDeriv_conj (det_of_gauge hu _) ?_
  filter_upwards [eventually_expTwist_small T hi hV hB] with t ht
  rw [expTwist_smul_gauge T hi.le hV.1 hu hB t, contour_gauge T hi ht hu y hx,
    contour_gauge T hi hV hu y hx]
  exact gauge_mul_inv_gauge (det_of_gauge hu x)
private theorem contourLogDrift_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i)
    (hu : u ∈ gaugeGroupAt L n k i) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) :
    contourLogDrift (PeriodicLattice.gaugeTransform u V) (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction (i + 1) u) (contourLogDrift V B) := by
  funext y
  have hg : (u (y.toSublattice (PeriodicLattice.levelDepth k i))).det = 1 := det_of_gauge hu _
  change PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy
          (PeriodicLattice.expTwist X (PeriodicLattice.gaugeTransform u V)) y x)
        (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x)
        (adjointForm u B) =
    ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i)))
      (PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
          (PeriodicLattice.complexMeanContourHolonomy V y x) B)
  rw [conj_smul, conj_finsum_mem hg]
  congr 1
  exact finsum_mem_congr rfl fun x hx => logDeriv_summand_gauge T hi hV hu y hx hB
end StepMaps
section LevelMaps
variable {L n k : ℕ} {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
private theorem restrictVertexFunction_zero (hL : 0 < L) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 l = l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_zero <;> assumption
private theorem restrictVertexFunction_succ (hL : 0 < L) (i : ℕ) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (restrictVertexFunction i l) = restrictVertexFunction (i + 1) l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_succ <;> assumption
private theorem restrictVertexFunction_mem (hu : u ∈ gaugeGroupAt L n k 0) (i : ℕ) :
    restrictVertexFunction i u ∈ gaugeGroupAt L n k i :=
  fun _ => hu _
private theorem extendByZero_gauge (hL : 0 < L) (g : Vertex L n k k → ComplexMatrix2) :
    _root_.YangMills.Construction.Tower.extendByZero (adjointVertexFn (restrictVertexFunction k u) g) = adjointVertexFn u (_root_.YangMills.Construction.Tower.extendByZero g) := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.extendByZero_adjoint <;> assumption
end LevelMaps
section PairingFacts
variable {L n k i : ℕ}
private theorem pairing_conj {ι : Type*} {v : ι → ComplexMatrix2} (hv : ∀ x, (v x).det = 1)
    (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (fun x => ComplexMatrix2.conjugateBy (v x) (f x))
      (fun x => ComplexMatrix2.conjugateBy (v x) (g x)) = traceFinsumPairing f g :=
  finsum_congr fun x => halfTrace_conj_mul (hv x) _ _
private theorem restrictPositive_adjointForm (u : Vertex L n k i → ComplexMatrix2)
    (f : Edge L n k i → ComplexMatrix2) :
    restrictToPositiveEdges (adjointForm u f) =
      fun b : PositiveEdge L n k i => ComplexMatrix2.conjugateBy (u b.1.source) (restrictToPositiveEdges f b) :=
  funext fun b => adjointForm_pos _ _ b.2
private theorem edgeFormPairing_adjointForm {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f g : Edge L n k i → ComplexMatrix2) :
    edgeFormPairing (adjointForm u f) (adjointForm u g) = edgeFormPairing f g := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.edgeFormPairing_adjointForm <;> assumption
private theorem pairing_adjointVertexFn {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f g : Vertex L n k i → ComplexMatrix2) :
    traceFinsumPairing (adjointVertexFn u f) (adjointVertexFn u g) = traceFinsumPairing f g :=
  pairing_conj hd f g
private theorem norm_adjointVertexFn {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f : Vertex L n k i → ComplexMatrix2) : traceFinsumNorm (adjointVertexFn u f) = traceFinsumNorm f := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.norm_adjointVertexFn <;> assumption
private theorem bracketTerm_gauge (T : TowerData L n k) {u : Vertex L n k 0 → ComplexMatrix2}
    (hd : ∀ x, (u x).det = 1)
    (U : Edge L n k 0 → ComplexMatrix2) (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    bracketTerm (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) (adjointForm u B) =
      adjointForm u (bracketTerm U l B) := by
  show extendOddly _ = extendOddly _
  refine extendOddly_congr T (Nat.zero_le k) fun b hb => ?_
  rw [adjointForm_pos _ _ hb]
  have e : bracketTerm U l B b =
      (Complex.I / 2) • ⁅l b.source + ComplexMatrix2.conjugateBy (U b) (l b.target), B b⁆ :=
    extendOddly_pos hb
  rw [e, conj_smul, conj_lie (hd _), conj_add]
  show (Complex.I / 2) • ⁅ComplexMatrix2.conjugateBy (u b.source) (l b.source) +
      ComplexMatrix2.conjugateBy (u b.source * U b * (u b.target)⁻¹)
        (ComplexMatrix2.conjugateBy (u b.target) (l b.target)),
      ComplexMatrix2.conjugateBy (u b.source) (B b)⁆ = _
  rw [conj_conj_gauge _ _ (hd _)]
end PairingFacts
section MeanAtAnyField
variable {L n k j : ℕ}
private theorem holonomy_gauge {v : Vertex L n k j → ComplexMatrix2} (hd : ∀ x, (v x).det = 1)
    (V : Edge L n k j → ComplexMatrix2) :
    ∀ (Γ : List (Edge L n k j)) (x x' : Vertex L n k j), PeriodicLattice.IsBondPathFromTo Γ x x' →
      PeriodicLattice.pathHolonomy (PeriodicLattice.gaugeTransform v V) Γ =
        v x * PeriodicLattice.pathHolonomy V Γ * (v x')⁻¹ := by
  intro Γ
  induction Γ with
  | nil =>
    intro x x' h
    obtain rfl := h.2.1 rfl
    simp [PeriodicLattice.pathHolonomy, mul_inv_cancel_of_det_one (hd x)]
  | cons b Γ ih =>
    intro x x' h
    obtain ⟨hp, -, hh, hl⟩ := h
    obtain rfl : b.source = x := hh b (by simp)
    have hΓ : PeriodicLattice.IsBondPathFromTo Γ b.target x' := by
      cases Γ with
      | nil => exact ⟨List.isChain_nil, fun _ => hl b (by simp), by simp, by simp⟩
      | cons b' Γ' =>
        have hc := List.isChain_cons_cons.1 hp
        refine ⟨hc.2, by simp, fun b'' hb => ?_, fun b'' hb => hl b'' (by simpa using hb)⟩
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst hb
        exact hc.1.symm
    have e := ih _ _ hΓ
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at e ⊢
    rw [e]
    show (v b.source * V b * (v b.target)⁻¹) * (v b.target * _ * (v x')⁻¹) = _
    have hi := inv_mul_cancel_of_det_one (hd b.target)
    simp only [mul_assoc]
    rw [← mul_assoc (v b.target)⁻¹, hi, one_mul]
private theorem contourMean_gauge (hlegs : AxisOrderLegsAreContours)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (V : Edge L n k j → ComplexMatrix2)
    (v : Vertex L n k j → ComplexMatrix2) (hd : ∀ x, (v x).det = 1) (c : Edge L n k (j + 1))
    (hc : c.IsPositivelyOriented) :
    contourMean (PeriodicLattice.gaugeTransform v V) c =
      v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourMean V c *
        (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ := by
  have hLpos : 0 < L := by have := hL.2; omega
  have hK : 0 < k := by omega
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hc
  have hgauge := fun (Γ : List (Edge L n k j)) (x x' : Vertex L n k j)
      (h : PeriodicLattice.IsBondPathFromTo Γ x x') => holonomy_gauge hd V Γ x x' h
  have hleg : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j), (x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock y → ∀ π, PeriodicLattice.IsBondPathFromTo (contourLeg y x π)
        (y.toSublattice (PeriodicLattice.levelDepth k j)) x := by
    intro y x hx π
    obtain ⟨σ, hσ⟩ := hlegs L n _ _ y x π
    have := ((hcf L n k hL hn j hj y x hx).2.1 _ ⟨σ, rfl⟩).1
    rw [← hσ] at this
    exact this
  have hcv : ∀ x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)), ∀ π, contourHolonomy (PeriodicLattice.gaugeTransform v V) c x π =
      v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourHolonomy V c x π *
        (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ := by
    intro x hx π
    have hx' : PeriodicLattice.shiftAcross c x ∈
        (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.target :
          Set (Vertex L n k j)) := hcross.1.mapsTo hx
    rw [contourHolonomy, contourHolonomy, hgauge _ _ _ (hleg _ _ hx π),
      hgauge _ _ _ (hcross.2 x hx).1, hgauge _ _ _ (hleg _ _ hx' π)]
    have a1 : ∀ M : ComplexMatrix2, (v x)⁻¹ * (v x * M) = M := fun M => by
      rw [← mul_assoc, inv_mul_cancel_of_det_one (hd x), one_mul]
    have a2 : ∀ M : ComplexMatrix2, (v (PeriodicLattice.shiftAcross c x))⁻¹ *
        (v (PeriodicLattice.shiftAcross c x) * M) = M := fun M => by
      rw [← mul_assoc, inv_mul_cancel_of_det_one (hd _), one_mul]
    have hu : IsUnit (Matrix.det (v (PeriodicLattice.shiftAcross c x))) := by
      rw [hd]; exact isUnit_one
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu]
    simp only [mul_assoc, a1, a2]
  rw [contourMean, contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  exact hcv x (by simpa using hx) π
private theorem TowerData.meanRadius_gauge (T : TowerData L n k) (hj : j < k) (V : Edge L n k j → ComplexMatrix2)
    {v : Vertex L n k j → ComplexMatrix2} (hd : ∀ x, (v x).det = 1) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    meanRadius (PeriodicLattice.gaugeTransform v V) c = meanRadius V c := by
  rw [meanRadius, meanRadius, T.mean_covariant j hj V v hd c hc, Matrix.det_mul, Matrix.det_mul, hd,
    Matrix.det_nonsing_inv, hd]
  simp
private theorem TowerData.normalizedMean_gauge (T : TowerData L n k) (hj : j < k)
    (V : Edge L n k j → ComplexMatrix2)
    {v : Vertex L n k j → ComplexMatrix2} (hd : ∀ x, (v x).det = 1) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    normalizedMean (PeriodicLattice.gaugeTransform v V) c =
      v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * normalizedMean V c *
        (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ := by
  rw [normalizedMean, normalizedMean, T.meanRadius_gauge hj V hd hc, T.mean_covariant j hj V v hd c hc,
    Matrix.mul_smul, Matrix.smul_mul]
end MeanAtAnyField
section LeftChart
variable {L n k i : ℕ}
private theorem matExp_conj {g : ComplexMatrix2} (hg : g.det = 1) (Y : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g Y) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.matExp (Complex.I • Y)) := by
  rw [← conj_smul]
  simp only [ComplexMatrix2.conjugateBy, ComplexMatrix2.matExp]
  exact Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [hg]; exact isUnit_one))
private theorem matExp_mul_gauge {g h : ComplexMatrix2} (hg : g.det = 1) (Y V : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g Y) * (g * V * h⁻¹) =
      g * (ComplexMatrix2.matExp (Complex.I • Y) * V) * h⁻¹ := by
  rw [matExp_conj hg]
  simp only [ComplexMatrix2.conjugateBy]
  calc g * ComplexMatrix2.matExp (Complex.I • Y) * g⁻¹ * (g * V * h⁻¹)
      = g * ComplexMatrix2.matExp (Complex.I • Y) * (g⁻¹ * g) * V * h⁻¹ := by simp only [mul_assoc]
    _ = g * (ComplexMatrix2.matExp (Complex.I • Y) * V) * h⁻¹ := by
      rw [inv_mul_cancel_of_det_one hg, mul_one]; simp only [mul_assoc]
private theorem expTwist_gauge (T : TowerData L n k) (hi : i ≤ k) {u : Vertex L n k i → ComplexMatrix2}
    (hd : ∀ x, (u x).det = 1) (A V : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.expTwist (adjointForm u A) (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist A V) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_pos hb, adjointForm_pos _ _ hb]
    show _ * (u b.source * V b * (u b.target)⁻¹) =
      u b.source * PeriodicLattice.expTwist A V b * (u b.target)⁻¹
    rw [expTwist_pos hb]
    exact matExp_mul_gauge (hd _) _ _
  · have hr := T.opposite_pos hi hb
    rw [expTwist_neg hb, adjointForm_pos _ _ hr]
    show (_ * (u b.opposite.source * V b.opposite * (u b.opposite.target)⁻¹))⁻¹ =
      u b.source * PeriodicLattice.expTwist A V b * (u b.target)⁻¹
    rw [expTwist_neg hb, matExp_mul_gauge (hd _), gauge_inv (hd _)]
    rfl
private theorem expTwist_mem_fields (T : TowerData L n k) {V B : Edge L n k 0 → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k 0) (hB : B ∈ edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist B V ∈ fieldSpace L n k 0 := by
  have hz := Nat.zero_le k
  have hl := T.left_chart_real 0 hz
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_pos hb]
      exact hl V hV B hB b hb
    · rw [expTwist_neg hb]
      exact inv_mem_compact (hl V hV B hB _ (T.opposite_pos hz hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_neg (T.opposite_not_pos hz hb), expTwist_pos hb, bond_opposite_opposite]
    · have hr := T.opposite_pos hz hb
      rw [expTwist_pos hr, expTwist_neg hb,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hl V hV B hB _ hr))]
private theorem fieldOfValues_gauge (T : TowerData L n k) (hi : i ≤ k) {g : Vertex L n k i → ComplexMatrix2}
    (hg : ∀ x, (g x).det = 1) (w : PositiveEdge L n k i → ComplexMatrix2) :
    fieldOfPositiveValues (fun c : PositiveEdge L n k i => g c.1.source * w c * (g c.1.target)⁻¹) =
      PeriodicLattice.gaugeTransform g (fieldOfPositiveValues w) := by
  funext b
  show _ = g b.source * fieldOfPositiveValues w b * (g b.target)⁻¹
  by_cases hb : b.IsPositivelyOriented
  · simp only [fieldOfPositiveValues, dif_pos hb]
  · have hr := T.opposite_pos hi hb
    simp only [fieldOfPositiveValues, dif_neg hb, dif_pos hr]
    exact gauge_inv (hg _)
end LeftChart
section ChainFacts
variable {L n k j : ℕ} {v : Vertex L n k 0 → ComplexMatrix2}
private theorem levelField_succ (X : ChainPoint L n k) (h : j < k) :
    levelField X (j + 1) = fieldOfPositiveValues fun c =>
      X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp only [levelField, dif_pos h]
private theorem det_restrict (hd : ∀ x, (v x).det = 1) (i : ℕ) (x : Vertex L n k i) :
    (restrictVertexFunction i v x).det = 1 := hd _
private theorem restrict_toSublattice (T : TowerData L n k) (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y :=
  congrFun (restrictVertexFunction_succ T.side_pos j v) y
private theorem levelField_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k) :
    ∀ j ≤ k, levelField (gaugeTransformPoint v X) j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X j) := by
  intro j
  induction j with
  | zero =>
    intro _
    show PeriodicLattice.gaugeTransform v X.fine =
      PeriodicLattice.gaugeTransform (restrictVertexFunction 0 v) X.fine
    rw [restrictVertexFunction_zero T.side_pos]
  | succ j ih =>
    intro hj
    have h : j < k := hj
    rw [levelField_succ _ h, levelField_succ _ h, ih h.le,
      ← fieldOfValues_gauge T hj (det_restrict hd (j + 1))]
    congr 1
    funext c
    have hg := det_restrict hd (j + 1) c.1.source
    rw [T.normalizedMean_gauge h _ (det_restrict hd j) c.2, restrict_toSublattice T, restrict_toSublattice T]
    show restrictVertexFunction (j + 1) v c.1.source * X.noise ⟨j, h⟩ c *
      (restrictVertexFunction (j + 1) v c.1.source)⁻¹ * _ = _
    calc _ = restrictVertexFunction (j + 1) v c.1.source * X.noise ⟨j, h⟩ c *
          ((restrictVertexFunction (j + 1) v c.1.source)⁻¹ * restrictVertexFunction (j + 1) v c.1.source) *
          normalizedMean (levelField X j) c.1 * (restrictVertexFunction (j + 1) v c.1.target)⁻¹ := by
          simp only [mul_assoc]
      _ = _ := by rw [inv_mul_cancel_of_det_one hg, mul_one]; simp only [mul_assoc]
private theorem meanRadius_chain (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    meanRadius (levelField (gaugeTransformPoint v X) i) c.1 = meanRadius (levelField X i) c.1 := by
  rw [levelField_gauge T hd X i i.2.le, T.meanRadius_gauge i.2 _ (det_restrict hd i) c.2]
private theorem logRadiusSum_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k) :
    logRadiusSum (gaugeTransformPoint v X) = logRadiusSum X := by
  unfold logRadiusSum
  refine Finset.sum_congr rfl fun i _ => finsum_congr fun c => ?_
  rw [meanRadius_chain T hd]
private theorem traceDefect_conj {g : ComplexMatrix2} (hg : g.det = 1) (m : ComplexMatrix2) :
    traceDefect (g * m * g⁻¹) = traceDefect m := by
  simp only [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_cancel_of_det_one hg, one_mul]
private theorem chainAction_gauge (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0) (a : ℝ)
    (X : ChainPoint L n k) (hX : X.fine ∈ fieldSpace L n k 0) :
    chainAction a (gaugeTransformPoint v X) = chainAction a X := by
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hv
  have e : plaquetteAction L n k (gaugeTransformPoint v X).fine = plaquetteAction L n k X.fine :=
    T.action_invariant _ hX _ hv
  have e2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (meanRadius (levelField (gaugeTransformPoint v X) i) c.1).re *
          traceDefect ((gaugeTransformPoint v X).noise i c) =
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) := fun i c => by
    rw [meanRadius_chain T hd X i c]
    exact congrArg _ (traceDefect_conj (det_restrict hd _ _) _)
  have e3 : (∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (levelField (gaugeTransformPoint v X) i) c.1).re *
        traceDefect ((gaugeTransformPoint v X).noise i c)) =
      ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) :=
    Finset.sum_congr rfl fun i _ => finsum_congr fun c => e2 i c
  unfold chainAction
  rw [e, e3]
private theorem expMove_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    {ξ ξ' : LevelForms L n k} (h : IsConjugatedCurrent v ξ ξ') :
    expMove ξ' (gaugeTransformPoint v X) = gaugeTransformPoint v (expMove ξ X) := by
  have h1 : (ξ'.1 : Edge L n k 0 → ComplexMatrix2) = adjointForm v ξ.1 := congrArg Prod.fst h
  have h2 : ∀ i : Fin k, (ξ'.2 i : Edge L n k (i + 1) → ComplexMatrix2) =
      adjointForm (restrictVertexFunction ((i : ℕ) + 1) v) (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) :=
    fun i => congrFun (congrArg Prod.snd h) i
  unfold expMove gaugeTransformPoint
  congr 1
  · rw [h1]
    exact expTwist_gauge T (Nat.zero_le k) hd _ _
  · funext i c
    rw [h2 i, adjointForm_pos _ _ c.2]
    exact matExp_mul_gauge (det_restrict hd _ _) _ _
private theorem expMove_fine_mem (T : TowerData L n k) {X : ChainPoint L n k}
    (hX : X.fine ∈ fieldSpace L n k 0) (η : LevelForms L n k) :
    (expMove η X).fine ∈ fieldSpace L n k 0 :=
  expTwist_mem_fields T hX η.1.2
private theorem leftSecondDeriv_gauge (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0) (a : ℝ)
    {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (A : LevelForms L n k →ₗ[ℝ] LevelForms L n k)
    (hA : ∀ ξ, IsConjugatedCurrent v ξ (A ξ)) (ξ ξ' : LevelForms L n k) :
    leftSecondDeriv (chainAction a) (gaugeTransformPoint v X) (A ξ) (A ξ') =
      leftSecondDeriv (chainAction a) X ξ ξ' := by
  have key : ∀ s t : ℝ, chainAction a (expMove (s • A ξ + t • A ξ') (gaugeTransformPoint v X)) =
      chainAction a (expMove (s • ξ + t • ξ') X) := by
    intro s t
    have hb := expMove_fine_mem T hX (s • ξ + t • ξ')
    have e : s • A ξ + t • A ξ' = A (s • ξ + t • ξ') := by
      rw [map_add, map_smul, map_smul]
    rw [e, expMove_gauge T (det_of_gauge hv) X (hA _), chainAction_gauge T hv a _ hb]
  simp only [leftSecondDeriv, key]
end ChainFacts
section RotatedValues
variable {L n k j : ℕ} {v : Vertex L n k 0 → ComplexMatrix2}
private theorem deriv_clEquiv_real (E : ComplexMatrix2 ≃L[ℝ] ComplexMatrix2) (f : ℝ → ComplexMatrix2) :
    deriv (fun t => E (f t)) 0 = E (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((E : ComplexMatrix2 →L[ℝ] ComplexMatrix2).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv
  · have hn : ¬ DifferentiableAt ℝ (fun t => E (f t)) 0 := fun h =>
      hf (E.comp_differentiableAt_iff.1 h)
    rw [deriv_zero_of_not_differentiableAt hn, deriv_zero_of_not_differentiableAt hf, map_zero]
private def conjEquivReal {g : ComplexMatrix2} (hg : g.det = 1) : ComplexMatrix2 ≃L[ℝ] ComplexMatrix2 :=
  (conjEquiv hg).restrictScalars ℝ
private theorem conjEquivReal_apply {g : ComplexMatrix2} (hg : g.det = 1) (Y : ComplexMatrix2) :
    conjEquivReal hg Y = ComplexMatrix2.conjugateBy g Y :=
  conjEquiv_apply hg Y
private theorem odd_ext (T : TowerData L n k) (hi : j ≤ k) {B B' : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, B b.opposite = -B b) (hB' : ∀ b, B' b.opposite = -B' b)
    (h : ∀ b, b.IsPositivelyOriented → B b = B' b) : B = B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := T.opposite_pos hi hb
    have e₁ := hB b.opposite
    have e₂ := hB' b.opposite
    rw [bond_opposite_opposite] at e₁ e₂
    rw [e₁, e₂, h _ hr]
private def rotateValues (v : Vertex L n k 0 → ComplexMatrix2) (x : LevelValues L n k) : LevelValues L n k :=
  (adjointForm v x.1, fun i => adjointForm (restrictVertexFunction ((i : ℕ) + 1) v) (x.2 i))
private theorem rotateValues_add (x y : LevelValues L n k) :
    rotateValues v (x + y) = rotateValues v x + rotateValues v y :=
  Prod.ext (adjointForm_add _ _ _) (funext fun _ => adjointForm_add _ _ _)
private theorem levelPairing_rotateValues (hd : ∀ x, (v x).det = 1) (x y : LevelValues L n k) :
    levelPairing (rotateValues v x) (rotateValues v y) = levelPairing x y := by
  unfold levelPairing rotateValues
  simp only [edgeFormPairing_adjointForm hd, edgeFormPairing_adjointForm (det_restrict hd _)]
private theorem leftDifferential_gauge (T : TowerData L n k) (hj : j < k) {u : Vertex L n k j → ComplexMatrix2}
    (hd : ∀ x, (u x).det = 1) (W B : Edge L n k j → ComplexMatrix2) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    leftDifferential normalizedMean (PeriodicLattice.gaugeTransform u W) (adjointForm u B) c =
      ComplexMatrix2.conjugateBy (u (c.source.toSublattice (PeriodicLattice.levelDepth k j)))
        (leftDifferential normalizedMean W B c) := by
  have hg := hd (c.source.toSublattice (PeriodicLattice.levelDepth k j))
  have e₁ : ∀ W' B' : Edge L n k j → ComplexMatrix2, leftDifferential normalizedMean W' B' c =
      logDirectionalDeriv ℝ (fun X => normalizedMean (PeriodicLattice.expTwist X W') c)
        (normalizedMean W' c) B' := fun _ _ => if_pos hc
  rw [e₁, e₁]
  unfold logDirectionalDeriv
  have key : ∀ t : ℝ, ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ t • adjointForm u B) (PeriodicLattice.gaugeTransform u W)) c *
        (normalizedMean (PeriodicLattice.gaugeTransform u W) c)⁻¹) =
      conjEquivReal hg (ComplexMatrix2.logSeries
        (normalizedMean (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) W) c *
        (normalizedMean W c)⁻¹)) := by
    intro t
    rw [smul_adjointForm, expTwist_gauge T hj.le hd, T.normalizedMean_gauge hj _ hd hc,
      T.normalizedMean_gauge hj _ hd hc, gauge_mul_inv_gauge (hd _), logSeries_conj hg,
      conjEquivReal_apply]
  simp only [key]
  rw [deriv_clEquiv_real, conjEquivReal_apply, conj_smul]
private theorem tangentTransport_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) (h : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by
  simp only [tangentTransport, dif_pos h]
  rw [extendOddly_pos hc, dif_pos hc]
private theorem tangentTransport_opposite (T : TowerData L n k) (X : ChainPoint L n k) (ξ : LevelForms L n k)
    (h : j < k) (b : Edge L n k (j + 1)) :
    tangentTransport X ξ (j + 1) b.opposite = -tangentTransport X ξ (j + 1) b := by
  simp only [tangentTransport, dif_pos h]
  exact extendOddly_opposite T h _ b
private theorem tangentTransport_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    {ξ ξ' : LevelForms L n k} (h : IsConjugatedCurrent v ξ ξ') :
    ∀ j ≤ k, tangentTransport (gaugeTransformPoint v X) ξ' j =
      adjointForm (restrictVertexFunction j v) (tangentTransport X ξ j) := by
  have h2 : ∀ i : Fin k, (ξ'.2 i : Edge L n k (i + 1) → ComplexMatrix2) =
      adjointForm (restrictVertexFunction ((i : ℕ) + 1) v) (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) :=
    fun i => congrFun (congrArg Prod.snd h) i
  intro j
  induction j with
  | zero =>
    intro _
    show (ξ'.1 : Edge L n k 0 → ComplexMatrix2) = adjointForm (restrictVertexFunction 0 v) ξ.1
    rw [restrictVertexFunction_zero T.side_pos]
    exact congrArg Prod.fst h
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    refine odd_ext T hj (tangentTransport_opposite T _ _ hlt) (extendOddly_opposite T hj _) fun c hc => ?_
    have e : (ξ'.2 ⟨j, hlt⟩ : Edge L n k (j + 1) → ComplexMatrix2) c =
        ComplexMatrix2.conjugateBy (restrictVertexFunction (j + 1) v c.source)
          ((ξ.2 ⟨j, hlt⟩ : Edge L n k (j + 1) → ComplexMatrix2) c) := by
      have := congrFun (h2 ⟨j, hlt⟩) c
      exact this.trans (adjointForm_pos _ _ hc)
    rw [tangentTransport_pos _ _ hlt hc, adjointForm_pos _ _ hc, tangentTransport_pos _ _ hlt hc, ih hlt.le,
      levelField_gauge T hd X j hlt.le, leftDifferential_gauge T hlt (det_restrict hd j) _ _ hc,
      restrict_toSublattice T, e, conj_add]
    show ComplexMatrix2.conjugateBy (restrictVertexFunction (j + 1) v c.source * X.noise ⟨j, hlt⟩ ⟨c, hc⟩ *
      (restrictVertexFunction (j + 1) v c.source)⁻¹) _ + _ = _
    rw [conj_conj_gauge _ _ (det_restrict hd _ _)]
private theorem chainDrift_gauge (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0)
    (X : ChainPoint L n k) (hs : ∀ j < k, levelField X j ∈ smallComplexFields L n k j)
    {ξ ξ' : LevelForms L n k} (h : IsConjugatedCurrent v ξ ξ')
    (hf : ∀ j ≤ k, tangentTransport X ξ j ∈ complexEdgeForms L n k j) :
    ∀ j ≤ k, chainDrift (gaugeTransformPoint v X) ξ' j =
      adjointVertexFn (restrictVertexFunction j v) (chainDrift X ξ j) := by
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hv
  intro j
  induction j with
  | zero =>
    intro _
    funext x
    exact (conj_zero _).symm
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    show adjointCubeAverage (levelField (gaugeTransformPoint v X) j)
        (chainDrift (gaugeTransformPoint v X) ξ' j) +
      contourLogDrift (levelField (gaugeTransformPoint v X) j)
        (tangentTransport (gaugeTransformPoint v X) ξ' j) = _
    rw [levelField_gauge T hd X j hlt.le, ih hlt.le, tangentTransport_gauge T hd X h j hlt.le,
      adjointCubeAverage_gauge T hlt (hs j hlt) (restrictVertexFunction_mem hv j),
      contourLogDrift_gauge T hlt (hs j hlt) (restrictVertexFunction_mem hv j) (hf j hlt.le),
      restrictVertexFunction_succ T.side_pos, ← adjointVertexFn_add]
    rfl
private theorem composedCubeAverage_gauge (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0)
    (X : ChainPoint L n k) (hs : ∀ j < k, levelField X j ∈ smallComplexFields L n k j)
    (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, composedCubeAverage (gaugeTransformPoint v X) j (adjointVertexFn v l) =
      adjointVertexFn (restrictVertexFunction j v) (composedCubeAverage X j l) := by
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hv
  intro j
  induction j with
  | zero =>
    intro _
    show adjointVertexFn v l = adjointVertexFn (restrictVertexFunction 0 v) l
    rw [restrictVertexFunction_zero T.side_pos]
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    show adjointCubeAverage (levelField (gaugeTransformPoint v X) j)
      (composedCubeAverage (gaugeTransformPoint v X) j (adjointVertexFn v l)) = _
    rw [levelField_gauge T hd X j hlt.le, ih hlt.le,
      adjointCubeAverage_gauge T hlt (hs j hlt) (restrictVertexFunction_mem hv j),
      restrictVertexFunction_succ T.side_pos]
    rfl
private theorem rotateValues_snd (x : LevelValues L n k) (i : Fin k) :
    (rotateValues v x).2 i = adjointForm (restrictVertexFunction ((i : ℕ) + 1) v) (x.2 i) := rfl
private theorem gaugeOrbitValues_snd (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2) (i : Fin k) :
    (gaugeOrbitValues X l).2 i = extendOddly fun c =>
      open Classical in
        if hc : c.IsPositivelyOriented then
          ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) l c.source) -
            restrictVertexFunction (i + 1) l c.source
        else 0 := rfl
private theorem gaugeOrbitValues_pos (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2) (i : Fin k)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    (gaugeOrbitValues X l).2 i c =
      ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩) (restrictVertexFunction ((i : ℕ) + 1) l c.source) -
        restrictVertexFunction ((i : ℕ) + 1) l c.source := by
  rw [gaugeOrbitValues_snd, extendOddly_pos hc, dif_pos hc]
private theorem chainBracket_snd (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (x : LevelValues L n k) (i : Fin k) :
    (chainBracket X l x).2 i = extendOddly fun c =>
      open Classical in
        if hc : c.IsPositivelyOriented then
          (Complex.I / 2) • ⁅restrictVertexFunction (i + 1) l c.source +
            ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) l c.source),
            x.2 i c⁆
        else 0 := rfl
private theorem chainBracket_pos (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (x : LevelValues L n k) (i : Fin k) {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    (chainBracket X l x).2 i c = (Complex.I / 2) • ⁅restrictVertexFunction ((i : ℕ) + 1) l c.source +
      ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩) (restrictVertexFunction ((i : ℕ) + 1) l c.source),
      x.2 i c⁆ := by
  rw [chainBracket_snd, extendOddly_pos hc, dif_pos hc]
private theorem gaugeOrbitValues_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    (l : Vertex L n k 0 → ComplexMatrix2) :
    gaugeOrbitValues (gaugeTransformPoint v X) (adjointVertexFn v l) =
      rotateValues v (gaugeOrbitValues X l) := by
  refine Prod.ext (covDiff_gauge T (Nat.zero_le k) hd X.fine l) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ k := i.2
  rw [rotateValues_snd]
  refine odd_ext T hi ?_ (extendOddly_opposite T hi _) fun c hc => ?_
  · rw [gaugeOrbitValues_snd]
    exact extendOddly_opposite T hi _
  rw [gaugeOrbitValues_pos _ _ i hc, adjointForm_pos _ _ hc, gaugeOrbitValues_pos _ _ i hc]
  show ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source * X.noise i ⟨c, hc⟩ *
        (restrictVertexFunction ((i : ℕ) + 1) v c.source)⁻¹)
      (ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source)
        (restrictVertexFunction ((i : ℕ) + 1) l c.source)) -
    ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source)
      (restrictVertexFunction ((i : ℕ) + 1) l c.source) = _
  rw [conj_conj_gauge _ _ (det_restrict hd _ _), conj_sub]
private theorem chainBracket_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    (l : Vertex L n k 0 → ComplexMatrix2) (x : LevelValues L n k) :
    chainBracket (gaugeTransformPoint v X) (adjointVertexFn v l) (rotateValues v x) =
      rotateValues v (chainBracket X l x) := by
  refine Prod.ext (bracketTerm_gauge T hd X.fine l x.1) (funext fun i => ?_)
  have hi : (i : ℕ) + 1 ≤ k := i.2
  rw [rotateValues_snd]
  refine odd_ext T hi ?_ (extendOddly_opposite T hi _) fun c hc => ?_
  · rw [chainBracket_snd]
    exact extendOddly_opposite T hi _
  have e : (rotateValues v x).2 i c =
      ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source) (x.2 i c) :=
    adjointForm_pos _ _ hc
  rw [chainBracket_pos _ _ _ i hc, adjointForm_pos _ _ hc, chainBracket_pos _ _ _ i hc, e]
  show (Complex.I / 2) • ⁅ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source)
        (restrictVertexFunction ((i : ℕ) + 1) l c.source) +
      ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source * X.noise i ⟨c, hc⟩ *
        (restrictVertexFunction ((i : ℕ) + 1) v c.source)⁻¹)
      (ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source)
        (restrictVertexFunction ((i : ℕ) + 1) l c.source)),
      ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.source) (x.2 i c)⁆ = _
  rw [conj_conj_gauge _ _ (det_restrict hd _ _), conj_smul, conj_lie (det_restrict hd _ _), conj_add]
private theorem topLog_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1) (X : ChainPoint L n k)
    {ξ ξ' : LevelForms L n k} (h : IsConjugatedCurrent v ξ ξ') (c : PositiveEdge L n k k) :
    topLog (gaugeTransformPoint v X) ξ' c =
      ComplexMatrix2.conjugateBy (restrictVertexFunction k v c.1.source) (topLog X ξ c) := by
  unfold topLog
  rw [expMove_gauge T hd X h, levelField_gauge T hd _ k le_rfl, levelField_gauge T hd X k le_rfl]
  show Complex.I⁻¹ • ComplexMatrix2.logSeries
      ((restrictVertexFunction k v c.1.source * _ * (restrictVertexFunction k v c.1.target)⁻¹) *
        (restrictVertexFunction k v c.1.source * _ * (restrictVertexFunction k v c.1.target)⁻¹)⁻¹) = _
  rw [gauge_mul_inv_gauge (det_restrict hd _ _), logSeries_conj (det_restrict hd _ _), conj_smul]
private theorem topSecondVariation_gauge (T : TowerData L n k) (hd : ∀ x, (v x).det = 1)
    (X : ChainPoint L n k)
    (A : LevelForms L n k →ₗ[ℝ] LevelForms L n k)
    (hA : ∀ ξ, IsConjugatedCurrent v ξ (A ξ)) (ξ ξ' : LevelForms L n k)
    (c : PositiveEdge L n k k) :
    topSecondVariation (gaugeTransformPoint v X) (A ξ) (A ξ') c =
      ComplexMatrix2.conjugateBy (restrictVertexFunction k v c.1.source) (topSecondVariation X ξ ξ' c) := by
  have hg := det_restrict hd k c.1.source
  have key : ∀ s t : ℝ, topLog (gaugeTransformPoint v X) (s • A ξ + t • A ξ') c =
      conjEquivReal hg (topLog X (s • ξ + t • ξ') c) := by
    intro s t
    have e : s • A ξ + t • A ξ' = A (s • ξ + t • ξ') := by
      rw [map_add, map_smul, map_smul]
    rw [e, topLog_gauge T hd X (hA _) c, conjEquivReal_apply]
  unfold topSecondVariation
  simp only [key, deriv_clEquiv_real]
  exact conjEquivReal_apply hg _
end RotatedValues
section FineLevel
variable {L n k : ℕ}
private structure NearIdentityFacts (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  mem_fields : U ∈ fieldSpace L n k 0
  mem_small : U ∈ smallIterateFields L n k
  covDiff_apply : ∀ l : vertexFunctionSpace L n k 0,
    (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) =
      covDiff U (l : Vertex L n k 0 → ComplexMatrix2)
  iterAverage_apply : ∀ l : vertexFunctionSpace L n k 0,
    (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2) =
      iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2)
  covDiff_transpose : ∀ (g : edgeFormSpace L n k 0) (f : vertexFunctionSpace L n k 0),
    traceFinsumPairing (covDiffRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      edgeFormPairing (g : Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k U f : Edge L n k 0 → ComplexMatrix2)
  iterAverage_transpose : ∀ (g : vertexFunctionSpace L n k k) (f : vertexFunctionSpace L n k 0),
    traceFinsumPairing (iterAverageRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
        (iterAverageLinear L n k U f : Vertex L n k k → ComplexMatrix2)
private structure GaugeIsometries (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2)
    (u : Vertex L n k 0 → ComplexMatrix2) where
  onForms : edgeFormSpace L n k 0 ≃ₗ[ℝ] edgeFormSpace L n k 0
  onVertex : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] vertexFunctionSpace L n k 0
  onTopForms : edgeFormSpace L n k k ≃ₗ[ℝ] edgeFormSpace L n k k
  onTopVertex : vertexFunctionSpace L n k k ≃ₗ[ℝ] vertexFunctionSpace L n k k
  onForms_apply : ∀ B : edgeFormSpace L n k 0,
    (onForms B : Edge L n k 0 → ComplexMatrix2) = adjointForm u B
  onVertex_apply : ∀ l : vertexFunctionSpace L n k 0,
    (onVertex l : Vertex L n k 0 → ComplexMatrix2) = adjointVertexFn u l
  onTopForms_apply : ∀ B : edgeFormSpace L n k k,
    (onTopForms B : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) B
  onTopVertex_apply : ∀ l : vertexFunctionSpace L n k k,
    (onTopVertex l : Vertex L n k k → ComplexMatrix2) = adjointVertexFn (restrictVertexFunction k u) l
  mem_gauge : u ∈ gaugeGroupAt L n k 0
  covDiff_comm : ∀ l ∈ vertexFunctionSpace L n k 0,
    covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
      adjointForm u (covDiff U l)
  iterAverage_comm : ∀ l ∈ vertexFunctionSpace L n k 0,
    iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) k (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction k u) (iterAdjointCubeAverage L n k U k l)
namespace GaugeIsometries
variable {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
  (P : GaugeIsometries L n k U u)
include P
private theorem det_one (x : Vertex L n k 0) : (u x).det = 1 := det_of_gauge P.mem_gauge x
private theorem det_one_top (x : Vertex L n k k) : (restrictVertexFunction k u x).det = 1 :=
  det_of_gauge (restrictVertexFunction_mem P.mem_gauge k) x
private theorem inner_onForms {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    (hc : IsEdgePairingCore c) (x y : edgeFormSpace L n k 0) :
    c.inner (P.onForms x) (P.onForms y) = c.inner x y := by
  rw [hc, hc, P.onForms_apply, P.onForms_apply, edgeFormPairing_adjointForm P.det_one]
private theorem inner_onVertex {c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    (hc : IsVertexPairingCore c) (x y : vertexFunctionSpace L n k 0) :
    c.inner (P.onVertex x) (P.onVertex y) = c.inner x y := by
  rw [hc, hc, P.onVertex_apply, P.onVertex_apply, pairing_adjointVertexFn P.det_one]
private theorem inner_onTopVertex {c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)}
    (hc : IsVertexPairingCore c) (x y : vertexFunctionSpace L n k k) :
    c.inner (P.onTopVertex x) (P.onTopVertex y) = c.inner x y := by
  rw [hc, hc, P.onTopVertex_apply, P.onTopVertex_apply, pairing_adjointVertexFn P.det_one_top]
variable (hU : NearIdentityFacts U) (hU' : NearIdentityFacts (PeriodicLattice.gaugeTransform u U))
include hU hU'
private theorem covDiffLinear_comm (l : vertexFunctionSpace L n k 0) :
    covDiffLinear L n k (PeriodicLattice.gaugeTransform u U) (P.onVertex l) =
      P.onForms (covDiffLinear L n k U l) :=
  Subtype.ext (by
    rw [hU'.covDiff_apply, P.onVertex_apply, P.covDiff_comm _ l.2, P.onForms_apply, hU.covDiff_apply])
private theorem iterAverageLinear_comm (l : vertexFunctionSpace L n k 0) :
    iterAverageLinear L n k (PeriodicLattice.gaugeTransform u U) (P.onVertex l) =
      P.onTopVertex (iterAverageLinear L n k U l) :=
  Subtype.ext (by
    rw [hU'.iterAverage_apply, P.onVertex_apply, P.iterAverage_comm _ l.2, P.onTopVertex_apply,
      hU.iterAverage_apply])
private theorem covDiffTranspose_comm {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (g : edgeFormSpace L n k 0) :
    covDiffRealTranspose L n k (PeriodicLattice.gaugeTransform u U) (P.onForms g) =
      P.onVertex (covDiffRealTranspose L n k U g) :=
  transpose_comm_of_isometry cS cF P.onVertex P.onForms (P.inner_onForms hF) (P.inner_onVertex hS)
    (P.covDiffLinear_comm hU hU')
    (fun y x => by rw [hS, hF]; exact congrArg Complex.re (hU.covDiff_transpose y x))
    (fun y x => by rw [hS, hF]; exact congrArg Complex.re (hU'.covDiff_transpose y x)) g
private theorem iterAverageTranspose_comm {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hS : IsVertexPairingCore cS)
    (hK : IsVertexPairingCore cK) (g : vertexFunctionSpace L n k k) :
    iterAverageRealTranspose L n k (PeriodicLattice.gaugeTransform u U) (P.onTopVertex g) =
      P.onVertex (iterAverageRealTranspose L n k U g) :=
  transpose_comm_of_isometry cS cK P.onVertex P.onTopVertex (P.inner_onTopVertex hK) (P.inner_onVertex hS)
    (P.iterAverageLinear_comm hU hU')
    (fun y x => by rw [hS, hK]; exact congrArg Complex.re (hU.iterAverage_transpose y x))
    (fun y x => by rw [hS, hK]; exact congrArg Complex.re (hU'.iterAverage_transpose y x)) g
private theorem gaugeSliceResidual_comm {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (hK : IsVertexPairingCore cK) (B : edgeFormSpace L n k 0) :
    gaugeSliceResidual (PeriodicLattice.gaugeTransform u U) (P.onForms B) =
      P.onVertex (gaugeSliceResidual U B) := by
  unfold gaugeSliceResidual
  rw [P.covDiffTranspose_comm hU hU' hF hS, P.iterAverageLinear_comm hU hU',
    P.iterAverageTranspose_comm hU hU' hS hK, map_sub, map_smul]
end GaugeIsometries
private theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
private theorem gaugeTransform_mem_fields {j : ℕ} {u : Vertex L n k j → ComplexMatrix2}
    {U : Edge L n k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform u U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8548 <;> assumption
private theorem eventually_nearIdentityFacts (hQ : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion)
    (hY : RealLinearMaps.RealLinearMapsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) (NearIdentityFacts (L := L) (n := n) (k := k)) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hDT, hnear⟩ := hQ L n (i + 1) hL hn hk
  obtain ⟨hAt, hTower⟩ := hY L n (i + 1) hL hn hk
  have hAi := hAt i (by omega)
  show ∀ᶠ V in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)), NearIdentityFacts V
  filter_upwards [self_mem_nhdsWithin, hnear, hE L n (i + 1) hL hn hk,
    hAi.iterAdjointCubeAverage_isLinear] with U hc hR hX hav
  obtain ⟨-, hTr, -⟩ := hR
  obtain ⟨hF, -, -⟩ := hX
  obtain ⟨T, -, hK⟩ := hDT 0 (Nat.zero_le _) U hc
  obtain ⟨T', -, hK'⟩ := hTr.average_transpose
  exact
    { mem_fields := hc
      mem_small := hF.1
      covDiff_apply := fun l =>
        linearMapWithValues_apply (hTower.covDiff_isLinear 0 (Nat.zero_le _) U hc) l
      iterAverage_apply := fun l => linearMapWithValues_apply hav l
      covDiff_transpose := fun g f => hK.2.2 g f
      iterAverage_transpose := fun g f => hK'.2.2 g f }
private theorem exists_gaugeIsometries (T : TowerData L n k)
    (hGC : AveragesGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {U : Edge L n k 0 → ComplexMatrix2}
    {u : Vertex L n k 0 → ComplexMatrix2} (hu : u ∈ gaugeGroupAt L n k 0) (hU : NearIdentityFacts U)
    (hU' : NearIdentityFacts (PeriodicLattice.gaugeTransform u U)) :
    Nonempty (GaugeIsometries L n k U u) := by
  have hc0 : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u :=
    fun x => det_of_gauge hu x
  have hck : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup (restrictVertexFunction k u) :=
    fun x => det_of_gauge (restrictVertexFunction_mem hu k) x
  have h0 := T.gauge_forms 0 (Nat.zero_le k) u hc0
  have hkk := T.gauge_forms k le_rfl (restrictVertexFunction k u) hck
  obtain ⟨⟨A, hA, -⟩, ⟨S, hS, -⟩⟩ := h0.2.2.2 hu
  obtain ⟨⟨Ak, hAk, -⟩, ⟨Sk, hSk, -⟩⟩ := hkk.2.2.2 (restrictVertexFunction_mem hu k)
  have cov := hGC L hL n k k hn le_rfl U hU.mem_small u hu hU'.mem_small
  have hsl : ∀ l ∈ vertexFunctionSpace L n k 0, ∀ x, l x ∈ ComplexMatrix2.traceless :=
    fun l hl x => (hl x (mem_univ x)).2
  exact ⟨{ onForms := A, onVertex := S, onTopForms := Ak, onTopVertex := Sk
           onForms_apply := hA, onVertex_apply := hS, onTopForms_apply := hAk, onTopVertex_apply := hSk
           mem_gauge := hu
           covDiff_comm := fun l hl => (cov.1 l (hsl l hl)).1
           iterAverage_comm := fun l hl => (cov.1 l (hsl l hl)).2 }⟩
end FineLevel
section PointFacts
variable {L n k j : ℕ}
private theorem mem_complexEdgeForms_of_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j) :
    B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
private structure LevelFacts (V : Edge L n k j → ComplexMatrix2) : Prop where
  mem_small : V ∈ smallComplexFields L n k j
  mean_mem : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup
  exists_deriv : ∃ P : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k (j + 1), ∀ B : edgeFormSpace L n k j,
    (P B : Edge L n k (j + 1) → ComplexMatrix2) =
      holLeftDifferential normalizedMean V (B : Edge L n k j → ComplexMatrix2)
  deriv_eq : ∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
    leftDifferential normalizedMean V B c = holLeftDifferential normalizedMean V B c
  exists_drift : ∃ T : edgeFormSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1),
    ∀ B : edgeFormSpace L n k j,
    (T B : Vertex L n k (j + 1) → ComplexMatrix2) = contourLogDrift V (B : Edge L n k j → ComplexMatrix2)
  exists_average : ∃ T : vertexFunctionSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1),
    ∀ l : vertexFunctionSpace L n k j,
    (T l : Vertex L n k (j + 1) → ComplexMatrix2) = adjointCubeAverage V (l : Vertex L n k j → ComplexMatrix2)
private theorem eventually_levelFacts (hS : MeanDerivOnForms.Claim)
    (hY : RealLinearMaps.RealLinearMapsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) :
    EventuallyNearIdentity (fieldSpace L n k j) (LevelFacts (L := L) (n := n) (k := k)) := by
  have hAt := (hY L n k hL hn (by omega)).1 j hj
  show ∀ᶠ V in 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)), LevelFacts V
  filter_upwards [hS L hL n k j hn hj, hAt.contourLogDrift_isLinear, hAt.adjointCubeAverage_isLinear]
    with V h₁ h₂ h₃
  obtain ⟨hsm, hre, hcf, hlin, hfm, hsame, -⟩ := h₁
  have hc : ∀ B : edgeFormSpace L n k j, (B : Edge L n k j → ComplexMatrix2) ∈ complexEdgeForms L n k j :=
    fun B => mem_complexEdgeForms_of_mem B.2
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
    { mem_small := hsm
      mean_mem := fun c hc => (hre c hc).2.2
      exists_deriv := ⟨⟨⟨fun B => ⟨_, hfm B B.2⟩, fun B B' => Subtype.ext (hadd B B')⟩,
        fun r B => Subtype.ext (hsmul r B)⟩, fun _ => rfl⟩
      deriv_eq := hsame
      exists_drift := h₂
      exists_average := h₃ }
private theorem exists_linear_extendOddly {E : Type*} [AddCommGroup E] [Module ℝ E] (T : TowerData L n k)
    (hj : j ≤ k)
    (f : E → Edge L n k j → ComplexMatrix2)
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
private theorem exists_conj_linear (T : TowerData L n k) (hj : j ≤ k) (m : PositiveEdge L n k j → ComplexMatrix2)
    (hm : ∀ c, m c ∈ PeriodicLattice.compactGaugeGroup) :
    ∃ T' : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j, ∀ (B : edgeFormSpace L n k j)
      {c : Edge L n k j} (hc : c.IsPositivelyOriented), (T' B : Edge L n k j → ComplexMatrix2) c =
        ComplexMatrix2.conjugateBy (m ⟨c, hc⟩) ((B : Edge L n k j → ComplexMatrix2) c) := by
  classical
  obtain ⟨T', hT⟩ := exists_linear_extendOddly T hj
    (fun (B : edgeFormSpace L n k j) (c : Edge L n k j) =>
      if hc : c.IsPositivelyOriented then
        ComplexMatrix2.conjugateBy (m ⟨c, hc⟩) ((B : Edge L n k j → ComplexMatrix2) c) else 0)
    (fun B b hb => by
      simp only [dif_pos hb]
      exact ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hm _) _ (B.2.1 b hb))
    (fun B B' b hb => by
      simp only [dif_pos hb]
      exact conj_add _ _ _)
    (fun r B b hb => by
      simp only [dif_pos hb]
      exact conj_real_smul _ _ _)
  refine ⟨T', fun B c hc => ?_⟩
  rw [hT, extendOddly_pos hc, dif_pos hc]
private structure PointFacts (X : ChainPoint L n k) : Prop where
  noise_mem : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup
  field_mem : ∀ j ≤ k, levelField X j ∈ fieldSpace L n k j
  level_facts : ∀ j < k, LevelFacts (levelField X j)
variable {X : ChainPoint L n k}
private theorem tangentTransport_linear (T : TowerData L n k) (hP : PointFacts X) :
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
    obtain ⟨P, hPv⟩ := (hP.level_facts j h).exists_deriv
    obtain ⟨W, hW⟩ := exists_conj_linear T hj (fun c => X.noise ⟨j, h⟩ c) (hP.noise_mem ⟨j, h⟩)
    let pr : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k (j + 1) :=
      (LinearMap.proj (φ := fun i : Fin k => edgeFormSpace L n k (i + 1)) ⟨j, h⟩) ∘ₗ LinearMap.snd ℝ _ _
    refine ⟨W ∘ₗ P ∘ₗ M + pr, fun ξ => ?_⟩
    refine odd_ext T hj (W (P (M ξ)) + pr ξ).2.2 (tangentTransport_opposite T _ _ h) fun c hc => ?_
    rw [tangentTransport_pos _ _ h hc, (hP.level_facts j h).deriv_eq _ _ hc, ← hM, ← hPv]
    exact congrArg₂ (· + ·) (hW _ hc) rfl
private theorem chainDrift_linear (T : TowerData L n k) (hP : PointFacts X) :
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
    obtain ⟨A, hA⟩ := (hP.level_facts j h).exists_average
    obtain ⟨C, hC⟩ := (hP.level_facts j h).exists_drift
    refine ⟨A ∘ₗ D + C ∘ₗ M, fun ξ => ?_⟩
    show ((A (D ξ) : Vertex L n k (j + 1) → ComplexMatrix2) + (C (M ξ) : Vertex L n k (j + 1) → ComplexMatrix2)) = _
    rw [hA, hC, hD, hM]
    rfl
private theorem composedCubeAverage_exists_linear (hP : PointFacts X) :
    ∀ j ≤ k, ∃ S : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k j,
      ∀ l : vertexFunctionSpace L n k 0,
      (S l : Vertex L n k j → ComplexMatrix2) = composedCubeAverage X j (l : Vertex L n k 0 → ComplexMatrix2) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨LinearMap.id, fun _ => rfl⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨S, hS⟩ := ih h.le
    obtain ⟨A, hA⟩ := (hP.level_facts j h).exists_average
    refine ⟨A ∘ₗ S, fun l => ?_⟩
    show (A (S l) : Vertex L n k (j + 1) → ComplexMatrix2) = _
    rw [hA, hS]
    rfl
private theorem extendByZero_linear :
    ∃ E : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0, ∀ g : vertexFunctionSpace L n k k,
      (E g : Vertex L n k 0 → ComplexMatrix2) = _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) := by
  have hm : ∀ g : vertexFunctionSpace L n k k, _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) ∈
      vertexFunctionSpace L n k 0 := fun g x _ => by
    unfold _root_.YangMills.Construction.Tower.extendByZero
    by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x
    · simp only [dif_pos h]
      exact g.2 _ (mem_univ _)
    · simp only [dif_neg h]
      exact ComplexMatrix2.hermitianTraceless.zero_mem
  have ha : ∀ g g' : vertexFunctionSpace L n k k, _root_.YangMills.Construction.Tower.extendByZero ((g + g' : vertexFunctionSpace L n k k) :
      Vertex L n k k → ComplexMatrix2) = _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) +
        _root_.YangMills.Construction.Tower.extendByZero (g' : Vertex L n k k → ComplexMatrix2) := fun g g' => by
    funext x
    simp only [_root_.YangMills.Construction.Tower.extendByZero, Pi.add_apply]
    by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h, add_zero]
  have hs : ∀ (r : ℝ) (g : vertexFunctionSpace L n k k), _root_.YangMills.Construction.Tower.extendByZero ((r • g : vertexFunctionSpace L n k k) :
      Vertex L n k k → ComplexMatrix2) = r • _root_.YangMills.Construction.Tower.extendByZero (g : Vertex L n k k → ComplexMatrix2) := fun r g => by
    funext x
    simp only [_root_.YangMills.Construction.Tower.extendByZero, Pi.smul_apply]
    by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h, smul_zero]
  exact ⟨⟨⟨fun g => ⟨_, hm g⟩, fun g g' => Subtype.ext (ha g g')⟩,
    fun r g => Subtype.ext (hs r g)⟩, fun _ => rfl⟩
abbrev _root_.YangMills.SharedProofs.p44528 := @extendByZero_linear
private theorem gaugeOrbit_linear (T : TowerData L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : PointFacts X) :
    ∃ O : vertexFunctionSpace L n k 0 →ₗ[ℝ] LevelForms L n k, ∀ l : vertexFunctionSpace L n k 0,
      formValues (O l) = gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2) := by
  obtain ⟨D₀, hD₀⟩ := hY.covDiff_isLinear 0 (Nat.zero_le k) X.fine (hP.field_mem 0 (Nat.zero_le k))
  have hN : ∀ i : Fin k, ∃ N : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k (i + 1),
      ∀ l : vertexFunctionSpace L n k 0, (N l : Edge L n k (i + 1) → ComplexMatrix2) =
        (gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2)).2 i := by
    classical
    intro i
    have hi : (i : ℕ) + 1 ≤ k := i.2
    obtain ⟨N, hN⟩ := exists_linear_extendOddly T hi
      (fun (l : vertexFunctionSpace L n k 0) (c : Edge L n k (i + 1)) =>
        if hc : c.IsPositivelyOriented then
          ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩)
              (restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.source) -
            restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.source
        else 0)
      (fun l b hb => by
        simp only [dif_pos hb]
        exact ComplexMatrix2.hermitianTraceless.sub_mem
          (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hP.noise_mem _ _) _ (l.2 _ (mem_univ _)))
          (l.2 _ (mem_univ _)))
      (fun l l' b hb => by
        simp only [dif_pos hb]
        show ComplexMatrix2.conjugateBy _ (restrictVertexFunction _ _ _ + restrictVertexFunction _ _ _) -
          (restrictVertexFunction _ _ _ + restrictVertexFunction _ _ _) = _
        rw [conj_add]
        abel)
      (fun r l b hb => by
        simp only [dif_pos hb]
        show ComplexMatrix2.conjugateBy _ (r • restrictVertexFunction _ _ _) -
          r • restrictVertexFunction _ _ _ = _
        rw [conj_real_smul, smul_sub])
    refine ⟨N, fun l => ?_⟩
    rw [hN, gaugeOrbitValues_snd]
  choose N hN using hN
  exact ⟨D₀.prod (LinearMap.pi N), fun l =>
    Prod.ext (hD₀ l) (funext fun i => hN i l)⟩
private theorem formValues_add (ξ η : LevelForms L n k) : formValues (ξ + η) = formValues ξ + formValues η := rfl
private theorem formValues_injective :
    Function.Injective (formValues (L := L) (m := n) (k := k)) := fun ξ η h => by
  refine Prod.ext (Subtype.ext (congrArg Prod.fst h)) (funext fun i => Subtype.ext ?_)
  exact congrFun (congrArg Prod.snd h) i
abbrev _root_.YangMills.SharedProofs.p13252 := @formValues_injective
private theorem shiftedGaugeMap_spec (T : TowerData L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : PointFacts X) : IsShiftedGaugeMap X (shiftedGaugeMap X) := by
  obtain ⟨M, hM⟩ := tangentTransport_linear T hP k le_rfl
  obtain ⟨D, hD⟩ := chainDrift_linear T hP k le_rfl
  obtain ⟨C, hC⟩ := hY.covDiff_isLinear k le_rfl _ (hP.field_mem k le_rfl)
  refine Classical.epsilon_spec (p := IsShiftedGaugeMap X) ⟨M + C ∘ₗ D, fun ξ => ?_⟩
  show (M ξ : Edge L n k k → ComplexMatrix2) + (C (D ξ) : Edge L n k k → ComplexMatrix2) = _
  rw [hM, hC, hD]
  rfl
private theorem gaugeTransform_spec (T : TowerData L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hP : PointFacts X) : IsGaugeTransform X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X) := by
  obtain ⟨D, hD⟩ := chainDrift_linear T hP k le_rfl
  obtain ⟨E, hE⟩ := extendByZero_linear (L := L) (n := n) (k := k)
  obtain ⟨O, hO⟩ := gaugeOrbit_linear T hY hP
  refine Classical.epsilon_spec (p := IsGaugeTransform X) ⟨LinearMap.id + O ∘ₗ E ∘ₗ D, fun ξ => ?_⟩
  show formValues (ξ + O (E (D ξ))) = _
  rw [formValues_add, hO, hE, hD]
  rfl
private theorem composedCubeAverageLinear_apply (hP : PointFacts X) (l : vertexFunctionSpace L n k 0) :
    (composedCubeAverageLinear X l : Vertex L n k k → ComplexMatrix2) =
      composedCubeAverage X k (l : Vertex L n k 0 → ComplexMatrix2) :=
  linearMapWithValues_apply (composedCubeAverage_exists_linear hP k le_rfl) l
end PointFacts
section RightValue
variable {L n k : ℕ} {v : Vertex L n k 0 → ComplexMatrix2} {X : ChainPoint L n k}
private theorem gaugedFormValue_gauge (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0) (a : ℝ)
    (hX : X.fine ∈ fieldSpace L n k 0)
    (hs : ∀ j < k, levelField X j ∈ smallComplexFields L n k j)
    (A : LevelForms L n k →ₗ[ℝ] LevelForms L n k) (hA : ∀ ξ, IsConjugatedCurrent v ξ (A ξ))
    (hf : ∀ ξ, ∀ j ≤ k, tangentTransport X ξ j ∈ complexEdgeForms L n k j)
    (hτ : ∀ ξ, _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform (gaugeTransformPoint v X) (A ξ) = A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ))
    {J J' : LevelForms L n k} {μ μ' : edgeFormSpace L n k k} (hJ : IsConjugatedCurrent v J J')
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k v) μ)
    (ξ : LevelForms L n k) :
    gaugedFormValue a (gaugeTransformPoint v X) J' μ' (A ξ) = gaugedFormValue a X J μ ξ := by
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hv
  have hdk : ∀ x, (restrictVertexFunction k v x).det = 1 := det_restrict hd k
  have hσ : gaugeCorrection (gaugeTransformPoint v X) (A ξ) = adjointVertexFn v (gaugeCorrection X ξ) := by
    unfold gaugeCorrection
    rw [chainDrift_gauge T hv X hs (hA ξ) (hf ξ) k le_rfl, extendByZero_gauge T.side_pos]
  have hval : formValues (A ξ) = rotateValues v (formValues ξ) := hA ξ
  have hJ' : formValues J' = rotateValues v (formValues J) := hJ
  have h₃ : traceFinsumPairing (restrictToPositiveEdges (μ' : Edge L n k k → ComplexMatrix2))
      (topSecondVariation (gaugeTransformPoint v X) (A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) (A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ))) =
      traceFinsumPairing (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2))
        (topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) := by
    have e : topSecondVariation (gaugeTransformPoint v X) (A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) (A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) =
        fun c : PositiveEdge L n k k => ComplexMatrix2.conjugateBy (restrictVertexFunction k v c.1.source)
          (topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) c) :=
      funext fun c => topSecondVariation_gauge T hd X A hA _ _ c
    rw [hμ, restrictPositive_adjointForm, e]
    exact pairing_conj (fun c => hdk _) _ _
  unfold gaugedFormValue
  rw [leftSecondDeriv_gauge T hv a hX A hA, hσ, hval, hJ', chainBracket_gauge T hd,
    levelPairing_rotateValues hd, gaugeOrbitValues_gauge T hd, chainBracket_gauge T hd,
    levelPairing_rotateValues hd, hτ ξ, h₃]
end RightValue
section PairOfPoints
variable {L n k : ℕ} {v : Vertex L n k 0 → ComplexMatrix2} {X : ChainPoint L n k}
private theorem exists_adjointForm_equiv (T : TowerData L n k) (hv : v ∈ gaugeGroupAt L n k 0) (i : Fin k) :
    ∃ Ai : edgeFormSpace L n k (i + 1) ≃ₗ[ℝ] edgeFormSpace L n k (i + 1), ∀ B : edgeFormSpace L n k (i + 1),
      (Ai B : Edge L n k (i + 1) → ComplexMatrix2) = adjointForm (restrictVertexFunction ((i : ℕ) + 1) v) B := by
  have hck : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
      (restrictVertexFunction ((i : ℕ) + 1) v) := fun x => det_of_gauge (restrictVertexFunction_mem hv _) x
  obtain ⟨⟨Ai, hAi, -⟩, -⟩ := (T.gauge_forms ((i : ℕ) + 1) i.2 _ hck).2.2.2 (restrictVertexFunction_mem hv _)
  exact ⟨Ai, hAi⟩
private theorem covariant_at_pair (T : TowerData L n k) (hY : RealLinearMaps.TowerLinearity L n k)
    (hGC : AveragesGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hv : v ∈ gaugeGroupAt L n k 0)
    {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (hK : IsVertexPairingCore cK)
    (hP : PointFacts X) (hP' : PointFacts (gaugeTransformPoint v X)) (hU : NearIdentityFacts X.fine)
    (hU' : NearIdentityFacts (PeriodicLattice.gaugeTransform v X.fine)) (a : ℝ)
    {J J' : LevelForms L n k} {μ μ' : edgeFormSpace L n k k}
    (hq : ∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ, q ξ = gaugedRightValue a X J μ ξ)
    (hJ : IsConjugatedCurrent v J J')
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) =
      adjointForm (restrictVertexFunction k v) (μ : Edge L n k k → ComplexMatrix2)) :
    logRadiusSum (gaugeTransformPoint v X) = logRadiusSum X ∧
    (∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ, q ξ =
      gaugedRightValue a (gaugeTransformPoint v X) J' μ' ξ) ∧
    ∃ (A : LevelForms L n k ≃ₗ[ℝ] LevelForms L n k)
      (F : edgeFormSpace L n k k ≃ₗ[ℝ] edgeFormSpace L n k k)
      (G₀ : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] vertexFunctionSpace L n k 0)
      (Gk : vertexFunctionSpace L n k k ≃ₗ[ℝ] vertexFunctionSpace L n k k),
      (∀ ξ, IsConjugatedCurrent v ξ (A ξ)) ∧
      (∀ C : edgeFormSpace L n k k, (F C : Edge L n k k → ComplexMatrix2) =
        adjointForm (restrictVertexFunction k v) (C : Edge L n k k → ComplexMatrix2)) ∧
      (∀ l : vertexFunctionSpace L n k 0, (G₀ l : Vertex L n k 0 → ComplexMatrix2) =
        adjointVertexFn v (l : Vertex L n k 0 → ComplexMatrix2)) ∧
      (∀ g : vertexFunctionSpace L n k k, (Gk g : Vertex L n k k → ComplexMatrix2) =
        adjointVertexFn (restrictVertexFunction k v) (g : Vertex L n k k → ComplexMatrix2)) ∧
      (∀ ξ ξ', levelPairing (formValues (A ξ)) (formValues (A ξ')) =
        levelPairing (formValues ξ) (formValues ξ')) ∧
      (∀ C C' : edgeFormSpace L n k k,
        (edgeFormPairing (F C : Edge L n k k → ComplexMatrix2) (F C' : Edge L n k k → ComplexMatrix2)).re =
          (edgeFormPairing (C : Edge L n k k → ComplexMatrix2) (C' : Edge L n k k → ComplexMatrix2)).re) ∧
      (∀ ξ, gaugedRightValue a (gaugeTransformPoint v X) J' μ' (A ξ) = gaugedRightValue a X J μ ξ) ∧
      (∀ ξ, shiftedGaugeMap (gaugeTransformPoint v X) (A ξ) = F (shiftedGaugeMap X ξ)) ∧
      ∀ y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k,
        ghostBlockOperator (gaugeTransformPoint v X) (G₀ y.1, Gk y.2) =
          (G₀ (ghostBlockOperator X y).1, Gk (ghostBlockOperator X y).2) := by
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hv
  have hdk : ∀ x, (restrictVertexFunction k v x).det = 1 := det_restrict hd k
  obtain ⟨P⟩ := exists_gaugeIsometries T hGC hL hn hv hU hU'
  choose Ai hAi using exists_adjointForm_equiv (L := L) (n := n) (k := k) T hv
  let A : LevelForms L n k ≃ₗ[ℝ] LevelForms L n k :=
    P.onForms.prodCongr (LinearEquiv.piCongrRight Ai)
  have hAT : ∀ ξ, IsConjugatedCurrent v ξ (A ξ) := fun ξ =>
    Prod.ext (P.onForms_apply ξ.1) (funext fun i => hAi i (ξ.2 i))
  have hval : ∀ ξ, formValues (A ξ) = rotateValues v (formValues ξ) := hAT
  have hs : ∀ j < k, levelField X j ∈ smallComplexFields L n k j :=
    fun j hj => (hP.level_facts j hj).mem_small
  have hf : ∀ ξ, ∀ j ≤ k, tangentTransport X ξ j ∈ complexEdgeForms L n k j := fun ξ j hj => by
    obtain ⟨M, hM⟩ := tangentTransport_linear T hP j hj
    rw [← hM]
    exact mem_complexEdgeForms_of_mem (M ξ).2
  have hX : X.fine ∈ fieldSpace L n k 0 := hU.mem_fields
  have hτ : ∀ ξ, _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform (gaugeTransformPoint v X) (A ξ) = A (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) := fun ξ => by
    refine formValues_injective ?_
    have hσ : gaugeCorrection (gaugeTransformPoint v X) (A ξ) =
        adjointVertexFn v (gaugeCorrection X ξ) := by
      unfold gaugeCorrection
      rw [chainDrift_gauge T hv X hs (hAT ξ) (hf ξ) k le_rfl, extendByZero_gauge T.side_pos]
    rw [gaugeTransform_spec T hY hP', hval, hval, gaugeTransform_spec T hY hP, hσ,
      gaugeOrbitValues_gauge T hd, rotateValues_add]
  have hmember : ∀ ξ, gaugedRightValue a (gaugeTransformPoint v X) J' μ' (A ξ) =
      gaugedRightValue a X J μ ξ := fun ξ => by
    have e := P.gaugeSliceResidual_comm hU hU' hF hS hK ξ.1
    have e' : traceFinsumNorm (gaugeSliceResidual (gaugeTransformPoint v X).fine (A ξ).1 :
        Vertex L n k 0 → ComplexMatrix2) = traceFinsumNorm (gaugeSliceResidual X.fine ξ.1 :
          Vertex L n k 0 → ComplexMatrix2) := by
      show traceFinsumNorm (gaugeSliceResidual (PeriodicLattice.gaugeTransform v X.fine) (P.onForms ξ.1) :
        Vertex L n k 0 → ComplexMatrix2) = _
      rw [e, P.onVertex_apply, norm_adjointVertexFn hd]
    have e₂ : gaugedFormValue a (gaugeTransformPoint v X) J' μ' (A ξ) = gaugedFormValue a X J μ ξ :=
      gaugedFormValue_gauge T hv a hX hs (A : LevelForms L n k →ₗ[ℝ] LevelForms L n k) hAT hf hτ hJ hμ ξ
    unfold gaugedRightValue
    rw [e₂, e']
  refine ⟨logRadiusSum_gauge T hd X, ?_, A, P.onTopForms, P.onVertex, P.onTopVertex, hAT,
    P.onTopForms_apply, P.onVertex_apply, P.onTopVertex_apply, ?_, ?_, hmember, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hq
    refine ⟨q.comp (A.symm : LevelForms L n k →ₗ[ℝ] LevelForms L n k), fun ξ => ?_⟩
    have e := hmember (A.symm ξ)
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e, ← hq]
    rfl
  · intro ξ ξ'
    rw [hval, hval, levelPairing_rotateValues hd]
  · intro C C'
    rw [P.onTopForms_apply, P.onTopForms_apply, edgeFormPairing_adjointForm hdk]
  · intro ξ
    refine Subtype.ext ?_
    rw [shiftedGaugeMap_spec T hY hP', P.onTopForms_apply, shiftedGaugeMap_spec T hY hP]
    unfold shiftedGaugeValues
    rw [tangentTransport_gauge T hd X (hAT ξ) k le_rfl, levelField_gauge T hd X k le_rfl,
      chainDrift_gauge T hv X hs (hAT ξ) (hf ξ) k le_rfl,
      covDiff_gauge T le_rfl hdk, adjointForm_add]
  · intro y
    have hb : ∀ l : vertexFunctionSpace L n k 0,
        composedCubeAverageLinear (gaugeTransformPoint v X) (P.onVertex l) =
        P.onTopVertex (composedCubeAverageLinear X l) := fun l => Subtype.ext (by
      rw [composedCubeAverageLinear_apply hP', P.onVertex_apply,
        composedCubeAverage_gauge T hv X hs _ k le_rfl, P.onTopVertex_apply,
        composedCubeAverageLinear_apply hP])
    have hbase : (gaugeTransformPoint v X).fine = PeriodicLattice.gaugeTransform v X.fine := rfl
    refine Prod.ext ?_ ?_
    · show covDiffRealTranspose L n k (gaugeTransformPoint v X).fine
          (covDiffLinear L n k (gaugeTransformPoint v X).fine (P.onVertex y.1)) +
        iterAverageRealTranspose L n k (gaugeTransformPoint v X).fine (P.onTopVertex y.2) =
        P.onVertex (covDiffRealTranspose L n k X.fine (covDiffLinear L n k X.fine y.1) +
          iterAverageRealTranspose L n k X.fine y.2)
      rw [hbase, P.covDiffLinear_comm hU hU', P.covDiffTranspose_comm hU hU' hF hS,
        P.iterAverageTranspose_comm hU hU' hS hK, map_add]
    · exact hb y.1
end PairOfPoints
section NearUnitPoint
variable {L n k j : ℕ}
private theorem continuousAt_inv_at_one : ContinuousAt (fun A : ComplexMatrix2 => A⁻¹) 1 := by
  have e : (fun A : ComplexMatrix2 => A⁻¹) = Ring.inverse := by
    funext A
    exact Matrix.nonsing_inv_eq_ringInverse A
  rw [e]
  exact NormedRing.inverse_continuousAt (1 : ComplexMatrix2ˣ)
abbrev _root_.YangMills.SharedProofs.p45833 := @continuousAt_inv_at_one
private theorem one_mem_fields : (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => one_mem _, fun _ _ => (Matrix.inv_eq_right_inv (mul_one 1)).symm⟩
private theorem fieldOfValues_mem (T : TowerData L n k) (hj : j ≤ k) {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [fieldOfPositiveValues, dif_pos hb]
      exact hw _
    · have hr := T.opposite_pos hj hb
      simp only [fieldOfPositiveValues, dif_neg hb, dif_pos hr]
      exact inv_mem_compact (hw _)
  · by_cases hb : b.IsPositivelyOriented
    · have hr := T.opposite_not_pos hj hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := by
        rw [bond_opposite_opposite]
        exact hb
      have e : (⟨b.opposite.opposite, hrr⟩ : PositiveEdge L n k j) = ⟨b, hb⟩ :=
        Subtype.ext (bond_opposite_opposite b)
      simp only [fieldOfPositiveValues, dif_neg hr, dif_pos hrr, dif_pos hb, e]
    · have hr := T.opposite_pos hj hb
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
private theorem continuous_matExp : Continuous (ComplexMatrix2.matExp) := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuous_matExp <;> assumption
private theorem tendsto_matExp_linear {N : ℕ} (g : (Fin N → ℝ) →ₗ[ℝ] ComplexMatrix2) :
    Tendsto (fun w => ComplexMatrix2.matExp (Complex.I • g w) * (1 : ComplexMatrix2)) (𝓝 0) (𝓝 1) := by
  have hc : Continuous fun w => g w := g.continuous_of_finiteDimensional
  have h0 : Continuous fun w => ComplexMatrix2.matExp (Complex.I • g w) :=
    continuous_matExp.comp (hc.const_smul Complex.I)
  have h1 : Continuous fun w => ComplexMatrix2.matExp (Complex.I • g w) * (1 : ComplexMatrix2) :=
    h0.mul continuous_const
  have h2 := h1.tendsto 0
  simpa [ComplexMatrix2.matExp] using h2
private theorem tendsto_levelFields (T : TowerData L n k) (hS : MeanDerivOnForms.Claim)
    (hAn : NormalizedMeanAnalytic) (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {N : ℕ}
    (f : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) :
    ∀ j ≤ k, Tendsto (fun w => levelField (expMove (f w) (unitPoint L n k)) j) (𝓝 0)
      (𝓝[fieldSpace L n k j] fun _ => (1 : ComplexMatrix2)) := by
  have hone : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  intro j
  induction j with
  | zero =>
    intro _
    have hp : ∀ b : Edge L n k 0, b.IsPositivelyOriented → Tendsto
        (fun w => ComplexMatrix2.matExp (Complex.I • ((f w).1 : Edge L n k 0 → ComplexMatrix2) b) *
          (1 : ComplexMatrix2))
        (𝓝 0) (𝓝 1) := fun b _ =>
      tendsto_matExp_linear ((LinearMap.proj b : (Edge L n k 0 → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2) ∘ₗ
        (edgeFormSpace L n k 0).subtype ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ f)
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_,
      Eventually.of_forall fun w => expTwist_mem_fields T one_mem_fields (f w).1.2⟩
    by_cases hb : b.IsPositivelyOriented
    · have e : (fun w => levelField (expMove (f w) (unitPoint L n k)) 0 b) = fun w =>
          ComplexMatrix2.matExp (Complex.I • ((f w).1 : Edge L n k 0 → ComplexMatrix2) b) *
            (1 : ComplexMatrix2) :=
        funext fun w => expTwist_pos hb
      rw [e]
      exact hp b hb
    · have hr := T.opposite_pos (Nat.zero_le k) hb
      have e : (fun w => levelField (expMove (f w) (unitPoint L n k)) 0 b) = fun w =>
          (ComplexMatrix2.matExp (Complex.I • ((f w).1 : Edge L n k 0 → ComplexMatrix2) b.opposite) *
            (1 : ComplexMatrix2))⁻¹ :=
        funext fun w => expTwist_neg hb
      rw [e]
      have h4 := continuousAt_inv_at_one.tendsto.comp (hp _ hr)
      rw [hone] at h4
      exact h4
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    have IH := ih hlt.le
    have hL2 : 2 ≤ L := by
      have := hL.2
      omega
    have : NeZero L := ⟨by omega⟩
    have hfin : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    let _ : Fintype (Edge L n k j) := Fintype.ofFinite _
    obtain ⟨ρ, hρ, HA⟩ := hAn L hL
    have hflat : (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
      ⟨fun _ _ => by simp [PeriodicLattice.complexGaugeGroup, ComplexMatrix2.unitDeterminant],
        fun _ _ => (Matrix.inv_eq_right_inv (mul_one 1)).symm⟩
    have hcont : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → Tendsto
        (fun w => normalizedMean (levelField (expMove (f w) (unitPoint L n k)) j) c)
        (𝓝 0) (𝓝 1) := by
      intro c hc
      have h1 := (HA n k j hn hlt _ hflat (fun b => by simpa using hρ) c hc).2.continuousAt
      have h2 := (hD L hL n k j hn hlt 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
      have h3 := h1.tendsto
      rw [h2] at h3
      exact h3.comp (IH.mono_right nhdsWithin_le_nhds)
    have hnoise : ∀ c : PositiveEdge L n k (j + 1), Tendsto
        (fun w => (expMove (f w) (unitPoint L n k)).noise ⟨j, hlt⟩ c) (𝓝 0) (𝓝 1) := fun c =>
      tendsto_matExp_linear
        ((LinearMap.proj c.1 : (Edge L n k (j + 1) → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2) ∘ₗ
        (edgeFormSpace L n k (j + 1)).subtype ∘ₗ
        (LinearMap.proj (φ := fun i : Fin k => edgeFormSpace L n k (i + 1)) ⟨j, hlt⟩) ∘ₗ
        LinearMap.snd ℝ _ _ ∘ₗ f)
    have hp : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented, Tendsto
        (fun w => (expMove (f w) (unitPoint L n k)).noise ⟨j, hlt⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (expMove (f w) (unitPoint L n k)) j) c) (𝓝 0) (𝓝 1) := by
      intro c hc
      have h := (hnoise ⟨c, hc⟩).mul (hcont c hc)
      rwa [mul_one] at h
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, ?_⟩
    · by_cases hb : b.IsPositivelyOriented
      · have e : (fun w => levelField (expMove (f w) (unitPoint L n k)) (j + 1) b) = fun w =>
            (expMove (f w) (unitPoint L n k)).noise ⟨j, hlt⟩ ⟨b, hb⟩ *
              normalizedMean (levelField (expMove (f w) (unitPoint L n k)) j) b :=
          funext fun w => levelField_pos _ hlt hb
        rw [e]
        exact hp b hb
      · have hr := T.opposite_pos hj hb
        have e : (fun w => levelField (expMove (f w) (unitPoint L n k)) (j + 1) b) = fun w =>
            ((expMove (f w) (unitPoint L n k)).noise ⟨j, hlt⟩ ⟨b.opposite, hr⟩ *
              normalizedMean (levelField (expMove (f w) (unitPoint L n k)) j) b.opposite)⁻¹ :=
          funext fun w => levelField_neg _ hlt hb hr
        rw [e]
        have h4 := continuousAt_inv_at_one.tendsto.comp (hp _ hr)
        rw [hone] at h4
        exact h4
    · filter_upwards [IH.eventually (hS L hL n k j hn hlt)] with w hw
      obtain ⟨-, hreal, -⟩ := hw
      rw [levelField_succ _ hlt]
      exact fieldOfValues_mem T hj fun c => Submonoid.mul_mem _
        (T.left_chart_real (j + 1) hj _ one_mem_fields _ ((f w).2 ⟨j, hlt⟩).2 c.1 c.2) (hreal c.1 c.2).2.2
private theorem exists_level_radius (hS : MeanDerivOnForms.Claim)
    (hY : RealLinearMaps.RealLinearMapsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ m ≤ k, ∃ δ : ℝ, 0 < δ ∧ ∀ j < m, ∀ V ∈ fieldSpace L n k j,
      (∀ b, ‖V b - 1‖ < δ) → LevelFacts V := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    intro hm
    have hlt : m < k := hm
    obtain ⟨δ, hδ, h⟩ := ih hlt.le
    have hfin : Finite (Edge L n k m) := PeriodicLattice.instFiniteBond _
    obtain ⟨δ', hδ', h'⟩ := exists_radius_of_nearOne (eventually_levelFacts (L := L) (n := n) (k := k) (j := m)
      hS hY hL hn hlt)
    refine ⟨min δ δ', lt_min hδ hδ', fun j hj V hV hs => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact h j hj' V hV fun b => (hs b).trans_le (min_le_left _ _)
    · exact h' V hV fun b => (hs b).trans_le (min_le_right _ _)
end NearUnitPoint
end ChainCovarianceProof
open ChainCovarianceProof YangMills.Construction.Tower in
theorem chainFunctionGaugeCovariance_holds
    (hEnt : ChainFunctionEntriesAnalytic)
    (hlegs : AxisOrderLegsAreContours)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hQ : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hGC : AveragesGaugeCovariant)
    (hA : SmoothingNearIdentity)
    (hG : GaugeEquivarianceFormsAllSides)
    (hPo : MeanStableFields.MeanStableFieldsHold)
    (hC : LeftChartFields.Claim)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hAct : ActionFacts.Statement)
    (hSp : FiniteSideFormSpaces)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement)
    (hS : MeanDerivOnForms.Claim)
    (hAn : NormalizedMeanAnalytic)
    (hD : NormalizedMeanAtOne) :
    ChainFunctionGaugeCovariance := by
  intro a ha L hL k n hk hn N e
  have T : TowerData L n k :=
    { side_pos := by have := hL.2; omega
      xor_positive := fun i hi b => hO L n k hL hn hk i hi b
      polydisc_ok := fun i hi c hc => (hA.1 L hL).2.2.periodic n k i hn hi c hc
      mem_polydisc := fun i hi c hc V hV =>
        ((hPo L hL k (by omega)).1 n hn).mem_polydisc i hi c hc V hV
      isOpen_nearOne := fun i hi => ((hPo L hL k (by omega)).1 n hn).isOpen_nearOne i hi
      gauge_forms := fun i hi => (hG L k i hL hi).1 n hn
      left_chart := fun i hi V hV B hB b hb =>
        ((hC.2.2 L k i hL hi).1 n hn).1.1.2 V hV B hB ⟨b, hb⟩
      left_chart_real := fun i hi V hV B hB b hb => by
        have h := (((hC.2.2 L k i hL hi).1 n hn).1.1.1 V hV B hB ⟨b, hb⟩).1 1
        simpa [LeftChartFields.leftExpMul,
          LeftChartFields.LatticeData.onPositive,
          LeftChartFields.finiteData] using h
      action_invariant := (hAct L k n hL hn).2.1
      mean_covariant := fun j hj V v hd c hc => contourMean_gauge hlegs hcf hbb hb hL hn hj V v hd c hc }
  have hYt := (hY L n k hL hn hk).2
  have hC₀ : EdgeFormsEuclidean L n k 0 := by
    obtain ⟨-, f, -, c, h⟩ := hSp L n k 0 hL hn (Nat.zero_le k)
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have h₀ : VertexFunctionsEuclidean L n k 0 := hSite L n k 0 hL hn (Nat.zero_le k)
  have hk' : VertexFunctionsEuclidean L n k k := hSite L n k k hL hn le_rfl
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hfin₀ : Finite (Edge L n k 0) := PeriodicLattice.instFiniteBond _
  obtain ⟨δ₀, hδ₀, hgood⟩ := exists_radius_of_nearOne
    (eventually_nearIdentityFacts (L := L) (n := n) (k := k) hQ hE hY hL hn hk)
  obtain ⟨δ₁, hδ₁, hstep⟩ := exists_level_radius (L := L) (n := n) (k := k) hS hY hL hn k le_rfl
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ :=
    ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, min_le_left _ _, min_le_right _ _⟩
  let f : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k :=
    LinearMap.fst ℝ _ _ ∘ₗ (e : (Fin N → ℝ) →ₗ[ℝ] LevelTriple L n k)
  have hten := tendsto_levelFields T hS hAn hD hL hn f
  have hev : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ∀ j ∈ Finset.range (k + 1),
      levelField (expMove (f w) (unitPoint L n k)) j ∈ fieldSpace L n k j ∧
        ∀ b, ‖levelField (expMove (f w) (unitPoint L n k)) j b - 1‖ < δ / 2 := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hjk : j ≤ k := by
      have := Finset.mem_range.1 hj
      omega
    have hfin : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    have hnear : ∀ᶠ V in 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)),
        V ∈ fieldSpace L n k j ∧ ∀ b, ‖V b - 1‖ < δ / 2 := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_near_one (half_pos hδ))]
        with V h₁ h₂
      exact ⟨h₁, h₂⟩
    exact (hten j hjk).eventually hnear
  obtain ⟨hq, -⟩ := hEnt a ha L hL k n hk hn N e
  refine ⟨δ / 4, by positivity, ?_⟩
  filter_upwards [hev, hq] with w hw hqw v hv hvn J' μ' hJ hμ
  have hw' : ∀ j ≤ k, levelField (expMove (e w).1 (unitPoint L n k)) j ∈ fieldSpace L n k j ∧
      ∀ b, ‖levelField (expMove (e w).1 (unitPoint L n k)) j b - 1‖ < δ / 2 :=
    fun j hj => hw j (Finset.mem_range.2 (by omega))
  have hvG : v ∈ gaugeGroupAt L n k 0 := hv
  have hd : ∀ x, (v x).det = 1 := det_of_gauge hvG
  have hsmall : ∀ j ≤ k, ∀ b,
      ‖levelField (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) j b - 1‖ < δ := by
    intro j hj b
    rw [levelField_gauge T hd _ j hj]
    change ‖restrictVertexFunction j v b.source * levelField (expMove (e w).1 (unitPoint L n k)) j b *
      (restrictVertexFunction j v b.target)⁻¹ - 1‖ < δ
    have h1 := (hw' j hj).2 b
    rcases hvn with hnear | hconst
    · have h0 := norm_gauge_sub_one_le (X := levelField (expMove (e w).1 (unitPoint L n k)) j b)
        (hv (b.source.toSublattice (PeriodicLattice.levelDepth k 0)))
        (hv (b.target.toSublattice (PeriodicLattice.levelDepth k 0)))
      have h2 : ‖restrictVertexFunction j v b.source - 1‖ < δ / 4 := hnear _
      have h3 : ‖restrictVertexFunction j v b.target - 1‖ < δ / 4 := hnear _
      have h0' : ‖restrictVertexFunction j v b.source * levelField (expMove (e w).1 (unitPoint L n k)) j b *
          (restrictVertexFunction j v b.target)⁻¹ - 1‖ ≤
            ‖levelField (expMove (e w).1 (unitPoint L n k)) j b - 1‖ +
            ‖restrictVertexFunction j v b.source - 1‖ + ‖restrictVertexFunction j v b.target - 1‖ := h0
      linarith
    · have e₁ : restrictVertexFunction j v b.target = restrictVertexFunction j v b.source := hconst _ _
      have hr : restrictVertexFunction j v b.source ∈ PeriodicLattice.compactGaugeGroup := hv _
      rw [e₁, norm_conj_sub_one_of_compact hr]
      exact h1.trans (half_lt_self hδ)
  have hP : PointFacts (expMove (e w).1 (unitPoint L n k)) :=
    { noise_mem := fun i c => T.left_chart_real (i + 1) i.2 _ one_mem_fields _ ((e w).1.2 i).2 c.1 c.2
      field_mem := fun j hj => (hw' j hj).1
      level_facts := fun j hj => hstep j hj _ (hw' j hj.le).1 fun b =>
        ((hw' j hj.le).2 b).trans (lt_of_lt_of_le (half_lt_self hδ) hδb) }
  have hconf' : ∀ j ≤ k, levelField (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) j ∈
      fieldSpace L n k j := fun j hj => by
    rw [levelField_gauge T hd _ j hj]
    exact gaugeTransform_mem_fields (fun x => hv _) (hP.field_mem j hj)
  have hP' : PointFacts (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) :=
    { noise_mem := fun i c => Submonoid.mul_mem _ (Submonoid.mul_mem _ (hv _) (hP.noise_mem i c))
        (inv_mem_compact (hv _))
      field_mem := hconf'
      level_facts := fun j hj => hstep j hj _ (hconf' j hj.le) fun b =>
        (hsmall j hj.le b).trans_le hδb }
  have hU := hgood _ (hP.field_mem 0 (Nat.zero_le k)) fun b =>
    ((hw' 0 (Nat.zero_le k)).2 b).trans (lt_of_lt_of_le (half_lt_self hδ) hδa)
  have hU' := hgood _ (hconf' 0 (Nat.zero_le k)) fun b =>
    (hsmall 0 (Nat.zero_le k) b).trans_le hδa
  have hcF := hC₀.2.choose_spec
  have hcS := h₀.2.choose_spec
  have hcK := hk'.2.choose_spec
  exact covariant_at_pair T hYt hGC hL hn hvG hcF hcS hcK hP hP' hU hU' a hqw hJ hμ
end RunningCouplingSlope
end YangMills.Construction
end
