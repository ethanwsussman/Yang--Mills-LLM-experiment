import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.ChainOfTheComplexIterateDifferentials
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscs
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesOnTheSides
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSides
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.GaugeCovarianceProof
open YangMills.Construction.Matrices
section Matrices
theorem inv_mul_cancel_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [h]; exact isUnit_one)
theorem mul_inv_cancel_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V * V⁻¹ = 1 :=
  Matrix.mul_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem inv_inv_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem det_eq_one_of_mem_compact {V : ComplexMatrix2}
    (h : V ∈ PeriodicLattice.compactGaugeGroup) : V.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem det_inv_of_det_one {g : ComplexMatrix2} (hg : g.det = 1) : (g⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_sub (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X - Y) =
      ComplexMatrix2.conjugateBy g X - ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_zero (g : ComplexMatrix2) : ComplexMatrix2.conjugateBy g 0 = 0 := by
  simp only [ComplexMatrix2.conjugateBy, mul_zero, zero_mul]
theorem conjugateBy_traceless {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem conjugateBy_conjugateBy_gauge {g h : ComplexMatrix2} (X A : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (g * X * h⁻¹) (ComplexMatrix2.conjugateBy h A) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy X A) := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_inv_rev, inv_inv_of_det_one hh]
  have hi := inv_mul_cancel_of_det_one hh
  calc g * X * h⁻¹ * (h * A * h⁻¹) * (h * (X⁻¹ * g⁻¹))
      = g * X * (h⁻¹ * h) * A * (h⁻¹ * h) * (X⁻¹ * g⁻¹) := by simp only [mul_assoc]
    _ = g * (X * A * X⁻¹) * g⁻¹ := by rw [hi, mul_one, mul_one]; simp only [mul_assoc]
def conjEquiv {g : ComplexMatrix2} (hg : g.det = 1) : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2 :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.mul ℂ ComplexMatrix2 g).comp
      ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip g⁻¹))
    ((ContinuousLinearMap.mul ℂ ComplexMatrix2 g⁻¹).comp
      ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip g))
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
theorem conjEquiv_apply {g : ComplexMatrix2} (hg : g.det = 1) (Y : ComplexMatrix2) :
    conjEquiv hg Y = ComplexMatrix2.conjugateBy g Y := by
  change g * (Y * g⁻¹) = g * Y * g⁻¹
  rw [mul_assoc]
theorem conjugateBy_finsum_mem {ι : Type*} {g : ComplexMatrix2} (hg : g.det = 1) (S : Set ι)
    (f : ι → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (∑ᶠ x ∈ S, f x) = ∑ᶠ x ∈ S, ComplexMatrix2.conjugateBy g (f x) := by
  let φ : ComplexMatrix2 →+ ComplexMatrix2 :=
    { toFun := ComplexMatrix2.conjugateBy g
      map_zero' := conjugateBy_zero g
      map_add' := conjugateBy_add g }
  have hφ : Function.Injective φ := fun X Y h => (conjEquiv hg).injective (by
    rw [conjEquiv_apply, conjEquiv_apply]
    exact h)
  change φ _ = ∑ᶠ x ∈ S, φ (f x)
  rw [φ.map_finsum_of_injective hφ]
  exact finsum_congr fun x => φ.map_finsum_of_injective hφ _
theorem logSeries_conj {g : ComplexMatrix2} (hg : g.det = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.logSeries (g * X * g⁻¹) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.logSeries X) := by
  have hi := inv_mul_cancel_of_det_one hg
  have hi' := mul_inv_cancel_of_det_one hg
  have hE : ∀ Y, conjEquiv hg Y = g * Y * g⁻¹ := conjEquiv_apply hg
  have hp : ∀ m : ℕ, (1 - g * X * g⁻¹) ^ m = g * (1 - X) ^ m * g⁻¹ := by
    intro m
    induction m with
    | zero => simp [hi']
    | succ m ih =>
      have e1 : 1 - g * X * g⁻¹ = g * (1 - X) * g⁻¹ := by
        rw [mul_sub, sub_mul, mul_one, hi']
      rw [pow_succ, ih, e1, pow_succ]
      calc g * (1 - X) ^ m * g⁻¹ * (g * (1 - X) * g⁻¹)
          = g * (1 - X) ^ m * (g⁻¹ * g) * (1 - X) * g⁻¹ := by simp only [mul_assoc]
        _ = g * ((1 - X) ^ m * (1 - X)) * g⁻¹ := by
          rw [hi, mul_one]; simp only [mul_assoc]
  have hs : ∑' m : ℕ, ((m + 1 : ℂ)⁻¹) • (1 - g * X * g⁻¹) ^ (m + 1) =
      conjEquiv hg (∑' m : ℕ, ((m + 1 : ℂ)⁻¹) • (1 - X) ^ (m + 1)) := by
    rw [(conjEquiv hg).map_tsum]
    refine tsum_congr fun m => ?_
    rw [map_smul, hE, hp]
  unfold ComplexMatrix2.logSeries
  rw [hs, hE]
  simp only [ComplexMatrix2.conjugateBy, mul_neg, neg_mul]
theorem mul_inv_gauge_conj {g h W W₀ : ComplexMatrix2} (hh : h.det = 1) :
    (g * W * h⁻¹) * (g * W₀ * h⁻¹)⁻¹ = g * (W * W₀⁻¹) * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_one hh]
  calc g * W * h⁻¹ * (h * (W₀⁻¹ * g⁻¹)) = g * W * (h⁻¹ * h) * (W₀⁻¹ * g⁻¹) := by
        simp only [mul_assoc]
    _ = g * (W * W₀⁻¹) * g⁻¹ := by
        rw [inv_mul_cancel_of_det_one hh, mul_one]; simp only [mul_assoc]
theorem deriv_continuousLinearEquiv (E : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2) (f : ℂ → ComplexMatrix2) :
    deriv (fun t => E (f t)) 0 = E (deriv f 0) := by
  by_cases hf : DifferentiableAt ℂ f 0
  · exact ((E : ComplexMatrix2 →L[ℂ] ComplexMatrix2).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
      hf.hasDerivAt).deriv
  · have hn : ¬ DifferentiableAt ℂ (fun t => E (f t)) 0 := fun h =>
      hf (E.comp_differentiableAt_iff.1 h)
    rw [deriv_zero_of_not_differentiableAt hn, deriv_zero_of_not_differentiableAt hf, map_zero]
theorem logDirectionalDeriv_conj {α β : Type*} {g : ComplexMatrix2} (hg : g.det = 1)
    {φ : (α → ComplexMatrix2) → ComplexMatrix2} {ψ : (β → ComplexMatrix2) → ComplexMatrix2}
    {W W' : ComplexMatrix2} {A : α → ComplexMatrix2} {A' : β → ComplexMatrix2}
    (h : ∀ᶠ t : ℂ in 𝓝 0, ψ (t • A') * W'⁻¹ = g * (φ (t • A) * W⁻¹) * g⁻¹) :
    logDirectionalDeriv ℂ ψ W' A' =
      ComplexMatrix2.conjugateBy g (logDirectionalDeriv ℂ φ W A) := by
  unfold logDirectionalDeriv
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hl : (fun t : ℂ => ComplexMatrix2.logSeries (ψ (t • A') * W'⁻¹)) =ᶠ[𝓝 0]
      fun t => conjEquiv hg (ComplexMatrix2.logSeries (φ (t • A) * W⁻¹)) := by
    filter_upwards [h] with t ht
    rw [ht, logSeries_conj hg, conjEquiv_apply]
  rw [hl.deriv_eq, deriv_continuousLinearEquiv, conjEquiv_apply, conjugateBy_smul]
end Matrices
section Data
variable {L n k i : ℕ}
structure TowerData (L n k : ℕ) : Prop where
  positive : 0 < L
  orientation : ∀ i ≤ k, ∀ b : Edge L n k i,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  admissible : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  inPolydisc : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ smallComplexFields L n k i, V ∈ nearIdentityPolydisc (polydiscRadius L) c
  isOpen_nearOne : ∀ i < k, IsOpenFieldSet PeriodicLattice.complexGaugeGroup
    (MeanStableFields.fieldsNearOne L n k i)
  gauge : ∀ i ≤ k, LeftChartFacts.GaugeEquivarianceForms L n k i
  left : ∀ i ≤ k, ∀ V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup,
    ∀ B ∈ complexEdgeForms L n k i, ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b ∈
          PeriodicLattice.complexGaugeGroup) ∧
        HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b)
          (Complex.I • B b * V b) 0
theorem opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem TowerData.opposite_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem TowerData.opposite_not_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases T.orientation i hi b with h | h
  · exact h.2
  · exact absurd hb h.2
theorem extendOddly_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
theorem extendOddly_neg {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
theorem extendOddly_congr (T : TowerData L n k) (hi : i ≤ k) {g g' : Edge L n k i → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → g b = g' b) : extendOddly g = extendOddly g' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_pos hb, extendOddly_pos hb, h b hb]
  · rw [extendOddly_neg hb, extendOddly_neg hb, h _ (T.opposite_pos hi hb)]
theorem extendOddly_opposite (T : TowerData L n k) (hi : i ≤ k) (g : Edge L n k i → ComplexMatrix2)
    (b : Edge L n k i) : extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_neg (T.opposite_not_pos hi hb), extendOddly_pos hb, opposite_opposite]
  · rw [extendOddly_pos (T.opposite_pos hi hb), extendOddly_neg hb, neg_neg]
theorem adjointForm_pos (u : Vertex L n k i → ComplexMatrix2) (B : Edge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) :=
  extendOddly_pos hb
theorem adjointForm_neg (u : Vertex L n k i → ComplexMatrix2) (B : Edge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (hb : ¬b.IsPositivelyOriented) :
    adjointForm u B b = -ComplexMatrix2.conjugateBy (u b.opposite.source) (B b.opposite) :=
  extendOddly_neg hb
theorem adjointForm_add (u : Vertex L n k i → ComplexMatrix2) (B B' : Edge L n k i → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.adjointForm_add <;> assumption
theorem smul_adjointForm (u : Vertex L n k i → ComplexMatrix2) (t : ℂ)
    (B : Edge L n k i → ComplexMatrix2) : t • adjointForm u B = adjointForm u (t • B) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, adjointForm_pos _ _ hb, conjugateBy_smul]
  · simp only [Pi.smul_apply, adjointForm_neg _ _ hb, conjugateBy_smul, smul_neg]
theorem adjointForm_mem (T : TowerData L n k) (hi : i ≤ k) {u : Vertex L n k i → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) : adjointForm u B ∈ complexEdgeForms L n k i := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite T hi _ b⟩
  rw [adjointForm_pos _ _ hb]
  exact conjugateBy_traceless (hu _) (hB.1 b hb)
theorem adjointVertexFn_add (u l l' : Vertex L n k i → ComplexMatrix2) :
    adjointVertexFn u (l + l') = adjointVertexFn u l + adjointVertexFn u l' :=
  funext fun _ => conjugateBy_add _ _ _
theorem covDiff_gauge (T : TowerData L n k) (hi : i ≤ k) {u : Vertex L n k i → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) (U : Edge L n k i → ComplexMatrix2) (l : Vertex L n k i → ComplexMatrix2) :
    covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
      adjointForm u (covDiff U l) := by
  unfold adjointForm
  refine (extendOddly_congr T hi fun b hb => ?_ :
    extendOddly (fun b => ComplexMatrix2.conjugateBy (PeriodicLattice.gaugeTransform u U b)
      (adjointVertexFn u l b.target) - adjointVertexFn u l b.source) = _)
  have hD : covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source :=
    extendOddly_pos hb
  change ComplexMatrix2.conjugateBy (u b.source * U b * (u b.target)⁻¹)
      (ComplexMatrix2.conjugateBy (u b.target) (l b.target)) -
    ComplexMatrix2.conjugateBy (u b.source) (l b.source) =
      ComplexMatrix2.conjugateBy (u b.source) (covDiff U l b)
  rw [hD, conjugateBy_conjugateBy_gauge _ _ (hu _), conjugateBy_sub]
theorem expTwist_pos {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b := if_pos hb
theorem expTwist_neg {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹ := if_neg hb
theorem expTwist_mem (T : TowerData L n k) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) :
    PeriodicLattice.expTwist B V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  have hp : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • B b) * V b).det = 1 := fun b hb => by
    have := (T.left i hi V hV B hB b hb).1 1
    rwa [one_smul] at this
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_pos hb]
      exact hp b hb
    · rw [expTwist_neg hb]
      exact det_inv_of_det_one (hp _ (T.opposite_pos hi hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_neg (T.opposite_not_pos hi hb), expTwist_pos hb, opposite_opposite]
    · have hr := T.opposite_pos hi hb
      rw [expTwist_pos hr, expTwist_neg hb, inv_inv_of_det_one (hp _ hr)]
theorem expTwist_zero (T : TowerData L n k) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_pos hb]
    simp [ComplexMatrix2.matExp]
  · have hr := T.opposite_pos hi hb
    rw [expTwist_neg hb]
    have := hV.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at this
    simp [ComplexMatrix2.matExp, this]
theorem eq_of_restrictToPositiveEdges_eq (T : TowerData L n k) (hi : i ≤ k)
    {V V' : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hV' : V' ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (h : restrictToPositiveEdges V = restrictToPositiveEdges V') : V = V' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact congrFun h ⟨b, hb⟩
  · have hr := T.opposite_pos hi hb
    have h₁ := hV.2 b.opposite (mem_univ _)
    have h₂ := hV'.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at h₁ h₂
    rw [h₁, h₂, show V b.opposite = V' b.opposite from congrFun h ⟨b.opposite, hr⟩]
theorem eventually_expTwist_small (T : TowerData L n k) (hj : i < k) {V B : Edge L n k i → ComplexMatrix2}
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
    have hd := (T.left i hj.le V hV.1 B hB b.1 b.2).2.continuousAt
    refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
    change _ = PeriodicLattice.expTwist (t • B) V b.1
    rw [expTwist_pos b.2]
    rfl
  have h0 : restrictToPositiveEdges (PeriodicLattice.expTwist ((0 : ℂ) • B) V) =
      restrictToPositiveEdges V := by
    rw [expTwist_zero T hj.le hV.1]
  have hev : ∀ᶠ t : ℂ in 𝓝 0, restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈ O :=
    hcont.eventually_mem (by rw [h0]; exact hO.mem_nhds hV0)
  filter_upwards [hev] with t ht
  have hm := expTwist_mem T hj.le hV.1 ((complexEdgeForms L n k i).smul_mem t hB)
  have hmem : restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈ restrictToPositiveEdges ''
      MeanStableFields.fieldsNearOne L n k i := by
    rw [himg]
    exact ⟨ht, fun b => hm.1 _ (mem_univ _)⟩
  obtain ⟨W, hW, he⟩ := hmem
  have : W = PeriodicLattice.expTwist (t • B) V :=
    eq_of_restrictToPositiveEdges_eq T hj.le hW.1 hm he
  exact this ▸ hW
end Data
section StepMaps
variable {L n k i : ℕ} {V : Edge L n k i → ComplexMatrix2} {u : Vertex L n k i → ComplexMatrix2}
theorem det_of_mem_gaugeGroupAt (hu : u ∈ gaugeGroupAt L n k i) (x : Vertex L n k i) :
    (u x).det = 1 :=
  det_eq_one_of_mem_compact (hu x)
theorem inv_gauge_form {g h X : ComplexMatrix2} (hh : h.det = 1) :
    (g * X * h⁻¹)⁻¹ = h * X⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_one hh, mul_assoc]
theorem expTwist_gauge (T : TowerData L n k) (hi : i ≤ k)
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hu : u ∈ gaugeGroupAt L n k i) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) (t : ℂ) :
    PeriodicLattice.expTwist (t • adjointForm u B) (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist (t • B) V) := by
  rw [smul_adjointForm]
  exact (T.gauge i hi u (fun x => det_of_mem_gaugeGroupAt hu x)).1 V hV (t • B)
    ((complexEdgeForms L n k i).smul_mem t hB)
theorem complexBlockAverage_of_not_pos {a : ℕ} (W : Edge L n k i → ComplexMatrix2)
    (T : TowerData L n k) (ha : a ≤ k) {c : Edge L n k a} (hc : ¬c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W c =
      (PeriodicLattice.complexBlockAverage W c.opposite)⁻¹ := by
  have hr := T.opposite_pos ha hc
  simp only [PeriodicLattice.complexBlockAverage, if_neg hc, if_pos hr]
theorem blockAverageStep_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i) :
    PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i V) := by
  have hr : ∀ x, (restrictVertexFunction (i + 1) u x).det = 1 := fun x =>
    det_eq_one_of_mem_compact (hu _)
  have hpos : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
          (PeriodicLattice.complexBlockAverage V) c :=
    fun c hc => ((T.admissible i hi c hc).gauge_covariant V (T.inPolydisc i hi c hc V hV) u hu).2.1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hp := T.opposite_pos (show i + 1 ≤ k from hi) hc
    show PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
      restrictVertexFunction (i + 1) u c.source * PeriodicLattice.complexBlockAverage V c *
        (restrictVertexFunction (i + 1) u c.target)⁻¹
    rw [complexBlockAverage_of_not_pos _ T (show i + 1 ≤ k from hi) hc, hpos _ hp,
      complexBlockAverage_of_not_pos V T (show i + 1 ≤ k from hi) hc]
    exact inv_gauge_form (hr _)
theorem contour_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x =
      u (y.toSublattice (PeriodicLattice.levelDepth k i)) *
        PeriodicLattice.complexMeanContourHolonomy V y x * (u x)⁻¹ := by
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  exact ((T.admissible i hi _ hc).gauge_covariant V (T.inPolydisc i hi _ hc V hV) u hu).2.2
    y (Or.inl rfl) x hx
theorem adjointCubeAverage_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i)
    (l : Vertex L n k i → ComplexMatrix2) :
    adjointCubeAverage (PeriodicLattice.gaugeTransform u V) (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction (i + 1) u) (adjointCubeAverage V l) := by
  funext y
  have hg : (u (y.toSublattice (PeriodicLattice.levelDepth k i))).det = 1 :=
    det_of_mem_gaugeGroupAt hu _
  change PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        ComplexMatrix2.conjugateBy
          (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x)
          (ComplexMatrix2.conjugateBy (u x) (l x)) =
    ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i)))
      (PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x))
  rw [conjugateBy_smul, conjugateBy_finsum_mem hg]
  congr 1
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [contour_gauge T hi hV hu y hx, conjugateBy_conjugateBy_gauge _ _ (det_of_mem_gaugeGroupAt hu x)]
theorem logDeriv_contour_gauge (T : TowerData L n k) (hi : i < k)
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
  refine logDirectionalDeriv_conj (det_of_mem_gaugeGroupAt hu _) ?_
  filter_upwards [eventually_expTwist_small T hi hV hB] with t ht
  rw [expTwist_gauge T hi.le hV.1 hu hB t, contour_gauge T hi ht hu y hx,
    contour_gauge T hi hV hu y hx]
  exact mul_inv_gauge_conj (det_of_mem_gaugeGroupAt hu x)
theorem contourLogDrift_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i)
    (hu : u ∈ gaugeGroupAt L n k i) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) :
    contourLogDrift (PeriodicLattice.gaugeTransform u V) (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction (i + 1) u) (contourLogDrift V B) := by
  funext y
  have hg : (u (y.toSublattice (PeriodicLattice.levelDepth k i))).det = 1 :=
    det_of_mem_gaugeGroupAt hu _
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
  rw [conjugateBy_smul, conjugateBy_finsum_mem hg]
  congr 1
  exact finsum_mem_congr rfl fun x hx => logDeriv_contour_gauge T hi hV hu y hx hB
theorem complexSmoothingDeriv_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i)
    (hu : u ∈ gaugeGroupAt L n k i) {B : Edge L n k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k i) :
    complexSmoothingDeriv (PeriodicLattice.gaugeTransform u V) (adjointForm u B) =
      adjointForm (restrictVertexFunction (i + 1) u) (complexSmoothingDeriv V B) := by
  unfold adjointForm
  refine (extendOddly_congr T (show i + 1 ≤ k from hi) fun c hc => ?_ :
    extendOddly (fun c => logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexBlockAverageStep i
        (PeriodicLattice.expTwist X (PeriodicLattice.gaugeTransform u V)) c)
      (PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.gaugeTransform u V) c)
      (extendOddly fun b => ComplexMatrix2.conjugateBy (u b.source) (B b))) = _)
  have e : complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.expTwist X V) c)
      (PeriodicLattice.complexBlockAverageStep i V c) B := if_pos hc
  rw [e]
  refine logDirectionalDeriv_conj (det_eq_one_of_mem_compact (hu _)) ?_
  filter_upwards [eventually_expTwist_small T hi hV hB] with t ht
  have hx := expTwist_gauge T hi.le hV.1 hu hB t
  unfold adjointForm at hx
  rw [hx, blockAverageStep_gauge T hi ht hu, blockAverageStep_gauge T hi hV hu]
  exact mul_inv_gauge_conj (det_eq_one_of_mem_compact (hu _))
end StepMaps
section Levels
variable {L n k : ℕ} {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
theorem coe_toSublattice {a b : ℤ} (hL : 0 < L) (h : a ≤ b) (y : PeriodicLattice.Site L n a) :
    ((y.toSublattice b : PeriodicLattice.Site L n b) : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
theorem restrictVertexFunction_zero (hL : 0 < L) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 l = l := by
  funext x
  show l (x.toSublattice (PeriodicLattice.levelDepth k 0)) = l x
  exact congrArg l (Subtype.ext (coe_toSublattice hL le_rfl x))
theorem restrictVertexFunction_succ (hL : 0 < L) (i : ℕ) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (restrictVertexFunction i l) = restrictVertexFunction (i + 1) l := by
  funext x
  show l ((x.toSublattice (PeriodicLattice.levelDepth k i)).toSublattice
      (PeriodicLattice.levelDepth k 0)) = l (x.toSublattice (PeriodicLattice.levelDepth k 0))
  have h₁ : PeriodicLattice.levelDepth k (i + 1) ≤ PeriodicLattice.levelDepth k i := by
    simp [PeriodicLattice.levelDepth]
    omega
  have h₂ : PeriodicLattice.levelDepth k i ≤ PeriodicLattice.levelDepth k 0 := by
    simp [PeriodicLattice.levelDepth]
  refine congrArg l (Subtype.ext ?_)
  rw [coe_toSublattice hL h₂, coe_toSublattice hL h₁, coe_toSublattice hL (h₁.trans h₂)]
theorem restrictVertexFunction_mem (hu : u ∈ gaugeGroupAt L n k 0) (i : ℕ) :
    restrictVertexFunction i u ∈ gaugeGroupAt L n k i :=
  fun _ => hu _
theorem complexBlockField_gauge (T : TowerData L n k) (hU : U ∈ smallIterateFields L n k)
    (hu : u ∈ gaugeGroupAt L n k 0) :
    ∀ i ≤ k, PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction i u)
        (PeriodicLattice.complexBlockFieldAtLevel i U) := by
  intro i
  induction i with
  | zero =>
    intro _
    show PeriodicLattice.gaugeTransform u U =
      PeriodicLattice.gaugeTransform (restrictVertexFunction 0 u) U
    rw [restrictVertexFunction_zero T.positive]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show PeriodicLattice.complexBlockAverageStep i
        (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U)) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i U))
    rw [ih hi.le, blockAverageStep_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i),
      restrictVertexFunction_succ T.positive]
theorem iterAdjointCubeAverage_gauge (T : TowerData L n k) (hU : U ∈ smallIterateFields L n k)
    (hu : u ∈ gaugeGroupAt L n k 0) (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ i ≤ k, iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) i (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction i u) (iterAdjointCubeAverage L n k U i l) := by
  intro i
  induction i with
  | zero =>
    intro _
    show adjointVertexFn u l = adjointVertexFn (restrictVertexFunction 0 u) l
    rw [restrictVertexFunction_zero T.positive]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show adjointCubeAverage
        (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U))
        (iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) i (adjointVertexFn u l)) =
      adjointVertexFn (restrictVertexFunction (i + 1) u)
        (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
          (iterAdjointCubeAverage L n k U i l))
    rw [ih hi.le, complexBlockField_gauge T hU hu i hi.le,
      adjointCubeAverage_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i),
      restrictVertexFunction_succ T.positive]
abbrev IterDerivChain (L n k : ℕ) : Prop :=
  ∀ U ∈ smallIterateFields L n k, ∀ B ∈ complexEdgeForms L n k 0,
    complexIterDeriv L n k 0 U B = B ∧
    (∀ j < k, complexIterDeriv L n k (j + 1) U B =
      complexSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U)
        (complexIterDeriv L n k j U B)) ∧
    ∀ j ≤ k, complexIterDeriv L n k j U B ∈ complexEdgeForms L n k j
theorem complexIterDeriv_gauge (T : TowerData L n k) (hI : IterDerivChain L n k)
    (hU : U ∈ smallIterateFields L n k) (hu : u ∈ gaugeGroupAt L n k 0)
    (hW : PeriodicLattice.gaugeTransform u U ∈ smallIterateFields L n k)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k 0)
    (hB' : adjointForm u B ∈ complexEdgeForms L n k 0) :
    ∀ i ≤ k, complexIterDeriv L n k i (PeriodicLattice.gaugeTransform u U) (adjointForm u B) =
      adjointForm (restrictVertexFunction i u) (complexIterDeriv L n k i U B) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [(hI _ hW _ hB').1, (hI U hU B hB).1, restrictVertexFunction_zero T.positive]
  | succ i ih =>
    intro h
    have hi : i < k := h
    rw [(hI _ hW _ hB').2.1 i hi, (hI U hU B hB).2.1 i hi, ih hi.le,
      complexBlockField_gauge T hU hu i hi.le,
      complexSmoothingDeriv_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i)
        ((hI U hU B hB).2.2 i hi.le),
      restrictVertexFunction_succ T.positive]
theorem iterContourLogDrift_gauge (T : TowerData L n k) (hI : IterDerivChain L n k)
    (hU : U ∈ smallIterateFields L n k) (hu : u ∈ gaugeGroupAt L n k 0)
    (hW : PeriodicLattice.gaugeTransform u U ∈ smallIterateFields L n k)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k 0)
    (hB' : adjointForm u B ∈ complexEdgeForms L n k 0) :
    ∀ i ≤ k, iterContourLogDrift L n k (PeriodicLattice.gaugeTransform u U) i (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction i u) (iterContourLogDrift L n k U i B) := by
  intro i
  induction i with
  | zero =>
    intro _
    funext x
    exact (conjugateBy_zero _).symm
  | succ i ih =>
    intro h
    have hi : i < k := h
    show adjointCubeAverage
          (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U))
          (iterContourLogDrift L n k (PeriodicLattice.gaugeTransform u U) i (adjointForm u B)) +
        contourLogDrift
          (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U))
          (complexIterDeriv L n k i (PeriodicLattice.gaugeTransform u U) (adjointForm u B)) =
      adjointVertexFn (restrictVertexFunction (i + 1) u)
        (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterContourLogDrift L n k U i B) +
          contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel i U)
            (complexIterDeriv L n k i U B))
    rw [ih hi.le, complexIterDeriv_gauge T hI hU hu hW hB hB' i hi.le,
      complexBlockField_gauge T hU hu i hi.le,
      adjointCubeAverage_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i),
      contourLogDrift_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i)
        ((hI U hU B hB).2.2 i hi.le), restrictVertexFunction_succ T.positive, adjointVertexFn_add]
end Levels
theorem averagesGaugeCovariant_proof (hA : SmoothingNearIdentity)
    (hG : GaugeEquivarianceFormsAllSides)
    (hP : MeanStableFields.MeanStableFieldsHold)
    (hC : LeftChartFields.Claim)
    (hI : ComplexIterDerivChain)
    (hR : CovariantIterRelations)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy) : AveragesGaugeCovariant := by
  intro L hL n k j hn hj U hU u hu hW
  have T : TowerData L n k :=
    { positive := by have := hL.2; omega
      orientation := fun i hi b => by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · obtain rfl : i = 0 := by omega
          exact hO L n 1 hL hn one_pos 1 le_rfl b
        · exact hO L n k hL hn hk i hi b
      admissible := fun i hi c hc => (hA.1 L hL).2.2.periodic n k i hn hi c hc
      inPolydisc := fun i hi c hc V hV =>
        ((hP L hL k (by omega)).1 n hn).mem_polydisc i hi c hc V hV
      isOpen_nearOne := fun i hi => ((hP L hL k (by omega)).1 n hn).isOpen_nearOne i hi
      gauge := fun i hi => (hG L k i hL hi).1 n hn
      left := fun i hi V hV B hB b hb =>
        ((hC.2.2 L k i hL hi).1 n hn).1.1.2 V hV B hB ⟨b, hb⟩ }
  have hI' : IterDerivChain L n k := fun W hW' B hB => hI L hL n k hn W hW' B hB
  have hd : ∀ x, (u x).det = 1 := det_of_mem_gaugeGroupAt hu
  refine ⟨fun l _ => ⟨covDiff_gauge T (Nat.zero_le k) hd U l,
    iterAdjointCubeAverage_gauge T hU hu l j hj⟩, fun B hB => ?_⟩
  have hB' := adjointForm_mem T (Nat.zero_le k) hd hB
  have hq := complexIterDeriv_gauge T hI' hU hu hW hB hB' j hj
  have hn' := iterContourLogDrift_gauge T hI' hU hu hW hB hB' j hj
  refine ⟨hq, ?_, hn'⟩
  rw [(hR L hL n k j hn hj _ hW).1 _ hB', (hR L hL n k j hn hj U hU).1 B hB, hq, hn',
    complexBlockField_gauge T hU hu j hj,
    covDiff_gauge T hj (det_of_mem_gaugeGroupAt (restrictVertexFunction_mem hu j)), adjointForm_add]
end YangMills.Construction.Tower.GaugeCovarianceProof
end
