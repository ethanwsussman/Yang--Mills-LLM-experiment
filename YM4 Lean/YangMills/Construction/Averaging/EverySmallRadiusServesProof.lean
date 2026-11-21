import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Lattice.HolonomyUnderReordering
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.Matrices.LogMeanCovarianceProof
import YangMills.Construction.Numerics.ExpLogNumericBounds
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Averaging.SmallRadiusProof
open YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices YangMills.Construction.Coordinates
theorem addCircle_coe_ne_zero_of_pos_of_lt {p t : ℝ} (hp : 0 < p) (h0 : 0 < t) (h1 : t < p) :
    (t : AddCircle p) ≠ 0 := by apply _root_.YangMills.SharedProofs.p5311 <;> assumption
theorem finite_site_of_floor {L m : ℕ} {j : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Finite (Site L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.site_finite <;> assumption
theorem finite_bond_of_floor {L m : ℕ} {j : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Finite (Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.bond_finite <;> assumption
theorem finite_plaquette_of_floor {L m : ℕ} {j : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Finite (Plaquette L m j) := by
  have := finite_site_of_floor (L := L) (m := m) (j := j) hL hj
  refine Finite.of_injective (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis)) ?_
  intro p p' hp
  have h1 := congrArg Prod.fst hp
  have h2 := congrArg (fun q => q.2.1) hp
  have h3 := congrArg (fun q => q.2.2) hp
  exact Plaquette.ext h1 h2 h3
theorem isPositivelyOriented_or_opposite {L m : ℕ} {j : ℤ} (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem not_opposite_isPositivelyOriented {L m : ℕ} {j : ℤ} (hL : 13 ≤ L) (hm : 0 < m)
    (hj : 0 ≤ j) (b : Bond L m j) (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  change b.source - b.target = _ at hν
  have hsum : unitStep L m j μ + unitStep L m j ν = 0 := by
    rw [← hμ, ← hν]; abel
  have hcoord : ((unitStep L m j μ + unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := by
    rw [hsum]; rfl
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hs0 : 0 < meshSize L j := by unfold meshSize; positivity
  have hs1 : meshSize L j ≤ 1 := by
    unfold meshSize
    exact zpow_le_one_of_nonpos₀ hL1 (by omega)
  have hside : (26 : ℝ) ≤ torusSide L m := by
    unfold torusSide
    have : (L : ℝ) ≤ (L : ℝ) ^ m := by
      calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℝ) ^ m := pow_le_pow_right₀ hL1 hm
    linarith
  have hp : 0 < torusSide L m := by linarith
  have hcoord' : (pointOnAxis L m μ (meshSize L j) + pointOnAxis L m ν (meshSize L j)) μ = 0 :=
    hcoord
  by_cases h : ν = μ
  · subst h
    simp only [pointOnAxis, Pi.add_apply, Pi.single_eq_same] at hcoord'
    rw [← AddCircle.coe_add] at hcoord'
    exact addCircle_coe_ne_zero_of_pos_of_lt hp (by linarith) (by linarith) hcoord'
  · simp only [pointOnAxis, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h),
      add_zero] at hcoord'
    exact addCircle_coe_ne_zero_of_pos_of_lt hp hs0 (by linarith) hcoord'
theorem inv_eq_star_of_mem_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : X⁻¹ = star X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem continuous_fieldValue_of_positive {L m : ℕ} {j : ℤ} {X : Type*} [TopologicalSpace X]
    (f : X → Bond L m j → ComplexMatrix2) (hr : ∀ x, f x ∈ compactGaugeFields L m j)
    (hpos : ∀ b : Bond L m j, b.IsPositivelyOriented → Continuous fun x => f x b)
    (b : Bond L m j) : Continuous fun x => f x b := by
  rcases isPositivelyOriented_or_opposite b with h | h
  · exact hpos b h
  · have e : (fun x => f x b) = fun x => star (f x b.opposite) := by
      funext x
      have h1 : f x b.opposite.opposite = (f x b.opposite)⁻¹ := (hr x).2 _ (mem_univ _)
      have h2 : b.opposite.opposite = b := rfl
      rw [h2] at h1
      rw [h1, inv_eq_star_of_mem_specialUnitary ((hr x).1 _ (mem_univ _))]
    rw [e]
    exact continuous_star.comp (hpos _ h)
theorem continuous_pathHolonomy_of_continuous {L m : ℕ} {j : ℤ} {X : Type*} [TopologicalSpace X]
    (f : X → Bond L m j → ComplexMatrix2) (hf : ∀ b, Continuous fun x => f x b)
    (Γ : List (Bond L m j)) : Continuous fun x => pathHolonomy (f x) Γ := by
  induction Γ with
  | nil => simpa [pathHolonomy] using continuous_const
  | cons b Γ ih =>
    have e : (fun x => pathHolonomy (f x) (b :: Γ)) = fun x => f x b * pathHolonomy (f x) Γ := by
      funext x; simp [pathHolonomy]
    rw [e]
    exact (hf b).mul ih
theorem isOpen_plaquetteHolonomy_near {L m : ℕ} {j : ℤ} {X : Type*} [TopologicalSpace X]
    [Finite (Plaquette L m j)] (f : X → Bond L m j → ComplexMatrix2)
    (hf : ∀ b, Continuous fun x => f x b) (P : Set (Plaquette L m j)) (ω : ℝ) :
    IsOpen {x | ∀ p ∈ P, ComplexMatrix2.operatorNorm (plaquetteHolonomy (f x) p - 1) < ω} := by
  have e : {x | ∀ p ∈ P, ComplexMatrix2.operatorNorm (plaquetteHolonomy (f x) p - 1) < ω} =
      ⋂ p ∈ P, {x | ComplexMatrix2.operatorNorm (plaquetteHolonomy (f x) p - 1) < ω} := by
    ext x; simp
  rw [e]
  refine (Set.toFinite P).isOpen_biInter fun p _ => ?_
  have hc : Continuous fun x => ComplexMatrix2.operatorNorm (plaquetteHolonomy (f x) p - 1) :=
    ((continuous_pathHolonomy_of_continuous f hf p.boundaryBonds).sub continuous_const).norm
  exact isOpen_lt hc continuous_const
theorem continuous_comp_of_induced {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : X → Y) (h : Y → Z) (hh : Continuous h) :
    @Continuous X Z (TopologicalSpace.induced g inferInstance) _ (h ∘ g) := by
  let _ : TopologicalSpace X := TopologicalSpace.induced g inferInstance
  exact hh.comp continuous_induced_dom
theorem isOpen_smallPlaquetteFields_at {L m K k : ℕ} (hL : 0 < L) (hk : k < K) (ω : ℝ)
    (c : BondAtLevel L m K (k + 1)) :
    IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))) := by
  have hfin : Finite (Plaquette L m (levelDepth K k)) :=
    finite_plaquette_of_floor hL (by simp only [levelDepth]; omega)
  have hpos : ∀ b : BondAtLevel L m K k, b.IsPositivelyOriented →
      @Continuous (gaugeFieldsAtLevel L m K k) ComplexMatrix2 (gaugeFieldsAtLevelTopology L m K k) _
        (fun x => x.1 b) := by
    intro b hb
    exact continuous_comp_of_induced
      (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := k))
      (fun v => ((v ⟨b, hb⟩ : ComplexMatrix2.specialUnitary) : ComplexMatrix2))
      (continuous_subtype_val.comp (continuous_apply _))
  have hall := @continuous_fieldValue_of_positive L m (levelDepth K k) (gaugeFieldsAtLevel L m K k)
    (gaugeFieldsAtLevelTopology L m K k) Subtype.val (fun x => x.2) hpos
  have key := @isOpen_plaquetteHolonomy_near L m (levelDepth K k) (gaugeFieldsAtLevel L m K k)
    (gaugeFieldsAtLevelTopology L m K k) hfin Subtype.val hall (doubleBlockPlaquettes c) ω
  convert key using 1
  ext U
  simp only [mem_preimage, smallPlaquetteFields, DoubleBlockPlaquettesNear, mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨U.2, h⟩⟩
section Bounds
variable {L m K k : ℕ}
theorem nonempty_axisOrdering {j j' : ℤ} (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(offsetAxes y x).equivFin.symm⟩
theorem isUnit_of_mem_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : IsUnit X := by apply _root_.YangMills.SharedProofs.p13429 <;> assumption
theorem pathHolonomy_mem_specialUnitary {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (Γ : List (Bond L m j)) :
    pathHolonomy U Γ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.pathHolonomy_mem_compactGaugeGroup <;> assumption
theorem unitBlock_subset_and_contours (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (c : BondAtLevel L m K (k + 1))
    {y : SiteAtLevel L m K (k + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))))
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) y) :
    unitBlock y ⊆ bondDoubleBlock c ∧ ∃ n, DoubleBlock.BlockSiteContours y x n := by
  obtain ⟨hb, h⟩ := (hC L m K hL.1 hL.2 hm k hk c).1 y (by simpa using hy)
  obtain ⟨⟨n, hn⟩, h2⟩ := h x hx
  exact ⟨hb, n, h2 n hn⟩
theorem extendByInverses_restrict_eq {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m (levelDepth K k)) (c : BondAtLevel L m K (k + 1))
    (b : BondAtLevel L m K k) (ht : (b.source : FourTorus L m) ∈ bondDoubleBlock c)
    (hh : (b.target : FourTorus L m) ∈ bondDoubleBlock c) :
    extendByInverses (positiveBondsInDoubleBlock c) (restrictToPositiveDoubleBlock c U) b = U b := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.extendByInverses_restrict <;> assumption
theorem configurationContourFamily_eq (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (c : BondAtLevel L m K (k + 1))
    {U : BondAtLevel L m K k → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m (levelDepth K k))
    {y : SiteAtLevel L m K (k + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))))
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) y)
    (i : Fin (Fintype.card (AxisOrdering y x))) :
    configurationContourFamily c U y x i =
      contourHolonomies U y x ((Fintype.equivFin (AxisOrdering y x)).symm i) := by
  obtain ⟨hb, n, hn⟩ := unitBlock_subset_and_contours hL hm hk hC c hy hx
  unfold configurationContourFamily contourHolonomyFamily holonomyInDoubleBlock contourHolonomies
    pathHolonomy
  congr 1
  apply List.map_congr_left
  intro b hbm
  obtain ⟨h1, h2⟩ := hn.2.2.2.2.2 _ ⟨_, rfl⟩ b hbm
  exact extendByInverses_restrict_eq hU c b (hb h1) (hb h2)
theorem triangular_le_of_le {n : ℕ} (h : n ≤ 2 * L) : n * (n - 1) / 2 ≤ 2 * L ^ 2 := by
  have h1 : n * (n - 1) ≤ (2 * L) * (2 * L) := Nat.mul_le_mul h (by omega)
  have h2 : (2 * L) * (2 * L) = 2 * (2 * L ^ 2) := by ring
  rw [h2] at h1
  exact Nat.div_le_of_le_mul h1
theorem holonomy_ratio_le_of_mem_contourSet (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hR : HolonomyReorderingBound) {ω : ℝ} (hω : 0 ≤ ω) (c : BondAtLevel L m K (k + 1))
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    {y : SiteAtLevel L m K (k + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))))
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) y)
    {Γ Γ' : List (BondAtLevel L m K k)} (hΓ : Γ ∈ contourSet y x)
    (hΓ' : Γ' ∈ contourSet y x) :
    ComplexMatrix2.operatorNorm (pathHolonomy U Γ' * (pathHolonomy U Γ)⁻¹ - 1) ≤
      (1 + ω) ^ (2 * L ^ 2) - 1 := by
  obtain ⟨hb, n, h1, h2, h3, h4, h5, -⟩ := unitBlock_subset_and_contours hL hm hk hC c hy hx
  obtain ⟨s, hs, hsΓ⟩ := h2 Γ hΓ
  obtain ⟨s', -, hsΓ'⟩ := h2 Γ' hΓ'
  have hre := h3 Γ hΓ Γ' hΓ' s s' hsΓ hsΓ'
  have hj : -(m : ℤ) ≤ levelDepth K k := by simp only [levelDepth]; omega
  have hsite := h4 Γ hΓ s hsΓ
  have key := hR L m hL.1 hL.2 hm (levelDepth K k) hj U hU.1 (y.toSublattice (levelDepth K k)) s s'
    ω hre hω (fun p hp => (hU.2 p fun q hq => hb (h5 q (hsite ▸ hp hq))).le)
  have hlen : (s.length : ℤ) ≤ 2 * ((L : ℤ) - 1) := by
    rw [hs]
    push_cast
    simpa using h1
  have hlen' : s.length ≤ 2 * L := by omega
  rw [← hsΓ, ← hsΓ']
  refine key.trans (sub_le_sub_right (pow_le_pow_right₀ (by linarith) ?_) 1)
  exact triangular_le_of_le hlen'
theorem radius_exp_chain (hN : Numerics.ExpLogNumericBounds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) :
    (1 + ω) ^ (2 * L ^ 2) - 1 ≤ Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ∧
    Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ≤ Real.exp (1 / 100) - 1 ∧
    Real.exp (1 / 100) - 1 ≤ 1 / 50 := by
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hω2 : 2 * (L : ℝ) ^ 2 * ω ≤ 1 / 100 := by
    have h := hω.2
    rw [averagingRadiusCap, le_div_iff₀ (by positivity)] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (1 + ω) ^ (2 * L ^ 2) ≤ Real.exp ω ^ (2 * L ^ 2) := by
      apply pow_le_pow_left₀ (by linarith [hω.1])
      linarith [Real.add_one_le_exp ω]
    have h2 : Real.exp ω ^ (2 * L ^ 2) = Real.exp (2 * (L : ℝ) ^ 2 * ω) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    linarith
  · linarith [Real.exp_le_exp.mpr hω2]
  · have := hN.1
    norm_num at this ⊢
    linarith
theorem holonomy_ratio_le_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1)) :
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ Γ ∈ contourSet y x, ∀ Γ' ∈ contourSet y x,
        ComplexMatrix2.operatorNorm (pathHolonomy U Γ' * (pathHolonomy U Γ)⁻¹ - 1) ≤
          (1 + ω) ^ (2 * L ^ 2) - 1 ∧
        (1 + ω) ^ (2 * L ^ 2) - 1 ≤ Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ∧
        Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ≤ Real.exp (1 / 100) - 1 ∧
        Real.exp (1 / 100) - 1 ≤ 1 / 50 := by
  intro U hU y hy x hx Γ hΓ Γ' hΓ'
  exact ⟨holonomy_ratio_le_of_mem_contourSet hL hm hk hC hR hω.1.le c hU hy hx hΓ hΓ',
    radius_exp_chain hN hL hω⟩
theorem familyDiameter_le_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1)) :
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x) ≤ 1 / 50 := by
  intro U hU y hy x hx
  have hpos : 0 < Fintype.card (AxisOrdering y x) :=
    Fintype.card_pos_iff.mpr (nonempty_axisOrdering y x)
  have : Nonempty (Fin (Fintype.card (AxisOrdering y x))) := ⟨⟨0, hpos⟩⟩
  unfold ComplexMatrix2.unitFamilyDiameter ComplexMatrix2.familyDiameter
  refine ciSup_le fun p => ?_
  rw [configurationContourFamily_eq hL hm hk hC c hU.1 hy hx p.1,
    configurationContourFamily_eq hL hm hk hC c hU.1 hy hx p.2]
  have h := holonomy_ratio_le_of_mem_contourSet hL hm hk hC hR hω.1.le c hU hy hx
    (Γ := orderedContour y x ((Fintype.equivFin (AxisOrdering y x)).symm p.2))
    (Γ' := orderedContour y x ((Fintype.equivFin (AxisOrdering y x)).symm p.1)) ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨h1, h2, h3⟩ := radius_exp_chain hN hL hω
  exact h.trans (by linarith)
theorem isLogMean_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (f : κ → ComplexMatrix2) (G : Set ComplexMatrix2) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean G (f ∘ e) W ↔ ComplexMatrix2.IsLogMean G f W := by
  unfold ComplexMatrix2.IsLogMean
  simp only [Function.comp]
  rw [e.forall_congr_left, e.sum_comp (fun i => ComplexMatrix2.logSeries (f i * W⁻¹))]
  simp
theorem logMean_eq_of_unique {ι : Type*} [Fintype ι] {G : Set ComplexMatrix2}
    {V : ι → ComplexMatrix2} {a : ComplexMatrix2}
    (h : ∀ W, ComplexMatrix2.IsLogMean G V W ↔ W = a) : ComplexMatrix2.logMean G V = a :=
  (h _).mp (Classical.epsilon_spec ⟨a, (h a).mpr rfl⟩)
theorem contourMean_spec_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) (hM : SmallDiameterMean.AverageStatement) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) (c : BondAtLevel L m K (k + 1)) :
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        HasContourMean U y x ∧
        meanContourHolonomy U y x =
          ComplexMatrix2.logMean compactGaugeGroup (configurationContourFamily c U y x) ∧
        meanContourHolonomy U y x =
          SmallDiameterMean.average (configurationContourFamily c U y x) ∧
        meanContourHolonomy U y x ∈ compactGaugeGroup ∧
        (∀ Γ ∈ contourSet y x,
          ComplexMatrix2.operatorNorm (pathHolonomy U Γ * (meanContourHolonomy U y x)⁻¹ - 1) ≤
            4 * ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x)) ∧
        4 * ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x) ≤ 2 / 25 := by
  intro U hU y hy x hx
  have hd := familyDiameter_le_at hL hm hk hC hR hN hω c U hU y hy x hx
  have hpos : 1 ≤ Fintype.card (AxisOrdering y x) :=
    Fintype.card_pos_iff.mpr (nonempty_axisOrdering y x)
  have hnum := configurationContourFamily_eq hL hm hk hC c hU.1 hy hx
  have hV : configurationContourFamily c U y x =
      contourHolonomies U y x ∘ (Fintype.equivFin (AxisOrdering y x)).symm := funext hnum
  generalize hVdef : configurationContourFamily c U y x = V at hd hV ⊢
  have hGi : ∀ i, V i ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    intro i
    rw [hV]
    exact pathHolonomy_mem_specialUnitary hU.1 _
  have hfam : ComplexMatrix2.IsSpecialUnitaryFamily V := ⟨hpos, hGi⟩
  have hinv : ComplexMatrix2.IsUnitFamily V :=
    ⟨hpos, fun i => isUnit_of_mem_specialUnitary (hGi i)⟩
  have hd40 : ComplexMatrix2.unitFamilyDiameter V ≤ 1 / 40 := by linarith
  have hmean := (hM.2.2.2 _ V hfam hd40).1
  have hA := hM.1 _ V hinv hd40
  have hMeanV : ∀ W, ComplexMatrix2.IsLogMean compactGaugeGroup V W ↔
      W = SmallDiameterMean.average V := fun W =>
    ⟨fun h => (hmean W).mp ⟨hfam, h⟩, fun h => ((hmean W).mpr h).2⟩
  have hMeanC : ∀ W, ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies U y x) W ↔
      W = SmallDiameterMean.average V := by
    intro W
    rw [← hMeanV W, hV, isLogMean_comp_equiv]
  have hav : meanContourHolonomy U y x = SmallDiameterMean.average V := logMean_eq_of_unique hMeanC
  refine ⟨⟨_, (hMeanC _).mpr rfl, fun W hW => (hMeanC W).mp hW⟩, ?_, hav, ?_, ?_, by linarith⟩
  · rw [hav, logMean_eq_of_unique hMeanV]
  · rw [hav]
    exact ((hMeanV _).mpr rfl).1
  · rintro Γ ⟨σ, rfl⟩
    have h7 := hA.2.2.2.2.2.2.1 (Fintype.equivFin (AxisOrdering y x) σ)
    rw [hV] at h7 ⊢
    rw [hav, hV]
    simpa [contourHolonomies] using h7
theorem image_restrict_subset_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1)) :
    restrictToPositiveDoubleBlock c ''
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) ⊆
    invertibleContourSet (j' := levelDepth K k) c := by
  rintro _ ⟨U, hU, rfl⟩
  have hd := familyDiameter_le_at hL hm hk hC hR hN hω c U hU
  refine ⟨fun b => isUnit_of_mem_specialUnitary (hU.1.1 _ (mem_univ _)), fun x hx => ?_,
    fun x hx => ?_⟩
  · exact (hd _ (by simp) x hx).trans_lt (by norm_num)
  · exact (hd _ (by simp) x hx).trans_lt (by norm_num)
theorem contourVariable_extends_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) (hM : SmallDiameterMean.AverageStatement) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) (c : BondAtLevel L m K (k + 1)) :
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        meanContourHolonomy U y x = contourVariable c (restrictToPositiveDoubleBlock c U) y x ∧
        (meanContourHolonomy U y x)⁻¹ =
          contourVariableInverse c (restrictToPositiveDoubleBlock c U) y x := by
  intro U hU y hy x hx
  have h := (contourMean_spec_at hL hm hk hC hR hN hM hω c U hU y hy x hx).2.2.1
  exact ⟨h, by rw [h]; rfl⟩
end Bounds
section Analytic
theorem isHolomorphicIn_of_differentiableAt {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : ∀ a ∈ O, DifferentiableAt ℂ f a) : ComplexCoordinates.IsHolomorphicIn O f := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.isHolomorphicIn_of_differentiableAt <;> assumption
def familyContinuousEquiv (n : ℕ) : (Fin n → ComplexMatrix2) ≃L[ℂ]
    ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { SmallDiameterMean.familyEquiv n with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem differentiableAt_nonsingInv {X : ComplexMatrix2} (hX : IsUnit X) :
    DifferentiableAt ℂ (fun X : ComplexMatrix2 => X⁻¹) X := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.differentiableAt_inv_of_isUnit <;> assumption
theorem isUnit_nonsingInv {X : ComplexMatrix2} (hX : IsUnit X) : IsUnit X⁻¹ := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.isUnit_inv_of_isUnit <;> assumption
theorem nonsingInv_mem_complexGaugeGroup {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
variable {L m : ℕ} {j j' : ℤ}
theorem differentiableAt_extendByInverses {n : ℕ} (P : Set (Bond L m j')) (ν : P → Fin n)
    (X : Fin n → ComplexMatrix2) (hX : ∀ i, IsUnit (X i)) (b : Bond L m j') :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => extendByInverses P (fun p => X (ν p)) b) X := by
  unfold extendByInverses
  by_cases h : b ∈ P
  · simp only [dif_pos h]
    exact differentiableAt_apply _ _
  · by_cases h' : b.opposite ∈ P
    · simp only [dif_neg h, dif_pos h']
      exact DifferentiableAt.comp (𝕜 := ℂ) X (differentiableAt_nonsingInv (hX _))
        (differentiableAt_apply _ _)
    · simp only [dif_neg h, dif_neg h']
      exact differentiableAt_const _
theorem differentiableAt_pathHolonomy_extendByInverses {n : ℕ} (P : Set (Bond L m j'))
    (ν : P → Fin n) (X : Fin n → ComplexMatrix2) (hX : ∀ i, IsUnit (X i))
    (Γ : List (Bond L m j')) :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => pathHolonomy (extendByInverses P fun p => X (ν p)) Γ)
      X := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact (differentiableAt_extendByInverses P ν X hX b).mul ih
theorem isUnit_extendByInverses (P : Set (Bond L m j')) (V : P → ComplexMatrix2)
    (hV : ∀ p, IsUnit (V p)) (b : Bond L m j') : IsUnit (extendByInverses P V b) := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.isUnit_extendByInverses <;> assumption
theorem extendByInverses_mem_complexGaugeGroup (P : Set (Bond L m j')) (V : P → ComplexMatrix2)
    (hV : ∀ p, V p ∈ complexGaugeGroup) (b : Bond L m j') :
    extendByInverses P V b ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.extendByInverses_mem_complexGaugeGroup <;> assumption
theorem isUnit_pathHolonomy_of_isUnit (U : Bond L m j' → ComplexMatrix2) (hU : ∀ b, IsUnit (U b))
    (Γ : List (Bond L m j')) : IsUnit (pathHolonomy U Γ) := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.isUnit_pathHolonomy <;> assumption
theorem pathHolonomy_mem_complexGaugeGroup (U : Bond L m j' → ComplexMatrix2)
    (hU : ∀ b, U b ∈ complexGaugeGroup) (Γ : List (Bond L m j')) :
    pathHolonomy U Γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem isUnit_contourHolonomyFamily (c : Bond L m j)
    {V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2} (hV : ∀ p, IsUnit (V p))
    (y : Site L m j) (x : Site L m j') (i) : IsUnit (contourHolonomyFamily c V y x i) :=
  isUnit_pathHolonomy_of_isUnit _ (isUnit_extendByInverses _ V hV) _
theorem contourHolonomyFamily_mem_complexGaugeGroup (c : Bond L m j)
    {V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2}
    (hV : ∀ p, V p ∈ complexGaugeGroup) (y : Site L m j) (x : Site L m j') (i) :
    contourHolonomyFamily c V y x i ∈ complexGaugeGroup :=
  pathHolonomy_mem_complexGaugeGroup _ (extendByInverses_mem_complexGaugeGroup _ V hV) _
theorem one_le_card_axisOrdering (y : Site L m j) (x : Site L m j') :
    1 ≤ Fintype.card (AxisOrdering y x) :=
  Fintype.card_pos_iff.mpr ⟨(offsetAxes y x).equivFin.symm⟩
theorem differentiableAt_contourHolonomyFamily (c : Bond L m j) {n : ℕ}
    (ν : positiveBondsInDoubleBlock (j' := j') c → Fin n) (X : Fin n → ComplexMatrix2)
    (hX : ∀ i, IsUnit (X i)) (y : Site L m j) (x : Site L m j') :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => contourHolonomyFamily c (fun p => X (ν p)) y x) X := by
  rw [differentiableAt_pi]
  intro i
  exact differentiableAt_pathHolonomy_extendByInverses _ ν X hX _
def unitValuedFields (c : Bond L m j) :
    Set (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) :=
  {V | ∀ p, IsUnit (V p)}
theorem isOpen_unitValuedFields [Finite (Bond L m j')] (c : Bond L m j) :
    IsOpen (unitValuedFields (j' := j') c) := by
  have h : unitValuedFields (j' := j') c =
      ⋂ p, (fun V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2 => V p) ⁻¹'
        {X : ComplexMatrix2 | IsUnit X} := by
    ext V
    simp [unitValuedFields]
  rw [h]
  exact isOpen_iInter_of_finite fun p => Units.isOpen.preimage (continuous_apply p)
theorem continuousOn_contourHolonomyFamily [Finite (Bond L m j')] (c : Bond L m j)
    (y : Site L m j) (x : Site L m j') :
    ContinuousOn (fun V => contourHolonomyFamily c V y x)
      (unitValuedFields (j' := j') c) := by
  intro V hV
  apply ContinuousAt.continuousWithinAt
  obtain ⟨n, ⟨ν⟩⟩ := Finite.exists_equiv_fin (positiveBondsInDoubleBlock (j' := j') c)
  have hd := differentiableAt_contourHolonomyFamily c ν (V ∘ ν.symm)
    (fun i => hV _) y x
  have hc : Continuous fun V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2 =>
      V ∘ ν.symm :=
    continuous_pi fun i => continuous_apply _
  have := ContinuousAt.comp (f := fun V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2 =>
    V ∘ ν.symm) (x := V) hd.continuousAt hc.continuousAt
  simpa [Function.comp_def, Equiv.symm_apply_apply] using this
theorem isOpen_invertibleContourSet_of_finite [Finite (Bond L m j')] [Finite (Site L m j')]
    (hM : SmallDiameterMean.AverageStatement) (c : Bond L m j) :
    IsOpen (invertibleContourSet (j' := j') c) := by
  have hU := isOpen_unitValuedFields (j' := j') c
  have key : ∀ (y : Site L m j) (x : Site L m j'), IsOpen
      (unitValuedFields (j' := j') c ∩ (fun V => contourHolonomyFamily c V y x) ⁻¹'
        SmallDiameterMean.narrowFamilies _) := fun y x =>
    (continuousOn_contourHolonomyFamily c y x).isOpen_inter_preimage hU
      (hM.2.2.1 _ (one_le_card_axisOrdering y x)).1
  have h : invertibleContourSet (j' := j') c = unitValuedFields (j' := j') c ∩
      ((⋂ x ∈ sitesInBlock j' c.source, unitValuedFields (j' := j') c ∩
          (fun V => contourHolonomyFamily c V c.source x) ⁻¹'
            SmallDiameterMean.narrowFamilies _) ∩
       (⋂ x ∈ sitesInBlock j' c.target, unitValuedFields (j' := j') c ∩
          (fun V => contourHolonomyFamily c V c.target x) ⁻¹'
            SmallDiameterMean.narrowFamilies _)) := by
    ext V
    simp only [invertibleContourSet, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage,
      SmallDiameterMean.narrowFamilies]
    constructor
    · rintro ⟨hV, h₁, h₂⟩
      exact ⟨hV, fun x hx => ⟨hV, isUnit_contourHolonomyFamily c hV _ x, h₁ x hx⟩,
        fun x hx => ⟨hV, isUnit_contourHolonomyFamily c hV _ x, h₂ x hx⟩⟩
    · rintro ⟨hV, h₁, h₂⟩
      exact ⟨hV, fun x hx => (h₁ x hx).2.2, fun x hx => (h₂ x hx).2.2⟩
  rw [h]
  exact hU.inter (((Set.toFinite _).isOpen_biInter fun x _ => key _ x).inter
    ((Set.toFinite _).isOpen_biInter fun x _ => key _ x))
section Coordinates
theorem doubleBlockEquiv_symm_apply (c : Bond L m j) {n : ℕ}
    (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n) (z) :
    (SmallRadius.doubleBlockEquiv c ν).symm z =
      fun p => (SmallDiameterMean.familyEquiv n).symm z (ν p) := rfl
theorem continuous_doubleBlockEquiv_symm (c : Bond L m j) {n : ℕ}
    (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n) :
    Continuous (SmallRadius.doubleBlockEquiv c ν).symm := by
  refine continuous_pi fun p => ?_
  simp only [doubleBlockEquiv_symm_apply]
  exact (continuous_apply (ν p)).comp (familyContinuousEquiv n).symm.continuous
theorem isOpen_image_doubleBlockEquiv (c : Bond L m j) {n : ℕ}
    (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n)
    {O : Set (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)} (hO : IsOpen O) :
    IsOpen (SmallRadius.doubleBlockEquiv c ν '' O) := by
  rw [Equiv.image_eq_preimage_symm]
  exact hO.preimage (continuous_doubleBlockEquiv_symm c ν)
theorem differentiableAt_contourHolonomyFamily_coords (c : Bond L m j) {n : ℕ}
    (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n) (y : Site L m j) (x : Site L m j') (z)
    (hz : (SmallRadius.doubleBlockEquiv c ν).symm z ∈ unitValuedFields (j' := j') c) :
    DifferentiableAt ℂ (fun z => SmallDiameterMean.familyEquiv _
      (contourHolonomyFamily c ((SmallRadius.doubleBlockEquiv c ν).symm z) y x)) z := by
  have hX : ∀ i, IsUnit ((SmallDiameterMean.familyEquiv n).symm z i) := fun i => by
    have := hz (ν.symm i)
    simpa [doubleBlockEquiv_symm_apply] using this
  have h₁ : DifferentiableAt ℂ (familyContinuousEquiv n).symm z :=
    (familyContinuousEquiv n).symm.differentiableAt
  have h₂ := differentiableAt_contourHolonomyFamily c (fun p => ν p)
    ((familyContinuousEquiv n).symm z) hX y x
  have h₃ := DifferentiableAt.comp (𝕜 := ℂ) z h₂ h₁
  exact DifferentiableAt.comp (𝕜 := ℂ) z
    (familyContinuousEquiv _).differentiableAt h₃
theorem isHolomorphicVia_contourVariables (hM : SmallDiameterMean.AverageStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (c : Bond L m j) (hO : IsOpen (invertibleContourSet (j' := j') c))
    (y : Site L m j) (x : Site L m j')
    (hdom : ∀ V ∈ invertibleContourSet (j' := j') c,
      contourHolonomyFamily c V y x ∈ SmallDiameterMean.narrowFamilies _)
    {n : ℕ} (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n) :
    ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := j') c)
        (fun V => contourVariable c V y x) ∧
      ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := j') c)
        (fun V => contourVariableInverse c V y x) := by
  set e := SmallRadius.doubleBlockEquiv c ν with he
  have hopen : IsOpen (e '' invertibleContourSet (j' := j') c) :=
    isOpen_image_doubleBlockEquiv c ν hO
  have hinv : ∀ z ∈ e '' invertibleContourSet (j' := j') c,
      e.symm z ∈ invertibleContourSet (j' := j') c := by
    rintro z ⟨V, hV, rfl⟩
    simpa using hV
  have hg : ComplexCoordinates.IsHolomorphicIn (e '' invertibleContourSet (j' := j') c)
      (fun z => SmallDiameterMean.familyEquiv _ (contourHolonomyFamily c (e.symm z) y x)) :=
    isHolomorphicIn_of_differentiableAt hopen fun z hz =>
      differentiableAt_contourHolonomyFamily_coords c ν y x z (hinv z hz).1
  have hA := (hM.2.2.1 _ (one_le_card_axisOrdering y x)).2.2
  have hAopen : IsOpen ((SmallDiameterMean.familyEquiv _) '' SmallDiameterMean.narrowFamilies
      (Fintype.card (AxisOrdering y x))) := hA.1
  have hmean := ((hP.1 _ _ hAopen).1 _ _ hA).2.2.2.1 _ _ _ hg (by
    intro z hz
    exact ⟨_, hdom _ (hinv z hz), rfl⟩)
  have hfirst : ComplexCoordinates.IsHolomorphicVia e ComplexCoordinates.matrixEquiv
      (invertibleContourSet (j' := j') c) (fun V => contourVariable c V y x) := by
    have : (ComplexCoordinates.matrixEquiv ∘ (fun V => contourVariable c V y x) ∘
        e.symm) = ((ComplexCoordinates.matrixEquiv ∘ SmallDiameterMean.average ∘
          (SmallDiameterMean.familyEquiv _).symm) ∘
        fun z => SmallDiameterMean.familyEquiv _ (contourHolonomyFamily c (e.symm z) y x)) := by
      funext z
      simp [contourVariable]
    unfold ComplexCoordinates.IsHolomorphicVia
    rw [this]
    exact hmean
  refine ⟨hfirst, ?_⟩
  have hI := hP.2.2.2.1
  have hIopen : IsOpen (ComplexCoordinates.matrixEquiv '' {X : ComplexMatrix2 | IsUnit X}) := hI.1
  have hback := ((hP.1 _ _ hIopen).1 _ _ hI).2.2.2.1 _ _ _ hfirst (by
    intro z hz
    refine ⟨_, ?_, rfl⟩
    have hs := hdom _ (hinv z hz)
    exact ((hM.1 _ _ ⟨one_le_card_axisOrdering y x, hs.1⟩ hs.2.le).2.2.2.2.2.1))
  have : (ComplexCoordinates.matrixEquiv ∘ (fun V => contourVariableInverse c V y x) ∘
      e.symm) = ((ComplexCoordinates.matrixEquiv ∘ (fun X : ComplexMatrix2 => X⁻¹) ∘
        ComplexCoordinates.matrixEquiv.symm) ∘
      (ComplexCoordinates.matrixEquiv ∘ (fun V => contourVariable c V y x) ∘
        e.symm)) := by
    funext z
    simp [contourVariableInverse]
  unfold ComplexCoordinates.IsHolomorphicVia
  rw [this]
  exact hback
end Coordinates
theorem contourHolonomyFamily_mem_narrowFamilies (c : Bond L m j)
    {V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2}
    (hV : V ∈ invertibleContourSet (j' := j') c) {y : Site L m j}
    (hy : y ∈ ({c.source, c.target} : Set (Site L m j))) {x : Site L m j'}
    (hx : x ∈ sitesInBlock j' y) :
    contourHolonomyFamily c V y x ∈ SmallDiameterMean.narrowFamilies _ := by
  refine ⟨isUnit_contourHolonomyFamily c hV.1 y x, ?_⟩
  rcases hy with rfl | hy
  · exact hV.2.1 x hx
  · rw [mem_singleton_iff] at hy
    subst hy
    exact hV.2.2 x hx
variable {K k : ℕ}
theorem neg_le_levelDepth (hk : k < K) : -(m : ℤ) ≤ levelDepth K k := by
  have : (k : ℤ) < K := by exact_mod_cast hk
  simp only [levelDepth]
  omega
theorem isOpen_invertibleContourSet_at (hL : 0 < L) (hk : k < K)
    (hM : SmallDiameterMean.AverageStatement) (c : BondAtLevel L m K (k + 1)) :
    IsOpen (invertibleContourSet (j' := levelDepth K k) c) := by
  have := finite_bond_of_floor (m := m) hL (neg_le_levelDepth hk)
  have := finite_site_of_floor (m := m) hL (neg_le_levelDepth hk)
  exact isOpen_invertibleContourSet_of_finite hM c
theorem holomorphic_contourVariable_at (hL : 0 < L) (hk : k < K)
    (hM : SmallDiameterMean.AverageStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (c : BondAtLevel L m K (k + 1)) :
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ (n : ℕ)
      (ν : positiveBondsInDoubleBlock (j' := levelDepth K k) c ≃ Fin n),
      ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
        (fun V => contourVariable c V y x) ∧
      ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
        (fun V => contourVariableInverse c V y x) := fun y hy x hx _ ν =>
  isHolomorphicVia_contourVariables hM hP c (isOpen_invertibleContourSet_at hL hk hM c) y x
    (fun _ hV => contourHolonomyFamily_mem_narrowFamilies c hV hy hx) ν
theorem contourVariable_values_at (hM : SmallDiameterMean.AverageStatement)
    (c : BondAtLevel L m K (k + 1)) :
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ V ∈ invertibleContourSet (j' := levelDepth K k) c,
      IsUnit (contourVariable c V y x) ∧
      IsUnit (contourVariableInverse c V y x) ∧
      ((∀ b, V b ∈ complexGaugeGroup) →
        contourVariable c V y x ∈ complexGaugeGroup ∧
        contourVariableInverse c V y x ∈ complexGaugeGroup) := by
  intro y hy x hx V hV
  have hs := contourHolonomyFamily_mem_narrowFamilies c hV hy hx
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, h12, -, -⟩ :=
    hM.1 _ _ ⟨one_le_card_axisOrdering y x, hs.1⟩ hs.2.le
  refine ⟨h6, isUnit_nonsingInv h6, fun hc => ?_⟩
  have h := (h12 (contourHolonomyFamily_mem_complexGaugeGroup c hc y x)).2
  exact ⟨h, nonsingInv_mem_complexGaugeGroup h⟩
end Analytic
section RealAnalytic
theorem inv_mem_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    X⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
theorem inv_inv_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_inv_of_mem_specialUnitary <;> assumption
theorem isRealAnalyticBetween_congr {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ι → ComplexMatrix2.FactorKind} {t : κ → ComplexMatrix2.FactorKind}
    {D : Set (ι → ComplexMatrix2)} {f g : (ι → ComplexMatrix2) → κ → ComplexMatrix2}
    (h : ComplexMatrix2.IsRealAnalyticBetween s t D f) (hfg : ∀ v ∈ D, g v = f v) :
    ComplexMatrix2.IsRealAnalyticBetween s t D g := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.isRealAnalyticBetween_congr <;> assumption
def familyReindex {ι ι' : Type} (a : ι ≃ ι') : (ι → ComplexMatrix2) →L[ℂ] (ι' → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a.symm i)
theorem familyReindex_mem_complexifiedProduct {ι ι' : Type} (a : ι ≃ ι')
    (v : ι → ComplexMatrix2) :
    familyReindex a v ∈
        ComplexMatrix2.complexifiedProduct (fun _ : ι' => ComplexMatrix2.FactorKind.group) ↔
      v ∈ ComplexMatrix2.complexifiedProduct (fun _ : ι => ComplexMatrix2.FactorKind.group) := by
  constructor
  · intro h i
    simpa [familyReindex] using h (a i)
  · intro h i
    exact h _
theorem familyReindex_mem_compactProduct {ι ι' : Type} (a : ι ≃ ι') (v : ι → ComplexMatrix2) :
    familyReindex a v ∈
        ComplexMatrix2.compactProduct (fun _ : ι' => ComplexMatrix2.FactorKind.group) ↔
      v ∈ ComplexMatrix2.compactProduct (fun _ : ι => ComplexMatrix2.FactorKind.group) := by
  constructor
  · intro h i
    simpa [familyReindex] using h (a i)
  · intro h i
    exact h _
theorem isHolomorphicBetween_reindex {ι ι' κ κ' : Type} [Fintype ι] [Fintype ι'] [Fintype κ]
    [Fintype κ'] (a : ι ≃ ι') (b : κ ≃ κ') {W : Set (ι' → ComplexMatrix2)}
    {h : (ι' → ComplexMatrix2) → κ' → ComplexMatrix2}
    (hh : ComplexMatrix2.IsHolomorphicBetween (fun _ : ι' => ComplexMatrix2.FactorKind.group)
      (fun _ : κ' => ComplexMatrix2.FactorKind.group) W h) :
    ComplexMatrix2.IsHolomorphicBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : κ => ComplexMatrix2.FactorKind.group)
      (familyReindex a ⁻¹' W) (fun v i => h (familyReindex a v) (b i)) := by
  obtain ⟨⟨O, hO, hW⟩, hmaps, hloc⟩ := hh
  refine ⟨⟨familyReindex a ⁻¹' O, hO.preimage (familyReindex a).continuous, ?_⟩, ?_, ?_⟩
  · rw [hW]
    ext v
    simp only [mem_preimage, mem_inter_iff, familyReindex_mem_complexifiedProduct]
  · intro v hv i
    exact hmaps hv (b i)
  · intro x hx
    obtain ⟨F, hF, hev⟩ := hloc _ hx
    refine ⟨fun v i => F (familyReindex a v) (b i), ?_, ?_⟩
    · have h₁ : AnalyticAt ℂ (fun v => F (familyReindex a v)) x :=
        AnalyticAt.fun_comp hF ((familyReindex a).analyticAt x)
      have h₂ : AnalyticAt ℂ (familyReindex b.symm) (F (familyReindex a x)) :=
        (familyReindex b.symm).analyticAt _
      exact AnalyticAt.fun_comp (f := fun v => F (familyReindex a v)) h₂ h₁
    · have ht : Filter.Tendsto (familyReindex a) (𝓝[familyReindex a ⁻¹' W] x)
          (𝓝[W] (familyReindex a x)) :=
        (familyReindex a).continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
      filter_upwards [ht.eventually hev] with y hy
      funext i
      rw [hy]
theorem isRelativelyOpen_compactProduct_reindex {ι ι' : Type} (a : ι ≃ ι')
    {D : Set (ι' → ComplexMatrix2)}
    (hD : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : ι' => ComplexMatrix2.FactorKind.group) D) :
    ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : ι => ComplexMatrix2.FactorKind.group)
      (familyReindex a ⁻¹' D) := by
  obtain ⟨O, hO, rfl⟩ := hD
  refine ⟨familyReindex a ⁻¹' O, hO.preimage (familyReindex a).continuous, ?_⟩
  ext v
  simp only [mem_preimage, mem_inter_iff, familyReindex_mem_compactProduct]
theorem isRealAnalyticBetween_reindex {ι ι' κ κ' : Type} [Fintype ι] [Fintype ι'] [Fintype κ]
    [Fintype κ'] (a : ι ≃ ι') (b : κ ≃ κ') {D : Set (ι' → ComplexMatrix2)}
    {f : (ι' → ComplexMatrix2) → κ' → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι' => ComplexMatrix2.FactorKind.group)
      (fun _ : κ' => ComplexMatrix2.FactorKind.group) D f) :
    ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : κ => ComplexMatrix2.FactorKind.group)
      (familyReindex a ⁻¹' D) (fun v i => f (familyReindex a v) (b i)) := by
  refine ⟨isRelativelyOpen_compactProduct_reindex a hf.1, fun x hx => ?_⟩
  obtain ⟨W, h, hxW, hh, hev⟩ := hf.2 _ hx
  refine ⟨familyReindex a ⁻¹' W, fun v i => h (familyReindex a v) (b i), hxW,
    isHolomorphicBetween_reindex a b hh, ?_⟩
  have ht : Filter.Tendsto (familyReindex a) (𝓝[familyReindex a ⁻¹' D] x) (𝓝[D] _) :=
    (familyReindex a).continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
  filter_upwards [ht.eventually hev] with y hy
  funext i
  rw [hy]
def matrixPowerLinearEquiv (n : ℕ) : (Fin n → ComplexMatrix2) ≃ₗ[ℂ]
    ComplexCoordinates (ComplexCoordinates.productDim fun _ : Fin n =>
      ComplexCoordinates.Component.matrix) :=
  { ComplexCoordinates.productEquiv fun _ : Fin n => ComplexCoordinates.Component.matrix with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
theorem isHolomorphicIn_of_linearMap {N N' : ℕ}
    (g : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N')
    {O : Set (ComplexCoordinates N)} (hO : IsOpen O) : ComplexCoordinates.IsHolomorphicIn O g := by
  have hc : Continuous g := g.continuous_of_finiteDimensional
  refine ⟨hO, hc.continuousOn, fun a _ j => Filter.Eventually.of_forall fun ζ => ?_⟩
  have hd : DifferentiableAt ℂ (LinearMap.toContinuousLinearMap g)
      (a + ζ • ComplexCoordinates.stdBasisVector j) :=
    (LinearMap.toContinuousLinearMap g).differentiableAt
  have hi : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by fun_prop
  exact hd.comp ζ hi
section
variable {L m : ℕ} {j' : ℤ}
theorem fieldOfPositiveValues_of_positive (v : PositivelyOrientedBond L m j' → ComplexMatrix2)
    {b : Bond L m j'} (hb : b.IsPositivelyOriented) : fieldOfPositiveValues v b = v ⟨b, hb⟩ :=
  dif_pos hb
theorem fieldOfPositiveValues_of_not_positive
    (v : PositivelyOrientedBond L m j' → ComplexMatrix2) {b : Bond L m j'}
    (hb : ¬ b.IsPositivelyOriented) (hr : b.opposite.IsPositivelyOriented) :
    fieldOfPositiveValues v b = (v ⟨b.opposite, hr⟩)⁻¹ :=
  (dif_neg hb).trans (dif_pos hr)
theorem fieldOfPositiveValues_valuesOnPositiveBonds {U : Bond L m j' → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') : fieldOfPositiveValues (valuesOnPositiveBonds U) = U := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.fieldOfPositiveValues_valuesOnPositiveBonds <;> assumption
theorem fieldOfPositiveValues_mem_compactGaugeFields (hL : 13 ≤ L) (hm : 0 < m) (hj : 0 ≤ j')
    {v : PositivelyOrientedBond L m j' → ComplexMatrix2} (hv : ∀ b, v b ∈ compactGaugeGroup) :
    fieldOfPositiveValues v ∈ compactGaugeFields L m j' := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_of_positive _ hb]
      exact hv _
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      rw [fieldOfPositiveValues_of_not_positive _ hb hr]
      exact inv_mem_specialUnitary (hv _)
  · by_cases hb : b.IsPositivelyOriented
    · have hr : b.opposite.opposite.IsPositivelyOriented := hb
      rw [fieldOfPositiveValues_of_positive _ hb,
        fieldOfPositiveValues_of_not_positive _
          (not_opposite_isPositivelyOriented hL hm hj b hb) hr]
      rfl
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      rw [fieldOfPositiveValues_of_positive _ hr, fieldOfPositiveValues_of_not_positive _ hb hr,
        inv_inv_specialUnitary (hv _)]
end
section
variable {L m K k : ℕ}
theorem isRelativelyOpen_image_valuesOnPositiveBonds (hL : 13 ≤ L) (hm : 0 < m) (hk : k < K)
    {ω : ℝ} (c : BondAtLevel L m K (k + 1))
    (hopen : IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))) :
    ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct
        fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
      (valuesOnPositiveBonds ''
        (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))) := by
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp hopen
  have hind : Topology.IsInducing
      (fun (w : PositivelyOrientedBond L m (levelDepth K k) → ComplexMatrix2.specialUnitary)
        (b : PositivelyOrientedBond L m (levelDepth K k)) => (w b : ComplexMatrix2)) :=
    Topology.IsInducing.piMap fun _ => Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOt⟩ := hind.isOpen_iff.mp ht
  refine ⟨O, hO, ?_⟩
  ext v
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨?_, fun b => hU.1.1 b.1 (mem_univ _)⟩
    have h₁ : (⟨U, hU.1⟩ : gaugeFieldsAtLevel L m K k) ∈ gaugeFieldAtLevelValues ⁻¹' t := by
      rw [hpre]
      exact hU
    have h₂ : gaugeFieldAtLevelValues (⟨U, hU.1⟩ : gaugeFieldsAtLevel L m K k) ∈ t := h₁
    rw [← hOt] at h₂
    exact h₂
  · rintro ⟨hvO, hvr⟩
    have hj : 0 ≤ levelDepth K k := by
      simp only [levelDepth]
      omega
    have hcfg := fieldOfPositiveValues_mem_compactGaugeFields hL hm hj (v := v) hvr
    have hpv : valuesOnPositiveBonds (fieldOfPositiveValues v) = v :=
      funext fun b => fieldOfPositiveValues_of_positive v b.2
    refine ⟨fieldOfPositiveValues v, ?_, hpv⟩
    have h₁ : (⟨fieldOfPositiveValues v, hcfg⟩ : gaugeFieldsAtLevel L m K k) ∈
        gaugeFieldAtLevelValues ⁻¹' t := by
      show gaugeFieldAtLevelValues _ ∈ t
      rw [← hOt]
      have h₂ : (fun b => ((gaugeFieldAtLevelValues
          (⟨fieldOfPositiveValues v, hcfg⟩ : gaugeFieldsAtLevel L m K k) b :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2)) = v := hpv
      show (fun b => ((gaugeFieldAtLevelValues
          (⟨fieldOfPositiveValues v, hcfg⟩ : gaugeFieldsAtLevel L m K k) b :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2)) ∈ O
      rw [h₂]
      exact hvO
    rw [hpre] at h₁
    exact h₁
theorem isRealAnalyticBetween_of_holomorphic_extension
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : EntrywiseHolomorphy.RestrictionStatement) {ω : ℝ}
    (c : BondAtLevel L m K (k + 1))
    (hopen : IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))))
    (hO : IsOpen (invertibleContourSet (j' := levelDepth K k) c))
    (hres : restrictToPositiveDoubleBlock c ''
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) ⊆
      invertibleContourSet (j' := levelDepth K k) c)
    [Fintype (PositivelyOrientedBond L m (levelDepth K k))]
    (G : (positiveBondsInDoubleBlock (j' := levelDepth K k) c → ComplexMatrix2) → ComplexMatrix2)
    (hhol : ∀ (n : ℕ) (ν : positiveBondsInDoubleBlock (j' := levelDepth K k) c ≃ Fin n),
      ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c) G)
    (hsl : ∀ V ∈ invertibleContourSet (j' := levelDepth K k) c,
      (∀ b, V b ∈ complexGaugeGroup) → G V ∈ complexGaugeGroup)
    (T : (PositivelyOrientedBond L m (levelDepth K k) → ComplexMatrix2) → ComplexMatrix2)
    (hT : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      T (valuesOnPositiveBonds U) = G (restrictToPositiveDoubleBlock c U))
    (hG : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      G (restrictToPositiveDoubleBlock c U) ∈ compactGaugeGroup) :
    ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
      (valuesOnPositiveBonds ''
        (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
      (fun v _ => T v) := by
  classical
  set D := valuesOnPositiveBonds ''
    (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) with hDdef
  let n := Fintype.card (PositivelyOrientedBond L m (levelDepth K k))
  let μ : PositivelyOrientedBond L m (levelDepth K k) ≃ Fin n := Fintype.equivFin _
  have hn : 1 ≤ n := by
    have : Nonempty (PositivelyOrientedBond L m (levelDepth K k)) :=
      ⟨⟨Bond.forwardFrom 0 0, 0, by simp [Bond.forwardFrom]⟩⟩
    exact Fintype.card_pos
  let toIndex : positiveBondsInDoubleBlock (j' := levelDepth K k) c → Fin n :=
    fun b => μ ⟨b.1, b.2.1⟩
  have hinj : Function.Injective toIndex := by
    intro a b h
    have := μ.injective h
    exact Subtype.ext (congrArg (fun p : PositivelyOrientedBond L m (levelDepth K k) => p.1) this)
  let proj : (Fin n → ComplexMatrix2) →
      positiveBondsInDoubleBlock (j' := levelDepth K k) c → ComplexMatrix2 :=
    fun X b => X (toIndex b)
  have hcont : Continuous proj := continuous_pi fun b => continuous_apply _
  let O := proj ⁻¹' invertibleContourSet (j' := levelDepth K k) c
  have hOo : IsOpen O := hO.preimage hcont
  have : Finite (positiveBondsInDoubleBlock (j' := levelDepth K k) c) :=
    Finite.of_injective toIndex hinj
  obtain ⟨n', ⟨ν⟩⟩ := Finite.exists_equiv_fin (positiveBondsInDoubleBlock (j' := levelDepth K k) c)
  have hF : EntrywiseHolomorphy.IsEntrywiseHolomorphic O (G ∘ proj) := by
    let e := matrixPowerLinearEquiv n
    let gL := (matrixPowerLinearEquiv n').toLinearMap ∘ₗ
      (LinearMap.funLeft ℂ ComplexMatrix2 fun i => toIndex (ν.symm i)) ∘ₗ e.symm.toLinearMap
    have hgl : ∀ X, gL (e X) = SmallRadius.doubleBlockEquiv c ν (proj X) := by
      intro X
      simp only [gL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
    have hImg : IsOpen (e '' O) := e.toContinuousLinearEquiv.toHomeomorph.isOpenMap O hOo
    have hg := isHolomorphicIn_of_linearMap gL hImg
    have hf := hhol n' ν
    have hmaps : MapsTo gL (e '' O) (SmallRadius.doubleBlockEquiv c ν ''
        invertibleContourSet (j' := levelDepth K k) c) := by
      rintro _ ⟨X, hX, rfl⟩
      exact ⟨proj X, hX, (hgl X).symm⟩
    have hcomp := ((hP.1 _ _ hf.1).1 _ _ hf).2.2.2.1 _ _ _ hg hmaps
    have heq : (ComplexCoordinates.matrixEquiv ∘ G ∘ (SmallRadius.doubleBlockEquiv c ν).symm) ∘ gL =
        ComplexCoordinates.matrixEquiv ∘ (G ∘ proj) ∘
          (ComplexCoordinates.productEquiv
            (EntrywiseHolomorphy.matrixKinds n)).symm := by
      funext z
      obtain ⟨X, rfl⟩ := e.surjective z
      have h₁ : (ComplexCoordinates.productEquiv
          (EntrywiseHolomorphy.matrixKinds n)).symm (e X) = X :=
        (ComplexCoordinates.productEquiv
          (EntrywiseHolomorphy.matrixKinds n)).symm_apply_apply X
      show ComplexCoordinates.matrixEquiv
          (G ((SmallRadius.doubleBlockEquiv c ν).symm (gL (e X)))) =
        ComplexCoordinates.matrixEquiv (G (proj ((ComplexCoordinates.productEquiv
          (EntrywiseHolomorphy.matrixKinds n)).symm (e X))))
      rw [hgl, Equiv.symm_apply_apply, h₁]
    rw [heq] at hcomp
    exact hcomp
  have hsl' : ∀ X ∈ O ∩ EntrywiseHolomorphy.unimodularPow n,
      (G ∘ proj) X ∈ ComplexMatrix2.unitDeterminant := fun X hX => hsl _ hX.1 fun b => hX.2 _
  have hback : ∀ v, familyReindex μ.symm (familyReindex μ v) = v := by
    intro v
    funext b
    simp [familyReindex]
  have hprojU : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      proj (familyReindex μ (valuesOnPositiveBonds U)) = restrictToPositiveDoubleBlock c U := by
    intro U
    funext b
    simp [familyReindex, proj, toIndex, valuesOnPositiveBonds, restrictToPositiveDoubleBlock]
  have hset : familyReindex μ ⁻¹' (familyReindex μ.symm ⁻¹' D) = D := by
    ext v
    simp only [mem_preimage, hback]
  have hDopen : ComplexMatrix2.IsRelativelyOpen (EntrywiseHolomorphy.unitaryPow n)
      (familyReindex μ.symm ⁻¹' D) :=
    isRelativelyOpen_compactProduct_reindex μ.symm
      (isRelativelyOpen_image_valuesOnPositiveBonds hL.2 hm hk c hopen)
  have hback' : ∀ X, familyReindex μ (familyReindex μ.symm X) = X := by
    intro X
    funext b
    simp [familyReindex]
  have hsub : familyReindex μ.symm ⁻¹' D ⊆ O ∩ EntrywiseHolomorphy.unitaryPow n := by
    intro X hX
    obtain ⟨U, hU, hUX⟩ := hX
    have hXU : X = familyReindex μ (valuesOnPositiveBonds U) := by rw [hUX, hback']
    refine ⟨?_, ?_⟩
    · show proj X ∈ invertibleContourSet (j' := levelDepth K k) c
      rw [hXU, hprojU]
      exact hres ⟨U, hU, rfl⟩
    · intro i
      rw [hXU]
      exact hU.1.1 _ (mem_univ _)
  have hin : ∀ X ∈ familyReindex μ.symm ⁻¹' D,
      (G ∘ proj) X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    intro X hX
    obtain ⟨U, hU, hUX⟩ := hX
    have hXU : X = familyReindex μ (valuesOnPositiveBonds U) := by rw [hUX, hback']
    show G (proj X) ∈ _
    rw [hXU, hprojU]
    exact hG U hU
  have main := (hH n hn O hOo (G ∘ proj) hF hsl').2 _ hsub hDopen hin
  have hre := isRealAnalyticBetween_reindex μ (Equiv.ofUnique (Fin 1) Unit) main
  rw [hset] at hre
  refine isRealAnalyticBetween_congr hre ?_
  rintro _ ⟨U, hU, rfl⟩
  funext _
  show T (valuesOnPositiveBonds U) = G (proj (familyReindex μ (valuesOnPositiveBonds U)))
  rw [hT U hU, hprojU]
end
section
variable {L m K k : ℕ}
theorem realAnalytic_contourMean_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : EntrywiseHolomorphy.RestrictionStatement) {ω : ℝ}
    (c : BondAtLevel L m K (k + 1))
    (hopen : IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))))
    (hvar : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y, meanContourHolonomy U y x ∈ compactGaugeGroup)
    (hO : IsOpen (invertibleContourSet (j' := levelDepth K k) c))
    (hres : restrictToPositiveDoubleBlock c ''
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) ⊆
      invertibleContourSet (j' := levelDepth K k) c)
    (hhol : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ (n : ℕ)
        (ν : positiveBondsInDoubleBlock (j' := levelDepth K k) c ≃ Fin n),
        ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
          ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
          (fun V => contourVariable c V y x) ∧
        ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
          ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
          (fun V => contourVariableInverse c V y x))
    (hval : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ V ∈ invertibleContourSet (j' := levelDepth K k) c,
        IsUnit (contourVariable c V y x) ∧
        IsUnit (contourVariableInverse c V y x) ∧
        ((∀ b, V b ∈ complexGaugeGroup) →
          contourVariable c V y x ∈ complexGaugeGroup ∧
          contourVariableInverse c V y x ∈ complexGaugeGroup))
    (hext : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y,
          meanContourHolonomy U y x = contourVariable c (restrictToPositiveDoubleBlock c U) y x ∧
          (meanContourHolonomy U y x)⁻¹ =
            contourVariableInverse c (restrictToPositiveDoubleBlock c U) y x) :
    ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ComplexMatrix2.IsRealAnalyticBetween
          (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
          (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
          (valuesOnPositiveBonds ''
            (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
          (fun v _ => meanContourHolonomy (fieldOfPositiveValues v) y x) ∧
        ComplexMatrix2.IsRealAnalyticBetween
          (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
          (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
          (valuesOnPositiveBonds ''
            (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
          (fun v _ => (meanContourHolonomy (fieldOfPositiveValues v) y x)⁻¹) := by
  intro _ y hy x hx
  refine ⟨isRealAnalyticBetween_of_holomorphic_extension hL hm hk hP hH c hopen hO hres
      (fun V => contourVariable c V y x) (fun n ν => (hhol y hy x hx n ν).1)
      (fun V hV hb => ((hval y hy x hx V hV).2.2 hb).1)
      (fun v => meanContourHolonomy (fieldOfPositiveValues v) y x) ?_ ?_,
    isRealAnalyticBetween_of_holomorphic_extension hL hm hk hP hH c hopen hO hres
      (fun V => contourVariableInverse c V y x) (fun n ν => (hhol y hy x hx n ν).2)
      (fun V hV hb => ((hval y hy x hx V hV).2.2 hb).2)
      (fun v => (meanContourHolonomy (fieldOfPositiveValues v) y x)⁻¹) ?_ ?_⟩
  · intro U hU
    show meanContourHolonomy (fieldOfPositiveValues (valuesOnPositiveBonds U)) y x = _
    rw [fieldOfPositiveValues_valuesOnPositiveBonds hU.1]
    exact (hext U hU y hy x hx).1
  · intro U hU
    show contourVariable c (restrictToPositiveDoubleBlock c U) y x ∈ _
    rw [← (hext U hU y hy x hx).1]
    exact hvar U hU y hy x hx
  · intro U hU
    show (meanContourHolonomy (fieldOfPositiveValues (valuesOnPositiveBonds U)) y x)⁻¹ = _
    rw [fieldOfPositiveValues_valuesOnPositiveBonds hU.1]
    exact (hext U hU y hy x hx).2
  · intro U hU
    show contourVariableInverse c (restrictToPositiveDoubleBlock c U) y x ∈ _
    rw [← (hext U hU y hy x hx).2]
    exact inv_mem_specialUnitary (hvar U hU y hy x hx)
end
end RealAnalytic
section Crossing
variable {L m K k : ℕ}
theorem specialUnitary_inv_mem {U : ComplexMatrix2} (h : U ∈ ComplexMatrix2.specialUnitary) :
    U⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem specialUnitary_inv_mul {U : ComplexMatrix2} (h : U ∈ ComplexMatrix2.specialUnitary) :
    U⁻¹ * U = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem specialUnitary_inv_inv {U : ComplexMatrix2} (h : U ∈ ComplexMatrix2.specialUnitary) :
    U⁻¹⁻¹ = U := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem specialUnitary_inv_mul_cancel_left {U : ComplexMatrix2}
    (h : U ∈ ComplexMatrix2.specialUnitary) (Y : ComplexMatrix2) : U⁻¹ * (U * Y) = Y := by
  rw [← mul_assoc, specialUnitary_inv_mul h, one_mul]
theorem norm_inv_sub_one_specialUnitary {V : ComplexMatrix2}
    (h : V ∈ ComplexMatrix2.specialUnitary) : ‖V⁻¹ - 1‖ = ‖V - 1‖ := by
  have e : V⁻¹ - 1 = V⁻¹ * (1 - V) := by rw [mul_sub, mul_one, specialUnitary_inv_mul h]
  rw [e, CStarRing.norm_mem_unitary_mul _
    (Matrix.specialUnitaryGroup_le_unitaryGroup (specialUnitary_inv_mem h)), norm_sub_rev]
theorem norm_conj_sub_one_specialUnitary {T : ComplexMatrix2}
    (h : T ∈ ComplexMatrix2.specialUnitary) (Y : ComplexMatrix2) :
    ‖T * Y * T⁻¹ - 1‖ = ‖Y - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.norm_conj_sub_one <;> assumption
theorem norm_mul_mul_sub_one_le {A B C : ComplexMatrix2} {a b c : ℝ} (hA : ‖A - 1‖ ≤ a)
    (hB : ‖B - 1‖ ≤ b) (hC : ‖C - 1‖ ≤ c) :
    ‖A * B * C - 1‖ ≤ (1 + a) * (1 + b) * (1 + c) - 1 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  have hb : 0 ≤ b := (norm_nonneg _).trans hB
  have nB : ‖B‖ ≤ 1 + b := by
    have : B = (B - 1) + 1 := by abel
    calc ‖B‖ = ‖(B - 1) + 1‖ := by rw [← this]
      _ ≤ ‖B - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 1 + b := by rw [norm_one]; linarith
  have nC : ‖C‖ ≤ 1 + c := by
    have : C = (C - 1) + 1 := by abel
    calc ‖C‖ = ‖(C - 1) + 1‖ := by rw [← this]
      _ ≤ ‖C - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 1 + c := by rw [norm_one]; linarith
  have e : A * B * C - 1 = (A - 1) * B * C + (B - 1) * C + (C - 1) := by noncomm_ring
  rw [e]
  have t₁ : ‖(A - 1) * B * C‖ ≤ a * (1 + b) * (1 + c) :=
    calc ‖(A - 1) * B * C‖ ≤ ‖A - 1‖ * ‖B‖ * ‖C‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ a * (1 + b) * (1 + c) := by gcongr
  have t₂ : ‖(B - 1) * C‖ ≤ b * (1 + c) :=
    (norm_mul_le _ _).trans (by gcongr)
  calc ‖(A - 1) * B * C + (B - 1) * C + (C - 1)‖
      ≤ ‖(A - 1) * B * C‖ + ‖(B - 1) * C‖ + ‖C - 1‖ := norm_add₃_le
    _ ≤ a * (1 + b) * (1 + c) + b * (1 + c) + c := by gcongr
    _ = (1 + a) * (1 + b) * (1 + c) - 1 := by ring
theorem norm_crossing_sub_one_lt {a b G G' X T : ComplexMatrix2}
    (ha : a ∈ ComplexMatrix2.specialUnitary) (hG : G ∈ ComplexMatrix2.specialUnitary)
    (hG' : G' ∈ ComplexMatrix2.specialUnitary) (hT : T ∈ ComplexMatrix2.specialUnitary)
    (h₁ : ‖G * a⁻¹ - 1‖ ≤ 2 / 25) (h₂ : ‖G' * b⁻¹ - 1‖ ≤ 2 / 25)
    (h₃ : ‖G * X * (T * G')⁻¹ - 1‖ ≤ 1 / 40) : ‖a * X * b⁻¹ * T⁻¹ - 1‖ < 1 / 5 := by
  have hGa : G * a⁻¹ ∈ ComplexMatrix2.specialUnitary := mul_mem hG (specialUnitary_inv_mem ha)
  have hid : a * X * b⁻¹ * T⁻¹ =
      (G * a⁻¹)⁻¹ * (G * X * (T * G')⁻¹) * (T * (G' * b⁻¹) * T⁻¹) := by
    rw [Matrix.mul_inv_rev G, specialUnitary_inv_inv ha, Matrix.mul_inv_rev T]
    simp only [mul_assoc, specialUnitary_inv_mul_cancel_left hG,
      specialUnitary_inv_mul_cancel_left hT, specialUnitary_inv_mul_cancel_left hG']
  have b₁ : ‖(G * a⁻¹)⁻¹ - 1‖ ≤ 2 / 25 := by
    rw [norm_inv_sub_one_specialUnitary hGa]; exact h₁
  have b₃ : ‖T * (G' * b⁻¹) * T⁻¹ - 1‖ ≤ 2 / 25 := by
    rw [norm_conj_sub_one_specialUnitary hT]; exact h₂
  rw [hid]
  refine (norm_mul_mul_sub_one_le b₁ h₃ b₃).trans_lt ?_
  norm_num
theorem toSublattice_unitStep (hL : 0 < L) (ν : Fin 4) :
    (unitStep L m (levelDepth K (k + 1)) ν).toSublattice (levelDepth K k) =
      L • unitStep L m (levelDepth K k) ν := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.toSublattice_unitStep_succ <;> assumption
theorem shiftAcross_eq (hL : 0 < L) {ν : Fin 4} (c : BondAtLevel L m K (k + 1))
    (hν : c.target - c.source = unitStep L m (levelDepth K (k + 1)) ν) (x : SiteAtLevel L m K k) :
    shiftAcross c x = x + L • unitStep L m (levelDepth K k) ν := by
  rw [shiftAcross, hν, toSublattice_unitStep hL]
theorem pathHolonomy_mem_of_compact {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (Γ : List (Bond L m j)) :
    pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p3102 <;> assumption
theorem pathHolonomy_append_eq {j : ℤ} (U : Bond L m j → ComplexMatrix2)
    (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem radius_exp_chain_across (hN : Numerics.ExpLogNumericBounds) (hL : 13 ≤ L) {l : ℕ}
    (hl : (l : ℤ) ≤ 3 * (L : ℤ) - 2) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) :
    (1 + ω) ^ (l * (l - 1) / 2) - 1 ≤ 1 / 40 := by
  have hl₁ : l ≤ 3 * L := by omega
  have hl₂ : l - 1 ≤ 3 * L := by omega
  have hprod : ((l * (l - 1) : ℕ) : ℝ) ≤ 9 * (L : ℝ) ^ 2 := by
    have : l * (l - 1) ≤ (3 * L) * (3 * L) := Nat.mul_le_mul hl₁ hl₂
    have h' : ((l * (l - 1) : ℕ) : ℝ) ≤ (((3 * L) * (3 * L) : ℕ) : ℝ) := by exact_mod_cast this
    refine h'.trans (le_of_eq ?_)
    push_cast
    ring
  have hNle : ((l * (l - 1) / 2 : ℕ) : ℝ) ≤ 9 / 2 * (L : ℝ) ^ 2 := by
    refine (Nat.cast_div_le).trans ?_
    push_cast at hprod ⊢
    linarith
  have hωpos : 0 < ω := hω.1
  have hωle : ω * (L : ℝ) ^ 2 ≤ 1 / 200 := by
    have := hω.2
    rw [averagingRadiusCap, le_div_iff₀ (by positivity)] at this
    linarith
  have hexp : ((l * (l - 1) / 2 : ℕ) : ℝ) * ω ≤ 9 / 400 := by
    calc ((l * (l - 1) / 2 : ℕ) : ℝ) * ω ≤ 9 / 2 * (L : ℝ) ^ 2 * ω := by gcongr
      _ = 9 / 2 * (ω * (L : ℝ) ^ 2) := by ring
      _ ≤ 9 / 400 := by linarith
  have hpow : (1 + ω) ^ (l * (l - 1) / 2) ≤ Real.exp (((l * (l - 1) / 2 : ℕ) : ℝ) * ω) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ω]) _
  have h3 : Real.exp (9 / 400) < 1.0228 := hN.2.1
  have h4 := Real.exp_le_exp.mpr hexp
  norm_num at h3 ⊢
  linarith
theorem crossingDefect_near_at (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement) (hR : HolonomyReorderingBound)
    (hN : Numerics.ExpLogNumericBounds) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1))
    (hvar : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y,
          meanContourHolonomy U y x ∈ compactGaugeGroup ∧
          (∀ Γ ∈ contourSet y x,
            ComplexMatrix2.operatorNorm (pathHolonomy U Γ * (meanContourHolonomy U y x)⁻¹ - 1) ≤
              2 / 25)) :
    c.IsPositivelyOriented →
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
        crossingDefect U c x ∈ compactGaugeGroup ∧
          ComplexMatrix2.operatorNorm (crossingDefect U c x - 1) < 1 / 5 := by
  rintro ⟨ν, hν⟩ U hU x hx
  have hLpos : 0 < L := by have := hL.2; omega
  have hreal : U ∈ compactGaugeFields L m (levelDepth K k) := hU.1
  have hsmall : DoubleBlockPlaquettesNear ω c U := hU.2
  have hhead : c.target = c.source + unitStep L m (levelDepth K (k + 1)) ν := by
    rw [← hν]; abel
  obtain ⟨-, hsite⟩ := (hC L m K hL.1 hL.2 hm k hk c).1 c.source (Or.inl rfl)
  obtain ⟨⟨n, hn⟩, hall⟩ := hsite x hx
  obtain ⟨-, h2, -⟩ := hall n hn
  let σ : AxisOrdering c.source x := (offsetAxes c.source x).equivFin.symm
  obtain ⟨𝔞, -, hpath⟩ := h2 _ ⟨σ, rfl⟩
  have hA := (hC L m K hL.1 hL.2 hm k hk c).2 ν hhead x hx σ 𝔞 hpath
  obtain ⟨hx', ⟨σ', -, hpath'⟩, hr1, -, -, hl2, hl3, hp1, hp2, -, hs2, -, -⟩ := hA
  have hreorder := hR L m hL.1 hL.2 hm (levelDepth K k) (by simp only [levelDepth]; omega) U hreal
    (c.source.toSublattice (levelDepth K k)) _ _ ω hr1 hω.1.le
    (fun p hp => (hsmall p (fun z hz => hs2 z (hp hz))).le)
  have hxeq := shiftAcross_eq hLpos c hν x
  have hxb : x + L • unitStep L m (levelDepth K k) ν ∈ sitesInBlock (levelDepth K k) c.target :=
    hx'
  obtain ⟨ha, hGa⟩ := hvar U hU c.source (by simp) x hx
  obtain ⟨hb, hGb⟩ := hvar U hU c.target (by simp) _ hxb
  have hW : crossingDefect U c x = meanContourHolonomy U c.source x *
      pathHolonomy U (axialPath x (x + L • unitStep L m (levelDepth K k) ν)) *
      (meanContourHolonomy U c.target (x + L • unitStep L m (levelDepth K k) ν))⁻¹ *
      (parallelTransport U c)⁻¹ := by
    rw [crossingDefect, crossingPath, hxeq]
  rw [hW]
  have hX := pathHolonomy_mem_of_compact hreal
    (axialPath x (x + L • unitStep L m (levelDepth K k) ν))
  have hT : parallelTransport U c ∈ ComplexMatrix2.specialUnitary :=
    pathHolonomy_mem_of_compact hreal _
  refine ⟨mul_mem (mul_mem (mul_mem ha hX) (specialUnitary_inv_mem hb))
    (specialUnitary_inv_mem hT), ?_⟩
  refine norm_crossing_sub_one_lt ha (pathHolonomy_mem_of_compact hreal _)
    (pathHolonomy_mem_of_compact hreal _) hT (hGa _ ⟨σ, rfl⟩) (hGb _ ⟨σ', rfl⟩) ?_
  have h3 := radius_exp_chain_across hN hL.2
    (l := (List.replicate L (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) ++ 𝔞).length)
    (by rw [hl2]; push_cast; exact hl3) hω
  have hrw : pathHolonomy U (orderedContour c.source x σ) *
      pathHolonomy U (axialPath x (x + L • unitStep L m (levelDepth K k) ν)) *
      (parallelTransport U c *
        pathHolonomy U (orderedContour c.target (x + L • unitStep L m (levelDepth K k) ν) σ'))⁻¹ =
      wordHolonomy U (c.source.toSublattice (levelDepth K k))
        (𝔞 ++ List.replicate L (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν)) *
      (wordHolonomy U (c.source.toSublattice (levelDepth K k))
        (List.replicate L (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) ++ 𝔞))⁻¹ := by
    rw [wordHolonomy, wordHolonomy, hp1, hp2, hpath', pathHolonomy_append_eq,
      pathHolonomy_append_eq, parallelTransport]
  rw [hrw]
  exact hreorder.trans h3
end Crossing
theorem everySmallRadiusSuffices (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hR : HolonomyReorderingBound) (hN : Numerics.ExpLogNumericBounds)
    (hM : SmallDiameterMean.AverageStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : EntrywiseHolomorphy.RestrictionStatement) : SmallRadius.EverySmallRadiusSuffices := by
  intro s ω hω k hk c
  have hL := s.isAdmissible
  have hL0 : 0 < s.L := by have := hL.2; omega
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hvar := contourMean_spec_at hL hm hk hC hR hN hM hω c
  have hdiam := familyDiameter_le_at hL hm hk hC hR hN hω c
  exact
  { isOpen_smallPlaquetteFields := fun ω' _ => isOpen_smallPlaquetteFields_at hL0 hk ω' c
    holonomy_ratio_le := holonomy_ratio_le_at hL hm hk hC hR hN hω c
    familyDiameter_le := hdiam
    contourMean_spec := hvar
    isOpen_invertibleContourSet := isOpen_invertibleContourSet_at hL0 hk hM c
    image_restrict_subset := image_restrict_subset_at hL hm hk hC hR hN hω c
    holomorphic_contourVariable := holomorphic_contourVariable_at hL0 hk hM hP c
    contourVariable_values := contourVariable_values_at hM c
    contourVariable_extends := contourVariable_extends_at hL hm hk hC hR hN hM hω c
    realAnalytic_contourMean := realAnalytic_contourMean_at hL hm hk hP hH c
      (isOpen_smallPlaquetteFields_at hL0 hk ω c)
      (fun U hU y hy x hx => (hvar U hU y hy x hx).2.2.2.1)
      (isOpen_invertibleContourSet_at hL0 hk hM c)
      (image_restrict_subset_at hL hm hk hC hR hN hω c)
      (holomorphic_contourVariable_at hL0 hk hM hP c) (contourVariable_values_at hM c)
      (contourVariable_extends_at hL hm hk hC hR hN hM hω c)
    crossingDefect_near := crossingDefect_near_at hL hm hk hC hR hN hω c
      (fun U hU y hy x hx => by
        obtain ⟨_, _, _, h4, h5, h6⟩ := hvar U hU y hy x hx
        exact ⟨h4, fun Γ hΓ => (h5 Γ hΓ).trans h6⟩) }
end YangMills.Construction.Averaging.SmallRadiusProof
end
