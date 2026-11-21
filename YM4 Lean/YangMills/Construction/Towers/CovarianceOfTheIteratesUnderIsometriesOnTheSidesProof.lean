import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadiiProof
import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.ComplexObjectsReadTheBondsOfADoubleBlock
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariables
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesOnTheSidesProof
import YangMills.Construction.Towers.ChainOfTheComplexIterateDifferentials
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovarianceOfTheIteratesUnderIsometriesOnTheSides
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.IsometriesInTheLeftChart
import YangMills.Construction.Towers.LinearityOfTheCovariantMapsOfAStepOnTheSides
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSides
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratesCovariance
open YangMills.Construction.Matrices
structure Inputs : Prop where
  sublattices : SublatticesSymmetriesScalingsAndProjections.Statement
  translations : Translations.TranslationProperties
  chartForms : LeftChartIsometryEquivariance
  chartFields : LeftChartFields.Claim
  meanStable : MeanStableFields.MeanStableFieldsHold
  iterated : IteratedMeans.IteratedMeansHold
  smoothing : SmoothingNearIdentity
  chain : ComplexIterDerivChain
  relations : CovariantIterRelations
  linear : StepMapsComplexLinear.Claim
  orientation : PeriodicLattice.LevelBondOrientationDichotomy
  average : PeriodicLattice.ComplexAverageEquivariance
  contour : PeriodicLattice.ComplexContourHolonomyCovariance
  images : PeriodicLattice.IsometryImages.Statement
  doubleBlock : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock
variable {L n k : ℕ}
theorem exists_latticeIsometry_of_affine {i : ℕ}
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) {v : InfiniteLattice.AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i))
    (hwv : ∀ x : InfiniteLattice.AmbientSpace,
      f (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) (w x + v)) :
    ∃ σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n, (∀ x, σ x = f x) ∧
      σ ∈ PeriodicLattice.latticeIsometries L n (PeriodicLattice.levelDepth k i) := by apply _root_.YangMills.Construction.Tower.EquivariantOnSides.exists_mem_latticeIsometries <;> assumption
structure Symmetry (L n k : ℕ) (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n) : Prop where
  admissible : Conventions.IsAdmissibleBlockingFactor L
  side_pos : 0 < n
  apply_eq : ∀ x, σ x = f x
  distance : IsDistancePreserving f
  sublattice_onto : ∀ i ≤ k, MapsSublatticeOnto k i f
  edges_onto : ∀ i ≤ k, MapsEdgesOnto k i f
  mem_isometries : σ ∈ PeriodicLattice.latticeIsometries L n (PeriodicLattice.levelDepth k k)
variable {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
  {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n}
theorem Symmetry.injective (h : Symmetry L n k f σ) : Function.Injective f := by
  have : f = σ := funext fun x => (h.apply_eq x).symm
  rw [this]
  exact σ.injective
theorem vertexPreimage_eq_of_apply {i : ℕ} (h : Symmetry L n k f σ) {x x' : Vertex L n k i}
    (hx : f x' = x) : vertexPreimage f x = x' := by
  have hs : f (vertexPreimage f x) = x :=
    Classical.epsilon_spec (p := fun y : Vertex L n k i => f y = x) ⟨x', hx⟩
  exact Subtype.ext (h.injective (hs.trans hx.symm))
theorem apply_vertexPreimage {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k) (x : Vertex L n k i) :
    f (vertexPreimage f x) = x := by
  have hmem : (x : PeriodicLattice.FourTorus L n) ∈
      f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) := by
    rw [h.sublattice_onto i hi]
    exact x.2
  obtain ⟨z, hz, hfz⟩ := hmem
  exact Classical.epsilon_spec (p := fun y : Vertex L n k i => f y = x) ⟨⟨z, hz⟩, hfz⟩
theorem coe_sitePreimage_symm {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k) (x : Vertex L n k i) :
    ((PeriodicLattice.sitePreimage σ.symm x : Vertex L n k i) : PeriodicLattice.FourTorus L n) =
      f x := by
  have hmem : f x ∈ (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
      Set (PeriodicLattice.FourTorus L n)) := by
    rw [← h.sublattice_onto i hi]
    exact ⟨x, x.2, rfl⟩
  have hs := Classical.epsilon_spec (p := fun z : Vertex L n k i =>
    (z : PeriodicLattice.FourTorus L n) = σ.symm.symm x) ⟨⟨f x, hmem⟩, by simp [h.apply_eq]⟩
  simpa [PeriodicLattice.sitePreimage, h.apply_eq] using hs
theorem sitePreimage_symm_vertexPreimage {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k)
    (y : Vertex L n k i) : PeriodicLattice.sitePreimage σ.symm (vertexPreimage f y) = y :=
  Subtype.ext ((coe_sitePreimage_symm h hi _).trans (apply_vertexPreimage h hi y))
theorem vertexPreimage_sitePreimage_symm {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k)
    (x : Vertex L n k i) : vertexPreimage f (PeriodicLattice.sitePreimage σ.symm x) = x :=
  vertexPreimage_eq_of_apply h (coe_sitePreimage_symm h hi x).symm
theorem edgePreimage_ends {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k) (b : Edge L n k i) :
    (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target := by
  obtain ⟨b₀, ht, hh⟩ := (h.edges_onto i hi).2 b
  exact Classical.epsilon_spec (p := fun b' : Edge L n k i =>
    b'.source = vertexPreimage f b.source ∧ b'.target = vertexPreimage f b.target)
    ⟨b₀, (vertexPreimage_eq_of_apply h ht.symm).symm, (vertexPreimage_eq_of_apply h hh.symm).symm⟩
theorem edgePreimage_opposite {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k) (b : Edge L n k i) :
    edgePreimage f b.opposite = (edgePreimage f b).opposite := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact ((edgePreimage_ends h hi b.opposite).1).trans (edgePreimage_ends h hi b).2.symm
  · exact ((edgePreimage_ends h hi b.opposite).2).trans (edgePreimage_ends h hi b).1.symm
theorem bondPreimage_eq_edgePreimage {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k)
    (b : Edge L n k i) : PeriodicLattice.bondPreimage σ b = edgePreimage f b := by
  have ht : ((edgePreimage f b).source : PeriodicLattice.FourTorus L n) = σ.symm b.source := by
    rw [(edgePreimage_ends h hi b).1, Equiv.eq_symm_apply, h.apply_eq, apply_vertexPreimage h hi]
  have hh : ((edgePreimage f b).target : PeriodicLattice.FourTorus L n) = σ.symm b.target := by
    rw [(edgePreimage_ends h hi b).2, Equiv.eq_symm_apply, h.apply_eq, apply_vertexPreimage h hi]
  have hex : ∃ b' : Edge L n k i, (b'.source : PeriodicLattice.FourTorus L n) = σ.symm b.source ∧
      (b'.target : PeriodicLattice.FourTorus L n) = σ.symm b.target := ⟨_, ht, hh⟩
  simp only [PeriodicLattice.bondPreimage, dif_pos hex]
  have hc := hex.choose_spec
  exact PeriodicLattice.Bond.ext (Subtype.ext (hc.1.trans ht.symm))
    (Subtype.ext (hc.2.trans hh.symm))
theorem bondImage_edgePreimage {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k) (b : Edge L n k i) :
    PeriodicLattice.bondImage σ (edgePreimage f b) = b := by
  have ht : (b.source : PeriodicLattice.FourTorus L n) = σ.symm.symm (edgePreimage f b).source := by
    rw [Equiv.symm_symm, (edgePreimage_ends h hi b).1, h.apply_eq, apply_vertexPreimage h hi]
  have hh : (b.target : PeriodicLattice.FourTorus L n) = σ.symm.symm (edgePreimage f b).target := by
    rw [Equiv.symm_symm, (edgePreimage_ends h hi b).2, h.apply_eq, apply_vertexPreimage h hi]
  have hex : ∃ b' : Edge L n k i, (b'.source : PeriodicLattice.FourTorus L n) =
      σ.symm.symm (edgePreimage f b).source ∧ (b'.target : PeriodicLattice.FourTorus L n) =
      σ.symm.symm (edgePreimage f b).target := ⟨b, ht, hh⟩
  simp only [PeriodicLattice.bondImage, PeriodicLattice.bondPreimage, dif_pos hex]
  have hc := hex.choose_spec
  exact PeriodicLattice.Bond.ext (Subtype.ext (hc.1.trans ht.symm))
    (Subtype.ext (hc.2.trans hh.symm))
theorem pushField_eq_transport {i : ℕ} (h : Symmetry L n k f σ) (hi : i ≤ k)
    (U : Edge L n k i → ComplexMatrix2) :
    pushField f U = PeriodicLattice.transportGaugeField σ U := by
  funext b
  simp only [pushField, PeriodicLattice.transportGaugeField, bondPreimage_eq_edgePreimage h hi]
theorem opposite_opposite {i : ℕ} (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem xor_isPositivelyOriented (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i ≤ k) (b : Edge L n k i) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : i = 0 := by omega
    exact H.orientation L n 1 hL hn one_pos 1 le_rfl b
  · exact H.orientation L n k hL hn hk i hi b
theorem opposite_pos_of_not_pos (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i ≤ k) {b : Edge L n k i} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  rcases xor_isPositivelyOriented H hL hn hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem not_opposite_pos_of_pos (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i ≤ k) {b : Edge L n k i} (hb : b.IsPositivelyOriented) :
    ¬b.opposite.IsPositivelyOriented := by
  rcases xor_isPositivelyOriented H hL hn hi b with h | h
  · exact h.2
  · exact absurd hb h.2
section
variable {i : ℕ}
theorem extendOddly_of_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
theorem extendOddly_of_not_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
theorem extendOddly_congr (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hi : i ≤ k) {g g' : Edge L n k i → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → g b = g' b) : extendOddly g = extendOddly g' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_pos hb, extendOddly_of_pos hb, h b hb]
  · rw [extendOddly_of_not_pos hb, extendOddly_of_not_pos hb,
      h _ (opposite_pos_of_not_pos H hL hn hi hb)]
theorem extendOddly_opposite (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hi : i ≤ k) (g : Edge L n k i → ComplexMatrix2) (b : Edge L n k i) :
    extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_not_pos (not_opposite_pos_of_pos H hL hn hi hb), extendOddly_of_pos hb,
      opposite_opposite]
  · rw [extendOddly_of_pos (opposite_pos_of_not_pos H hL hn hi hb), extendOddly_of_not_pos hb,
      neg_neg]
theorem tangentEdgeValue_add (U A A' : Edge L n k i → ComplexMatrix2) (b : Edge L n k i) :
    tangentEdgeValue U (A + A') b = tangentEdgeValue U A b + tangentEdgeValue U A' b := by
  by_cases hb : b.IsPositivelyOriented
  · simp [tangentEdgeValue, hb]
  · simp only [tangentEdgeValue, if_neg hb, Pi.add_apply, ComplexMatrix2.conjugateBy, mul_add,
      add_mul, neg_add]
theorem tangentEdgeValue_smul (U A : Edge L n k i → ComplexMatrix2) (t : ℂ) (b : Edge L n k i) :
    tangentEdgeValue U (t • A) b = t • tangentEdgeValue U A b := by
  by_cases hb : b.IsPositivelyOriented
  · simp [tangentEdgeValue, hb]
  · simp only [tangentEdgeValue, if_neg hb, Pi.smul_apply, ComplexMatrix2.conjugateBy,
      Matrix.mul_smul, Matrix.smul_mul, smul_neg]
theorem isometryOnTangent_add (U A A' : Edge L n k i → ComplexMatrix2) :
    isometryOnTangent f U (A + A') = isometryOnTangent f U A + isometryOnTangent f U A' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [isometryOnTangent, Pi.add_apply, extendOddly_of_pos hb, tangentEdgeValue_add]
  · simp only [isometryOnTangent, Pi.add_apply, extendOddly_of_not_pos hb, tangentEdgeValue_add,
      neg_add]
theorem isometryOnTangent_smul (U A : Edge L n k i → ComplexMatrix2) (t : ℂ) :
    isometryOnTangent f U (t • A) = t • isometryOnTangent f U A := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [isometryOnTangent, Pi.smul_apply, extendOddly_of_pos hb, tangentEdgeValue_smul]
  · simp only [isometryOnTangent, Pi.smul_apply, extendOddly_of_not_pos hb, tangentEdgeValue_smul,
      smul_neg]
theorem conjugateBy_mem_traceless {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem det_inv_of_det_eq_one {g : ComplexMatrix2} (hg : g.det = 1) : (g⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem isometryOnTangent_mem (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hi : i ≤ k) {U B : Edge L n k i → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) : isometryOnTangent f U B ∈ complexEdgeForms L n k i := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite H hL hn hi _ b⟩
  rw [isometryOnTangent, extendOddly_of_pos hb]
  by_cases hc : (edgePreimage f b).IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos hc]
    exact hB.1 _ hc
  · simp only [tangentEdgeValue, if_neg hc]
    refine ComplexMatrix2.traceless.neg_mem
      (conjugateBy_mem_traceless (det_inv_of_det_eq_one (hU.1 _ (mem_univ _))) ?_)
    exact hB.1 _ (opposite_pos_of_not_pos H hL hn hi hc)
end
section
variable {i : ℕ}
theorem covDiff_covariance (H : Inputs) (h : Symmetry L n k f σ) (hi : i ≤ k) :
    ∀ U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup ∧
      ∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        covDiff (pushField f U) (pushSiteFunction f l) =
          isometryOnTangent f U (covDiff U l) :=
  (((H.translations L h.admissible k i hi).2.1 n h.side_pos).2.2).2.2.1 f h.distance
    (h.sublattice_onto i hi)
theorem pushField_mem_smallComplexFields (H : Inputs) (h : Symmetry L n k f σ) (hi : i ≤ k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i) :
    pushField f V ∈ smallComplexFields L n k i :=
  ⟨(covDiff_covariance H h hi V hV.1).1, fun _ => hV.2 _⟩
theorem mem_nearIdentityPolydisc_of_small (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    V ∈ nearIdentityPolydisc (polydiscRadius L) c :=
  ((H.meanStable L h.admissible k (by omega)).1 n h.side_pos).mem_polydisc i hj c hc V hV
theorem mem_domainNearOne_of_small (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    V ∈ (PeriodicLattice.complexAveragingDomainNearOne c : Set (Edge L n k i → ComplexMatrix2)) :=
  (((H.smoothing.1 L h.admissible).2.2).periodic n k i h.side_pos hj c hc).subset_complexDomain
    (mem_nearIdentityPolydisc_of_small H h hj hV hc)
theorem blockAverageStep_mem (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i) :
    PeriodicLattice.complexBlockAverageStep i V ∈
      fieldsIn L n k (i + 1) PeriodicLattice.complexGaugeGroup :=
  ((H.iterated L h.admissible k (by omega)).1 n h.side_pos).meanStep_mem i hj V hV
theorem blockAverage_push_of_pos (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    {b : Edge L n k (i + 1)} (hb : b.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage (pushField f V) b =
      PeriodicLattice.complexBlockAverage V (edgePreimage f b) := by
  have hj' : i + 1 ≤ k := hj
  have hsm := pushField_mem_smallComplexFields H h hj.le hV
  have hdb := mem_domainNearOne_of_small H h hj hsm hb
  rw [pushField_eq_transport h hj.le] at hdb ⊢
  have hidx : -(n : ℤ) ≤ PeriodicLattice.levelDepth k k := by
    have := h.side_pos
    simp only [PeriodicLattice.levelDepth]
    omega
  have hidx' : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k (i + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hconf : ∀ c : Edge L n k (i + 1),
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
        (PeriodicLattice.bondsInDoubleBlock c) V :=
    fun _ => ⟨fun b _ => hV.1.1 b (mem_univ _), fun b _ => hV.1.2 b (mem_univ _)⟩
  by_cases hp : (edgePreimage f b).IsPositivelyOriented
  · have hA := H.average L n k i _ σ h.admissible h.side_pos hidx h.mem_isometries hj hidx' V
      (edgePreimage f b) b hp hb (Or.inl (bondImage_edgePreimage h hj' b).symm) (hconf _)
    exact hA.average_image (bondImage_edgePreimage h hj' b).symm
      (mem_domainNearOne_of_small H h hj hV hp)
  · have hc := opposite_pos_of_not_pos H h.admissible h.side_pos hj' hp
    have himg : PeriodicLattice.bondImage σ (edgePreimage f b).opposite = b.opposite := by
      rw [← edgePreimage_opposite h hj', bondImage_edgePreimage h hj']
    have hb' : b = (PeriodicLattice.bondImage σ (edgePreimage f b).opposite).opposite := by
      rw [himg, opposite_opposite]
    have hA := H.average L n k i _ σ h.admissible h.side_pos hidx h.mem_isometries hj hidx' V
      (edgePreimage f b).opposite b hc hb (Or.inr hb') (hconf _)
    rw [hA.average_opposite hb' (mem_domainNearOne_of_small H h hj hV hc) hdb]
    simp only [PeriodicLattice.complexBlockAverage, if_pos hc, if_neg hp]
theorem blockAverageStep_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i) :
    PeriodicLattice.complexBlockAverageStep i (pushField f V) =
      pushField f (PeriodicLattice.complexBlockAverageStep i V) := by
  have hj' : i + 1 ≤ k := hj
  funext b
  change PeriodicLattice.complexBlockAverage (pushField f V) b =
    PeriodicLattice.complexBlockAverage V (edgePreimage f b)
  by_cases hb : b.IsPositivelyOriented
  · exact blockAverage_push_of_pos H h hj hV hb
  · have hr := opposite_pos_of_not_pos H h.admissible h.side_pos hj' hb
    have h₁ := blockAverage_push_of_pos H h hj hV hr
    rw [edgePreimage_opposite h hj'] at h₁
    have h₂ : PeriodicLattice.complexBlockAverage (pushField f V) b =
        (PeriodicLattice.complexBlockAverage (pushField f V) b.opposite)⁻¹ := by
      have := (blockAverageStep_mem H h hj (pushField_mem_smallComplexFields H h hj.le hV)).2
        b.opposite (mem_univ _)
      rwa [opposite_opposite] at this
    have h₃ : PeriodicLattice.complexBlockAverage V (edgePreimage f b) =
        (PeriodicLattice.complexBlockAverage V (edgePreimage f b).opposite)⁻¹ := by
      have := (blockAverageStep_mem H h hj hV).2 (edgePreimage f b).opposite (mem_univ _)
      rwa [opposite_opposite] at this
    rw [h₂, h₃, h₁]
end
section
variable {i : ℕ}
theorem neg_le_levelDepth (h : Symmetry L n k f σ) : -(n : ℤ) ≤ PeriodicLattice.levelDepth k k := by
  have := h.side_pos
  simp only [PeriodicLattice.levelDepth]
  omega
theorem meanContour_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (pushField f V)
        (PeriodicLattice.sitePreimage σ.symm y) (PeriodicLattice.sitePreimage σ.symm x) =
      PeriodicLattice.complexMeanContourHolonomy V y x := by
  have hidx' : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k (i + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨hdiam, -, -, hid, -⟩ := H.contour L n _ σ h.admissible h.side_pos (neg_le_levelDepth h)
    h.mem_isometries k i hj hidx' y x hx
  have hcfg : V ∈ PeriodicLattice.complexGaugeFields
      (PeriodicLattice.bondsInside (PeriodicLattice.unitBlock y) :
        Set (PeriodicLattice.BondAtLevel L n k i)) :=
    ⟨fun b _ => hV.1.1 b (mem_univ _), fun b _ => hV.1.2 b (mem_univ _)⟩
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  have hd := (mem_domainNearOne_of_small H h hj hV hc).1.2.1 x hx
  rw [pushField_eq_transport h hj.le]
  exact hid V ⟨⟨hcfg, by rw [hdiam V hcfg]; exact hd⟩, ⟨hcfg, hd⟩⟩
theorem finsum_block_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    (y : Vertex L n k (i + 1)) (g G : Vertex L n k i → ComplexMatrix2)
    (hg : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (vertexPreimage f y : Vertex L n k (i + 1)),
      G x = g (PeriodicLattice.sitePreimage σ.symm x)) :
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y, g x =
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (vertexPreimage f y : Vertex L n k (i + 1)), G x := by
  have hle : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k (i + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have h0 : 0 ≤ PeriodicLattice.levelDepth k (i + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hdep : PeriodicLattice.levelDepth k i = PeriodicLattice.levelDepth k (i + 1) + 1 := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hb := ((H.images L n h.admissible h.side_pos _ (neg_le_levelDepth h) σ h.mem_isometries
    (PeriodicLattice.levelDepth k (i + 1)) (PeriodicLattice.levelDepth k i) hle h0 hdep).1
      (vertexPreimage f y : Vertex L n k (i + 1))).1
  have hb' : BijOn (PeriodicLattice.sitePreimage σ.symm)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
        (vertexPreimage f y : Vertex L n k (i + 1)))
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) := by
    have e := sitePreimage_symm_vertexPreimage h (show i + 1 ≤ k from hj) y
    unfold PeriodicLattice.IsometryImages.MapsBlockSites at hb
    rwa [e] at hb
  exact (finsum_mem_eq_of_bijOn _ hb' hg).symm
theorem adjointCubeAverage_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (l : Vertex L n k i → ComplexMatrix2) :
    adjointCubeAverage (pushField f V) (pushSiteFunction f l) =
      pushSiteFunction f (adjointCubeAverage V l) := by
  funext y
  simp only [adjointCubeAverage, pushSiteFunction]
  congr 1
  refine finsum_block_push H h hj y _ _ fun x hx => ?_
  have hc := meanContour_push H h hj hV (vertexPreimage f y) hx
  rw [sitePreimage_symm_vertexPreimage h (show i + 1 ≤ k from hj)] at hc
  rw [hc, vertexPreimage_sitePreimage_symm h hj.le]
end
section
variable {i : ℕ}
theorem expTwist_of_pos {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b := if_pos hb
theorem expTwist_of_not_pos {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹ := if_neg hb
theorem expTwist_line_values (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) {b : Edge L n k i} (hb : b.IsPositivelyOriented) :
    (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b ∈
        PeriodicLattice.complexGaugeGroup) ∧
      HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * V b)
        (Complex.I • B b * V b) 0 :=
  ((H.chartFields.2.2 L k i hL hi).1 n hn).1.1.2 V hV B hB ⟨b, hb⟩
theorem expTwist_mem (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) :
    PeriodicLattice.expTwist B V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  have hp : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • B b) * V b).det = 1 := fun b hb => by
    have := (expTwist_line_values H hL hn hi hV hB hb).1 1
    rwa [one_smul] at this
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_pos hb]
      exact hp b hb
    · rw [expTwist_of_not_pos hb]
      exact det_inv_of_det_eq_one (hp _ (opposite_pos_of_not_pos H hL hn hi hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_not_pos (not_opposite_pos_of_pos H hL hn hi hb), expTwist_of_pos hb,
        opposite_opposite]
    · have hr := opposite_pos_of_not_pos H hL hn hi hb
      rw [expTwist_of_pos hr, expTwist_of_not_pos hb,
        Matrix.nonsing_inv_nonsing_inv _ (by rw [hp _ hr]; exact isUnit_one)]
theorem expTwist_zero_smul (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hi : i ≤ k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_pos hb]
    simp [ComplexMatrix2.matExp]
  · have hr := opposite_pos_of_not_pos H hL hn hi hb
    rw [expTwist_of_not_pos hb]
    have := hV.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at this
    simp [ComplexMatrix2.matExp, this]
theorem eq_of_restrictToPositiveEdges_eq (H : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i ≤ k)
    {V V' : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hV' : V' ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (h : restrictToPositiveEdges V = restrictToPositiveEdges V') : V = V' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact congrFun h ⟨b, hb⟩
  · have hr := opposite_pos_of_not_pos H hL hn hi hb
    have h₁ := hV.2 b.opposite (mem_univ _)
    have h₂ := hV'.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at h₁ h₂
    rw [h₁, h₂, show V b.opposite = V' b.opposite from congrFun h ⟨b.opposite, hr⟩]
theorem eventually_expTwist_mem_small (H : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : i < k) {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k i) (hB : B ∈ complexEdgeForms L n k i) :
    ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • B) V ∈ smallComplexFields L n k i := by
  obtain ⟨-, O, hO, himg⟩ :=
    ((H.meanStable L hL k (by omega)).1 n hn).isOpen_nearOne i hj
  have hV0 : restrictToPositiveEdges V ∈ O := by
    have : restrictToPositiveEdges V ∈ restrictToPositiveEdges ''
        MeanStableFields.fieldsNearOne L n k i :=
      mem_image_of_mem _ hV
    rw [himg] at this
    exact this.1
  have hcont : ContinuousAt
      (fun t : ℂ => restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V)) 0 := by
    refine continuousAt_pi.2 fun b => ?_
    have hd := (expTwist_line_values H hL hn hj.le hV.1 hB b.2).2.continuousAt
    refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
    change _ = PeriodicLattice.expTwist (t • B) V b.1
    rw [expTwist_of_pos b.2]
    rfl
  have h0 : restrictToPositiveEdges (PeriodicLattice.expTwist ((0 : ℂ) • B) V) =
      restrictToPositiveEdges V := by
    rw [expTwist_zero_smul H hL hn hj.le hV.1]
  have hev : ∀ᶠ t : ℂ in 𝓝 0,
      restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈ O :=
    hcont.eventually_mem (by rw [h0]; exact hO.mem_nhds hV0)
  filter_upwards [hev] with t ht
  have hm := expTwist_mem H hL hn hj.le hV.1 ((complexEdgeForms L n k i).smul_mem t hB)
  have hmem : restrictToPositiveEdges (PeriodicLattice.expTwist (t • B) V) ∈
      restrictToPositiveEdges '' MeanStableFields.fieldsNearOne L n k i := by
    rw [himg]
    exact ⟨ht, fun b => hm.1 _ (mem_univ _)⟩
  obtain ⟨W, hW, he⟩ := hmem
  have : W = PeriodicLattice.expTwist (t • B) V :=
    eq_of_restrictToPositiveEdges_eq H hL hn hj.le hW.1 hm he
  exact this ▸ hW
theorem expTwist_push (H : Inputs) (h : Symmetry L n k f σ) (hi : i ≤ k)
    {V B : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k i) (t : ℂ) :
    PeriodicLattice.expTwist (t • isometryOnTangent f V B) (pushField f V) =
      pushField f (PeriodicLattice.expTwist (t • B) V) := by
  rw [← isometryOnTangent_smul]
  exact (((H.chartForms L k i h.admissible hi).1 n h.side_pos) f h.distance
    (h.sublattice_onto i hi) V hV).1 _ ((complexEdgeForms L n k i).smul_mem t hB)
theorem logDirectionalDeriv_congr {α β : Type*} {φ : (α → ComplexMatrix2) → ComplexMatrix2}
    {ψ : (β → ComplexMatrix2) → ComplexMatrix2} {W W' : ComplexMatrix2} {A : α → ComplexMatrix2}
    {A' : β → ComplexMatrix2}
    (h : ∀ᶠ t : ℂ in 𝓝 0, ComplexMatrix2.logSeries (φ (t • A) * W⁻¹) =
      ComplexMatrix2.logSeries (ψ (t • A') * W'⁻¹)) :
    logDirectionalDeriv ℂ φ W A = logDirectionalDeriv ℂ ψ W' A' := by
  unfold logDirectionalDeriv
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [Filter.EventuallyEq.deriv_eq h]
theorem logDeriv_meanContour_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V B : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (hB : B ∈ complexEdgeForms L n k i) (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
      (vertexPreimage f y : Vertex L n k (i + 1))) :
    logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V)
          (vertexPreimage f y : Vertex L n k (i + 1)) x)
        (PeriodicLattice.complexMeanContourHolonomy V
          (vertexPreimage f y : Vertex L n k (i + 1)) x) B =
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy
          (PeriodicLattice.expTwist X (pushField f V)) y
          (PeriodicLattice.sitePreimage σ.symm x))
        (PeriodicLattice.complexMeanContourHolonomy (pushField f V) y
          (PeriodicLattice.sitePreimage σ.symm x))
        (isometryOnTangent f V B) := by
  have hc : ∀ W ∈ smallComplexFields L n k i,
      PeriodicLattice.complexMeanContourHolonomy (pushField f W) y
          (PeriodicLattice.sitePreimage σ.symm x) =
        PeriodicLattice.complexMeanContourHolonomy W
          (vertexPreimage f y : Vertex L n k (i + 1)) x :=
    fun W hW => by
      have := meanContour_push H h hj hW (vertexPreimage f y) hx
      rwa [sitePreimage_symm_vertexPreimage h (show i + 1 ≤ k from hj)] at this
  refine logDirectionalDeriv_congr ?_
  filter_upwards [eventually_expTwist_mem_small H h.admissible h.side_pos hj hV hB] with t ht
  rw [expTwist_push H h hj.le hV.1 hB, hc _ ht, hc _ hV]
theorem contourLogDrift_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V B : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (hB : B ∈ complexEdgeForms L n k i) :
    contourLogDrift (pushField f V) (isometryOnTangent f V B) =
      pushSiteFunction f (contourLogDrift V B) := by
  funext y
  change PeriodicLattice.inverseFourthPowerWeight L • _ =
    PeriodicLattice.inverseFourthPowerWeight L • _
  rw [finsum_block_push H h hj y _ _ fun x hx => logDeriv_meanContour_push H h hj hV hB y hx]
end
section
variable {i : ℕ}
theorem differentiableAt_matrix_inv {M : ComplexMatrix2} (hM : IsUnit M) :
    DifferentiableAt ℂ (fun A : ComplexMatrix2 => A⁻¹) M := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.differentiableAt_inv_of_isUnit <;> assumption
theorem deriv_log_inv_curve (H : Inputs) {X : ℂ → ComplexMatrix2} (hd : DifferentiableAt ℂ X 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hG : ∀ t ∈ Metric.ball (0 : ℂ) ρ, X t ∈ PeriodicLattice.complexGaugeGroup) :
    Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries ((X t)⁻¹ * ((X 0)⁻¹)⁻¹)) 0 =
      -ComplexMatrix2.conjugateBy (X 0)⁻¹
        (Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (X t * (X 0)⁻¹)) 0) := by
  have hA := H.chartFields.2.1 ρ hρ
  obtain ⟨-, -, hX, -⟩ := hA X (fun t ht => hG t ht) hd
  have h0 : (X 0).det = 1 := hG 0 (Metric.mem_ball_self hρ)
  have hu : IsUnit (X 0) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h0]; exact isUnit_one)
  have hYd : DifferentiableAt ℂ (fun t => (X t)⁻¹) 0 :=
    DifferentiableAt.comp (g := fun A : ComplexMatrix2 => A⁻¹) (0 : ℂ)
      (differentiableAt_matrix_inv hu) hd
  obtain ⟨-, -, hY, -⟩ := hA (fun t => (X t)⁻¹)
    (fun t ht => det_inv_of_det_eq_one (hG t ht)) hYd
  have hprod : HasDerivAt (fun t => X t * (X t)⁻¹)
      (deriv X 0 * (X 0)⁻¹ + X 0 * deriv (fun t => (X t)⁻¹) 0) 0 :=
    hd.hasDerivAt.mul hYd.hasDerivAt
  have hone : (fun t => X t * (X t)⁻¹) =ᶠ[𝓝 0] fun _ => (1 : ComplexMatrix2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with t ht
    exact Matrix.mul_nonsing_inv _ (by rw [show (X t).det = 1 from hG t ht]; exact isUnit_one)
  have hz : deriv X 0 * (X 0)⁻¹ + X 0 * deriv (fun t => (X t)⁻¹) 0 = 0 := by
    have := hprod.deriv
    rw [hone.deriv_eq] at this
    simpa using this.symm
  have hY' : deriv (fun t => (X t)⁻¹) 0 = -((X 0)⁻¹ * (deriv X 0 * (X 0)⁻¹)) := by
    have hl : (X 0)⁻¹ * X 0 = 1 :=
      Matrix.nonsing_inv_mul _ (by rw [h0]; exact isUnit_one)
    have := congrArg (fun A => (X 0)⁻¹ * A) hz
    simp only [mul_add, mul_zero, ← mul_assoc, hl, one_mul] at this
    rw [eq_neg_of_add_eq_zero_right this]
    simp only [mul_assoc]
  rw [hY, hX, hY']
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul, neg_mul, smul_neg,
    mul_assoc]
theorem differentiableAt_blockAverage_expTwist (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V B : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (hB : B ∈ complexEdgeForms L n k i) {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    DifferentiableAt ℂ
      (fun t : ℂ => PeriodicLattice.complexBlockAverage
        (PeriodicLattice.expTwist (t • B) V) c) 0 := by
  have hS := ((H.smoothing.1 L h.admissible).2.2).periodic n k i h.side_pos hj c hc
  obtain ⟨⟨inst, -, -, hloc⟩, -⟩ := hS.holomorphic_smoothing
  let _ := inst
  obtain ⟨F, hFa, hev⟩ := hloc (PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c) V)
    ⟨V, mem_nearIdentityPolydisc_of_small H h hj hV hc, rfl⟩
  have hsm := eventually_expTwist_mem_small H h.admissible h.side_pos hj hV hB
  set v : ℂ → PeriodicLattice.PositiveBondOf (PeriodicLattice.bondsInDoubleBlock c :
      Set (Edge L n k i)) → ComplexMatrix2 := fun t =>
    PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c)
      (PeriodicLattice.expTwist (t • B) V) with hvdef
  have hv : DifferentiableAt ℂ v 0 := by
    refine differentiableAt_pi.2 fun b => ?_
    have hd := (expTwist_line_values H h.admissible h.side_pos hj.le hV.1 hB b.2.2).2.differentiableAt
    refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    change PeriodicLattice.expTwist (t • B) V b.1 = _
    rw [expTwist_of_pos b.2.2]
    rfl
  have hv0 : v 0 = PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) V := by
    simp only [hvdef]
    rw [expTwist_zero_smul H h.admissible h.side_pos hj.le hV.1]
  have htend : Tendsto v (𝓝 0) (𝓝[PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c) '' nearIdentityPolydisc (polydiscRadius L) c]
      (PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) V)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hv.continuousAt.tendsto
      rwa [hv0] at this
    · filter_upwards [hsm] with t ht
      exact ⟨_, mem_nearIdentityPolydisc_of_small H h hj ht hc, rfl⟩
  have hev2 := htend.eventually hev
  have hFd : DifferentiableAt ℂ F (v 0) := by
    rw [hv0]
    exact hFa.differentiableAt
  have hFv : DifferentiableAt ℂ (fun t => F (v t) ()) 0 :=
    differentiableAt_pi.1 (DifferentiableAt.comp (0 : ℂ) hFd hv) ()
  refine hFv.congr_of_eventuallyEq ?_
  filter_upwards [hsm, hev2] with t ht hfe
  rw [← congrFun hfe ()]
  refine (H.doubleBlock L h.admissible n k i h.side_pos hj c hc _ _ fun b hb => ?_).average_eq
  by_cases hp : b.IsPositivelyOriented
  · simp only [PeriodicLattice.extendFromPositive, dif_pos (And.intro hb hp)]
    rfl
  · have hr := opposite_pos_of_not_pos H h.admissible h.side_pos hj.le hp
    have hbr : b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)) :=
      ⟨hb.2, hb.1⟩
    have hcfg := ht.1.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at hcfg
    simp only [PeriodicLattice.extendFromPositive, dif_neg (fun q : _ ∧ _ => hp q.2),
      dif_pos (And.intro hbr hr)]
    exact hcfg
theorem complexSmoothingDeriv_push (H : Inputs) (h : Symmetry L n k f σ) (hj : i < k)
    {V B : Edge L n k i → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k i)
    (hB : B ∈ complexEdgeForms L n k i) :
    complexSmoothingDeriv (pushField f V) (isometryOnTangent f V B) =
      isometryOnTangent f (PeriodicLattice.complexBlockAverageStep i V)
        (complexSmoothingDeriv V B) := by
  have hj' : i + 1 ≤ k := hj
  have hsm := eventually_expTwist_mem_small H h.admissible h.side_pos hj hV hB
  have hR : isometryOnTangent f (PeriodicLattice.complexBlockAverageStep i V)
      (complexSmoothingDeriv V B) = extendOddly fun b =>
        tangentEdgeValue (PeriodicLattice.complexBlockAverageStep i V) (complexSmoothingDeriv V B)
          (edgePreimage f b) := rfl
  rw [hR, complexSmoothingDeriv, holLeftDifferential]
  refine extendOddly_congr H h.admissible h.side_pos hj' fun b hb => ?_
  have hM : ∀ᶠ t : ℂ in 𝓝 0,
      PeriodicLattice.complexBlockAverageStep i
          (PeriodicLattice.expTwist (t • isometryOnTangent f V B) (pushField f V)) b =
        PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist (t • B) V)
          (edgePreimage f b) := by
    filter_upwards [hsm] with t ht
    rw [expTwist_push H h hj.le hV.1 hB]
    exact blockAverage_push_of_pos H h hj ht hb
  have hM0 : PeriodicLattice.complexBlockAverageStep i (pushField f V) b =
      PeriodicLattice.complexBlockAverage V (edgePreimage f b) :=
    blockAverage_push_of_pos H h hj hV hb
  by_cases hp : (edgePreimage f b).IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos hp]
    rw [complexSmoothingDeriv, holLeftDifferential, extendOddly_of_pos hp]
    refine logDirectionalDeriv_congr ?_
    filter_upwards [hM] with t ht
    rw [ht, hM0]
    rfl
  · have hc := opposite_pos_of_not_pos H h.admissible h.side_pos hj' hp
    simp only [tangentEdgeValue, if_neg hp]
    rw [complexSmoothingDeriv, holLeftDifferential, extendOddly_of_pos hc]
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hsm
    have hd := differentiableAt_blockAverage_expTwist H h hj hV hB hc
    have hX0 : PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist ((0 : ℂ) • B) V)
        (edgePreimage f b).opposite =
        PeriodicLattice.complexBlockAverage V (edgePreimage f b).opposite := by
      rw [expTwist_zero_smul H h.admissible h.side_pos hj.le hV.1]
    have hinv := deriv_log_inv_curve H hd hε fun t ht =>
      (blockAverageStep_mem H h hj (hball t ht)).1 (edgePreimage f b).opposite (mem_univ _)
    simp only [hX0] at hinv
    have hneg : ∀ W : Edge L n k i → ComplexMatrix2,
        PeriodicLattice.complexBlockAverage W (edgePreimage f b) =
          (PeriodicLattice.complexBlockAverage W (edgePreimage f b).opposite)⁻¹ := fun W => by
      simp only [PeriodicLattice.complexBlockAverage, if_pos hc, if_neg hp]
    unfold logDirectionalDeriv
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = -ComplexMatrix2.conjugateBy
      (PeriodicLattice.complexBlockAverage V (edgePreimage f b).opposite)⁻¹
      (Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries
        (PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist (t • B) V)
          (edgePreimage f b).opposite *
          (PeriodicLattice.complexBlockAverage V (edgePreimage f b).opposite)⁻¹)) 0)
    rw [← hinv]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hM] with t ht
    rw [ht, hM0, hneg, hneg]
end
section
variable {U : Edge L n k 0 → ComplexMatrix2}
theorem complexBlockFieldAtLevel_push (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.complexBlockFieldAtLevel j (pushField f U) =
      pushField f (PeriodicLattice.complexBlockFieldAtLevel j U) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjk : j < k := hj
    change PeriodicLattice.complexBlockAverageStep j
        (PeriodicLattice.complexBlockFieldAtLevel j (pushField f U)) =
      pushField f (PeriodicLattice.complexBlockAverageStep j
        (PeriodicLattice.complexBlockFieldAtLevel j U))
    rw [ih hjk.le]
    exact blockAverageStep_push H h hjk (hU.2 j hjk)
theorem pushField_mem_smallIterateFields (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) : pushField f U ∈ smallIterateFields L n k := by
  refine ⟨(covDiff_covariance H h (Nat.zero_le k) U hU.1).1, fun j hj => ?_⟩
  rw [complexBlockFieldAtLevel_push H h hU hj.le]
  exact pushField_mem_smallComplexFields H h hj.le (hU.2 j hj)
theorem complexBlockFieldAtLevel_mem (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.complexBlockFieldAtLevel j U ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  cases j with
  | zero => exact hU.1
  | succ j => exact blockAverageStep_mem H h hj (hU.2 j hj)
theorem iterAdjointCubeAverage_push (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) (l : Vertex L n k 0 → ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) :
    iterAdjointCubeAverage L n k (pushField f U) j (pushSiteFunction f l) =
      pushSiteFunction f (iterAdjointCubeAverage L n k U j l) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjk : j < k := hj
    change adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j (pushField f U))
        (iterAdjointCubeAverage L n k (pushField f U) j (pushSiteFunction f l)) =
      pushSiteFunction f (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
        (iterAdjointCubeAverage L n k U j l))
    rw [ih hjk.le, complexBlockFieldAtLevel_push H h hU hjk.le]
    exact adjointCubeAverage_push H h hjk (hU.2 j hjk) _
theorem complexIterDeriv_push (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) {j : ℕ} (hj : j ≤ k) :
    complexIterDeriv L n k j (pushField f U) (isometryOnTangent f U B) =
      isometryOnTangent f (PeriodicLattice.complexBlockFieldAtLevel j U)
        (complexIterDeriv L n k j U B) := by
  have hc := H.chain L h.admissible n k h.side_pos U hU B hB
  have hc' := H.chain L h.admissible n k h.side_pos _ (pushField_mem_smallIterateFields H h hU) _
    (isometryOnTangent_mem H h.admissible h.side_pos (Nat.zero_le k) (f := f) hU.1 hB)
  induction j with
  | zero =>
    rw [hc'.1, hc.1]
    rfl
  | succ j ih =>
    have hjk : j < k := hj
    rw [hc'.2.1 j hjk, hc.2.1 j hjk, ih hjk.le, complexBlockFieldAtLevel_push H h hU hjk.le]
    exact complexSmoothingDeriv_push H h hjk (hU.2 j hjk) (hc.2.2 j hjk.le)
theorem iterContourLogDrift_mem (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) {j : ℕ} (hj : j ≤ k) (y : Vertex L n k j) :
    iterContourLogDrift L n k U j B y ∈ ComplexMatrix2.traceless := by
  have hc := H.chain L h.admissible n k h.side_pos U hU B hB
  induction j with
  | zero => exact ComplexMatrix2.traceless.zero_mem
  | succ j ih =>
    have hjk : j < k := hj
    have hl := H.linear L h.admissible n k j h.side_pos hjk _ (hU.2 j hjk)
    exact ComplexMatrix2.traceless.add_mem ((hl.2.2.1 _ (ih hjk.le)).2 y)
      ((hl.1 _ (hc.2.2 j hjk.le)).2 y)
theorem iterContourLogDrift_push (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) {j : ℕ} (hj : j ≤ k) :
    iterContourLogDrift L n k (pushField f U) j (isometryOnTangent f U B) =
      pushSiteFunction f (iterContourLogDrift L n k U j B) := by
  have hc := H.chain L h.admissible n k h.side_pos U hU B hB
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjk : j < k := hj
    change adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j (pushField f U))
        (iterContourLogDrift L n k (pushField f U) j (isometryOnTangent f U B)) +
      contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j (pushField f U))
        (complexIterDeriv L n k j (pushField f U) (isometryOnTangent f U B)) =
      pushSiteFunction f (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
          (iterContourLogDrift L n k U j B) +
        contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U)
          (complexIterDeriv L n k j U B))
    rw [ih hjk.le, complexIterDeriv_push H h hU hB hjk.le,
      complexBlockFieldAtLevel_push H h hU hjk.le,
      adjointCubeAverage_push H h hjk (hU.2 j hjk),
      contourLogDrift_push H h hjk (hU.2 j hjk) (hc.2.2 j hjk.le)]
    rfl
theorem iterCovariantDeriv_push (H : Inputs) (h : Symmetry L n k f σ)
    (hU : U ∈ smallIterateFields L n k) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) {j : ℕ} (hj : j ≤ k) :
    iterCovariantDeriv L n k (pushField f U) j (isometryOnTangent f U B) =
      isometryOnTangent f (PeriodicLattice.complexBlockFieldAtLevel j U)
        (iterCovariantDeriv L n k U j B) := by
  have hr := (H.relations L h.admissible n k j h.side_pos hj U hU).1 B hB
  have hr' := (H.relations L h.admissible n k j h.side_pos hj _
    (pushField_mem_smallIterateFields H h hU)).1 _
    (isometryOnTangent_mem H h.admissible h.side_pos (Nat.zero_le k) (f := f) hU.1 hB)
  rw [hr', hr, complexIterDeriv_push H h hU hB hj, complexBlockFieldAtLevel_push H h hU hj,
    iterContourLogDrift_push H h hU hB hj,
    (covDiff_covariance H h hj _ (complexBlockFieldAtLevel_mem H h hU hj)).2 _
      (iterContourLogDrift_mem H h hU hB hj),
    isometryOnTangent_add]
end
theorem iteratesIsometryCovariant (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hTr : Translations.TranslationProperties)
    (hF : LeftChartIsometryEquivariance)
    (hA : LeftChartFields.Claim)
    (hS : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hP : SmoothingNearIdentity)
    (hC : ComplexIterDerivChain)
    (hR : CovariantIterRelations)
    (hLin : StepMapsComplexLinear.Claim)
    (hX : PeriodicLattice.LevelBondOrientationDichotomy)
    (hM : PeriodicLattice.ComplexAverageEquivariance)
    (hK : PeriodicLattice.ComplexContourHolonomyCovariance)
    (hI : PeriodicLattice.IsometryImages.Statement)
    (hD : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock) : IteratesIsometryCovariant := by
  intro L hL n k j hn hj f hf hm U hU
  have H : Inputs := ⟨hT, hTr, hF, hA, hS, hO, hP, hC, hR, hLin, hX, hM, hK, hI, hD⟩
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨⟨w, hw, v, hv, hwv⟩, hrest⟩ := (hT L hL0 hL k).2.2.2.1 n hn k le_rfl f hf hm
  obtain ⟨σ, hσf, hσ⟩ := exists_latticeIsometry_of_affine hw hv hwv
  have h : Symmetry L n k f σ :=
    ⟨hL, hn, hσf, hf, fun i hi => (hrest i hi).1, fun i hi => (hrest i hi).2.1, hσ⟩
  exact ⟨fun l hl => ⟨(covDiff_covariance H h (Nat.zero_le k) U hU.1).2 l hl,
      iterAdjointCubeAverage_push H h hU l hj⟩,
    fun B hB => ⟨complexIterDeriv_push H h hU hB hj, iterCovariantDeriv_push H h hU hB hj,
      iterContourLogDrift_push H h hU hB hj⟩⟩
end YangMills.Construction.Tower.IteratesCovariance
end
