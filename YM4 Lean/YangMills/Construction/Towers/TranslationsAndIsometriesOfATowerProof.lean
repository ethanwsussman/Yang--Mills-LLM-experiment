import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.Matrices.ConjugationOnTraceless
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATower
import YangMills.Construction.Towers.WhatTheDilationKeepsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace Translations
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec colourVertices colourEdges colourFaces)
open QuotientLattices (NeighboursAtSpacing AreNeighbours IsSignedAxisStep)
theorem latticeSubgroup_meshAt_le {L k i j : ℕ} (hL : (L : ℝ) ≠ 0) (h : i ≤ j) :
    InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  rintro x ⟨N, hN⟩
  refine ⟨fun μ => N μ * (L : ℤ) ^ (j - i), fun μ => ?_⟩
  have hs : meshAt L k j = (L : ℝ) ^ (j - i) * meshAt L k i := by
    unfold meshAt
    rw [← zpow_natCast, ← zpow_add₀ hL]
    congr 1
    omega
  rw [hN μ, hs]
  push_cast
  ring
theorem castVec_mem_latticeSubgroup_top (L k : ℕ) (N : Fin 4 → ℤ) :
    castVec N ∈ InfiniteLattice.latticeSubgroup (meshAt L k k) :=
  ⟨N, fun μ => by simp [castVec, meshAt]⟩
theorem image_addRight_subgroup {T : Type*} [AddCommGroup T] (H : AddSubgroup T) {c : T}
    (hc : c ∈ H) (f : T → T) (hf : ∀ z, f z = z + c) : f '' (H : Set T) = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hf]
    exact H.add_mem hx hc
  · intro hy
    exact ⟨y - c, H.sub_mem hy hc, by rw [hf]; abel⟩
theorem conjugateBy_inv_neg_sub (hA : Matrices.ComplexMatrix2.ConjugationPreservesTraceless)
    {g X Y : Matrices.ComplexMatrix2} (hg : g ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    -Matrices.ComplexMatrix2.conjugateBy g⁻¹ (Matrices.ComplexMatrix2.conjugateBy g X - Y) =
      Matrices.ComplexMatrix2.conjugateBy g⁻¹ Y - X := by
  have hc : Matrices.ComplexMatrix2.conjugateBy g⁻¹ (Matrices.ComplexMatrix2.conjugateBy g X) = X :=
    ((hA.2.2 g (hA.1 g hg)).2.2.2.2.2.2.2 X hX).1
  have hs : Matrices.ComplexMatrix2.conjugateBy g⁻¹ (Matrices.ComplexMatrix2.conjugateBy g X - Y) =
      Matrices.ComplexMatrix2.conjugateBy g⁻¹ (Matrices.ComplexMatrix2.conjugateBy g X) -
        Matrices.ComplexMatrix2.conjugateBy g⁻¹ Y := by
    simp only [Matrices.ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
  rw [hs, hc]
  abel
section OnTheTorus
variable {L n k i : ℕ}
theorem torusProj_mem_sublattice {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L n) v ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) := by
  obtain ⟨N, hN⟩ := hv
  refine ⟨N, fun μ => ?_⟩
  show ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = _
  rw [hN μ, meshSize_levelDepth]
def translateEdge (c : Vertex L n k i) (b : Edge L n k i) : Edge L n k i :=
  ⟨b.source + c, b.target + c, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
theorem translateEdge_isPositivelyOriented (c : Vertex L n k i) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : (translateEdge c b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨μ, ?_⟩
  show b.target + c - (b.source + c) = _
  rw [add_sub_add_right_eq_sub, h]
theorem edgeImage_eq_translateEdge
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n} {c : Vertex L n k i}
    (hm : ∀ x : Vertex L n k i, vertexImage f x = x + c) (b : Edge L n k i) :
    edgeImage f b = translateEdge c b := by
  have spec : (edgeImage f b).source = vertexImage f b.source ∧
      (edgeImage f b).target = vertexImage f b.target :=
    Classical.epsilon_spec
      (p := fun b' : Edge L n k i =>
        b'.source = vertexImage f b.source ∧ b'.target = vertexImage f b.target)
      ⟨translateEdge c b, (hm _).symm, (hm _).symm⟩
  exact PeriodicLattice.Bond.ext (spec.1.trans (hm _)) (spec.2.trans (hm _))
theorem vertexImage_torusShift {v : AmbientSpace}
    (hc : TorusMetric.torusProj (PeriodicLattice.torusSide L n) v ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i))
    (x : Vertex L n k i) :
    vertexImage (torusShift L n v) x = x + (⟨_, hc⟩ : Vertex L n k i) :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : Vertex L n k i =>
      (x' : PeriodicLattice.FourTorus L n) = torusShift L n v x)
    ⟨x + (⟨_, hc⟩ : Vertex L n k i), rfl⟩)
theorem torusShift_neg_torusShift (v : AmbientSpace) (z : PeriodicLattice.FourTorus L n) :
    torusShift L n (-v) (torusShift L n v z) = z := by
  funext μ
  simp [torusShift, TorusMetric.torusProj]
theorem torusShift_torusShift_neg (v : AmbientSpace) (z : PeriodicLattice.FourTorus L n) :
    torusShift L n v (torusShift L n (-v) z) = z := by
  funext μ
  simp [torusShift, TorusMetric.torusProj]
theorem torusShift_isDistancePreserving (v : AmbientSpace) :
    IsDistancePreserving (L := L) (n := n) (torusShift L n v) := by
  intro a b
  simp only [torusShift, add_sub_add_right_eq_sub]
theorem torusShift_mapsSublatticeOnto {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) :
    MapsSublatticeOnto (L := L) (n := n) k i (torusShift L n v) :=
  image_addRight_subgroup _ (torusProj_mem_sublattice hv) _ fun _ => rfl
theorem torusShift_local_structure {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i)) (x : Vertex L n k i) :
    ((vertexImage (torusShift L n v) x : Vertex L n k i) : PeriodicLattice.FourTorus L n) =
      torusShift L n v x ∧
    (∀ μ : Fin 4, edgeImage (k := k) (j := i) (torusShift L n v)
        (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (vertexImage (torusShift L n v) x) μ) ∧
    ∀ (μ ν : Fin 4) (h : μ < ν),
      vertexImage (torusShift L n v) ''
          PeriodicLattice.Plaquette.vertices (⟨x, μ, ν, h⟩ : Face L n k i) =
        PeriodicLattice.Plaquette.vertices
          (⟨vertexImage (torusShift L n v) x, μ, ν, h⟩ : Face L n k i) ∧
      ∀ r : Fin 4, edgeImage (k := k) (j := i) (torusShift L n v)
          (faceEdges (⟨x, μ, ν, h⟩ : Face L n k i) r) =
        faceEdges (⟨vertexImage (torusShift L n v) x, μ, ν, h⟩ : Face L n k i) r := by
  have hc := torusProj_mem_sublattice (L := L) (n := n) hv
  have hm := vertexImage_torusShift (L := L) (n := n) (k := k) (i := i) hc
  have hfwd : ∀ (y : Vertex L n k i) (μ : Fin 4),
      edgeImage (k := k) (j := i) (torusShift L n v) (PeriodicLattice.Bond.forwardFrom y μ) =
        PeriodicLattice.Bond.forwardFrom (vertexImage (torusShift L n v) y) μ := by
    intro y μ
    rw [edgeImage_eq_translateEdge hm, hm]
    refine PeriodicLattice.Bond.ext rfl ?_
    show y + PeriodicLattice.unitStep L n _ μ + _ = y + _ + PeriodicLattice.unitStep L n _ μ
    abel
  refine ⟨by rw [hm]; rfl, hfwd x, fun μ ν h => ⟨?_, fun r => ?_⟩⟩
  · simp only [PeriodicLattice.Plaquette.vertices, Set.image_insert_eq, Set.image_singleton, hm]
    rw [add_right_comm (x + PeriodicLattice.unitStep L n _ μ) (PeriodicLattice.unitStep L n _ ν),
      add_right_comm x (PeriodicLattice.unitStep L n _ μ),
      add_right_comm x (PeriodicLattice.unitStep L n _ ν)]
  · have hstep : ∀ μ' : Fin 4,
        vertexImage (torusShift L n v) (x + PeriodicLattice.unitStep L n _ μ') =
          vertexImage (torusShift L n v) x + PeriodicLattice.unitStep L n _ μ' := by
      intro μ'
      rw [hm, hm]
      abel
    fin_cases r
    · exact hfwd x μ
    · exact (hfwd _ ν).trans (by rw [hstep]; rfl)
    · exact (hfwd _ μ).trans (by rw [hstep]; rfl)
    · exact hfwd x ν
theorem torusShift_respectsLevels {j : ℕ} (hL : (L : ℝ) ≠ 0) {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j)) :
    ShiftRespectsLevels L n k j v :=
  ⟨fun x => by
      funext μ
      simp [torusShift, TorusMetric.torusProj],
    torusShift_isDistancePreserving v,
    fun _ hi => torusShift_mapsSublatticeOnto (latticeSubgroup_meshAt_le hL hi hv),
    torusShift_neg_torusShift v,
    torusShift_torusShift_neg v,
    fun _ hi x => torusShift_local_structure (latticeSubgroup_meshAt_le hL hi hv) x⟩
theorem opposite_isPositivelyOriented_of_not (b : Edge L n k i)
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem extendOddly_congr {g g' : Edge L n k i → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k i, b.IsPositivelyOriented → g b = g' b) :
    extendOddly g = extendOddly g' := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem apply_vertexPreimage {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : MapsSublatticeOnto k i f) (x : Vertex L n k i) : f (vertexPreimage f x) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgePreimage_endpoints
    (hP : NeighboursAtSpacing (QuotientLattices.torusDist L n)
      (PeriodicLattice.sublattice L n (QuotientLattices.refinementIndex k i))
      (PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k i))
      (QuotientLattices.torusAxisSteps L n k i))
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hi : IsDistancePreserving f) (hf : MapsSublatticeOnto k i f) (b : Edge L n k i) :
    (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target := by
  obtain ⟨hinj, -, hinv⟩ := hP.2 f hi hf
  have key : ∀ y : Vertex L n k i,
      Function.invFunOn f (PeriodicLattice.sublattice L n
        (QuotientLattices.refinementIndex k i) : Set (PeriodicLattice.FourTorus L n))
        (y : PeriodicLattice.FourTorus L n) = (vertexPreimage f y : Vertex L n k i) := by
    intro y
    have hex : ∃ a ∈ (PeriodicLattice.sublattice L n
        (QuotientLattices.refinementIndex k i) : Set (PeriodicLattice.FourTorus L n)),
        f a = (y : PeriodicLattice.FourTorus L n) :=
      ⟨_, (vertexPreimage f y).2, apply_vertexPreimage hf y⟩
    exact hinj (Function.invFunOn_mem hex) (vertexPreimage f y).2
      ((Function.invFunOn_eq hex).trans (apply_vertexPreimage hf y).symm)
  have hpair : AreNeighbours (QuotientLattices.torusAxisSteps L n k i)
      (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) := by
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · refine ⟨1, μ, ?_⟩
      have := congrArg (Subtype.val) h
      simpa [IsSignedAxisStep, QuotientLattices.torusAxisSteps] using this
    · refine ⟨-1, μ, ?_⟩
      have := congrArg (Subtype.val) h
      simpa [IsSignedAxisStep, QuotientLattices.torusAxisSteps] using this
  obtain ⟨ε, μ, hstep⟩ := hinv _ b.source.2 _ b.target.2 hpair
  have hstep' : ((vertexPreimage f b.target : Vertex L n k i) : PeriodicLattice.FourTorus L n) -
      (vertexPreimage f b.source : Vertex L n k i) =
        (ε : ℤ) • QuotientLattices.torusAxisSteps L n k i μ := by
    have := hstep
    rw [IsSignedAxisStep, key, key] at this
    exact this
  have hadj : ∃ μ : Fin 4, vertexPreimage f b.target - vertexPreimage f b.source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ ∨
      vertexPreimage f b.target - vertexPreimage f b.source =
        -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ := by
    refine ⟨μ, ?_⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [QuotientLattices.torusAxisSteps] using hstep'))
    · exact Or.inr (Subtype.ext (by simpa [QuotientLattices.torusAxisSteps] using hstep'))
  exact Classical.epsilon_spec
    (p := fun b' : Edge L n k i =>
      b'.source = vertexPreimage f b.source ∧ b'.target = vertexPreimage f b.target)
    ⟨⟨vertexPreimage f b.source, vertexPreimage f b.target, hadj⟩, rfl, rfl⟩
theorem extendOddly_of_pos {g : Edge L n k i → Matrices.ComplexMatrix2} {b : Edge L n k i}
    (h : b.IsPositivelyOriented) : extendOddly g b = g b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem covDiff_of_pos {U : Edge L n k i → Matrices.ComplexMatrix2}
    {l : Vertex L n k i → Matrices.ComplexMatrix2} {b : Edge L n k i}
    (h : b.IsPositivelyOriented) :
    covDiff U l b = Matrices.ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source :=
  extendOddly_of_pos h
theorem edgePreimage_opposite
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (ends : ∀ b : Edge L n k i, (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target) (b : Edge L n k i) :
    edgePreimage f b.opposite = (edgePreimage f b).opposite :=
  PeriodicLattice.Bond.ext ((ends b.opposite).1.trans (ends b).2.symm)
    ((ends b.opposite).2.trans (ends b).1.symm)
theorem covDiff_pushField (hA : Matrices.ComplexMatrix2.ConjugationPreservesTraceless)
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (ends : ∀ b : Edge L n k i, (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target)
    {U : Edge L n k i → Matrices.ComplexMatrix2}
    (hdet : ∀ b, U b ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hrev : ∀ b : Edge L n k i, U b.opposite = (U b)⁻¹)
    {l : Vertex L n k i → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    covDiff (pushField f U) (pushSiteFunction f l) =
      isometryOnTangent f U (covDiff U l) := by
  show extendOddly _ = extendOddly _
  refine extendOddly_congr fun b _ => ?_
  show Matrices.ComplexMatrix2.conjugateBy (U (edgePreimage f b)) (l (vertexPreimage f b.target)) -
      l (vertexPreimage f b.source) =
    tangentEdgeValue U (covDiff U l) (edgePreimage f b)
  obtain ⟨ht, hh⟩ := ends b
  rw [← ht, ← hh]
  generalize edgePreimage f b = c
  unfold tangentEdgeValue
  by_cases hp : c.IsPositivelyOriented
  · rw [if_pos hp, covDiff_of_pos hp]
  · have hr := opposite_isPositivelyOriented_of_not c hp
    have hU : U c = (U c.opposite)⁻¹ := hrev c.opposite
    rw [if_neg hp, covDiff_of_pos hr, hU]
    exact (conjugateBy_inv_neg_sub hA (hdet _) (hl _)).symm
theorem vertexPreimage_torusShift {v : AmbientSpace}
    (hc : TorusMetric.torusProj (PeriodicLattice.torusSide L n) v ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i))
    (x : Vertex L n k i) :
    vertexPreimage (torusShift L n v) x = x + -(⟨_, hc⟩ : Vertex L n k i) := by
  have spec : ((vertexPreimage (torusShift L n v) x : Vertex L n k i) :
      PeriodicLattice.FourTorus L n) + TorusMetric.torusProj (PeriodicLattice.torusSide L n) v =
        x :=
    Classical.epsilon_spec
      (p := fun x' : Vertex L n k i => torusShift L n v x' = x)
      ⟨x + -(⟨_, hc⟩ : Vertex L n k i), by
        show (x : PeriodicLattice.FourTorus L n) +
            -TorusMetric.torusProj (PeriodicLattice.torusSide L n) v +
          TorusMetric.torusProj (PeriodicLattice.torusSide L n) v = x
        abel⟩
  exact Subtype.ext (eq_add_neg_of_add_eq spec)
theorem edgePreimage_eq_translateEdge
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n} {c : Vertex L n k i}
    (hm : ∀ x : Vertex L n k i, vertexPreimage f x = x + c) (b : Edge L n k i) :
    edgePreimage f b = translateEdge c b := by
  have spec : (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target :=
    Classical.epsilon_spec
      (p := fun b' : Edge L n k i =>
        b'.source = vertexPreimage f b.source ∧ b'.target = vertexPreimage f b.target)
      ⟨translateEdge c b, (hm _).symm, (hm _).symm⟩
  exact PeriodicLattice.Bond.ext (spec.1.trans (hm _)) (spec.2.trans (hm _))
theorem covDiffEquivariant_torus {j : ℕ} (hL : (L : ℝ) ≠ 0) (hj : j ≤ k)
    (hP : NeighboursAtSpacing (QuotientLattices.torusDist L n)
      (PeriodicLattice.sublattice L n (QuotientLattices.refinementIndex k j))
      (PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k j))
      (QuotientLattices.torusAxisSteps L n k j))
    (hA : Matrices.ComplexMatrix2.ConjugationPreservesTraceless) :
    CovDiffEquivariant L n k j := by
  refine ⟨fun v hv => ⟨torusShift_isDistancePreserving v, torusShift_mapsSublatticeOnto hv⟩,
    fun N => latticeSubgroup_meshAt_le hL hj (castVec_mem_latticeSubgroup_top L k N),
    fun f hi hf U hU => ?_, fun v hv b hb => ?_⟩
  · have ends := edgePreimage_endpoints (k := k) (i := j) hP hi hf
    obtain ⟨hU₁, hU₂⟩ :
        PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U := hU
    refine ⟨⟨fun b _ => hU₁ _ (mem_univ _), fun b _ => ?_⟩,
      fun l hl => covDiff_pushField hA ends (fun b => hU₁ b (mem_univ b))
        (fun b => hU₂ b (mem_univ b)) hl⟩
    show U (edgePreimage f b.opposite) = (U (edgePreimage f b))⁻¹
    rw [edgePreimage_opposite ends b]
    exact hU₂ _ (mem_univ _)
  · have hc := torusProj_mem_sublattice (L := L) (n := n) hv
    have heq := edgePreimage_eq_translateEdge
      (vertexPreimage_torusShift (L := L) (n := n) (k := k) (i := j) hc) b
    have hpos : (edgePreimage (k := k) (j := j) (torusShift L n v) b).IsPositivelyOriented := by
      rw [heq]
      exact translateEdge_isPositivelyOriented _ hb
    refine ⟨hpos, fun U _ B _ => ?_⟩
    show extendOddly _ b = _
    rw [extendOddly_of_pos hb]
    show tangentEdgeValue U B (edgePreimage (torusShift L n v) b) = _
    unfold tangentEdgeValue
    rw [if_pos hpos]
end OnTheTorus
end Translations
namespace FullSpace.Translations
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec colourVertices colourEdges colourFaces)
open QuotientLattices (NeighboursAtSpacing AreNeighbours IsSignedAxisStep)
section SingleMesh
variable {a : ℝ}
def translateLink (c : InfiniteLattice.LatticePoint a) (b : InfiniteLattice.Link a) :
    InfiniteLattice.Link a :=
  ⟨b.initial + c, b.terminal + c, by
    obtain ⟨μ, h⟩ := b.isAdjacent
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
theorem translateLink_isPositivelyOriented (c : InfiniteLattice.LatticePoint a)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    (translateLink c b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨μ, ?_⟩
  show b.terminal + c - (b.initial + c) = _
  rw [add_sub_add_right_eq_sub, h]
theorem edgeImage_eq_translateLink {f : AmbientSpace → AmbientSpace}
    {c : InfiniteLattice.LatticePoint a}
    (hm : ∀ x : InfiniteLattice.LatticePoint a, vertexImage f x = x + c)
    (b : InfiniteLattice.Link a) :
    edgeImage f b = translateLink c b := by
  have spec : (edgeImage f b).initial = vertexImage f b.initial ∧
      (edgeImage f b).terminal = vertexImage f b.terminal :=
    Classical.epsilon_spec
      (p := fun b' : InfiniteLattice.Link a =>
        b'.initial = vertexImage f b.initial ∧ b'.terminal = vertexImage f b.terminal)
      ⟨translateLink c b, (hm _).symm, (hm _).symm⟩
  exact InfiniteLattice.Link.ext (spec.1.trans (hm _)) (spec.2.trans (hm _))
theorem vertexImage_spaceShift {v : AmbientSpace} (hc : v ∈ InfiniteLattice.latticeSubgroup a)
    (x : InfiniteLattice.LatticePoint a) :
    vertexImage (spaceShift v) x = x + (⟨v, hc⟩ : InfiniteLattice.LatticePoint a) :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a => (x' : AmbientSpace) = spaceShift v x)
    ⟨x + (⟨v, hc⟩ : InfiniteLattice.LatticePoint a), rfl⟩)
theorem spaceShift_isDistancePreserving (v : AmbientSpace) :
    IsDistancePreserving (spaceShift v) := by apply _root_.YangMills.Construction.SeparatedTuples.isEuclidIsometry_translate <;> assumption
theorem spaceShift_mapsSublatticeOnto {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup a) :
    MapsSublatticeOnto a (spaceShift v) :=
  _root_.YangMills.Construction.Tower.Translations.image_addRight_subgroup _ hv _ fun _ => rfl
theorem spaceShift_local_structure {v : AmbientSpace} (hv : v ∈ InfiniteLattice.latticeSubgroup a)
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage (spaceShift v) x : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      spaceShift v x ∧
    (∀ μ : Fin 4, edgeImage (spaceShift v) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (vertexImage (spaceShift v) x) μ) ∧
    ∀ (μ ν : Fin 4) (h : μ < ν),
      vertexImage (spaceShift v) ''
          faceCorners (⟨x, μ, ν, h⟩ : InfiniteLattice.ElementaryPlaquette a) =
        faceCorners
          (⟨vertexImage (spaceShift v) x, μ, ν, h⟩ : InfiniteLattice.ElementaryPlaquette a) ∧
      ∀ r : Fin 4, edgeImage (spaceShift v)
          (faceEdges (⟨x, μ, ν, h⟩ : InfiniteLattice.ElementaryPlaquette a) r) =
        faceEdges
          (⟨vertexImage (spaceShift v) x, μ, ν, h⟩ : InfiniteLattice.ElementaryPlaquette a) r := by
  have hm := vertexImage_spaceShift (a := a) hv
  have hfwd : ∀ (y : InfiniteLattice.LatticePoint a) (μ : Fin 4),
      edgeImage (spaceShift v) (InfiniteLattice.Link.forwardFrom y μ) =
        InfiniteLattice.Link.forwardFrom (vertexImage (spaceShift v) y) μ := by
    intro y μ
    rw [edgeImage_eq_translateLink hm, hm]
    refine InfiniteLattice.Link.ext rfl ?_
    show y + InfiniteLattice.axisStep a μ + _ = y + _ + InfiniteLattice.axisStep a μ
    abel
  refine ⟨by rw [hm]; rfl, hfwd x, fun μ ν h => ⟨?_, fun r => ?_⟩⟩
  · simp only [faceCorners, Set.image_insert_eq, Set.image_singleton, hm]
    rw [add_right_comm (x + InfiniteLattice.axisStep a μ) (InfiniteLattice.axisStep a ν),
      add_right_comm x (InfiniteLattice.axisStep a μ),
      add_right_comm x (InfiniteLattice.axisStep a ν)]
  · have hstep : ∀ μ' : Fin 4,
        vertexImage (spaceShift v) (x + InfiniteLattice.axisStep a μ') =
          vertexImage (spaceShift v) x + InfiniteLattice.axisStep a μ' := by
      intro μ'
      rw [hm, hm]
      abel
    fin_cases r
    · exact hfwd x μ
    · exact (hfwd _ ν).trans (by rw [hstep]; rfl)
    · exact (hfwd _ μ).trans (by rw [hstep]; rfl)
    · exact hfwd x ν
theorem link_opposite_isPositivelyOriented_of_not (b : InfiniteLattice.Link a)
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_congr {g g' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → g b = g' b) :
    extendOddly g = extendOddly g' := by
  funext b
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, if_pos hb, h b hb]
  · rw [if_neg hb, if_neg hb, h _ (link_opposite_isPositivelyOriented_of_not b hb)]
theorem apply_vertexPreimage {f : AmbientSpace → AmbientSpace} (hf : MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) : f (vertexPreimage f x) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgePreimage_endpoints
    (hP : NeighboursAtSpacing QuotientLattices.spaceDist
      (InfiniteLattice.latticeSubgroup a) a (QuotientLattices.spaceAxisSteps a))
    {f : AmbientSpace → AmbientSpace} (hi : IsDistancePreserving f)
    (hf : MapsSublatticeOnto a f) (b : InfiniteLattice.Link a) :
    (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal := by
  obtain ⟨hinj, -, hinv⟩ := hP.2 f hi hf
  have key : ∀ y : InfiniteLattice.LatticePoint a,
      Function.invFunOn f (InfiniteLattice.latticeSubgroup a : Set AmbientSpace)
        (y : AmbientSpace) = (vertexPreimage f y : InfiniteLattice.LatticePoint a) := by
    intro y
    have hex : ∃ x ∈ (InfiniteLattice.latticeSubgroup a : Set AmbientSpace),
        f x = (y : AmbientSpace) :=
      ⟨_, (vertexPreimage f y).2, apply_vertexPreimage hf y⟩
    exact hinj (Function.invFunOn_mem hex) (vertexPreimage f y).2
      ((Function.invFunOn_eq hex).trans (apply_vertexPreimage hf y).symm)
  have hpair : AreNeighbours (QuotientLattices.spaceAxisSteps a)
      (b.initial : AmbientSpace) (b.terminal : AmbientSpace) := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · refine ⟨1, μ, ?_⟩
      have := congrArg (Subtype.val) h
      simpa [IsSignedAxisStep, QuotientLattices.spaceAxisSteps] using this
    · refine ⟨-1, μ, ?_⟩
      have := congrArg (Subtype.val) h
      simpa [IsSignedAxisStep, QuotientLattices.spaceAxisSteps] using this
  obtain ⟨ε, μ, hstep⟩ := hinv _ b.initial.2 _ b.terminal.2 hpair
  have hstep' : ((vertexPreimage f b.terminal : InfiniteLattice.LatticePoint a) : AmbientSpace) -
      (vertexPreimage f b.initial : InfiniteLattice.LatticePoint a) =
        (ε : ℤ) • QuotientLattices.spaceAxisSteps a μ := by
    have := hstep
    rw [IsSignedAxisStep, key, key] at this
    exact this
  have hadj : ∃ μ : Fin 4, vertexPreimage f b.terminal - vertexPreimage f b.initial =
        InfiniteLattice.axisStep a μ ∨
      vertexPreimage f b.terminal - vertexPreimage f b.initial =
        -InfiniteLattice.axisStep a μ := by
    refine ⟨μ, ?_⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [QuotientLattices.spaceAxisSteps] using hstep'))
    · exact Or.inr (Subtype.ext (by simpa [QuotientLattices.spaceAxisSteps] using hstep'))
  exact Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexPreimage f b.initial ∧ b'.terminal = vertexPreimage f b.terminal)
    ⟨⟨vertexPreimage f b.initial, vertexPreimage f b.terminal, hadj⟩, rfl, rfl⟩
theorem extendOddly_of_pos {g : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {b : InfiniteLattice.Link a} (h : b.IsPositivelyOriented) : extendOddly g b = g b :=
  if_pos h
theorem covDiff_of_pos {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2} {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) :
    covDiff U l b = Matrices.ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial :=
  extendOddly_of_pos h
theorem edgePreimage_opposite {f : AmbientSpace → AmbientSpace}
    (ends : ∀ b : InfiniteLattice.Link a, (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal) (b : InfiniteLattice.Link a) :
    edgePreimage f b.opposite = (edgePreimage f b).opposite :=
  InfiniteLattice.Link.ext ((ends b.opposite).1.trans (ends b).2.symm)
    ((ends b.opposite).2.trans (ends b).1.symm)
theorem covDiff_pushField (hA : Matrices.ComplexMatrix2.ConjugationPreservesTraceless)
    {f : AmbientSpace → AmbientSpace}
    (ends : ∀ b : InfiniteLattice.Link a, (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal)
    {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hdet : ∀ b, U b ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hrev : ∀ b : InfiniteLattice.Link a, U b.opposite = (U b)⁻¹)
    {l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    covDiff (pushField f U) (pushSiteFunction f l) =
      isometryOnTangent f U (covDiff U l) := by
  show extendOddly _ = extendOddly _
  refine extendOddly_congr fun b _ => ?_
  show Matrices.ComplexMatrix2.conjugateBy (U (edgePreimage f b)) (l (vertexPreimage f b.terminal)) -
      l (vertexPreimage f b.initial) =
    tangentEdgeValue U (covDiff U l) (edgePreimage f b)
  obtain ⟨ht, hh⟩ := ends b
  rw [← ht, ← hh]
  generalize edgePreimage f b = c
  unfold tangentEdgeValue
  by_cases hp : c.IsPositivelyOriented
  · rw [if_pos hp, covDiff_of_pos hp]
  · have hr := link_opposite_isPositivelyOriented_of_not c hp
    have hU : U c = (U c.opposite)⁻¹ := hrev c.opposite
    rw [if_neg hp, covDiff_of_pos hr, hU]
    exact (_root_.YangMills.Construction.Tower.Translations.conjugateBy_inv_neg_sub hA
      (hdet _) (hl _)).symm
theorem vertexPreimage_spaceShift {v : AmbientSpace} (hc : v ∈ InfiniteLattice.latticeSubgroup a)
    (x : InfiniteLattice.LatticePoint a) :
    vertexPreimage (spaceShift v) x = x + -(⟨v, hc⟩ : InfiniteLattice.LatticePoint a) := by
  have spec : ((vertexPreimage (spaceShift v) x : InfiniteLattice.LatticePoint a) :
      AmbientSpace) + v = x :=
    Classical.epsilon_spec
      (p := fun x' : InfiniteLattice.LatticePoint a => spaceShift v x' = x)
      ⟨x + -(⟨v, hc⟩ : InfiniteLattice.LatticePoint a), by
        show (x : AmbientSpace) + -v + v = x
        abel⟩
  exact Subtype.ext (eq_add_neg_of_add_eq spec)
theorem edgePreimage_eq_translateLink {f : AmbientSpace → AmbientSpace}
    {c : InfiniteLattice.LatticePoint a}
    (hm : ∀ x : InfiniteLattice.LatticePoint a, vertexPreimage f x = x + c)
    (b : InfiniteLattice.Link a) :
    edgePreimage f b = translateLink c b := by
  have spec : (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal :=
    Classical.epsilon_spec
      (p := fun b' : InfiniteLattice.Link a =>
        b'.initial = vertexPreimage f b.initial ∧ b'.terminal = vertexPreimage f b.terminal)
      ⟨translateLink c b, (hm _).symm, (hm _).symm⟩
  exact InfiniteLattice.Link.ext (spec.1.trans (hm _)) (spec.2.trans (hm _))
end SingleMesh
variable {L k : ℕ}
theorem spaceShift_respectsLevels {j : ℕ} (hL : (L : ℝ) ≠ 0) {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j)) :
    ShiftRespectsLevels L k j v :=
  ⟨spaceShift_isDistancePreserving v,
    fun _ hi => spaceShift_mapsSublatticeOnto
      (_root_.YangMills.Construction.Tower.Translations.latticeSubgroup_meshAt_le hL hi hv),
    fun z => by simp [spaceShift],
    fun z => by simp [spaceShift],
    fun _ hi x => spaceShift_local_structure
      (_root_.YangMills.Construction.Tower.Translations.latticeSubgroup_meshAt_le hL hi hv) x⟩
theorem covDiffEquivariant_space {j : ℕ} (hL : (L : ℝ) ≠ 0) (hj : j ≤ k)
    (hP : NeighboursAtSpacing QuotientLattices.spaceDist
      (InfiniteLattice.latticeSubgroup (meshAt L k j)) (meshAt L k j)
      (QuotientLattices.spaceAxisSteps (meshAt L k j)))
    (hA : Matrices.ComplexMatrix2.ConjugationPreservesTraceless) :
    CovDiffEquivariant L k j := by
  refine ⟨fun v hv => ⟨spaceShift_isDistancePreserving v, spaceShift_mapsSublatticeOnto hv⟩,
    fun N => _root_.YangMills.Construction.Tower.Translations.latticeSubgroup_meshAt_le hL hj
      (_root_.YangMills.Construction.Tower.Translations.castVec_mem_latticeSubgroup_top L k N),
    fun f hi hf U hU => ?_, fun v hv b hb => ?_⟩
  · have ends := edgePreimage_endpoints hP hi hf
    obtain ⟨hU₁, hU₂⟩ := hU
    refine ⟨⟨fun b => hU₁ _, fun b => ?_⟩,
      fun l hl => covDiff_pushField hA ends hU₁ hU₂ hl⟩
    show U (edgePreimage f b.opposite) = (U (edgePreimage f b))⁻¹
    rw [edgePreimage_opposite ends b]
    exact hU₂ _
  · have heq := edgePreimage_eq_translateLink (vertexPreimage_spaceShift hv) b
    have hpos : (edgePreimage (spaceShift v) b).IsPositivelyOriented := by
      rw [heq]
      exact translateLink_isPositivelyOriented _ hb
    refine ⟨hpos, fun U _ B _ => ?_⟩
    show extendOddly _ b = _
    rw [extendOddly_of_pos hb]
    show tangentEdgeValue U B (edgePreimage (spaceShift v) b) = _
    unfold tangentEdgeValue
    rw [if_pos hpos]
theorem actionPreservesColourAndAxes_of_le {i : ℕ} (hL : (L : ℝ) ≠ 0) (hi : i ≤ k) :
    ActionPreservesColourAndAxes L k i := by
  intro N
  have hv := _root_.YangMills.Construction.Tower.Translations.latticeSubgroup_meshAt_le hL hi
    (_root_.YangMills.Construction.Tower.Translations.castVec_mem_latticeSubgroup_top L k N)
  refine ⟨fun c x => rfl, fun c b μ hb => ⟨rfl, ?_⟩, fun c p => ⟨rfl, rfl, rfl⟩⟩
  have heq : edgeImage (PeriodicOperators.intShift N) b.1 = translateLink _ b.1 :=
    edgeImage_eq_translateLink (f := spaceShift (castVec N)) (vertexImage_spaceShift hv) b.1
  have spec : (PeriodicOperators.shiftEdge N b).1 =
      edgeImage (PeriodicOperators.intShift N) b.1 :=
    Classical.epsilon_spec
      (p := fun b' : PeriodicOperators.PosEdge L k i =>
        b'.1 = edgeImage (PeriodicOperators.intShift N) b.1)
      ⟨⟨translateLink _ b.1, translateLink_isPositivelyOriented _ b.2⟩, heq.symm⟩
  show (PeriodicOperators.shiftEdge N b).1.terminal -
    (PeriodicOperators.shiftEdge N b).1.initial = _
  rw [spec, heq]
  show b.1.terminal + _ - (b.1.initial + _) = _
  rw [add_sub_add_right_eq_sub, hb]
end FullSpace.Translations
namespace Translations
open QuotientLattices (NeighboursAtSpacing)
theorem translationProperties_holds (h₁ : QuotientLattices.TorusAndSpaceLatticeProperties)
    (h₂ : Matrices.ComplexMatrix2.ConjugationPreservesTraceless) : TranslationProperties := by
  intro L hL k j hj
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this.ne'
  have hwhole : NeighboursAtSpacing QuotientLattices.spaceDist
      (InfiniteLattice.latticeSubgroup (meshAt L k j)) (meshAt L k j)
      (QuotientLattices.spaceAxisSteps (meshAt L k j)) := by
    have h := (h₁ L hL 1 j k le_rfl hj).2.2.2.2.2.2.2.2
    have e : PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k j) =
        meshAt L k j := meshSize_levelDepth L k j
    rw [e] at h
    exact h
  refine ⟨by simp [meshAt], fun n hn => ⟨fun v hv => torusShift_respectsLevels hL0 hv,
    fun N => torusShift_respectsLevels hL0 (castVec_mem_latticeSubgroup_top L k N),
    covDiffEquivariant_torus hL0 hj (h₁ L hL n j k hn hj).2.2.2.2.2.2.2.1 h₂⟩,
    fun v hv => FullSpace.Translations.spaceShift_respectsLevels hL0 hv,
    fun N => FullSpace.Translations.spaceShift_respectsLevels hL0
      (castVec_mem_latticeSubgroup_top L k N),
    FullSpace.Translations.covDiffEquivariant_space hL0 hj hwhole h₂,
    fun i hi => FullSpace.Translations.actionPreservesColourAndAxes_of_le hL0 hi⟩
end Translations
end YangMills.Construction.Tower
end
