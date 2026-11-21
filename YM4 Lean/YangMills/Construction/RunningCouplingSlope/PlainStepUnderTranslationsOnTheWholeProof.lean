import YangMills.Construction.RunningCouplingSlope.PlainStepAtRealConfigurationsOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheFormsOnTheWholeProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace MeanStepShift
open Tower Matrices
open InfiniteLattice (AmbientSpace)
section SingleSublattice
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
private theorem coe_vertexImage (hM : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    ((FullSpace.vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
private theorem apply_vertexPreimage (hM : FullSpace.MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) :
    f (FullSpace.vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
private theorem vertexPreimage_vertexImage (hM : FullSpace.MapsSublatticeOnto a f)
    (hi : Function.Injective f) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexPreimage f (FullSpace.vertexImage f x) = x :=
  Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM x)))
private theorem edgeImage_ends (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage f b).initial = FullSpace.vertexImage f b.initial ∧
      (FullSpace.edgeImage f b).terminal = FullSpace.vertexImage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_endpoints <;> assumption
private theorem edgePreimage_ends (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
      (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgePreimage_endpoints <;> assumption
private theorem edgeImage_edgePreimage (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    FullSpace.edgeImage f (FullSpace.edgePreimage f b) = b := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_edgePreimage <;> assumption
private theorem edgePreimage_edgeImage (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    FullSpace.edgePreimage f (FullSpace.edgeImage f b) = b := by
  obtain ⟨t, h⟩ := edgeImage_ends hM hB b
  obtain ⟨t', h'⟩ := edgePreimage_ends hM hB hi (FullSpace.edgeImage f b)
  refine InfiniteLattice.Link.ext ?_ ?_
  · rw [t', t, vertexPreimage_vertexImage hM hi]
  · rw [h', h, vertexPreimage_vertexImage hM hi]
private theorem edgeImage_opposite (hM : FullSpace.MapsSublatticeOnto a f)
    (hB : FullSpace.MapsLinksOnto a f) (b : InfiniteLattice.Link a) :
    FullSpace.edgeImage f b.opposite = (FullSpace.edgeImage f b).opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_opposite <;> assumption
variable (hM : FullSpace.MapsSublatticeOnto a f) (hB : FullSpace.MapsLinksOnto a f)
  (hadd : ∀ p q : AmbientSpace, f (p + q) = f p + q)
include hM hadd in
private theorem vertexImage_add (x s : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage f (x + s) = FullSpace.vertexImage f x + s := by
  apply Subtype.ext
  show ((FullSpace.vertexImage f (x + s) : InfiniteLattice.LatticePoint a) : AmbientSpace) =
    ((FullSpace.vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) +
      (s : AmbientSpace)
  rw [coe_vertexImage hM, coe_vertexImage hM]
  exact hadd _ _
include hM hadd in
private theorem vertexImage_sub (x s : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage f (x - s) = FullSpace.vertexImage f x - s := by
  have h := vertexImage_add hM hadd (x - s) s
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]
include hM hB hadd in
private theorem edgeImage_forwardFrom (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.edgeImage f (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage f x) μ := by
  obtain ⟨t, h⟩ := edgeImage_ends hM hB (InfiniteLattice.Link.forwardFrom x μ)
  refine InfiniteLattice.Link.ext t ?_
  rw [h]
  exact vertexImage_add hM hadd _ _
include hM hB hadd in
private theorem edgeImage_backwardLink (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.edgeImage f (FullSpace.backwardLink x μ) =
      FullSpace.backwardLink (FullSpace.vertexImage f x) μ := by
  obtain ⟨t, h⟩ := edgeImage_ends hM hB (FullSpace.backwardLink x μ)
  refine InfiniteLattice.Link.ext t ?_
  rw [h]
  exact vertexImage_sub hM hadd _ _
include hM hB hadd in
private theorem forwardSteps_image (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℕ) :
    FullSpace.forwardSteps (FullSpace.vertexImage f x) μ m =
      (FullSpace.forwardSteps x μ m).map (FullSpace.edgeImage f) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [FullSpace.forwardSteps, List.map_cons]
    rw [edgeImage_forwardFrom hM hB hadd, ← vertexImage_add hM hadd, ih]
include hM hB hadd in
private theorem backwardSteps_image (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℕ) :
    FullSpace.backwardSteps (FullSpace.vertexImage f x) μ m =
      (FullSpace.backwardSteps x μ m).map (FullSpace.edgeImage f) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [FullSpace.backwardSteps, List.map_cons]
    rw [edgeImage_backwardLink hM hB hadd, ← vertexImage_sub hM hadd, ih]
include hM hB hadd in
private theorem stepsInOrder_image (d : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a)
    (l : List (Fin 4)) :
    FullSpace.stepsInOrder d (FullSpace.vertexImage f x) l =
      (FullSpace.stepsInOrder d x l).map (FullSpace.edgeImage f) := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [FullSpace.stepsInOrder, List.map_append]
    have e : FullSpace.signedSteps (FullSpace.vertexImage f x) μ (d μ) =
        (FullSpace.signedSteps x μ (d μ)).map (FullSpace.edgeImage f) := by
      unfold FullSpace.signedSteps
      split_ifs
      · exact forwardSteps_image hM hB hadd _ _ _
      · exact backwardSteps_image hM hB hadd _ _ _
    rw [e, ← ih, vertexImage_add hM hadd]
include hM hB hadd in
private theorem terminal_sub_initial (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage f b).terminal - (FullSpace.edgeImage f b).initial =
      b.terminal - b.initial := by
  obtain ⟨t, h⟩ := edgeImage_ends hM hB b
  have e := vertexImage_add hM hadd b.initial (b.terminal - b.initial)
  rw [add_sub_cancel] at e
  rw [t, h, e, add_sub_cancel_left]
include hM hB hadd in
private theorem isPositivelyOriented_edgeImage {b : InfiniteLattice.Link a} :
    (FullSpace.edgeImage f b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  unfold InfiniteLattice.Link.IsPositivelyOriented
  rw [terminal_sub_initial hM hB hadd]
private theorem linkHolonomy_pushField
    (hinv : ∀ b : InfiniteLattice.Link a, FullSpace.edgePreimage f (FullSpace.edgeImage f b) = b)
    (V : InfiniteLattice.Link a → ComplexMatrix2) (Γ : List (InfiniteLattice.Link a)) :
    FullSpace.linkHolonomy (FullSpace.pushField f V) (Γ.map (FullSpace.edgeImage f)) =
      FullSpace.linkHolonomy V Γ := by
  induction Γ with
  | nil => rfl
  | cons b Γ ih =>
    have h1 := ih
    simp only [FullSpace.linkHolonomy, List.map_map] at h1
    simp only [FullSpace.linkHolonomy, List.map_cons, List.prod_cons, List.map_map]
    rw [h1]
    simp only [FullSpace.pushField, Function.comp, hinv]
end SingleSublattice
private structure TranslationData (L k : ℕ) (f : AmbientSpace → AmbientSpace) : Prop where
  onSublattice : ∀ i ≤ k, FullSpace.MapsSublatticeOnto (meshAt L k i) f
  onLinks : ∀ i ≤ k, FullSpace.MapsLinksOnto (meshAt L k i) f
  injective : Function.Injective f
  distancePreserving : FullSpace.IsDistancePreserving f
  add_right : ∀ p q : AmbientSpace, f (p + q) = f p + q
section ContourPaths
variable {L k j : ℕ} {f : AmbientSpace → AmbientSpace}
private theorem coe_toFiner (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (y : FullSpace.Vertex L k (j + 1)) :
    ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) = y := by
  have hT := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.1
  have hmem : (y : AmbientSpace) ∈ FullSpace.cube L (meshAt L k j) y := by
    refine ⟨0, fun μ => ?_, by simp⟩
    have := hL.2
    simp
    omega
  have h1 : (y : AmbientSpace) ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
    hT.subset_sublattice y hmem
  exact Classical.epsilon_spec (p := fun x : FullSpace.Vertex L k j => (x : AmbientSpace) = y)
    ⟨⟨y, h1⟩, rfl⟩
private theorem toFiner_vertexImage (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (T : TranslationData L k f)
    (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.toFiner (meshAt L k j) (FullSpace.vertexImage f y) =
      (FullSpace.vertexImage f (FullSpace.toFiner (meshAt L k j) y) : FullSpace.Vertex L k j) := by
  apply Subtype.ext
  rw [coe_toFiner hZ hL hj, coe_vertexImage (T.onSublattice _ (by omega)),
    coe_vertexImage (T.onSublattice _ hj.le), coe_toFiner hZ hL hj]
private theorem cubeOffset_vertexImage (T : TranslationData L k f) (hj : j < k)
    (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j) :
    FullSpace.cubeOffset L (FullSpace.vertexImage f y : FullSpace.Vertex L k (j + 1))
        (FullSpace.vertexImage f x : FullSpace.Vertex L k j) =
      FullSpace.cubeOffset L y x := by
  have e : ((FullSpace.vertexImage f x : FullSpace.Vertex L k j) : AmbientSpace) -
      ((FullSpace.vertexImage f y : FullSpace.Vertex L k (j + 1)) : AmbientSpace) =
        (x : AmbientSpace) - (y : AmbientSpace) := by
    rw [coe_vertexImage (T.onSublattice _ hj.le), coe_vertexImage (T.onSublattice _ (by omega))]
    have h := T.add_right (y : AmbientSpace) ((x : AmbientSpace) - (y : AmbientSpace))
    rw [add_sub_cancel] at h
    rw [h, add_sub_cancel_left]
  unfold FullSpace.cubeOffset FullSpace.IsCubeOffset
  simp only [e]
private theorem contourLeg_image (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (T : TranslationData L k f)
    (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j) (π : Equiv.Perm (Fin 4)) :
    contourLeg (FullSpace.vertexImage f y : FullSpace.Vertex L k (j + 1))
        (FullSpace.vertexImage f x : FullSpace.Vertex L k j) π =
      (contourLeg y x π).map (FullSpace.edgeImage f) := by
  unfold contourLeg
  rw [cubeOffset_vertexImage T hj, toFiner_vertexImage hZ hL hj T,
    stepsInOrder_image (T.onSublattice _ hj.le) (T.onLinks _ hj.le) T.add_right]
private theorem shifted_image (hj : j < k) (T : TranslationData L k f)
    (c : FullSpace.Edge L k (j + 1)) (x : FullSpace.Vertex L k j) :
    FullSpace.shifted (FullSpace.edgeImage f c) (FullSpace.vertexImage f x : FullSpace.Vertex L k j) =
      (FullSpace.vertexImage f (FullSpace.shifted c x) : FullSpace.Vertex L k j) := by
  unfold FullSpace.shifted
  rw [terminal_sub_initial (T.onSublattice _ (by omega)) (T.onLinks _ (by omega)) T.add_right,
    vertexImage_add (T.onSublattice _ hj.le) T.add_right]
private theorem cubeVertices_bijOn (hM : FullSpace.MapsSublatticeOnto (meshAt L k j) f)
    (hi : Function.Injective f)
    (hZ : ∀ y : FullSpace.Vertex L k (j + 1), f '' FullSpace.cube L (meshAt L k j) y =
      FullSpace.cube L (meshAt L k j) (FullSpace.vertexImage f y))
    (y : FullSpace.Vertex L k (j + 1)) :
    BijOn (FullSpace.vertexImage f : FullSpace.Vertex L k j → FullSpace.Vertex L k j)
      (FullSpace.cubeVertices L (meshAt L k j) y)
      (FullSpace.cubeVertices L (meshAt L k j) (FullSpace.vertexImage f y)) := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.cubeVertices_bijOn <;> assumption
private theorem cube_image (hB : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (T : TranslationData L k f) (y : FullSpace.Vertex L k (j + 1)) :
    f '' FullSpace.cube L (meshAt L k j) y =
      FullSpace.cube L (meshAt L k j) (FullSpace.vertexImage f y) :=
  (hB L k (j + 1) hL (by omega) (by omega) (by omega)).2.2.2.2 f T.distancePreserving
    (T.onSublattice _ (by omega)) y
private theorem crossingPath_image (hZ : BlockPathContourPivotStatement) (hB : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (T : TranslationData L k f)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial) :
    FullSpace.crossingPath (FullSpace.edgeImage f c) (FullSpace.vertexImage f x : FullSpace.Vertex L k j) =
      (FullSpace.crossingPath c x).map (FullSpace.edgeImage f) := by
  have hT := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.2.2.1
  have hMj := T.onSublattice j hj.le
  have hBj := T.onLinks j hj.le
  have hM1 := T.onSublattice (j + 1) (by omega)
  have hB1 := T.onLinks (j + 1) (by omega)
  obtain ⟨μ, hμ⟩ := hc
  have hμ' : (FullSpace.edgeImage f c).terminal - (FullSpace.edgeImage f c).initial =
      InfiniteLattice.axisStep (meshAt L k (j + 1)) μ := by
    rw [terminal_sub_initial hM1 hB1 T.add_right]
    exact hμ
  have hx' : (FullSpace.vertexImage f x : FullSpace.Vertex L k j) ∈
      FullSpace.cubeVertices L (meshAt L k j) (FullSpace.edgeImage f c).initial := by
    rw [(edgeImage_ends hM1 hB1 c).1]
    exact (cubeVertices_bijOn hMj T.injective (cube_image hB hL hj T) c.initial).mapsTo hx
  have e1 : FullSpace.crossingPath (FullSpace.edgeImage f c)
      (FullSpace.vertexImage f x : FullSpace.Vertex L k j) = _ :=
    hT.crossingPath_eq (FullSpace.edgeImage f c) μ hμ' _ hx'
  have e2 : FullSpace.crossingPath c x = _ := hT.crossingPath_eq c μ hμ x hx
  rw [e1, e2, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show InfiniteLattice.Link.forwardFrom _ μ =
    FullSpace.edgeImage f (InfiniteLattice.Link.forwardFrom _ μ)
  rw [edgeImage_forwardFrom hMj hBj T.add_right, vertexImage_add hMj T.add_right]
private theorem contourMean_pushField (hZ : BlockPathContourPivotStatement) (hB : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (T : TranslationData L k f)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    (V : FullSpace.Edge L k j → ComplexMatrix2) :
    contourMean (FullSpace.pushField f V) (FullSpace.edgeImage f c) = contourMean V c := by
  have hMj := T.onSublattice j hj.le
  have hBj := T.onLinks j hj.le
  have hM1 := T.onSublattice (j + 1) (by omega)
  have hB1 := T.onLinks (j + 1) (by omega)
  have hinv := edgePreimage_edgeImage hMj hBj T.injective
  obtain ⟨ht, hh⟩ := edgeImage_ends hM1 hB1 c
  unfold contourMean
  congr 1
  rw [ht]
  symm
  refine finsum_mem_eq_of_bijOn _
    (cubeVertices_bijOn hMj T.injective (cube_image hB hL hj T) c.initial)
    fun x hx => Finset.sum_congr rfl fun π _ => ?_
  unfold contourHolonomy
  rw [shifted_image hj T c x, ht, hh, contourLeg_image hZ hL hj T, contourLeg_image hZ hL hj T,
    crossingPath_image hZ hB hL hj T hc hx, linkHolonomy_pushField hinv,
    linkHolonomy_pushField hinv, linkHolonomy_pushField hinv]
private theorem meanRadius_pushField (hZ : BlockPathContourPivotStatement) (hB : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (T : TranslationData L k f)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    (V : FullSpace.Edge L k j → ComplexMatrix2) :
    meanRadius (FullSpace.pushField f V) (FullSpace.edgeImage f c) = meanRadius V c := by
  unfold meanRadius
  rw [contourMean_pushField hZ hB hL hj T hc]
private theorem normalizedMean_pushField (hZ : BlockPathContourPivotStatement)
    (hB : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (T : TranslationData L k f) {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    (V : FullSpace.Edge L k j → ComplexMatrix2) :
    normalizedMean (FullSpace.pushField f V) (FullSpace.edgeImage f c) = normalizedMean V c := by
  unfold normalizedMean
  rw [meanRadius_pushField hZ hB hL hj T hc, contourMean_pushField hZ hB hL hj T hc]
end ContourPaths
section LinkOrientation
variable {a : ℝ}
private theorem positive_or_opposite_positive (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
private theorem extendOddly_of_not_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_of_not_pos <;> assumption
end LinkOrientation
section TwistedFamilies
variable {L k j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
end TwistedFamilies
section CovariantStep
variable {L k j : ℕ} {f : AmbientSpace → AmbientSpace}
private theorem logDirectionalDeriv_congr
    {φ₁ φ₂ : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2} {W₁ W₂ : ComplexMatrix2}
    {B₁ B₂ : FullSpace.Edge L k j → ComplexMatrix2} (hW₀ : W₁ = W₂)
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), φ₁ (t • B₁) = φ₂ (t • B₂)) :
    logDirectionalDeriv ℂ φ₁ W₁ B₁ = logDirectionalDeriv ℂ φ₂ W₂ B₂ := by
  subst hW₀
  unfold logDirectionalDeriv
  refine congrArg _ (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [h] with t ht
  show ComplexMatrix2.logSeries (φ₁ (t • B₁) * _) = ComplexMatrix2.logSeries (φ₂ (t • B₂) * _)
  rw [ht]
private theorem eventually_mem_nearIdentityPolydisc (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {r : ℝ} (hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    {c : FullSpace.Edge L k (j + 1)} (hcp : c.IsPositivelyOriented) :
    ∀ᶠ t in 𝓝 (0 : ℂ), FullSpace.expTwist (t • B) V ∈ FullSpace.nearIdentityPolydisc L k j r c := by apply _root_.YangMills.SharedProofs.p8922 <;> assumption
private theorem tangentEdgeValue_smul {a : ℝ} (U B : InfiniteLattice.Link a → ComplexMatrix2)
    (t : ℂ) (b : InfiniteLattice.Link a) :
    FullSpace.tangentEdgeValue U (t • B) b = t • FullSpace.tangentEdgeValue U B b := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.tangentEdgeValue_smul <;> assumption
private theorem isometryOnTangent_smul {a : ℝ} (U B : InfiniteLattice.Link a → ComplexMatrix2)
    (t : ℂ) : FullSpace.isometryOnTangent f U (t • B) = t • FullSpace.isometryOnTangent f U B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [FullSpace.isometryOnTangent, Pi.smul_apply, extendOddly_of_positive _ hb,
      tangentEdgeValue_smul]
  · simp only [FullSpace.isometryOnTangent, Pi.smul_apply, extendOddly_of_not_positive _ hb,
      tangentEdgeValue_smul, smul_neg]
private theorem forwardFrom_positive (y : FullSpace.Vertex L k (j + 1)) :
    (InfiniteLattice.Link.forwardFrom y 0 : FullSpace.Edge L k (j + 1)).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.forwardFrom_positive <;> assumption
private theorem contourLogDrift_pushField (hB : BlockStructure)
    (hH : FullSpace.ComplexSmoothingEquivariance.Statement)
    (hI : LeftChartIsometryEquivariance) (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (T : TranslationData L k f) {V B₀ : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L)
    (hB₀ : B₀ ∈ FullSpace.complexEdgeForms (meshAt L k j)) (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.contourLogDrift (FullSpace.pushField f V) (FullSpace.isometryOnTangent f V B₀)
        (FullSpace.vertexImage f y) =
      FullSpace.contourLogDrift V B₀ y := by
  have hMj := T.onSublattice j hj.le
  have hM1 := T.onSublattice (j + 1) (by omega)
  unfold FullSpace.contourLogDrift
  congr 1
  symm
  refine finsum_mem_eq_of_bijOn _
    (cubeVertices_bijOn hMj T.injective (cube_image hB hL hj T) y) fun x hx => ?_
  have hc := forwardFrom_positive (k := k) (j := j) y
  have hPol : V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L)
      (InfiniteLattice.Link.forwardFrom y 0) :=
    ⟨⟨fun b _ => hV.1 b, fun b _ => hV.2 b⟩, fun b _ => hr b⟩
  have h0 := (hH L hL k j hj f T.distancePreserving hM1 _ hc V hPol).1 y (Or.inl rfl) x hx
  refine logDirectionalDeriv_congr h0.symm ?_
  filter_upwards [eventually_mem_nearIdentityPolydisc hA hPd hL hj hV hr hB₀ hc] with t ht
  have hXm : t • B₀ ∈ FullSpace.complexEdgeForms (meshAt L k j) :=
    (FullSpace.complexEdgeForms _).smul_mem _ hB₀
  have e := (hI L k j hL hj.le).2 f T.distancePreserving hMj V hV _ hXm
  rw [isometryOnTangent_smul] at e
  show _ = FullSpace.complexContourMean L (FullSpace.expTwist (t • FullSpace.isometryOnTangent f V B₀)
    (FullSpace.pushField f V)) (FullSpace.vertexImage f y) (FullSpace.vertexImage f x)
  rw [e, (hH L hL k j hj f T.distancePreserving hM1 _ hc _ ht).1 y (Or.inl rfl) x hx]
private theorem meanCovariantStep_of_positive (V B₀ : FullSpace.Edge L k j → ComplexMatrix2)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanCovariantStep V B₀ c =
      logDirectionalDeriv ℂ (fun X => normalizedMean (FullSpace.expTwist X V) c)
          (normalizedMean V c) B₀ +
        (ComplexMatrix2.conjugateBy (normalizedMean V c) (FullSpace.contourLogDrift V B₀ c.terminal) -
          FullSpace.contourLogDrift V B₀ c.initial) := by apply _root_.YangMills.DeltaSharedProofs.p501203 <;> assumption
end CovariantStep
end MeanStepShift
open MeanStepShift Tower Matrices in
theorem meanStepShiftCovariant_holds
    (hZ : BlockPathContourPivotStatement)
    (hB : BlockStructure)
    (hS : SmoothingNearIdentity)
    (hH : FullSpace.ComplexSmoothingEquivariance.Statement)
    (hI : LeftChartIsometryEquivariance)
    (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold)
    (hTr : Translations.TranslationProperties) :
    MeanStepShiftCovariant := by
  intro L hL
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨polydiscRadius L, hρ, ?_⟩
  intro k j hj n V hV
  have hk : 1 ≤ k := by omega
  have hT := (hTr L hL k k le_rfl).2.2.2.1 n
  have hCt := ((hZ L hL k 0 k hk (Nat.zero_le _) le_rfl).2.2.2.2.2.2 hk).1
  have hMk : FullSpace.MapsSublatticeOnto (meshAt L k k) (PeriodicOperators.intShift n) :=
    hT.2.1 k le_rfl
  have hv : PeriodicOperators.castVec n ∈
      (InfiniteLattice.latticeSubgroup (meshAt L k k) : Set InfiniteLattice.AmbientSpace) := by
    have h0 : PeriodicOperators.intShift n 0 ∈ PeriodicOperators.intShift n ''
        (InfiniteLattice.latticeSubgroup (meshAt L k k) : Set InfiniteLattice.AmbientSpace) :=
      ⟨0, (InfiniteLattice.latticeSubgroup _).zero_mem, rfl⟩
    rw [show PeriodicOperators.intShift n '' (InfiniteLattice.latticeSubgroup (meshAt L k k) :
      Set InfiniteLattice.AmbientSpace) = InfiniteLattice.latticeSubgroup (meshAt L k k) from hMk]
      at h0
    simpa [PeriodicOperators.intShift] using h0
  have T : TranslationData L k (PeriodicOperators.intShift n) :=
    { onSublattice := fun i hi => hT.2.1 i hi
      onLinks := fun i hi =>
        (hCt.mapsSublatticeAndLinks ⟨PeriodicOperators.castVec n, hv⟩ i hi).2
      injective := hT.2.2.1.injective
      distancePreserving := hT.1
      add_right := fun p q => by
        show p + q + PeriodicOperators.castVec n = p + PeriodicOperators.castVec n + q
        abel }
  set f := PeriodicOperators.intShift n with hf
  have hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := hV.2
  have hMj := T.onSublattice j hj.le
  have hM1 := T.onSublattice (j + 1) (by omega)
  have hB1 := T.onLinks (j + 1) (by omega)
  refine ⟨?_, fun c hc => ⟨meanRadius_pushField hZ hB hL hj T hc V, fun B₀ hB₀ => ?_⟩⟩
  · funext c'
    obtain ⟨c, rfl⟩ : ∃ c, FullSpace.edgeImage f c = c' :=
      ⟨_, edgeImage_edgePreimage hM1 hB1 T.injective c'⟩
    show nextMeanIterate (FullSpace.pushField f V) (FullSpace.edgeImage f c) =
      nextMeanIterate V (FullSpace.edgePreimage f (FullSpace.edgeImage f c))
    rw [edgePreimage_edgeImage hM1 hB1 T.injective]
    by_cases hc : c.IsPositivelyOriented
    · have hc' : (FullSpace.edgeImage f c).IsPositivelyOriented :=
        (isPositivelyOriented_edgeImage hM1 hB1 T.add_right).2 hc
      unfold nextMeanIterate
      rw [if_pos hc', if_pos hc, normalizedMean_pushField hZ hB hL hj T hc]
    · have hc' : ¬ (FullSpace.edgeImage f c).IsPositivelyOriented := fun h =>
        hc ((isPositivelyOriented_edgeImage hM1 hB1 T.add_right).1 h)
      have hr' := (positive_or_opposite_positive c).resolve_left hc
      unfold nextMeanIterate
      rw [if_neg hc', if_neg hc, ← edgeImage_opposite hM1 hB1,
        normalizedMean_pushField hZ hB hL hj T hr']
  · have hc' : (FullSpace.edgeImage f c).IsPositivelyOriented :=
      (isPositivelyOriented_edgeImage hM1 hB1 T.add_right).2 hc
    obtain ⟨ht, hh⟩ := edgeImage_ends hM1 hB1 c
    rw [meanCovariantStep_of_positive _ _ hc', meanCovariantStep_of_positive _ _ hc, ht, hh,
      contourLogDrift_pushField hB hH hI hA hPd hL hj T hV.1 hr hB₀,
      contourLogDrift_pushField hB hH hI hA hPd hL hj T hV.1 hr hB₀,
      normalizedMean_pushField hZ hB hL hj T hc]
    refine congrArg (· + _) (logDirectionalDeriv_congr rfl
      (Eventually.of_forall fun t => ?_))
    have hXm : t • B₀ ∈ FullSpace.complexEdgeForms (meshAt L k j) :=
      (FullSpace.complexEdgeForms _).smul_mem _ hB₀
    have e := (hI L k j hL hj.le).2 f T.distancePreserving hMj V hV.1 _ hXm
    rw [isometryOnTangent_smul] at e
    show normalizedMean (FullSpace.expTwist (t • FullSpace.isometryOnTangent f V B₀)
      (FullSpace.pushField f V)) (FullSpace.edgeImage f c) =
        normalizedMean (FullSpace.expTwist (t • B₀) V) c
    rw [e, normalizedMean_pushField hZ hB hL hj T hc]
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
