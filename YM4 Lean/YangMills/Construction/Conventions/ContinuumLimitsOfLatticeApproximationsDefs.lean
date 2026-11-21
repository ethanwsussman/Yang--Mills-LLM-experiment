import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import YangMills.Construction.ReflectionPositivity.FrameOfFunctionalsOnSeparatedTuplesDefs
import YangMills.Construction.ReflectionPositivity.RepresentativesLatticeApproximationsLimitsAndBoundedTriples
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LimitConventions
open InfiniteLattice (RefinedGaugeField IsShiftInvariant AmbientSpace refinedSpacing
  hyperoctahedralLinearGroup)
open LatticeConventions (NormalHyperplane supNorm)
open SeparatedTuples (FormalSpan SepTuple spanIn basisVec supportedIn)
abbrev ApproxTriple (L : ℕ) : Type :=
  ReflectionPositivity.ApproximatingSequences.LatticeApproximation L
instance isProbabilityMeasure_approxState {L : ℕ} (T : ApproxTriple L) (j : ℕ+) :
    IsProbabilityMeasure (T.state j) :=
  T.isProbabilityMeasure_state j
namespace ApproxTriple
variable {L : ℕ} (T : ApproxTriple L)
def tupleRep (j : ℕ+) (X : SepTuple) : RefinedGaugeField L (T.cutoff j) → ℝ :=
  ReflectionPositivity.ApproximatingSequences.LatticeApproximation.latticeProduct T j X.1
def IsReflPos : Prop :=
  ∀ j, IsShiftInvariant (T.state j) ∧
    ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (refinedSpacing L (T.cutoff j))),
      NormalHyperplane.IsReflectionPositiveAcrossMirror hQ (T.state j)
def ConvergesTo (σ : SepTuple → ℝ) : Prop :=
  ∀ X : SepTuple,
    Tendsto (fun j => ∫ U, T.tupleRep j X U ∂T.state j) atTop (𝓝 (σ X))
def spanRep (j : ℕ+) :
    FormalSpan →ₗ[ℂ] RefinedGaugeField L (T.cutoff j) → ℂ :=
  SeparatedTuples.linearExtend fun X U => (T.tupleRep j X U : ℂ)
end ApproxTriple
def cubicMotionGroup : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {g | ∃ w ∈ hyperoctahedralLinearGroup, ∃ v : AmbientSpace, ∀ x, g x = w x + v}
  mul_mem' := by
    rintro g h ⟨w, hw, v, hg⟩ ⟨w', hw', v', hh⟩
    refine ⟨w * w', mul_mem hw hw', w v' + v, fun x => ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hh, hg, map_add, LinearEquiv.mul_apply,
      add_assoc]
  one_mem' := ⟨1, one_mem _, 0, fun x => by simp⟩
  inv_mem' := by
    rintro g ⟨w, hw, v, hg⟩
    refine ⟨w⁻¹, inv_mem hw, -(w⁻¹ v), fun x => ?_⟩
    have hx : x = w (g⁻¹ x) + v := by
      rw [← hg]
      simp
    have hy : g⁻¹ x = w⁻¹ (x - v) := by
      conv_rhs => rw [hx]
      simp
    rw [hy, map_sub, sub_eq_add_neg]
def supDist (x : AmbientSpace) (S : Set AmbientSpace) : ℝ≥0∞ :=
  ⨅ y ∈ S, ENNReal.ofReal (supNorm (x - y))
abbrev SpaceVec : Type := Fin 3 → ℝ
def mkPoint (a : SpaceVec) (t : ℝ) : AmbientSpace := Fin.snoc (α := fun _ => ℝ) a t
def spacePart (x : AmbientSpace) : SpaceVec := fun i => x i.castSucc
theorem mkPoint_last (a : SpaceVec) (t : ℝ) : mkPoint a t (Fin.last 3) = t :=
  Fin.snoc_last (α := fun _ => ℝ) t a
theorem mkPoint_castSucc (a : SpaceVec) (t : ℝ) (i : Fin 3) : mkPoint a t i.castSucc = a i :=
  Fin.snoc_castSucc (α := fun _ => ℝ) t a i
@[simp] theorem spacePart_mkPoint (a : SpaceVec) (t : ℝ) : spacePart (mkPoint a t) = a :=
  funext fun i => mkPoint_castSucc a t i
@[simp] theorem timeComponent_mkPoint (a : SpaceVec) (t : ℝ) :
    TimeAxis.timeComponent (mkPoint a t) = t :=
  mkPoint_last a t
@[simp] theorem mkPoint_spacePart_timeComponent (x : AmbientSpace) :
    mkPoint (spacePart x) (TimeAxis.timeComponent x) = x := by
  refine funext fun μ => Fin.lastCases ?_ (fun i => ?_) μ
  · exact mkPoint_last _ _
  · exact mkPoint_castSucc _ _ _
theorem spacePart_add (x y : AmbientSpace) : spacePart (x + y) = spacePart x + spacePart y := rfl
theorem spacePart_smul (c : ℝ) (x : AmbientSpace) : spacePart (c • x) = c • spacePart x := rfl
theorem timeComponent_add (x y : AmbientSpace) :
    TimeAxis.timeComponent (x + y) = TimeAxis.timeComponent x + TimeAxis.timeComponent y := rfl
theorem timeComponent_smul (c : ℝ) (x : AmbientSpace) :
    TimeAxis.timeComponent (c • x) = c * TimeAxis.timeComponent x := rfl
theorem mkPoint_inj {a b : SpaceVec} {s t : ℝ} (h : mkPoint a s = mkPoint b t) :
    a = b ∧ s = t := by
  constructor
  · simpa using congrArg spacePart h
  · simpa using congrArg TimeAxis.timeComponent h
theorem mkPoint_add (a b : SpaceVec) (s t : ℝ) :
    mkPoint (a + b) (s + t) = mkPoint a s + mkPoint b t := by
  rw [← mkPoint_spacePart_timeComponent (mkPoint a s + mkPoint b t), spacePart_add,
    timeComponent_add]
  simp
theorem mkPoint_smul (c : ℝ) (a : SpaceVec) (t : ℝ) :
    mkPoint (c • a) (c * t) = c • mkPoint a t := by
  rw [← mkPoint_spacePart_timeComponent (c • mkPoint a t), spacePart_smul, timeComponent_smul]
  simp
def spaceBasisVec (i : Fin 3) : SpaceVec := Pi.single i 1
theorem mkPoint_spaceBasisVec (i : Fin 3) :
    mkPoint (spaceBasisVec i) 0 = LatticeConventions.basisVector i.castSucc := by
  refine funext fun μ => Fin.lastCases ?_ (fun k => ?_) μ
  · have h : Fin.last 3 ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    rw [mkPoint_last, LatticeConventions.basisVector, Pi.single_eq_of_ne h]
  · rw [mkPoint_castSucc]
    simp [spaceBasisVec, LatticeConventions.basisVector, Pi.single_apply, Fin.castSucc_inj]
abbrev spaceDot (a q : SpaceVec) : ℝ := SeparatedTupleFunctionals.dotProd a q
def signedSpaceBasis : Set SpaceVec :=
  {a | ∃ i : Fin 3, a = spaceBasisVec i ∨ a = -spaceBasisVec i}
def octahedralGroup3 : Subgroup (SpaceVec ≃ₗ[ℝ] SpaceVec) where
  carrier := {w | w '' signedSpaceBasis = signedSpaceBasis}
  mul_mem' := by
    intro w w' hw hw'
    change (fun x => w (w' x)) '' signedSpaceBasis = signedSpaceBasis
    rw [← image_image (fun x => w x) (fun x => w' x), hw', hw]
  one_mem' := by
    change (fun x => x) '' signedSpaceBasis = signedSpaceBasis
    simp
  inv_mem' := by
    intro w hw
    change w.symm '' signedSpaceBasis = signedSpaceBasis
    conv_lhs => rw [← (show w '' signedSpaceBasis = signedSpaceBasis from hw)]
    rw [image_image]
    simp
theorem exists_mem_octahedralGroup3 (f : SpaceVec →ₗ[ℝ] SpaceVec)
    (hf : BijOn f signedSpaceBasis signedSpaceBasis) : ∃ w ∈ octahedralGroup3, ⇑w = ⇑f := by
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • spaceBasisVec i := by
      funext k
      simp [Finset.sum_apply, spaceBasisVec, Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    obtain ⟨y, -, hy⟩ := hf.surjOn (show spaceBasisVec i ∈ signedSpaceBasis from
      ⟨i, Or.inl rfl⟩)
    exact ⟨y, hy⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, hf.image_eq, rfl⟩
def timeExtension (w : SpaceVec ≃ₗ[ℝ] SpaceVec) : AmbientSpace ≃ₗ[ℝ] AmbientSpace where
  toFun x := mkPoint (w (spacePart x)) (TimeAxis.timeComponent x)
  invFun x := mkPoint (w.symm (spacePart x)) (TimeAxis.timeComponent x)
  map_add' x y := by
    rw [spacePart_add, timeComponent_add, map_add, mkPoint_add]
  map_smul' c x := by
    rw [spacePart_smul, timeComponent_smul, map_smul, mkPoint_smul]
    rfl
  left_inv x := by simp
  right_inv x := by simp
theorem timeExtension_mkPoint (w : SpaceVec ≃ₗ[ℝ] SpaceVec) (a : SpaceVec) (t : ℝ) :
    timeExtension w (mkPoint a t) = mkPoint (w a) t := by
  simp [timeExtension]
theorem mem_hyperoctahedralLinearGroup_iff_toEquiv (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) :
    w ∈ hyperoctahedralLinearGroup ↔ w.toEquiv ∈ TorusLifts.hyperoctahedralGroupEuclidean := by
  rw [InfiniteLattice.mem_hyperoctahedralLinearGroup_iff]
  constructor
  · rintro ⟨π, s, h⟩
    exact ⟨π, s, Equiv.ext fun x => funext fun μ => h x μ⟩
  · rintro ⟨π, s, h⟩
    exact ⟨π, s, fun x μ => congrFun (congrArg (fun g : Equiv.Perm AmbientSpace => g x) h) μ⟩
def timeLineStabilizer : Subgroup (AmbientSpace ≃ₗ[ℝ] AmbientSpace) where
  carrier := {w | w ∈ hyperoctahedralLinearGroup ∧ w '' TimeAxis.timeLine = TimeAxis.timeLine}
  mul_mem' := by
    rintro w w' ⟨hw, fw⟩ ⟨hw', fw'⟩
    refine ⟨mul_mem hw hw', ?_⟩
    change (fun x => w (w' x)) '' TimeAxis.timeLine = TimeAxis.timeLine
    rw [← image_image (fun x => w x) (fun x => w' x), fw', fw]
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    change (fun x => x) '' TimeAxis.timeLine = TimeAxis.timeLine
    simp
  inv_mem' := by
    rintro w ⟨hw, fw⟩
    refine ⟨inv_mem hw, ?_⟩
    change w.symm '' TimeAxis.timeLine = TimeAxis.timeLine
    conv_lhs => rw [← (show w '' TimeAxis.timeLine = TimeAxis.timeLine from fw)]
    rw [image_image]
    simp
def spatialRestriction (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) : SpaceVec →ₗ[ℝ] SpaceVec where
  toFun a := spacePart (w (mkPoint a 0))
  map_add' a b := by
    have h : mkPoint (a + b) 0 = mkPoint a 0 + mkPoint b 0 := by
      simpa using mkPoint_add a b 0 0
    rw [h, map_add, spacePart_add]
  map_smul' c a := by
    have h : mkPoint (c • a) 0 = c • mkPoint a 0 := by
      simpa using mkPoint_smul c a 0
    rw [h, map_smul, spacePart_smul]
    rfl
theorem apply_mkPoint_zero (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace)
    (hw : ∀ a, TimeAxis.IsPurelySpatial (w (mkPoint a 0)))
    (a : SpaceVec) : w (mkPoint a 0) = mkPoint (spatialRestriction w a) 0 := by
  have h : TimeAxis.timeComponent (w (mkPoint a 0)) = 0 := hw a
  conv_lhs => rw [← mkPoint_spacePart_timeComponent (w (mkPoint a 0)), h]
  rfl
end YangMills.Construction.LimitConventions
end
