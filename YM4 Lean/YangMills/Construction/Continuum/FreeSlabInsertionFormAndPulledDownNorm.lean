import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.ReflectionsAndOneInsertion.PeriodicGibbsLimitStandingDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionsAndOneInsertion
open InfiniteLattice (AmbientSpace)
open R4TupleForms (singleTuple)
namespace SlabInsertion
abbrev timeVec (t : ℝ) : AmbientSpace := Pi.single TimeAxis.timeIdx t
abbrev timeAbove (a : ℝ) : Set AmbientSpace := {x | a < TimeAxis.timeComponent x}
abbrev timeBelow (a : ℝ) : Set AmbientSpace := {x | TimeAxis.timeComponent x < a}
abbrev centralSlab (η : ℝ) : Set AmbientSpace := {x | |TimeAxis.timeComponent x| < η / 4}
theorem push_mem_supportedIn {r ρ : AmbientSpace → AmbientSpace} (hr : invMap r = ρ) (hρ : Continuous ρ)
    {U V : Set AmbientSpace} (hUV : ∀ x, ρ x ∈ U → x ∈ V) {X : SepTuple} (hX : X ∈ supportedIn U) :
    push r X ∈ supportedIn V := by
  unfold push
  split_ifs with h
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    rw [hr]
    exact fun x hx => hUV x (hX g hg (tsupport_comp_subset_preimage g hρ hx))
  · exact nil_mem_supportedIn V
theorem pushSpan_mem_spanIn {r ρ : AmbientSpace → AmbientSpace} (hr : invMap r = ρ) (hρ : Continuous ρ)
    {U V : Set AmbientSpace} (hUV : ∀ x, ρ x ∈ U → x ∈ V) {F : FormalSpan} (hF : F ∈ spanIn U) :
    pushSpan r F ∈ spanIn V := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    have h : pushSpan r (basisVec X.1) = basisVec (push r X.1) := linearExtend_basisVec _ _
    rw [h]
    exact Submodule.subset_span ⟨⟨_, push_mem_supportedIn hr hρ hUV X.2⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
theorem conjugation_mem_spanIn {U : Set AmbientSpace} {F : FormalSpan} (hF : F ∈ spanIn U) :
    conjugation F ∈ spanIn U := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.conjugation_mem_spanIn <;> assumption
theorem timeReflection_timeReflection (x : AmbientSpace) :
    TimeAxis.timeReflection (TimeAxis.timeReflection x) = x := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.timeReflection_involutive_apply <;> assumption
theorem invMap_timeReflection : invMap TimeAxis.timeReflection = TimeAxis.timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.invMap_timeReflection <;> assumption
theorem continuous_timeReflection : Continuous TimeAxis.timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.continuous_timeReflection <;> assumption
theorem timeComponent_timeReflection (x : AmbientSpace) :
    TimeAxis.timeComponent (TimeAxis.timeReflection x) = -TimeAxis.timeComponent x := by
  simp [TimeAxis.timeComponent, TimeAxis.timeIdx, TimeAxis.timeReflection]
theorem invMap_translate (v : AmbientSpace) :
    invMap (SeparatedTuples.translate v) = fun x => x - v := by
  have hinj : Function.Injective (SeparatedTuples.translate v) := fun y z hyz => add_right_cancel hyz
  funext x
  have hx : SeparatedTuples.translate v (x - v) = x := by simp [SeparatedTuples.translate]
  calc invMap (SeparatedTuples.translate v) x
        = invMap (SeparatedTuples.translate v) (SeparatedTuples.translate v (x - v)) := by rw [hx]
    _ = x - v := Function.leftInverse_invFun hinj _
theorem timeComponent_sub_timeVec (x : AmbientSpace) (t : ℝ) :
    TimeAxis.timeComponent (x - timeVec t) = TimeAxis.timeComponent x - t := by
  simp [TimeAxis.timeComponent]
variable (σ : TupleFunctional) {η : ℝ}
def reflectConj (F : spanIn (timeAbove (η / 4))) : FormalSpan :=
  pushSpan TimeAxis.timeReflection (conjugation F.1)
def insertionForm (F : spanIn (timeAbove (η / 4))) (k : RealValued) (hk : IsC1c k)
    (F' : spanIn (timeAbove (η / 4))) : ℂ :=
  σ.spanExtension (formalMul (formalMul (reflectConj F) (basisVec (singleTuple k hk))) F'.1)
theorem translate_mem_upperHalfSpace (F : spanIn (timeAbove (η / 4))) :
    pushSpan (SeparatedTuples.translate (timeVec (-(η / 4)))) F.1 ∈ spanIn TimeAxis.upperHalfSpace := by
  have hc : Continuous fun x : AmbientSpace => x - timeVec (-(η / 4)) := continuous_id.sub continuous_const
  have hUV : ∀ x, x - timeVec (-(η / 4)) ∈ timeAbove (η / 4) → x ∈ TimeAxis.upperHalfSpace := fun x hx => by
    have h : η / 4 < TimeAxis.timeComponent (x - timeVec (-(η / 4))) := hx
    rw [timeComponent_sub_timeVec] at h
    change TimeAxis.timeComponent x > 0
    linarith
  exact pushSpan_mem_spanIn (invMap_translate _) hc hUV F.2
def shiftDown (_hη : 0 < η) (F : spanIn (timeAbove (η / 4))) : PositiveSpan :=
  ⟨pushSpan (SeparatedTuples.translate (timeVec (-(η / 4)))) F.1, translate_mem_upperHalfSpace F⟩
def shiftDownNorm (hη : 0 < η) (F : spanIn (timeAbove (η / 4))) : ℝ := spanClassNorm σ (shiftDown hη F)
theorem reflectConj_mem (F : spanIn (timeAbove (η / 4))) :
    reflectConj F ∈ spanIn (timeBelow (-(η / 4))) := by
  refine pushSpan_mem_spanIn invMap_timeReflection continuous_timeReflection (fun x hx => ?_)
    (conjugation_mem_spanIn F.2)
  have h : η / 4 < TimeAxis.timeComponent (TimeAxis.timeReflection x) := hx
  rw [timeComponent_timeReflection] at h
  change TimeAxis.timeComponent x < -(η / 4)
  linarith
theorem singleTuple_mem {k : RealValued} (hk : IsC1c k) (hs : tsupport k ⊆ centralSlab η) :
    basisVec (singleTuple k hk) ∈ spanIn (centralSlab η) := by
  refine Submodule.subset_span ⟨⟨singleTuple k hk, fun f hf => ?_⟩, rfl⟩
  obtain rfl : f = k := List.mem_singleton.1 hf
  exact hs
theorem disjoint_timeBelow_centralSlab : Disjoint (timeBelow (-(η / 4))) (centralSlab η) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₀ : |TimeAxis.timeComponent x| < η / 4 := h'
    have h₁ := (abs_lt.1 h₀).1
    have h₂ : TimeAxis.timeComponent x < -(η / 4) := h
    linarith
theorem disjoint_union_timeAbove (hη : 0 < η) :
    Disjoint (timeBelow (-(η / 4)) ∪ centralSlab η) (timeAbove (η / 4)) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₂ : η / 4 < TimeAxis.timeComponent x := h'
    rcases h with h | h
    · have h₁ : TimeAxis.timeComponent x < -(η / 4) := h
      linarith
    · have h₀ : |TimeAxis.timeComponent x| < η / 4 := h
      have h₁ := (abs_lt.1 h₀).2
      linarith
theorem formalMulDefined_insertion (hη : 0 < η) (F F' : spanIn (timeAbove (η / 4))) {k : RealValued}
    (hk : IsC1c k) (hs : tsupport k ⊆ centralSlab η) :
    R4TupleForms.FormalMulDefined (reflectConj F) (basisVec (singleTuple k hk)) ∧
      R4TupleForms.FormalMulDefined
        (formalMul (reflectConj F) (basisVec (singleTuple k hk))) F'.1 :=
  ⟨R4TupleForms.formalMulDefined_of_mem disjoint_timeBelow_centralSlab (reflectConj_mem F)
      (singleTuple_mem hk hs),
    R4TupleForms.formalMulDefined_of_mem (disjoint_union_timeAbove hη)
      (R4TupleForms.formalMul_mem disjoint_timeBelow_centralSlab (reflectConj_mem F)
        (singleTuple_mem hk hs)) F'.2⟩
end SlabInsertion
end YangMills.Construction
