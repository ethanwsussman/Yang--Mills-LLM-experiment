import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open InfiniteLattice (Link GaugeField IsLocalObservable IsRegionMeasurable IsBoundedObservable
  IsLinearPart LatticeSymmetry LatticePoint AmbientSpace UnitLatticeSymmetry axisShiftInvariantSigma
  hyperoctahedralLinearGroup latticeMotion shiftInvariantSigma localRegionObservables
  boundedRegionObservables hyperplaneReflect signedUnitVectors latticeSubgroup axisStep shift
  unitRegionObservables)
namespace SymmetryActionAndReflections
private theorem linkMap_linkMap {s r : UnitLatticeSymmetry}
    (h : Function.LeftInverse s.toFun r.toFun) (b : Link 1) : s.linkMap (r.linkMap b) = b :=
  Link.ext (Subtype.ext (h _)) (Subtype.ext (h _))
private theorem pullbackField_pullbackField {s r : UnitLatticeSymmetry}
    (h : Function.LeftInverse s.toFun r.toFun) (U : GaugeField 1) :
    r.pullbackField (s.pullbackField U) = U :=
  Subtype.ext (funext fun b => congrArg U.1 (linkMap_linkMap h b))
private theorem compMapsAndPullbacks_holds (r r' : UnitLatticeSymmetry) :
    CompMapsAndPullbacks r r' :=
  ⟨rfl, rfl⟩
private theorem actionRulesOn_all (r r' : UnitLatticeSymmetry) (hr : Continuous r.pullbackField)
    (𝒞 : (GaugeField 1 → ℂ) → Prop) : ActionRulesOn r r' 𝒞 := by
  intro F H _ _
  refine ⟨rfl, ?_, rfl, fun _ => rfl, rfl, rfl, fun hF => hF.comp hr⟩
  intro s hs
  funext U
  change F (r.pullbackField (s.pullbackField U)) = F U
  rw [pullbackField_pullbackField hs.1]
private theorem isLocalObservable_actOn {r : UnitLatticeSymmetry}
    (hLoc : InfiniteLattice.ActOnLocalRegions (1 : ℝ))
    {F : GaugeField 1 → ℂ} (oF : IsBoundedObservable F) (lF : IsLocalObservable F) :
    IsLocalObservable (r.actOn F) := by
  obtain ⟨S, bS, mS⟩ := lF
  have hF : F ∈ localRegionObservables 1 (Set.univ : Set AmbientSpace) :=
    Set.mem_iUnion₂.mpr ⟨S, bS, oF, by rw [Set.univ_inter]; exact mS⟩
  have hrF : r.actOn F ∈ localRegionObservables 1 (r.setImage Set.univ) := by
    rw [← hLoc.1 r Set.univ]
    exact ⟨F, hF, rfl⟩
  obtain ⟨Q, bQ, hQ⟩ := Set.mem_iUnion₂.mp hrF
  exact ⟨_, Bornology.IsBounded.subset bQ Set.inter_subset_right, hQ.2⟩
variable (P : UnitMirrorPair)
private theorem reflect_leftInverse : Function.LeftInverse P.reflect.toFun P.reflect.toFun :=
  InfiniteLattice.hyperplaneReflect_hyperplaneReflect P.normal_dotProduct_self_ne_zero P.height
private theorem setImage_upper :
    P.reflect.setImage {x | P.height ≤ P.normal ⬝ᵥ x} = {x | P.normal ⬝ᵥ x ≤ P.height} := by
  have hN := P.normal_dotProduct_self_ne_zero
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : P.height ≤ P.normal ⬝ᵥ x := hx
    have h := InfiniteLattice.dotProduct_hyperplaneReflect_sub hN P.height x
    change P.normal ⬝ᵥ hyperplaneReflect P.normal P.height x ≤ P.height
    linarith
  · intro hy
    have hy' : P.normal ⬝ᵥ y ≤ P.height := hy
    refine ⟨hyperplaneReflect P.normal P.height y, ?_,
      InfiniteLattice.hyperplaneReflect_hyperplaneReflect hN P.height y⟩
    have h := InfiniteLattice.dotProduct_hyperplaneReflect_sub hN P.height y
    change P.height ≤ P.normal ⬝ᵥ hyperplaneReflect P.normal P.height y
    linarith
private theorem setImage_lower :
    P.reflect.setImage {x | P.normal ⬝ᵥ x ≤ P.height} = {x | P.height ≤ P.normal ⬝ᵥ x} := by
  have hN := P.normal_dotProduct_self_ne_zero
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : P.normal ⬝ᵥ x ≤ P.height := hx
    have h := InfiniteLattice.dotProduct_hyperplaneReflect_sub hN P.height x
    change P.height ≤ P.normal ⬝ᵥ hyperplaneReflect P.normal P.height x
    linarith
  · intro hy
    have hy' : P.height ≤ P.normal ⬝ᵥ y := hy
    refine ⟨hyperplaneReflect P.normal P.height y, ?_,
      InfiniteLattice.hyperplaneReflect_hyperplaneReflect hN P.height y⟩
    have h := InfiniteLattice.dotProduct_hyperplaneReflect_sub hN P.height y
    change P.normal ⬝ᵥ hyperplaneReflect P.normal P.height y ≤ P.height
    linarith
private theorem normal_mem_latticeSubgroup : P.normal ∈ latticeSubgroup 1 := by
  have h : ∀ ι, ∃ k : ℤ, P.normal ι = (k : ℝ) * 1 := fun ι => by
    rcases P.normal_apply_trichotomy ι with e | e | e
    · exact ⟨0, by simp [e]⟩
    · exact ⟨1, by simp [e]⟩
    · exact ⟨-1, by simp [e]⟩
  choose k hk using h
  exact ⟨k, hk⟩
private theorem normal_ne_zero : P.normal ≠ 0 := fun h =>
  P.normal_dotProduct_self_ne_zero (by rw [h]; simp)
private def linearReflection : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  LinearEquiv.ofInvolutive
    { toFun := hyperplaneReflect P.normal 0
      map_add' := fun x y => by
        funext κ
        simp only [hyperplaneReflect, dotProduct_add, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      map_smul' := fun t x => by
        funext κ
        simp only [hyperplaneReflect, dotProduct_smul, RingHom.id_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul]
        ring }
    (InfiniteLattice.hyperplaneReflect_hyperplaneReflect P.normal_dotProduct_self_ne_zero 0)
private theorem linearReflection_apply (x : AmbientSpace) :
    linearReflection P x = hyperplaneReflect P.normal 0 x := rfl
private theorem hyperplaneReflect_eq_add (x : AmbientSpace) :
    hyperplaneReflect P.normal P.height x =
      linearReflection P x + hyperplaneReflect P.normal P.height 0 := by
  rw [linearReflection_apply]
  funext κ
  simp only [hyperplaneReflect, dotProduct_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  ring
private theorem linearReflection_link (b : Link 1) :
    linearReflection P ((b.terminal : AmbientSpace) - (b.initial : AmbientSpace)) ∈ signedUnitVectors := by
  have hh : (((P.reflect.linkMap b).terminal : LatticePoint 1) : AmbientSpace) -
      (((P.reflect.linkMap b).initial : LatticePoint 1) : AmbientSpace) =
      linearReflection P ((b.terminal : AmbientSpace) - (b.initial : AmbientSpace)) := by
    change hyperplaneReflect P.normal P.height b.terminal -
      hyperplaneReflect P.normal P.height b.initial = _
    rw [hyperplaneReflect_eq_add P b.terminal, hyperplaneReflect_eq_add P b.initial,
      add_sub_add_right_eq_sub, map_sub]
  obtain ⟨ν, h | h⟩ := (P.reflect.linkMap b).isAdjacent
  · exact ⟨ν, Or.inl (hh.symm.trans (congrArg Subtype.val h))⟩
  · exact ⟨ν, Or.inr (hh.symm.trans (congrArg Subtype.val h))⟩
private theorem linearReflection_signedUnitVectors {x : AmbientSpace} (hx : x ∈ signedUnitVectors) :
    linearReflection P x ∈ signedUnitVectors := by
  obtain ⟨μ, rfl | rfl⟩ := hx
  · have h := linearReflection_link P (Link.forwardFrom 0 μ)
    have e : (((Link.forwardFrom (0 : LatticePoint 1) μ).terminal : LatticePoint 1) : AmbientSpace) -
        (((Link.forwardFrom (0 : LatticePoint 1) μ).initial : LatticePoint 1) : AmbientSpace) =
        Pi.single μ 1 := by
      change ((0 : AmbientSpace) + Pi.single μ 1) - 0 = _
      simp
    rwa [e] at h
  · have h := linearReflection_link P (Link.forwardFrom 0 μ).opposite
    have e : (((Link.forwardFrom (0 : LatticePoint 1) μ).opposite.terminal : LatticePoint 1) :
        AmbientSpace) -
        (((Link.forwardFrom (0 : LatticePoint 1) μ).opposite.initial : LatticePoint 1) : AmbientSpace) =
        -Pi.single μ 1 := by
      change (0 : AmbientSpace) - ((0 : AmbientSpace) + Pi.single μ 1) = _
      simp
    rwa [e] at h
private theorem linearReflection_mem : linearReflection P ∈ hyperoctahedralLinearGroup := by
  change linearReflection P '' signedUnitVectors = signedUnitVectors
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact linearReflection_signedUnitVectors P hx
  · intro hy
    exact ⟨linearReflection P y, linearReflection_signedUnitVectors P hy,
      InfiniteLattice.hyperplaneReflect_hyperplaneReflect P.normal_dotProduct_self_ne_zero 0 y⟩
private theorem linearReflection_normal : linearReflection P P.normal = -P.normal := by
  have hN := P.normal_dotProduct_self_ne_zero
  rw [linearReflection_apply]
  funext κ
  simp only [hyperplaneReflect, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, sub_zero]
  field_simp
  ring
private theorem isLinearPart_reflect : IsLinearPart 1 P.reflect.toFun (linearReflection P) :=
  ⟨linearReflection_mem P, P.reflect.pointMap 0, funext fun x => hyperplaneReflect_eq_add P x⟩
private theorem reflect_comp_shift (k : ℤ) (v : LatticePoint 1)
    (hv : (v : AmbientSpace) = (k : ℝ) • P.normal) :
    P.reflect.comp (shift (-v)) = (shift v).comp P.reflect := by
  have hN := P.normal_dotProduct_self_ne_zero
  apply latticeSymmetry_ext
  funext x
  change hyperplaneReflect P.normal P.height (x + -(v : AmbientSpace)) =
    hyperplaneReflect P.normal P.height x + (v : AmbientSpace)
  rw [hv]
  funext κ
  simp only [hyperplaneReflect, dotProduct_add, dotProduct_neg, dotProduct_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring
private theorem mirrorReflectionProperties_holds : MirrorReflectionProperties P :=
  ⟨rfl, funext (reflect_leftInverse P), setImage_upper P, setImage_lower P,
    normal_mem_latticeSubgroup P, normal_ne_zero P,
    ⟨linearReflection P, isLinearPart_reflect P, linearReflection_normal P⟩,
    fun k v hv => reflect_comp_shift P k v hv⟩
private theorem nonneg_on_opposite_side
    (hKeep : InfiniteLattice.ActOnPreservesAlgebraAndRegions (1 : ℝ))
    (hLoc : InfiniteLattice.ActOnLocalRegions (1 : ℝ))
    (hCont : Continuous P.reflect.pullbackField)
    {A B : Set AmbientSpace} (hBA : P.reflect.setImage B = A) (ν : Measure (GaugeField 1))
    (hpos : ∀ F ∈ unitRegionObservables A, IsLocalObservable F →
      0 ≤ ∫ U, conj (P.reflect.actOn F U) * F U ∂ν)
    {F' : GaugeField 1 → ℂ} (oF' : IsBoundedObservable F') (lF' : IsLocalObservable F')
    (mF' : IsRegionMeasurable B F') :
    0 ≤ ∫ U, conj (P.reflect.actOn F' U) * F' U ∂ν := by
  have hF : P.reflect.actOn F' ∈ unitRegionObservables A := by
    have h : P.reflect.actOn F' ∈ boundedRegionObservables 1 (P.reflect.setImage B) := by
      rw [← (hKeep P.reflect).2 B]
      exact ⟨F', ⟨oF', mF'⟩, rfl⟩
    rw [hBA] at h
    exact h
  have hinv : P.reflect.actOn (P.reflect.actOn F') = F' :=
    (actionRulesOn_all P.reflect P.reflect hCont (fun _ => True) F' F' trivial trivial).2.1
      P.reflect ⟨reflect_leftInverse P, reflect_leftInverse P⟩
  have h := hpos _ hF (isLocalObservable_actOn hLoc oF' lF')
  rw [hinv] at h
  have him : (∫ U, conj (F' U) * P.reflect.actOn F' U ∂ν).im = 0 :=
    (Complex.le_def.mp h).2.symm
  have e : (fun U => conj (P.reflect.actOn F' U) * F' U) =
      fun U => conj (conj (F' U) * P.reflect.actOn F' U) := by
    funext U
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [e, integral_conj, Complex.conj_eq_iff_im.mpr him]
  exact h
private theorem positivityFromOneHalfSpace_holds
    (hKeep : InfiniteLattice.ActOnPreservesAlgebraAndRegions (1 : ℝ))
    (hLoc : InfiniteLattice.ActOnLocalRegions (1 : ℝ))
    (hCont : Continuous P.reflect.pullbackField) :
    PositivityFromOneHalfSpace P := by
  intro H hH ν hν hpos
  refine ⟨hν, fun H' hH' F oF lF mF => ?_⟩
  rcases hH with rfl | hH
  · rcases hH' with rfl | hH'
    · exact hpos F ⟨oF, mF⟩ lF
    · rw [Set.mem_singleton_iff] at hH'
      subst hH'
      exact nonneg_on_opposite_side P hKeep hLoc hCont (setImage_lower P) ν hpos oF lF mF
  · rw [Set.mem_singleton_iff] at hH
    subst hH
    rcases hH' with rfl | hH'
    · exact nonneg_on_opposite_side P hKeep hLoc hCont (setImage_upper P) ν hpos oF lF mF
    · rw [Set.mem_singleton_iff] at hH'
      subst hH'
      exact hpos F ⟨oF, mF⟩ lF
theorem of_symmetryActionOnObservables (hAct : InfiniteLattice.SymmetryActionOnObservables) :
    SymmetryActionAndReflections := by
  have hPull : InfiniteLattice.PullbackFieldIsHomeomorph (1 : ℝ) :=
    (hAct ⟨1, one_pos⟩).2.1
  have hKeep : InfiniteLattice.ActOnPreservesAlgebraAndRegions (1 : ℝ) :=
    (hAct ⟨1, one_pos⟩).2.2.1
  have hLin : InfiniteLattice.ActOnLinearIsometric (1 : ℝ) :=
    (hAct ⟨1, one_pos⟩).2.2.2.2.2.1
  have hLoc : InfiniteLattice.ActOnLocalRegions (1 : ℝ) :=
    (hAct ⟨1, one_pos⟩).2.2.2.2.2.2.2.2.1
  have hInv : InfiniteLattice.LatticeSymmetryInverses (1 : ℝ) :=
    (hAct ⟨1, one_pos⟩).2.2.2.2.2.2.2.2.2.1
  have hCont : ∀ r : UnitLatticeSymmetry, Continuous r.pullbackField :=
    fun r => ((hPull r).2).continuous
  refine ⟨compMapsAndPullbacks_holds, fun r D => (hKeep r).2 D,
    fun μ I hI => ⟨hI.1, hI.2 _⟩, ?_, ?_, fun r r' => actionRulesOn_all r r' (hCont r) _,
    fun r r' => actionRulesOn_all r r' (hCont r) _, fun r J hJ => hJ.comp (hCont r).measurable,
    mirrorReflectionProperties_holds, fun P => positivityFromOneHalfSpace_holds P hKeep hLoc (hCont _)⟩
  · intro r
    obtain ⟨t, ht⟩ := (hInv r).2.1
    exact ⟨fun b => ⟨t.linkMap b, linkMap_linkMap ht.2 b⟩, (hPull r).2, ⟨t, ht⟩, rfl⟩
  · intro r F oF
    exact ⟨((hKeep r).1 F F oF oF).1, ((hLin r).2 F oF).2.2.2,
      fun lF => isLocalObservable_actOn hLoc oF lF⟩
end SymmetryActionAndReflections
end YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
