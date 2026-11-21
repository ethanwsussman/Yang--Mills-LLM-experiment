import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGridsProof
import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamilyProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStatesProof
import YangMills.Construction.LawInAState.LawsAreInvariantUnderTranslationsProof
import YangMills.Construction.ReflectionPositivity.FunctionsOfTheBondsInASet
import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.HalfAndShift
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint Link GaugeField
  IsBoundedObservable IsLocalObservable IsRegionMeasurable IsSymmetricUnder IsShiftInvariant
  LatticeSymmetry observableSupNorm regionObservables latticeSubgroup shift hyperplaneReflect)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns continuousLocal)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair
  IsReflectionPositiveAcross)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet
  isReflectionPositiveAcross_iff)
variable {a : ℝ}
private theorem measurable_pullbackField (r : LatticeSymmetry a) :
    Measurable r.pullbackField := by apply _root_.YangMills.SharedProofs.p50069 <;> assumption
private theorem isBoundedObservable_actOn (r : LatticeSymmetry a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (r.actOn F) := by apply _root_.YangMills.Construction.InfiniteLattice.LiftedGibbsStates.isBoundedObservable_actOn <;> assumption
private theorem isBoundedObservable_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => F U * G U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
private theorem isBoundedObservable_conj {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable fun U => conj (F U) := by apply _root_.YangMills.Construction.NormalFamilies.ReflectionIdentities.isBoundedObservable_conj <;> assumption
private theorem isBoundedObservable_affine {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (z : ℂ) : IsBoundedObservable fun U => 1 + z * F U := by
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨(hm.const_mul z).const_add 1, 1 + ‖z‖ * C, fun U => ?_⟩
  calc ‖1 + z * F U‖ ≤ ‖(1 : ℂ)‖ + ‖z * F U‖ := norm_add_le _ _
    _ ≤ 1 + ‖z‖ * C := by
      rw [norm_one, norm_mul]
      gcongr
      exact hC U
private theorem isRegionMeasurable_affine {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) (z : ℂ) : IsRegionMeasurable S fun U => 1 + z * F U := by
  have hφ : Measurable fun w : ℂ => 1 + z * w := (measurable_id.const_mul z).const_add 1
  exact hφ.comp hF
private theorem isLocalObservable_affine {F : GaugeField a → ℂ} (hF : IsLocalObservable F)
    (z : ℂ) : IsLocalObservable fun U => 1 + z * F U := by
  obtain ⟨Q, hQ, hm⟩ := hF
  exact ⟨Q, hQ, isRegionMeasurable_affine hm z⟩
private theorem integrable_of_bounded (ν : BorelProb a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : Integrable F ν.1 := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.integrable_of_isBoundedObservable <;> assumption
private theorem norm_integral_le_of_bound (ν : BorelProb a) {G : GaugeField a → ℂ} {C : ℝ}
    (h : ∀ U, ‖G U‖ ≤ C) : ‖∫ U, G U ∂ν.1‖ ≤ C := by
  have : IsProbabilityMeasure ν.1 := ν.2
  simpa using norm_integral_le_of_norm_le_const (μ := ν.1) (Filter.Eventually.of_forall h)
abbrev _root_.YangMills.DeltaSharedProofs.p501847 := @norm_integral_le_of_bound
private theorem integral_conj_affine_mul_of_integrable (μ : Measure (GaugeField a))
    [IsProbabilityMeasure μ] {h h' : GaugeField a → ℂ} (i1 : Integrable h μ)
    (i2 : Integrable (fun U => conj (h' U)) μ)
    (i3 : Integrable (fun U => conj (h' U) * h U) μ) (z : ℂ) :
    ∫ U, conj (1 + z * h' U) * (1 + z * h U) ∂μ =
      1 + z * ∫ U, h U ∂μ + conj z * conj (∫ U, h' U ∂μ) +
        z * conj z * ∫ U, conj (h' U) * h U ∂μ := by
  have e : ∀ U, conj (1 + z * h' U) * (1 + z * h U) =
      ((1 + z * h U) + conj z * conj (h' U)) + z * conj z * (conj (h' U) * h U) := fun U => by
    simp only [map_add, map_mul, map_one]
    ring
  have j0 : Integrable (fun U => z * h U) μ := i1.const_mul z
  have j1 : Integrable (fun U => 1 + z * h U) μ := (integrable_const _).add j0
  have j2 : Integrable (fun U => conj z * conj (h' U)) μ := i2.const_mul _
  have j3 : Integrable (fun U => (1 + z * h U) + conj z * conj (h' U)) μ := j1.add j2
  have j4 : Integrable (fun U => z * conj z * (conj (h' U) * h U)) μ := i3.const_mul _
  simp only [e]
  rw [integral_add j3 j4, integral_add j1 j2, integral_add (integrable_const _) j0,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_conj]
  simp
private theorem integral_conj_affine_mul (ν : BorelProb a) {h h' : GaugeField a → ℂ}
    (hh : IsBoundedObservable h) (hh' : IsBoundedObservable h') (z : ℂ) :
    ∫ U, conj (1 + z * h' U) * (1 + z * h U) ∂ν.1 =
      1 + z * ∫ U, h U ∂ν.1 + conj z * conj (∫ U, h' U ∂ν.1) +
        z * conj z * ∫ U, conj (h' U) * h U ∂ν.1 := by
  have : IsProbabilityMeasure ν.1 := ν.2
  exact integral_conj_affine_mul_of_integrable ν.1 (integrable_of_bounded ν hh)
    (integrable_of_bounded ν (isBoundedObservable_conj hh'))
    (integrable_of_bounded ν (isBoundedObservable_mul (isBoundedObservable_conj hh') hh)) z
private theorem pullbackField_comp_eq {r s t u : LatticeSymmetry a}
    (h : r.toFun ∘ s.toFun = t.toFun ∘ u.toFun) (U : GaugeField a) :
    s.pullbackField (r.pullbackField U) = u.pullbackField (t.pullbackField U) :=
  Subtype.ext (funext fun b => congrArg U.1
    (Link.ext (Subtype.ext (congrFun h b.initial)) (Subtype.ext (congrFun h b.terminal))))
private theorem pullbackField_comp {r s t : LatticeSymmetry a}
    (h : r.toFun ∘ s.toFun = t.toFun) (U : GaugeField a) :
    s.pullbackField (r.pullbackField U) = t.pullbackField U :=
  Subtype.ext (funext fun b => congrArg U.1
    (Link.ext (Subtype.ext (congrFun h b.initial)) (Subtype.ext (congrFun h b.terminal))))
private theorem pullbackField_eq_self {t : LatticeSymmetry a} (h : t.toFun = id)
    (U : GaugeField a) : t.pullbackField U = U := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGridArithmetic.pullbackField_of_eq_id <;> assumption
private def shiftInvariantSubgroup (ν : BorelProb a) : AddSubgroup (LatticePoint a) where
  carrier := {v | IsSymmetricUnder ν.1 (shift v)}
  zero_mem' := fun A _ => by
    have h : (shift (0 : LatticePoint a)).toFun = id := funext fun x => by
      change x + ((0 : LatticePoint a) : AmbientSpace) = x
      simp
    exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
      congrArg A (pullbackField_eq_self h U))
  add_mem' := fun {u v} hu hv A hA => by
    have h : (shift u).toFun ∘ (shift v).toFun = (shift (u + v)).toFun :=
      funext fun x => by
        change x + (v : AmbientSpace) + (u : AmbientSpace) = x + ((u + v : LatticePoint a) : AmbientSpace)
        rw [AddSubgroup.coe_add]
        abel
    have e : ∫ U, (shift (u + v)).actOn A U ∂ν.1 =
        ∫ U, (shift u).actOn ((shift v).actOn A) U ∂ν.1 :=
      integral_congr_ae (Filter.Eventually.of_forall fun U =>
        (congrArg A (pullbackField_comp h U)).symm)
    rw [e, hu _ (isBoundedObservable_actOn _ hA), hv A hA]
  neg_mem' := fun {v} hv A hA => by
    have h : (shift v).toFun ∘ (shift (-v)).toFun = id := funext fun x => by
      change x + ((-v : LatticePoint a) : AmbientSpace) + (v : AmbientSpace) = x
      rw [AddSubgroup.coe_neg]
      abel
    have h' : (shift v).toFun ∘ (shift (-v)).toFun = (shift (0 : LatticePoint a)).toFun :=
      h.trans (funext fun x => by
        change x = x + ((0 : LatticePoint a) : AmbientSpace)
        simp)
    have hid : (shift (0 : LatticePoint a)).toFun = id := h'.symm.trans h
    have e : ∫ U, A U ∂ν.1 =
        ∫ U, (shift v).actOn ((shift (-v)).actOn A) U ∂ν.1 :=
      integral_congr_ae (Filter.Eventually.of_forall fun U => by
        change A U = A ((shift (-v)).pullbackField ((shift v).pullbackField U))
        rw [pullbackField_comp h', pullbackField_eq_self hid])
    rw [e, hv _ (isBoundedObservable_actOn _ hA)]
private theorem hyperplaneReflect_add_smul {n : AmbientSpace} (hn : n ⬝ᵥ n ≠ 0) (c t : ℝ)
    (x : AmbientSpace) :
    hyperplaneReflect n c (x + t • n) = hyperplaneReflect n c x - t • n := by
  simp only [hyperplaneReflect, dotProduct_add, dotProduct_smul, smul_eq_mul]
  funext μ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
private theorem dotProduct_reflect_sub (P : MirrorPair a) (x : AmbientSpace) :
    P.normal ⬝ᵥ P.reflect.toFun x - P.height = -(P.normal ⬝ᵥ x - P.height) :=
  InfiniteLattice.dotProduct_hyperplaneReflect_sub P.normal_dotProduct_self_ne_zero P.height x
private theorem reflect_reflect (P : MirrorPair a) (x : AmbientSpace) :
    P.reflect.toFun (P.reflect.toFun x) = x :=
  InfiniteLattice.hyperplaneReflect_hyperplaneReflect P.normal_dotProduct_self_ne_zero P.height x
private theorem setImage_upperHalf (P : MirrorPair a) :
    P.reflect.setImage P.upperHalf = P.lowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := dotProduct_reflect_sub P y
    have hy' : P.height ≤ P.normal ⬝ᵥ y := hy
    change P.normal ⬝ᵥ P.reflect.toFun y ≤ P.height
    linarith
  · intro hx
    have h := dotProduct_reflect_sub P x
    have hx' : P.normal ⬝ᵥ x ≤ P.height := hx
    refine ⟨P.reflect.toFun x, ?_, reflect_reflect P x⟩
    change P.height ≤ P.normal ⬝ᵥ P.reflect.toFun x
    linarith
private theorem setImage_lowerHalf (P : MirrorPair a) :
    P.reflect.setImage P.lowerHalf = P.upperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := dotProduct_reflect_sub P y
    have hy' : P.normal ⬝ᵥ y ≤ P.height := hy
    change P.height ≤ P.normal ⬝ᵥ P.reflect.toFun y
    linarith
  · intro hx
    have h := dotProduct_reflect_sub P x
    have hx' : P.height ≤ P.normal ⬝ᵥ x := hx
    refine ⟨P.reflect.toFun x, ?_, reflect_reflect P x⟩
    change P.normal ⬝ᵥ P.reflect.toFun x ≤ P.height
    linarith
private theorem reflect_comp_shift (P : MirrorPair a) (k : ℤ) :
    P.reflect.toFun ∘ (shift (k • normalShift P)).toFun =
      (shift ((-k) • normalShift P)).toFun ∘ P.reflect.toFun := by
  funext x
  change hyperplaneReflect P.normal P.height (x + ((k • normalShift P : LatticePoint a) : AmbientSpace)) =
    hyperplaneReflect P.normal P.height x + (((-k) • normalShift P : LatticePoint a) : AmbientSpace)
  rw [coe_zsmul_normalShift, coe_zsmul_normalShift,
    hyperplaneReflect_add_smul P.normal_dotProduct_self_ne_zero, sub_eq_add_neg, ← neg_smul]
  push_cast
  congr 2
  ring
private theorem reflect_actOn_shift (P : MirrorPair a) (k : ℤ) (F : GaugeField a → ℂ) :
    P.reflect.actOn ((shift (k • normalShift P)).actOn F) =
      (shift ((-k) • normalShift P)).actOn (P.reflect.actOn F) :=
  funext fun U => congrArg F (pullbackField_comp_eq (reflect_comp_shift P k) U)
private theorem reflectionProperties (ha : 0 < a) (P : MirrorPair a) : ReflectionProperties P := by
  refine ⟨P.reflect.preservesDist, P.reflect.image_eq, funext (reflect_reflect P),
    setImage_upperHalf P, setImage_lowerHalf P, fun x hx => ?_, smul_normal_mem P, ?_,
    reflect_comp_shift P, fun k F _ => reflect_actOn_shift P k F⟩
  · have hx' : P.normal ⬝ᵥ x = P.height := hx
    change hyperplaneReflect P.normal P.height x = x
    simp [hyperplaneReflect, hx']
  · intro h
    rcases smul_eq_zero.mp h with h | h
    · exact ha.ne' h
    · apply P.normal_dotProduct_self_ne_zero
      rw [h]
      simp
private theorem actOn_reflect_reflect (P : MirrorPair a) (F : GaugeField a → ℂ) :
    P.reflect.actOn (P.reflect.actOn F) = F := by
  have h : P.reflect.toFun ∘ P.reflect.toFun = id := funext (reflect_reflect P)
  have h' : P.reflect.toFun ∘ P.reflect.toFun = (shift (0 : LatticePoint a)).toFun :=
    h.trans (funext fun x => by
      change x = x + ((0 : LatticePoint a) : AmbientSpace)
      simp)
  have hid : (shift (0 : LatticePoint a)).toFun = id := h'.symm.trans h
  funext U
  change F (P.reflect.pullbackField (P.reflect.pullbackField U)) = F U
  rw [pullbackField_comp h', pullbackField_eq_self hid]
private theorem integral_actOn_reflect_of_mem (ν : BorelProb a) (P : MirrorPair a)
    {S : Set AmbientSpace} (hpos : IsReflPosOn ν P S) {H : GaugeField a → ℂ}
    (hH : H ∈ regionObservables a S) (hl : IsLocalObservable H) :
    ∫ U, P.reflect.actOn H U ∂ν.1 = ∫ U, H U ∂ν.1 := by
  have ho : IsBoundedObservable H := hH.1
  have ho' := isBoundedObservable_actOn P.reflect ho
  have hz : ∀ z : ℂ, 0 ≤ 1 + z * ∫ U, H U ∂ν.1 +
      conj z * conj (∫ U, P.reflect.actOn H U ∂ν.1) +
        z * conj z * ∫ U, conj (P.reflect.actOn H U) * H U ∂ν.1 := fun z => by
    rw [← integral_conj_affine_mul ν ho ho' z]
    exact hpos (fun U => 1 + z * H U) (isLocalObservable_affine hl z)
      ⟨isBoundedObservable_affine ho z, isRegionMeasurable_affine hH.2 z⟩
  have hs : 0 ≤ ∫ U, conj (P.reflect.actOn H U) * H U ∂ν.1 := hpos H hl hH
  set x := ∫ U, H U ∂ν.1
  set y := ∫ U, P.reflect.actOn H U ∂ν.1
  set s := ∫ U, conj (P.reflect.actOn H U) * H U ∂ν.1
  have hsim : s.im = 0 := ((Complex.le_def.mp hs).2).symm
  have h1 := ((Complex.le_def.mp (hz 1)).2).symm
  have h2 := ((Complex.le_def.mp (hz Complex.I)).2).symm
  simp [hsim] at h1 h2
  apply Complex.ext
  · linarith
  · linarith
private theorem exists_shift_into_half (ha : 0 < a) (P : MirrorPair a) {Q S : Set AmbientSpace}
    (hQ : Bornology.IsBounded Q) (hS : S = P.upperHalf ∨ S = P.lowerHalf) :
    ∃ m : ℤ, ∀ x ∈ Q, x + ((m : ℝ) * a) • P.normal ∈ S := by
  have hN : 0 < P.normal ⬝ᵥ P.normal :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      P.normal_dotProduct_self_ne_zero.symm
  have hc : Continuous fun x : AmbientSpace => P.normal ⬝ᵥ x - P.height := by
    simp only [dotProduct]
    fun_prop
  obtain ⟨r, hr⟩ := hQ.subset_closedBall 0
  obtain ⟨R, hR⟩ :=
    (isCompact_closedBall (0 : AmbientSpace) r).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨k, hk⟩ := exists_nat_ge (R / (a * (P.normal ⬝ᵥ P.normal)))
  have hk' : R ≤ (k : ℝ) * a * (P.normal ⬝ᵥ P.normal) := by
    rwa [div_le_iff₀ (mul_pos ha hN), ← mul_assoc] at hk
  have hb : ∀ x ∈ Q, |P.normal ⬝ᵥ x - P.height| ≤ (k : ℝ) * a * (P.normal ⬝ᵥ P.normal) :=
    fun x hx => (hR x (hr hx)).trans hk'
  rcases hS with rfl | rfl
  · refine ⟨k, fun x hx => ?_⟩
    have h := abs_le.mp (hb x hx)
    change P.height ≤ P.normal ⬝ᵥ (x + _)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    push_cast
    linarith [h.1]
  · refine ⟨-k, fun x hx => ?_⟩
    have h := abs_le.mp (hb x hx)
    change P.normal ⬝ᵥ (x + _) ≤ P.height
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    push_cast
    linarith [h.2]
private theorem integral_actOn_reflect_of_local
    (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) (ha : 0 < a) (P : MirrorPair a)
    {S : Set AmbientSpace} (hS : S = P.upperHalf ∨ S = P.lowerHalf) (ν : BorelProb a)
    (hτ : IsSymmetricUnder ν.1 (shift (normalShift P))) (hpos : IsReflPosOn ν P S)
    {H : GaugeField a → ℂ} (ho : IsBoundedObservable H) (hl : IsLocalObservable H) :
    ∫ U, P.reflect.actOn H U ∂ν.1 = ∫ U, H U ∂ν.1 := by
  have hl' := hl
  obtain ⟨Q, hQ, hm⟩ := hl
  obtain ⟨m, hmS⟩ := exists_shift_into_half ha P hQ hS
  have hinv : ∀ k : ℤ, IsSymmetricUnder ν.1 (shift (k • normalShift P)) := fun k =>
    (shiftInvariantSubgroup ν).zsmul_mem
      (show normalShift P ∈ shiftInvariantSubgroup ν from hτ) k
  obtain ⟨-, -, -, -, -, -, -, -, himg, -, -, -, hloc⟩ :=
    (hF a ha).2.2.1 (shift (m • normalShift P)) (shift (m • normalShift P))
  have h1 : (shift (m • normalShift P)).actOn H ∈
      regionObservables a ((shift (m • normalShift P)).setImage Q) := by
    rw [← himg]
    exact ⟨H, ⟨ho, hm⟩, rfl⟩
  have hsub : (shift (m • normalShift P)).setImage Q ∩ (latticeSubgroup a : Set AmbientSpace) ⊆ S := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    have h := hmS x hx
    change x + ((m • normalShift P : LatticePoint a) : AmbientSpace) ∈ S
    rwa [coe_zsmul_normalShift]
  have h2 := (hB a ha ((shift (m • normalShift P)).setImage Q) S).2.1.1 hsub h1
  have h3 := integral_actOn_reflect_of_mem ν P hpos h2 (hloc H ho hl')
  rw [reflect_actOn_shift, hinv _ _ (isBoundedObservable_actOn _ ho), hinv m H ho] at h3
  exact h3
private theorem isSymmetricUnder_reflect
    (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) (ha : 0 < a) (P : MirrorPair a)
    {S : Set AmbientSpace} (hS : S = P.upperHalf ∨ S = P.lowerHalf) (ν : BorelProb a)
    (hτ : IsSymmetricUnder ν.1 (shift (normalShift P))) (hpos : IsReflPosOn ν P S) :
    IsSymmetricUnder ν.1 P.reflect := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨hcomp, -, -, -, huniq⟩ := (hF a ha).1
  obtain ⟨-, -, -, -, hdense, -⟩ := (hF a ha).2.1
  have hφ := measurable_pullbackField P.reflect
  let ν' : BorelProb a := (⟨ν.1.map P.reflect.pullbackField,
    Measure.isProbabilityMeasure_map hφ.aemeasurable⟩ :
      {μ : Measure (GaugeField a) // IsProbabilityMeasure μ})
  have hmap : ∀ A : GaugeField a → ℂ, IsBoundedObservable A →
      ∫ U, A U ∂ν'.1 = ∫ U, P.reflect.actOn A U ∂ν.1 := fun A hA =>
    integral_map hφ.aemeasurable hA.1.aestronglyMeasurable
  have hobs : ∀ F ∈ continuousFns a, IsBoundedObservable F := fun F hc => by
    have hc' : Continuous F := hc
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc'.continuousOn
    exact ⟨hc'.measurable, C, fun U => hC U (mem_univ U)⟩
  have heq : ν' = ν := huniq ν' ν fun F hFc => by
    have ho := hobs F hFc
    change ∫ U, F U ∂ν'.1 = ∫ U, F U ∂ν.1
    rw [hmap F ho]
    by_contra hne
    have hd : 0 < ‖(∫ U, P.reflect.actOn F U ∂ν.1) - ∫ U, F U ∂ν.1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨F', hF', hε⟩ := hdense F hFc _ (div_pos hd (by norm_num : (0 : ℝ) < 3))
    obtain ⟨-, ho', hl'⟩ := hF'
    obtain ⟨C, hC⟩ := ho.2
    obtain ⟨C', hC'⟩ := ho'.2
    have hD : ∀ U, ‖(F - F') U‖ ≤ observableSupNorm (F - F') := fun U =>
      le_ciSup (f := fun U => ‖(F - F') U‖) ⟨C + C', by
        rintro _ ⟨V, rfl⟩
        exact (norm_sub_le _ _).trans (add_le_add (hC V) (hC' V))⟩ U
    have i1 := integrable_of_bounded ν ho
    have i2 := integrable_of_bounded ν ho'
    have i3 := integrable_of_bounded ν (isBoundedObservable_actOn P.reflect ho)
    have i4 := integrable_of_bounded ν (isBoundedObservable_actOn P.reflect ho')
    have e1 : ‖(∫ U, F U ∂ν.1) - ∫ U, F' U ∂ν.1‖ ≤ observableSupNorm (F - F') := by
      rw [← integral_sub i1 i2]
      exact norm_integral_le_of_bound ν hD
    have e2 : ‖(∫ U, P.reflect.actOn F U ∂ν.1) -
        ∫ U, P.reflect.actOn F' U ∂ν.1‖ ≤ observableSupNorm (F - F') := by
      rw [← integral_sub i3 i4]
      exact norm_integral_le_of_bound ν fun U => hD _
    have e3 := integral_actOn_reflect_of_local hF hB ha P hS ν hτ hpos ho' hl'
    rw [e3] at e2
    have e4 : (∫ U, P.reflect.actOn F U ∂ν.1) - ∫ U, F U ∂ν.1 =
        ((∫ U, P.reflect.actOn F U ∂ν.1) - ∫ U, F' U ∂ν.1) -
          ((∫ U, F U ∂ν.1) - ∫ U, F' U ∂ν.1) := by ring
    have e5 := norm_sub_le ((∫ U, P.reflect.actOn F U ∂ν.1) - ∫ U, F' U ∂ν.1)
      ((∫ U, F U ∂ν.1) - ∫ U, F' U ∂ν.1)
    rw [← e4] at e5
    linarith
  intro A hA
  rw [← hmap A hA, heq]
private theorem isReflPosOn_of_reflected (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (ha : 0 < a) (P : MirrorPair a) {S S' : Set AmbientSpace} (hSS : P.reflect.setImage S' = S)
    (ν : BorelProb a) (hinv : IsSymmetricUnder ν.1 P.reflect) (hpos : IsReflPosOn ν P S) :
    IsReflPosOn ν P S' := by
  intro F hl hF'
  obtain ⟨-, -, -, -, -, -, -, -, himg, -, -, -, hloc⟩ := (hF a ha).2.2.1 P.reflect P.reflect
  have h1 : P.reflect.actOn F ∈ regionObservables a S := by
    rw [← hSS, ← himg]
    exact ⟨F, hF', rfl⟩
  have h2 := hpos _ (hloc F hF'.1 hl) h1
  rw [actOn_reflect_reflect] at h2
  have ho := isBoundedObservable_actOn P.reflect hF'.1
  have h3 := hinv (fun U => conj (F U) * P.reflect.actOn F U)
    (isBoundedObservable_mul (isBoundedObservable_conj hF'.1) ho)
  have h4 : ∫ U, P.reflect.actOn
      (fun U => conj (F U) * P.reflect.actOn F U) U ∂ν.1 =
      ∫ U, conj (P.reflect.actOn F U) * F U ∂ν.1 :=
    integral_congr_ae (Filter.Eventually.of_forall fun U => by
      have hh : P.reflect.actOn F (P.reflect.pullbackField U) = F U :=
        congrFun (actOn_reflect_reflect P F) U
      change conj (F (P.reflect.pullbackField U)) *
        P.reflect.actOn F (P.reflect.pullbackField U) = _
      rw [hh]
      rfl)
  change 0 ≤ ∫ U, conj (P.reflect.actOn F U) * F U ∂ν.1
  rw [← h4, h3]
  exact h2
private theorem halfDeterminesOther (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) (ha : 0 < a) (P : MirrorPair a) :
    HalfDeterminesOther P := by
  intro S S' hS ν hτ hpos
  have hinv := isSymmetricUnder_reflect hF hB ha P (hS.imp (·.1) (·.1)) ν hτ hpos
  have hSS : P.reflect.setImage S' = S := by
    rcases hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact setImage_lowerHalf P
    · exact setImage_upperHalf P
  have hother := isReflPosOn_of_reflected hF ha P hSS ν hinv hpos
  refine ⟨hinv, hother, ?_⟩
  rw [isReflectionPositiveAcross_iff]
  rcases hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hpos, hother⟩
  · exact ⟨hother, hpos⟩
private theorem positiveClassChar (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) (ha : 0 < a) : PositiveClassChar a := by
  have hone := fun P : MirrorPair a => halfDeterminesOther hF hB ha P
  have hset : reflectionPositiveSet a =
      {ν | IsShiftInvariant ν.1 ∧ ∀ P : MirrorPair a, IsReflectionPositiveAcross ν.1 P} := by
    ext ν
    constructor
    · rintro ⟨hT, hP⟩
      exact ⟨hT, fun P => (hone P _ _ (Or.inl ⟨rfl, rfl⟩) ν (hT _) (hP P)).2.2⟩
    · rintro ⟨hT, hP⟩
      exact ⟨hT, fun P => ((isReflectionPositiveAcross_iff ν P).mp (hP P)).1⟩
  refine ⟨hset, ?_, ?_, ?_⟩
  · rintro ν ⟨hT, hP⟩ P
    exact (hone P _ _ (Or.inl ⟨rfl, rfl⟩) ν (hT _) (hP P)).1
  · rw [hset]
    ext μ
    constructor
    · rintro ⟨ν, ⟨hT, hP⟩, rfl⟩
      exact ⟨ν.2, hT, hP⟩
    · rintro ⟨hp, hT, hP⟩
      exact ⟨(⟨μ, hp⟩ : {μ : Measure (GaugeField a) // IsProbabilityMeasure μ}), ⟨hT, hP⟩, rfl⟩
  · intro P Q hQ ν hT
    obtain ⟨P', hn, hc, hp⟩ := MirrorHyperplanes.exists_of_latticeMirror Q
    have hPP : P'.hyperplane = P.hyperplane := hp.trans hQ
    have hrefl : Q.symmetry = P.reflect :=
      (MirrorHyperplanes.latticeSymmetry_ext (by
        change hyperplaneReflect Q.cls.realNormal Q.level = hyperplaneReflect P'.normal P'.height
        rw [hn, hc])).trans (P'.reflect_eq_of_hyperplane_eq P hPP)
    have hside : ∀ H, Q.IsHalfSpace H ↔ H ∈ P.halfSpaces := fun H => by
      rw [← P'.halfSpaces_eq_of_hyperplane_eq P hPP]
      simp only [InfiniteLattice.LatticeMirror.IsHalfSpace, MirrorHyperplanes.MirrorPair.halfSpaces,
        hn, hc, mem_insert_iff, mem_singleton_iff]
    have hint : ∀ (A : GaugeField a → ℂ) (U : GaugeField a), A U * Q.conjReflect A U =
        conj (P.reflect.actOn A U) * A U := fun A U => by
      simp only [InfiniteLattice.LatticeMirror.conjReflect, hrefl, mul_comm]
    refine ⟨fun H hH => ⟨?_, fun ⟨hp', h⟩ => ⟨hp', fun A ho hl hm => ?_⟩⟩, ?_⟩
    · rintro ⟨-, h⟩
      have hpos : IsReflPosOn ν P H := fun F hl hF' => by
        have h' := h F hF'.1 hl hF'.2
        simp only [hint] at h'
        exact h'
      rcases (hside H).mp hH with rfl | rfl
      · exact (hone P _ _ (Or.inl ⟨rfl, rfl⟩) ν (hT _) hpos).2.2
      · exact (hone P _ _ (Or.inr ⟨rfl, rfl⟩) ν (hT _) hpos).2.2
    · simp only [hint]
      exact h H ((hside H).mp hH) A ho hl hm
    · simp only [InfiniteLattice.IsReflectionPositiveAt, IsReflectionPositiveAcross, hside, hint]
theorem halfAndShiftStatement_holds (hF : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : RegionFunctions.RegionFunctionsStatement) : HalfAndShiftStatement :=
  ⟨fun _ ha => ⟨fun P => ⟨reflectionProperties ha P, halfDeterminesOther hF hB ha P⟩,
    positiveClassChar hF hB ha⟩,
    (positiveClassChar hF hB one_pos).2.2.1⟩
end YangMills.Construction.ReflectionPositivity.HalfAndShift
