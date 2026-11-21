import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.ReflectionPositivity.TranslatesOfPositiveCombinationsAndTheirReflectedProductsProof
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpace
import YangMills.Construction.ReflectionPositivity.MovingTestFunctions
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.FormProperties
open SeparatedTuples TupleForm HilbertSpaceBasics
open InfiniteLattice (AmbientSpace)
open Mirrors (axialHyperplane)
def lowerHalfSpace : Set AmbientSpace := {x | TimeAxis.timeComponent x < 0}
theorem isOpen_upperHalfSpace : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply TimeAxis.timeIdx)
theorem isOpen_lowerHalfSpace : IsOpen lowerHalfSpace :=
  isOpen_lt (continuous_apply TimeAxis.timeIdx) continuous_const
theorem disjoint_lowerHalfSpace_upperHalfSpace : Disjoint lowerHalfSpace TimeAxis.upperHalfSpace :=
  Set.disjoint_left.2 fun x hxl hxu =>
    lt_asymm (show TimeAxis.timeComponent x < 0 from hxl) (show 0 < TimeAxis.timeComponent x from hxu)
theorem axialHyperplane_reflect_eq :
    (axialHyperplane TimeAxis.timeIdx 0).reflect = TimeAxis.timeReflection :=
  Mirrors.timeReflection_eq_axialReflection.symm
theorem axialHyperplane_positiveSide_eq :
    (axialHyperplane TimeAxis.timeIdx 0).positiveSide = TimeAxis.upperHalfSpace :=
  Mirrors.upperHalfSpace_eq_positiveSide.symm
theorem isEuclidIsometry_timeReflection : IsEuclidIsometry TimeAxis.timeReflection := by
  intro x y
  simp [TorusMetric.euclidNormVec, TimeAxis.timeReflection, Fin.sum_univ_four]
  ring_nf
theorem timeReflection_comp_translate (a : AmbientSpace) :
    TimeAxis.timeReflection ∘ SeparatedTuples.translate a =
      SeparatedTuples.translate (TimeAxis.timeReflection a) ∘ TimeAxis.timeReflection := by
  funext x i
  fin_cases i <;> simp [TimeAxis.timeReflection, SeparatedTuples.translate] <;> ring
theorem timeComponent_add (a b : AmbientSpace) :
    TimeAxis.timeComponent (a + b) = TimeAxis.timeComponent a + TimeAxis.timeComponent b := rfl
theorem timeComponent_sub (a b : AmbientSpace) :
    TimeAxis.timeComponent (a - b) = TimeAxis.timeComponent a - TimeAxis.timeComponent b := rfl
theorem timeComponent_smul_coordVec (t : ℝ) :
    TimeAxis.timeComponent (t • PeriodicLattice.coordVec TimeAxis.timeIdx) = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem timeReflection_smul_coordVec (t : ℝ) :
    TimeAxis.timeReflection (t • PeriodicLattice.coordVec TimeAxis.timeIdx) =
      -(t • PeriodicLattice.coordVec TimeAxis.timeIdx) := by
  funext i
  fin_cases i <;>
    simp [TimeAxis.timeReflection, PeriodicLattice.coordVec, TimeAxis.timeIdx]
theorem timeReflection_of_isPurelySpatial {v : AmbientSpace} (hv : TimeAxis.IsPurelySpatial v) :
    TimeAxis.timeReflection v = v := by
  have h3 : v 3 = 0 := hv
  funext i
  fin_cases i <;> simp [TimeAxis.timeReflection, h3]
theorem coe_spanBasisIn (U : Set AmbientSpace) (X : supportedIn U) :
    ((spanBasisIn U X : spanIn U) : FormalSpan) = basisVec X.1 := congrArg Subtype.val (Module.Basis.span_apply (linearIndependent_basisVec U) X)
theorem spanExtension_basisVec (σ : TupleFunctional) (X : SepTuple) :
    σ.spanExtension (basisVec X) = (σ X : ℂ) :=
  linearExtend_basisVec _ X
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem supportedIn_mono {U V : Set AmbientSpace} (h : U ⊆ V) : supportedIn U ⊆ supportedIn V :=
  fun _ hX f hf => (hX f hf).trans h
theorem spanIn_mono {U V : Set AmbientSpace} (h : U ⊆ V) :
    spanIn U ≤ spanIn V :=
  Submodule.span_mono (by
    rintro _ ⟨X, rfl⟩
    exact ⟨⟨X.1, supportedIn_mono h X.2⟩, rfl⟩)
theorem conjugation_mem_spanIn {U : Set AmbientSpace} {G : FormalSpan} (hG : G ∈ spanIn U) :
    conjugation G ∈ spanIn U := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    rw [conjugation_basisVec]
    exact Submodule.subset_span ⟨X, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx
theorem exists_finite_expansion (F : PositiveSpan) :
    ∃ J : ℕ, 1 ≤ J ∧ ∃ (X : Fin J → supportedIn TimeAxis.upperHalfSpace) (c : Fin J → ℂ),
      F.1 = ∑ b, c b • basisVec (X b).1 := by
  classical
  let B := spanBasisIn TimeAxis.upperHalfSpace
  let R := B.repr F
  let e₀ : supportedIn TimeAxis.upperHalfSpace := ⟨SepTuple.nil, nil_mem_supportedIn _⟩
  let s := insert e₀ R.support
  have hs : 1 ≤ s.card := Finset.card_pos.2 ⟨e₀, Finset.mem_insert_self _ _⟩
  let e := s.equivFin
  refine ⟨s.card, hs, fun b => (e.symm b).1, fun b => R (e.symm b).1, ?_⟩
  have h1 : F = ∑ x ∈ s, R x • B x := by
    have h := B.linearCombination_repr F
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_insert _ _) _ (by simp)] at h
    exact h.symm
  have h2 : F.1 = ∑ x ∈ s, R x • basisVec x.1 := by
    conv_lhs => rw [h1]
    simp [B, coe_spanBasisIn]
  refine h2.trans ?_
  rw [← Finset.sum_coe_sort s (fun x => R x • basisVec x.1)]
  exact (e.symm.sum_comp (fun x : s => R x.1 • basisVec x.1.1)).symm
variable (σ : TupleFunctional)
theorem reflectionForm_self_nonneg
    (h : σ.IsReflectionPositive (axialHyperplane TimeAxis.timeIdx 0))
    (F : PositiveSpan) : 0 ≤ reflectionForm σ F F := by
  obtain ⟨J, hJ, X, c, hF⟩ := exists_finite_expansion F
  have hp := h J hJ (fun b => (X b).1) (fun b => by
    rw [axialHyperplane_positiveSide_eq]
    exact (X b).2) c
  rw [axialHyperplane_reflect_eq] at hp
  have key : reflectionForm σ F F = ∑ b, ∑ b', conj (c b) * c b' *
      (σ (SepTuple.juxt (push TimeAxis.timeReflection (X b).1) (X b').1) : ℂ) := by
    have hθ : pushSpan TimeAxis.timeReflection (∑ b, conj (c b) • basisVec (X b).1) =
        ∑ b, conj (c b) • basisVec (push TimeAxis.timeReflection (X b).1) := by
      simp only [map_sum, map_smul, pushSpan_basisVec]
    unfold reflectionForm reflectConj
    rw [hF, conjugation_sum, hθ, formalMul_sum]
    simp only [map_sum, map_smul, spanExtension_basisVec, smul_eq_mul]
  rw [key]
  exact hp
theorem isPosSemidef_reflectionForm
    (h : σ.IsReflectionPositive (axialHyperplane TimeAxis.timeIdx 0)) :
    IsPosSemidef (reflectionForm σ) :=
  { toIsSesquilinear := isSesquilinear_reflectionForm σ, nonneg := reflectionForm_self_nonneg σ h }
theorem juxt_nil (X : SepTuple) : SepTuple.juxt X SepTuple.nil = X := by
  have h : SepTuple.Composable X SepTuple.nil := fun f _ g hg => by
    simp [SepTuple.nil] at hg
  exact Subtype.ext (by rw [SepTuple.juxt_val h]; simp [SepTuple.nil])
theorem nil_juxt (X : SepTuple) : SepTuple.juxt SepTuple.nil X = X := by
  have h : SepTuple.Composable SepTuple.nil X := fun f hf g _ => by
    simp [SepTuple.nil] at hf
  exact Subtype.ext (by rw [SepTuple.juxt_val h]; simp [SepTuple.nil])
theorem reflectionForm_spanBasisIn (X Y : supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ (spanBasisIn TimeAxis.upperHalfSpace X) (spanBasisIn TimeAxis.upperHalfSpace Y) =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by
  simp only [reflectionForm, reflectConj, coe_spanBasisIn, conjugation_basisVec, pushSpan_basisVec,
    formalMul_basisVec, spanExtension_basisVec]
theorem reflectedValuesAgree : ReflectedValuesAgree σ := by
  intro h
  have hH : IsHermitianForm (reflectionForm σ) := (isPosSemidef_reflectionForm σ h).isHermitianForm
  have hE : ∀ X : supportedIn TimeAxis.upperHalfSpace,
      reflectionForm σ unitSpan (spanBasisIn TimeAxis.upperHalfSpace X) = (σ X.1 : ℂ) := fun X => by
    unfold unitSpan
    rw [reflectionForm_spanBasisIn, push_nil, nil_juxt]
  refine ⟨fun X => ⟨?_, hH _ _, ?_⟩, ?_⟩
  · unfold unitSpan
    rw [reflectionForm_spanBasisIn, juxt_nil]
  · rw [hE, Complex.conj_ofReal]
  · unfold unitSpan
    rw [reflectionForm_spanBasisIn, push_nil, juxt_nil, σ.map_nil]
    simp
section Shifts
variable (hPush : BasicFacts.PushSpanProperties)
include hPush
theorem pushSpan_mem_of_image_subset (r : AmbientSpace → AmbientSpace) (hr : IsEuclidIsometry r)
    {U V : Set AmbientSpace} (hU : IsOpen U)
    (hUV : r '' U ⊆ V) {G : FormalSpan} (hG : G ∈ spanIn U) :
    pushSpan r G ∈ spanIn V := by
  have hmap := ((hPush r r hr hr 0 0 0).2.2.2.2.1 U hU).2
  have hm : pushSpan r G ∈ spanIn (r '' U) := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hG
  exact spanIn_mono hUV hm
theorem pushSpan_translate_mem {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) G ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.SeparatedTuples.PositiveTranslates.pushSpan_translate_mem_spanIn <;> assumption
theorem coe_shiftedSpan {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    (shiftedSpan v F).1 = pushSpan (translate v) F.1 := by
  unfold shiftedSpan
  rw [dif_pos (pushSpan_translate_mem hPush hv F.2)]
theorem reflectConj_mem_lowerHalfSpace (F : PositiveSpan) : reflectConj F ∈ spanIn lowerHalfSpace := by
  refine pushSpan_mem_of_image_subset hPush _ isEuclidIsometry_timeReflection isOpen_upperHalfSpace ?_
    (conjugation_mem_spanIn F.2)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : 0 < x 3 := hx
  show TimeAxis.timeReflection x 3 < 0
  simpa [TimeAxis.timeReflection] using hx'
theorem timeReflection_conjugation_translate (a : AmbientSpace) (G : FormalSpan) :
    pushSpan TimeAxis.timeReflection (conjugation (pushSpan (translate a) G)) =
      pushSpan (translate (TimeAxis.timeReflection a))
        (pushSpan TimeAxis.timeReflection (conjugation G)) := by
  have hτ := isEuclidIsometry_translate a
  have hτ' := isEuclidIsometry_translate (TimeAxis.timeReflection a)
  have hθ := isEuclidIsometry_timeReflection
  rw [(hPush _ _ hτ hτ 0 0 G).2.2.2.1, ← (hPush _ _ hθ hτ 0 0 (conjugation G)).1,
    timeReflection_comp_translate, (hPush _ _ hτ' hθ 0 0 (conjugation G)).1]
theorem shiftedSpan_shiftedSpan {a b : AmbientSpace} (ha : 0 ≤ TimeAxis.timeComponent a)
    (hb : 0 ≤ TimeAxis.timeComponent b) (F : PositiveSpan) :
    shiftedSpan a (shiftedSpan b F) = shiftedSpan (a + b) F := by
  have hab : 0 ≤ TimeAxis.timeComponent (a + b) := by
    rw [timeComponent_add]
    linarith
  apply Subtype.ext
  have hτ := isEuclidIsometry_translate a
  rw [coe_shiftedSpan hPush ha, coe_shiftedSpan hPush hb, coe_shiftedSpan hPush hab,
    (hPush _ _ hτ hτ a b F.1).2.1]
theorem reflectedCorrelation_eq_reflectionForm {w : AmbientSpace} (hw : 0 ≤ TimeAxis.timeComponent w)
    (F : PositiveSpan) :
    reflectedCorrelation σ F w = reflectionForm σ F (shiftedSpan w F) := by
  unfold reflectedCorrelation reflectionForm
  rw [coe_shiftedSpan hPush hw]
variable {σ}
omit hPush in
theorem spanExtension_pushSpan_translate (hI : σ.IsTranslateInvariant) (w : AmbientSpace)
    (G : FormalSpan) :
    σ.spanExtension (pushSpan (translate w) G) = σ.spanExtension G := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h, map_smul, map_smul, map_smul, pushSpan_basisVec, spanExtension_basisVec,
      spanExtension_basisVec, hI w X]
theorem spanExtension_formalMul_translate (hI : σ.IsTranslateInvariant) (u : AmbientSpace)
    (F : PositiveSpan) {G' : FormalSpan} (hG' : G' ∈ spanIn TimeAxis.upperHalfSpace) :
    σ.spanExtension (formalMul (pushSpan (translate u) (reflectConj F))
        (pushSpan (translate u) G')) =
      σ.spanExtension (formalMul (reflectConj F) G') := by
  have hτ := isEuclidIsometry_translate u
  rw [(hPush _ _ hτ hτ 0 0 0).2.2.2.2.2 lowerHalfSpace TimeAxis.upperHalfSpace isOpen_lowerHalfSpace
    isOpen_upperHalfSpace disjoint_lowerHalfSpace_upperHalfSpace _
    (reflectConj_mem_lowerHalfSpace hPush F) _ hG',
    spanExtension_pushSpan_translate hI]
theorem reflectionForm_shiftedSpan_right (hI : σ.IsTranslateInvariant) {t : ℝ} (ht : 0 ≤ t)
    (F F' : PositiveSpan) :
    reflectionForm σ F (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F') =
      reflectionForm σ (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F) F' := by
  set w : AmbientSpace := t • PeriodicLattice.coordVec TimeAxis.timeIdx with hw
  have hwt : 0 ≤ TimeAxis.timeComponent w := by rwa [hw, timeComponent_smul_coordVec]
  have hτ := isEuclidIsometry_translate (-w)
  have hback : pushSpan (translate (-w)) (pushSpan (translate w) F'.1) = F'.1 := by
    rw [(hPush _ _ hτ hτ (-w) w F'.1).2.1, neg_add_cancel, (hPush _ _ hτ hτ 0 0 F'.1).2.2.1]
  have hrefl : reflectConj (shiftedSpan w F) =
      pushSpan (translate (-w)) (reflectConj F) := by
    unfold reflectConj
    rw [coe_shiftedSpan hPush hwt, timeReflection_conjugation_translate hPush, hw,
      timeReflection_smul_coordVec]
  unfold reflectionForm
  rw [hrefl, coe_shiftedSpan hPush hwt F', ← spanExtension_formalMul_translate hPush hI (-w) F
    (pushSpan_translate_mem hPush hwt F'.2), hback]
theorem reflectionForm_shiftedSpan_spatial (hI : σ.IsTranslateInvariant) {v : AmbientSpace}
    (hv : TimeAxis.IsPurelySpatial v) (F F' : PositiveSpan) :
    reflectionForm σ (shiftedSpan v F) (shiftedSpan v F') = reflectionForm σ F F' := by
  have hvt : 0 ≤ TimeAxis.timeComponent v := le_of_eq (Eq.symm hv)
  have hrefl : reflectConj (shiftedSpan v F) = pushSpan (translate v) (reflectConj F) := by
    unfold reflectConj
    rw [coe_shiftedSpan hPush hvt, timeReflection_conjugation_translate hPush,
      timeReflection_of_isPurelySpatial hv]
  unfold reflectionForm
  rw [hrefl, coe_shiftedSpan hPush hvt, spanExtension_formalMul_translate hPush hI v F F'.2]
theorem reflectedCorrelation_two_mul (hI : σ.IsTranslateInvariant) {t : ℝ} (ht : 0 ≤ t)
    (F : PositiveSpan) :
    reflectedCorrelation σ F ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) =
      reflectionForm σ (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F)
        (shiftedSpan (t • PeriodicLattice.coordVec TimeAxis.timeIdx) F) := by
  have hwt : 0 ≤ TimeAxis.timeComponent (t • PeriodicLattice.coordVec TimeAxis.timeIdx) := by
    rwa [timeComponent_smul_coordVec]
  have h2 : 0 ≤ TimeAxis.timeComponent ((2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx) := by
    rw [timeComponent_smul_coordVec]
    linarith
  have hsum : (2 * t) • PeriodicLattice.coordVec TimeAxis.timeIdx =
      t • PeriodicLattice.coordVec TimeAxis.timeIdx +
        t • PeriodicLattice.coordVec TimeAxis.timeIdx := by
    rw [← add_smul, two_mul]
  rw [reflectedCorrelation_eq_reflectionForm σ hPush h2, hsum, ← shiftedSpan_shiftedSpan hPush hwt hwt,
    reflectionForm_shiftedSpan_right hPush hI ht]
theorem shiftsCommuteWithForm (F F' : PositiveSpan) :
    ShiftsCommuteWithForm σ F F' := fun hI =>
  ⟨fun _ ht => ⟨reflectionForm_shiftedSpan_right hPush hI ht F F',
      reflectedCorrelation_two_mul hPush hI ht F⟩,
    fun _ hv => reflectionForm_shiftedSpan_spatial hPush hI hv F F'⟩
theorem reflectedCorrelation_nonneg (hI : σ.IsTranslateInvariant)
    (hp : σ.IsReflectionPositive (axialHyperplane TimeAxis.timeIdx 0)) {t : ℝ} (ht : 0 ≤ t)
    (F : PositiveSpan) :
    0 ≤ reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx) := by
  have h := reflectedCorrelation_two_mul hPush hI (t := t / 2) (by linarith) F
  rw [show 2 * (t / 2) = t by ring] at h
  rw [h]
  exact reflectionForm_self_nonneg σ hp _
theorem reflectedCorrelation_sub_eq_conj (hI : σ.IsTranslateInvariant)
    (hp : σ.IsReflectionPositive (axialHyperplane TimeAxis.timeIdx 0)) {t : ℝ} (ht : 0 ≤ t)
    {v : AmbientSpace} (hv : TimeAxis.IsPurelySpatial v) (F : PositiveSpan) :
    reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx - v) =
      conj (reflectedCorrelation σ F (t • PeriodicLattice.coordVec TimeAxis.timeIdx + v)) := by
  set w : AmbientSpace := t • PeriodicLattice.coordVec TimeAxis.timeIdx with hw
  have hv0 : TimeAxis.timeComponent v = 0 := hv
  have hwt : 0 ≤ TimeAxis.timeComponent w := by rwa [hw, timeComponent_smul_coordVec]
  have hvt : 0 ≤ TimeAxis.timeComponent v := hv0.ge
  have hm : 0 ≤ TimeAxis.timeComponent (w - v) := by
    rw [timeComponent_sub, hv0]
    linarith
  have hq : 0 ≤ TimeAxis.timeComponent (w + v) := by
    rw [timeComponent_add, hv0]
    linarith
  have hH : IsHermitianForm (reflectionForm σ) := (isPosSemidef_reflectionForm σ hp).isHermitianForm
  rw [reflectedCorrelation_eq_reflectionForm σ hPush hm, reflectedCorrelation_eq_reflectionForm σ hPush hq,
    ← reflectionForm_shiftedSpan_spatial hPush hI hv F (shiftedSpan (w - v) F),
    shiftedSpan_shiftedSpan hPush hvt hm, show v + (w - v) = w by abel, hw,
    reflectionForm_shiftedSpan_right hPush hI ht, ← hw, shiftedSpan_shiftedSpan hPush hwt hvt]
  exact hH _ _
theorem correlationNonnegConj (F : PositiveSpan) :
    CorrelationNonnegConj σ F := by
  intro hI hp t ht v hv
  have h₁ := reflectedCorrelation_nonneg hPush hI hp ht F
  have h₂ := reflectedCorrelation_sub_eq_conj hPush hI hp ht hv F
  have h₃ := reflectedCorrelation_nonneg hPush hI hp (t := 2 * t) (by linarith) F
  have h₀ := reflectedCorrelation_nonneg hPush hI hp (t := 0) le_rfl F
  rw [zero_smul] at h₀
  refine ⟨h₁, h₂, h₃, reflectionForm_self_nonneg σ hp F, ?_⟩
  have i₀ := (Complex.le_def.1 h₀).2
  have i₁ := (Complex.le_def.1 h₁).2
  have i₃ := (Complex.le_def.1 h₃).2
  simp only [Complex.zero_im] at i₀ i₁ i₃
  rw [h₂]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.conj_im, ← i₀, ← i₁, ← i₃]
  simp
end Shifts
section Continuity
variable {σ}
theorem continuousAt_juxt_value (hPush : BasicFacts.PushSpanProperties)
    (hRefl : BasicFacts.ReflectedJuxtapositionAtHyperplane)
    (hMove : MovingTests.TranslatesTendsto) (hσ : σ.IsAdmissiblyContinuous)
    {X Y : SepTuple} (hX : X ∈ supportedIn TimeAxis.upperHalfSpace)
    (hY : Y ∈ supportedIn TimeAxis.upperHalfSpace) {v : AmbientSpace}
    (hv : 0 ≤ TimeAxis.timeComponent v) :
    ContinuousAt (fun w : AmbientSpace => σ (SepTuple.juxt (push TimeAxis.timeReflection X)
      (push (SeparatedTuples.translate w) Y))) v := by
  have hτ := isEuclidIsometry_translate v
  have hsub : SeparatedTuples.translate v '' TimeAxis.upperHalfSpace ⊆ TimeAxis.upperHalfSpace := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : 0 < TimeAxis.timeComponent x := hx
    show 0 < TimeAxis.timeComponent (x + v)
    rw [timeComponent_add]
    linarith
  have hY' : push (translate v) Y ∈ supportedIn TimeAxis.upperHalfSpace := by
    refine supportedIn_mono hsub ?_
    rw [← ((hPush _ _ hτ hτ 0 0 0).2.2.2.2.1 _ isOpen_upperHalfSpace).1]
    exact ⟨Y, hY, rfl⟩
  have hdef : SepTuple.Composable (push TimeAxis.timeReflection X) (push (translate v) Y) := by
    have h := (hRefl (axialHyperplane TimeAxis.timeIdx 0) X (push (translate v) Y)
      (by rwa [axialHyperplane_positiveSide_eq]) (by rwa [axialHyperplane_positiveSide_eq])).2
    rwa [axialHyperplane_reflect_eq] at h
  refine tendsto_of_seq_tendsto fun w hw => ?_
  obtain ⟨r₀, -, -, hconv, -⟩ := (hMove 1 le_rfl Y w v hw).2 _ hdef
  exact hσ r₀ _ _ hconv
theorem continuousOn_spanExtension_value (hPush : BasicFacts.PushSpanProperties)
    (hRefl : BasicFacts.ReflectedJuxtapositionAtHyperplane)
    (hMove : MovingTests.TranslatesTendsto) (hσ : σ.IsAdmissiblyContinuous)
    {A : FormalSpan} (hA : A ∈ spanIn TimeAxis.upperHalfSpace) :
    ∀ {B : FormalSpan}, B ∈ spanIn TimeAxis.upperHalfSpace →
      ContinuousOn (fun v : AmbientSpace => σ.spanExtension (formalMul
        (pushSpan TimeAxis.timeReflection (conjugation A))
        (pushSpan (translate v) B))) {v | 0 ≤ TimeAxis.timeComponent v} := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    intro B hB
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, rfl⟩ := hy
      simp only [conjugation_basisVec, pushSpan_basisVec, formalMul_basisVec,
        spanExtension_basisVec]
      intro v hv
      exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_juxt_value hPush hRefl hMove hσ X.2 Y.2 hv)).continuousWithinAt
    | zero => simpa using continuousOn_const
    | add y z _ _ hy hz =>
      simp only [map_add]
      exact hy.add hz
    | smul c y _ hy =>
      simp only [map_smul, smul_eq_mul]
      exact continuousOn_const.mul hy
  | zero =>
    intro B _
    simpa using continuousOn_const
  | add y z _ _ hy hz =>
    intro B hB
    simp only [map_add, LinearMap.add_apply]
    exact (hy hB).add (hz hB)
  | smul c y _ hy =>
    intro B hB
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    exact continuousOn_const.mul (hy hB)
theorem continuousInShift (hPush : BasicFacts.PushSpanProperties)
    (hRefl : BasicFacts.ReflectedJuxtapositionAtHyperplane) (hMove : MovingTests.TranslatesTendsto)
    (F F' : PositiveSpan) : ContinuousInShift σ F F' := by
  intro hσ
  refine (continuousOn_spanExtension_value hPush hRefl hMove hσ F.2 F'.2).congr fun v hv => ?_
  unfold reflectionForm reflectConj
  rw [coe_shiftedSpan hPush hv]
end Continuity
theorem assertion_holds (h₁ : SeparatedTuples.BasicFacts.MainFacts) (h₂ : MovingTests.Statement) :
    Assertion := by
  obtain ⟨-, -, hRefl, -, hPush, -⟩ := h₁
  intro σ F F'
  exact ⟨fun h => ⟨isPosSemidef_reflectionForm σ h, (isPosSemidef_reflectionForm σ h).isHermitianForm⟩,
    reflectedValuesAgree σ, shiftsCommuteWithForm hPush F F',
    correlationNonnegConj hPush F,
    continuousInShift hPush hRefl h₂.1 F F'⟩
end YangMills.Construction.ReflectionPositivity.FormProperties
