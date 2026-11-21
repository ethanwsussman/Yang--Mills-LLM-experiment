import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.Functions.DerivativeOfACompositeInDistinctVariablesProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfACommutingPairProof
import YangMills.Construction.SpectralCalculus.SpectralIntegralGenerators
import YangMills.Construction.SpectralCalculus.SpectralResolutionUniqueness
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreePropertiesProof
import YangMills.Construction.TwoPoints.FormIsTheLimitAtRiemannSumsProof
import YangMills.Construction.TwoPoints.OneFieldSpaceAndSlidesAlongTheNormal
import YangMills.Construction.TwoPoints.TranslatesAndSuperpositionsInTheSharpNorm
import Mathlib
set_option autoImplicit false
open scoped NNReal Topology ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction
open SpectralCalculus Filter Set
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
namespace ReflectedSpaceSlides
section Form
theorem dot_add_right (n x y : AmbientSpace) :
    euclidDot n (x + y) = euclidDot n x + euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem dot_sub_right (n x y : AmbientSpace) :
    euclidDot n (x - y) = euclidDot n x - euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_sub_right <;> assumption
theorem dot_smul_right (n x : AmbientSpace) (s : ℝ) :
    euclidDot n (s • x) = s * euclidDot n x := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.euclidDot_smul <;> assumption
theorem dot_comm (x y : AmbientSpace) : euclidDot x y = euclidDot y x := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_comm <;> assumption
theorem dot_self_of_unit {n : AmbientSpace} (hn : euclidNorm n = 1) : euclidDot n n = 1 := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.euclidDot_self_of_unit <;> assumption
theorem dot_le_norm {n : AmbientSpace} (hn : euclidNorm n = 1) (z : AmbientSpace) :
    euclidDot n z ≤ euclidNorm z := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ n z
  rw [show Real.sqrt (∑ μ, n μ ^ 2) = 1 from hn, one_mul] at h
  exact h
theorem euclidNorm_sub_comm (x y : AmbientSpace) : euclidNorm (x - y) = euclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNorm_eq_norm (x : AmbientSpace) : euclidNorm x = ‖WithLp.toLp 2 x‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_smul_unit {m : AmbientSpace} (hm : euclidNorm m = 1) (s : ℝ) :
    euclidNorm (s • m) = |s| := by
  rw [euclidNorm_eq_norm, WithLp.toLp_smul, _root_.norm_smul, ← euclidNorm_eq_norm, hm, mul_one,
    Real.norm_eq_abs]
theorem continuous_dot (n : AmbientSpace) : Continuous (euclidDot n) := by
  unfold euclidDot
  fun_prop
theorem continuous_euclidNorm : Continuous (euclidNorm : AmbientSpace → ℝ) := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.continuous_euclidNorm <;> assumption
theorem separatedBy_of_sides {n : AmbientSpace} (hn : euclidNorm n = 1) {Y Y' : Set AmbientSpace}
    {a a' : ℝ} (hY : ∀ y ∈ Y, euclidDot n y ≤ -a) (hY' : ∀ y ∈ Y', a' ≤ euclidDot n y) :
    SeparatedBy (a + a') Y Y' := by
  intro y hy y' hy'
  rw [euclidNorm_sub_comm]
  have h := dot_le_norm hn (y' - y)
  rw [dot_sub_right] at h
  linarith [hY y hy, hY' y' hy']
theorem reflectAcross_smul_self {n : AmbientSpace} (hn : euclidNorm n = 1) (s : ℝ) :
    reflectAcross n (s • n) = (-s) • n := by
  simp only [reflectAcross, dot_smul_right, dot_self_of_unit hn]
  module
theorem reflectAcross_of_orthogonal {n v : AmbientSpace} (hv : euclidDot v n = 0) :
    reflectAcross n v = v := by
  simp [reflectAcross, dot_comm n v, hv]
section Translates
variable {E : Type*}
theorem translateFun_translateFun (u v : AmbientSpace) (f : AmbientSpace → E) :
    translateFun u (translateFun v f) = translateFun (u + v) f := by
  funext x
  simp only [translateFun, sub_sub]
theorem translateFun_zero (f : AmbientSpace → E) : translateFun 0 f = f := by
  funext x
  simp [translateFun]
end Translates
theorem mem_cc1In_iff (O : Set AmbientSpace) (f : AmbientSpace → ℂ) :
    f ∈ cc1In O ↔ ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O :=
  Iff.rfl
theorem mem_compactC1Complex_of_mem {O : Set AmbientSpace} {f : AmbientSpace → ℂ}
    (hf : f ∈ cc1In O) : f ∈ compactC1Complex :=
  (mem_cc1In_iff _ _).mpr ⟨hf.1, hf.2.1, subset_univ _⟩
theorem addRight_mem_motions (v : AmbientSpace) : Equiv.addRight v ∈ euclideanMotions := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.addRight_mem_euclideanMotions <;> assumption
theorem actOn_addRight (v : AmbientSpace) (f : AmbientSpace → ℂ) :
    actOn (Equiv.addRight v) f = translateFun v f := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.actOn_addRight <;> assumption
abbrev reflConj (n : AmbientSpace) (f : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  reflectFun n (conjFun f)
theorem reflConj_add (n : AmbientSpace) (f g : AmbientSpace → ℂ) :
    reflConj n (f + g) = reflConj n f + reflConj n g := by
  funext x
  simp [reflectFun, conjFun]
theorem reflConj_smul (n : AmbientSpace) (a : ℂ) (f : AmbientSpace → ℂ) :
    reflConj n (a • f) = conj a • reflConj n f := by
  funext x
  simp [reflectFun, conjFun]
theorem conjFun_conjFun (f : AmbientSpace → ℂ) : conjFun (conjFun f) = f := by
  funext x
  simp [conjFun]
theorem conjFun_reflectFun (n : AmbientSpace) (f : AmbientSpace → ℂ) :
    conjFun (reflectFun n f) = reflectFun n (conjFun f) := rfl
theorem conjFun_translateFun (v : AmbientSpace) (f : AmbientSpace → ℂ) :
    conjFun (translateFun v f) = translateFun v (conjFun f) := rfl
structure Setup (St : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (C₂ : ℝ → ℝ → ℝ) (n : AmbientSpace) : Prop where
  unit_norm : euclidNorm n = 1
  normal : n ∈ reflectionNormals
  reflection : IsIsometricInvolutiveReflection n
  reflection_mem : ∃ w ∈ hyperoctahedralPerms, ⇑w = reflectAcross n
  preserves : ∀ f ∈ compactC1Complex, SymmetriesPreserve St f
  symm : ComplexifyDefinedSymm S
  linear : ComplexifyLinear S
  invariant : ComplexifyInvariant S
  conj_comm : ComplexifyConjCommute S
  bound : ComplexifyBallBound St S C₂
  reflPositive : IsReflectionPositive S
  modulus : TranslateModulusBound St
  decay : IsBallDecayBound St S C₂
variable {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {C₂ : ℝ → ℝ → ℝ}
  {n : AmbientSpace}
theorem Setup.reflect_reflect (h : Setup St S C₂ n) (x : AmbientSpace) :
    reflectAcross n (reflectAcross n x) = x :=
  congrFun h.reflection.2.1 x
theorem Setup.dot_reflect (h : Setup St S C₂ n) (x : AmbientSpace) :
    euclidDot n (reflectAcross n x) = -euclidDot n x :=
  h.reflection.2.2.1 x
theorem Setup.translate_preserves (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (v : AmbientSpace) :
    PreservesNormsAndBallSupport St f (translateFun v f) :=
  ((h.preserves f hf).1 v).1
theorem Setup.tsupport_translateFun (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (v : AmbientSpace) {x : AmbientSpace}
    (hx : x ∈ tsupport (translateFun v f)) : ∃ y ∈ tsupport f, x = y + v := by
  rw [((h.preserves f hf).1 v).2.2] at hx
  obtain ⟨y, hy, y', rfl, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩
theorem Setup.conj_preserves (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : PreservesNormsAndBallSupport St f (conjFun f) :=
  (h.preserves f hf).2.2.2.1
theorem Setup.tsupport_conjFun (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : tsupport (conjFun f) = tsupport f :=
  (h.preserves f hf).2.2.2.2.2
theorem Setup.reflect_preserves (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : PreservesNormsAndBallSupport St f (reflectFun n f) :=
  ((h.preserves f hf).2.1 n h.unit_norm).1
theorem Setup.tsupport_reflectFun (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : tsupport (reflectFun n f) = reflectAcross n '' tsupport f :=
  ((h.preserves f hf).2.1 n h.unit_norm).2.2
theorem Setup.reflConj_mem (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : reflConj n f ∈ compactC1Complex :=
  (h.reflect_preserves (h.conj_preserves hf).mem).mem
theorem Setup.sharpNorm_reflConj (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : St.sharpNorm (reflConj n f) = St.sharpNorm f :=
  (h.reflect_preserves (h.conj_preserves hf).mem).sharpNorm_eq.trans
    (h.conj_preserves hf).sharpNorm_eq
theorem Setup.dot_of_mem_tsupport_reflConj (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) {x : AmbientSpace} (hx : x ∈ tsupport (reflConj n f)) :
    ∃ y ∈ tsupport f, euclidDot n x = -euclidDot n y := by
  rw [h.tsupport_reflectFun (h.conj_preserves hf).mem, h.tsupport_conjFun hf] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, h.dot_reflect y⟩
theorem Setup.ball_reflConj (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) {R : ℝ} (hR : 0 < R)
    (hb : ∃ x, tsupport f ⊆ euclidClosedBall x R) :
    ∃ x, tsupport (reflConj n f) ⊆ euclidClosedBall x R := by
  obtain ⟨x, hx⟩ := hb
  obtain ⟨x', hx'⟩ := (h.conj_preserves hf).ballSupport x R hR hx
  exact (h.reflect_preserves (h.conj_preserves hf).mem).ballSupport x' R hR hx'
theorem Setup.disjointPair_reflConj (h : Setup St S C₂ n) {f g : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (hg : g ∈ compactC1Complex)
    (pf : ∀ x ∈ tsupport f, 0 < euclidDot n x) (pg : ∀ x ∈ tsupport g, 0 ≤ euclidDot n x) :
    IsDisjointSupportPair (reflConj n f) g := by
  refine ⟨h.reflConj_mem hf, hg, Set.disjoint_left.mpr fun x hx hx' => ?_⟩
  obtain ⟨y, hy, e⟩ := h.dot_of_mem_tsupport_reflConj hf hx
  have := pf y hy
  have := pg x hx'
  linarith
theorem disjointPair_symm {f g : AmbientSpace → ℂ} (h : IsDisjointSupportPair f g) :
    IsDisjointSupportPair g f :=
  ⟨h.2.1, h.1, Disjoint.symm h.2.2⟩
theorem mem_halfSpaceDomain_iff (f : AmbientSpace → ℂ) : f ∈ halfSpaceDomain n ↔
    ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ posHalfSpace n :=
  Iff.rfl
theorem dot_pos_of_mem {f : AmbientSpace → ℂ} (hf : f ∈ halfSpaceDomain n) :
    ∀ x ∈ tsupport f, 0 < euclidDot n x :=
  fun _ hx => hf.2.2 hx
theorem Setup.disjointPair_domain (h : Setup St S C₂ n) {f g : AmbientSpace → ℂ}
    (hf : f ∈ halfSpaceDomain n) (hg : g ∈ halfSpaceDomain n) :
    IsDisjointSupportPair (reflConj n f) g :=
  h.disjointPair_reflConj (mem_compactC1Complex_of_mem hf) (mem_compactC1Complex_of_mem hg)
    (dot_pos_of_mem hf) fun x hx => (dot_pos_of_mem hg x hx).le
theorem Setup.complexifyForm_translateFun (h : Setup St S C₂ n) (v : AmbientSpace)
    {f g : AmbientSpace → ℂ} (hp : IsDisjointSupportPair f g) :
    complexifyForm S (translateFun v f) (translateFun v g) = complexifyForm S f g := by
  have := (h.invariant _ (addRight_mem_motions v) f g hp).2
  rwa [actOn_addRight, actOn_addRight] at this
theorem Setup.complexifyForm_reflectFun (h : Setup St S C₂ n) {f g : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f g) :
    IsDisjointSupportPair (reflectFun n f) (reflectFun n g) ∧
      complexifyForm S (reflectFun n f) (reflectFun n g) = complexifyForm S f g := by
  obtain ⟨w, hw, he⟩ := h.reflection_mem
  have hinv : ∀ x, w⁻¹ x = reflectAcross n x := fun x => by
    rw [Equiv.Perm.inv_eq_iff_eq, he, h.reflect_reflect]
  have hon : ∀ f : AmbientSpace → ℂ, actOn w f = reflectFun n f := fun f => by
    funext x
    change f (w⁻¹ x) = f (reflectAcross n x)
    rw [hinv]
  have := h.invariant w ⟨w, hw, 0, fun _ => (add_zero _).symm⟩ f g hp
  rwa [hon, hon] at this
theorem Setup.posHermitian (h : Setup St S C₂ n) :
    IsPosHermitianForm (reflectedForm S n) where
  add_left f₁ f₂ g := by
    have hp₁ := h.disjointPair_domain f₁.2 g.2
    have hp₂ := h.disjointPair_domain f₂.2 g.2
    have := (h.linear 1 1 _ _ _ hp₁ hp₂).2.1
    simp only [one_smul, one_mul] at this
    simp only [reflectedForm, Submodule.coe_add, reflConj_add, this]
  smul_left a f g := by
    have hp := h.disjointPair_domain f.2 g.2
    have := (h.linear (conj a) 0 _ _ _ hp hp).2.1
    simp only [zero_smul, add_zero, zero_mul] at this
    simp only [reflectedForm, Submodule.coe_smul, reflConj_smul, this]
  add_right f g₁ g₂ := by
    have hp₁ := disjointPair_symm (h.disjointPair_domain f.2 g₁.2)
    have hp₂ := disjointPair_symm (h.disjointPair_domain f.2 g₂.2)
    have := (h.linear 1 1 _ _ _ hp₁ hp₂).2.2
    simp only [one_smul, one_mul] at this
    simp only [reflectedForm, Submodule.coe_add, this]
  smul_right a f g := by
    have hp := disjointPair_symm (h.disjointPair_domain f.2 g.2)
    have := (h.linear a 0 _ _ _ hp hp).2.2
    simp only [zero_smul, add_zero, zero_mul] at this
    simp only [reflectedForm, Submodule.coe_smul, this]
  conj_symm f g := by
    have hp := h.disjointPair_domain f.2 g.2
    have hq := h.disjointPair_domain g.2 f.2
    have e₁ := (h.symm _ _ hq).2
    have hr := h.complexifyForm_reflectFun (disjointPair_symm hq)
    have hθ : reflectFun n (reflConj n (g : AmbientSpace → ℂ)) = conjFun g := by
      funext x
      simp [reflectFun, Function.comp, h.reflect_reflect]
    have e₂ := hr.2
    rw [hθ] at e₂
    have hc := (h.conj_comm _ _ hp).2
    have hθ' : conjFun (reflConj n (f : AmbientSpace → ℂ)) = reflectFun n f := by
      rw [conjFun_reflectFun, conjFun_conjFun]
    rw [hθ'] at hc
    simp only [reflectedForm]
    rw [e₁, ← e₂, hc]
  nonneg f := by
    have := (h.reflPositive n h.normal f f.2).2
    exact Complex.le_def.mpr ⟨by simpa [reflectedForm] using this.2,
      by simpa [reflectedForm] using this.1.symm⟩
end Form
section Translations
variable {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {C₂ : ℝ → ℝ → ℝ}
  {n : AmbientSpace}
theorem zero_le_sharpNorm (St : FixedScale) (f : AmbientSpace → ℂ) : 0 ≤ St.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem Setup.translateFun_mem (h : Setup St S C₂ n) {v : AmbientSpace}
    (hv : 0 ≤ euclidDot n v) {f : AmbientSpace → ℂ} (hf : f ∈ halfSpaceDomain n) :
    translateFun v f ∈ halfSpaceDomain n := by
  have hc := mem_compactC1Complex_of_mem hf
  have hk := h.translate_preserves hc v
  refine (mem_halfSpaceDomain_iff _).mpr ⟨hk.mem.1, hk.mem.2.1, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := h.tsupport_translateFun hc v hx
  change 0 < euclidDot n (y + v)
  rw [dot_add_right]
  linarith [dot_pos_of_mem hf y hy]
def Setup.shiftMap (h : Setup St S C₂ n) (v : AmbientSpace) (hv : 0 ≤ euclidDot n v) :
    halfSpaceDomain n →ₗ[ℂ] halfSpaceDomain n where
  toFun f := ⟨translateFun v f, h.translateFun_mem hv f.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)
theorem Setup.complexifyForm_shift (h : Setup St S C₂ n) {f g : AmbientSpace → ℂ}
    (hf : f ∈ halfSpaceDomain n) (hg : g ∈ halfSpaceDomain n) (v u : AmbientSpace)
    (hu : 0 ≤ euclidDot n u) :
    complexifyForm S (reflConj n (translateFun v f))
        (translateFun (reflectAcross n v + u) g) =
      complexifyForm S (reflConj n f) (translateFun u g) := by
  have e : reflConj n (translateFun v f) =
      translateFun (reflectAcross n v) (reflConj n f) := by
    rw [reflConj, conjFun_translateFun]
    exact (h.reflection.2.2.2 ℂ (conjFun f) v 0).1
  rw [e, ← translateFun_translateFun]
  exact h.complexifyForm_translateFun _ (h.disjointPair_domain hf (h.translateFun_mem hu hg))
theorem Setup.dot_smul_self (h : Setup St S C₂ n) (s : ℝ) : euclidDot n (s • n) = s := by
  rw [dot_smul_right, dot_self_of_unit h.unit_norm, mul_one]
theorem Setup.dot_smul_nonneg (h : Setup St S C₂ n) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ euclidDot n (s • n) := by
  rwa [h.dot_smul_self]
theorem Setup.shiftMap_symm (h : Setup St S C₂ n) {s : ℝ} (hs : 0 ≤ s)
    (f g : halfSpaceDomain n) :
    reflectedForm S n (h.shiftMap (s • n) (h.dot_smul_nonneg hs) f) g =
      reflectedForm S n f (h.shiftMap (s • n) (h.dot_smul_nonneg hs) g) := by
  have := h.complexifyForm_shift f.2 g.2 (s • n) (s • n) (h.dot_smul_nonneg hs)
  rw [reflectAcross_smul_self h.unit_norm, show (-s) • n + s • n = 0 by module,
    translateFun_zero] at this
  exact this
theorem Setup.shiftMap_self (h : Setup St S C₂ n) {t : ℝ} (ht : 0 ≤ t) (f : halfSpaceDomain n) :
    reflectedForm S n (h.shiftMap (t • n) (h.dot_smul_nonneg ht) f)
        (h.shiftMap (t • n) (h.dot_smul_nonneg ht) f) =
      reflectedForm S n f (h.shiftMap ((2 * t) • n) (h.dot_smul_nonneg (by positivity)) f) := by
  have := h.complexifyForm_shift f.2 f.2 (t • n) ((2 * t) • n) (h.dot_smul_nonneg (by positivity))
  rw [reflectAcross_smul_self h.unit_norm, show (-t) • n + (2 * t) • n = t • n by module] at this
  exact this
theorem Setup.shiftMap_isometry (h : Setup St S C₂ n) {v : AmbientSpace}
    (hv : euclidDot v n = 0) (hv' : 0 ≤ euclidDot n v) (f g : halfSpaceDomain n) :
    reflectedForm S n (h.shiftMap v hv' f) (h.shiftMap v hv' g) = reflectedForm S n f g := by
  have := h.complexifyForm_shift f.2 g.2 v 0 (by simp [euclidDot])
  rw [reflectAcross_of_orthogonal hv, add_zero, translateFun_zero] at this
  exact this
theorem exists_height_radius {f : AmbientSpace → ℂ} (hf : f ∈ halfSpaceDomain n) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ (∀ x ∈ tsupport f, δ ≤ euclidDot n x) ∧
      tsupport f ⊆ euclidClosedBall 0 R := by
  have hK : IsCompact (tsupport f) := hf.2.1
  obtain ⟨R, hR⟩ := hK.bddAbove_image continuous_euclidNorm.continuousOn
  have hball : tsupport f ⊆ euclidClosedBall 0 (max R 1) := fun x hx => by
    change euclidNorm (x - 0) ≤ _
    rw [sub_zero]
    exact (hR ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  have hpos : 0 < max R 1 := lt_max_of_lt_right one_pos
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne (continuous_dot n).continuousOn
    exact ⟨_, _, dot_pos_of_mem hf x₀ hx₀, hpos, fun x hx => hmin hx, hball⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    exact ⟨1, _, one_pos, hpos, by simp [hne], hball⟩
theorem Setup.norm_complexifyForm_le (h : Setup St S C₂ n) {f g : AmbientSpace → ℂ}
    (hf : f ∈ halfSpaceDomain n) (hg : g ∈ halfSpaceDomain n) {δ R : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (sf : ∀ x ∈ tsupport f, δ ≤ euclidDot n x)
    (sg : ∀ x ∈ tsupport g, δ ≤ euclidDot n x)
    (bf : ∃ x, tsupport f ⊆ euclidClosedBall x R) (bg : ∃ x, tsupport g ⊆ euclidClosedBall x R) :
    ‖complexifyForm S (reflConj n f) g‖ ≤
      4 * C₂ (2 * δ) R * St.sharpNorm f * St.sharpNorm g := by
  have hfc := mem_compactC1Complex_of_mem hf
  obtain ⟨x, hx⟩ := h.ball_reflConj hfc hR bf
  obtain ⟨x', hx'⟩ := bg
  have hd : SeparatedBy (2 * δ) (tsupport (reflConj n f)) (tsupport g) := by
    rw [two_mul]
    refine separatedBy_of_sides h.unit_norm (fun y hy => ?_) sg
    obtain ⟨y', hy', e⟩ := h.dot_of_mem_tsupport_reflConj hfc hy
    linarith [sf y' hy']
  have := h.bound (2 * δ) R (by positivity) hR x x' _ (h.reflConj_mem hfc) g
    (mem_compactC1Complex_of_mem hg) hx hx' hd
  rwa [h.sharpNorm_reflConj hfc] at this
theorem Setup.bddAbove_seminorm_shift (h : Setup St S C₂ n) (f : halfSpaceDomain n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ) (ht : 0 ≤ t),
      formSeminorm (reflectedForm S n) (h.shiftMap (t • n) (h.dot_smul_nonneg ht) f) ≤ B := by
  obtain ⟨δ, R, hδ, hR, sf, bf⟩ := exists_height_radius f.2
  have hfc := mem_compactC1Complex_of_mem f.2
  refine ⟨Real.sqrt (4 * C₂ (2 * δ) R * St.sharpNorm f * St.sharpNorm f), Real.sqrt_nonneg _,
    fun t ht => ?_⟩
  refine Real.sqrt_le_sqrt ?_
  rw [h.shiftMap_self ht]
  have h2 : 0 ≤ 2 * t := by positivity
  have hk := h.translate_preserves hfc ((2 * t) • n)
  have hb := h.norm_complexifyForm_le f.2 (h.translateFun_mem (h.dot_smul_nonneg h2) f.2) hδ hR sf
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := h.tsupport_translateFun hfc _ hx
      rw [dot_add_right, h.dot_smul_self]
      linarith [sf y hy])
    ⟨0, bf⟩ (hk.ballSupport 0 R hR bf)
  rw [hk.sharpNorm_eq] at hb
  exact (Complex.re_le_norm _).trans hb
theorem Setup.seminorm_shift_le (h : Setup St S C₂ n) (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
    {s : ℝ} (hs : 0 ≤ s) (f : halfSpaceDomain n) :
    formSeminorm (reflectedForm S n) (h.shiftMap (s • n) (h.dot_smul_nonneg hs) f) ≤
      formSeminorm (reflectedForm S n) f := by
  obtain ⟨B, hB, hb⟩ := h.bddAbove_seminorm_shift f
  set A : halfSpaceDomain n → halfSpaceDomain n :=
    fun g => h.shiftMap (s • n) (h.dot_smul_nonneg hs) g with hA
  have hiter : ∀ k : ℕ, ∃ hk : 0 ≤ (k : ℝ) * s, A^[k] f = h.shiftMap (((k : ℝ) * s) • n)
      (h.dot_smul_nonneg hk) f := by
    intro k
    refine ⟨by positivity, ?_⟩
    induction k with
    | zero =>
      refine Subtype.ext ?_
      simp [Setup.shiftMap, translateFun_zero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      refine Subtype.ext ?_
      change translateFun (s • n) (translateFun (((k : ℝ) * s) • n) (f : AmbientSpace → ℂ)) =
        translateFun _ _
      rw [translateFun_translateFun]
      congr 1
      push_cast
      module
  have hfin := (hI (halfSpaceDomain n) (reflectedForm S n) A h.posHermitian
    (fun f g => h.shiftMap_symm hs f g)).2 f 1 B zero_le_one hB (fun k m _ hm => by
      obtain ⟨hk, e⟩ := hiter m
      have hm1 : (1 : ℝ) ≤ m := by
        rw [hm]
        exact_mod_cast Nat.one_le_two_pow
      rw [e, one_pow, mul_one]
      exact (hb _ hk).trans (le_mul_of_one_le_right hB hm1))
  simpa using hfin
def transOp (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (n v : AmbientSpace) :
    ReflectedSpace S n →L[ℂ] ReflectedSpace S n :=
  Classical.epsilon (ActsByTranslation S n v)
def Setup.IsContractive (h : Setup St S C₂ n) (v : AmbientSpace) (hv : 0 ≤ euclidDot n v) :
    Prop :=
  ∀ f, formSeminorm (reflectedForm S n) (h.shiftMap v hv f) ≤ formSeminorm (reflectedForm S n) f
theorem Setup.actsByTranslation_iff (h : Setup St S C₂ n) (v : AmbientSpace)
    (hv : 0 ≤ euclidDot n v) (B : ReflectedSpace S n →L[ℂ] ReflectedSpace S n) :
    ActsByTranslation S n v B ↔ IsCompletionExtension (reflectedForm S n) (h.shiftMap v hv) B := by
  constructor
  · intro hB f
    obtain ⟨_, he⟩ := hB f
    exact he
  · intro hB f
    exact ⟨h.translateFun_mem hv f.2, hB f⟩
theorem Setup.isContractive_add (h : Setup St S C₂ n) {v w : AmbientSpace}
    {hv : 0 ≤ euclidDot n v} {hw : 0 ≤ euclidDot n w}
    (hcv : h.IsContractive v hv) (hcw : h.IsContractive w hw) (hvw : 0 ≤ euclidDot n (v + w)) :
    h.IsContractive (v + w) hvw := by
  intro f
  have e : h.shiftMap (v + w) hvw f = h.shiftMap v hv (h.shiftMap w hw f) :=
    Subtype.ext (translateFun_translateFun v w (f : AmbientSpace → ℂ)).symm
  rw [e]
  exact (hcv _).trans (hcw _)
theorem Setup.shiftMap_zero (h : Setup St S C₂ n) (hz : 0 ≤ euclidDot n (0 : AmbientSpace))
    (f : halfSpaceDomain n) : h.shiftMap 0 hz f = f :=
  Subtype.ext (translateFun_zero _)
theorem Setup.isContractive_zero (h : Setup St S C₂ n)
    (hz : 0 ≤ euclidDot n (0 : AmbientSpace)) : h.IsContractive 0 hz := fun f => by
  rw [h.shiftMap_zero]
theorem dot_zero_nonneg : 0 ≤ euclidDot n (0 : AmbientSpace) := by
  simp [euclidDot]
section Operators
variable (hC : FormCompletionAndBoundedExtension)
include hC
theorem Setup.extBasics (h : Setup St S C₂ n) {v : AmbientSpace} {hv : 0 ≤ euclidDot n v}
    (hc : h.IsContractive v hv) :
    CompletionExtensionBasics (reflectedForm S n) (h.shiftMap v hv) 1 :=
  (hC.1 _ _ h.posHermitian).2.2 _ 1 ⟨zero_le_one, fun f => by simpa using hc f⟩
theorem Setup.transOp_isExtension (h : Setup St S C₂ n) {v : AmbientSpace}
    {hv : 0 ≤ euclidDot n v} (hc : h.IsContractive v hv) :
    IsCompletionExtension (reflectedForm S n) (h.shiftMap v hv) (transOp S n v) := by
  obtain ⟨T, hT, -⟩ := (h.extBasics hC hc).existsUnique_extension
  exact (h.actsByTranslation_iff v hv _).mp
    (Classical.epsilon_spec (p := ActsByTranslation S n v)
      ⟨T, (h.actsByTranslation_iff v hv T).mpr hT⟩)
theorem Setup.transOp_class (h : Setup St S C₂ n) {v : AmbientSpace} {hv : 0 ≤ euclidDot n v}
    (hc : h.IsContractive v hv) (f : halfSpaceDomain n) :
    transOp S n v (reflectedClass S n f) = reflectedClass S n (h.shiftMap v hv f) :=
  h.transOp_isExtension hC hc f
theorem Setup.norm_transOp_le (h : Setup St S C₂ n) {v : AmbientSpace}
    {hv : 0 ≤ euclidDot n v} (hc : h.IsContractive v hv) : ‖transOp S n v‖ ≤ 1 :=
  (h.extBasics hC hc).norm_le _ (h.transOp_isExtension hC hc)
theorem Setup.transOp_mul (h : Setup St S C₂ n) {v w : AmbientSpace}
    {hv : 0 ≤ euclidDot n v} {hw : 0 ≤ euclidDot n w}
    (hcv : h.IsContractive v hv) (hcw : h.IsContractive w hw) :
    transOp S n v * transOp S n w = transOp S n (v + w) := by
  have hvw : 0 ≤ euclidDot n (v + w) := by
    rw [dot_add_right]
    exact add_nonneg hv hw
  have hc := h.isContractive_add hcv hcw hvw
  refine ((h.extBasics hC hcv).extension_comp (h.shiftMap w hw) 1
    ⟨zero_le_one, fun f => by simpa using hcw f⟩ _ _ _ (h.transOp_isExtension hC hcv)
    (h.transOp_isExtension hC hcw) (fun f => ?_)).symm
  have e : (h.shiftMap v hv ∘ₗ h.shiftMap w hw) f = h.shiftMap (v + w) hvw f :=
    Subtype.ext (translateFun_translateFun v w (f : AmbientSpace → ℂ))
  rw [e]
  exact h.transOp_isExtension hC hc f
theorem Setup.transOp_zero (h : Setup St S C₂ n) : transOp S n 0 = 1 := by
  have hz : 0 ≤ euclidDot n (0 : AmbientSpace) := dot_zero_nonneg
  have hc := h.isContractive_zero hz
  refine (h.extBasics hC hc).existsUnique_extension.unique (h.transOp_isExtension hC hc)
    fun f => ?_
  rw [h.shiftMap_zero]
  rfl
theorem Setup.translationExtendsUniquely (h : Setup St S C₂ n) {v : AmbientSpace}
    {hv : 0 ≤ euclidDot n v} (hc : h.IsContractive v hv) :
    TranslationExtendsUniquely S n v := by
  refine ⟨⟨fun f => h.translateFun_mem hv f.2, fun f f' e => ?_⟩, ?_⟩
  · exact (h.extBasics hC hc).constClass_map_eq f f' e
  · obtain ⟨T, hT, hu⟩ := (h.extBasics hC hc).existsUnique_extension
    exact ⟨T, (h.actsByTranslation_iff v hv T).mpr hT, fun B hB =>
      hu B ((h.actsByTranslation_iff v hv B).mp hB)⟩
theorem Setup.reflectedClass_sub (h : Setup St S C₂ n) (f g : halfSpaceDomain n) :
    reflectedClass S n (f - g) = reflectedClass S n f - reflectedClass S n g :=
  ((hC.1 _ _ h.posHermitian).2.1.isLinearMap_constClass.mk' _).map_sub f g
theorem Setup.norm_reflectedClass (h : Setup St S C₂ n) (f : halfSpaceDomain n) :
    ‖reflectedClass S n f‖ = formSeminorm (reflectedForm S n) f := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), formSeminorm]
  congr 1
  exact congrArg Complex.re ((hC.1 _ _ h.posHermitian).2.1.inner_constClass f f)
theorem Setup.inner_reflectedClass (h : Setup St S C₂ n) (f g : halfSpaceDomain n) :
    inner ℂ (reflectedClass S n f) (reflectedClass S n g) = reflectedForm S n f g :=
  (hC.1 _ _ h.posHermitian).2.1.inner_constClass f g
theorem Setup.dense_range_reflectedClass (h : Setup St S C₂ n) :
    Dense (range (reflectedClass S n)) :=
  (isSeqDense_iff_dense _).mp (hC.1 _ _ h.posHermitian).2.1.isSeqDense_range_constClass
end Operators
end Translations
section Generators
variable {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {C₂ : ℝ → ℝ → ℝ}
  {n : AmbientSpace}
theorem Setup.reflectedForm_sub_right (h : Setup St S C₂ n) (f g g' : halfSpaceDomain n) :
    reflectedForm S n f (g - g') = reflectedForm S n f g - reflectedForm S n f g' := by
  have hf := h.posHermitian
  rw [sub_eq_add_neg, hf.add_right, ← neg_one_smul ℂ g', hf.smul_right]
  ring
theorem Setup.reflectedForm_sub_left (h : Setup St S C₂ n) (f f' g : halfSpaceDomain n) :
    reflectedForm S n (f - f') g = reflectedForm S n f g - reflectedForm S n f' g := by
  have hf := h.posHermitian
  rw [sub_eq_add_neg, hf.add_left, ← neg_one_smul ℂ f', hf.smul_left]
  simp
  ring
theorem tsupport_sub_subset_union (f g : AmbientSpace → ℂ) :
    tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by apply _root_.YangMills.Construction.TwoPoints.FormIsGridSumLimit.tsupport_sub_subset_union <;> assumption
theorem Setup.tendsto_reflectedForm_shift (h : Setup St S C₂ n) (f : halfSpaceDomain n)
    {ι : Type*} {l : Filter ι} (z : ι → AmbientSpace) (hz : ∀ i, 0 ≤ euclidDot n (z i))
    (hl : Tendsto (fun i => euclidNorm (z i)) l (𝓝[>] 0)) :
    Tendsto (fun i => reflectedForm S n f (h.shiftMap (z i) (hz i) f)) l
      (𝓝 (reflectedForm S n f f)) := by
  obtain ⟨δ, R, hδ, hR, sf, bf⟩ := exists_height_radius f.2
  have hfc := mem_compactC1Complex_of_mem f.2
  have hmod := h.modulus f hfc
  have hlim : Tendsto (fun i => St.translationModulus f (euclidNorm (z i))) l (𝓝 0) :=
    hmod.2.2.2.2.2.comp hl
  have hsmall : ∀ᶠ i in l, euclidNorm (z i) < 2 :=
    (hl.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds two_pos)
  have hR2 : 0 < R + 2 := by positivity
  set M : ℝ := 4 * C₂ (2 * δ) (R + 2) * St.sharpNorm f with hMdef
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num)
    (h.decay.1 _ _ (by positivity) hR2)) (zero_le_sharpNorm St _)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (by simpa using hlim.const_mul M)
  filter_upwards [hsmall] with i hi
  rw [← h.reflectedForm_sub_right]
  have hball : ∀ x ∈ tsupport (f : AmbientSpace → ℂ), euclidNorm (x - 0) ≤ R :=
    fun x hx => bf hx
  have hfb : tsupport (f : AmbientSpace → ℂ) ⊆ euclidClosedBall 0 (R + 2) := fun x hx => by
    have := hball x hx
    change euclidNorm (x - 0) ≤ R + 2
    linarith
  set g : halfSpaceDomain n := h.shiftMap (z i) (hz i) f - f with hg
  have hgc : (g : AmbientSpace → ℂ) = translateFun (z i) (f : AmbientSpace → ℂ) - f := rfl
  have hsupp : ∀ x ∈ tsupport (g : AmbientSpace → ℂ),
      (∃ y ∈ tsupport (f : AmbientSpace → ℂ), x = y + z i) ∨
        x ∈ tsupport (f : AmbientSpace → ℂ) := fun x hx => by
    rw [hgc] at hx
    rcases tsupport_sub_subset_union _ _ hx with hx | hx
    · exact Or.inl (h.tsupport_translateFun hfc _ hx)
    · exact Or.inr hx
  have hb := h.norm_complexifyForm_le f.2 g.2 hδ hR2 sf
    (fun x hx => by
      rcases hsupp x hx with ⟨y, hy, rfl⟩ | hx'
      · rw [dot_add_right]
        linarith [sf y hy, hz i]
      · exact sf x hx')
    ⟨0, hfb⟩
    ⟨0, fun x hx => by
      rcases hsupp x hx with ⟨y, hy, rfl⟩ | hx'
      · change euclidNorm (y + z i - 0) ≤ R + 2
        rw [sub_zero]
        have h1 := euclidNorm_add_le y (z i)
        have h2 := hball y hy
        rw [sub_zero] at h2
        linarith
      · exact hfb hx'⟩
  have hs : St.sharpNorm (g : AmbientSpace → ℂ) ≤ St.translationModulus f (euclidNorm (z i)) := by
    have := hmod.2.2.2.2.1 (z i) 0
    rwa [translateFun_zero, sub_zero] at this
  calc ‖reflectedForm S n f g‖ ≤ M * St.sharpNorm (g : AmbientSpace → ℂ) := hb
    _ ≤ M * St.translationModulus f (euclidNorm (z i)) := mul_le_mul_of_nonneg_left hs hM
theorem tendsto_apply_of_dense {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {l : Filter ι} {D : Set H} (hD : Dense D) (A : ι → H →L[ℂ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hl : ∀ u ∈ D, Tendsto (fun i => A i u) l (𝓝 u)) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 v) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨u, hu, hvu⟩ := hD.exists_dist_lt v (show 0 < ε / 3 by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (hl u hu) (ε / 3) (by positivity)] with i hi
  have h1 : dist (A i v) (A i u) ≤ dist v u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖A i (v - u)‖ ≤ ‖A i‖ * ‖v - u‖ := (A i).le_opNorm _
      _ ≤ 1 * ‖v - u‖ := by gcongr; exact hA i
      _ = ‖v - u‖ := one_mul _
  have h2 := dist_triangle4 (A i v) (A i u) u v
  rw [dist_comm u v] at h2
  linarith
section Operators
variable (hC : FormCompletionAndBoundedExtension)
include hC
theorem Setup.tendsto_reflectedClass_shift (h : Setup St S C₂ n) (f : halfSpaceDomain n)
    {ι : Type*} {l : Filter ι} (z : ι → AmbientSpace) (hz : ∀ i, 0 ≤ euclidDot n (z i))
    (hq : Tendsto (fun i => reflectedForm S n (h.shiftMap (z i) (hz i) f)
      (h.shiftMap (z i) (hz i) f)) l (𝓝 (reflectedForm S n f f)))
    (hc : Tendsto (fun i => reflectedForm S n f (h.shiftMap (z i) (hz i) f)) l
      (𝓝 (reflectedForm S n f f))) :
    Tendsto (fun i => reflectedClass S n (h.shiftMap (z i) (hz i) f)) l
      (𝓝 (reflectedClass S n f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hform := h.posHermitian
  have e : ∀ i, ‖reflectedClass S n (h.shiftMap (z i) (hz i) f) - reflectedClass S n f‖ =
      Real.sqrt ((reflectedForm S n (h.shiftMap (z i) (hz i) f) (h.shiftMap (z i) (hz i) f) -
        conj (reflectedForm S n f (h.shiftMap (z i) (hz i) f)) -
        reflectedForm S n f (h.shiftMap (z i) (hz i) f) + reflectedForm S n f f).re) := fun i => by
    rw [← h.reflectedClass_sub hC, h.norm_reflectedClass hC, formSeminorm,
      h.reflectedForm_sub_left, h.reflectedForm_sub_right, h.reflectedForm_sub_right,
      hform.conj_symm f (h.shiftMap (z i) (hz i) f)]
    congr 2
    ring
  simp_rw [e]
  have hself : conj (reflectedForm S n f f) = reflectedForm S n f f :=
    (hform.conj_symm f f).symm
  have hcc := (Complex.continuous_conj.tendsto _).comp hc
  rw [hself] at hcc
  have hs := ((hq.sub hcc).sub hc).add (tendsto_const_nhds (x := reflectedForm S n f f))
  have hz0 : reflectedForm S n f f - reflectedForm S n f f - reflectedForm S n f f +
      reflectedForm S n f f = 0 := by ring
  rw [hz0] at hs
  have := (Real.continuous_sqrt.tendsto _).comp ((Complex.continuous_re.tendsto _).comp hs)
  have h0 : Real.sqrt (Complex.re 0) = 0 := by simp
  rw [h0] at this
  exact this
end Operators
theorem transferSemigroup_apply (s : ℝ≥0) :
    transferSemigroup S n s = transOp S n ((s : ℝ) • n) := rfl
theorem lateralGroup_apply (m' : AmbientSpace) (s : ℝ) :
    lateralGroup S n m' s = transOp S n (s • m') := rfl
theorem Setup.isContractive_normal (h : Setup St S C₂ n)
    (hI : HilbertSpace.IteratedCauchySchwarz.Claim) (s : ℝ≥0) :
    h.IsContractive ((s : ℝ) • n) (h.dot_smul_nonneg s.2) :=
  fun f => h.seminorm_shift_le hI s.2 f
theorem tendsto_euclidNorm_smul_normal (h : Setup St S C₂ n) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 => euclidNorm ((c * (t : ℝ)) • n)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have e : (fun t : ℝ≥0 => euclidNorm ((c * (t : ℝ)) • n)) = fun t : ℝ≥0 => c * (t : ℝ) := by
      funext t
      rw [euclidNorm_smul_unit h.unit_norm, abs_of_nonneg (by positivity)]
    rw [e]
    have : Tendsto (fun t : ℝ≥0 => c * (t : ℝ)) (𝓝 0) (𝓝 (c * ((0 : ℝ≥0) : ℝ))) :=
      (NNReal.continuous_coe.tendsto 0).const_mul c
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    rw [mem_Ioi, euclidNorm_smul_unit h.unit_norm, abs_of_nonneg (by positivity)]
    positivity
theorem Setup.isSelfAdjointContractionSemigroup (h : Setup St S C₂ n)
    (hC : FormCompletionAndBoundedExtension) (hI : HilbertSpace.IteratedCauchySchwarz.Claim) :
    IsSelfAdjointContractionSemigroup (transferSemigroup S n) where
  isSymmetricBounded t u v := by
    have hc := h.isContractive_normal hI t
    exact (h.extBasics hC hc).extension_adjoint _ 1 ⟨zero_le_one, fun f => by simpa using hc f⟩
      _ _ (h.transOp_isExtension hC hc) (h.transOp_isExtension hC hc)
      (fun f g => h.shiftMap_symm t.2 f g) u v
  isContractive t := h.norm_transOp_le hC (h.isContractive_normal hI t)
  map_zero := by
    rw [transferSemigroup_apply]
    simpa using h.transOp_zero hC
  map_add t t' := by
    rw [transferSemigroup_apply, transferSemigroup_apply, transferSemigroup_apply,
      h.transOp_mul hC (h.isContractive_normal hI t) (h.isContractive_normal hI t'),
      NNReal.coe_add, add_smul]
  tendsto v := by
    refine tendsto_apply_of_dense (h.dense_range_reflectedClass hC) (transferSemigroup S n)
      (fun t => h.norm_transOp_le hC (h.isContractive_normal hI t)) ?_ v
    rintro _ ⟨f, rfl⟩
    have h1 : Tendsto (fun t : ℝ≥0 => euclidNorm ((t : ℝ) • n)) (𝓝[>] 0) (𝓝[>] 0) := by
      simpa using tendsto_euclidNorm_smul_normal h one_pos
    have hc := h.tendsto_reflectedForm_shift f (fun t : ℝ≥0 => (t : ℝ) • n)
      (fun t => h.dot_smul_nonneg t.2) h1
    have hq0 := h.tendsto_reflectedForm_shift f (fun t : ℝ≥0 => (2 * (t : ℝ)) • n)
      (fun t => h.dot_smul_nonneg (by positivity)) (tendsto_euclidNorm_smul_normal h two_pos)
    have hq : Tendsto (fun t : ℝ≥0 =>
        reflectedForm S n (h.shiftMap ((t : ℝ) • n) (h.dot_smul_nonneg t.2) f)
        (h.shiftMap ((t : ℝ) • n) (h.dot_smul_nonneg t.2) f)) (𝓝[>] 0)
        (𝓝 (reflectedForm S n f f)) :=
      hq0.congr fun t => (h.shiftMap_self t.2 f).symm
    refine (h.tendsto_reflectedClass_shift hC f _ _ hq hc).congr fun t => ?_
    exact (h.transOp_class hC (h.isContractive_normal hI t) f).symm
theorem Setup.hasTransferSemigroup (h : Setup St S C₂ n)
    (hC : FormCompletionAndBoundedExtension) (hI : HilbertSpace.IteratedCauchySchwarz.Claim) :
    HasTransferSemigroup S n where
  posHermitian := h.posHermitian
  complete := isCompleteForm_inner
  translation_extends s := h.translationExtendsUniquely hC (h.isContractive_normal hI s)
  selfAdjointContraction := h.isSelfAdjointContractionSemigroup hC hI
section Group
variable {m' : AmbientSpace}
theorem dot_smul_orthogonal (hm : IsUnitNormalTo n m') (s : ℝ) : euclidDot (s • m') n = 0 := by
  rw [dot_comm, dot_smul_right, dot_comm, hm.2, mul_zero]
theorem dot_smul_orthogonal_nonneg (hm : IsUnitNormalTo n m') (s : ℝ) :
    0 ≤ euclidDot n (s • m') := by
  rw [dot_comm, dot_smul_orthogonal hm]
theorem Setup.seminorm_lateral_eq (h : Setup St S C₂ n) (hm : IsUnitNormalTo n m') (s : ℝ)
    (f : halfSpaceDomain n) :
    formSeminorm (reflectedForm S n) (h.shiftMap (s • m') (dot_smul_orthogonal_nonneg hm s) f) =
      formSeminorm (reflectedForm S n) f := by
  rw [formSeminorm, formSeminorm, h.shiftMap_isometry (dot_smul_orthogonal hm s)]
theorem Setup.isContractive_lateral (h : Setup St S C₂ n) (hm : IsUnitNormalTo n m') (s : ℝ) :
    h.IsContractive (s • m') (dot_smul_orthogonal_nonneg hm s) :=
  fun f => (h.seminorm_lateral_eq hm s f).le
theorem Setup.stronglyContinuousUnitary (h : Setup St S C₂ n)
    (hC : FormCompletionAndBoundedExtension) (hm : IsUnitNormalTo n m') :
    IsStronglyContinuousUnitaryGroup (lateralGroup S n m') := by
  have hmul : ∀ s s', lateralGroup S n m' s * lateralGroup S n m' s' =
      lateralGroup S n m' (s + s') := fun s s' => by
    rw [lateralGroup_apply, lateralGroup_apply, lateralGroup_apply,
      h.transOp_mul hC (h.isContractive_lateral hm s) (h.isContractive_lateral hm s'), add_smul]
  have hzero : lateralGroup S n m' 0 = 1 := by
    rw [lateralGroup_apply]
    simpa using h.transOp_zero hC
  refine ⟨fun s => ⟨?_, fun v => ?_⟩, hzero, hmul, fun v => ?_⟩
  · have h₁ : lateralGroup S n m' s * lateralGroup S n m' (-s) = 1 := by
      rw [hmul, add_neg_cancel, hzero]
    have h₂ : lateralGroup S n m' (-s) * lateralGroup S n m' s = 1 := by
      rw [hmul, neg_add_cancel, hzero]
    refine Function.bijective_iff_has_inverse.mpr
      ⟨lateralGroup S n m' (-s), fun v => ?_, fun v => ?_⟩
    · exact congrArg (fun B : ReflectedSpace S n →L[ℂ] ReflectedSpace S n => B v) h₂
    · exact congrArg (fun B : ReflectedSpace S n →L[ℂ] ReflectedSpace S n => B v) h₁
  · have hc := h.isContractive_lateral hm s
    exact (h.extBasics hC hc).extension_isometry (h.seminorm_lateral_eq hm s) _
      (h.transOp_isExtension hC hc) v
  · refine tendsto_apply_of_dense (h.dense_range_reflectedClass hC) (lateralGroup S n m')
      (fun t => h.norm_transOp_le hC (h.isContractive_lateral hm t)) ?_ v
    rintro _ ⟨f, rfl⟩
    have h1 : Tendsto (fun s : ℝ => euclidNorm (s • m')) (𝓝[≠] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have e : (fun s : ℝ => euclidNorm (s • m')) = fun s => |s| := by
          funext s
          exact euclidNorm_smul_unit hm.1 s
        rw [e]
        have : Tendsto (fun s : ℝ => |s|) (𝓝 0) (𝓝 |(0 : ℝ)|) := continuous_abs.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [mem_Ioi, euclidNorm_smul_unit hm.1]
        exact abs_pos.mpr hs
    have hc := h.tendsto_reflectedForm_shift f (fun s : ℝ => s • m')
      (fun s => dot_smul_orthogonal_nonneg hm s) h1
    have hq : Tendsto (fun s : ℝ =>
        reflectedForm S n (h.shiftMap (s • m') (dot_smul_orthogonal_nonneg hm s) f)
        (h.shiftMap (s • m') (dot_smul_orthogonal_nonneg hm s) f)) (𝓝[≠] 0)
        (𝓝 (reflectedForm S n f f)) := by
      refine tendsto_const_nhds.congr fun s => ?_
      exact (h.shiftMap_isometry (dot_smul_orthogonal hm s) _ f f).symm
    refine (h.tendsto_reflectedClass_shift hC f _ _ hq hc).congr fun s => ?_
    exact (h.transOp_class hC (h.isContractive_lateral hm s) f).symm
theorem Setup.commutingSemigroupGroup (h : Setup St S C₂ n)
    (hC : FormCompletionAndBoundedExtension) (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
    (hm : IsUnitNormalTo n m') :
    IsCommutingSemigroupGroup (transferSemigroup S n) (lateralGroup S n m') where
  semigroup := h.isSelfAdjointContractionSemigroup hC hI
  group := h.stronglyContinuousUnitary hC hm
  commute t s := by
    change transferSemigroup S n t * lateralGroup S n m' s =
      lateralGroup S n m' s * transferSemigroup S n t
    rw [transferSemigroup_apply, lateralGroup_apply,
      h.transOp_mul hC (h.isContractive_normal hI t) (h.isContractive_lateral hm s),
      h.transOp_mul hC (h.isContractive_lateral hm s) (h.isContractive_normal hI t), add_comm]
end Group
theorem isBoundedMeasurable_spectralCharacter (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (spectralCharacter t s) := by apply _root_.YangMills.Construction.SpectralCalculus.JointSpectralProof.isBoundedMeasurable_spectralCharacter <;> assumption
theorem isCompositionEq_fullDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) :
    IsCompositionEq (fullDomainOperator A) (fullDomainOperator B) (A * B) :=
  fun _ => ⟨Submodule.mem_top, Submodule.mem_top, rfl⟩
theorem nonnegEnergyStrip_eq (B : MeasurableSubtype ℝ) : nonnegEnergyStrip B = fstCylinderSet B :=
  Subtype.ext (by
    ext p
    simp [nonnegEnergyStrip, fstCylinderSet])
section Spectral
variable (hC : FormCompletionAndBoundedExtension)
  (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
  (hJ : JointSpectralTheorem) (hS : SpectralIntegralTheorem)
  (hO : SpectralResolutionUniqueness)
include hC hI hJ
theorem Setup.isJointSpectralPVM (h : Setup St S C₂ n) {m' : AmbientSpace}
    (hm : IsUnitNormalTo n m') :
    IsJointSpectralPVM (transferSemigroup S n) (lateralGroup S n m')
      (jointSpectralMeasure S n m') := by
  obtain ⟨P, hP, -⟩ := (hJ _ _ _ (h.commutingSemigroupGroup hC hI hm)).existsUnique_pvm
  have := nonempty_projValuedMeasure (ReflectedSpace S n)
  exact Classical.epsilon_spec (p := IsJointSpectralMeasure S n m') ⟨P, hP⟩
include hS hO
theorem Setup.hasLateralGroup (h : Setup St S C₂ n) {m' : AmbientSpace}
    (hm : IsUnitNormalTo n m') : HasLateralGroup S n m' := by
  have hp := h.commutingSemigroupGroup hC hI hm
  have hP := h.isJointSpectralPVM hC hI hJ hm
  have hG := (hS _).2 _ _ _ hp hP
  have hF := (hS (ReflectedSpace S n)).1 (jointSpectralMeasure S n m')
  obtain ⟨-, -, hmeas, -, hcomm, hfin⟩ :=
    (hO (ReflectedSpace S n)).2.2 (jointSpectralMeasure S n m')
  obtain ⟨hT, hU, -⟩ := hfin _ _ hp hP
  have hT' : ∀ t : ℝ≥0, expNegMul t (reflectedHamiltonian S n m') =
      fullDomainOperator (transferSemigroup S n t) := fun t => (hT t).symm
  have hU' : ∀ s : ℝ, expIMul s (reflectedMomentum S n m') =
      fullDomainOperator (lateralGroup S n m' s) := fun s => (hU s).symm
  exact
    { translation_extends := fun s =>
        h.translationExtendsUniquely hC (h.isContractive_lateral hm s)
      commuting := hp
      existsUnique_jointMeasure := (hJ _ _ _ hp).existsUnique_pvm
      hamiltonian_nonneg := hG.isPositive_energy
      momentum_selfAdjoint := hG.isSelfAdjoint_momentum
      hamiltonian_generates := ⟨hG.mem_domain_energy_iff, hG.tendsto_energy⟩
      momentum_generates := ⟨hG.mem_domain_momentum_iff, hG.tendsto_momentum⟩
      transferSemigroup_eq := hT'
      lateralGroup_eq := hU'
      product_eq_integral := fun t s => by
        rw [hT', hU', ← hF.eq_boundedSpectralIntegral _ _
          (isBoundedMeasurable_spectralCharacter t s) (hP t s)]
        exact isCompositionEq_fullDomain _ _
      stronglyCommute := hcomm
      spectralProjection_hamiltonian := fun B => by
        rw [nonnegEnergyStrip_eq]
        exact (hmeas B).1
      spectralProjection_momentum := fun B => (hmeas B).2 }
theorem Setup.hamiltonian_eq (h : Setup St S C₂ n) {m' m'' : AmbientSpace}
    (hm' : IsUnitNormalTo n m') (hm'' : IsUnitNormalTo n m'') :
    reflectedHamiltonian S n m' = reflectedHamiltonian S n m'' := by
  have l₁ := (h.hasLateralGroup hC hI hJ hS hO hm').hamiltonian_generates
  have l₂ := (h.hasLateralGroup hC hI hJ hS hO hm'').hamiltonian_generates
  refine LinearPMap.ext ?_ fun x hx hx' => ?_
  · ext v
    rw [l₁.1 v, l₂.1 v]
  · exact tendsto_nhds_unique (l₁.2 ⟨x, hx⟩) (l₂.2 ⟨x, hx'⟩)
end Spectral
end Generators
section Laplace
open MeasureTheory
def expKernel (w : ℂ) (p : SpectralPlane) : ℂ := Complex.exp (-(w * ((p.1 : ℝ) : ℂ)))
theorem norm_expKernel (w : ℂ) (p : SpectralPlane) :
    ‖expKernel w p‖ = Real.exp (-(w.re * (p.1 : ℝ))) := by
  rw [expKernel, Complex.norm_exp]
  simp
theorem norm_expKernel_le_one {w : ℂ} (hw : 0 ≤ w.re) (p : SpectralPlane) :
    ‖expKernel w p‖ ≤ 1 := by
  rw [norm_expKernel]
  exact Real.exp_le_one_iff.mpr (by
    have : 0 ≤ w.re * (p.1 : ℝ) := mul_nonneg hw p.1.2
    linarith)
theorem measurable_expKernel (w : ℂ) : Measurable (expKernel w) := by
  unfold expKernel
  have h : Measurable fun p : SpectralPlane => ((p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp measurable_fst)
  exact Complex.measurable_exp.comp ((h.const_mul w).neg)
def laplaceTrans (m : ComplexMeasure SpectralPlane) (w : ℂ) : ℂ :=
  complexIntegral m (expKernel w)
theorem integrable_of_norm_le (m : ComplexMeasure SpectralPlane) {F : SpectralPlane → ℂ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ p, ‖F p‖ ≤ C) : m.Integrable F :=
  Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hC)
theorem norm_mulPairing_le : ‖mulPairing‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  simp
theorem norm_complexIntegral_le (m : ComplexMeasure SpectralPlane) {F : SpectralPlane → ℂ}
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p, ‖F p‖ ≤ C) :
    ‖complexIntegral m F‖ ≤ C * m.variation.real univ := by
  have h := VectorMeasure.norm_integral_le_of_norm_le_const (μ := m) (B := mulPairing) (f := F)
    (C := C) (Eventually.of_forall hC)
  refine h.trans ?_
  have := norm_mulPairing_le
  calc C * ‖mulPairing‖ * m.variation.real univ
      ≤ C * 1 * m.variation.real univ := by gcongr
    _ = C * m.variation.real univ := by ring
theorem complexIntegral_const_mul (m : ComplexMeasure SpectralPlane) {F : SpectralPlane → ℂ}
    (hF : m.Integrable F) (c : ℂ) :
    complexIntegral m (fun p => c * F p) = c * complexIntegral m F := by
  let C : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ c
  have h1 : C (m.integral F mulPairing) = m.integral F
      ((ContinuousLinearMap.compL ℝ ℂ ℂ ℂ C) ∘L mulPairing) :=
    VectorMeasure.continuousLinearMap_apply_integral hF
  have h2 : m.integral (fun y => C (F y)) mulPairing = m.integral F (mulPairing ∘L C) :=
    VectorMeasure.integral_continuousLinearMap_comp hF
  have h3 : (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ C) ∘L mulPairing = mulPairing ∘L C := by
    ext x y
    simp [C, mul_assoc]
  change m.integral (fun y => C (F y)) mulPairing = C (m.integral F mulPairing)
  rw [h1, h2, h3]
theorem complexIntegral_sub (m : ComplexMeasure SpectralPlane) {F G : SpectralPlane → ℂ}
    (hF : m.Integrable F) (hG : m.Integrable G) :
    complexIntegral m (fun p => F p - G p) = complexIntegral m F - complexIntegral m G :=
  VectorMeasure.integral_fun_sub hF hG
theorem norm_laplaceTrans_le (m : ComplexMeasure SpectralPlane) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖laplaceTrans m w‖ ≤ m.variation.real univ := by
  simpa [laplaceTrans] using norm_complexIntegral_le m zero_le_one (norm_expKernel_le_one hw)
theorem continuousOn_laplaceTrans (m : ComplexMeasure SpectralPlane) :
    ContinuousOn (laplaceTrans m) {w | 0 ≤ w.re} := by
  refine VectorMeasure.continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
    (fun w _ => (measurable_expKernel w).aestronglyMeasurable)
    (fun w hw => Eventually.of_forall (norm_expKernel_le_one hw))
    (integrable_const _) (Eventually.of_forall fun p => ?_)
  unfold expKernel
  fun_prop
theorem self_mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos x)]
  exact h
theorem hasDerivAt_expKernel (w : ℂ) (p : SpectralPlane) :
    HasDerivAt (fun z => expKernel z p) (-((p.1 : ℝ) : ℂ) * expKernel w p) w := by
  unfold expKernel
  have h : HasDerivAt (fun z : ℂ => -(z * ((p.1 : ℝ) : ℂ))) (-((p.1 : ℝ) : ℂ)) w := by
    simpa using ((hasDerivAt_id' w).mul_const ((p.1 : ℝ) : ℂ)).fun_neg
  have := h.cexp
  simpa [mul_comm] using this
theorem norm_deriv_expKernel_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : a ≤ z.re)
    (p : SpectralPlane) : ‖-((p.1 : ℝ) : ℂ) * expKernel z p‖ ≤ a⁻¹ := by
  have hE : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2
  rw [norm_mul, norm_neg, norm_expKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
  have h1 : Real.exp (-(z.re * (p.1 : ℝ))) ≤ Real.exp (-(a * (p.1 : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := self_mul_exp_neg_le_one (a * (p.1 : ℝ))
  have h3 : (p.1 : ℝ) * Real.exp (-(z.re * (p.1 : ℝ))) ≤
      (p.1 : ℝ) * Real.exp (-(a * (p.1 : ℝ))) :=
    mul_le_mul_of_nonneg_left h1 hE
  refine h3.trans ?_
  rw [← one_div, le_div_iff₀ ha]
  linarith
theorem hasDerivAt_laplaceTrans (m : ComplexMeasure SpectralPlane) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (laplaceTrans m)
      (complexIntegral m fun p => -((p.1 : ℝ) : ℂ) * expKernel w p) w := by
  set a : ℝ := w.re / 2 with ha_def
  have ha : 0 < a := by positivity
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hball : ∀ᶠ t : ℂ in 𝓝[≠] 0, ‖t‖ < a := by
    have : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ < a := by
      have h := (continuous_norm (E := ℂ)).tendsto 0
      simp only [norm_zero] at h
      exact h.eventually (gt_mem_nhds ha)
    exact this.filter_mono nhdsWithin_le_nhds
  have hK : ∀ (z : ℂ), 0 ≤ z.re → m.Integrable (expKernel z) := fun z hz =>
    integrable_of_norm_le m (measurable_expKernel z) (norm_expKernel_le_one hz)
  have hre : ∀ t : ℂ, ‖t‖ < a → a ≤ (w + t).re := fun t ht => by
    have h1 : |t.re| ≤ ‖t‖ := Complex.abs_re_le_norm t
    have h2 := (abs_le.mp h1).1
    simp only [Complex.add_re]
    linarith
  have hlip : ∀ t : ℂ, ‖t‖ < a → ∀ p,
      ‖expKernel (w + t) p - expKernel w p‖ ≤ a⁻¹ * ‖t‖ := by
    intro t ht p
    have hconv : Convex ℝ {z : ℂ | a ≤ z.re} := convex_halfSpace_re_ge a
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => expKernel z p)
      (f' := fun z => -((p.1 : ℝ) : ℂ) * expKernel z p) (C := a⁻¹)
      (x := w) (y := w + t)
      (fun z _ => (hasDerivAt_expKernel z p).hasDerivWithinAt)
      (fun z hz => norm_deriv_expKernel_le ha hz p)
      (by
        change a ≤ w.re
        rw [ha_def]
        linarith)
      (hre t ht)
    simpa using this
  have hlim : Tendsto (fun t : ℂ => m.integral
      (fun p => t⁻¹ * (expKernel (w + t) p - expKernel w p)) mulPairing) (𝓝[≠] 0)
      (𝓝 (m.integral (fun p => -((p.1 : ℝ) : ℂ) * expKernel w p) mulPairing)) :=
    VectorMeasure.tendsto_integral_filter_of_dominated_convergence (fun _ => a⁻¹)
    (Eventually.of_forall fun t =>
      (((measurable_expKernel (w + t)).sub (measurable_expKernel w)).const_mul
        t⁻¹).aestronglyMeasurable)
    (by
      filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
      refine Eventually.of_forall fun p => ?_
      have ht0' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht0
      rw [norm_mul, norm_inv]
      calc ‖t‖⁻¹ * ‖expKernel (w + t) p - expKernel w p‖
          ≤ ‖t‖⁻¹ * (a⁻¹ * ‖t‖) := by
            gcongr
            exact hlip t ht p
        _ = a⁻¹ := by field_simp)
    (integrable_const _)
    (Eventually.of_forall fun p => by
      have h := (hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_expKernel w p))
      simpa using h)
  refine hlim.congr' ?_
  filter_upwards [hball] with t ht
  have hz : 0 ≤ (w + t).re := ha.le.trans (hre t ht)
  have h1 := complexIntegral_const_mul m ((hK (w + t) hz).sub (hK w hw.le)) t⁻¹
  have h2 := complexIntegral_sub m (hK (w + t) hz) (hK w hw.le)
  simp only [laplaceTrans, smul_eq_mul]
  rw [← h2]
  exact h1
theorem isOpen_re_gt (a : ℝ) : IsOpen {z : ℂ | a < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re
theorem eqOn_halfPlane_of_eq_real {a : ℝ} {G₁ G₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ G₁ {z | a < z.re}) (h₂ : DifferentiableOn ℂ G₂ {z | a < z.re})
    (h : ∀ x : ℝ, a < x → G₁ (x : ℂ) = G₂ (x : ℂ)) : EqOn G₁ G₂ {z | a < z.re} := by
  have ho := isOpen_re_gt a
  have hc : IsPreconnected {z : ℂ | a < z.re} := (convex_halfSpace_re_gt a).isPreconnected
  have z₀mem : (((a + 1 : ℝ)) : ℂ) ∈ {z : ℂ | a < z.re} := by simp
  refine (h₁.analyticOnNhd ho).eqOn_of_preconnected_of_frequently_eq (h₂.analyticOnNhd ho) hc
    z₀mem ?_
  have hseq : Tendsto (fun k : ℕ => (((a + 1 + 1 / ((k : ℝ) + 1) : ℝ)) : ℂ)) atTop
      (𝓝[≠] (((a + 1 : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h1 : Tendsto (fun k : ℕ => a + 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (a + 1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    · have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      intro he
      linarith
  refine hseq.frequently (Frequently.of_forall fun k => ?_)
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  exact h _ (by linarith)
abbrev lineEquiv : ℂ ≃ Coordinates.ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
theorem lineEquiv_conj_apply (f : ℂ → ℂ) (z : Coordinates.ComplexCoordinates 1) (i : Fin 1) :
    (lineEquiv ∘ f ∘ lineEquiv.symm) z i = f (z 0) := by
  simp [lineEquiv]
theorem differentiableOn_of_holomorphicVia {O : Set ℂ} {f : ℂ → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicVia lineEquiv lineEquiv O f) :
    DifferentiableOn ℂ f O := by apply _root_.YangMills.Construction.CompositeDerivative.differentiableOn_of_isHolomorphicVia <;> assumption
theorem holomorphicVia_of_differentiableOn {O : Set ℂ} {f : ℂ → ℂ} (hO : IsOpen O)
    (hf : DifferentiableOn ℂ f O) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia lineEquiv lineEquiv O f := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.isHolomorphicVia_of_differentiableOn <;> assumption
end Laplace
section Slides
open MeasureTheory
theorem exists_continuation_of_laplace {δ : ℝ} (hδ : 0 < δ) (Φ : ℝ → ℂ) (B : ℝ → ℝ)
    (H : ∀ η : ℝ, 0 < η → η ≤ δ / 2 → ∃ μ : ComplexMeasure SpectralPlane,
      μ.variation.real univ ≤ B η ∧ ∀ x : ℝ, -δ + 2 * η ≤ x →
        laplaceTrans μ ((x + δ - 2 * η : ℝ) : ℂ) = Φ x) :
    (∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z | -δ < z.re} ∧ ∀ x : ℝ, -δ < x → G (x : ℂ) = Φ x) ∧
    ∀ G : ℂ → ℂ, DifferentiableOn ℂ G {z | -δ < z.re} → (∀ x : ℝ, -δ < x → G (x : ℂ) = Φ x) →
      ∀ η : ℝ, 0 < η → η ≤ δ / 2 → ∀ z : ℂ, -δ + 2 * η ≤ z.re → ‖G z‖ ≤ B η := by
  classical
  have H' : ∀ η : ℝ, ∃ μ : ComplexMeasure SpectralPlane, 0 < η → η ≤ δ / 2 →
      μ.variation.real univ ≤ B η ∧ ∀ x : ℝ, -δ + 2 * η ≤ x →
        laplaceTrans μ ((x + δ - 2 * η : ℝ) : ℂ) = Φ x := fun η => by
    by_cases hη : 0 < η ∧ η ≤ δ / 2
    · obtain ⟨μ, hμ⟩ := H η hη.1 hη.2
      exact ⟨μ, fun _ _ => hμ⟩
    · exact ⟨0, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hη⟩
  choose μ hμ using H'
  let F : ℝ → ℂ → ℂ := fun η z => laplaceTrans (μ η) (z + ((δ - 2 * η : ℝ) : ℂ))
  have hre : ∀ (η : ℝ) (z : ℂ), (z + ((δ - 2 * η : ℝ) : ℂ)).re = z.re + δ - 2 * η :=
    fun η z => by
      simp only [Complex.add_re, Complex.ofReal_re]
      ring
  have hFd : ∀ η, DifferentiableOn ℂ (F η) {z | -δ + 2 * η < z.re} := fun η z hz => by
    have hz' : 0 < (z + ((δ - 2 * η : ℝ) : ℂ)).re := by
      rw [hre]
      have : -δ + 2 * η < z.re := hz
      linarith
    exact ((hasDerivAt_laplaceTrans (μ η) hz').comp_add_const z _).differentiableAt.differentiableWithinAt
  have hFc : ∀ η, ContinuousOn (F η) {z | -δ + 2 * η ≤ z.re} := fun η => by
    refine (continuousOn_laplaceTrans (μ η)).comp (by fun_prop) fun z hz => ?_
    change 0 ≤ (z + ((δ - 2 * η : ℝ) : ℂ)).re
    rw [hre]
    have : -δ + 2 * η ≤ z.re := hz
    linarith
  have hFr : ∀ η, 0 < η → η ≤ δ / 2 → ∀ x : ℝ, -δ + 2 * η ≤ x → F η (x : ℂ) = Φ x :=
    fun η h₁ h₂ x hx => by
      have := (hμ η h₁ h₂).2 x hx
      rw [← this]
      change laplaceTrans (μ η) _ = _
      congr 1
      push_cast
      ring
  have hFb : ∀ η, 0 < η → η ≤ δ / 2 → ∀ z : ℂ, -δ + 2 * η ≤ z.re → ‖F η z‖ ≤ B η :=
    fun η h₁ h₂ z hz => by
      refine (norm_laplaceTrans_le (μ η) ?_).trans (hμ η h₁ h₂).1
      rw [hre]
      linarith
  have hmono : ∀ {a b : ℝ}, a ≤ b → {z : ℂ | b < z.re} ⊆ {z : ℂ | a < z.re} :=
    fun hab z hz => lt_of_le_of_lt hab hz
  have hagree : ∀ η η', 0 < η' → η' ≤ η → η ≤ δ / 2 →
      EqOn (F η') (F η) {z | -δ + 2 * η < z.re} :=
    fun η η' h₁ h₂ h₃ => eqOn_halfPlane_of_eq_real
      ((hFd η').mono (hmono (by linarith))) (hFd η) fun x hx => by
        rw [hFr η' h₁ (h₂.trans h₃) x (by linarith), hFr η (h₁.trans_le h₂) h₃ x hx.le]
  have hagree' : ∀ η η' (z : ℂ), 0 < η → η ≤ δ / 2 → 0 < η' → η' ≤ δ / 2 →
      -δ + 2 * η < z.re → -δ + 2 * η' < z.re → F η z = F η' z :=
    fun η η' z a₁ a₂ b₁ b₂ c₁ c₂ => by
      rcases le_total η η' with hle | hle
      · exact hagree η' η a₁ hle b₂ c₂
      · exact (hagree η η' b₁ hle a₂ c₁).symm
  refine ⟨?_, ?_⟩
  · let e : ℂ → ℝ := fun z => min (δ / 2) ((z.re + δ) / 4)
    have he₀ : ∀ z : ℂ, -δ < z.re → 0 < e z := fun z hz =>
      lt_min (by positivity) (by linarith)
    have he₁ : ∀ z, e z ≤ δ / 2 := fun z => min_le_left _ _
    have he₂ : ∀ z : ℂ, -δ < z.re → -δ + 2 * e z < z.re := fun z hz => by
      have : e z ≤ (z.re + δ) / 4 := min_le_right _ _
      linarith
    refine ⟨fun z => F (e z) z, fun z₀ hz₀ => ?_, fun x hx => ?_⟩
    · have hz₀' : -δ < z₀.re := hz₀
      have hopen : IsOpen {z : ℂ | -δ + 2 * e z₀ < z.re} := isOpen_re_gt _
      have hmem : z₀ ∈ {z : ℂ | -δ + 2 * e z₀ < z.re} := he₂ z₀ hz₀
      have hd : DifferentiableAt ℂ (F (e z₀)) z₀ :=
        (hFd (e z₀) z₀ hmem).differentiableAt (hopen.mem_nhds hmem)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hopen.mem_nhds hmem] with z hz
      have hz' : -δ + 2 * e z₀ < z.re := hz
      have hz'' : -δ < z.re := by linarith [he₀ z₀ hz₀']
      exact hagree' _ _ z (he₀ z hz'') (he₁ z) (he₀ z₀ hz₀') (he₁ z₀) (he₂ z hz'') hz'
    · have hx' : -δ < ((x : ℂ)).re := by simpa using hx
      have := he₂ (x : ℂ) hx'
      exact hFr _ (he₀ _ hx') (he₁ _) x (by simpa using this.le)
  · intro G hG hGr η h₁ h₂ z hz
    have ha : -δ ≤ -δ + 2 * η := by linarith
    have hopen : EqOn G (F η) {z | -δ + 2 * η < z.re} := eqOn_halfPlane_of_eq_real
      (hG.mono (hmono ha)) (hFd η) fun x hx => by
        rw [hGr x (by linarith), hFr η h₁ h₂ x hx.le]
    have hclosed : EqOn G (F η) {z | -δ + 2 * η ≤ z.re} := by
      refine hopen.of_subset_closure ?_ (hFc η)
        (fun w hw => le_of_lt (show -δ + 2 * η < w.re from hw)) ?_
      · exact hG.continuousOn.mono fun w hw => by
          have : -δ + 2 * η ≤ w.re := hw
          change -δ < w.re
          linarith
      · rw [Complex.closure_setOfPred_lt_re]
    rw [hclosed hz]
    exact hFb η h₁ h₂ z hz
variable {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {C₂ : ℝ → ℝ → ℝ}
  {n : AmbientSpace}
def leftProfile (n : AmbientSpace) (a : ℝ) (f : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  reflectFun n (translateFun (a • n) (conjFun f))
def rightProfile (n : AmbientSpace) (b : ℝ) (f : AmbientSpace → ℂ) : AmbientSpace → ℂ :=
  translateFun (b • n) f
theorem Setup.reflConj_leftProfile (h : Setup St S C₂ n) (a : ℝ) (f : AmbientSpace → ℂ) :
    reflConj n (leftProfile n a f) = translateFun (a • n) f := by
  funext x
  simp [leftProfile, reflectFun, conjFun, translateFun, h.reflect_reflect]
theorem Setup.leftProfile_mem (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (a : ℝ) : leftProfile n a f ∈ compactC1Complex :=
  (h.reflect_preserves (h.translate_preserves (h.conj_preserves hf).mem _).mem).mem
theorem Setup.sharpNorm_leftProfile (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (a : ℝ) : St.sharpNorm (leftProfile n a f) = St.sharpNorm f := by
  have h₁ := h.conj_preserves hf
  have h₂ := h.translate_preserves h₁.mem (a • n)
  exact ((h.reflect_preserves h₂.mem).sharpNorm_eq.trans h₂.sharpNorm_eq).trans h₁.sharpNorm_eq
theorem Setup.ball_leftProfile (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (a : ℝ) {R : ℝ} (hR : 0 < R)
    (hb : ∃ x, tsupport f ⊆ euclidClosedBall x R) :
    ∃ x, tsupport (leftProfile n a f) ⊆ euclidClosedBall x R := by
  obtain ⟨x, hx⟩ := hb
  have h₁ := h.conj_preserves hf
  have h₂ := h.translate_preserves h₁.mem (a • n)
  obtain ⟨x₁, hx₁⟩ := h₁.ballSupport x R hR hx
  obtain ⟨x₂, hx₂⟩ := h₂.ballSupport x₁ R hR hx₁
  exact (h.reflect_preserves h₂.mem).ballSupport x₂ R hR hx₂
theorem Setup.dot_leftProfile (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) {c η : ℝ} (hs : tsupport f ⊆ {x | euclidDot n x ≤ c}) :
    ∀ x ∈ tsupport (leftProfile n (-(c + η)) f), η ≤ euclidDot n x := by
  intro x hx
  have h₁ := h.conj_preserves hf
  have h₂ := h.translate_preserves h₁.mem ((-(c + η)) • n)
  rw [leftProfile, h.tsupport_reflectFun h₂.mem] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := h.tsupport_translateFun h₁.mem _ hy
  rw [h.tsupport_conjFun hf] at hy'
  have : euclidDot n y' ≤ c := hs hy'
  rw [h.dot_reflect, dot_add_right, h.dot_smul_self]
  linarith
theorem Setup.dot_rightProfile (h : Setup St S C₂ n) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) {c' b : ℝ} (hs : tsupport f ⊆ {x | c' ≤ euclidDot n x}) :
    ∀ x ∈ tsupport (rightProfile n b f), c' + b ≤ euclidDot n x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h.tsupport_translateFun hf _ hx
  have : c' ≤ euclidDot n y := hs hy
  rw [dot_add_right, h.dot_smul_self]
  linarith
theorem mem_halfSpaceDomain_of_height {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex)
    {η : ℝ} (hη : 0 < η) (hs : ∀ x ∈ tsupport f, η ≤ euclidDot n x) : f ∈ halfSpaceDomain n :=
  (mem_halfSpaceDomain_iff _).mpr ⟨hf.1, hf.2.1, fun x hx => lt_of_lt_of_le hη (hs x hx)⟩
theorem Setup.complexifyForm_profiles (h : Setup St S C₂ n) {c δ η : ℝ}
    {f₁ f₂ : AmbientSpace → ℂ} (hp : IsSeparatedPair n c δ f₁ f₂) {x : ℝ} (hx : -δ < x) :
    complexifyForm S (reflConj n (leftProfile n (-(c + η)) f₁))
        (translateFun ((x + δ - 2 * η) • n) (rightProfile n (-(c + δ - η)) f₂)) =
      slideFn S n f₁ f₂ x := by
  have hk := h.translate_preserves hp.right_mem (x • n)
  have hpair : IsDisjointSupportPair f₁ (translateFun (x • n) f₂) := by
    refine ⟨hp.left_mem, hk.mem, Set.disjoint_left.mpr fun y hy hy' => ?_⟩
    obtain ⟨y', hy'', rfl⟩ := h.tsupport_translateFun hp.right_mem _ hy'
    have h₁ : euclidDot n (y' + x • n) ≤ c := hp.left_tsupport hy
    have h₂ : c + δ ≤ euclidDot n y' := hp.right_tsupport hy''
    rw [dot_add_right, h.dot_smul_self] at h₁
    linarith
  rw [h.reflConj_leftProfile, rightProfile, translateFun_translateFun]
  have e : (x + δ - 2 * η) • n + (-(c + δ - η)) • n = (-(c + η)) • n + x • n := by module
  rw [e, ← translateFun_translateFun]
  exact h.complexifyForm_translateFun _ hpair
section LaplaceMeasures
variable (hC : FormCompletionAndBoundedExtension)
  (hI : HilbertSpace.IteratedCauchySchwarz.Claim) (hJ : JointSpectralTheorem)
include hC hI hJ
theorem Setup.exists_laplace_measure (h : Setup St S C₂ n) {m' : AmbientSpace}
    (hm : IsUnitNormalTo n m') {c δ R : ℝ} {f₁ f₂ : AmbientSpace → ℂ} (hR : 0 < R)
    (b₁ : ∃ x, tsupport f₁ ⊆ euclidClosedBall x R) (b₂ : ∃ x, tsupport f₂ ⊆ euclidClosedBall x R)
    (hp : IsSeparatedPair n c δ f₁ f₂) (η : ℝ) (h₀ : 0 < η) (_ : η ≤ δ / 2) :
    ∃ μ : ComplexMeasure SpectralPlane,
      μ.variation.real univ ≤ 4 * C₂ (2 * η) R * St.sharpNorm f₁ * St.sharpNorm f₂ ∧
      ∀ x : ℝ, -δ + 2 * η ≤ x →
        laplaceTrans μ ((x + δ - 2 * η : ℝ) : ℂ) = slideFn S n f₁ f₂ x := by
  have s₁ := h.dot_leftProfile hp.left_mem (η := η) hp.left_tsupport
  have s₂ : ∀ x ∈ tsupport (rightProfile n (-(c + δ - η)) f₂), η ≤ euclidDot n x :=
    fun x hx => by
      have := h.dot_rightProfile hp.right_mem hp.right_tsupport x hx
      linarith
  have c₁ := h.leftProfile_mem hp.left_mem (-(c + η))
  have c₂ : rightProfile n (-(c + δ - η)) f₂ ∈ compactC1Complex :=
    (h.translate_preserves hp.right_mem _).mem
  let g₁ : halfSpaceDomain n := ⟨_, mem_halfSpaceDomain_of_height c₁ h₀ s₁⟩
  let g₂ : halfSpaceDomain n := ⟨_, mem_halfSpaceDomain_of_height c₂ h₀ s₂⟩
  have bg₁ := h.ball_leftProfile hp.left_mem (-(c + η)) hR b₁
  have bg₂ : ∃ x, tsupport (rightProfile n (-(c + δ - η)) f₂) ⊆ euclidClosedBall x R := by
    obtain ⟨x, hx⟩ := b₂
    exact (h.translate_preserves hp.right_mem _).ballSupport x R hR hx
  have hsharp₂ : St.sharpNorm (rightProfile n (-(c + δ - η)) f₂) = St.sharpNorm f₂ :=
    (h.translate_preserves hp.right_mem _).sharpNorm_eq
  set Q : ℝ := 4 * C₂ (2 * η) R with hQdef
  have hQ : 0 ≤ Q := mul_nonneg (by norm_num) (h.decay.1 _ _ (by positivity) hR)
  have hnorm : ∀ (g : halfSpaceDomain n) (f : AmbientSpace → ℂ),
      (∀ x ∈ tsupport (g : AmbientSpace → ℂ), η ≤ euclidDot n x) →
      (∃ x, tsupport (g : AmbientSpace → ℂ) ⊆ euclidClosedBall x R) →
      St.sharpNorm g = St.sharpNorm f →
      ‖reflectedClass S n g‖ ≤ Real.sqrt Q * St.sharpNorm f := fun g f sg bg e => by
    have hb := h.norm_complexifyForm_le g.2 g.2 h₀ hR sg sg bg bg
    rw [e] at hb
    rw [h.norm_reflectedClass hC, formSeminorm, ← Real.sqrt_sq (zero_le_sharpNorm St f),
      ← Real.sqrt_mul hQ]
    refine Real.sqrt_le_sqrt ?_
    refine (Complex.re_le_norm _).trans ?_
    calc ‖reflectedForm S n g g‖ ≤ Q * St.sharpNorm f * St.sharpNorm f := hb
      _ = Q * St.sharpNorm f ^ 2 := by ring
  have hp' := h.commutingSemigroupGroup hC hI hm
  have hfacts := hJ _ _ _ hp'
  refine ⟨pairSpectralMeasure (transferSemigroup S n) (lateralGroup S n m')
    (reflectedClass S n g₁) (reflectedClass S n g₂), ?_, fun x hx => ?_⟩
  · refine (hfacts.variation_le _ _).trans ?_
    have n₁ := hnorm g₁ f₁ s₁ bg₁ (h.sharpNorm_leftProfile hp.left_mem _)
    have n₂ := hnorm g₂ f₂ s₂ bg₂ hsharp₂
    calc ‖reflectedClass S n g₁‖ * ‖reflectedClass S n g₂‖
        ≤ (Real.sqrt Q * St.sharpNorm f₁) * (Real.sqrt Q * St.sharpNorm f₂) :=
          mul_le_mul n₁ n₂ (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (zero_le_sharpNorm St _))
      _ = (Real.sqrt Q * Real.sqrt Q) * St.sharpNorm f₁ * St.sharpNorm f₂ := by ring
      _ = Q * St.sharpNorm f₁ * St.sharpNorm f₂ := by rw [Real.mul_self_sqrt hQ]
  · have ht : 0 ≤ x + δ - 2 * η := by linarith
    let t : ℝ≥0 := ⟨x + δ - 2 * η, ht⟩
    have hT := hfacts.hasSpectralTransform (reflectedClass S n g₁) (reflectedClass S n g₂) t 0
    have hU : lateralGroup S n m' 0 = 1 := (h.stronglyContinuousUnitary hC hm).map_zero
    rw [hU, one_apply_eq_self, transferSemigroup_apply,
      h.transOp_class hC (h.isContractive_normal hI t), h.inner_reflectedClass hC] at hT
    have hslide := h.complexifyForm_profiles (η := η) hp (x := x) (by linarith)
    have hk : spectralCharacter t 0 = expKernel ((x + δ - 2 * η : ℝ) : ℂ) := by
      funext p
      simp only [spectralCharacter, expKernel]
      rw [show ((t : ℝ≥0) : ℝ) = x + δ - 2 * η from rfl]
      congr 1
      push_cast
      ring
    rw [laplaceFourier, hk] at hT
    change laplaceTrans _ _ = _
    rw [laplaceTrans, ← hT, ← hslide]
    rfl
end LaplaceMeasures
theorem dot_coordVec (l : Fin 4) (x : AmbientSpace) : euclidDot (coordVec l) x = x l := by
  simp [euclidDot, PeriodicLattice.coordVec, Pi.single_apply]
theorem exists_unitNormalTo (hE : ReflectionsPlaneFacts.Statement)
    (hn : n ∈ reflectionNormals) : ∃ m', IsUnitNormalTo n m' := by
  have hunit : ∀ l : Fin 4, euclidNorm (coordVec l) = 1 := fun l => by
    simpa [signedAxis] using hE.1.1 l 1 (Or.inl rfl)
  have hpick : ∀ μ ν : Fin 4, ∃ l, l ≠ μ ∧ l ≠ ν := by decide
  rcases hn with ⟨μ, ε, -, rfl⟩ | ⟨μ, ν, ε, ε', -, -, -, rfl⟩
  · obtain ⟨l, h₁, -⟩ := hpick μ μ
    refine ⟨coordVec l, hunit l, ?_⟩
    rw [dot_coordVec]
    simp [PeriodicLattice.coordVec, h₁]
  · obtain ⟨l, h₁, h₂⟩ := hpick μ ν
    refine ⟨coordVec l, hunit l, ?_⟩
    rw [dot_coordVec]
    simp [PeriodicLattice.coordVec, h₁, h₂]
theorem reflectedSpaceAndSlides (hC : FormCompletionAndBoundedExtension)
    (hE : ReflectionsPlaneFacts.Statement)
    (hF : AdmissibleFormConsequences.Statement)
    (hI : HilbertSpace.IteratedCauchySchwarz.Claim)
    (hJ : JointSpectralTheorem) (hS : SpectralIntegralTheorem)
    (hO : SpectralResolutionUniqueness)
    (hT : SharpNormTranslates) :
    ReflectedSpaceAndSlides.Statement := by
  intro St S C₂ n hform hball
  obtain ⟨hMir, hInv, -, hSt, hForm⟩ := hF
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅⟩, a₆⟩ := hForm St S C₂ hform.isDisjointForm hform.admissible hball
  have hunit : euclidNorm n = 1 := by
    rcases hform.mem_normals with ⟨μ, ε, hε, rfl⟩ | ⟨μ, ν, ε, ε', hμν, hε, hε', rfl⟩
    · exact hE.1.1 μ ε hε
    · exact hE.1.2.1 μ ν ε ε' hμν hε hε'
  have h : Setup St S C₂ n :=
    { unit_norm := hunit
      normal := hform.mem_normals
      reflection := hInv n hunit
      reflection_mem := (hMir n hform.mem_normals).1
      preserves := (hSt St).1
      symm := a₁
      linear := a₂
      invariant := a₃
      conj_comm := a₄
      bound := a₅
      reflPositive := a₆
      modulus := (hT St).1
      decay := hball }
  refine ⟨⟨h.hasTransferSemigroup hC hI, fun m' hm => h.hasLateralGroup hC hI hJ hS hO hm,
    fun m' m'' hm' hm'' => h.hamiltonian_eq hC hI hJ hS hO hm' hm''⟩,
    fun R c δ f₁ f₂ hR b₁ b₂ hp => ?_⟩
  obtain ⟨m', hm⟩ := exists_unitNormalTo hE hform.mem_normals
  obtain ⟨⟨G, hGd, hGr⟩, hB⟩ := exists_continuation_of_laplace hp.gap_pos (slideFn S n f₁ f₂)
    (fun η => 4 * C₂ (2 * η) R * St.sharpNorm f₁ * St.sharpNorm f₂)
    (h.exists_laplace_measure hC hI hJ hm hR b₁ b₂ hp)
  have hspec : IsSlideContinuation S n δ f₁ f₂ (slideContinuation S n δ f₁ f₂) :=
    Classical.epsilon_spec (p := IsSlideContinuation S n δ f₁ f₂)
      ⟨G, holomorphicVia_of_differentiableOn (isOpen_re_gt _) hGd, fun s hs => hGr s hs⟩
  exact ⟨hspec, fun η h₀ h₁ s hs =>
    hB _ (differentiableOn_of_holomorphicVia hspec.holomorphic) hspec.eq_slideFn η h₀ h₁ s hs⟩
end Slides
end ReflectedSpaceSlides
end TwoPoints
end YangMills.Construction
end
