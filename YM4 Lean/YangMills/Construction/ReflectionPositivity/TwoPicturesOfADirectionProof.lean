import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.FormHilbert.FormCompletionAndDenseExtension
import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASet
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField LatticePoint axisStep shift halfSpaceLocalObservables
  observableSupNorm IsBoundedObservable IsLocalObservable IsRegionMeasurable UnitLatticeSymmetry
  unitRegionObservables closedHalfSpace hyperplaneReflect)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open HilbertSpace (SesqForm)
open JointSpectrum (CommutingFamily SpectralDomain)
open FormHilbert
open FormHilbert.DenseExtension
namespace ReflectionPairProof
abbrev translateObs (v : LatticePoint (1 : ℝ)) (F : GaugeField (1 : ℝ) → ℂ) :
    GaugeField (1 : ℝ) → ℂ :=
  (shift v).actOn F
theorem translateObs_add (v w : LatticePoint (1 : ℝ)) (F : GaugeField (1 : ℝ) → ℂ) :
    translateObs v (translateObs w F) = translateObs (v + w) F := by
  have h : (shift v).comp (shift w) = shift (v + w) := by
    apply latticeSymmetry_ext
    funext x
    change x + (w : InfiniteLattice.AmbientSpace) + (v : InfiniteLattice.AmbientSpace) =
      x + ((v + w : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace)
    rw [AddSubgroup.coe_add]
    abel
  exact congrArg (fun r : UnitLatticeSymmetry => r.actOn F) h
theorem translateObs_zero (F : GaugeField (1 : ℝ) → ℂ) : translateObs 0 F = F := by
  funext U
  change F ((shift (0 : LatticePoint (1 : ℝ))).pullbackField U) = F U
  congr 1
  apply Subtype.ext
  funext b
  change U.1 ((shift (0 : LatticePoint (1 : ℝ))).linkMap b) = U.1 b
  refine congrArg U.1 ?_
  apply InfiniteLattice.Link.ext
  · apply Subtype.ext
    change (b.initial : InfiniteLattice.AmbientSpace) +
      ((0 : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) = _
    simp
  · apply Subtype.ext
    change (b.terminal : InfiniteLattice.AmbientSpace) +
      ((0 : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) = _
    simp
theorem reflect_apply {P : UnitMirrorPair} {μ : Fin 4} (hn : P.normal = basisVec μ)
    (x : InfiniteLattice.AmbientSpace) :
    P.reflect.toFun x = x - (2 * (x μ - P.height)) • basisVec μ := by
  change hyperplaneReflect P.normal P.height x = _
  have h : basisVec μ ⬝ᵥ basisVec μ = 1 := by
    rw [basisVec_dotProduct]
    simp [basisVec]
  rw [hyperplaneReflect, hn, basisVec_dotProduct, h, div_one]
theorem reflect_comp_shift_normal {P : UnitMirrorPair} {μ : Fin 4}
    (hn : P.normal = basisVec μ) (v : LatticePoint (1 : ℝ))
    (hv : ∀ i, i ≠ μ → (v : InfiniteLattice.AmbientSpace) i = 0) :
    P.reflect.comp (shift v) = (shift (-v)).comp P.reflect := by
  apply latticeSymmetry_ext
  funext x i
  change P.reflect.toFun (x + (v : InfiniteLattice.AmbientSpace)) i =
    P.reflect.toFun x i + ((-v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) i
  rw [reflect_apply hn, reflect_apply hn, AddSubgroup.coe_neg]
  by_cases h : i = μ
  · subst h
    simp [basisVec]
    ring
  · simp [basisVec, Pi.single_eq_of_ne h, hv i h]
theorem reflect_comp_shift_tangent {P : UnitMirrorPair} {μ : Fin 4}
    (hn : P.normal = basisVec μ) (v : LatticePoint (1 : ℝ))
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0) :
    P.reflect.comp (shift v) = (shift v).comp P.reflect := by
  apply latticeSymmetry_ext
  funext x i
  change P.reflect.toFun (x + (v : InfiniteLattice.AmbientSpace)) i =
    P.reflect.toFun x i + (v : InfiniteLattice.AmbientSpace) i
  rw [reflect_apply hn, reflect_apply hn]
  by_cases h : i = μ
  · subst h
    simp [basisVec, hv]
  · simp [basisVec, Pi.single_eq_of_ne h]
def baseMirror (p : ReflectionPair) (μ : Fin 4) : UnitMirrorPair :=
  match p with
  | .link => linkPlane μ
  | .site => sitePlane μ
def raisedMirror (p : ReflectionPair) (μ : Fin 4) : UnitMirrorPair :=
  match p with
  | .link => sitePlane μ
  | .site => ⟨basisVec μ, 1 / 2, Or.inl ⟨⟨μ, rfl⟩, 1, by norm_num⟩⟩
theorem reflect_eq_baseMirror (p : ReflectionPair) (μ : Fin 4) :
    p.reflect μ = (baseMirror p μ).reflect := by
  cases p <;> rfl
theorem baseMirror_normal (p : ReflectionPair) (μ : Fin 4) :
    (baseMirror p μ).normal = basisVec μ := by
  cases p <;> rfl
theorem raisedMirror_normal (p : ReflectionPair) (μ : Fin 4) :
    (raisedMirror p μ).normal = basisVec μ := by
  cases p <;> rfl
theorem baseMirror_height_nonpos (p : ReflectionPair) (μ : Fin 4) :
    (baseMirror p μ).height ≤ 0 := by
  cases p
  · change -(1 / 2 : ℝ) ≤ 0
    norm_num
  · exact le_rfl
theorem raisedMirror_height (p : ReflectionPair) (μ : Fin 4) :
    (raisedMirror p μ).height = (baseMirror p μ).height + 1 / 2 := by
  cases p
  · change (0 : ℝ) = -(1 / 2) + 1 / 2
    norm_num
  · change (1 / 2 : ℝ) = 0 + 1 / 2
    norm_num
theorem raisedMirror_reflect_comp_shift (p : ReflectionPair) (μ : Fin 4) :
    (raisedMirror p μ).reflect.comp (shift (axisStep 1 μ)) = (baseMirror p μ).reflect := by
  apply latticeSymmetry_ext
  funext x i
  change (raisedMirror p μ).reflect.toFun (x + (axisStep 1 μ : LatticePoint (1 : ℝ)).1) i =
    (baseMirror p μ).reflect.toFun x i
  rw [reflect_apply (raisedMirror_normal p μ), reflect_apply (baseMirror_normal p μ),
    raisedMirror_height]
  by_cases h : i = μ
  · subst h
    simp [basisVec, axisStep]
    ring
  · simp [basisVec, axisStep, Pi.single_eq_of_ne h]
theorem axisStep_apply_self (μ : Fin 4) :
    ((axisStep 1 μ : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem axisStep_apply_ne {l μ : Fin 4} (h : l ≠ μ) :
    ((axisStep 1 l : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = 0 := by
  simp [axisStep, Pi.single_eq_of_ne h.symm]
theorem isBoundedObservable_actOn (hA : SymmetryActionAndReflections)
    (r : UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (r.actOn F) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_actOn <;> assumption
theorem supNorm_actOn (hA : SymmetryActionAndReflections)
    (r : UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    observableSupNorm (r.actOn F) = observableSupNorm F := by
  obtain ⟨-, -, -, -, h, -⟩ := hA
  exact (h r F hF).2.1
theorem isLocalObservable_actOn (hA : SymmetryActionAndReflections)
    (r : UnitLatticeSymmetry) {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F)
    (hl : IsLocalObservable F) : IsLocalObservable (r.actOn F) := by
  obtain ⟨-, -, -, -, h, -⟩ := hA
  exact (h r F hF).2.2 hl
theorem isBoundedObservable_conj_mul {G H : GaugeField (1 : ℝ) → ℂ}
    (hG : IsBoundedObservable G) (hH : IsBoundedObservable H) :
    IsBoundedObservable fun U => conj (G U) * H U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_conj_mul <;> assumption
theorem norm_le_supNorm {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField (1 : ℝ)) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨-, C, hC⟩ := hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem supNorm_nonneg (F : GaugeField (1 : ℝ) → ℂ) : 0 ≤ observableSupNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _
section Pairing
variable (ν : unitPositiveClass)
def reflPairing (θ : UnitLatticeSymmetry) (F H : GaugeField (1 : ℝ) → ℂ) : ℂ :=
  ∫ U, conj (θ.actOn F U) * H U ∂(ν : Measure (GaugeField (1 : ℝ)))
instance isProbabilityMeasure_unitPositiveClass :
    IsProbabilityMeasure (ν : Measure (GaugeField (1 : ℝ))) := ν.2.1
variable {ν}
theorem integrable_of_isBoundedObservable {A : GaugeField (1 : ℝ) → ℂ}
    (hA : IsBoundedObservable A) : Integrable A (ν : Measure (GaugeField (1 : ℝ))) := by
  obtain ⟨m, C, hC⟩ := hA
  exact Integrable.of_bound m.aestronglyMeasurable C (Eventually.of_forall hC)
variable (hA : SymmetryActionAndReflections)
  {θ : UnitLatticeSymmetry} {F F₁ F₂ H H₁ H₂ : GaugeField (1 : ℝ) → ℂ}
include hA
theorem integrable_reflPairing_integrand (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    Integrable (fun U => conj (θ.actOn F U) * H U) (ν : Measure (GaugeField (1 : ℝ))) :=
  integrable_of_isBoundedObservable
    (isBoundedObservable_conj_mul (isBoundedObservable_actOn hA θ hF) hH)
theorem reflPairing_add_left (h₁ : IsBoundedObservable F₁) (h₂ : IsBoundedObservable F₂)
    (hH : IsBoundedObservable H) :
    reflPairing ν θ (F₁ + F₂) H = reflPairing ν θ F₁ H + reflPairing ν θ F₂ H := by
  unfold reflPairing
  rw [← integral_add (integrable_reflPairing_integrand hA h₁ hH)
    (integrable_reflPairing_integrand hA h₂ hH)]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change conj (F₁ (θ.pullbackField U) + F₂ (θ.pullbackField U)) * H U = _
  rw [map_add, add_mul]
  rfl
theorem reflPairing_add_right (hF : IsBoundedObservable F) (h₁ : IsBoundedObservable H₁)
    (h₂ : IsBoundedObservable H₂) :
    reflPairing ν θ F (H₁ + H₂) = reflPairing ν θ F H₁ + reflPairing ν θ F H₂ := by
  unfold reflPairing
  rw [← integral_add (integrable_reflPairing_integrand hA hF h₁)
    (integrable_reflPairing_integrand hA hF h₂)]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [Pi.add_apply, mul_add]
omit hA in
theorem reflPairing_smul_left (c : ℂ) :
    reflPairing ν θ (c • F) H = conj c * reflPairing ν θ F H := by
  unfold reflPairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change conj (c * F (θ.pullbackField U)) * H U = _
  rw [map_mul, mul_assoc]
  rfl
omit hA in
theorem reflPairing_smul_right (c : ℂ) :
    reflPairing ν θ F (c • H) = c * reflPairing ν θ F H := by
  unfold reflPairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem reflPairing_eq_shift (r : UnitLatticeSymmetry) (v : LatticePoint (1 : ℝ))
    (hF : IsBoundedObservable F) (hH : IsBoundedObservable H) :
    reflPairing ν r F H = reflPairing ν ((shift v).comp r) F (translateObs v H) :=
  (ν.2.2.1 v _ (isBoundedObservable_conj_mul (isBoundedObservable_actOn hA r hF) hH)).symm
theorem reflPairing_translate_normal {P : UnitMirrorPair} {μ : Fin 4}
    (hn : P.normal = basisVec μ) (v : LatticePoint (1 : ℝ))
    (hv : ∀ i, i ≠ μ → (v : InfiniteLattice.AmbientSpace) i = 0)
    (hF : IsBoundedObservable F) (hH : IsBoundedObservable H) :
    reflPairing ν P.reflect (translateObs v F) H = reflPairing ν P.reflect F (translateObs v H) := by
  have h := reflPairing_eq_shift (ν := ν) hA P.reflect (-v) hF
    (isBoundedObservable_actOn hA (shift v) hH)
  rw [h, ← reflect_comp_shift_normal hn v hv, translateObs_add, neg_add_cancel,
    translateObs_zero]
  rfl
theorem reflPairing_translate_tangent {P : UnitMirrorPair} {μ : Fin 4}
    (hn : P.normal = basisVec μ) (v : LatticePoint (1 : ℝ))
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0)
    (hF : IsBoundedObservable F) (hH : IsBoundedObservable H) :
    reflPairing ν P.reflect (translateObs v F) (translateObs v H) = reflPairing ν P.reflect F H := by
  rw [reflPairing_eq_shift (ν := ν) hA P.reflect v hF hH, ← reflect_comp_shift_tangent hn v hv]
  rfl
theorem norm_reflPairing_le (hF : IsBoundedObservable F) :
    ‖reflPairing ν θ F F‖ ≤ observableSupNorm F ^ 2 := by
  have hb : ∀ U, ‖conj (θ.actOn F U) * F U‖ ≤
      observableSupNorm F * observableSupNorm F := by
    intro U
    rw [norm_mul, RCLike.norm_conj]
    refine mul_le_mul ?_ (norm_le_supNorm hF U) (norm_nonneg _) (supNorm_nonneg F)
    rw [← supNorm_actOn hA θ hF]
    exact norm_le_supNorm (isBoundedObservable_actOn hA θ hF) U
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure (GaugeField (1 : ℝ))))
    (Eventually.of_forall hb)
  simpa [reflPairing, sq] using this
end Pairing
section HalfSpace
variable (hA : SymmetryActionAndReflections)
  (hR : InfiniteLattice.LinkLocalFunctions.Statement)
  {μ : Fin 4} {F : GaugeField (1 : ℝ) → ℂ}
include hA hR
theorem translateObs_mem_upper (hF : F ∈ halfSpaceLocalObservables μ) (v : LatticePoint (1 : ℝ)) :
    translateObs v F ∈ unitRegionObservables {x | (v : InfiniteLattice.AmbientSpace) μ ≤ x μ} := by
  obtain ⟨-, himage, -⟩ := hA
  obtain ⟨-, -, hmono, -⟩ := hR
  have h : translateObs v F ∈ unitRegionObservables ((shift v).setImage (closedHalfSpace μ)) := by
    rw [← himage (shift v) (closedHalfSpace μ)]
    exact ⟨F, hF.1, rfl⟩
  refine hmono _ _ ?_ h
  rintro _ ⟨x, hx, rfl⟩
  change (v : InfiniteLattice.AmbientSpace) μ ≤ x μ + (v : InfiniteLattice.AmbientSpace) μ
  have : 0 ≤ x μ := hx
  linarith
theorem translateObs_mem (hF : F ∈ halfSpaceLocalObservables μ) {v : LatticePoint (1 : ℝ)}
    (hv : 0 ≤ (v : InfiniteLattice.AmbientSpace) μ) :
    translateObs v F ∈ halfSpaceLocalObservables μ := by
  refine ⟨?_, isLocalObservable_actOn hA _ hF.1.1 hF.2⟩
  obtain ⟨-, -, hmono, -⟩ := id hR
  refine hmono _ _ ?_ (translateObs_mem_upper hA hR hF v)
  intro x hx
  have h₁ : (v : InfiniteLattice.AmbientSpace) μ ≤ x μ := hx
  exact hv.trans h₁
omit hA in
theorem reflPairing_self_nonneg {ν : unitPositiveClass} {P : UnitMirrorPair}
    (hn : P.normal = basisVec μ) {t : ℝ} (ht : P.height ≤ t)
    (hF : F ∈ unitRegionObservables {x | t ≤ x μ}) (hl : IsLocalObservable F) :
    0 ≤ reflPairing ν P.reflect F F := by
  obtain ⟨-, -, hmono, -⟩ := hR
  have hside : {x : InfiniteLattice.AmbientSpace | P.height ≤ P.normal ⬝ᵥ x} ∈ P.halfSpaces :=
    Or.inl rfl
  refine (ν.2.2.2 P).2 _ hside F hF.1 hl ?_
  refine (hmono _ _ ?_ hF).2
  intro x hx
  change P.height ≤ P.normal ⬝ᵥ x
  rw [hn, basisVec_dotProduct]
  exact ht.trans hx
end HalfSpace
theorem sq_mul_le_of_mul_le {X Y Z W c : ℝ} (hX : 0 ≤ X) (hc : 0 < c) (ih : X * c ≤ Y * Z)
    (h2 : Z ^ 2 ≤ c * W) : X ^ 2 * c ≤ Y ^ 2 * W := by
  have h3 : (X * c) ^ 2 ≤ (Y * Z) ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
  have h4 : (X ^ 2 * c) * c ≤ (Y ^ 2 * W) * c :=
    calc (X ^ 2 * c) * c = (X * c) ^ 2 := by ring
      _ ≤ (Y * Z) ^ 2 := h3
      _ = Y ^ 2 * Z ^ 2 := by ring
      _ ≤ Y ^ 2 * (c * W) := mul_le_mul_of_nonneg_left h2 (sq_nonneg Y)
      _ = (Y ^ 2 * W) * c := by ring
  exact le_of_mul_le_mul_right h4 hc
theorem le_of_sq_le_mul_doubled {a : ℕ → ℝ} {M : ℝ} (h0 : ∀ k, 0 ≤ a k) (hM : ∀ k, a k ≤ M)
    (hd : ∀ k, a k ^ 2 ≤ a 0 * a (2 * k)) : a 1 ≤ a 0 := by
  by_contra hlt
  rw [not_le] at hlt
  rcases (h0 0).eq_or_lt with h | hpos
  · have h1 := hd 1
    rw [← h, zero_mul] at h1
    have h2 : 0 < a 1 := (h0 0).trans_lt hlt
    nlinarith
  · have key : ∀ j : ℕ, a 1 ^ (2 ^ j) * a 0 ≤ a 0 ^ (2 ^ j) * a (2 ^ j) := by
      intro j
      induction j with
      | zero => simp [mul_comm]
      | succ j ih =>
        have e3 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        have e1 : a 1 ^ 2 ^ (j + 1) = (a 1 ^ 2 ^ j) ^ 2 := by rw [← pow_mul, pow_succ]
        have e2 : a 0 ^ 2 ^ (j + 1) = (a 0 ^ 2 ^ j) ^ 2 := by rw [← pow_mul, pow_succ]
        rw [e1, e2, e3]
        exact sq_mul_le_of_mul_le (pow_nonneg (h0 1) _) hpos ih (hd (2 ^ j))
    have hr : 1 < a 1 / a 0 := (one_lt_div hpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / a 0) hr
    have h1 : (a 1 / a 0) ^ n ≤ (a 1 / a 0) ^ (2 ^ n) :=
      pow_le_pow_right₀ hr.le Nat.lt_two_pow_self.le
    have h2 : (a 1 / a 0) ^ (2 ^ n) ≤ M / a 0 := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hpos _) hpos]
      rw [mul_comm M]
      exact (key n).trans (mul_le_mul_of_nonneg_left (hM _) (pow_nonneg (h0 0) _))
    linarith
section Classes
variable {ν : unitPositiveClass} {μ : Fin 4} {p : ReflectionPair}
theorem pairForm_eq_reflPairing (F H : halfSpaceLocalObservables μ) :
    p.pairForm ν μ F H = reflPairing ν (p.reflect μ) F H :=
  p.pairForm_apply ν μ F H
theorem isPosSesqForm_pairForm (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement) :
    IsPosSesqForm (p.pairForm ν μ) := by
  refine ⟨⟨fun F₁ F₂ H => ?_, fun c F H => ?_, fun F H₁ H₂ => ?_, fun c F H => ?_⟩, fun F => ?_⟩
  · simp only [pairForm_eq_reflPairing]
    exact reflPairing_add_left hA F₁.2.1.1 F₂.2.1.1 H.2.1.1
  · simp only [pairForm_eq_reflPairing]
    exact reflPairing_smul_left c
  · simp only [pairForm_eq_reflPairing]
    exact reflPairing_add_right hA F.2.1.1 H₁.2.1.1 H₂.2.1.1
  · simp only [pairForm_eq_reflPairing]
    exact reflPairing_smul_right c
  · have h : 0 ≤ p.pairForm ν μ F F := by
      rw [pairForm_eq_reflPairing, reflect_eq_baseMirror]
      exact reflPairing_self_nonneg hR (baseMirror_normal p μ) (baseMirror_height_nonpos p μ)
        F.2.1 F.2.2
    have h' := Complex.le_def.mp h
    exact ⟨by simpa using h'.2.symm, by simpa using h'.1⟩
theorem obsClass_of_mem {F : GaugeField (1 : ℝ) → ℂ}
    (h : F ∈ halfSpaceLocalObservables μ) :
    p.obsClass ν μ F = formClass (p.pairForm ν μ) ⟨F, h⟩ :=
  dif_pos h
theorem inner_obsClass (hpos : IsPosSesqForm (p.pairForm ν μ)) {F H : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) (hH : H ∈ halfSpaceLocalObservables μ) :
    inner ℂ (p.obsClass ν μ F) (p.obsClass ν μ H) = reflPairing ν (p.reflect μ) F H := by
  rw [obsClass_of_mem hF, obsClass_of_mem hH, inner_formClass hpos]
  exact p.pairForm_apply ν μ _ _
theorem norm_obsClass_sq (hpos : IsPosSesqForm (p.pairForm ν μ)) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) :
    ‖p.obsClass ν μ F‖ ^ 2 = ‖reflPairing ν (p.reflect μ) F F‖ := by
  rw [← inner_obsClass hpos hF hF, inner_self_eq_norm_sq_to_K]
  simp
theorem norm_obsClass_le_supNorm (hA : SymmetryActionAndReflections)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) :
    ‖p.obsClass ν μ F‖ ≤ observableSupNorm F := by
  have h := norm_reflPairing_le (ν := ν) (θ := p.reflect μ) hA hF.1.1
  rw [← norm_obsClass_sq hpos hF] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (supNorm_nonneg F) two_ne_zero).mp h
theorem nsmul_axisStep_apply_self (k : ℕ) (μ : Fin 4) :
    ((k • axisStep 1 μ : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = k := by
  simp [axisStep]
theorem nsmul_axisStep_apply_ne (k : ℕ) {i μ : Fin 4} (h : i ≠ μ) :
    ((k • axisStep 1 μ : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) i = 0 := by
  simp [axisStep, Pi.single_eq_of_ne h]
theorem norm_obsClass_translate_le (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) :
    ‖p.obsClass ν μ (translateObs (axisStep 1 μ) F)‖ ≤ ‖p.obsClass ν μ F‖ := by
  have hmem : ∀ k : ℕ, translateObs (k • axisStep 1 μ) F ∈ halfSpaceLocalObservables μ :=
    fun k => translateObs_mem hA hR hF (by rw [nsmul_axisStep_apply_self]; positivity)
  have h := le_of_sq_le_mul_doubled
    (a := fun k : ℕ => ‖p.obsClass ν μ (translateObs (k • axisStep 1 μ) F)‖)
    (M := observableSupNorm F) (fun _ => norm_nonneg _) (fun k => ?_) (fun k => ?_)
  · simpa [translateObs_zero] using h
  · refine (norm_obsClass_le_supNorm hA hpos (hmem k)).trans (supNorm_actOn hA _ hF.1.1).le
  · have e : ‖p.obsClass ν μ (translateObs (k • axisStep 1 μ) F)‖ ^ 2 =
        ‖inner ℂ (p.obsClass ν μ F)
          (p.obsClass ν μ (translateObs ((2 * k) • axisStep 1 μ) F))‖ := by
      rw [norm_obsClass_sq hpos (hmem k), inner_obsClass hpos hF (hmem (2 * k)),
        reflect_eq_baseMirror,
        reflPairing_translate_normal hA (baseMirror_normal p μ) (k • axisStep 1 μ)
          (fun i hi => nsmul_axisStep_apply_ne k hi) hF.1.1 (hmem k).1.1, translateObs_add,
        ← add_smul, two_mul]
    simp only [zero_smul, translateObs_zero]
    rw [e]
    exact norm_inner_le_norm _ _
def translateLinearMap (v : LatticePoint (1 : ℝ))
    (hmem : ∀ F ∈ halfSpaceLocalObservables μ, translateObs v F ∈ halfSpaceLocalObservables μ) :
    halfSpaceLocalObservables μ →ₗ[ℂ] halfSpaceLocalObservables μ where
  toFun F := ⟨translateObs v F, hmem F F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (ν μ p) in
def IntertwinesShift (v : LatticePoint (1 : ℝ)) (A : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) : Prop :=
  ∀ F ∈ halfSpaceLocalObservables μ, A (p.obsClass ν μ F) = p.obsClass ν μ (translateObs v F)
theorem ext_on_obsClasses (hc : FormCompletionClasses (p.pairForm ν μ))
    {A B : p.Hilb ν μ →L[ℂ] p.Hilb ν μ}
    (h : ∀ F ∈ halfSpaceLocalObservables μ, A (p.obsClass ν μ F) = B (p.obsClass ν μ F)) :
    A = B := by
  obtain ⟨-, -, -, M, hM, hd⟩ := hc
  have hdr : DenseRange (formClass (p.pairForm ν μ)) := by
    change Dense (Set.range (formClass (p.pairForm ν μ)))
    rw [← hM]
    exact hd
  refine DFunLike.coe_injective (hdr.equalizer A.continuous B.continuous (funext fun F => ?_))
  have := h F F.2
  rwa [obsClass_of_mem F.2] at this
theorem IntertwinesShift.mul {v w : LatticePoint (1 : ℝ)} {A B : p.Hilb ν μ →L[ℂ] p.Hilb ν μ}
    (hA : IntertwinesShift ν μ p v A) (hB : IntertwinesShift ν μ p w B)
    (hw : ∀ F ∈ halfSpaceLocalObservables μ, translateObs w F ∈ halfSpaceLocalObservables μ) :
    IntertwinesShift ν μ p (v + w) (A * B) := by
  intro F hF
  change A (B _) = _
  rw [hB F hF, hA _ (hw F hF), translateObs_add]
theorem intertwinesShift_one : IntertwinesShift ν μ p 0 1 := by
  intro F _
  rw [translateObs_zero]
  rfl
theorem IntertwinesShift.pow {v : LatticePoint (1 : ℝ)} {A : p.Hilb ν μ →L[ℂ] p.Hilb ν μ}
    (hA : IntertwinesShift ν μ p v A)
    (hv : ∀ (k : ℕ), ∀ F ∈ halfSpaceLocalObservables μ,
      translateObs (k • v) F ∈ halfSpaceLocalObservables μ)
    (n : ℕ) : IntertwinesShift ν μ p (n • v) (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact intertwinesShift_one
  | succ n ih =>
    rw [pow_succ', succ_nsmul']
    exact hA.mul ih (hv n)
theorem exists_intertwinesShift (hcl : ExtendsFromFormClasses (p.pairForm ν μ) (p.Hilb ν μ))
    (hpos : IsPosSesqForm (p.pairForm ν μ)) {v : LatticePoint (1 : ℝ)}
    (hmem : ∀ F ∈ halfSpaceLocalObservables μ, translateObs v F ∈ halfSpaceLocalObservables μ)
    (hle : ∀ F ∈ halfSpaceLocalObservables μ,
      ‖p.obsClass ν μ (translateObs v F)‖ ≤ ‖p.obsClass ν μ F‖) :
    ∃ A : p.Hilb ν μ →L[ℂ] p.Hilb ν μ, IntertwinesShift ν μ p v A ∧ ‖A‖ ≤ 1 ∧
      ((∀ F ∈ halfSpaceLocalObservables μ,
        ‖p.obsClass ν μ (translateObs v F)‖ = ‖p.obsClass ν μ F‖) →
        ∀ ψ ψ', inner ℂ (A ψ) (A ψ') = inner ℂ ψ ψ') := by
  have hsq : ∀ F : halfSpaceLocalObservables μ,
      ‖formClass (p.pairForm ν μ) F‖ ^ 2 = (p.pairForm ν μ F F).re := by
    intro F
    rw [← inner_formClass hpos F F, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hcoe : ∀ F : halfSpaceLocalObservables μ,
      formClass (p.pairForm ν μ) F = p.obsClass ν μ F := fun F =>
    (obsClass_of_mem F.2).symm
  let a : halfSpaceLocalObservables μ →ₗ[ℂ] p.Hilb ν μ :=
    (formClass (p.pairForm ν μ)) ∘ₗ translateLinearMap v hmem
  have haF : ∀ F : halfSpaceLocalObservables μ, a F = p.obsClass ν μ (translateObs v F) :=
    fun F => obsClass_of_mem (hmem F F.2) |>.symm
  have hb : ∀ F, ‖a F‖ ^ 2 ≤ (1 : ℝ) ^ 2 * (p.pairForm ν μ F F).re := by
    intro F
    rw [one_pow, one_mul, ← hsq, haF, hcoe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle F F.2) 2
  obtain ⟨⟨A, hAF, -⟩, hall⟩ := hcl 1 a zero_le_one hb
  obtain ⟨hnorm, huni⟩ := hall A hAF
  refine ⟨A, fun F hF => ?_, hnorm, fun heq => ?_⟩
  · have := hAF ⟨F, hF⟩
    rw [haF] at this
    rw [obsClass_of_mem hF]
    exact this
  · refine (huni fun F => ?_).1
    rw [← hsq, haF, hcoe, heq F F.2]
end Classes
section Family
variable {ν : unitPositiveClass} {μ : Fin 4} {p : ReflectionPair}
theorem norm_obsClass_translate_tangent (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) {v : LatticePoint (1 : ℝ)}
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) :
    ‖p.obsClass ν μ (translateObs v F)‖ = ‖p.obsClass ν μ F‖ := by
  have hm := translateObs_mem hA hR hF hv.ge
  have h := norm_obsClass_sq (ν := ν) (p := p) hpos hm
  rw [reflect_eq_baseMirror,
    reflPairing_translate_tangent hA (baseMirror_normal p μ) v hv hF.1.1 hF.1.1,
    ← reflect_eq_baseMirror, ← norm_obsClass_sq hpos hF] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
theorem exists_unitary_intertwinesShift (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) (hc : FormCompletionClasses (p.pairForm ν μ))
    (hcl : ExtendsFromFormClasses (p.pairForm ν μ) (p.Hilb ν μ)) {v : LatticePoint (1 : ℝ)}
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0) :
    ∃ U : p.Hilb ν μ →L[ℂ] p.Hilb ν μ,
      U ∈ unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ) ∧ IntertwinesShift ν μ p v U := by
  have hv' : ((-v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = 0 := by simp [hv]
  have hm : ∀ F ∈ halfSpaceLocalObservables μ, translateObs v F ∈ halfSpaceLocalObservables μ :=
    fun F hF => translateObs_mem hA hR hF hv.ge
  have hm' : ∀ F ∈ halfSpaceLocalObservables μ,
      translateObs (-v) F ∈ halfSpaceLocalObservables μ :=
    fun F hF => translateObs_mem hA hR hF hv'.ge
  have he := fun F (hF : F ∈ halfSpaceLocalObservables μ) =>
    norm_obsClass_translate_tangent (ν := ν) (p := p) hA hR hpos hv hF
  have he' := fun F (hF : F ∈ halfSpaceLocalObservables μ) =>
    norm_obsClass_translate_tangent (ν := ν) (p := p) hA hR hpos hv' hF
  obtain ⟨U, hU, -, hUi⟩ := exists_intertwinesShift hcl hpos hm fun F hF => (he F hF).le
  obtain ⟨U', hU', -, -⟩ := exists_intertwinesShift hcl hpos hm' fun F hF => (he' F hF).le
  have h₁ : U * U' = 1 := ext_on_obsClasses hc fun F hF => by
    have h := (hU.mul hU' hm') F hF
    rw [add_neg_cancel, translateObs_zero] at h
    exact h
  have h₂ : U' * U = 1 := ext_on_obsClasses hc fun F hF => by
    have h := (hU'.mul hU hm) F hF
    rw [neg_add_cancel, translateObs_zero] at h
    exact h
  refine ⟨U, (mem_unitary_iff_isUnitaryLinearMap U).mpr ⟨?_, hUi he⟩, hU⟩
  refine Function.bijective_iff_has_inverse.mpr ⟨U', fun ψ => ?_, fun ψ => ?_⟩
  · exact congrArg (fun A : p.Hilb ν μ →L[ℂ] p.Hilb ν μ => A ψ) h₂
  · exact congrArg (fun A : p.Hilb ν μ →L[ℂ] p.Hilb ν μ => A ψ) h₁
theorem IntertwinesShift.commute {v w : LatticePoint (1 : ℝ)}
    {A B : p.Hilb ν μ →L[ℂ] p.Hilb ν μ}
    (hc : FormCompletionClasses (p.pairForm ν μ))
    (hA : IntertwinesShift ν μ p v A) (hB : IntertwinesShift ν μ p w B)
    (hv : ∀ F ∈ halfSpaceLocalObservables μ, translateObs v F ∈ halfSpaceLocalObservables μ)
    (hw : ∀ F ∈ halfSpaceLocalObservables μ, translateObs w F ∈ halfSpaceLocalObservables μ) :
    Commute A B :=
  ext_on_obsClasses hc fun F hF => by
    have h₁ := (hA.mul hB hw) F hF
    have h₂ := (hB.mul hA hv) F hF
    rw [add_comm] at h₂
    exact h₁.trans h₂.symm
theorem transfer_selfAdjoint_bounds (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) (hc : FormCompletionClasses (p.pairForm ν μ))
    (hsa : SelfAdjointCriteria (p.Hilb ν μ))
    {T : p.Hilb ν μ →L[ℂ] p.Hilb ν μ} (hT : IntertwinesShift ν μ p (axisStep 1 μ) T)
    (hTn : ‖T‖ ≤ 1) :
    IsSelfAdjoint T ∧ 0 ≤ T ∧ T ≤ 1 := by
  have hm : ∀ F ∈ halfSpaceLocalObservables μ,
      translateObs (axisStep 1 μ) F ∈ halfSpaceLocalObservables μ :=
    fun F hF => translateObs_mem hA hR hF (by rw [axisStep_apply_self]; norm_num)
  obtain ⟨-, -, -, M, hM, hd⟩ := hc
  have hcl : ∀ ψ ∈ M, ∃ F ∈ halfSpaceLocalObservables μ, ψ = p.obsClass ν μ F := by
    intro ψ hψ
    have h : ψ ∈ (M : Set (p.Hilb ν μ)) := hψ
    rw [hM] at h
    obtain ⟨F, rfl⟩ := h
    exact ⟨F, F.2, (obsClass_of_mem F.2).symm⟩
  have hsym : ∀ ψ ∈ M, ∀ ψ' ∈ M, inner ℂ ψ (T ψ') = inner ℂ (T ψ) ψ' := by
    intro ψ hψ ψ' hψ'
    obtain ⟨F, hF, rfl⟩ := hcl ψ hψ
    obtain ⟨H, hH, rfl⟩ := hcl ψ' hψ'
    rw [hT H hH, hT F hF, inner_obsClass hpos hF (hm H hH), inner_obsClass hpos (hm F hF) hH,
      reflect_eq_baseMirror, reflPairing_translate_normal hA (baseMirror_normal p μ) (axisStep 1 μ)
        (fun i hi => by simp [axisStep, Pi.single_eq_of_ne hi]) hF.1.1 hH.1.1]
  have hnn : ∀ ψ ∈ M, 0 ≤ inner ℂ ψ (T ψ) := by
    intro ψ hψ
    obtain ⟨F, hF, rfl⟩ := hcl ψ hψ
    rw [hT F hF, inner_obsClass hpos hF (hm F hF), reflect_eq_baseMirror]
    have h := reflPairing_self_nonneg (ν := ν) hR (raisedMirror_normal p μ)
      (t := ((axisStep 1 μ : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ)
      (by rw [axisStep_apply_self, raisedMirror_height]; linarith [baseMirror_height_nonpos p μ])
      (translateObs_mem_upper hA hR hF (axisStep 1 μ)) (isLocalObservable_actOn hA _ hF.1.1 hF.2)
    have e : reflPairing ν (raisedMirror p μ).reflect (translateObs (axisStep 1 μ) F)
        (translateObs (axisStep 1 μ) F) =
        reflPairing ν (baseMirror p μ).reflect F (translateObs (axisStep 1 μ) F) := by
      rw [← raisedMirror_reflect_comp_shift p μ]
      rfl
    rwa [e] at h
  obtain ⟨hTs, hT0⟩ := hsa.1 T M hd hsym
  have hT0 := hT0 hnn
  refine ⟨hTs, hT0, (le_iff_inner_sub_nonneg (IsSelfAdjoint.one _) hTs).mpr fun ψ => ?_⟩
  have hz : 0 ≤ inner ℂ ψ (T ψ) := by
    simpa using (le_iff_inner_sub_nonneg hTs (IsSelfAdjoint.zero _)).mp hT0 ψ
  have hz' := Complex.le_def.mp hz
  have hle : (inner ℂ ψ (T ψ)).re ≤ ‖ψ‖ ^ 2 :=
    calc (inner ℂ ψ (T ψ)).re ≤ ‖inner ℂ ψ (T ψ)‖ := Complex.re_le_norm _
      _ ≤ ‖ψ‖ * ‖T ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * ‖ψ‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖T ψ‖ ≤ ‖T‖ * ‖ψ‖ := T.le_opNorm ψ
          _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right hTn (norm_nonneg _)
          _ = ‖ψ‖ := one_mul _
      _ = ‖ψ‖ ^ 2 := (sq _).symm
  have hin : inner ℂ ψ (((1 : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) - T) ψ) =
      ((‖ψ‖ ^ 2 : ℝ) : ℂ) - inner ℂ ψ (T ψ) := by
    change inner ℂ ψ (ψ - T ψ) = _
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hin, Complex.le_def]
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re, Complex.ofReal_re, Complex.zero_re]
    linarith
  · have h := hz'.2
    rw [Complex.zero_im] at h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im]
    linarith
theorem exists_opFamily (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    (hpos : IsPosSesqForm (p.pairForm ν μ)) (hc : FormCompletionClasses (p.pairForm ν μ))
    (hcl : ExtendsFromFormClasses (p.pairForm ν μ) (p.Hilb ν μ))
    (hsa : SelfAdjointCriteria (p.Hilb ν μ)) :
    (∃! T, p.IsTransferOp ν μ T) ∧
      (∀ l : TransverseAxis μ, ∃! U : p.Hilb ν μ →L[ℂ] p.Hilb ν μ,
        U ∈ unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ) ∧ p.IsShiftOp ν μ l.1 U) ∧
      ∃ S, p.IsOpFamily ν μ S := by
  have hm : ∀ F ∈ halfSpaceLocalObservables μ,
      translateObs (axisStep 1 μ) F ∈ halfSpaceLocalObservables μ :=
    fun F hF => translateObs_mem hA hR hF (by rw [axisStep_apply_self]; norm_num)
  have hml : ∀ l : TransverseAxis μ, ∀ F ∈ halfSpaceLocalObservables μ,
      translateObs (axisStep 1 l.1) F ∈ halfSpaceLocalObservables μ :=
    fun l F hF => translateObs_mem hA hR hF (axisStep_apply_ne l.2).ge
  obtain ⟨T, hT, hTn, -⟩ := exists_intertwinesShift hcl hpos hm fun F hF =>
    norm_obsClass_translate_le hA hR hpos hF
  obtain ⟨hTs, hT0, hT1⟩ := transfer_selfAdjoint_bounds hA hR hpos hc hsa hT hTn
  have hUex := fun l : TransverseAxis μ =>
    exists_unitary_intertwinesShift (ν := ν) (p := p) hA hR hpos hc hcl (axisStep_apply_ne l.2)
  choose U hUm hU using hUex
  refine ⟨⟨T, hT, fun T' hT' => ext_on_obsClasses hc fun F hF =>
      (hT' F hF).trans (hT F hF).symm⟩,
    fun l => ⟨U l, ⟨hUm l, hU l⟩, fun U' hU' => ext_on_obsClasses hc fun F hF =>
      (hU'.2 F hF).trans (hU l F hF).symm⟩, ?_⟩
  exact ⟨{ A := T
           B := fun l => ⟨U l, hUm l⟩
           isSelfAdjoint_A := hTs
           zero_le_A := hT0
           A_le_one := hT1
           commute_A_B := fun l => IntertwinesShift.commute hc hT (hU l) hm (hml l)
           commute_B_B := fun l l' => IntertwinesShift.commute hc (hU l) (hU l') (hml l) (hml l') },
    hT, hU⟩
theorem nsmul_apply_eq_zero {v : LatticePoint (1 : ℝ)}
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0) (k : ℕ) :
    ((k • v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = 0 := by
  simp [hv]
theorem intertwinesShift_zpow (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    {u : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)} {v : LatticePoint (1 : ℝ)}
    (hv : (v : InfiniteLattice.AmbientSpace) μ = 0)
    (hu : IntertwinesShift ν μ p v (u : p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) (k : ℤ) :
    IntertwinesShift ν μ p (k • v) ((u ^ k : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) :
      p.Hilb ν μ →L[ℂ] p.Hilb ν μ) := by
  have hv' : ((-v : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) μ = 0 := by simp [hv]
  have hinv : IntertwinesShift ν μ p (-v)
      ((u⁻¹ : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) := by
    intro F hF
    have h := hu _ (translateObs_mem hA hR hF hv'.ge)
    rw [translateObs_add, add_neg_cancel, translateObs_zero] at h
    rw [← h]
    have e := congrArg (fun g : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ) =>
      (g : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) (p.obsClass ν μ (translateObs (-v) F)))
      (inv_mul_cancel u)
    exact e
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul]
    have e : ((u ^ n : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) :
        p.Hilb ν μ →L[ℂ] p.Hilb ν μ) = (u : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) ^ n := by simp
    rw [e]
    exact hu.pow (fun k F hF => translateObs_mem hA hR hF (nsmul_apply_eq_zero hv k).ge) n
  · have hk : (-(n : ℤ)) • v = n • (-v) := by simp
    rw [hk, zpow_neg, zpow_natCast, ← inv_pow]
    have e : (((u⁻¹) ^ n : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) :
        p.Hilb ν μ →L[ℂ] p.Hilb ν μ) =
        ((u⁻¹ : unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) ^ n :=
      SubmonoidClass.coe_pow (u⁻¹) n
    rw [e]
    exact hinv.pow (fun k F hF => translateObs_mem hA hR hF (nsmul_apply_eq_zero hv' k).ge) n
theorem intertwinesShift_noncommProd (hA : SymmetryActionAndReflections)
    (hR : InfiniteLattice.LinkLocalFunctions.Statement)
    {S : CommutingFamily (p.Hilb ν μ) (TransverseAxis μ)} (hS : p.IsOpFamily ν μ S)
    (y : TransverseAxis μ → ℤ) (s : Finset (TransverseAxis μ)) :
    ∀ hcomm, IntertwinesShift ν μ p (∑ l ∈ s, y l • axisStep 1 l.1)
        ((s.noncommProd (fun l => S.B l ^ y l) hcomm :
          unitary (p.Hilb ν μ →L[ℂ] p.Hilb ν μ)) : p.Hilb ν μ →L[ℂ] p.Hilb ν μ) ∧
      ((∑ l ∈ s, y l • axisStep 1 l.1 : LatticePoint (1 : ℝ)) :
        InfiniteLattice.AmbientSpace) μ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hcomm
    refine ⟨?_, by simp⟩
    simpa using intertwinesShift_one (ν := ν) (μ := μ) (p := p)
  | insert a s ha ih =>
    intro hcomm
    have ha0 : ((y a • axisStep 1 a.1 : LatticePoint (1 : ℝ)) :
        InfiniteLattice.AmbientSpace) μ = 0 := by
      simp [axisStep_apply_ne a.2]
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.sum_insert ha]
    obtain ⟨h₁, h₂⟩ := ih (hcomm.mono fun l hl => Finset.mem_insert_of_mem hl)
    refine ⟨?_, ?_⟩
    · exact (intertwinesShift_zpow hA hR (axisStep_apply_ne a.2) (hS.2 a) (y a)).mul h₁
        (fun F hF => translateObs_mem hA hR hF h₂.ge)
    · rw [AddSubgroup.coe_add, Pi.add_apply, ha0, h₂, add_zero]
theorem sum_transverse_axisSteps (w : Fin 4 → ℤ) (hw : w μ = 0) :
    ∑ l : TransverseAxis μ, w l.1 • axisStep 1 l.1 = intPoint w := by
  apply Subtype.ext
  funext i
  let g : Fin 4 → ℝ := fun l =>
    ((w l • axisStep 1 l : LatticePoint (1 : ℝ)) : InfiniteLattice.AmbientSpace) i
  have e : ((∑ l : TransverseAxis μ, w l.1 • axisStep 1 l.1 : LatticePoint (1 : ℝ)) :
      InfiniteLattice.AmbientSpace) i = ∑ l : TransverseAxis μ, g l.1 := by
    simp only [g, AddSubgroup.val_finsetSum, Finset.sum_apply]
  rw [e, ← Finset.sum_subtype (Finset.univ.filter (· ≠ μ)) (by simp) g,
    Finset.sum_filter_of_ne, Finset.sum_eq_single i]
  · simp [g, axisStep, intPoint]
  · intro l _ hl
    simp [g, axisStep, Pi.single_eq_of_ne hl.symm]
  · simp
  · intro l _ hl hlμ
    subst hlμ
    exact hl (by simp [g, hw])
end Family
theorem reflectionPairTheorem_holds (hAct : SymmetryActionAndReflections)
    (hHil : FormCompletionAndExtensionTheorem)
    (hReads : InfiniteLattice.LinkLocalFunctions.Statement)
    (hSpec : JointSpectralCalculusTheorem) : ReflectionPairTheorem := by
  intro ν μ p
  have hpos : IsPosSesqForm (p.pairForm ν μ) := isPosSesqForm_pairForm hAct hReads
  obtain ⟨-, hc, -, hcl, -, -, hsa⟩ :=
    hHil (halfSpaceLocalObservables μ) (p.Hilb ν μ) (p.Hilb ν μ) (p.pairForm ν μ) hpos
  obtain ⟨hTex, hUex, hSex⟩ := exists_opFamily hAct hReads hpos hc hcl hsa
  have hsys : p.IsOpFamily ν μ (p.opFamily ν μ) := Classical.epsilon_spec hSex
  obtain ⟨-, hE, hall⟩ := hSpec (p.Hilb ν μ) (TransverseAxis μ) (p.opFamily ν μ)
  have hspec : IsJointPVM (p.opFamily ν μ) (p.jointPVM ν μ) :=
    Classical.epsilon_spec hE.exists
  obtain ⟨-, -, -, -, hk, -⟩ := hall _ hspec
  refine ⟨⟨hpos, hpos.isConjSymm, fun F hF => norm_obsClass_le_supNorm hAct hpos hF⟩,
    ⟨hTex, hUex, hsys⟩, ?_, hE, hspec, hk.oneLevel, hk.zeroLevel⟩
  intro F hF H hH n w hw
  have hU := (intertwinesShift_noncommProd hAct hReads hsys (fun l => w l.1) Finset.univ
    (fun l _ l' _ _ => (p.opFamily ν μ).commute_zpow_unitary (fun l => w l.1) l l'))
  rw [sum_transverse_axisSteps w hw] at hU
  have hT : IntertwinesShift ν μ p (n • axisStep 1 μ) ((p.opFamily ν μ).A ^ n) :=
    IntertwinesShift.pow hsys.1 (fun k F hF => translateObs_mem hAct hReads hF
      (by rw [nsmul_axisStep_apply_self]; positivity)) n
  have hmem : ∀ G ∈ halfSpaceLocalObservables μ,
      translateObs (intPoint w) G ∈ halfSpaceLocalObservables μ :=
    fun G hG => translateObs_mem hAct hReads hG hU.2.ge
  have h := (hT.mul hU.1 hmem) H hH
  have hG : translateObs (n • axisStep 1 μ + intPoint w) H ∈ halfSpaceLocalObservables μ :=
    translateObs_mem hAct hReads hH (by
      rw [AddSubgroup.coe_add, Pi.add_apply, nsmul_axisStep_apply_self, hU.2]
      simp)
  exact (congrArg (inner ℂ (p.obsClass ν μ F)) h).trans (inner_obsClass hpos hF hG)
end ReflectionPairProof
end YangMills.Construction.ReflectionPositivity.DirectionPictures
