import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.RealTransposeConstruction
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.LeftChartFields
def hermComponent (Y : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (Y + Y.conjTranspose)
def skewComponent (Y : ComplexMatrix2) : ComplexMatrix2 :=
  (2 * Complex.I)⁻¹ • (Y - Y.conjTranspose)
theorem hermComponent_add_I_smul_skewComponent (Y : ComplexMatrix2) :
    hermComponent Y + Complex.I • skewComponent Y = Y := by
  have key : Complex.I * (2 * Complex.I)⁻¹ = 1 / 2 := by
    field_simp
  rw [hermComponent, skewComponent, smul_smul, key]
  module
theorem mem_hermitianTraceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.hermitianTraceless ↔
      X = X.conjTranspose ∧ ComplexMatrix2.fullTrace X = 0 := Iff.rfl
theorem mem_traceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.traceless ↔ ComplexMatrix2.fullTrace X = 0 := Iff.rfl
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless :=
  mem_traceless_iff.2 (mem_hermitianTraceless_iff.1 hX).2
theorem fullTrace_conjTranspose (Y : ComplexMatrix2) :
    ComplexMatrix2.fullTrace Y.conjTranspose = star (ComplexMatrix2.fullTrace Y) :=
  Matrix.trace_conjTranspose Y
theorem hermComponent_mem {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless) :
    hermComponent Y ∈ ComplexMatrix2.hermitianTraceless := by
  have htr : ComplexMatrix2.fullTrace Y = 0 := mem_traceless_iff.1 hY
  refine mem_hermitianTraceless_iff.2 ⟨?_, ?_⟩
  · simp only [hermComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    simp [add_comm]
  · simp only [hermComponent, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_conjTranspose]
    simp only [ComplexMatrix2.fullTrace] at htr
    simp [htr]
theorem skewComponent_mem {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless) :
    skewComponent Y ∈ ComplexMatrix2.hermitianTraceless := by
  have htr : ComplexMatrix2.fullTrace Y = 0 := mem_traceless_iff.1 hY
  refine mem_hermitianTraceless_iff.2 ⟨?_, ?_⟩
  · simp only [skewComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have hstar : star ((2 * Complex.I)⁻¹) = -(2 * Complex.I)⁻¹ := by
      simp [Complex.conj_I]
    rw [hstar]
    module
  · simp only [skewComponent, ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_conjTranspose]
    simp only [ComplexMatrix2.fullTrace] at htr
    simp [htr]
theorem conjTranspose_add_I_smul {X Y : ComplexMatrix2} (hX : X = X.conjTranspose)
    (hY : Y = Y.conjTranspose) :
    (X + Complex.I • Y).conjTranspose = X - Complex.I • Y := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, ← hX, ← hY]
  simp [sub_eq_add_neg]
theorem hermComponent_add_I_smul {X Y : ComplexMatrix2} (hX : X = X.conjTranspose)
    (hY : Y = Y.conjTranspose) : hermComponent (X + Complex.I • Y) = X := by
  rw [hermComponent, conjTranspose_add_I_smul hX hY]
  module
theorem skewComponent_add_I_smul {X Y : ComplexMatrix2} (hX : X = X.conjTranspose)
    (hY : Y = Y.conjTranspose) : skewComponent (X + Complex.I • Y) = Y := by
  have key : (2 * Complex.I)⁻¹ * (2 * Complex.I) = 1 := by
    field_simp
  rw [skewComponent, conjTranspose_add_I_smul hX hY]
  have hdiff : X + Complex.I • Y - (X - Complex.I • Y) = (2 * Complex.I) • Y := by module
  rw [hdiff, smul_smul, key, one_smul]
theorem smul_add_I_smul (c : ℂ) (A B : ComplexMatrix2) :
    c • (A + Complex.I • B) =
      (c.re • A - c.im • B) + Complex.I • (c.im • A + c.re • B) := by
  have hc := Complex.re_add_im c
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul]
  linear_combination (-(A a b + Complex.I * B a b)) * hc + ((c.im : ℂ) * B a b) * Complex.I_sq
open ComplexOrder in
theorem eq_zero_of_fullTrace_mul_self {D : ComplexMatrix2} (hD : D = D.conjTranspose)
    (htr : ComplexMatrix2.fullTrace (D * D) = 0) : D = 0 := by
  have htr' : Matrix.trace (D.conjTranspose * D) = 0 := by rw [← hD]; exact htr
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 htr'
variable {ι ι' : Type}
abbrev LieFn (ι : Type) : Type := ↥(pairedFunctions ι).realSubmodule
abbrev ComplexLieFn (ι : Type) : Type := ↥(pairedFunctions ι).complexSubmodule
theorem mem_realSubmodule_iff {f : ι → ComplexMatrix2} :
    f ∈ (pairedFunctions ι).realSubmodule ↔ ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless := by
  change f ∈ GroupLieProduct.hermitianTracelessFunctions ι ↔ _
  simp [GroupLieProduct.hermitianTracelessFunctions, Submodule.mem_pi]
theorem mem_complexSubmodule_iff {f : ι → ComplexMatrix2} :
    f ∈ (pairedFunctions ι).complexSubmodule ↔ ∀ i, f i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.mem_complexSubmodule_iff <;> assumption
theorem LieFn.apply_mem (g : LieFn ι) (i : ι) : g.1 i ∈ ComplexMatrix2.hermitianTraceless :=
  mem_realSubmodule_iff.1 g.2 i
theorem ComplexLieFn.apply_mem (g : ComplexLieFn ι) (i : ι) :
    g.1 i ∈ ComplexMatrix2.traceless :=
  mem_complexSubmodule_iff.1 g.2 i
theorem LieFn.apply_eq_conjTranspose (g : LieFn ι) (i : ι) :
    g.1 i = (g.1 i).conjTranspose :=
  (mem_hermitianTraceless_iff.1 (LieFn.apply_mem g i)).1
def ofLie (g : LieFn ι) : ComplexLieFn ι :=
  ⟨g.1, mem_complexSubmodule_iff.2 fun i =>
    mem_traceless_of_mem_hermitianTraceless (LieFn.apply_mem g i)⟩
def reFn (f : ComplexLieFn ι) : LieFn ι :=
  ⟨fun i => hermComponent (f.1 i),
    mem_realSubmodule_iff.2 fun i => hermComponent_mem (ComplexLieFn.apply_mem f i)⟩
def imFn (f : ComplexLieFn ι) : LieFn ι :=
  ⟨fun i => skewComponent (f.1 i),
    mem_realSubmodule_iff.2 fun i => skewComponent_mem (ComplexLieFn.apply_mem f i)⟩
theorem val_eq_reFn_add_imFn (f : ComplexLieFn ι) :
    f.1 = (reFn f).1 + Complex.I • (imFn f).1 :=
  funext fun i => (hermComponent_add_I_smul_skewComponent (f.1 i)).symm
theorem reFn_imFn_of_eq {h : ComplexLieFn ι} {u v : LieFn ι}
    (hs : h.1 = u.1 + Complex.I • v.1) : reFn h = u ∧ imFn h = v := by
  constructor
  · refine Subtype.ext (funext fun i => ?_)
    change hermComponent (h.1 i) = u.1 i
    rw [hs]
    exact hermComponent_add_I_smul (LieFn.apply_eq_conjTranspose u i)
      (LieFn.apply_eq_conjTranspose v i)
  · refine Subtype.ext (funext fun i => ?_)
    change skewComponent (h.1 i) = v.1 i
    rw [hs]
    exact skewComponent_add_I_smul (LieFn.apply_eq_conjTranspose u i)
      (LieFn.apply_eq_conjTranspose v i)
theorem hasRealDecomposition (ι : Type) : (pairedFunctions ι).HasRealDecomposition := by
  intro f
  refine ⟨(reFn f, imFn f), val_eq_reFn_add_imFn f, ?_⟩
  rintro ⟨p₁, p₂⟩ hs
  obtain ⟨h₁, h₂⟩ := reFn_imFn_of_eq (h := f) (u := p₁) (v := p₂) hs
  exact Prod.ext h₁.symm h₂.symm
theorem apply_eq_reFn_add_imFn (f : ComplexLieFn ι) (i : ι) :
    f.1 i = (reFn f).1 i + Complex.I • (imFn f).1 i :=
  (hermComponent_add_I_smul_skewComponent (f.1 i)).symm
section Extension
variable (T₀ : LieFn ι →ₗ[ℝ] LieFn ι')
def extendFun (h : ComplexLieFn ι) : ComplexLieFn ι' :=
  ⟨(T₀ (reFn h)).1 + Complex.I • (T₀ (imFn h)).1,
    (pairedFunctions ι').complexSubmodule.add_mem (ofLie (T₀ (reFn h))).2
      ((pairedFunctions ι').complexSubmodule.smul_mem _ (ofLie (T₀ (imFn h))).2)⟩
theorem extendFun_val_of_eq {h : ComplexLieFn ι} {u v : LieFn ι}
    (hs : h.1 = u.1 + Complex.I • v.1) :
    (extendFun T₀ h).1 = (T₀ u).1 + Complex.I • (T₀ v).1 := by
  obtain ⟨rfl, rfl⟩ := reFn_imFn_of_eq hs
  rfl
def extend : ComplexLieFn ι →ₗ[ℂ] ComplexLieFn ι' where
  toFun := extendFun T₀
  map_add' h h' := by
    refine Subtype.ext ?_
    have hs : (h + h').1 = (reFn h + reFn h').1 + Complex.I • (imFn h + imFn h').1 := by
      funext i
      change h.1 i + h'.1 i = ((reFn h).1 i + (reFn h').1 i) +
        Complex.I • ((imFn h).1 i + (imFn h').1 i)
      rw [apply_eq_reFn_add_imFn h i, apply_eq_reFn_add_imFn h' i]
      module
    rw [extendFun_val_of_eq T₀ hs, map_add, map_add]
    funext i
    change ((T₀ (reFn h)).1 i + (T₀ (reFn h')).1 i) +
        Complex.I • ((T₀ (imFn h)).1 i + (T₀ (imFn h')).1 i) =
      ((T₀ (reFn h)).1 i + Complex.I • (T₀ (imFn h)).1 i) +
        ((T₀ (reFn h')).1 i + Complex.I • (T₀ (imFn h')).1 i)
    module
  map_smul' c h := by
    refine Subtype.ext ?_
    have hs : (c • h).1 = (c.re • reFn h - c.im • imFn h).1 +
        Complex.I • (c.im • reFn h + c.re • imFn h).1 := by
      funext i
      change c • h.1 i = (c.re • (reFn h).1 i - c.im • (imFn h).1 i) +
        Complex.I • (c.im • (reFn h).1 i + c.re • (imFn h).1 i)
      rw [apply_eq_reFn_add_imFn h i]
      exact smul_add_I_smul c _ _
    rw [extendFun_val_of_eq T₀ hs]
    simp only [map_add, map_sub, map_smul]
    funext i
    change (c.re • (T₀ (reFn h)).1 i - c.im • (T₀ (imFn h)).1 i) +
        Complex.I • (c.im • (T₀ (reFn h)).1 i + c.re • (T₀ (imFn h)).1 i) =
      c • ((T₀ (reFn h)).1 i + Complex.I • (T₀ (imFn h)).1 i)
    exact (smul_add_I_smul c _ _).symm
theorem isComplexification_extend : PairedFunctionSpace.IsComplexification T₀ (extend T₀) :=
  fun _ _ _ hs => extendFun_val_of_eq T₀ hs
theorem complexification_eq_extend : PairedFunctionSpace.complexification T₀ = extend T₀ := by
  have hspec : PairedFunctionSpace.IsComplexification T₀
      (PairedFunctionSpace.complexification T₀) :=
    Classical.epsilon_spec ⟨extend T₀, isComplexification_extend T₀⟩
  refine LinearMap.ext fun h => Subtype.ext ?_
  exact (hspec (reFn h) (imFn h) h (val_eq_reFn_add_imFn h)).trans
    (isComplexification_extend T₀ (reFn h) (imFn h) h (val_eq_reFn_add_imFn h)).symm
theorem extend_ofLie_val (f : LieFn ι) : (extend T₀ (ofLie f)).1 = (T₀ f).1 := by
  have hs : (ofLie f).1 = f.1 + Complex.I • (0 : LieFn ι).1 := by
    funext i
    change f.1 i = f.1 i + Complex.I • (0 : ComplexMatrix2)
    simp
  have hval := extendFun_val_of_eq T₀ hs
  rw [map_zero] at hval
  refine hval.trans (funext fun i => ?_)
  change (T₀ f).1 i + Complex.I • (0 : ComplexMatrix2) = (T₀ f).1 i
  simp
theorem preservesFiniteSupport_extend
    (hT : PairedFunctionSpace.PreservesRealFiniteSupport T₀) :
    PairedFunctionSpace.PreservesFiniteSupport (extend T₀) := by
  intro f hf
  have hf' : (Function.support f.1).Finite := hf
  have hre : (pairedFunctions ι).IsFinitelySupported (reFn f).1 := by
    refine Set.Finite.subset hf' fun i hi => Function.mem_support.2 fun hz =>
      Function.mem_support.1 hi ?_
    change hermComponent (f.1 i) = 0
    rw [hz]
    simp [hermComponent]
  have him : (pairedFunctions ι).IsFinitelySupported (imFn f).1 := by
    refine Set.Finite.subset hf' fun i hi => Function.mem_support.2 fun hz =>
      Function.mem_support.1 hi ?_
    change skewComponent (f.1 i) = 0
    rw [hz]
    simp [skewComponent]
  have h₁ : (Function.support (T₀ (reFn f)).1).Finite := hT _ hre
  have h₂ : (Function.support (T₀ (imFn f)).1).Finite := hT _ him
  refine Set.Finite.subset (h₁.union h₂) fun i hi => ?_
  by_contra hn
  rw [Set.mem_union, not_or, Function.mem_support, Function.mem_support, not_not, not_not] at hn
  refine Function.mem_support.1 hi ?_
  change (T₀ (reFn f)).1 i + Complex.I • (T₀ (imFn f)).1 i = 0
  rw [hn.1, hn.2]
  simp
def conjFn (h : ComplexLieFn ι) : ComplexLieFn ι :=
  ⟨fun i => (h.1 i).conjTranspose, mem_complexSubmodule_iff.2 fun i => mem_traceless_iff.2 (by
    rw [fullTrace_conjTranspose, mem_traceless_iff.1 (ComplexLieFn.apply_mem h i)]
    simp)⟩
theorem conjFn_conjFn (h : ComplexLieFn ι) : conjFn (conjFn h) = h :=
  Subtype.ext (funext fun _ => Matrix.conjTranspose_conjTranspose _)
theorem conjFn_ofLie (g : LieFn ι) : conjFn (ofLie g) = ofLie g :=
  Subtype.ext (funext fun i => (LieFn.apply_eq_conjTranspose g i).symm)
theorem conjFn_val (h : ComplexLieFn ι) :
    (conjFn h).1 = (reFn h).1 + Complex.I • (-(imFn h)).1 := by
  funext i
  change (h.1 i).conjTranspose = (reFn h).1 i + Complex.I • (-(imFn h).1 i)
  conv_lhs => rw [apply_eq_reFn_add_imFn h i]
  rw [conjTranspose_add_I_smul (LieFn.apply_eq_conjTranspose (reFn h) i)
    (LieFn.apply_eq_conjTranspose (imFn h) i)]
  module
theorem extend_conjFn (h : ComplexLieFn ι) : extend T₀ (conjFn h) = conjFn (extend T₀ h) := by
  refine Subtype.ext ?_
  have hval := extendFun_val_of_eq T₀ (conjFn_val h)
  rw [map_neg] at hval
  refine hval.trans (funext fun i => ?_)
  change (T₀ (reFn h)).1 i + Complex.I • (-(T₀ (imFn h)).1 i) =
    ((T₀ (reFn h)).1 i + Complex.I • (T₀ (imFn h)).1 i).conjTranspose
  rw [conjTranspose_add_I_smul (LieFn.apply_eq_conjTranspose (T₀ (reFn h)) i)
    (LieFn.apply_eq_conjTranspose (T₀ (imFn h)) i)]
  module
end Extension
theorem traceFinsumPairing_conjTranspose (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (fun i => (f i).conjTranspose) (fun i => (g i).conjTranspose) =
      star (traceFinsumPairing f g) := by
  unfold traceFinsumPairing
  refine Eq.trans (finsum_congr fun i => ?_) ((starAddEquiv (R := ℂ)).map_finsum _).symm
  change ComplexMatrix2.halfTrace ((f i).conjTranspose * (g i).conjTranspose) =
    star (ComplexMatrix2.halfTrace (f i * g i))
  rw [← Matrix.conjTranspose_mul]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose,
    Matrix.trace_mul_comm (g i)]
  simp
theorem transposeMap_spec (H : HasUniqueTranspose (pairedFunctions ι) (pairedFunctions ι'))
    (T : ComplexLieFn ι →ₗ[ℂ] ComplexLieFn ι')
    (hT : PairedFunctionSpace.PreservesFiniteSupport T) :
    PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) ∧
      ∀ R : ComplexLieFn ι' → ComplexLieFn ι,
        (∀ (g : ComplexLieFn ι') (f : ComplexLieFn ι),
          (pairedFunctions ι).IsFinitelySupported f →
          (pairedFunctions ι).pair (R g) f = (pairedFunctions ι').pair g (T f)) →
        R = PairedFunctionSpace.transposeMap T := by
  obtain ⟨T', h₁, h₂⟩ := H T hT
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec ⟨T', h₁⟩
  have heq : PairedFunctionSpace.transposeMap T = T' := DFunLike.coe_injective (h₂ _ hspec)
  rw [heq]
  exact ⟨h₁, h₂⟩
section Transpose
variable (T₀ : LieFn ι →ₗ[ℝ] LieFn ι')
  (H : HasUniqueTranspose (pairedFunctions ι) (pairedFunctions ι'))
  (hT : PairedFunctionSpace.PreservesRealFiniteSupport T₀)
include H hT
theorem transposeMap_extend_conjFn (g : ComplexLieFn ι') :
    PairedFunctionSpace.transposeMap (extend T₀) (conjFn g) =
      conjFn (PairedFunctionSpace.transposeMap (extend T₀) g) := by
  obtain ⟨s₁, s₂⟩ := transposeMap_spec H (extend T₀) (preservesFiniteSupport_extend T₀ hT)
  have hR : (fun g => conjFn (PairedFunctionSpace.transposeMap (extend T₀) (conjFn g))) =
      ⇑(PairedFunctionSpace.transposeMap (extend T₀)) := by
    refine s₂ _ fun g f hf => ?_
    have hf' : (pairedFunctions ι).IsFinitelySupported (conjFn f).1 := by
      refine Set.Finite.subset (show (Function.support f.1).Finite from hf) fun i hi =>
        Function.mem_support.2 fun hz => Function.mem_support.1 hi ?_
      change (f.1 i).conjTranspose = 0
      rw [hz]
      simp
    have ha := s₁ (conjFn g) (conjFn f) hf'
    have ha' : traceFinsumPairing
        (PairedFunctionSpace.transposeMap (extend T₀) (conjFn g)).1 (conjFn f).1 =
        traceFinsumPairing (conjFn g).1 (conjFn (extend T₀ f)).1 := by
      rw [← extend_conjFn]
      exact ha
    have hb : traceFinsumPairing
        (conjFn (PairedFunctionSpace.transposeMap (extend T₀) (conjFn g))).1
          (conjFn (conjFn f)).1 =
        star (traceFinsumPairing
          (PairedFunctionSpace.transposeMap (extend T₀) (conjFn g)).1 (conjFn f).1) :=
      traceFinsumPairing_conjTranspose _ _
    rw [conjFn_conjFn] at hb
    have hc : traceFinsumPairing (conjFn g).1 (conjFn (extend T₀ f)).1 =
        star (traceFinsumPairing g.1 (extend T₀ f).1) :=
      traceFinsumPairing_conjTranspose _ _
    change traceFinsumPairing
        (conjFn (PairedFunctionSpace.transposeMap (extend T₀) (conjFn g))).1 f.1 =
      traceFinsumPairing g.1 (extend T₀ f).1
    rw [hb, ha', hc, star_star]
  have hg := congrFun hR (conjFn g)
  simp only [conjFn_conjFn] at hg
  exact hg.symm
theorem transposeMap_extend_ofLie_mem (g : LieFn ι') :
    (PairedFunctionSpace.transposeMap (extend T₀) (ofLie g)).1 ∈
      (pairedFunctions ι).realSubmodule := by
  have hg := transposeMap_extend_conjFn T₀ H hT (ofLie g)
  rw [conjFn_ofLie] at hg
  exact mem_realSubmodule_iff.2 fun i => mem_hermitianTraceless_iff.2
    ⟨congrFun (congrArg Subtype.val hg) i, mem_traceless_iff.1 (ComplexLieFn.apply_mem _ i)⟩
def restrictedTranspose : LieFn ι' →ₗ[ℝ] LieFn ι where
  toFun g := ⟨(PairedFunctionSpace.transposeMap (extend T₀) (ofLie g)).1,
    transposeMap_extend_ofLie_mem T₀ H hT g⟩
  map_add' g g' := by
    refine Subtype.ext ?_
    have hs : ofLie (g + g') = ofLie g + ofLie g' := Subtype.ext rfl
    have ha : PairedFunctionSpace.transposeMap (extend T₀) (ofLie (g + g')) =
        PairedFunctionSpace.transposeMap (extend T₀) (ofLie g) +
          PairedFunctionSpace.transposeMap (extend T₀) (ofLie g') := by
      rw [hs, map_add]
    have hb := congrArg (Subtype.val (p := (· ∈ (pairedFunctions ι).complexSubmodule))) ha
    exact hb
  map_smul' r g := by
    refine Subtype.ext ?_
    have hs : ofLie (r • g) = (r : ℂ) • ofLie g := by
      refine Subtype.ext (funext fun i => ?_)
      change r • g.1 i = (r : ℂ) • g.1 i
      ext a b
      simp
    have ha : PairedFunctionSpace.transposeMap (extend T₀) (ofLie (r • g)) =
        (r : ℂ) • PairedFunctionSpace.transposeMap (extend T₀) (ofLie g) := by
      rw [hs, map_smul]
    refine (congrArg Subtype.val ha).trans (funext fun i => ?_)
    change (r : ℂ) • (PairedFunctionSpace.transposeMap (extend T₀) (ofLie g)).1 i =
      r • (PairedFunctionSpace.transposeMap (extend T₀) (ofLie g)).1 i
    ext a b
    simp
end Transpose
theorem traceFinsumPairing_single [DecidableEq ι] (a : ι → ComplexMatrix2) (σ : ι)
    (Y : ComplexMatrix2) :
    traceFinsumPairing a (Pi.single σ Y) = ComplexMatrix2.halfTrace (a σ * Y) := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.traceFinsumPairing_single <;> assumption
theorem eq_of_traceFinsumPairing_eq {a b : LieFn ι}
    (h : ∀ f : LieFn ι, (pairedFunctions ι).IsFinitelySupported f.1 →
      traceFinsumPairing a.1 f.1 = traceFinsumPairing b.1 f.1) : a = b := by
  classical
  refine Subtype.ext (funext fun (σ : ι) => ?_)
  obtain ⟨D, hDdef⟩ : ∃ D, D = a.1 σ - b.1 σ := ⟨_, rfl⟩
  have hD : D ∈ ComplexMatrix2.hermitianTraceless :=
    hDdef ▸ ComplexMatrix2.hermitianTraceless.sub_mem (LieFn.apply_mem a σ) (LieFn.apply_mem b σ)
  have hm : (Pi.single σ D : ι → ComplexMatrix2) ∈ (pairedFunctions ι).realSubmodule := by
    refine mem_realSubmodule_iff.2 fun i => ?_
    by_cases hi : i = σ
    · subst hi
      simpa using hD
    · rw [Pi.single_eq_of_ne hi]
      exact ComplexMatrix2.hermitianTraceless.zero_mem
  have hf : (pairedFunctions ι).IsFinitelySupported (Pi.single σ D : ι → ComplexMatrix2) := by
    refine Set.Finite.subset (Set.finite_singleton σ) fun i hi => ?_
    by_contra hn
    exact Function.mem_support.1 hi (Pi.single_eq_of_ne hn _)
  have he : traceFinsumPairing a.1 (Pi.single σ D : ι → ComplexMatrix2) =
      traceFinsumPairing b.1 (Pi.single σ D : ι → ComplexMatrix2) :=
    h ⟨_, hm⟩ hf
  have he₁ : ComplexMatrix2.halfTrace (a.1 σ * D) = ComplexMatrix2.halfTrace (b.1 σ * D) :=
    (traceFinsumPairing_single (a.1 : ι → ComplexMatrix2) σ D).symm.trans
      (he.trans (traceFinsumPairing_single (b.1 : ι → ComplexMatrix2) σ D))
  have he₂ : Matrix.trace (a.1 σ * D) = Matrix.trace (b.1 σ * D) :=
    mul_left_cancel₀ (by norm_num) he₁
  have hz : D = 0 := by
    refine eq_zero_of_fullTrace_mul_self (mem_hermitianTraceless_iff.1 hD).1 ?_
    change Matrix.trace (D * D) = 0
    have hs : D * D = a.1 σ * D - b.1 σ * D := by rw [← sub_mul, ← hDdef]
    rw [hs, Matrix.trace_sub, he₂, sub_self]
  exact sub_eq_zero.1 (hDdef ▸ hz)
theorem realTransposeProperties_of (T₀ : LieFn ι →ₗ[ℝ] LieFn ι')
    (H : HasUniqueTranspose (pairedFunctions ι) (pairedFunctions ι'))
    (hT : PairedFunctionSpace.PreservesRealFiniteSupport T₀) :
    PairedFunctionSpace.RealTransposeProperties T₀ := by
  have hc := complexification_eq_extend T₀
  have s₁ := (transposeMap_spec H (extend T₀) (preservesFiniteSupport_extend T₀ hT)).1
  have hIs : PairedFunctionSpace.IsRealTransposeMap T₀ (restrictedTranspose T₀ H hT) := by
    intro g h hs
    rw [hc]
    have he : h = ofLie g := Subtype.ext hs
    subst he
    rfl
  have hE : PairedFunctionSpace.IsRealTransposeMap T₀ (PairedFunctionSpace.realTransposeMap T₀) :=
    Classical.epsilon_spec ⟨_, hIs⟩
  have hEq : PairedFunctionSpace.realTransposeMap T₀ = restrictedTranspose T₀ H hT :=
    LinearMap.ext fun g => Subtype.ext
      ((hE g (ofLie g) rfl).trans (hIs g (ofLie g) rfl).symm)
  have hP : ∀ (g : LieFn ι') (f : LieFn ι), (pairedFunctions ι).IsFinitelySupported f →
      (pairedFunctions ι).pair (PairedFunctionSpace.realTransposeMap T₀ g) f =
        (pairedFunctions ι').pair g (T₀ f) := by
    intro g f hf
    rw [hEq]
    have ha := s₁ (ofLie g) (ofLie f) hf
    have he : traceFinsumPairing (PairedFunctionSpace.transposeMap (extend T₀) (ofLie g)).1 f.1 =
        traceFinsumPairing g.1 (extend T₀ (ofLie f)).1 := ha
    rw [extend_ofLie_val] at he
    exact he
  unfold PairedFunctionSpace.RealTransposeProperties
  refine ⟨?_, ?_, ?_, hE, hP, ?_⟩
  · rw [hc]
    exact isComplexification_extend T₀
  · rw [hc]
    exact preservesFiniteSupport_extend T₀ hT
  · intro g
    refine ⟨ofLie g, rfl, ?_⟩
    rw [hc]
    exact transposeMap_extend_ofLie_mem T₀ H hT g
  · intro R hR
    funext g
    exact eq_of_traceFinsumPairing_eq fun f hf => (hR g f hf).trans (hP g f hf).symm
theorem admitsRealTransposes_of
    (H : HasUniqueTranspose (pairedFunctions ι) (pairedFunctions ι')) :
    PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions ι) (pairedFunctions ι') :=
  ⟨hasRealDecomposition ι, fun T₀ hT => realTransposeProperties_of T₀ H hT⟩
theorem realTransposesExist_of_claim (h : LeftChartFields.Claim) : RealTransposesExist := by
  intro L k hL
  have ha := h.2.2 L k 0 hL (Nat.zero_le k)
  exact ⟨fun n hn c c' => admitsRealTransposes_of ((ha.1 n hn).2.2 c c').1,
    fun c c' => admitsRealTransposes_of (ha.2.2 c c')⟩
end YangMills.Construction.Tower.RealTransposeConstruction
end
