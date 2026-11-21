import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace EuclideanBalls
def opNormEuclid {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  sSup ((fun x => Euclidean.euclidNorm (A.mulVec x)) ''
    {x | Euclidean.euclidNorm x ≤ 1})
end EuclideanBalls
namespace EuclideanFunctionals
open ReflectionPositivity.AxisMirror RealPlane
theorem mem_C1c_iff_mem_compactC1 {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ f ∈ EuclideanBalls.compactC1 4 𝕜 := by
  have hd : ∀ x y : Fin 4 → ℝ, Ambient.metric defaultMirrorData Ambient.euclidean x y =
      TorusMetric.euclidNormVec (x - y) := fun _ _ => rfl
  have hs : supp f = tsupport f :=
    SeparatedTuplesR4.closureWrt_euclid_eq_closure hd _
  change (ContDiff ℝ 1 f ∧ MetricNotions.IsCompactWrt _ (supp f)) ↔
    ContDiff ℝ 1 f ∧ HasCompactSupport f
  rw [SeparatedTuplesR4.isCompactWrt_euclid_iff hd, hs]
  rfl
def disjointComplexTuples (n : ℕ) : Set (Fin n → R4 → ℂ) :=
  {h | (∀ l, h l ∈ C1c ℂ) ∧
    Pairwise fun k l => Disjoint (supp (h k)) (supp (h l))}
theorem mem_disjointComplexTuples_iff {n : ℕ} (hn : 1 ≤ n) (h : Fin n → R4 → ℂ) :
    h ∈ disjointComplexTuples n ↔ ComplexComponents h :=
  ⟨fun hh => ⟨hn, hh.1, hh.2⟩, fun hh => ⟨hh.mem, hh.disjoint⟩⟩
theorem complexTuple_of_length_zero (h : Fin 0 → R4 → ℂ) :
    complexTuple h = toFree [] := by
  simp [complexTuple]
def complexify (X : FnList) : Fin X.length → R4 → ℂ :=
  fun l x => (X.get l x : ℂ)
theorem supp_eq_of_ne_zero_iff {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜'] {f : R4 → 𝕜}
    {g : R4 → 𝕜'} (h : ∀ x, f x ≠ 0 ↔ g x ≠ 0) : supp f = supp g := by
  have e : {x : R4 | f x ≠ 0} = {x : R4 | g x ≠ 0} := Set.ext h
  exact congrArg (MetricNotions.closureWrt (Ambient.metric defaultMirrorData Ambient.euclidean)) e
theorem supp_ofReal (f : R4 → ℝ) : supp (fun x => (f x : ℂ)) = supp f := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.supp_ofReal <;> assumption
theorem ofReal_mem_C1c {f : R4 → ℝ} (hf : f ∈ C1c ℝ) :
    (fun x => (f x : ℂ)) ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.ofReal_mem_C1c <;> assumption
theorem complexify_mem {X : FnList} (hX : X ∈ sepAll) :
    complexify X ∈ disjointComplexTuples X.length := by
  have hs := isSeparatedList_of_mem_sepAll hX
  refine ⟨fun l => ofReal_mem_C1c (hs.1 _ (List.get_mem X l)), ?_⟩
  intro k l hkl
  have e : ∀ i, supp (complexify X i) = supp (X.get i) := fun i => supp_ofReal _
  show Disjoint (supp (complexify X k)) (supp (complexify X l))
  rw [e, e]
  rcases lt_or_gt_of_ne hkl with h | h
  · exact List.pairwise_iff_get.1 hs.2 k l h
  · exact (List.pairwise_iff_get.1 hs.2 l k h).symm
theorem complexTuple_complexify (X : FnList) :
    complexTuple (complexify X) = toFree X := by
  have hreal : ∀ l, IsRealValued (complexify X l) := fun l x => by
    simp [complexify]
  rw [complexTuple, if_pos hreal]
  congr 1
  apply List.ext_get (by simp)
  intro i h₁ h₂
  funext x
  simp [complexify]
theorem ofFn_re_mem_sepN {n : ℕ} {h : Fin n → R4 → ℂ} (hh : h ∈ disjointComplexTuples n)
    (hreal : ∀ l, IsRealValued (h l)) :
    (List.ofFn fun l x => (h l x).re) ∈ sepN n := by
  have hsupp : ∀ l, supp (fun x => (h l x).re) = supp (h l) := fun l =>
    supp_eq_of_ne_zero_iff fun x =>
      ⟨fun hne h0 => hne (by simp [h0]), fun hne h0 => hne (Complex.ext h0 (hreal l x))⟩
  have hlen : (List.ofFn fun l (x : R4) => (h l x).re).length = n := List.length_ofFn
  refine ⟨hlen, ?_, ?_⟩
  · intro f hf
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact ⟨show ContDiff ℝ 1 (fun x => (h l x).re) from
        Complex.reCLM.contDiff.comp (show ContDiff ℝ 1 (h l) from (hh.1 l).1),
      (congrArg (MetricNotions.IsCompactWrt (Ambient.metric defaultMirrorData Ambient.euclidean))
        (hsupp l)).mpr (hh.1 l).2⟩
  · show List.Pairwise (fun f g : R4 → ℝ => Disjoint (supp f) (supp g)) _
    rw [List.pairwise_ofFn]
    intro k l hkl
    show Disjoint (supp fun x => (h k x).re) (supp fun x => (h l x).re)
    rw [hsupp, hsupp]
    exact hh.2 hkl.ne
def labelConstants (C : RealPlane.realLabels → ℝ) (φ : RealPlane → ℝ) : ℝ :=
  open Classical in if h : φ ∈ RealPlane.realLabels then C ⟨φ, h⟩ else 0
structure ProductPlaneData (m : SharpScale) (S : ConnFamily) where
  fnl : EuclidFunctionalWithRecon m S
  coneCond : fnl.ConeCondition
  exponent : ℝ
  labelBound : RealPlane.realLabels → ℝ
  fraction : ℝ
  productBound : ProductBoundHolds fnl exponent (labelConstants labelBound) fraction
namespace ProductPlaneData
variable {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S)
theorem exponent_pos : 0 < d.exponent := d.productBound.pos_exponent
theorem fraction_mem : d.fraction ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
  ⟨d.productBound.pos_fraction, d.productBound.fraction_lt_quarter⟩
end ProductPlaneData
end EuclideanFunctionals
end YangMills.Construction
end
