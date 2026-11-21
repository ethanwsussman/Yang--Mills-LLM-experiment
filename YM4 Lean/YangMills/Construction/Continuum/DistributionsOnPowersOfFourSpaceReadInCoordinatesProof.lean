import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import Mathlib
set_option autoImplicit false
open TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction
open ReflectionSpaces PeriodicSpace PeriodicSpace.Kind
namespace CoordinateRepresentation
variable {p : ℕ+}
section EvaluationMaps
variable (hD : TupleMetric.QuotientDistanceAndLifts) (D : Params)
include hD
theorem proj_bijective :
    Function.Bijective (Tuple.proj D euclidean (p := p)) := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.proj_bijective <;> assumption
theorem isCompactT_iff (S : Set (euclidean.Tuple D p)) :
    Tuple.IsCompactT D euclidean S ↔
      IsCompact (Tuple.proj D euclidean ⁻¹' S) := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.isCompactT_iff <;> assumption
theorem tsupport_comp_proj (F : euclidean.Tuple D p → ℂ) :
    tsupport (F ∘ Tuple.proj D euclidean) =
      Tuple.proj D euclidean ⁻¹' Tuple.supportT D euclidean F := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.tsupport_comp_proj <;> assumption
theorem mem_testFns_iff (hC : ContPartialsIffContDiff)
    {Ω : Set (euclidean.Tuple D p)} {W : Opens (Euclidean.Coord (4 * (p : ℕ)))}
    (hW : IsCoordinateImageOfSet Ω W) (F : euclidean.Tuple D p → ℂ) :
    F ∈ Tuple.testFns D euclidean Ω ↔
      F ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.mem_testFns_iff <;> assumption
end EvaluationMaps
section Norms
variable {n : ℕ}
theorem cNorm_nonneg (ν : ℕ) (G : Euclidean.Coord n → ℂ) :
    0 ≤ Euclidean.cNorm ν G :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
end Norms
theorem tuple_cNorm_le (hD : TupleMetric.QuotientDistanceAndLifts)
    (hDer : TupleDerivatives.Statement) (D : Params)
    {F : euclidean.Tuple D p → ℂ} (hF : Tuple.IsSmoothT D euclidean F)
    (hG : ContDiff ℝ ∞ (F ∘ Tuple.proj D euclidean))
    (hc : HasCompactSupport (F ∘ Tuple.proj D euclidean)) (ν : ℕ) :
    Tuple.cNorm D euclidean ν F ≤
      ENNReal.ofReal (Euclidean.cNorm ν (F ∘ Tuple.proj D euclidean)) := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.tupleCNorm_le_ofReal_cNorm <;> assumption
theorem distributionsReadInCoordinates_holds (hD : TupleMetric.QuotientDistanceAndLifts)
    (hDer : TupleDerivatives.Statement)
    (hC : ContPartialsIffContDiff) : CoordinateRepresentation.DistributionsReadInCoordinates := by
  intro D p Ω W _ hW
  have hb := proj_bijective (p := p) hD D
  have hm := mem_testFns_iff hD D hC hW
  let e := Equiv.ofBijective _ hb
  have hcomp : ∀ G : Euclidean.Coord (4 * (p : ℕ)) → ℂ,
      (G ∘ e.symm) ∘ Tuple.proj D euclidean = G := fun G =>
    funext fun x => congrArg G (e.symm_apply_apply x)
  have hback : ∀ G ∈ Euclidean.testFunctionSpace W,
      G ∘ e.symm ∈ Tuple.testFns D euclidean Ω := fun G hG =>
    (hm _).2 (by rw [hcomp]; exact hG)
  refine ⟨fun F hF => (hm F).1 hF, fun G hG => ⟨G ∘ e.symm, hback G hG, hcomp G⟩, fun T hT => ?_⟩
  let Φ : Euclidean.testFunctionSpace W → Tuple.testFns D euclidean Ω :=
    fun G => ⟨G.1 ∘ e.symm, hback _ G.2⟩
  have hΦ : ∀ (F : Tuple.testFns D euclidean Ω) (G : Euclidean.testFunctionSpace W),
      (G : Euclidean.Coord (4 * (p : ℕ)) → ℂ) = F.1 ∘ Tuple.proj D euclidean →
        Φ G = F := by
    intro F G h
    refine Subtype.ext (funext fun y => ?_)
    show G.1 (e.symm y) = F.1 y
    rw [h]
    exact congrArg F.1 (e.apply_symm_apply y)
  let L : Module.Dual ℂ (Euclidean.testFunctionSpace W) :=
    { toFun := fun G => T (Φ G)
      map_add' := fun G G' => hT.1.1 _ _ _ rfl
      map_smul' := fun c G => hT.1.2 c _ _ rfl }
  have hbound : ∀ K : Set (Euclidean.Coord (4 * (p : ℕ))), IsCompact K →
      K ⊆ W → ∃ ν : ℕ, Euclidean.HasOrderBound L K ν := by
    intro K hK hKW
    have hKc : Tuple.IsCompactT D euclidean (Tuple.proj D euclidean '' K) :=
      (isCompactT_iff hD D _).2 (by rw [Set.preimage_image_eq _ hb.1]; exact hK)
    have hKΩ : Tuple.proj D euclidean '' K ⊆ Ω := by
      rintro _ ⟨x, hx, rfl⟩
      have hxW : x ∈ (W : Set (Euclidean.Coord (4 * (p : ℕ)))) := hKW hx
      rw [show (W : Set (Euclidean.Coord (4 * (p : ℕ)))) = _ from hW] at hxW
      exact hxW
    obtain ⟨ν, C, hCν⟩ := hT.2 _ hKc hKΩ
    refine ⟨ν, C, C.2, fun G hG => ?_⟩
    have hG1 : (Φ G).1 ∘ Tuple.proj D euclidean = G.1 := hcomp G.1
    have hsupp : Tuple.supportT D euclidean (Φ G).1 ⊆
        Tuple.proj D euclidean '' K := by
      intro y hy
      obtain ⟨x, rfl⟩ := hb.2 y
      refine ⟨x, hG ?_, rfl⟩
      show x ∈ tsupport G.1
      rw [← hG1, tsupport_comp_proj hD]
      exact hy
    have h1 := hCν (Φ G) hsupp
    have hF := (Φ G).2
    have hG' := (hm _).1 hF
    have h2 := tuple_cNorm_le hD hDer D hF.1 hG'.1 hG'.2.1 ν
    rw [hG1] at h2
    have h3 : ENNReal.ofReal ‖T (Φ G)‖ ≤
        ENNReal.ofReal ((C : ℝ) * Euclidean.cNorm ν G.1) := by
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      exact h1.trans (mul_le_mul' le_rfl h2)
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg C.coe_nonneg (cNorm_nonneg ν _))).1 h3
  refine ⟨⟨L, hbound⟩, ⟨hW, fun F G h => congrArg T (hΦ F G h)⟩, ?_⟩
  rintro ⟨f, hf⟩ ⟨-, h'⟩
  have hfL : f = L := LinearMap.ext fun G => h' (Φ G) G (hcomp G.1).symm
  subst hfL
  rfl
end CoordinateRepresentation
end YangMills.Construction
