import YangMills.Construction.LimitTheorem.RotationsAndTheConeOnOneCompletionProof
import YangMills.Construction.TotalDensitiesGiveASystem.RotationsOfSpaceActOnACompletion
import Mathlib
set_option autoImplicit false
open Filter Matrix MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.TotalDensities.RotationsActOnCompletion
open LimitTheorem SystemsWithFiveBounds
open SeparatedTuples ReflectionPositivity.TupleForm
  SpectralTheory OrthogonalAction Orthogonal TestFunctions
open Continuum.RotationModulus
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass IsTimeShiftFamily
  posTupleVec timeShift timeBasisVec vacuum)
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
section Classes
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
theorem spanClass_coe (F : PositiveSpan) :
    spanClass σ h F.1 = posClass σ h F := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanClass_val <;> assumption
theorem spanClass_of_mem {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    spanClass σ h G = posClass σ h ⟨G, hG⟩ := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanClass_of_mem <;> assumption
variable (hC : HilbertSpaceFacts.CompletionProperties)
  (hId : HilbertSpaceFacts.DenseSubsetIdentities)
include hC in
theorem inner_posClass (F F' : PositiveSpan) :
    ⟪posClass σ h F, posClass σ h F'⟫_ℂ = reflectionForm σ F F' :=
  (hC _ (reflectionForm σ) h).2.1 F F'
include hC in
theorem dense_range_posClass : Dense (Set.range (posClass σ h)) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.dense_range_posClass <;> assumption
include hC hId in
theorem clm_ext_posClass {A B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hAB : ∀ F, A (posClass σ h F) = B (posClass σ h F)) : A = B := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.ext_on_posClass <;> assumption
end Classes
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem spanExtension_pushSpan {σ : TupleFunctional} {r : AmbientSpace → AmbientSpace}
    (hI : σ.IsInvariant r) (G : FormalSpan) :
    σ.spanExtension (pushSpan r G) = σ.spanExtension G := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanExtension_pushSpan <;> assumption
theorem pushSpan_mem_spanIn {r : AmbientSpace → AmbientSpace}
    (h : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, push r X ∈ supportedIn TimeAxis.upperHalfSpace)
    {C : FormalSpan} (hC : C ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan r C ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p30829 <;> assumption
def rotationSpanMap (hRules : Laws.Statement) (R : orthogonalGroupThree) :
    PositiveSpan →ₗ[ℂ] PositiveSpan :=
  (pushSpan (matMap (embedOrthogonal R))).restrict fun _ hG => (hRules.2.2.1 R).2.2.1.mapsTo hG
theorem rotationSpanMap_coe (hRules : Laws.Statement) (R : orthogonalGroupThree)
    (F : PositiveSpan) :
    (rotationSpanMap hRules R F).1 = pushSpan (matMap (embedOrthogonal R)) F.1 := rfl
theorem reflectionForm_rotationSpanMap (hRules : Laws.Statement) {σ : TupleFunctional}
    (R : orthogonalGroupThree) (hI : σ.IsInvariant (matMap (embedOrthogonal R)))
    (F F' : PositiveSpan) :
    reflectionForm σ (rotationSpanMap hRules R F) (rotationSpanMap hRules R F') =
      reflectionForm σ F F' := by
  obtain ⟨-, -, -, -, -, hLast⟩ := hRules.2.2.1 R
  have e := (hLast F.1 F.2 F'.1 F'.2).1
  unfold reflectionForm reflectConj
  rw [rotationSpanMap_coe, rotationSpanMap_coe, e, spanExtension_pushSpan hI]
theorem pushSpan_rotation_mul (hRules : Laws.Statement) (R R' : orthogonalGroupThree)
    (G : FormalSpan) :
    pushSpan (matMap (embedOrthogonal (R * R'))) G =
      pushSpan (matMap (embedOrthogonal R)) (pushSpan (matMap (embedOrthogonal R')) G) := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.pushSpan_mul <;> assumption
section Operators
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
structure IsRotationLift (hRules : Laws.Statement)
    (U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop where
  apply_posClass : ∀ R F, U R (posClass σ h F) = posClass σ h (rotationSpanMap hRules R F)
  inner_apply : ∀ R φ ψ, ⟪U R φ, U R ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ
variable (hC : HilbertSpaceFacts.CompletionProperties)
  (hId : HilbertSpaceFacts.DenseSubsetIdentities)
include hC hId in
theorem exists_rotationLift (hO : HilbertSpaceFacts.CompletionOperatorExtension)
    (hRules : Laws.Statement)
    (hI : ∀ R : orthogonalGroupThree, σ.IsInvariant (matMap (embedOrthogonal R))) :
    ∃ U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      IsRotationLift hRules U := by
  have hex : ∀ R : orthogonalGroupThree, ∃ B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F, B (posClass σ h F) = posClass σ h (rotationSpanMap hRules R F)) ∧
        ∀ φ ψ, ⟪B φ, B ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := fun R => by
    obtain ⟨-, B, hB, -, -⟩ := hO _ (reflectionForm σ) h 1 (rotationSpanMap hRules R)
      zero_le_one fun F => by
      rw [one_mul]
      exact le_of_eq (congrArg (fun z : ℂ => Real.sqrt z.re)
        (reflectionForm_rotationSpanMap hRules R (hI R) F F))
    refine ⟨B, hB, fun φ ψ => ?_⟩
    exact (hId _ _ (dense_range_posClass hC)).1 B B 1 1 (by
      rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
      rw [hB, hB, inner_posClass hC, reflectionForm_rotationSpanMap hRules R (hI R)]
      exact (inner_posClass hC F F').symm) φ ψ
  choose U hU using hex
  exact ⟨U, ⟨fun R => (hU R).1, fun R => (hU R).2⟩⟩
variable {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem IsRotationLift.norm_map (hU : IsRotationLift hRules U) (R : orthogonalGroupThree)
    (ψ : PhysicalSpace σ h) : ‖U R ψ‖ = ‖ψ‖ := by
  have hn : ‖U R ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ _ _ _ _ ψ, hU.inner_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hn
include hC hId in
theorem IsRotationLift.comp_eq_mul (hU : IsRotationLift hRules U) (R R' : orthogonalGroupThree) :
    U R ∘L U R' = U (R * R') :=
  clm_ext_posClass hC hId fun F => by
    show U R (U R' (posClass σ h F)) = _
    rw [hU.apply_posClass, hU.apply_posClass, hU.apply_posClass]
    exact congrArg _ (Subtype.ext (pushSpan_rotation_mul hRules R R' F.1).symm)
include hC hId in
theorem IsRotationLift.apply_one (hU : IsRotationLift hRules U) (ψ : PhysicalSpace σ h) :
    U 1 ψ = ψ := by
  have h₁ : U 1 (U 1 ψ) = U 1 ψ := by
    have := congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T ψ)
      (hU.comp_eq_mul hC hId 1 1)
    simpa using this
  have h₂ : U 1 (U 1 ψ - ψ) = 0 := by rw [map_sub, h₁, sub_self]
  have h₃ := hU.norm_map 1 (U 1 ψ - ψ)
  rw [h₂, norm_zero] at h₃
  exact sub_eq_zero.1 (norm_eq_zero.1 h₃.symm)
include hC hId in
theorem IsRotationLift.surjective (hU : IsRotationLift hRules U) (R : orthogonalGroupThree) :
    Function.Surjective (U R) := fun ψ => by
  refine ⟨U R⁻¹ ψ, ?_⟩
  have := congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T ψ)
    (hU.comp_eq_mul hC hId R R⁻¹)
  simp only [ContinuousLinearMap.comp_apply, mul_inv_cancel] at this
  rw [this, hU.apply_one hC hId]
include hC hId in
def IsRotationLift.toUnitary (hU : IsRotationLift hRules U) (R : orthogonalGroupThree) :
    PhysicalSpace σ h ≃ₗᵢ[ℂ] PhysicalSpace σ h :=
  LinearIsometryEquiv.ofSurjective
    ⟨(U R : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h), hU.norm_map R⟩ (hU.surjective hC hId R)
theorem IsRotationLift.apply_vacuum (hU : IsRotationLift hRules U) (R : orthogonalGroupThree) :
    U R (vacuum σ h) = vacuum σ h := by
  unfold vacuum
  rw [hU.apply_posClass]
  exact congrArg _ (Subtype.ext (hRules.2.2.1 R).2.2.2.2.1)
end Operators
theorem tendsto_matrixOperatorNorm_sub_one :
    Tendsto (fun R : orthogonalGroupThree => matrixOperatorNorm (R.1 - 1))
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.tendsto_matrixOperatorNorm_sub_one <;> assumption
theorem tendsto_sharpNormR4_rotate (hRules : Laws.Statement)
    (hMod : SharpNormRotationModulus) {M : ℝ}
    (hM : 1 ≤ M) {f : RealValued} (hf : IsC1c f) {ρ : ℝ} (hρ : 0 < ρ)
    (hb : tsupport f ⊆ closedBallR4 0 ρ) :
    Tendsto (fun R : orthogonalGroupThree => sharpNormR4 M (orthogonalAct (embedOrthogonal R) f - f))
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.tendsto_sharpNormR4_rotate <;> assumption
theorem reflectionForm_posTupleVec (σ : TupleFunctional)
    (X Y : supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ (posTupleVec X) (posTupleVec Y) =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by apply _root_.YangMills.SharedProofs.p11521 <;> assumption
theorem tsupport_subset_closedBall (X : SepTuple) (l : Fin X.1.length) :
    tsupport (X.1.get l) ⊆ closedBallR4 0 (maxSupportRadius X) := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.tsupport_get_subset <;> assumption
section Strong
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
def IsContinuousAtOne (U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h)
    (ψ : PhysicalSpace σ h) : Prop :=
  Tendsto (fun R : orthogonalGroupThree => ‖U R ψ - ψ‖) (@nhds _ (operatorNormTopology 3) 1) (𝓝 0)
theorem posClass_eq_zero_of_zero_mem (hC : HilbertSpaceFacts.CompletionProperties)
    (hRules : Laws.Statement) (hm : σ.IsEntrywiseLinear) (X : supportedIn TimeAxis.upperHalfSpace)
    (h0 : (0 : RealValued) ∈ X.1.1) :
    posClass σ h (posTupleVec X) = 0 := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.posClass_eq_zero_of_zero_component <;> assumption
theorem norm_apply_sub_sq (hC : HilbertSpaceFacts.CompletionProperties)
    (hU : IsRotationLift hRules U) (R : orthogonalGroupThree)
    (X : supportedIn TimeAxis.upperHalfSpace)
    (hR : push (matMap (embedOrthogonal R)) X.1 ∈ supportedIn TimeAxis.upperHalfSpace) :
    ‖U R (posClass σ h (posTupleVec X)) - posClass σ h (posTupleVec X)‖ ^ 2 =
      2 * (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) -
        σ (SepTuple.juxt (push TimeAxis.timeReflection X.1)
          (push (matMap (embedOrthogonal R)) X.1))) := by
  have hrot : U R (posClass σ h (posTupleVec X)) = posClass σ h (posTupleVec ⟨_, hR⟩) := by
    rw [hU.apply_posClass]
    exact congrArg _ (Subtype.ext (pushSpan_basisVec _ X.1))
  have hn := hU.norm_map R (posClass σ h (posTupleVec X))
  have h₁ : ‖posClass σ h (posTupleVec X)‖ ^ 2 =
      σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) := by
    rw [@norm_sq_eq_re_inner ℂ, inner_posClass hC, reflectionForm_posTupleVec]
    rfl
  have h₂ : RCLike.re ⟪posClass σ h (posTupleVec X), U R (posClass σ h (posTupleVec X))⟫_ℂ =
      σ (SepTuple.juxt (push TimeAxis.timeReflection X.1)
        (push (matMap (embedOrthogonal R)) X.1)) := by
    rw [hrot, inner_posClass hC, reflectionForm_posTupleVec]
    rfl
  rw [norm_sub_rev, @norm_sub_sq ℂ, hn, h₂, h₁]
  ring
theorem isContinuousAtOne_posTupleVec (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsRotationLift hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (X : supportedIn TimeAxis.upperHalfSpace) :
    IsContinuousAtOne U (posClass σ h (posTupleVec X)) := by
  unfold IsContinuousAtOne
  by_cases h0 : X.1.1 = []
  · have hE : X.1 = SepTuple.nil := Subtype.ext h0
    have : ∀ R : orthogonalGroupThree,
        ‖U R (posClass σ h (posTupleVec X)) - posClass σ h (posTupleVec X)‖ = 0 := by
      intro R
      have hX : posTupleVec X = posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩ :=
        Subtype.ext (congrArg basisVec hE)
      rw [hX]
      change ‖U R (vacuum σ h) - vacuum σ h‖ = 0
      rw [hU.apply_vacuum, sub_self, norm_zero]
    simp only [this]
    exact tendsto_const_nhds
  by_cases hz : (0 : RealValued) ∈ X.1.1
  · have : ∀ R : orthogonalGroupThree,
        ‖U R (posClass σ h (posTupleVec X)) - posClass σ h (posTupleVec X)‖ = 0 := by
      intro R
      rw [posClass_eq_zero_of_zero_mem hC hRules four.entrywiseLinear X hz, map_zero, sub_self,
        norm_zero]
    simp only [this]
    exact tendsto_const_nhds
  have hlen : 1 ≤ X.1.size := List.length_pos_iff.2 h0
  have hne : ∀ f ∈ X.1.1, f ≠ 0 := fun f hfX e => hz (e ▸ hfX)
  obtain ⟨hd, hρ, hT⟩ := hCont M σ B hM four X.1 X.2 hlen hne
  have hs : ∀ l : Fin X.1.1.length, Tendsto
      (fun R : orthogonalGroupThree =>
        sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.1.1.get l) - X.1.1.get l))
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := fun l =>
    tendsto_sharpNormR4_rotate hRules hMod hM (X.1.2.1 _ (List.get_mem _ _)) hρ
      (tsupport_subset_closedBall X.1 l)
  set b := B (2 * X.1.size) (minSupportDist X.1 / 2) (maxSupportRadius X.1 + minSupportDist X.1)
  have hrhs : Tendsto (fun R : orthogonalGroupThree => continuityBound M X.1 R b)
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := by
    have := (tendsto_finsetSum Finset.univ fun l _ =>
      (hs l).mul_const (∏ l' ∈ Finset.univ.erase l, sharpNormR4 M (X.1.1.get l'))).const_mul
        (2 * b * ∏ l, sharpNormR4 M (X.1.1.get l))
    simpa [continuityBound] using this
  have hev : ∀ᶠ R : orthogonalGroupThree in @nhds _ (operatorNormTopology 3) 1,
      matrixOperatorNorm (R.1 - 1) * maxSupportRadius X.1 ≤ minSupportDist X.1 / 4 := by
    have h₁ := tendsto_matrixOperatorNorm_sub_one.mul_const (maxSupportRadius X.1)
    rw [zero_mul] at h₁
    exact h₁.eventually_le_const (by positivity)
  have hsq := squeeze_zero' (Eventually.of_forall fun R : orthogonalGroupThree =>
      sq_nonneg ‖U R (posClass σ h (posTupleVec X)) - posClass σ h (posTupleVec X)‖)
    (hev.mono fun R hR => by
      obtain ⟨hR', -, hLe⟩ := hT R hR
      rw [norm_apply_sub_sq hC hU R X hR']
      exact hLe) hrhs
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
theorem isContinuousAtOne_posClass (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsRotationLift hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (F : PositiveSpan) :
    IsContinuousAtOne U (posClass σ h F) := by
  let S : Submodule ℂ (PhysicalSpace σ h) :=
    { carrier := {ψ | IsContinuousAtOne U ψ}
      add_mem' := by
        intro a b ha hb
        have h₁ := Tendsto.add ha hb
        rw [add_zero] at h₁
        refine squeeze_zero (fun _ => norm_nonneg _) (fun R => ?_) h₁
        rw [map_add, add_sub_add_comm]
        exact norm_add_le _ _
      zero_mem' := by
        change IsContinuousAtOne U 0
        unfold IsContinuousAtOne
        simp
      smul_mem' := by
        intro z a ha
        have h₁ := Tendsto.const_mul ‖z‖ ha
        rw [mul_zero] at h₁
        refine h₁.congr fun R => ?_
        rw [map_smul, ← smul_sub, norm_smul] }
  have hall : ∀ (C : FormalSpan) (hC' : C ∈ spanIn TimeAxis.upperHalfSpace),
      posClass σ h ⟨C, hC'⟩ ∈ S := by
    intro C hC'
    induction hC' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨X, rfl⟩ := hx
      exact isContinuousAtOne_posTupleVec hC hCont hMod hU hM four X
    | zero =>
      have : (⟨0, Submodule.zero_mem _⟩ : PositiveSpan) = 0 := rfl
      rw [this, map_zero]
      exact S.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, add_mem hx hy⟩ : PositiveSpan) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add]
      exact S.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, Submodule.smul_mem _ a hx⟩ : PositiveSpan) = a • ⟨x, hx⟩ := rfl
      rw [this, map_smul]
      exact S.smul_mem a ih
  exact hall F.1 F.2
theorem isContinuousAtOne (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsRotationLift hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (ψ : PhysicalSpace σ h) : IsContinuousAtOne U ψ := by
  unfold IsContinuousAtOne
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, hF, ⟨F, rfl⟩⟩ :=
    Metric.dense_iff.1 (dense_range_posClass (σ := σ) (h := h) hC) ψ (ε / 3) (by positivity)
  have hFn : ‖posClass σ h F - ψ‖ < ε / 3 := by
    rwa [Metric.mem_ball, dist_eq_norm] at hF
  have ht := (Metric.tendsto_nhds.1 (isContinuousAtOne_posClass hC hCont hMod hU hM four F))
    (ε / 3) (by positivity)
  refine ht.mono fun R hR => ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hR ⊢
  have e : U R ψ - ψ = U R (ψ - posClass σ h F) + (U R (posClass σ h F) - posClass σ h F) +
      (posClass σ h F - ψ) := by
    rw [map_sub]
    abel
  have h₁ : ‖U R (ψ - posClass σ h F)‖ < ε / 3 := by
    rw [hU.norm_map, norm_sub_rev]
    exact hFn
  rw [e]
  calc _ ≤ ‖U R (ψ - posClass σ h F)‖ + ‖U R (posClass σ h F) - posClass σ h F‖ +
        ‖posClass σ h F - ψ‖ := norm_add₃_le
    _ < ε := by linarith
theorem tendsto_inv_mul (R₀ : orthogonalGroupThree) :
    Tendsto (fun R : orthogonalGroupThree => R₀⁻¹ * R) (@nhds _ (operatorNormTopology 3) R₀)
      (@nhds _ (operatorNormTopology 3) 1) := by apply _root_.YangMills.Construction.LimitTheorem.RotationsAndCone.tendsto_inv_mul <;> assumption
theorem continuous_apply (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsRotationLift hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (ψ : PhysicalSpace σ h) :
    Continuous fun R : orthogonalGroupThree => U R ψ := by
  have key : @Continuous _ _ (operatorNormTopology 3) _ fun R : orthogonalGroupThree => U R ψ := by
    refine (@continuous_iff_continuousAt _ _ (operatorNormTopology 3) _ _).2 fun R₀ => ?_
    change Tendsto _ (@nhds _ (operatorNormTopology 3) R₀) (𝓝 _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (Tendsto.comp (isContinuousAtOne hC hCont hMod hU hM four ψ)
      (tendsto_inv_mul R₀)).congr fun R => ?_
    have hg : U R = (U R₀).comp (U (R₀⁻¹ * R)) := by
      rw [hU.comp_eq_mul hC hId, mul_inv_cancel_left]
    change ‖U (R₀⁻¹ * R) ψ - ψ‖ = _
    rw [hg, ContinuousLinearMap.comp_apply, ← map_sub, hU.norm_map]
  rw [operatorNormTopology_eq 3] at key
  exact key
end Strong
section Relations
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem IsRotationLift.mul_eq_of_intertwine (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities) (hU : IsRotationLift hRules U)
    (R : orthogonalGroupThree) {T T' : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    {S S' : FormalSpan →ₗ[ℂ] FormalSpan}
    (hmS : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, S G ∈ spanIn TimeAxis.upperHalfSpace)
    (hT : ∀ F : PositiveSpan, T (posClass σ h F) = spanClass σ h (S F.1))
    (hT' : ∀ F : PositiveSpan, T' (posClass σ h F) = spanClass σ h (S' F.1))
    (hrel : ∀ G ∈ spanIn TimeAxis.upperHalfSpace,
      pushSpan (matMap (embedOrthogonal R)) (S G) = S' (pushSpan (matMap (embedOrthogonal R)) G)) :
    U R * T = T' * U R :=
  clm_ext_posClass hC hId fun F => by
    show U R (T (posClass σ h F)) = T' (U R (posClass σ h F))
    rw [hT, spanClass_of_mem (hmS F.1 F.2), hU.apply_posClass, hU.apply_posClass, hT']
    exact (spanClass_coe _).symm.trans (congrArg (spanClass σ h) (hrel F.1 F.2))
theorem IsRotationLift.commute_timeShift (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities) (hU : IsRotationLift hRules U)
    (hT : IsTimeShiftFamily σ h (timeShift σ h)) (R : orthogonalGroupThree) (t : ℝ≥0) :
    Commute (U R) (timeShift σ h t) := by
  obtain ⟨-, -, -, -, -, hLast⟩ := hRules.2.2.1 R
  exact hU.mul_eq_of_intertwine hC hId R
    (fun G hG => pushSpan_mem_spanIn (fun X hX => ((hRules.2.2.1 1).2.1 X hX).1 t t.2) hG)
    (hT t) (hT t) fun G hG => (hLast G hG G hG).2.1 t t.2
end Relations
theorem statement_holds (hHF : HilbertSpaceFacts.Facts) (hRules : Laws.Statement)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus) :
    TotalDensities.RotationsActOnCompletion.Statement := by
  obtain ⟨-, -, -, -, -, hC, -, hO, -, -, -, -, -, -, -, -, -, -, -, hId, -⟩ := hHF
  intro M σ B h hM four hrec h'
  obtain rfl : h' = h := rfl
  obtain ⟨U, hU⟩ := exists_rotationLift (h := h') hC hId hO hRules four.orthogonal_invariant
  obtain ⟨-, hT, -⟩ := hrec.2.1
  refine ⟨U, fun R F => ?_, ⟨fun R => ⟨hU.norm_map R, hU.surjective hC hId R⟩, hU.comp_eq_mul hC hId⟩,
    continuous_apply hC hId hCont hMod hU hM four, hU.apply_vacuum,
    fun R t => hU.commute_timeShift hC hId hT R t⟩
  have hm : rotationMap (embedOrthogonal R) = matMap (embedOrthogonal R) := funext fun x => by
    simp [rotationMap, ofOrthogonal, Motions.RigidMotion.toFun, matMap]
  rw [hm, hU.apply_posClass]
  exact (spanClass_coe _).symm
end YangMills.Construction.TotalDensities.RotationsActOnCompletion
end
