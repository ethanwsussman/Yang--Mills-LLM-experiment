import YangMills.Construction.Continuum.ModulusOfARotationInTheSharpNorm
import YangMills.Construction.LimitTheorem.MeasureOfTheTranslationsOnOneCompletionProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import Mathlib
set_option autoImplicit false
open Filter Matrix MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.LimitTheorem.RotationsAndCone
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.ReconstructionComplements
  SpectralTheory Orthogonal TestFunctions
open OrthogonalAction hiding spatialPart
open Continuum.RotationModulus
open HilbertSpaceBasics (IsPosSemidef ofBounded)
open ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass IsSpaceShiftFamily IsTimeShiftFamily
  posTupleVec spaceShift embedSpatial timeShift timeBasisVec vacuum)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open LimitConventions (spaceDot)
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
theorem spanExtension_pushSpan {σ : TupleFunctional} {r : AmbientSpace → AmbientSpace} (hI : σ.IsInvariant r)
    (G : FormalSpan) : σ.spanExtension (pushSpan r G) = σ.spanExtension G := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanExtension_pushSpan <;> assumption
theorem pushSpan_mem {r : AmbientSpace → AmbientSpace}
    (h : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, push r X ∈ supportedIn TimeAxis.upperHalfSpace)
    {C : FormalSpan} (hC : C ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan r C ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p30829 <;> assumption
def spatialRotationSpan (hRules : Laws.Statement) (R : orthogonalGroupThree) :
    PositiveSpan →ₗ[ℂ] PositiveSpan :=
  (pushSpan (matMap (embedOrthogonal R))).restrict fun _ hG => (hRules.2.2.1 R).2.2.1.mapsTo hG
theorem spatialRotationSpan_coe (hRules : Laws.Statement) (R : orthogonalGroupThree)
    (F : PositiveSpan) :
    (spatialRotationSpan hRules R F).1 = pushSpan (matMap (embedOrthogonal R)) F.1 := rfl
theorem reflectionForm_spatialRotation (hRules : Laws.Statement) {σ : TupleFunctional} (R : orthogonalGroupThree)
    (hI : σ.IsInvariant (matMap (embedOrthogonal R))) (F F' : PositiveSpan) :
    reflectionForm σ (spatialRotationSpan hRules R F) (spatialRotationSpan hRules R F') = reflectionForm σ F F' := by
  obtain ⟨-, -, -, -, -, hLast⟩ := hRules.2.2.1 R
  have e := (hLast F.1 F.2 F'.1 F'.2).1
  unfold reflectionForm reflectConj
  rw [spatialRotationSpan_coe, spatialRotationSpan_coe, e, spanExtension_pushSpan hI]
theorem pushSpan_mul (hRules : Laws.Statement) (R R' : orthogonalGroupThree) (G : FormalSpan) :
    pushSpan (matMap (embedOrthogonal (R * R'))) G =
      pushSpan (matMap (embedOrthogonal R)) (pushSpan (matMap (embedOrthogonal R')) G) := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    have e := (hRules.1 (embedOrthogonal R) (embedOrthogonal R')).2.2.2.1 X
    rw [h, map_smul, map_smul, map_smul, pushSpan_basisVec, pushSpan_basisVec,
      pushSpan_basisVec, e, (hRules.2.1 R R').2.2.2.2.1]
section Operators
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)}
structure IsOrthogonalRep (hRules : Laws.Statement) (U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop where
  apply_posClass : ∀ R F, U R (posClass σ h F) = posClass σ h (spatialRotationSpan hRules R F)
  inner_apply : ∀ R φ ψ, ⟪U R φ, U R ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ
variable (hC : HilbertSpaceFacts.CompletionProperties)
  (hId : HilbertSpaceFacts.DenseSubsetIdentities)
include hC hId in
theorem exists_orthogonalRep (hO : HilbertSpaceFacts.CompletionOperatorExtension) (hRules : Laws.Statement)
    (hI : ∀ R : orthogonalGroupThree, σ.IsInvariant (matMap (embedOrthogonal R))) :
    ∃ U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h, IsOrthogonalRep hRules U := by
  have hex : ∀ R : orthogonalGroupThree, ∃ B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F, B (posClass σ h F) = posClass σ h (spatialRotationSpan hRules R F)) ∧
        ∀ φ ψ, ⟪B φ, B ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := fun R => by
    obtain ⟨-, B, hB, -, -⟩ := hO _ (reflectionForm σ) h 1 (spatialRotationSpan hRules R) zero_le_one fun F => by
      rw [one_mul]
      exact le_of_eq (congrArg (fun z : ℂ => Real.sqrt z.re) (reflectionForm_spatialRotation hRules R (hI R) F F))
    refine ⟨B, hB, fun φ ψ => ?_⟩
    exact (hId _ _ (dense_range_posClass hC)).1 B B 1 1 (by
      rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
      rw [hB, hB, inner_posClass hC, reflectionForm_spatialRotation hRules R (hI R)]
      exact (inner_posClass hC F F').symm) φ ψ
  choose U hU using hex
  exact ⟨U, ⟨fun R => (hU R).1, fun R => (hU R).2⟩⟩
variable {hRules : Laws.Statement} {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem IsOrthogonalRep.norm_apply (hU : IsOrthogonalRep hRules U) (R : orthogonalGroupThree) (ψ : PhysicalSpace σ h) :
    ‖U R ψ‖ = ‖ψ‖ := by
  have hn : ‖U R ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ _ _ _ _ ψ, hU.inner_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hn
include hC hId in
theorem IsOrthogonalRep.comp_eq (hU : IsOrthogonalRep hRules U) (R R' : orthogonalGroupThree) :
    U R ∘L U R' = U (R * R') :=
  clm_ext_posClass hC hId fun F => by
    show U R (U R' (posClass σ h F)) = _
    rw [hU.apply_posClass, hU.apply_posClass, hU.apply_posClass]
    exact congrArg _ (Subtype.ext (pushSpan_mul hRules R R' F.1).symm)
include hC hId in
theorem IsOrthogonalRep.one_apply (hU : IsOrthogonalRep hRules U) (ψ : PhysicalSpace σ h) : U 1 ψ = ψ := by
  have h₁ : U 1 (U 1 ψ) = U 1 ψ := by
    have := congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T ψ) (hU.comp_eq hC hId 1 1)
    simpa using this
  have h₂ : U 1 (U 1 ψ - ψ) = 0 := by rw [map_sub, h₁, sub_self]
  have h₃ := hU.norm_apply 1 (U 1 ψ - ψ)
  rw [h₂, norm_zero] at h₃
  exact sub_eq_zero.1 (norm_eq_zero.1 h₃.symm)
include hC hId in
theorem IsOrthogonalRep.surjective (hU : IsOrthogonalRep hRules U) (R : orthogonalGroupThree) :
    Function.Surjective (U R) := fun ψ => by
  refine ⟨U R⁻¹ ψ, ?_⟩
  have := congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T ψ) (hU.comp_eq hC hId R R⁻¹)
  simp only [ContinuousLinearMap.comp_apply, mul_inv_cancel] at this
  rw [this, hU.one_apply hC hId]
include hC hId in
def IsOrthogonalRep.toUnitary (hU : IsOrthogonalRep hRules U) (R : orthogonalGroupThree) :
    PhysicalSpace σ h ≃ₗᵢ[ℂ] PhysicalSpace σ h :=
  LinearIsometryEquiv.ofSurjective ⟨(U R : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h), hU.norm_apply R⟩ (hU.surjective hC hId R)
theorem IsOrthogonalRep.apply_vacuum (hU : IsOrthogonalRep hRules U) (R : orthogonalGroupThree) :
    U R (vacuum σ h) = vacuum σ h := by
  unfold vacuum
  rw [hU.apply_posClass]
  exact congrArg _ (Subtype.ext (hRules.2.2.1 R).2.2.2.2.1)
end Operators
theorem tendsto_matrixOperatorNorm_sub_one :
    Tendsto (fun R : orthogonalGroupThree => matrixOperatorNorm (R.1 - 1)) (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := by
  have hc : @Continuous _ _ (operatorNormTopology 3) _
      (fun R : orthogonalGroupThree => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) R.1) :=
    continuous_induced_dom
  have h := tendsto_iff_norm_sub_tendsto_zero.1 (@Continuous.tendsto _ _ (operatorNormTopology 3) _ _ hc 1)
  refine h.congr fun R => ?_
  simp [matrixOperatorNorm, map_sub]
theorem sharpNormR4_nonneg (M : ℝ) (f : RealValued) : 0 ≤ sharpNormR4 M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem tendsto_sharpNormR4_rotate (hRules : Laws.Statement) (hMod : SharpNormRotationModulus) {M : ℝ}
    (hM : 1 ≤ M) {f : RealValued} (hf : IsC1c f) {ρ : ℝ} (hρ : 0 < ρ)
    (hb : tsupport f ⊆ closedBallR4 0 ρ) :
    Tendsto (fun R : orthogonalGroupThree => sharpNormR4 M (orthogonalAct (embedOrthogonal R) f - f))
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := by
  have hm := hMod M hM f hf ρ hρ hb
  have h₁ : Tendsto embedOrthogonal (@nhds _ (operatorNormTopology 3) 1)
      (comap (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1)) (𝓝 0)) := by
    rw [tendsto_comap_iff]
    refine tendsto_matrixOperatorNorm_sub_one.congr fun R => ?_
    exact ((hRules.2.1 R R).2.2.2.2.2.2.1).symm
  exact squeeze_zero (fun _ => sharpNormR4_nonneg _ _) (fun R => hm.1 (embedOrthogonal R)) (hm.2.comp h₁)
theorem reflectionForm_posTupleVec (σ : TupleFunctional) (X Y : supportedIn TimeAxis.upperHalfSpace) :
    reflectionForm σ (posTupleVec X) (posTupleVec Y) =
      (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by apply _root_.YangMills.SharedProofs.p11521 <;> assumption
theorem tsupport_get_subset (X : SepTuple) (l : Fin X.1.length) :
    tsupport (X.1.get l) ⊆ closedBallR4 0 (maxSupportRadius X) := by
  intro x hx
  have hcont : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  have hK : IsCompact (⋃ l, tsupport (X.1.get l)) :=
    isCompact_iUnion fun l => (X.2.1 _ (List.get_mem _ _)).2
  have hB : BddAbove {r | ∃ x ∈ ⋃ l, tsupport (X.1.get l), r = euclidNormVec x} := by
    obtain ⟨C, hC⟩ := (hK.image hcont).bddAbove
    refine ⟨C, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact hC ⟨y, hy, rfl⟩
  change euclidNormVec (x - 0) ≤ maxSupportRadius X
  rw [sub_zero]
  exact le_csSup hB ⟨x, Set.mem_iUnion.2 ⟨l, hx⟩, rfl⟩
section Strong
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
def TendsToSelfAtOne (U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) (ψ : PhysicalSpace σ h) : Prop :=
  Tendsto (fun R : orthogonalGroupThree => ‖U R ψ - ψ‖) (@nhds _ (operatorNormTopology 3) 1) (𝓝 0)
theorem posClass_eq_zero_of_zero_component (hC : HilbertSpaceFacts.CompletionProperties) (hRules : Laws.Statement)
    (hm : σ.IsEntrywiseLinear) (X : supportedIn TimeAxis.upperHalfSpace) (h0 : (0 : RealValued) ∈ X.1.1) :
    posClass σ h (posTupleVec X) = 0 := by
  have hd := (hRules.2.2.1 1).1 X.1 X.2 X.1 X.2
  obtain ⟨s, t, hst⟩ := List.append_of_mem h0
  have hY : (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1).1 =
      ((push TimeAxis.timeReflection X.1).1 ++ s) ++ (0 : RealValued) :: t := by
    rw [SepTuple.juxt_val hd, hst]
    simp
  have hm' := hm _ t 0 0 0 0 _ _ _ hY hY (by simpa using hY)
  have hz : σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) = 0 := by simpa using hm'
  have hi := inner_posClass (h := h) hC (posTupleVec X) (posTupleVec X)
  rw [reflectionForm_posTupleVec, hz] at hi
  exact (inner_self_eq_zero (𝕜 := ℂ)).1 (hi.trans Complex.ofReal_zero)
theorem norm_apply_sub_sq (hC : HilbertSpaceFacts.CompletionProperties)
    (hU : IsOrthogonalRep hRules U) (R : orthogonalGroupThree) (X : supportedIn TimeAxis.upperHalfSpace)
    (hR : push (matMap (embedOrthogonal R)) X.1 ∈ supportedIn TimeAxis.upperHalfSpace) :
    ‖U R (posClass σ h (posTupleVec X)) - posClass σ h (posTupleVec X)‖ ^ 2 =
      2 * (σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) -
        σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) (push (matMap (embedOrthogonal R)) X.1))) := by
  have hrot : U R (posClass σ h (posTupleVec X)) = posClass σ h (posTupleVec ⟨_, hR⟩) := by
    rw [hU.apply_posClass]
    exact congrArg _ (Subtype.ext (pushSpan_basisVec _ X.1))
  have hn := hU.norm_apply R (posClass σ h (posTupleVec X))
  have h₁ : ‖posClass σ h (posTupleVec X)‖ ^ 2 = σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) X.1) := by
    rw [@norm_sq_eq_re_inner ℂ, inner_posClass hC, reflectionForm_posTupleVec]
    rfl
  have h₂ : RCLike.re ⟪posClass σ h (posTupleVec X), U R (posClass σ h (posTupleVec X))⟫_ℂ =
      σ (SepTuple.juxt (push TimeAxis.timeReflection X.1) (push (matMap (embedOrthogonal R)) X.1)) := by
    rw [hrot, inner_posClass hC, reflectionForm_posTupleVec]
    rfl
  rw [norm_sub_rev, @norm_sub_sq ℂ, hn, h₂, h₁]
  ring
theorem tendsToSelf_posTupleVec (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsOrthogonalRep hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (X : supportedIn TimeAxis.upperHalfSpace) :
    TendsToSelfAtOne U (posClass σ h (posTupleVec X)) := by
  unfold TendsToSelfAtOne
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
      rw [posClass_eq_zero_of_zero_component hC hRules four.entrywiseLinear X hz, map_zero, sub_self, norm_zero]
    simp only [this]
    exact tendsto_const_nhds
  have hlen : 1 ≤ X.1.size := List.length_pos_iff.2 h0
  have hne : ∀ f ∈ X.1.1, f ≠ 0 := fun f hfX e => hz (e ▸ hfX)
  obtain ⟨hd, hρ, hT⟩ := hCont M σ B hM four X.1 X.2 hlen hne
  have hs : ∀ l : Fin X.1.1.length, Tendsto
      (fun R : orthogonalGroupThree => sharpNormR4 M (orthogonalAct (embedOrthogonal R) (X.1.1.get l) - X.1.1.get l))
      (@nhds _ (operatorNormTopology 3) 1) (𝓝 0) := fun l =>
    tendsto_sharpNormR4_rotate hRules hMod hM (X.1.2.1 _ (List.get_mem _ _)) hρ (tsupport_get_subset X.1 l)
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
theorem tendsToSelf_posClass (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsOrthogonalRep hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (F : PositiveSpan) :
    TendsToSelfAtOne U (posClass σ h F) := by
  let S : Submodule ℂ (PhysicalSpace σ h) :=
    { carrier := {ψ | TendsToSelfAtOne U ψ}
      add_mem' := by
        intro a b ha hb
        have h₁ := Tendsto.add ha hb
        rw [add_zero] at h₁
        refine squeeze_zero (fun _ => norm_nonneg _) (fun R => ?_) h₁
        rw [map_add, add_sub_add_comm]
        exact norm_add_le _ _
      zero_mem' := by
        change TendsToSelfAtOne U 0
        unfold TendsToSelfAtOne
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
      exact tendsToSelf_posTupleVec hC hCont hMod hU hM four X
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
theorem tendsToSelf (hC : HilbertSpaceFacts.CompletionProperties)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsOrthogonalRep hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (ψ : PhysicalSpace σ h) : TendsToSelfAtOne U ψ := by
  unfold TendsToSelfAtOne
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, hF, ⟨F, rfl⟩⟩ := Metric.dense_iff.1 (dense_range_posClass (σ := σ) (h := h) hC) ψ (ε / 3) (by positivity)
  have hFn : ‖posClass σ h F - ψ‖ < ε / 3 := by
    rwa [Metric.mem_ball, dist_eq_norm] at hF
  have ht := (Metric.tendsto_nhds.1 (tendsToSelf_posClass hC hCont hMod hU hM four F)) (ε / 3) (by positivity)
  refine ht.mono fun R hR => ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hR ⊢
  have e : U R ψ - ψ = U R (ψ - posClass σ h F) + (U R (posClass σ h F) - posClass σ h F) +
      (posClass σ h F - ψ) := by
    rw [map_sub]
    abel
  have h₁ : ‖U R (ψ - posClass σ h F)‖ < ε / 3 := by
    rw [hU.norm_apply, norm_sub_rev]
    exact hFn
  rw [e]
  calc _ ≤ ‖U R (ψ - posClass σ h F)‖ + ‖U R (posClass σ h F) - posClass σ h F‖ +
        ‖posClass σ h F - ψ‖ := norm_add₃_le
    _ < ε := by linarith
theorem tendsto_inv_mul (R₀ : orthogonalGroupThree) :
    Tendsto (fun R : orthogonalGroupThree => R₀⁻¹ * R) (@nhds _ (operatorNormTopology 3) R₀)
      (@nhds _ (operatorNormTopology 3) 1) := by
  let C : orthogonalGroupThree → (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    fun R => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) R.1
  have hnh : @nhds _ (operatorNormTopology 3) (1 : orthogonalGroupThree) = comap C (𝓝 (C 1)) :=
    nhds_induced _ _
  rw [hnh, tendsto_comap_iff]
  have hcC : @Continuous _ _ (operatorNormTopology 3) _ C := continuous_induced_dom
  have h₁ := (@Continuous.tendsto _ _ (operatorNormTopology 3) _ _ hcC R₀).const_mul (C R₀⁻¹)
  have hm : ∀ R R' : orthogonalGroupThree, C (R * R') = C R * C R' := fun R R' => by
    simp [C, map_mul]
  rw [← hm, inv_mul_cancel] at h₁
  exact h₁.congr fun R => (hm _ _).symm
theorem continuous_orbit_map (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hU : IsOrthogonalRep hRules U) {M : ℝ} {B : ℕ → ℝ → ℝ → ℝ} (hM : 1 ≤ M)
    (four : RotationHypotheses M σ B) (ψ : PhysicalSpace σ h) :
    Continuous fun R : orthogonalGroupThree => U R ψ := by
  have key : @Continuous _ _ (operatorNormTopology 3) _ fun R : orthogonalGroupThree => U R ψ := by
    refine (@continuous_iff_continuousAt _ _ (operatorNormTopology 3) _ _).2 fun R₀ => ?_
    change Tendsto _ (@nhds _ (operatorNormTopology 3) R₀) (𝓝 _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (Tendsto.comp (tendsToSelf hC hCont hMod hU hM four ψ) (tendsto_inv_mul R₀)).congr fun R => ?_
    have hg : U R = (U R₀).comp (U (R₀⁻¹ * R)) := by
      rw [hU.comp_eq hC hId, mul_inv_cancel_left]
    change ‖U (R₀⁻¹ * R) ψ - ψ‖ = _
    rw [hg, ContinuousLinearMap.comp_apply, ← map_sub, hU.norm_apply]
  rw [operatorNormTopology_eq 3] at key
  exact key
end Strong
theorem embedSpatial_eq_spacetimePoint (a : Fin 3 → ℝ) : embedSpatial a = spacetimePoint a 0 := by apply _root_.YangMills.Construction.LimitTheorem.TranslationMeasureProof.embedSpatial_eq_spacetimePoint <;> assumption
section Relations
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem IsOrthogonalRep.intertwine (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities) (hU : IsOrthogonalRep hRules U)
    (R : orthogonalGroupThree) {T T' : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h} {S S' : FormalSpan →ₗ[ℂ] FormalSpan}
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
theorem IsOrthogonalRep.commute_timeShift (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities) (hU : IsOrthogonalRep hRules U)
    (hT : IsTimeShiftFamily σ h (timeShift σ h)) (R : orthogonalGroupThree) (t : ℝ≥0) :
    Commute (U R) (timeShift σ h t) := by
  obtain ⟨-, -, -, -, -, hLast⟩ := hRules.2.2.1 R
  exact hU.intertwine hC hId R
    (fun G hG => pushSpan_mem (fun X hX => ((hRules.2.2.1 1).2.1 X hX).1 t t.2) hG)
    (hT t) (hT t) fun G hG => (hLast G hG G hG).2.1 t t.2
theorem IsOrthogonalRep.mul_spaceShift (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities) (hU : IsOrthogonalRep hRules U)
    (hS : IsSpaceShiftFamily σ h (spaceShift σ h)) (R : orthogonalGroupThree) (a : Fin 3 → ℝ) :
    U R * spaceShift σ h a = spaceShift σ h (R.1 *ᵥ a) * U R := by
  obtain ⟨-, -, -, -, -, hLast⟩ := hRules.2.2.1 R
  refine hU.intertwine hC hId R
    (fun G hG => pushSpan_mem (fun X hX => ?_) hG) (hS a) (hS (R.1 *ᵥ a)) fun G hG => ?_
  · rw [embedSpatial_eq_spacetimePoint]
    exact ((hRules.2.2.1 1).2.1 X hX).2 a
  · rw [embedSpatial_eq_spacetimePoint, embedSpatial_eq_spacetimePoint]
    exact (hLast G hG G hG).2.2 a
end Relations
section Conjugates
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem compBounded_ofBounded (B C : ℋ →L[ℂ] ℋ) :
    compBounded (ofBounded B) C = ofBounded (B * C) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.compBounded_ofBounded <;> assumption
theorem ofBounded_inj {A B : ℋ →L[ℂ] ℋ} (h : ofBounded A = ofBounded B) : A = B := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_injective <;> assumption
def conjCLM (V : ℋ ≃ₗᵢ[ℂ] ℋ) (B : ℋ →L[ℂ] ℋ) : ℋ →L[ℂ] ℋ :=
  (V.toContinuousLinearEquiv : ℋ →L[ℂ] ℋ) ∘L B ∘L (V.symm.toContinuousLinearEquiv : ℋ →L[ℂ] ℋ)
omit [CompleteSpace ℋ] in
theorem conjCLM_apply (V : ℋ ≃ₗᵢ[ℂ] ℋ) (B : ℋ →L[ℂ] ℋ) (ψ : ℋ) :
    conjCLM V B ψ = V (B (V.symm ψ)) := rfl
theorem unitaryConj_ofBounded (V : ℋ ≃ₗᵢ[ℂ] ℋ) (B : ℋ →L[ℂ] ℋ) :
    SpectralTheory.unitaryConj V (ofBounded B) = ofBounded (conjCLM V B) := by
  refine (unboundedOperator_eq_iff _ _).2 ⟨?_, ?_⟩
  · refine (Submodule.eq_top_iff'.2 fun x => ?_)
    exact ⟨V.symm x, Submodule.mem_top, by simp⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain rfl : x = y := hxy
    have hm : V (V.symm x) ∈ (SpectralTheory.unitaryConj V (ofBounded B)).domain := by
      simpa using hx
    have e := unitaryConj_apply V (ofBounded B) ⟨V.symm x, Submodule.mem_top⟩ hm
    have hs : (⟨x, hx⟩ : (SpectralTheory.unitaryConj V (ofBounded B)).domain) =
        ⟨V (V.symm x), hm⟩ := Subtype.ext (by simp)
    rw [hs, e]
    rfl
end Conjugates
def rotateMomentum (R : orthogonalGroupThree) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Fin.cons (α := fun _ => ℝ) (y 0) (R.1 *ᵥ spatialPart y)
theorem rotateMomentum_zero (R : orthogonalGroupThree) (y : Fin 4 → ℝ) : rotateMomentum R y 0 = y 0 := rfl
theorem spatialPart_rotateMomentum (R : orthogonalGroupThree) (y : Fin 4 → ℝ) :
    spatialPart (rotateMomentum R y) = R.1 *ᵥ spatialPart y := rfl
theorem measurable_rotateMomentum (R : orthogonalGroupThree) : Measurable (rotateMomentum R) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_pi_apply 0
  · have hc : Continuous fun y : Fin 4 → ℝ => R.1 *ᵥ spatialPart y :=
      Continuous.matrix_mulVec continuous_const (continuous_pi fun i => continuous_apply i.succ)
    exact (measurable_pi_apply j).comp hc.measurable
theorem spaceDot_mulVec (R : orthogonalGroupThree) (a q : Fin 3 → ℝ) :
    spaceDot a (R.1 *ᵥ q) = spaceDot ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) q := by
  have hinv : (R⁻¹ : orthogonalGroupThree).1 = R.1ᵀ := rfl
  rw [hinv]
  simp only [spaceDot, SeparatedTupleFunctionals.dotProd, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem unitaryPhase_comp_rotateMomentum (R : orthogonalGroupThree) (τ : ℝ) (a : Fin 3 → ℝ) :
    unitaryPhase τ a ∘ rotateMomentum R = unitaryPhase τ ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) := by
  funext y
  simp only [Function.comp_apply, unitaryPhase, rotateMomentum_zero, spatialPart_rotateMomentum, spaceDot_mulVec]
theorem measurable_unitaryPhase (τ : ℝ) (a : Fin 3 → ℝ) : Measurable (unitaryPhase τ a) := by
  have hc : Continuous (unitaryPhase τ a) := by
    unfold unitaryPhase spatialPart spaceDot SeparatedTupleFunctionals.dotProd
    fun_prop
  exact hc.measurable
section Covariance
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem jointMeasure_eq_zero_of_preimage (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hRi : SpectralIntegralLawsHold)
    (hGd : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hU : IsOrthogonalRep hRules U) (hrec : HasReconstruction σ h) (hMeas : MeasureClaim σ h)
    (R : orthogonalGroupThree) (A : BorelSets 4)
    (h0 : jointMeasure σ h ⟨rotateMomentum R ⁻¹' A.1, measurable_rotateMomentum R A.2⟩ = 0) :
    jointMeasure σ h A = 0 := by
  set E := jointMeasure σ h with hEdef
  set V := hU.toUnitary hC hId R with hVdef
  obtain ⟨hex, hE⟩ := hMeas
  obtain ⟨F, hF, hFE⟩ := id hE
  obtain ⟨-, hT, -, -, -, ⟨F₁, hF₁, hF₁c, hF₁e⟩, -, -⟩ := hrec.2.1
  obtain ⟨-, hS, -, -, -, -, -⟩ := hrec.2.2.1
  have hGen := (hGd (PhysicalSpace σ h)).1 F
  have hFF : F₁ = F := hGen.2.2.1.eq_of_generator F₁ (hF₁.symm.trans hF)
  subst hFF
  have hSF := hGen.2.1 hF₁c
  have hsg : ∀ t, F₁.contractionFlow t = timeShift σ h t := fun t =>
    ofBounded_inj ((hSF.expNegMulOp_eq t).symm.trans (hF₁e t).symm)
  have hcomm : F₁.CommutesWithFlows (U R) :=
    Or.inr ⟨hF₁c, fun t _ _ => by
      rw [hsg]
      exact hU.commute_timeShift hC hId hT R t⟩
  have hconj := (hGen.2.2.2 _ hcomm).2 V fun ψ => rfl
  have RF := hRi 1 (PhysicalSpace σ h) F₁
  have hFV : F₁.unitaryTransport V = F₁ := hGen.2.2.1.eq_of_generator _ (by
    show (F₁.unitaryTransport V).functionalCalculus (coordFun 0) = F₁.functionalCalculus (coordFun 0)
    rw [RF.calculus_unitaryTransport _ V _ (measurable_coordFun 0)]
    exact hconj)
  have hW : ∀ τ : ℝ, conjCLM V (F₁.unitaryFlow τ) = F₁.unitaryFlow τ := fun τ => by
    have hm : Measurable fun x : Fin 1 → ℝ => Complex.exp (Complex.I * τ * x 0) := by fun_prop
    have e : F₁.expIMulOp τ = SpectralTheory.unitaryConj V (F₁.expIMulOp τ) := by
      conv_lhs => rw [← hFV]
      exact RF.calculus_unitaryTransport _ V _ hm
    rw [hGen.1.expIMulOp_eq τ, unitaryConj_ofBounded] at e
    exact (ofBounded_inj e).symm
  have RE := hRi 4 (PhysicalSpace σ h) E
  have hπ := measurable_rotateMomentum R
  have RI := hRi 4 (PhysicalSpace σ h) (E.imageMeasure (rotateMomentum R) hπ)
  have hGm : IsJointGroupMeasure σ h ((E.imageMeasure (rotateMomentum R) hπ).unitaryTransport V) := by
    refine ⟨F₁, hF, fun τ a => ?_⟩
    rw [RI.calculus_unitaryTransport _ V _ (measurable_unitaryPhase τ a),
      RE.calculus_imageMeasure 4 _ hπ _ (measurable_unitaryPhase τ a), unitaryPhase_comp_rotateMomentum, ← hFE,
      hGen.1.expIMulOp_eq τ, compBounded_ofBounded, compBounded_ofBounded, unitaryConj_ofBounded]
    congr 1
    ext ψ
    have h₁ : V (F₁.unitaryFlow τ (V.symm (U R (spaceShift σ h ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) (V.symm ψ))))) =
        F₁.unitaryFlow τ (U R (spaceShift σ h ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) (V.symm ψ))) :=
      congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T (U R (spaceShift σ h ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) (V.symm ψ)))) (hW τ)
    have h₂ := congrArg (fun T : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => T (V.symm ψ))
      (hU.mul_spaceShift hC hId hS R ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a))
    have h₃ : R.1 *ᵥ ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec]
      have : R.1 * (R⁻¹ : orthogonalGroupThree).1 = 1 := congrArg Subtype.val (mul_inv_cancel R)
      rw [this, Matrix.one_mulVec]
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, h₃] at h₂
    have h₄ : U R (V.symm ψ) = ψ := V.apply_symm_apply ψ
    rw [h₄] at h₂
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, conjCLM_apply]
    have h₅ : V.symm (U R (spaceShift σ h ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) (V.symm ψ))) =
        spaceShift σ h ((R⁻¹ : orthogonalGroupThree).1 *ᵥ a) (V.symm ψ) := V.symm_apply_apply _
    rw [h₅] at h₁
    rw [h₁, h₂]
  have hGE : (E.imageMeasure (rotateMomentum R) hπ).unitaryTransport V = E := hex.unique hGm hE
  ext ψ
  have e := RI.unitaryTransport_apply _ V A ψ
  rw [hGE] at e
  rw [e]
  have e₂ : (E.imageMeasure (rotateMomentum R) hπ) A = E ⟨rotateMomentum R ⁻¹' A.1, hπ A.2⟩ := RE.imageMeasure_apply 4 _ hπ A
  rw [e₂, h0]
  simp
end Covariance
section Cone
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem spectral_eq_zero_of_subset (E : ProjectionMeasure 4 ℋ) {A B : BorelSets 4} (hAB : B.1 ⊆ A.1)
    (h0 : E A = 0) : E B = 0 := by apply _root_.YangMills.Construction.LimitTheorem.TranslationMeasureProof.apply_eq_zero_of_subset <;> assumption
theorem spectral_iUnion_eq_zero (E : ProjectionMeasure 4 ℋ) {ι : Type} [Countable ι] (A : ι → BorelSets 4)
    (h0 : ∀ i, E (A i) = 0) : E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ = 0 := by
  ext ψ
  have hz : E.spectralValueMeasure ψ (⋃ i, (A i).1) = 0 := by
    refine measure_iUnion_null fun i => ?_
    have := E.spectralValueMeasure_apply ψ (A i)
    rw [h0 i] at this
    simpa using this
  have e := E.spectralValueMeasure_apply ψ ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩
  rw [show E.spectralValueMeasure ψ (⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ : BorelSets 4).1 = 0 from hz] at e
  have h₁ : ‖E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ ψ‖ ^ 2 ≤ 0 :=
    ENNReal.ofReal_eq_zero.1 e.symm
  have h₂ : ‖E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ ψ‖ = 0 := by
    nlinarith [norm_nonneg (E ⟨⋃ i, (A i).1, MeasurableSet.iUnion fun i => (A i).2⟩ ψ)]
  simpa using h₂
end Cone
theorem exists_orthogonal_firstCol {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    ∃ R : orthogonalGroupThree, ∀ i, R.1 i 0 = n.ofLp i := by
  have hv : Orthonormal ℝ (Set.domRestrict ({0} : Set (Fin 3)) fun _ => n) := by
    refine ⟨fun _ => hn, fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (b j).ofLp i
  have hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    refine (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).2 ?_
    ext i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    simp only [Matrix.mul_apply, A, Matrix.of_apply]
    rw [Matrix.one_apply, ← h, PiLp.inner_apply]
    simp [mul_comm]
  refine ⟨⟨A, hA⟩, fun i => ?_⟩
  have h0 := hb 0 rfl
  simp [A, h0]
def directionalSpacelike (n : EuclideanSpace ℝ (Fin 3)) : BorelSets 4 :=
  ⟨{y | y 0 < |∑ i, n.ofLp i * spatialPart y i|}, by
    have hc : Continuous fun y : Fin 4 → ℝ => |∑ i, n.ofLp i * spatialPart y i| := by
      unfold spatialPart
      fun_prop
    exact measurableSet_lt (measurable_pi_apply 0) hc.measurable⟩
theorem exists_countable_directional_cover : ∃ (ι : Type) (_ : Countable ι) (n : ι → EuclideanSpace ℝ (Fin 3)),
    (∀ u, ‖n u‖ = 1) ∧ spacelikeRegion ⊆ ⋃ u, (directionalSpacelike (n u)).1 := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin 3))
  have hcount : Countable ↥(s \ {0}) := (hs.mono Set.sdiff_subset).to_subtype
  have hne : ∀ u : ↥(s \ {0}), ‖u.1‖ ≠ 0 := fun u => norm_ne_zero_iff.2 u.2.2
  refine ⟨↥(s \ {0}), hcount, fun u => (‖u.1‖⁻¹ : ℝ) • u.1, fun u => ?_, fun y hy => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hne u)]
  set q : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (spatialPart y) with hq
  have hnorm : ‖q‖ = Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [q, spatialPart, Fin.sum_univ_three]
  have hy' : y 0 < ‖q‖ := by rw [hnorm]; exact hy
  let O : Set (EuclideanSpace ℝ (Fin 3)) := {u | u ≠ 0} ∩ {u | y 0 * ‖u‖ < |inner ℝ u q|}
  have hO : IsOpen O := by
    refine (isOpen_ne).inter (isOpen_lt (by fun_prop) ?_)
    exact continuous_abs.comp (continuous_id.inner continuous_const)
  have hOn : O.Nonempty := by
    by_cases hq0 : q = 0
    · refine ⟨EuclideanSpace.single 0 1, ?_, ?_⟩
      · intro h0
        have : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by simp
        rw [h0] at this
        simp at this
      · rw [hq0, norm_zero] at hy'
        change y 0 * ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ < |inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) q|
        rw [hq0]
        simpa using hy'
    · refine ⟨q, hq0, ?_⟩
      change y 0 * ‖q‖ < |inner ℝ q q|
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity), sq]
      exact mul_lt_mul_of_pos_right hy' (norm_pos_iff.2 hq0)
  obtain ⟨v, hvO, hvs⟩ := hd.inter_open_nonempty O hO hOn
  refine Set.mem_iUnion.2 ⟨⟨v, hvs, hvO.1⟩, ?_⟩
  have hv : 0 < ‖v‖ := norm_pos_iff.2 hvO.1
  have hin : ∑ i, ((‖v‖⁻¹ : ℝ) • v).ofLp i * spatialPart y i = ‖v‖⁻¹ * inner ℝ v q := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [q, mul_comm, mul_assoc]
  change y 0 < |∑ i, ((‖v‖⁻¹ : ℝ) • v).ofLp i * spatialPart y i|
  rw [hin, abs_mul, abs_of_pos (inv_pos.2 hv), lt_inv_mul_iff₀ hv, mul_comm]
  exact hvO.2
section Final
variable {σ : TupleFunctional} {h : IsPosSemidef (reflectionForm σ)} {hRules : Laws.Statement}
  {U : orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
theorem jointMeasure_directionalSpacelike (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hRi : SpectralIntegralLawsHold)
    (hGd : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hU : IsOrthogonalRep hRules U) (hrec : HasReconstruction σ h) (hMeas : MeasureClaim σ h)
    (hMar : MarginalClaim σ h) {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    jointMeasure σ h (directionalSpacelike n) = 0 := by
  obtain ⟨R, hR⟩ := exists_orthogonal_firstCol hn
  refine jointMeasure_eq_zero_of_preimage hC hId hRi hGd hU hrec hMeas R _ ?_
  refine spectral_eq_zero_of_subset _ (A := ⟨forwardCone.1ᶜ, forwardCone.2.compl⟩) ?_ hMar.2
  intro y hy hpy
  have hy' : rotateMomentum R y 0 < |∑ i, n.ofLp i * spatialPart (rotateMomentum R y) i| := hy
  have hp : |y (0 : Fin 3).succ| ≤ y 0 := hpy (0 : Fin 3)
  have e : ∑ i, n.ofLp i * spatialPart (rotateMomentum R y) i = spatialPart y 0 := by
    rw [spatialPart_rotateMomentum]
    have hRR : R.1ᵀ * R.1 = 1 := by
      have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 R.2
      simpa [Matrix.star_eq_conjTranspose] using this
    have h₁ : ((R.1ᵀ * R.1) *ᵥ spatialPart y) 0 = ∑ i, n.ofLp i * (R.1 *ᵥ spatialPart y) i := by
      rw [← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hR]
    rw [← h₁, hRR, Matrix.one_mulVec]
  rw [rotateMomentum_zero, e] at hy'
  exact absurd hp (not_le.2 hy')
theorem jointMeasure_spacelikeRegion (hC : HilbertSpaceFacts.CompletionProperties)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hRi : SpectralIntegralLawsHold)
    (hGd : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hU : IsOrthogonalRep hRules U) (hrec : HasReconstruction σ h) (hMeas : MeasureClaim σ h)
    (hMar : MarginalClaim σ h) :
    jointMeasure σ h ⟨spacelikeRegion, isOpen_spacelikeRegion.measurableSet⟩ = 0 := by
  obtain ⟨ι, _, n, hn, hcov⟩ := exists_countable_directional_cover
  exact spectral_eq_zero_of_subset _ hcov (spectral_iUnion_eq_zero _ _ fun u =>
    jointMeasure_directionalSpacelike hC hId hRi hGd hU hrec hMeas hMar (hn u))
end Final
theorem rotationsAndCone_holds (hHF : HilbertSpaceFacts.Facts) (hRules : Laws.Statement)
    (hCont : ModulusEstimate) (hMod : SharpNormRotationModulus)
    (hRi : SpectralIntegralLawsHold)
    (hGd : GeneratorsAndFlows.GeneratorFlowTheorem) : RotationsAndConeStatement := by
  obtain ⟨-, -, -, -, -, hC, -, hO, -, -, -, -, -, -, -, -, -, -, -, hId, -⟩ := hHF
  intro M σ B h P
  obtain ⟨U, hU⟩ := exists_orthogonalRep (h := h) hC hId hO hRules P.hyps.orthogonal_invariant
  obtain ⟨-, hT, -⟩ := P.reconstruction.2.1
  refine ⟨fun h' => ?_, fun h' => ?_, jointMeasure_spacelikeRegion hC hId hRi hGd hU P.reconstruction P.measure P.marginal⟩
  · obtain rfl : h' = h := rfl
    refine ⟨_, ⟨jointMeasure σ h', fun r => ?_, rfl⟩, ?_⟩
    · obtain ⟨h₀, hi, -, -⟩ := P.operators
      fin_cases r
      · exact h₀
      · exact hi 0
      · exact hi 1
      · exact hi 2
    · intro y hy
      by_contra hn
      have hn' : ¬ (Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) ≤ y 0) := hn
      have hb : y ∈ spacelikeRegion := not_le.1 hn'
      exact hy (Set.mem_sUnion.2 ⟨spacelikeRegion, ⟨isOpen_spacelikeRegion,
        jointMeasure_spacelikeRegion hC hId hRi hGd hU P.reconstruction P.measure P.marginal⟩, hb⟩)
  · obtain rfl : h' = h := rfl
    refine ⟨U, fun R F => ?_, ⟨fun R => ⟨hU.norm_apply R, hU.surjective hC hId R⟩, hU.comp_eq hC hId⟩,
      continuous_orbit_map hC hId hCont hMod hU P.one_le P.hyps, hU.apply_vacuum,
      fun R t => hU.commute_timeShift hC hId hT R t⟩
    have hm : orthogonalMap (embedOrthogonal R) = matMap (embedOrthogonal R) := funext fun x => by
      simp [orthogonalMap, ofOrthogonal, Motions.RigidMotion.toFun, matMap]
    rw [hm, hU.apply_posClass]
    exact (spanClass_coe _).symm
end YangMills.Construction.LimitTheorem.RotationsAndCone
end
