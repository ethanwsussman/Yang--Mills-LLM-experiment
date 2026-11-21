import YangMills.Construction.Towers.TransposeOfTheRestrictionOnTheWholeProof
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.MapsOfTwoSidesFromPeriodicLinearMaps
import YangMills.Construction.Towers.ScaledNormsOfSmallIteratesAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.UnitScale.OneStepChart.FromPeriodic
section Matrices
theorem real_smul_mem_traceless (r : ℝ) {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless) :
    r • A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledNormBounds.real_smul_mem_traceless <;> assumption
theorem finsum_real_smul_mem_traceless {ι : Type*} (c : ι → ℝ) (F : ι → ComplexMatrix2)
    (hF : ∀ i, F i ∈ ComplexMatrix2.traceless) :
    ∑ᶠ i, c i • F i ∈ ComplexMatrix2.traceless :=
  finsum_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
    (fun _ _ => ComplexMatrix2.traceless.add_mem)
    fun i => real_smul_mem_traceless _ (hF i)
theorem support_real_smul_finite {ι : Type*} {c : ι → ℝ} (F : ι → ComplexMatrix2)
    (hc : {i | c i ≠ 0}.Finite) :
    (Function.support fun i => c i • F i).Finite :=
  hc.subset fun i hi h0 => Function.mem_support.1 hi (by rw [h0, zero_smul])
theorem finsum_real_smul_add {ι : Type*} {c : ι → ℝ} (F G : ι → ComplexMatrix2)
    (hc : {i | c i ≠ 0}.Finite) :
    ∑ᶠ i, c i • (F i + G i) = ∑ᶠ i, c i • F i + ∑ᶠ i, c i • G i := by
  simp only [smul_add]
  exact finsum_add_distrib (support_real_smul_finite F hc) (support_real_smul_finite G hc)
theorem finsum_real_smul_complex_smul {ι : Type*} {c : ι → ℝ} (z : ℂ) (F : ι → ComplexMatrix2)
    (hc : {i | c i ≠ 0}.Finite) :
    ∑ᶠ i, c i • (z • F i) = z • ∑ᶠ i, c i • F i := by
  rw [smul_finsum' z (support_real_smul_finite F hc)]
  exact finsum_congr fun i => smul_comm _ _ _
theorem halfTrace_mul_real_smul (r : ℝ) (A B : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * r • B) = (r : ℂ) * ComplexMatrix2.halfTrace (A * B) := by
  have h : r • B = (r : ℂ) • B := by
    ext i j
    simp
  rw [h, Matrix.mul_smul]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul]
  ring
theorem halfTrace_real_smul_mul (r : ℝ) (A B : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (r • A * B) = (r : ℂ) * ComplexMatrix2.halfTrace (A * B) := by
  have h : r • A = (r : ℂ) • A := by
    ext i j
    simp
  rw [h, Matrix.smul_mul]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul]
  ring
theorem halfTrace_mul_sum {ι : Type*} (s : Finset ι) (A : ComplexMatrix2) (F : ι → ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * ∑ i ∈ s, F i) = ∑ i ∈ s, ComplexMatrix2.halfTrace (A * F i) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.mul_sum, Matrix.trace_sum]
theorem halfTrace_sum_mul {ι : Type*} (s : Finset ι) (A : ComplexMatrix2) (F : ι → ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((∑ i ∈ s, F i) * A) = ∑ i ∈ s, ComplexMatrix2.halfTrace (F i * A) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.sum_mul, Finset.mul_sum,
    Matrix.trace_sum]
theorem halfTrace_sub_mul (A B C : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((A - B) * C) =
      ComplexMatrix2.halfTrace (A * C) - ComplexMatrix2.halfTrace (B * C) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, sub_mul, Matrix.trace_sub, mul_sub]
def diagBasis : ComplexMatrix2 := !![1, 0; 0, -1]
theorem diagBasis_mem : diagBasis ∈ ComplexMatrix2.traceless := by
  change ComplexMatrix2.fullTrace diagBasis = 0
  simp [ComplexMatrix2.fullTrace, diagBasis, Matrix.trace_fin_two]
theorem eq_zero_of_halfTrace_mul_eq_zero {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (h : ∀ t ∈ ComplexMatrix2.traceless, ComplexMatrix2.halfTrace (A * t) = 0) : A = 0 := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.eq_zero_of_halfTrace_mul_eq_zero <;> assumption
theorem real_smul_diagBasis_injective {r r' : ℝ} (h : r • diagBasis = r' • diagBasis) :
    r = r' := by
  have h1 := congrFun (congrFun h 0) 0
  simpa [diagBasis] using h1
end Matrices
section EvaluationMaps
open Classical in
def singleValue {P : Type} (p : P) (t : ComplexMatrix2) : P → ComplexMatrix2 :=
  fun p' => if p' = p then t else 0
theorem singleValue_self {P : Type} (p : P) (t : ComplexMatrix2) : singleValue p t p = t := by
  simp [singleValue]
theorem singleValue_of_ne {P : Type} {p p' : P} (t : ComplexMatrix2) (h : p' ≠ p) :
    singleValue p t p' = 0 := by
  simp [singleValue, h]
theorem singleValue_mem {P : Type} (p : P) {t : ComplexMatrix2} (ht : t ∈ ComplexMatrix2.traceless)
    (p' : P) : singleValue p t p' ∈ ComplexMatrix2.traceless := by
  by_cases h : p' = p
  · rw [h, singleValue_self]
    exact ht
  · rw [singleValue_of_ne t h]
    exact ComplexMatrix2.traceless.zero_mem
theorem finsum_smul_singleValue {P : Type} (c : P → ℝ) (p : P) (t : ComplexMatrix2) :
    ∑ᶠ p', c p' • singleValue p t p' = c p • t := by
  rw [finsum_eq_single _ p fun p' h => by rw [singleValue_of_ne t h, smul_zero], singleValue_self]
theorem traceFinsumPairing_singleValue {P : Type} (a : P → ComplexMatrix2) (p : P) (t : ComplexMatrix2) :
    traceFinsumPairing a (singleValue p t) = ComplexMatrix2.halfTrace (a p * t) := by apply _root_.YangMills.Construction.Tower.FullSpace.RestrictionTranspose.pair_pointMass <;> assumption
variable {S S' : PairedFunctionSpace} {P P' : Type}
  {v : (S.index → ComplexMatrix2) → P → ComplexMatrix2}
  {v' : (S'.index → ComplexMatrix2) → P' → ComplexMatrix2}
theorem exists_linearMap_of_kernel (R : IsSlotEvaluation S P v) (R' : IsSlotEvaluation S' P' v')
    (K : P' → P → ℝ) (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (hrow : ∀ q, {p | K q p ≠ 0}.Finite)
    (hmem : ∀ f ∈ S.complexSubmodule, m f ∈ S'.complexSubmodule)
    (hval : ∀ f ∈ S.complexSubmodule, ∀ q, v' (m f) q = ∑ᶠ p, K q p • v f p) :
    ∃ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
      ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = m f := by
  refine ⟨{ toFun := fun f => ⟨m f, hmem f f.2⟩, map_add' := ?_, map_smul' := ?_ }, fun f => rfl⟩
  · intro f g
    apply Subtype.ext
    show m ((f + g : S.complexSubmodule) : S.index → ComplexMatrix2) = m f + m g
    refine R'.eq_of_eval_eq _ (hmem _ (f + g).2) _
      (S'.complexSubmodule.add_mem (hmem _ f.2) (hmem _ g.2)) ?_
    rw [R'.eval_add _ (hmem _ f.2) _ (hmem _ g.2)]
    funext q
    rw [Pi.add_apply, hval _ (f + g).2, hval _ f.2, hval _ g.2, Submodule.coe_add,
      R.eval_add _ f.2 _ g.2]
    simpa only [Pi.add_apply] using finsum_real_smul_add _ _ (hrow q)
  · intro z f
    apply Subtype.ext
    show m ((z • f : S.complexSubmodule) : S.index → ComplexMatrix2) = z • m f
    refine R'.eq_of_eval_eq _ (hmem _ (z • f).2) _
      (S'.complexSubmodule.smul_mem z (hmem _ f.2)) ?_
    rw [R'.eval_smul z _ (hmem _ f.2)]
    funext q
    rw [Pi.smul_apply, hval _ (z • f).2, hval _ f.2, Submodule.coe_smul, R.eval_smul z _ f.2]
    simpa only [Pi.smul_apply] using finsum_real_smul_complex_smul z _ (hrow q)
theorem exists_linearMap_of_transposedKernel (R : IsSlotEvaluation S P v)
    (R' : IsSlotEvaluation S' P' v') (K : P' → P → ℝ) (hcol : ∀ p, {q | K q p ≠ 0}.Finite) :
    ∃ T' : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule, ∀ (g : S'.complexSubmodule) (p : P),
      v (T' g) p = ∑ᶠ q, K q p • v' g q := by
  have hex : ∀ g : S'.complexSubmodule, ∃ f ∈ S.complexSubmodule,
      v f = fun p => ∑ᶠ q, K q p • v' g q := fun g =>
    R.exists_eval_eq _ fun p => finsum_real_smul_mem_traceless _ _ fun q => R'.eval_mem g g.2 q
  choose F hF hFv using hex
  have hv : ∀ (g : S'.complexSubmodule) (p : P), v (F g) p = ∑ᶠ q, K q p • v' g q :=
    fun g p => congrFun (hFv g) p
  refine ⟨{ toFun := fun g => ⟨F g, hF g⟩, map_add' := ?_, map_smul' := ?_ }, hv⟩
  · intro g g'
    apply Subtype.ext
    show F (g + g') = F g + F g'
    refine R.eq_of_eval_eq _ (hF _) _ (S.complexSubmodule.add_mem (hF g) (hF g')) ?_
    rw [R.eval_add _ (hF g) _ (hF g')]
    funext p
    rw [Pi.add_apply, hv, hv, hv, Submodule.coe_add, R'.eval_add _ g.2 _ g'.2]
    simpa only [Pi.add_apply] using finsum_real_smul_add _ _ (hcol p)
  · intro z g
    apply Subtype.ext
    show F (z • g) = z • F g
    refine R.eq_of_eval_eq _ (hF _) _ (S.complexSubmodule.smul_mem z (hF g)) ?_
    rw [R.eval_smul z _ (hF g)]
    funext p
    rw [Pi.smul_apply, hv, hv, Submodule.coe_smul, R'.eval_smul z _ g.2]
    simpa only [Pi.smul_apply] using finsum_real_smul_complex_smul z _ (hcol p)
theorem traceFinsumPairing_kernel_transpose (K : P' → P → ℝ) (hcol : ∀ p, {q | K q p ≠ 0}.Finite)
    (a : P' → ComplexMatrix2) (b : P → ComplexMatrix2) (hb : (Function.support b).Finite) :
    traceFinsumPairing (fun p => ∑ᶠ q, K q p • a q) b =
      traceFinsumPairing a (fun q => ∑ᶠ p, K q p • b p) := by
  classical
  set Fs := hb.toFinset with hFs
  set Q : Finset P' := Fs.biUnion fun p => (hcol p).toFinset with hQ
  have hw : ∀ p ∈ Fs, ∑ᶠ q, K q p • a q = ∑ q ∈ Q, K q p • a q := by
    intro p hp
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    have hk : K q p ≠ 0 := fun h0 => Function.mem_support.1 hq (by rw [h0, zero_smul])
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨p, hp, (hcol p).mem_toFinset.2 hk⟩)
  have hc : ∀ q, ∑ᶠ p, K q p • b p = ∑ p ∈ Fs, K q p • b p := by
    intro q
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    have hk : b p ≠ 0 := fun h0 => Function.mem_support.1 hp (by rw [h0, smul_zero])
    exact Finset.mem_coe.2 (hb.mem_toFinset.2 (Function.mem_support.2 hk))
  have hl : traceFinsumPairing (fun p => ∑ᶠ q, K q p • a q) b =
      ∑ p ∈ Fs, ComplexMatrix2.halfTrace ((∑ᶠ q, K q p • a q) * b p) := by
    rw [traceFinsumPairing]
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    have hk : b p ≠ 0 := fun h0 => Function.mem_support.1 hp (by simp [h0])
    exact Finset.mem_coe.2 (hb.mem_toFinset.2 (Function.mem_support.2 hk))
  have hr : traceFinsumPairing a (fun q => ∑ᶠ p, K q p • b p) =
      ∑ q ∈ Q, ComplexMatrix2.halfTrace (a q * ∑ p ∈ Fs, K q p • b p) := by
    rw [traceFinsumPairing]
    simp only [hc]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra hqQ
    apply Function.mem_support.1 hq
    have h0 : ∑ p ∈ Fs, K q p • b p = 0 := Finset.sum_eq_zero fun p hp => by
      have hk : K q p = 0 := by
        by_contra hk
        exact hqQ (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨p, hp, (hcol p).mem_toFinset.2 hk⟩))
      rw [hk, zero_smul]
    rw [h0]
    simp
  rw [hl, hr]
  calc ∑ p ∈ Fs, ComplexMatrix2.halfTrace ((∑ᶠ q, K q p • a q) * b p)
      = ∑ p ∈ Fs, ∑ q ∈ Q, (K q p : ℂ) * ComplexMatrix2.halfTrace (a q * b p) :=
        Finset.sum_congr rfl fun p hp => by
          rw [hw p hp, halfTrace_sum_mul]
          exact Finset.sum_congr rfl fun q _ => halfTrace_real_smul_mul _ _ _
    _ = ∑ q ∈ Q, ∑ p ∈ Fs, (K q p : ℂ) * ComplexMatrix2.halfTrace (a q * b p) := Finset.sum_comm
    _ = ∑ q ∈ Q, ComplexMatrix2.halfTrace (a q * ∑ p ∈ Fs, K q p • b p) :=
        Finset.sum_congr rfl fun q _ => by
          rw [halfTrace_mul_sum]
          exact Finset.sum_congr rfl fun p _ => (halfTrace_mul_real_smul _ _ _).symm
theorem transposeOfValues_of_kernel (R : IsSlotEvaluation S P v) (R' : IsSlotEvaluation S' P' v')
    (K : P' → P → ℝ) (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (hrow : ∀ q, {p | K q p ≠ 0}.Finite) (hcol : ∀ p, {q | K q p ≠ 0}.Finite)
    (hmem : ∀ f ∈ S.complexSubmodule, m f ∈ S'.complexSubmodule)
    (hval : ∀ f ∈ S.complexSubmodule, ∀ q, v' (m f) q = ∑ᶠ p, K q p • v f p) :
    ∀ g ∈ S'.complexSubmodule,
      PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule ∧
      ∀ p, v (PairedFunctionSpace.transposeOfValues S S' m g) p = ∑ᶠ q, K q p • v' g q := by
  obtain ⟨T, hT⟩ := exists_linearMap_of_kernel R R' K m hrow hmem hval
  have hC : ∀ f : S.complexSubmodule,
      (PairedFunctionSpace.linearOfValues S S' m f : S'.index → ComplexMatrix2) = m f :=
    Classical.epsilon_spec
      (p := fun T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule =>
        ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = m f) ⟨T, hT⟩
  obtain ⟨T', hT'⟩ := exists_linearMap_of_transposedKernel R R' K hcol
  have hIs : PairedFunctionSpace.IsTransposeMap (PairedFunctionSpace.linearOfValues S S' m) T' := by
    intro g f hf
    have hb : (Function.support (v f)).Finite := (R.isFinitelySupported_iff f f.2).1 hf
    rw [R.pair_eq, R'.pair_eq]
    have e1 : v (T' g) = fun p => ∑ᶠ q, K q p • v' g q := funext (hT' g)
    have e2 : v' (PairedFunctionSpace.linearOfValues S S' m f) =
        fun q => ∑ᶠ p, K q p • v f p := by
      funext q
      rw [hC, hval f f.2]
    rw [e1, e2]
    exact traceFinsumPairing_kernel_transpose K hcol _ _ hb
  have hE : PairedFunctionSpace.IsTransposeMap (PairedFunctionSpace.linearOfValues S S' m)
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m)) :=
    Classical.epsilon_spec
      (p := PairedFunctionSpace.IsTransposeMap (PairedFunctionSpace.linearOfValues S S' m))
      ⟨T', hIs⟩
  have hU : ∀ g : S'.complexSubmodule,
      v (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) g) =
        v (T' g) := by
    intro g
    funext p
    have hz : v (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) g) p -
        v (T' g) p = 0 := by
      refine eq_zero_of_halfTrace_mul_eq_zero
        (ComplexMatrix2.traceless.sub_mem (R.eval_mem _ (Subtype.property _) p)
        (R.eval_mem _ (Subtype.property _) p)) fun t ht => ?_
      obtain ⟨f, hf, hfv⟩ := R.exists_eval_eq (singleValue p t) (singleValue_mem p ht)
      have hfs : S.IsFinitelySupported f := (R.isFinitelySupported_iff f hf).2 (by
        rw [hfv]
        refine (Set.finite_singleton p).subset fun p' hp' => ?_
        by_contra hne
        exact Function.mem_support.1 hp' (singleValue_of_ne t fun h => hne (by simp [h])))
      have h1 := hE g ⟨f, hf⟩ hfs
      have h2 := hIs g ⟨f, hf⟩ hfs
      rw [R.pair_eq] at h1 h2
      have h3 := h1.trans h2.symm
      simp only [hfv, traceFinsumPairing_singleValue] at h3
      rw [halfTrace_sub_mul, h3, sub_self]
    exact sub_eq_zero.1 hz
  intro g hg
  have hdef : PairedFunctionSpace.transposeOfValues S S' m g =
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) ⟨g, hg⟩ :
        S.complexSubmodule).1 :=
    dif_pos hg
  rw [hdef]
  refine ⟨Subtype.property _, fun p => ?_⟩
  rw [hU, hT']
end EvaluationMaps
section Slots
variable {s : ℕ} {X : TwoScaleFunctions}
def slotLift (R : CellCoordinates s X) : R.TorusSlot → X.Slot :=
  Function.surjInv R.proj_surjective
theorem proj_slotLift (R : CellCoordinates s X) (a : R.TorusSlot) : R.proj (slotLift R a) = a :=
  Function.surjInv_eq _ _
theorem proj_shiftSlot_smul (R : CellCoordinates s X) (v : Fin 4 → ℤ) (p : X.Slot) :
    R.proj (R.shiftSlot (s • v) p) = R.proj p :=
  ((R.proj_eq_iff p _).2 ⟨v, rfl⟩).symm
theorem exists_eq_shiftSlot_slotLift (R : CellCoordinates s X) (p : X.Slot) :
    ∃ v : Fin 4 → ℤ, p = R.shiftSlot (s • v) (slotLift R (R.proj p)) :=
  (R.proj_eq_iff _ _).1 (proj_slotLift R _)
theorem shiftSlot_neg_shiftSlot (R : CellCoordinates s X) (z : Fin 4 → ℤ) (p : X.Slot) :
    R.shiftSlot (-z) (R.shiftSlot z p) = p := by
  rw [← R.shiftSlot_add, neg_add_cancel, R.shiftSlot_zero]
theorem shiftSlot_shiftSlot_neg (R : CellCoordinates s X) (z : Fin 4 → ℤ) (p : X.Slot) :
    R.shiftSlot z (R.shiftSlot (-z) p) = p := by
  rw [← R.shiftSlot_add, add_neg_cancel, R.shiftSlot_zero]
def shiftSlotEquiv (R : CellCoordinates s X) (z : Fin 4 → ℤ) : X.Slot ≃ X.Slot :=
  ⟨R.shiftSlot z, R.shiftSlot (-z), shiftSlot_neg_shiftSlot R z, shiftSlot_shiftSlot_neg R z⟩
theorem eq_of_shiftSlot_smul_eq (R : CellCoordinates s X) (hs : 0 < s) {v v' : Fin 4 → ℤ}
    {p : X.Slot} (h : R.shiftSlot (s • v) p = R.shiftSlot (s • v') p) : v = v' := by
  have h0 : R.shiftSlot (-(s • v') + s • v) p = p := by
    rw [R.shiftSlot_add, h, shiftSlot_neg_shiftSlot]
  have h2 : s • v = s • v' := (neg_add_eq_zero.1 (R.eq_zero_of_shiftSlot_eq _ _ h0)).symm
  exact smul_right_injective _ hs.ne' h2
theorem slotFibre_bijective (R : CellCoordinates s X) (hs : 0 < s) :
    Function.Bijective fun x : R.TorusSlot × (Fin 4 → ℤ) =>
      R.shiftSlot (s • x.2) (slotLift R x.1) := by
  constructor
  · rintro ⟨a, v⟩ ⟨a', v'⟩ h
    have h' : R.shiftSlot (s • v) (slotLift R a) = R.shiftSlot (s • v') (slotLift R a') := h
    have ha : a = a' := by
      have h1 := congrArg R.proj h'
      rwa [proj_shiftSlot_smul, proj_shiftSlot_smul, proj_slotLift, proj_slotLift] at h1
    subst ha
    rw [eq_of_shiftSlot_smul_eq R hs h']
  · intro p
    obtain ⟨v, hv⟩ := exists_eq_shiftSlot_slotLift R p
    exact ⟨(R.proj p, v), hv.symm⟩
theorem finsum_eq_finsum_fibres {M : Type*} [AddCommMonoid M] (R : CellCoordinates s X) (hs : 0 < s)
    (F : X.Slot → M) (hF : (Function.support F).Finite) :
    ∑ᶠ p, F p = ∑ᶠ a, ∑ᶠ v, F (R.shiftSlot (s • v) (slotLift R a)) := by
  let e := Equiv.ofBijective _ (slotFibre_bijective R hs)
  rw [← finsum_comp_equiv e]
  have hsupp : (Function.support fun x => F (e x)).Finite :=
    (hF.preimage e.injective.injOn).subset fun x hx => hx
  exact finsum_curry _ hsupp
end Slots
section Kernels
variable {s : ℕ} {X Y : TwoScaleFunctions}
  {O : (X.fullSpace.index → ComplexMatrix2) → Y.fullSpace.index → ComplexMatrix2}
  {O' : (X.torusSpace.index → ComplexMatrix2) → Y.torusSpace.index → ComplexMatrix2}
theorem kernel_shift_invariant (RX : CellCoordinates s X) (RY : CellCoordinates s Y)
    (h : PeriodicOperator X Y O O') (K : Y.Slot → X.Slot → ℝ)
    (hK : ∀ f ∈ X.fullSpace.complexSubmodule, ∀ q, Y.eval (O f) q = ∑ᶠ p, K q p • X.eval f p)
    (z : Fin 4 → ℤ) (q : Y.Slot) (p : X.Slot) :
    K (RY.shiftSlot z q) (RX.shiftSlot z p) = K q p := by
  obtain ⟨f, hf, hfv⟩ :=
    RX.full_basis.exists_eval_eq (singleValue p diagBasis) (singleValue_mem p diagBasis_mem)
  have h1 : Y.eval (O (X.shift z f)) (RY.shiftSlot z q) =
      K (RY.shiftSlot z q) (RX.shiftSlot z p) • diagBasis := by
    rw [hK _ (RX.shift_mem z f hf)]
    refine Eq.trans ?_
      (finsum_smul_singleValue (K (RY.shiftSlot z q)) (RX.shiftSlot z p) diagBasis)
    refine finsum_congr fun p' => ?_
    rw [RX.eval_shift z f hf, hfv]
    congr 1
    by_cases hp : p' = RX.shiftSlot z p
    · rw [hp, shiftSlot_neg_shiftSlot, singleValue_self, singleValue_self]
    · rw [singleValue_of_ne _ hp, singleValue_of_ne]
      intro h'
      exact hp (by rw [← h', shiftSlot_shiftSlot_neg])
  have h2 : Y.eval (Y.shift z (O f)) (RY.shiftSlot z q) = K q p • diagBasis := by
    rw [RY.eval_shift z _ (h.full_mem f hf), shiftSlot_neg_shiftSlot, hK f hf, hfv,
      finsum_smul_singleValue]
  rw [h.commutes z f hf] at h1
  exact (real_smul_diagBasis_injective (h1.symm.trans h2))
theorem kernel_column_finite (RX : CellCoordinates s X) (RY : CellCoordinates s Y) (hs : 0 < s)
    (K : Y.Slot → X.Slot → ℝ) (hrow : ∀ q, {p | K q p ≠ 0}.Finite)
    (hinv : ∀ z q p, K (RY.shiftSlot z q) (RX.shiftSlot z p) = K q p) (p : X.Slot) :
    {q | K q p ≠ 0}.Finite := by
  have := RY.finite_torusSlot
  have hfin : ∀ a, {v : Fin 4 → ℤ | K (slotLift RY a) (RX.shiftSlot (-(s • v)) p) ≠ 0}.Finite := by
    intro a
    refine (hrow (slotLift RY a)).preimage
      (f := fun v : Fin 4 → ℤ => RX.shiftSlot (-(s • v)) p) ?_
    intro v _ v' _ h
    have h' : RX.shiftSlot (s • (-v)) p = RX.shiftSlot (s • (-v')) p := by
      simpa [smul_neg] using h
    exact neg_injective (eq_of_shiftSlot_smul_eq RX hs h')
  refine (Set.finite_iUnion fun a =>
    (hfin a).image fun v => RY.shiftSlot (s • v) (slotLift RY a)).subset ?_
  intro q hq
  obtain ⟨v, hv⟩ := exists_eq_shiftSlot_slotLift RY q
  refine Set.mem_iUnion.2 ⟨RY.proj q, v, ?_, hv.symm⟩
  have h1 := hinv (s • v) (slotLift RY (RY.proj q)) (RX.shiftSlot (-(s • v)) p)
  rw [← hv, shiftSlot_shiftSlot_neg] at h1
  show K _ _ ≠ 0
  rw [← h1]
  exact hq
def torusKernel (RX : CellCoordinates s X) (RY : CellCoordinates s Y) (K : Y.Slot → X.Slot → ℝ)
    (b : RY.TorusSlot) (a : RX.TorusSlot) : ℝ :=
  ∑ᶠ v : Fin 4 → ℤ, K (slotLift RY b) (RX.shiftSlot (s • v) (slotLift RX a))
theorem torusEval_of_kernel (RX : CellCoordinates s X) (RY : CellCoordinates s Y) (hs : 0 < s)
    (h : PeriodicOperator X Y O O') (K : Y.Slot → X.Slot → ℝ)
    (hrow : ∀ q, {p | K q p ≠ 0}.Finite)
    (hK : ∀ f ∈ X.fullSpace.complexSubmodule, ∀ q, Y.eval (O f) q = ∑ᶠ p, K q p • X.eval f p) :
    ∀ f ∈ X.torusSpace.complexSubmodule, ∀ b,
      RY.torusEval (O' f) b = ∑ᶠ a, torusKernel RX RY K b a • RX.torusEval f a := by
  intro f hf b
  have h1 : RY.torusEval (O' f) b = Y.eval (O (X.extend f)) (slotLift RY b) := by
    rw [h.map_extend f hf, RY.eval_extend _ (h.torus_mem f hf), proj_slotLift]
  rw [h1, hK _ (RX.extend_mem f hf)]
  have h2 : ∀ p, K (slotLift RY b) p • X.eval (X.extend f) p =
      K (slotLift RY b) p • RX.torusEval f (RX.proj p) :=
    fun p => by rw [RX.eval_extend f hf]
  simp only [h2]
  rw [finsum_eq_finsum_fibres RX hs _ (support_real_smul_finite _ (hrow _))]
  refine finsum_congr fun a => ?_
  rw [torusKernel, finsum_smul]
  refine finsum_congr fun v => ?_
  rw [proj_shiftSlot_smul, proj_slotLift]
theorem transposedKernel_eval_extend (RX : CellCoordinates s X) (RY : CellCoordinates s Y) (hs : 0 < s)
    (K : Y.Slot → X.Slot → ℝ) (hcol : ∀ p, {q | K q p ≠ 0}.Finite)
    (hinv : ∀ z q p, K (RY.shiftSlot z q) (RX.shiftSlot z p) = K q p)
    (g : Y.torusSpace.index → ComplexMatrix2) (hg : g ∈ Y.torusSpace.complexSubmodule)
    (p : X.Slot) :
    ∑ᶠ q, K q p • Y.eval (Y.extend g) q =
      ∑ᶠ b, torusKernel RX RY K b (RX.proj p) • RY.torusEval g b := by
  have h2 : ∀ q, K q p • Y.eval (Y.extend g) q =
      K q p • RY.torusEval g (RY.proj q) :=
    fun q => by rw [RY.eval_extend g hg]
  simp only [h2]
  rw [finsum_eq_finsum_fibres RY hs _ (support_real_smul_finite _ (hcol _))]
  refine finsum_congr fun b => ?_
  obtain ⟨v₀, hv₀⟩ := exists_eq_shiftSlot_slotLift RX p
  rw [torusKernel, finsum_smul]
  refine Eq.trans ?_ (finsum_comp_equiv (Equiv.subLeft v₀) (f := fun v =>
    K (slotLift RY b) (RX.shiftSlot (s • v) (slotLift RX (RX.proj p))) • RY.torusEval g b))
  refine finsum_congr fun v => ?_
  rw [proj_shiftSlot_smul, proj_slotLift]
  have h3 := hinv (s • v) (slotLift RY b)
    (RX.shiftSlot (s • (v₀ - v)) (slotLift RX (RX.proj p)))
  rw [← RX.shiftSlot_add, ← smul_add, add_sub_cancel, ← hv₀] at h3
  simp only [Equiv.subLeft_apply, h3]
end Kernels
theorem periodicOperatorIsTwoScaleMap_holds : PeriodicOperatorIsTwoScaleMap := by
  intro s hs X Y RX RY O O' h
  obtain ⟨K, hrow, hK⟩ := h.realKernel
  have hinv := kernel_shift_invariant RX RY h K hK
  have hcol := kernel_column_finite RX RY hs K hrow hinv
  have := RX.finite_torusSlot
  have := RY.finite_torusSlot
  have hW := transposeOfValues_of_kernel RX.full_basis RY.full_basis K O hrow hcol
    h.full_mem hK
  have hS := transposeOfValues_of_kernel RX.torus_coordinates RY.torus_coordinates (torusKernel RX RY K) O'
    (fun _ => Set.toFinite _) (fun _ => Set.toFinite _) h.torus_mem
    (torusEval_of_kernel RX RY hs h K hrow hK)
  refine
    { map_extend := h.map_extend
      transpose_map_extend := ?_
      commutes := h.commutes
      transpose_commutes := ?_
      realKernel := h.realKernel
      transpose_realKernel := ⟨fun p q => K q p, hcol, fun g hg p => (hW g hg).2 p⟩ }
  · intro g hg
    obtain ⟨m₁, v₁⟩ := hW _ (RY.extend_mem g hg)
    obtain ⟨m₂, v₂⟩ := hS g hg
    refine RX.full_basis.eq_of_eval_eq _ m₁ _ (RX.extend_mem _ m₂) ?_
    funext p
    rw [v₁, RX.eval_extend _ m₂, v₂]
    exact transposedKernel_eval_extend RX RY hs K hcol hinv g hg p
  · intro z g hg
    obtain ⟨m₁, v₁⟩ := hW _ (RY.shift_mem z g hg)
    obtain ⟨m₂, v₂⟩ := hW g hg
    refine RX.full_basis.eq_of_eval_eq _ m₁ _ (RX.shift_mem z _ m₂) ?_
    funext p
    rw [v₁, RX.eval_shift z _ m₂, v₂]
    refine Eq.trans ?_ (finsum_comp_equiv (shiftSlotEquiv RY (-z)) (f := fun q =>
      K q (RX.shiftSlot (-z) p) • Y.eval g q))
    refine finsum_congr fun q => ?_
    rw [RY.eval_shift z g hg]
    show _ = K (RY.shiftSlot (-z) q) (RX.shiftSlot (-z) p) • Y.eval g (RY.shiftSlot (-z) q)
    rw [hinv]
end Tower.UnitScale.OneStepChart.FromPeriodic
end YangMills.Construction
end
