import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.FourKernelsOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.HessianOfTheWilsonAction
import YangMills.Construction.Towers.TheMassiveJetsProof
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocal
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ThreeLocalOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.Coordinates
open YangMills.Construction.Matrices
section Generic
open Classical
variable {F : PeriodicData}
structure IsFinitaryEntire (G : (F.Carrier → ℂ) → ℂ) : Prop where
  finite_support : ∃ A : Finset F.Carrier, ∀ ζ ζ' : F.Carrier → ℂ, (∀ κ ∈ A, ζ κ = ζ' κ) → G ζ = G ζ'
  continuous : Continuous G
  entire_update : ∀ (ζ : F.Carrier → ℂ) (κ : F.Carrier),
    Differentiable ℂ fun t : ℂ => G (Function.update ζ κ t)
namespace IsFinitaryEntire
theorem const (c : ℂ) : IsFinitaryEntire (F := F) fun _ => c :=
  ⟨⟨∅, fun _ _ _ => rfl⟩, continuous_const, fun _ _ => differentiable_const c⟩
theorem add {G G' : (F.Carrier → ℂ) → ℂ} (h : IsFinitaryEntire G)
    (h' : IsFinitaryEntire G') : IsFinitaryEntire fun ζ => G ζ + G' ζ := by
  obtain ⟨A, hA⟩ := h.finite_support
  obtain ⟨A', hA'⟩ := h'.finite_support
  refine ⟨⟨A ∪ A', fun ζ ζ' e => ?_⟩, h.continuous.add h'.continuous, fun ζ κ =>
    (h.entire_update ζ κ).add (h'.entire_update ζ κ)⟩
  rw [hA ζ ζ' fun κ hκ => e κ (Finset.mem_union_left _ hκ),
    hA' ζ ζ' fun κ hκ => e κ (Finset.mem_union_right _ hκ)]
theorem mul {G G' : (F.Carrier → ℂ) → ℂ} (h : IsFinitaryEntire G)
    (h' : IsFinitaryEntire G') : IsFinitaryEntire fun ζ => G ζ * G' ζ := by
  obtain ⟨A, hA⟩ := h.finite_support
  obtain ⟨A', hA'⟩ := h'.finite_support
  refine ⟨⟨A ∪ A', fun ζ ζ' e => ?_⟩, h.continuous.mul h'.continuous, fun ζ κ =>
    (h.entire_update ζ κ).mul (h'.entire_update ζ κ)⟩
  rw [hA ζ ζ' fun κ hκ => e κ (Finset.mem_union_left _ hκ),
    hA' ζ ζ' fun κ hκ => e κ (Finset.mem_union_right _ hκ)]
theorem sum {X : Type} (M : Finset X) {G : X → (F.Carrier → ℂ) → ℂ}
    (h : ∀ m ∈ M, IsFinitaryEntire (G m)) :
    IsFinitaryEntire fun ζ => ∑ m ∈ M, G m ζ := by
  induction M using Finset.induction_on with
  | empty => simpa using const (F := F) 0
  | insert m M hm ih =>
    have e : (fun ζ => ∑ x ∈ insert m M, G x ζ) = fun ζ => G m ζ + ∑ x ∈ M, G x ζ :=
      funext fun ζ => Finset.sum_insert hm
    rw [e]
    exact (h m (Finset.mem_insert_self _ _)).add
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))
theorem of_fieldValues {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) {h : ComplexCoordinates l → ℂ}
    (hh : IsEntireFn h) :
    IsFinitaryEntire fun ζ : F.Carrier → ℂ => h (fieldValues e ζ) := by
  have hcont : Continuous h := by
    have h1 := continuousOn_univ.1 hh.2.2.1
    exact (continuous_apply (0 : Fin 1)).comp h1
  refine ⟨⟨Finset.univ.image fun j => ((e j : S) : F.Carrier), fun ζ ζ' c => ?_⟩,
    hcont.comp (continuous_pi fun j => continuous_apply _), fun ζ κ t₀ => ?_⟩
  · have : fieldValues e ζ = fieldValues e ζ' :=
      funext fun j => c _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rw [this]
  · by_cases hκ : κ ∈ S
    · set j := e.symm ⟨κ, hκ⟩ with hj
      have hej : ((e j : S) : F.Carrier) = κ := by simp [hj]
      set a := fieldValues e (Function.update ζ κ t₀) with ha
      have hval : ∀ t : ℂ, fieldValues e (Function.update ζ κ t) =
          a + (t - t₀) • ComplexCoordinates.stdBasisVector j := by
        intro t
        funext i
        by_cases hi : i = j
        · subst hi
          simp [ha, fieldValues, hej, ComplexCoordinates.stdBasisVector]
        · have hne : ((e i : S) : F.Carrier) ≠ κ := by
            intro c
            apply hi
            apply e.injective
            apply Subtype.ext
            rw [c, hej]
          simp [ha, fieldValues, Function.update_of_ne hne, ComplexCoordinates.stdBasisVector,
            Pi.single_eq_of_ne hi]
      have h0 := (hh.2.2.2 a (mem_univ _) j).self_of_nhds
      have h1 : DifferentiableAt ℂ
          (fun s : ℂ => h (a + s • ComplexCoordinates.stdBasisVector j)) 0 :=
        differentiableAt_pi.1 h0 0
      have h2 : DifferentiableAt ℂ (fun t : ℂ => t - t₀) t₀ := by fun_prop
      have h3 : DifferentiableAt ℂ
          (fun s : ℂ => h (a + s • ComplexCoordinates.stdBasisVector j)) ((fun t : ℂ => t - t₀) t₀) := by
        simpa using h1
      have h4 : DifferentiableAt ℂ
          ((fun s : ℂ => h (a + s • ComplexCoordinates.stdBasisVector j)) ∘ fun t : ℂ => t - t₀) t₀ :=
        DifferentiableAt.comp (f := fun t : ℂ => t - t₀) t₀ h3 h2
      have e4 : (fun t : ℂ => h (fieldValues e (Function.update ζ κ t))) =
          (fun s : ℂ => h (a + s • ComplexCoordinates.stdBasisVector j)) ∘ fun t : ℂ => t - t₀ :=
        funext fun t => by simp only [Function.comp, hval]
      rw [e4]
      exact h4
    · have hval : ∀ t : ℂ, fieldValues e (Function.update ζ κ t) = fieldValues e ζ := by
        intro t
        funext i
        have hne : ((e i : S) : F.Carrier) ≠ κ := fun c => hκ (c ▸ (e i).2)
        simp [fieldValues, Function.update_of_ne hne]
      simp only [hval]
      exact differentiableAt_const _
theorem fieldExtend_apply_index {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (z : ComplexCoordinates l)
    (j : Fin l) : fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem fieldExtend_of_not_mem {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (z : ComplexCoordinates l)
    {κ : F.Carrier} (hκ : κ ∉ S) : fieldExtend e z κ = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_of_notMem <;> assumption
theorem exists_fieldValues {G : (F.Carrier → ℂ) → ℂ} (hG : IsFinitaryEntire G) (κ₀ : F.Carrier) :
    ∃ (S : Set F.Carrier) (l : ℕ) (e : Fin l ≃ S) (h : ComplexCoordinates l → ℂ),
      IsEntireFn h ∧ ∀ ζ, G ζ = h (fieldValues e ζ) := by
  obtain ⟨A, hA⟩ := hG.finite_support
  set A' := insert κ₀ A with hA'
  let e : Fin A'.card ≃ ((A' : Set F.Carrier)) :=
    A'.equivFin.symm.trans (Equiv.subtypeEquivRight fun _ => by simp)
  have hsurj : ∀ κ ∈ A', ∃ j, ((e j : (A' : Set F.Carrier)) : F.Carrier) = κ := by
    intro κ hκ
    refine ⟨e.symm ⟨κ, by simpa using hκ⟩, by simp⟩
  have hcont : Continuous fun z : ComplexCoordinates A'.card => fieldExtend e z := by
    refine continuous_pi fun κ => ?_
    by_cases hκ : κ ∈ A'
    · obtain ⟨j, rfl⟩ := hsurj κ hκ
      simp only [fieldExtend_apply_index]
      exact continuous_apply j
    · have hκ' : κ ∉ (A' : Set F.Carrier) := by simpa using hκ
      simp only [fieldExtend_of_not_mem e _ hκ']
      exact continuous_const
  refine ⟨A', A'.card, e, fun z => G (fieldExtend e z), ⟨?_, isOpen_univ, ?_, ?_⟩, fun ζ => ?_⟩
  · exact Finset.card_pos.2 ⟨κ₀, Finset.mem_insert_self _ _⟩
  · exact (continuous_pi fun _ => hG.continuous.comp hcont).continuousOn
  · intro a _ j
    refine Eventually.of_forall fun s => differentiableAt_pi.2 fun _ => ?_
    have hform : ∀ s : ℂ, fieldExtend e (a + s • ComplexCoordinates.stdBasisVector j) =
        Function.update (fieldExtend e a) ((e j : (A' : Set F.Carrier)) : F.Carrier) (a j + s) := by
      intro s
      funext κ
      by_cases hκ : κ ∈ A'
      · obtain ⟨i, rfl⟩ := hsurj κ hκ
        by_cases hi : i = j
        · subst hi
          rw [fieldExtend_apply_index, Function.update_self]
          simp [ComplexCoordinates.stdBasisVector]
        · have hne : ((e i : (A' : Set F.Carrier)) : F.Carrier) ≠ ((e j : (A' : Set F.Carrier)) : F.Carrier) :=
            fun c => hi (e.injective (Subtype.ext c))
          rw [fieldExtend_apply_index, Function.update_of_ne hne, fieldExtend_apply_index]
          simp [ComplexCoordinates.stdBasisVector, Pi.single_eq_of_ne hi]
      · have hκ' : κ ∉ (A' : Set F.Carrier) := by simpa using hκ
        have hne : κ ≠ ((e j : (A' : Set F.Carrier)) : F.Carrier) := fun c => hκ' (c ▸ (e j).2)
        rw [fieldExtend_of_not_mem e _ hκ', Function.update_of_ne hne,
          fieldExtend_of_not_mem e _ hκ']
    simp only [hform]
    have h1 : DifferentiableAt ℂ (fun s : ℂ => a j + s) s := by fun_prop
    exact ((hG.entire_update _ _) _).comp s h1
  · refine hA _ _ fun κ hκ => ?_
    obtain ⟨j, rfl⟩ := hsurj κ (Finset.mem_insert_of_mem hκ)
    rw [fieldExtend_apply_index]
    rfl
theorem eq_zero {G : (F.Carrier → ℂ) → ℂ} (hG : IsFinitaryEntire G) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ ζ : F.Carrier → ℂ, (∀ κ, ‖ζ κ‖ ≤ r) → G ζ = 0) (ζ : F.Carrier → ℂ) : G ζ = 0 := by
  have key : ∀ B : Finset F.Carrier, ∀ ζ : F.Carrier → ℂ, (∀ κ, κ ∉ B → ‖ζ κ‖ ≤ r) → G ζ = 0 := by
    intro B
    induction B using Finset.induction_on with
    | empty => exact fun ζ h => h0 ζ fun κ => h κ (Finset.notMem_empty κ)
    | insert κ B _ ih =>
      intro ζ h
      have han : AnalyticOnNhd ℂ (fun t : ℂ => G (Function.update ζ κ t)) univ :=
        (hG.entire_update ζ κ).differentiableOn.analyticOnNhd isOpen_univ
      have hnear : (fun t : ℂ => G (Function.update ζ κ t)) =ᶠ[𝓝 (0 : ℂ)] 0 := by
        filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with t ht
        refine ih _ fun κ' hκ' => ?_
        by_cases c : κ' = κ
        · subst c
          simpa using ht
        · rw [Function.update_of_ne c]
          exact h κ' fun m => (Finset.mem_insert.1 m).elim c hκ'
      have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ 0) hnear
      have := hall (mem_univ (ζ κ))
      simpa using this
  obtain ⟨A, hA⟩ := hG.finite_support
  rw [hA ζ (fun κ => if κ ∈ A then ζ κ else 0) fun κ hκ => by simp [hκ]]
  refine key A _ fun κ hκ => ?_
  simp [hκ, hr.le]
end IsFinitaryEntire
end Generic
section Kernels
variable {F I I' I'' : PeriodicData}
def IsLocalEntireOpFun (F I I' : PeriodicData) (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsLocalOpFun F I I' T ∧
    ∀ ι' ι, IsFinitaryEntire fun ζ => T ζ ι' ι
theorem IsLocalEntireOpFun.congr {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (h : IsLocalEntireOpFun F I I' T) (e : ∀ ζ, T' ζ = T ζ) : IsLocalEntireOpFun F I I' T' := by
  rw [funext e]
  exact h
theorem entries_of_hasEntireKernelEntries {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (h : HasEntireKernelEntries F I I' T) (ι' : I'.Carrier) (ι : I.Carrier) :
    IsFinitaryEntire fun ζ => T ζ ι' ι := by
  obtain ⟨S, l, e, f, hf, hT⟩ := h ι' ι
  have e' : (fun ζ => T ζ ι' ι) = fun ζ => f (fieldValues e ζ) := funext hT
  rw [e']
  exact IsFinitaryEntire.of_fieldValues e hf
theorem hasEntireKernelEntries_of_entries (κ₀ : F.Carrier) {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (h : ∀ ι' ι, IsFinitaryEntire fun ζ => T ζ ι' ι) : HasEntireKernelEntries F I I' T :=
  fun ι' ι => (h ι' ι).exists_fieldValues κ₀
theorem entry_eq_zero_of_far {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hm : IsLocalWith F I I' T ρ R) {ι' : I'.Carrier} {ι : I.Carrier}
    (he : IsFinitaryEntire fun ζ => T ζ ι' ι)
    (hd : ¬ euclidNormVec (I.pos ι - I'.pos ι') ≤ R) (ζ : F.Carrier → ℂ) : T ζ ι' ι = 0 :=
  he.eq_zero (half_pos hm.radius_pos)
    (fun ζ hζ => hm.vanish_far ζ ⟨_, half_lt_self hm.radius_pos, hζ⟩ ι' ι hd) ζ
theorem isLocalEntireOpFun_add (hFacts : JetDomains.OpFunJetTheory)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (h : IsLocalEntireOpFun F I I' T)
    (h' : IsLocalEntireOpFun F I I' T') : IsLocalEntireOpFun F I I' (opFunAdd T T') :=
  ⟨(hFacts.1 F I I' I hF hI hI' hI).1 T T' h.1 h'.1, fun ι' ι => (h.2 ι' ι).add (h'.2 ι' ι)⟩
theorem isLocalEntireOpFun_transpose (hFacts : JetDomains.OpFunJetTheory)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (h : IsLocalEntireOpFun F I I' T) :
    IsLocalEntireOpFun F I' I (opFunTranspose T) :=
  ⟨(hFacts.1 F I I' I hF hI hI' hI).2.2 T h.1, fun ι ι' =>
    (IsFinitaryEntire.const _).mul (h.2 ι' ι)⟩
theorem isLocalEntireOpFun_comp (hFacts : JetDomains.OpFunJetTheory)
    (hFin : CovariantFiniteRange.Claim) (hF : IsPeriodic F)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ}
    (h : IsLocalEntireOpFun F I I' T) (h' : IsLocalEntireOpFun F I'' I S) :
    IsLocalEntireOpFun F I'' I' (opFunComp T S) := by
  refine ⟨(hFacts.1 F I I' I'' hF hI hI' hI'').2.1 T S h.1 h'.1, fun ι' ι'' => ?_⟩
  obtain ⟨ρ, R, hm⟩ := h.1
  have hfin := (hFin.1 I hI).1 (I'.pos ι') R
  have e : (fun ζ => opFunComp T S ζ ι' ι'') =
      fun ζ => ∑ m ∈ hfin.toFinset, T ζ ι' m * S ζ m ι'' := by
    funext ζ
    refine tsum_eq_sum fun m hm' => ?_
    have hd : ¬ euclidNormVec (I.pos m - I'.pos ι') ≤ R := by
      simpa [nearIndices] using hm'
    rw [entry_eq_zero_of_far hm (h.2 ι' m) hd ζ, zero_mul]
  rw [e]
  exact IsFinitaryEntire.sum _ fun m _ => (h.2 ι' m).mul (h'.2 m ι'')
theorem isLocalEntireOpFun_const
    (hConst : ConstantOpFun.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hP : IsPeriodicKernel I I' T) (hR : IsFiniteRange I I' T) :
    IsLocalEntireOpFun F I I'
      (ConstantOpFun.constAssign F T) :=
  ⟨(hConst F I I' hF hI hI' T hP hR 1 0 one_pos (by simp [imStrip]) 0 0).1.1,
    fun _ _ => IsFinitaryEntire.const _⟩
end Kernels
theorem finestMesh_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_pos <;> assumption
theorem ofCoeffs_mem_complexEdgeForms {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : (edgePauliCoordinates L k 0).Index → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs c ∈ complexEdgeForms (meshAt L k 0) := by
  classical
  have ha : 0 < meshAt L k 0 := finestMesh_pos hL k
  have hmem : ∀ b : (edgePauliCoordinates L k 0).Place, ofPauliCoeffs c b ∈ ComplexMatrix2.traceless := fun b =>
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (by
      show Matrix.trace (ComplexMatrix2.pauliFamily a) = 0
      fin_cases a <;>
        simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
          OneLoop.pauliZ, Matrix.trace_fin_two])
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · show (if b.IsPositivelyOriented then _ else _) ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [if_pos hb, dif_pos hb]
    exact hmem _
  · show (if b.opposite.IsPositivelyOriented then _ else _) = -(if b.IsPositivelyOriented then _ else _)
    by_cases h : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented := fun hr =>
        InfiniteLattice.opposite_notMem_positiveLinks ha
          (InfiniteLattice.mem_positiveLinks_iff.2 h)
          (InfiniteLattice.mem_positiveLinks_iff.2 hr)
      rw [if_neg hr, if_pos h]
      rfl
    · have hr : b.opposite.IsPositivelyOriented :=
        ((InfiniteLattice.mem_positiveLinks_or_opposite_mem b).resolve_left
          fun m => h (InfiniteLattice.mem_positiveLinks_iff.1 m)) |>
          InfiniteLattice.mem_positiveLinks_iff.1
      rw [if_pos hr, if_neg h, neg_neg]
theorem exists_complexForm {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    ∃ a ∈ complexEdgeForms (meshAt L k 0), remainderGaugeField a = gaugeFieldOfForm L k ζ := by
  have hη := (finestMesh_pos hL k).ne'
  refine ⟨(((finestMesh L k)⁻¹ : ℝ) : ℂ) • (edgePauliCoordinates L k 0).ofCoeffs ζ,
    Submodule.smul_mem _ _ (ofCoeffs_mem_complexEdgeForms hL ζ), ?_⟩
  have e : scaledRemainderForm ((((finestMesh L k)⁻¹ : ℝ) : ℂ) • (edgePauliCoordinates L k 0).ofCoeffs ζ) =
      (edgePauliCoordinates L k 0).ofCoeffs ζ := by
    funext b
    show finestMesh L k • ((((finestMesh L k)⁻¹ : ℝ) : ℂ) • (edgePauliCoordinates L k 0).ofCoeffs ζ b) = _
    rw [Complex.coe_smul, smul_smul, mul_inv_cancel₀ hη, one_smul]
  show expForm (scaledRemainderForm _) = expForm _
  rw [e]
theorem localEntireOperators (hFour : ScaledKernelsLocal.FourKernelsLocal)
    (hHessian : WilsonHessian.DecompositionHolds)
    (hFacts : JetDomains.OpFunJetTheory)
    (hConst : ConstantOpFun.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hFin : CovariantFiniteRange.Claim)
    (hIndex : TowerIndexSets.Claim) : LocalEntireOperators := by
  intro L hL k hk
  obtain ⟨hS, hB, hP⟩ := hIndex L hL k 0 (Nat.zero_le k)
  have hF : IsPeriodic (remainderIndex L k) := hB
  obtain ⟨hD, hE, hZ, hC⟩ := hFour L hL k hk
  let κ₀ : (remainderIndex L k).Carrier := (0, Classical.arbitrary _)
  have toLocal : ∀ {I I' : PeriodicData} {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ},
      IsLocalEntire L k I I' T → IsLocalEntireOpFun (remainderIndex L k) I I' T :=
    fun h => ⟨h.1, entries_of_hasEntireKernelEntries h.2⟩
  have ofLocal : ∀ {I I' : PeriodicData} {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ},
      IsLocalEntireOpFun (remainderIndex L k) I I' T → IsLocalEntire L k I I' T :=
    fun h => ⟨h.1, hasEntireKernelEntries_of_entries κ₀ h.2⟩
  have hd := ((hFree.2 L hL k hk).1.edgeCoboundary 0 (Nat.zero_le k)).finite_range
  have hDifference := isLocalEntireOpFun_const (F := remainderIndex L k) hConst hF hB hP hd.1 hd.2.1
  have hSum := isLocalEntireOpFun_add hFacts hF hB hP hDifference (toLocal hE)
  have hSumT := isLocalEntireOpFun_transpose hFacts hF hB hP hSum
  have hSquare := isLocalEntireOpFun_comp hFacts hFin hF hP hB hB hSumT
    (isLocalEntireOpFun_comp hFacts hFin hF hP hP hB (toLocal hZ) hSum)
  have hH₀ := isLocalEntireOpFun_add hFacts hF hB hB hSquare (toLocal hC)
  have hDl := toLocal hD
  have hDt := isLocalEntireOpFun_transpose hFacts hF hS hB hDl
  have hDDt := isLocalEntireOpFun_comp hFacts hFin hF hS hB hB hDl hDt
  have hDtD := isLocalEntireOpFun_comp hFacts hFin hF hB hS hS hDt hDl
  have hH : IsLocalEntireOpFun (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
      (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).H) :=
    hH₀.congr fun ζ => by
      obtain ⟨a, ha, hc⟩ := exists_complexForm hL ζ
      have h2 := (hHessian L hL k hk).2 a ha
      rw [hc] at h2
      exact h2
  have hK := isLocalEntireOpFun_add hFacts hF hB hB hH hDDt
  exact ⟨ofLocal hH, ofLocal hK, ofLocal hDtD⟩
end YangMills.Construction.Tower.FullSpace.ThreeLocalOperators
end
