import YangMills.Construction.EuclideanFunctionals.BoundedMapFromADenseSubspaceExtends
import YangMills.Construction.EuclideanFunctionals.ConcatenationIsTheTensorProductAndTheFormsInComponents
import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.EuclideanFunctionals.OneInsertionAsAnOperator
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntries
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OneInsertionOperator
open TensorCompRules (splitTerm)
theorem smul_timeVec_apply_three (c : ℝ) : (c • timeVec) 3 = c := by
  simp [PeriodicLattice.coordVec]
theorem timeFlip_neg_smul_timeVec (c : ℝ) : timeFlip ((-c) • timeVec) = c • timeVec := by
  rw [timeFlip_apply, smul_timeVec_apply_three]
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
section Motions
variable (hE : MotionMulRules.EmptyAndShiftRules)
include hE
theorem pullDown_liftOnce (c : ℝ) (F : FreeSep) :
    pullDown c (liftOnce c F) = F := by
  have h := (hE ((-c) • timeVec) (c • timeVec) F).1
  have e : (-c) • timeVec + c • timeVec = 0 := by rw [neg_smul, neg_add_cancel]
  rw [e] at h
  exact h.trans (hE 0 0 F).2.1
theorem liftOnce_pullDown (c : ℝ) (F : FreeSep) :
    liftOnce c (pullDown c F) = F := by
  have h := (hE (c • timeVec) ((-c) • timeVec) F).1
  have e : c • timeVec + (-c) • timeVec = 0 := by rw [neg_smul, add_neg_cancel]
  rw [e] at h
  exact h.trans (hE 0 0 F).2.1
end Motions
section Heights
variable (hA : MotionMulRules.FinCombAboveLevel)
include hA
theorem liftOnce_mem (c : ℝ) {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    liftOnce c F ∈ finCombIn {x | c < x 3} := by
  have h := (hA (c • timeVec) 0 F hF).1
  rw [smul_timeVec_apply_three, zero_add] at h
  exact h
theorem liftTwice_mem (c : ℝ) {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    liftTwice c F ∈ finCombIn {x | 2 * c < x 3} := by
  have h := (hA ((2 * c) • timeVec) 0 F hF).1
  rw [smul_timeVec_apply_three, zero_add] at h
  exact h
theorem pullDown_mem (c : ℝ) {F : FreeSep} (hF : F ∈ finCombIn {x | c < x 3}) :
    pullDown c F ∈ finCombIn upperHalf := by
  have h := (hA ((-c) • timeVec) c F hF).1
  rw [smul_timeVec_apply_three, add_neg_cancel] at h
  exact h
end Heights
theorem isOpen_timeSlab (c : ℝ) : IsOpen {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} :=
  (isOpen_lt continuous_const (continuous_apply 3)).inter
    (isOpen_lt (continuous_apply 3) continuous_const)
theorem isOpen_timeNeg : IsOpen {x : R4 | x 3 < 0} :=
  isOpen_lt (continuous_apply 3) continuous_const
theorem isOpen_timeGt (c : ℝ) : IsOpen {x : R4 | c < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem liftComponent_mem (hP : TupleRules.ReImAndMotionOfFns) (m : SharpScale)
    (c : ℝ) {h : R4 → ℂ} (hh : h ∈ C1c ℂ) :
    liftComponent c h ∈ C1c ℂ :=
  (hP m (EuclidMotion.transl (c • timeVec)) 1 h hh).2.2.2.1
theorem supp_liftFn_subset (hP : TupleRules.ReImAndMotionOfFns) (m : SharpScale)
    {c : ℝ} {h : R4 → ℂ} (hh : h ∈ C1c ℂ)
    (hs : supp h ⊆ {x | |x 3| < c}) :
    supp (liftComponent c h) ⊆ {x | 0 < x 3 ∧ x 3 < 2 * c} := by
  intro x hx
  have e := (hP m (EuclidMotion.transl (c • timeVec)) 1 h hh).2.2.2.2.1
  rw [liftComponent, e] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy₀ : |y 3| < c := hs hy
  have hy' := abs_lt.1 hy₀
  have e' : (y + c • timeVec) 3 = y 3 + c := by
    rw [Pi.add_apply, smul_timeVec_apply_three]
  change 0 < (y + c • timeVec) 3 ∧ (y + c • timeVec) 3 < 2 * c
  rw [e']
  constructor <;> linarith [hy'.1, hy'.2]
theorem singleInsertion_props (hT : MotionMulRules.ComplexTupleRules)
    {g : R4 → ℂ} (hg : g ∈ C1c ℂ) {O : Set R4} (hO : IsOpen O)
    (hs : supp g ⊆ O) :
    singleComponent g ∈ finCombIn O ∧
    tensorComp 1 (singleComponent g) = tensorOfFns (fun _ : Fin 1 => g) ∧
    tensorCompZero (singleComponent g) = 0 ∧
    (∀ q, 1 ≤ q → q ≠ 1 → tensorComp q (singleComponent g) = 0) ∧
    ∀ z : R4, (EuclidMotion.transl z).actFree (singleComponent g) =
      singleComponent ((EuclidMotion.transl z).actFn g) :=
  hT 1 (fun _ => g) O ⟨le_rfl, fun _ => hg, fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩ hO
    (fun _ => hs)
theorem tensorComp_freeMul_singleEntry
    (hC : MulTensor.MulComponents)
    {G A : FreeSep} {g : R4 → ℂ} (D : MulDefined G A)
    (T₁ : tensorComp 1 G = tensorOfFns (fun _ : Fin 1 => g))
    (T₀ : tensorCompZero G = 0)
    (Tq : ∀ q, 1 ≤ q → q ≠ 1 → tensorComp q G = 0) (q : ℕ) :
    tensorComp (q + 1) (freeMul G A) = headTensor g (tensorComp q A) := by
  have e₁ : ∀ y, tensorComp 1 G y = g (y 0) := fun y => by
    rw [T₁, tensorOfFns_apply]
    simp
  have key : ∀ k : Fin (q + 1 + 1), k ≠ ⟨1, by omega⟩ → splitTerm G A (q + 1) k = 0 := by
    intro k hk
    have hk' : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
    by_cases k0 : (k : ℕ) = 0
    · rw [splitTerm, if_pos k0, T₀]
      funext x
      simp [TestSpaces.scalarTensorLeft]
    by_cases kn : (k : ℕ) = q + 1
    · rw [splitTerm, if_neg k0, if_pos kn, Tq (q + 1) (by omega) (by omega)]
      funext x
      simp [TestSpaces.scalarTensorRight]
    · rw [splitTerm, if_neg k0, if_neg kn, Tq k (by omega) hk']
      funext x
      simp [TestSpaces.tensorFun]
  rw [(hC G A D).2.1 (q + 1) (by omega), Fintype.sum_eq_single _ key]
  funext x
  rcases q with _ | q
  · rw [splitTerm, if_neg (by simp), if_pos (by simp)]
    change tensorCompZero A * tensorComp 1 G x =
      g (x 0) * tensorComp 0 A fun l => x l.succ
    rw [e₁, tensorComp_zero_apply, mul_comm]
  · rw [splitTerm, if_neg (by simp), if_neg (by simp)]
    change tensorComp 1 G _ * tensorComp (q + 1) A _ =
      g (x 0) * tensorComp (q + 1) A fun l => x l.succ
    rw [e₁]
    refine congrArg₂ (· * ·) (congrArg g (congrArg x (Fin.ext ?_)))
      (congrArg _ (funext fun l => congrArg x (Fin.ext ?_)))
    · rfl
    · change 1 + (l : ℕ) = (l : ℕ) + 1
      omega
theorem tensorComp_actFree_transl (hAct : TupleRules.MotionOnFree) (z : R4)
    (A : FreeSep) (q : ℕ) :
    tensorComp q ((EuclidMotion.transl z).actFree A) =
      translateArgs z (tensorComp q A) := by
  rcases q with _ | q
  · funext e
    rw [translateArgs_zero, tensorComp_zero_apply, tensorComp_zero_apply]
    exact ((hAct 1 1 A).2.2.2.2.2.2.2 z).1
  · exact ((hAct 1 1 A).2.2.2.2.2.2.2 z).2 (q + 1) (by omega)
section Classes
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
theorem reconClass_of_mem {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    reconClass σ F = σ.recon.cls ⟨F, hF⟩ :=
  dif_pos hF
theorem inner_reconClass {F A : FreeSep} (hF : F ∈ finCombIn upperHalf)
    (hA : A ∈ finCombIn upperHalf) :
    ⟪reconClass σ F, reconClass σ A⟫_ℂ = osForm S F A := by
  rw [reconClass_of_mem σ hF, reconClass_of_mem σ hA]
  exact σ.recon.inner_cls _ _
end Classes
section Main
variable (hR : MotionMulRules.MotionMulTupleRules)
  (hC : MulTensor.Holds)
  (hI : MomentSymmetry.ReductionHolds)
  (hX : DenseExtension.DenseExtensionTheorem)
  (hT : TupleRules.TupleSpanActionRules)
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
  {c : ℝ} {h : R4 → ℂ}
include hR hC hI hT in
theorem inner_reconClass_prependInsertion (hc : 0 < c) (hh : h ∈ C1c ℂ)
    (hs : supp h ⊆ {x | |x 3| < c}) {F A : FreeSep}
    (hF : F ∈ finCombIn upperHalf) (hA : A ∈ finCombIn upperHalf)
    (hP : prependComponent c h A ∈ finCombIn upperHalf) :
    ⟪reconClass σ F, reconClass σ (prependComponent c h A)⟫_ℂ =
      insertion S (liftOnce c F) h (liftOnce c A) := by
  obtain ⟨hE, hTr, hThree, hTup, -, -, hMir, -, -, hAbove, -, -, -, -⟩ := hR
  obtain ⟨hParts, -, -, -, hDisj, -⟩ := hT
  have hg := liftComponent_mem hParts m c hh
  have hgs := supp_liftFn_subset hParts m hh hs
  obtain ⟨mG, -, -, -, tG⟩ := singleInsertion_props hTup hg (isOpen_timeSlab c) hgs
  have mF : flipConj F ∈ finCombIn {x | x 3 < 0} := ((hC m S σ).2.1 F hF).1
  have mA := liftTwice_mem hAbove c hA
  have d₁ : Disjoint {x : R4 | x 3 < 0} {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} :=
    Set.disjoint_left.2 fun x h₁ h₂ => absurd h₂.1 (not_lt.2 (le_of_lt h₁))
  have d₂ : Disjoint {x : R4 | x 3 < 0} {x : R4 | 2 * c < x 3} :=
    Set.disjoint_left.2 fun x (h₁ : x 3 < 0) (h₂ : 2 * c < x 3) => by linarith
  have d₃ : Disjoint {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} {x : R4 | 2 * c < x 3} :=
    Set.disjoint_left.2 fun x h₁ (h₂ : 2 * c < x 3) => by linarith [h₁.2]
  have D₁ := ((hDisj _ _ isOpen_timeNeg (isOpen_timeSlab c) d₁).1 _ mF _ mG).1
  have D₂ := ((hDisj _ _ isOpen_timeNeg (isOpen_timeGt _) d₂).1 _ mF _ mA).1
  have D₃ := ((hDisj _ _ (isOpen_timeSlab c) (isOpen_timeGt _) d₃).1 _ mG _ mA).1
  obtain ⟨d₁₂, -, e₃, -⟩ := hThree _ _ _ D₁ D₂ D₃
  rw [inner_reconClass σ hF hP]
  have step : osForm S F (prependComponent c h A) =
      centeredFnFree S (freeMul (freeMul (flipConj F)
        (singleComponent (liftComponent c h))) (liftTwice c A)) := by
    rw [e₃]
    rfl
  have t₃ : (EuclidMotion.transl ((-c) • timeVec)).actFree (flipConj F) =
      flipConj (liftOnce c F) := by
    have e := hMir ((-c) • timeVec) F
    rw [timeFlip_neg_smul_timeVec] at e
    exact e
  have t₄ : (EuclidMotion.transl ((-c) • timeVec)).actFree (singleComponent (liftComponent c h)) =
      singleComponent h := by
    rw [tG]
    congr 1
    funext x
    rw [EuclidMotion.actFn_transl, liftComponent, EuclidMotion.actFn_transl]
    congr 1
    rw [neg_smul, sub_neg_eq_add, add_sub_cancel_right]
  have t₅ : (EuclidMotion.transl ((-c) • timeVec)).actFree (liftTwice c A) = liftOnce c A := by
    have e := (hE ((-c) • timeVec) ((2 * c) • timeVec) A).1
    have e' : (-c) • timeVec + (2 * c) • timeVec = c • timeVec := by
      rw [← add_smul]
      congr 1
      ring
    rw [e'] at e
    exact e
  have t₁ := (hTr ((-c) • timeVec) _ _ d₁₂).2
  have t₂ := (hTr ((-c) • timeVec) _ _ D₁).2
  rw [step, ← ((hI m S σ).2.1 _).1 ((-c) • timeVec)]
  refine congrArg _ (t₁.trans ?_)
  refine (congrArg₂ (fun U V => freeMul U V) (t₂.trans ?_) t₅)
  exact congrArg₂ (fun U V => freeMul U V) t₃ t₄
include hR hC hI hT in
theorem norm_reconClass_cons_le (hc : 0 < c) (hh : h ∈ C1c ℂ)
    (hs : supp h ⊆ {x | |x 3| < c}) {b : ℝ} (hb : 0 ≤ b)
    (hB : InsertionBounded σ c h b) {A : FreeSep}
    (hA : A ∈ finCombIn upperHalf)
    (hP : prependComponent c h A ∈ finCombIn upperHalf) :
    ‖reconClass σ (prependComponent c h A)‖ ≤ b * ‖reconClass σ A‖ := by
  have hE := hR.1
  have hAbove := hR.2.2.2.2.2.2.2.2.2.1
  have e := inner_reconClass_prependInsertion hR hC hI hT σ hc hh hs hP hA hP
  have hv := hB _ (liftOnce_mem hAbove c hP) _ (liftOnce_mem hAbove c hA)
  rw [← e, heightNorm, heightNorm, pullDown_liftOnce hE, pullDown_liftOnce hE] at hv
  have hn : ‖⟪reconClass σ (prependComponent c h A), reconClass σ (prependComponent c h A)⟫_ℂ‖ =
      ‖reconClass σ (prependComponent c h A)‖ * ‖reconClass σ (prependComponent c h A)‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [sq]
  rw [hn] at hv
  by_cases v0 : ‖reconClass σ (prependComponent c h A)‖ = 0
  · rw [v0]
    exact mul_nonneg hb (norm_nonneg _)
  · have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm v0)
    refine le_of_mul_le_mul_left ?_ hpos
    calc _ ≤ _ := hv
      _ = _ := by ring
theorem exists_linearMap_on_range {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (cl L : V →ₗ[ℂ] H) (hker : LinearMap.ker cl ≤ LinearMap.ker L) :
    ∃ Z₀ : LinearMap.range cl →ₗ[ℂ] H, ∀ A, Z₀ ⟨cl A, LinearMap.mem_range_self cl A⟩ = L A := by
  refine ⟨(LinearMap.ker cl).liftQ L hker ∘ₗ cl.quotKerEquivRange.symm.toLinearMap, fun A => ?_⟩
  change (LinearMap.ker cl).liftQ L hker
    (cl.quotKerEquivRange.symm ⟨cl A, LinearMap.mem_range_self cl A⟩) = L A
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl
theorem exists_linearMap_prependComponent
    (hPm : ∀ A ∈ finCombIn upperHalf,
      prependComponent c h A ∈ finCombIn upperHalf) :
    ∃ L : finCombIn upperHalf →ₗ[ℂ] σ.space,
      ∀ A, L A = reconClass σ (prependComponent c h A.1) := by
  have hPm' : ∀ A ∈ finCombIn upperHalf,
      ((freeMul (singleComponent (liftComponent c h))) ∘ₗ
        (EuclidMotion.transl ((2 * c) • timeVec)).actFree) A ∈ finCombIn upperHalf := hPm
  refine ⟨σ.recon.cls ∘ₗ LinearMap.restrict _ hPm', fun A => ?_⟩
  rw [reconClass_of_mem σ (hPm A.1 A.2)]
  rfl
include hR hC hI hX hT in
theorem exists_unique_insertionOp (hc : 0 < c) (hh : h ∈ C1c ℂ)
    (hs : supp h ⊆ {x | |x 3| < c}) {b : ℝ} (hb : 0 ≤ b)
    (hB : InsertionBounded σ c h b)
    (hPm : ∀ A ∈ finCombIn upperHalf,
      prependComponent c h A ∈ finCombIn upperHalf) :
    ∃ Z : σ.space →L[ℂ] σ.space, ActsOnReconClasses σ c h Z ∧
      (∀ Z' : σ.space →L[ℂ] σ.space, ActsOnReconClasses σ c h Z' → Z' = Z) ∧
      ‖Z‖ ≤ b := by
  obtain ⟨L, hL⟩ := exists_linearMap_prependComponent σ hPm
  obtain ⟨cl, hcl₀⟩ : ∃ cl, cl = σ.recon.cls := ⟨_, rfl⟩
  have hcl : ∀ A : finCombIn upperHalf, cl A = reconClass σ A.1 := fun A => by
    rw [hcl₀]
    exact (reconClass_of_mem σ A.2).symm
  have hLb : ∀ A : finCombIn upperHalf, ‖L A‖ ≤ b * ‖cl A‖ := fun A => by
    rw [hL, hcl]
    exact norm_reconClass_cons_le hR hC hI hT σ hc hh hs hb hB A.2 (hPm A.1 A.2)
  have hker : LinearMap.ker cl ≤ LinearMap.ker L := fun A hA => by
    have h₀ : cl A = 0 := hA
    have h₁ := hLb A
    rw [h₀, norm_zero, mul_zero] at h₁
    exact norm_le_zero_iff.1 h₁
  obtain ⟨Z₀, hZ₀⟩ := exists_linearMap_on_range (V := finCombIn upperHalf)
    (H := σ.space) cl L (by exact hker)
  have hdense : Dense ((LinearMap.range cl : Submodule ℂ σ.space) : Set σ.space) := by
    rw [LinearMap.coe_range, hcl₀]
    exact σ.recon.denseRange_cls
  have hbound : ∀ ψ : LinearMap.range cl, ‖Z₀ ψ‖ ≤ b * ‖(ψ : σ.space)‖ := by
    rintro ⟨_, A, rfl⟩
    rw [hZ₀]
    exact hLb A
  obtain ⟨Z, hZ, hU, hN⟩ := hX m S σ (LinearMap.range cl) b Z₀ hdense hb hbound
  have hZA : ActsOnReconClasses σ c h Z := fun A hA => by
    have e := hZ ⟨cl ⟨A, hA⟩, LinearMap.mem_range_self cl _⟩
    rw [hZ₀, hL] at e
    rw [← hcl ⟨A, hA⟩]
    exact e
  refine ⟨Z, hZA, fun Z' hZ' => hU Z' ?_, hN⟩
  rintro ⟨_, A, rfl⟩
  rw [hZ₀, hL]
  have e := hZ' A.1 A.2
  rw [← hcl] at e
  exact e
theorem statement_holds (hR : MotionMulRules.MotionMulTupleRules)
    (hC : MulTensor.Holds)
    (hI : MomentSymmetry.ReductionHolds)
    (hX : DenseExtension.DenseExtensionTheorem)
    (hT : TupleRules.TupleSpanActionRules) : statement := by
  intro m S σ c h b hc hh hs hb hB
  have hE := hR.1
  have hAbove := hR.2.2.2.2.2.2.2.2.2.1
  have hOne := (hR.2.2.2.2.2.2.2.2.2.2.1 c hc h hh hs)
  have hPm : ∀ A ∈ finCombIn upperHalf,
      prependComponent c h A ∈ finCombIn upperHalf := fun A hA => (hOne.1 A hA).2
  have hDef : ∀ A ∈ finCombIn upperHalf,
      MulDefined (singleComponent (liftComponent c h)) (liftTwice c A) :=
    fun A hA => (hOne.1 A hA).1
  have hParts := hT.1
  have hg := liftComponent_mem hParts m c hh
  have hgs := supp_liftFn_subset hParts m hh hs
  obtain ⟨-, T₁, T₀, Tq, -⟩ := singleInsertion_props hR.2.2.2.1 hg (isOpen_timeSlab c) hgs
  have hSucc : ∀ A ∈ finCombIn upperHalf, ∀ q : ℕ,
      tensorComp (q + 1) (prependComponent c h A) =
        headTensor (liftComponent c h) (translateArgs ((2 * c) • timeVec) (tensorComp q A)) := by
    intro A hA q
    rw [prependComponent, tensorComp_freeMul_singleEntry (hC m S σ).1 (hDef A hA) T₁ T₀ Tq q]
    rw [liftTwice, tensorComp_actFree_transl hT.2.2.1]
  have hLin : PrependLinear c h := ⟨hPm, fun A _ A' _ z => by
    simp only [prependComponent, liftTwice, map_add, map_smul]⟩
  have hComp : PrependComponents c h := by
    refine ⟨fun A hA => ?_, hSucc, fun A hA q x => ?_, fun A hA x => ?_⟩
    · rw [prependComponent, ((hC m S σ).1 _ _ (hDef A hA)).1, T₀, zero_mul]
    · rw [hSucc A hA q]
      change liftComponent c h (x 0) *
        translateArgs ((2 * c) • timeVec) (tensorComp q A) (fun l => x l.succ) = _
      rw [liftComponent, EuclidMotion.actFn_transl]
      rfl
    · refine (congrFun (hSucc A hA 0) x).trans ?_
      change liftComponent c h (x 0) *
        translateArgs ((2 * c) • timeVec) (tensorComp 0 A) (fun l => x l.succ) = _
      rw [translateArgs_zero, tensorComp_zero_apply, mul_comm]
  have hShift : ShiftGivesInsertion σ c h b := fun F hF A hA =>
    ⟨liftOnce_mem hAbove c hF, liftOnce_mem hAbove c hA,
      by rw [heightNorm, pullDown_liftOnce hE],
      inner_reconClass_prependInsertion hR hC hI hT σ hc hh hs hF hA (hPm A hA),
      norm_reconClass_cons_le hR hC hI hT σ hc hh hs hb hB hA (hPm A hA)⟩
  obtain ⟨Z, hZ, hU, hN⟩ := exists_unique_insertionOp hR hC hI hX hT σ hc hh hs hb hB hPm
  have hEps : ActsOnReconClasses σ c h (insertionOp σ c h) := Classical.epsilon_spec ⟨Z, hZ⟩
  have hEq : insertionOp σ c h = Z := hU _ hEps
  refine ⟨hLin, hComp, hShift, ⟨Z, hZ, hU⟩, hEps, hEq ▸ hN, fun F hF A hA => ?_⟩
  have mF := pullDown_mem hAbove c hF
  have mA := pullDown_mem hAbove c hA
  rw [hEps _ mA, inner_reconClass_prependInsertion hR hC hI hT σ hc hh hs mF mA (hPm _ mA),
    liftOnce_pullDown hE, liftOnce_pullDown hE]
end Main
end YangMills.Construction.EuclideanFunctionals.OneInsertionOperator
