import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstructionProof
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntries
import YangMills.Construction.EuclideanFunctionals.TranslationsAndConcatenationsOfTuplesWithComplexComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror TorusMetric RealPlane MeasureTheory
open scoped ComplexConjugate Pointwise
namespace EuclideanFunctionals.MotionMulRules
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.norm_le_euclidNormVec <;> assumption
open TupleRules TupleConcat
theorem mem_supp_iff {𝕜 : Type*} [RCLike 𝕜] {f : R4 → 𝕜} {x : R4} :
    x ∈ supp f ↔ ∀ ρ : ℝ, 0 < ρ → ∃ y : R4, f y ≠ 0 ∧ euclidNormVec (x - y) < ρ :=
  Iff.rfl
theorem supp_subset_closure_ne {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    supp f ⊆ closure {x | f x ≠ 0} := fun x hx => by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy, hd⟩ := mem_supp_iff.1 hx ε hε
  exact ⟨y, hy, by rw [dist_eq_norm]; exact (norm_le_euclidNormVec _).trans_lt hd⟩
theorem supp_actFn {𝕜 : Type*} [RCLike 𝕜] (g : EuclidMotion) (f : R4 → 𝕜) :
    supp (g.actFn f) = g '' supp f := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ x, mem_supp_iff.2 fun ρ hρ => ?_, g.apply_inv_apply x⟩
    obtain ⟨y, hy, hd⟩ := mem_supp_iff.1 hx ρ hρ
    refine ⟨g⁻¹ y, hy, ?_⟩
    rw [EuclidMotion.euclidNormVec_sub]
    exact hd
  · rintro ⟨w, hw, rfl⟩
    refine mem_supp_iff.2 fun ρ hρ => ?_
    obtain ⟨y, hy, hd⟩ := mem_supp_iff.1 hw ρ hρ
    refine ⟨g y, ?_, ?_⟩
    · change f (g⁻¹ (g y)) ≠ 0
      rw [EuclidMotion.inv_apply_apply]
      exact hy
    · rw [EuclidMotion.euclidNormVec_sub]
      exact hd
theorem movedSupportRules_holds : MovedSupportRules := by
  intro f _ _ w
  refine ⟨?_, supp_actFn timeFlip f⟩
  rw [supp_actFn, Set.add_singleton]
  rfl
theorem mem_finCombIn_iff {U : Set R4} {F : FreeSep} :
    F ∈ finCombIn U ↔ ∀ X ∈ F.support, X.1 ∈ sepIn U := by
  rw [finCombIn, Finsupp.mem_supported]
  exact Iff.rfl
theorem mem_finCombIn_of_combSupp_subset {U : Set R4} {F : FreeSep}
    (h : combSupp F ⊆ U) : F ∈ finCombIn U :=
  mem_finCombIn_iff.2 fun X hX =>
    ⟨X.2, fun f hf _ hx => h (Set.mem_iUnion₂.2 ⟨X, hX, Set.mem_iUnion₂.2 ⟨f, hf, hx⟩⟩)⟩
theorem finCombIn_mono {U V : Set R4} (h : U ⊆ V) {F : FreeSep}
    (hF : F ∈ finCombIn U) : F ∈ finCombIn V :=
  mem_finCombIn_iff.2 fun X hX => by
    have hX' := mem_finCombIn_iff.1 hF X hX
    exact ⟨hX'.1, fun f hf => (hX'.2 f hf).trans h⟩
theorem freeConj_mem_finCombIn {U : Set R4} {F : FreeSep} (hF : F ∈ finCombIn U) :
    freeConj F ∈ finCombIn U :=
  mem_finCombIn_iff.2 fun X hX => mem_finCombIn_iff.1 hF X (by
    rw [freeConj, Finsupp.mem_support_iff, Finsupp.mapRange_apply] at hX
    rw [Finsupp.mem_support_iff]
    intro h
    exact hX (by rw [h, map_zero]))
theorem nil_mem_sepAll : ([] : FnList) ∈ sepAll := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.nil_mem_sepAll <;> assumption
theorem liftLin_toFree_self (F : FreeSep) :
    liftLin (fun Y : sepAll => toFree Y.1) F = F := by
  induction F using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add f g hf hg => rw [map_add, hf, hg]
  | single X a =>
    have e : Finsupp.single X a = a • toFree X.1 := by
      rw [toFree_of_mem X.2, Finsupp.smul_single_one]
    rw [e, map_smul, liftLin_toFree (fun Y : sepAll => toFree Y.1) X]
theorem actFree_nil (g : EuclidMotion) : g.actFree (toFree []) = toFree [] :=
  liftLin_toFree (fun X : sepAll => toFree (g.actList X.1)) ⟨[], nil_mem_sepAll⟩
theorem freeConj_nil : freeConj (toFree []) = toFree [] := by
  rw [toFree_of_mem nil_mem_sepAll, freeConj, Finsupp.mapRange_single, map_one]
theorem flipConj_nil : flipConj (toFree []) = toFree [] := by
  rw [flipConj, freeConj_nil, actFree_nil]
theorem freeMul_toFree_left (X : sepAll) :
    freeMul (toFree X.1) = liftLin fun Y : sepAll => toFree (listAppend X.1 Y.1) :=
  liftLin_toFree
    (fun X : sepAll => liftLin fun Y : sepAll => toFree (listAppend X.1 Y.1)) X
theorem freeMul_nil_left (F : FreeSep) : freeMul (toFree []) F = F := by
  rw [freeMul_toFree_left ⟨[], nil_mem_sepAll⟩]
  exact liftLin_toFree_self F
theorem freeMul_nil_right (F : FreeSep) : freeMul F (toFree []) = F := by
  induction F using Finsupp.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg]
  | single X a =>
    have e : Finsupp.single X a = a • toFree X.1 := by
      rw [toFree_of_mem X.2, Finsupp.smul_single_one]
    rw [e, map_smul, LinearMap.smul_apply, freeMul_toFree_left,
      liftLin_toFree (fun Y : sepAll => toFree (listAppend X.1 Y.1))
        ⟨[], nil_mem_sepAll⟩]
    congr 2
    exact List.append_nil _
theorem actList_transl_zero (X : FnList) : (EuclidMotion.transl 0).actList X = X := by
  have e : (EuclidMotion.transl 0).actFn = (id : (R4 → ℝ) → R4 → ℝ) := by
    funext f x
    simp [EuclidMotion.actFn_transl]
  simp [EuclidMotion.actList, e]
theorem shiftFree_zero (F : FreeSep) : shiftFree 0 F = F := by
  change liftLin (fun X : sepAll => toFree ((EuclidMotion.transl 0).actList X.1)) F = F
  simp only [actList_transl_zero]
  exact liftLin_toFree_self F
theorem emptyAndShiftRules_holds (hT : ∀ v w : R4, TranslOnComb v w) :
    EmptyAndShiftRules := fun v w F =>
  ⟨(hT v w).1 F, shiftFree_zero F, actFree_nil _, flipConj_nil,
    freeMul_nil_left F, freeMul_nil_right F⟩
theorem shiftMulRule_holds (hR : DefinedMulRules) :
    ShiftMulRule := fun v F A h =>
  ⟨(hR (EuclidMotion.transl v) F A h).2.2.2.1, (hR (EuclidMotion.transl v) F A h).2.2.2.2⟩
theorem mulAssocRule_holds (hA : MulAssoc) : MulAssocRule := by
  intro F A B h₁ h₂ h₃
  obtain ⟨a, b, c⟩ := hA F A B ⟨h₁, h₂, h₃⟩
  exact ⟨a, b, c, c⟩
theorem complexTupleRules_holds (hW : TupleRules.ComplexTupleRules) :
    MotionMulRules.ComplexTupleRules := by
  intro n h U hh hU hs
  have t := fun g => hW U hU g n h hh hs
  exact ⟨(t 1).1, (t 1).2.2.1, (t 1).2.2.2.1, (t 1).2.2.2.2.1,
    fun v => (t (EuclidMotion.transl v)).2.2.2.2.2.2.1⟩
theorem headTailRules_holds (hW : TupleRules.ComplexTupleRules) (hR : DefinedMulRules)
    (hT : ∀ (n : ℕ) (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) (v : R4),
      ComplexComponents (consEntries h hs) →
        TranslTuple v hs ∧ SameComponents h hs ∧
          EqualCases h hs ∧ SameValues h hs ∧ SameClasses h hs) :
    HeadTailRules := by
  intro m h U hh hU hs
  have hcons : consEntries (h 0) (fun l : Fin (m + 1) => h l.succ) = h := Fin.cons_self_tail h
  have hlong : consTuple (h 0) (fun l : Fin (m + 1) => h l.succ) = complexTuple h := by
    rw [consTuple, hcons]
  obtain ⟨-, ⟨hdef, hsame, -, -⟩, -, -, hclass⟩ :=
    hT (m + 1) (h 0) (fun l => h l.succ) 0 (by rw [hcons]; exact hh)
  have hE₁ : ComplexComponents (fun _ : Fin 1 => h 0) :=
    ⟨le_rfl, fun _ => hh.mem 0, fun k l hkl => (hkl (Subsingleton.elim k l)).elim⟩
  have hE₂ : ComplexComponents (fun l : Fin (m + 1) => h l.succ) :=
    ⟨by omega, fun l => hh.mem _, fun k l hkl => hh.disjoint fun e => hkl (Fin.succ_injective _ e)⟩
  have s₁ := (hW U hU 1 1 (fun _ => h 0) hE₁ fun _ => hs 0).2.1
  have s₂ := (hW U hU 1 (m + 1) (fun l => h l.succ) hE₂ fun l => hs _).2.1
  have s₃ := (hR 1 _ _ hdef).1
  refine ⟨hdef, mem_finCombIn_of_combSupp_subset (s₃.trans (Set.union_subset ?_ ?_)), ?_, ?_⟩
  · exact s₁.trans (Set.iUnion_subset fun _ => hs 0)
  · exact s₂.trans (Set.iUnion_subset fun _ => hs _)
  · rw [← hlong]
    exact hsame
  · intro hsub M S σ
    have := (hclass (fun l => by rw [hcons]; exact (hs l).trans hsub)).2.2 M S σ
    rw [hlong] at this
    exact this
theorem centeredFnFree_single_real (hF : CenteredInitialValues.InitialValues) (S : ConnFamily)
    {f : R4 → ℝ} (hf : f ∈ C1c ℝ) :
    centeredFnFree S (toFree [f]) = 0 := by
  have e := liftLin_toFree (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ))
    (CenteredInitialValues.singleSep hf)
  have h0 := (hF S).2.1 f hf
  rw [h0] at e
  change liftLin (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ)) (toFree [f]) = 0
  exact e.trans Complex.ofReal_zero
theorem centeredFnFree_singleEntry (hP : ReImAndMotionOfFns)
    (hF : CenteredInitialValues.InitialValues) (S : ConnFamily) {g : R4 → ℂ}
    (hg : g ∈ C1c ℂ) : centeredFnFree S (singleComponent g) = 0 := by
  have hp := hP ⟨1, le_rfl⟩ 1 1 g hg
  have hpart : ∀ ε : Fin 2, reOrImPart ε g ∈ C1c ℝ := fun ε => by
    by_cases h : ε = 0
    · simpa [reOrImPart, h] using hp.1
    · simpa [reOrImPart, h] using hp.2.1
  rw [singleComponent, complexTuple]
  split_ifs with hreal
  · simpa [List.ofFn_succ] using centeredFnFree_single_real hF S hp.1
  · rw [map_sum]
    refine Finset.sum_eq_zero fun ε _ => ?_
    rw [map_smul]
    have e : List.ofFn (fun l : Fin 1 => reOrImPart (ε l) g) = [reOrImPart (ε 0) g] := by
      simp [List.ofFn_succ]
    rw [e, centeredFnFree_single_real hF S (hpart _), smul_zero]
theorem singleComponentValueZero_holds (hP : ReImAndMotionOfFns)
    (hF : CenteredInitialValues.InitialValues) : SingleEntryValueZero :=
  fun _ S _ _ _ hh => centeredFnFree_singleEntry hP hF S (hh.mem _)
theorem timeFlip_add (x v : R4) : timeFlip (x + v) = timeFlip x + timeFlip v := by
  rw [timeFlip_apply, timeFlip_apply, timeFlip_apply]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem shiftFlipConjRule_holds (hA : MotionOnFree) (hM : TimeFlipHalfSpaces) :
    ShiftFlipConjRule := by
  intro b F
  have hmm : timeFlip (timeFlip b) = b := by
    have h := EuclidMotion.inv_apply_apply timeFlip b
    rwa [hM.1] at h
  have hcomm : EuclidMotion.transl b * timeFlip = timeFlip * EuclidMotion.transl (timeFlip b) :=
    EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
        EuclidMotion.transl_apply, timeFlip_add, hmm]
  have a₁ := (hA (EuclidMotion.transl b) timeFlip (freeConj F)).1
  have a₂ := (hA timeFlip (EuclidMotion.transl (timeFlip b)) (freeConj F)).1
  have a₃ := (hA (EuclidMotion.transl (timeFlip b)) 1 F).2.1
  change (EuclidMotion.transl b).actFree (timeFlip.actFree (freeConj F)) =
    timeFlip.actFree (freeConj ((EuclidMotion.transl (timeFlip b)).actFree F))
  rw [a₃, a₁, a₂, hcomm]
theorem finCombMonotone_holds : FinCombMonotone :=
  fun _ _ _ _ h _ hF => finCombIn_mono h hF
theorem isOpen_time_gt (c : ℝ) : IsOpen {x : R4 | c < x 3} :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem transl_image_time_gt (b : R4) (c : ℝ) :
    (EuclidMotion.transl b) '' {x : R4 | c < x 3} = {x | c + b 3 < x 3} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change c + b 3 < (y + b) 3
    have : c < y 3 := hy
    simpa using this
  · intro hx
    refine ⟨x - b, ?_, ?_⟩
    · have : c + b 3 < x 3 := hx
      change c < (x - b) 3
      simp only [Pi.sub_apply]
      linarith
    · rw [EuclidMotion.transl_apply, sub_add_cancel]
theorem finCombAboveLevel_holds (hI : MotionOfListsAndCombs) (hM : TimeFlipHalfSpaces) :
    FinCombAboveLevel := by
  intro b c F hF
  constructor
  · have h := (hI (EuclidMotion.transl b) _ (isOpen_time_gt c)).2.2.mapsTo hF
    rwa [transl_image_time_gt] at h
  · have h := (hI timeFlip _ (isOpen_time_gt c)).2.2.mapsTo (freeConj_mem_finCombIn hF)
    rwa [hM.2 c] at h
theorem smul_timeVec_time (c : ℝ) : (c • timeVec) 3 = c := by
  simp [PeriodicLattice.coordVec]
theorem insertionRules_holds (hP : ReImAndMotionOfFns) (hI : MotionOfListsAndCombs)
    (hM : TimeFlipHalfSpaces) (hD : MulOnDisjointOpen)
    (hW : TupleRules.ComplexTupleRules) (hRf : FlipConjMulDefined) : InsertionRules := by
  intro c hc h hh hs
  have hp := hP ⟨1, le_rfl⟩ (EuclidMotion.transl (c • timeVec)) 1 h hh
  have hmem : shiftFn (c • timeVec) h ∈ C1c ℂ := hp.2.2.2.1
  have hE : ComplexComponents (fun _ : Fin 1 => shiftFn (c • timeVec) h) :=
    ⟨le_rfl, fun _ => hmem, fun k l hkl => (hkl (Subsingleton.elim k l)).elim⟩
  have hO₁ : IsOpen {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} :=
    (isOpen_lt continuous_const (continuous_apply 3)).inter
      (isOpen_lt (continuous_apply 3) continuous_const)
  have hsupp : supp (shiftFn (c • timeVec) h) ⊆ {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} := by
    rw [supp_actFn]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : |y 3| < c := hs hy
    have e : (EuclidMotion.transl (c • timeVec)) y 3 = y 3 + c := by
      rw [EuclidMotion.transl_apply, Pi.add_apply, smul_timeVec_time]
    have := abs_lt.1 hy'
    exact ⟨by rw [e]; linarith, by rw [e]; linarith⟩
  have hone := (hW _ hO₁ 1 1 (fun _ => shiftFn (c • timeVec) h) hE fun _ => hsupp).1
  have hdisj : Disjoint {x : R4 | 0 < x 3 ∧ x 3 < 2 * c} {x : R4 | 2 * c < x 3} :=
    Set.disjoint_left.2 fun x h₁ h₂ => absurd h₁.2 (not_lt.2 (le_of_lt h₂))
  have hraise : ∀ A ∈ finCombIn upperHalf,
      shiftFree ((2 * c) • timeVec) A ∈ finCombIn {x : R4 | 2 * c < x 3} := by
    intro A hA
    have h₀ := (finCombAboveLevel_holds hI hM ((2 * c) • timeVec) 0 A hA).1
    rwa [zero_add, smul_timeVec_time] at h₀
  have hcon := (hD _ _ hO₁ (isOpen_time_gt (2 * c)) hdisj).1
  refine ⟨fun A hA => ?_, fun A _ B _ w => ?_, fun F hF A hA => ?_⟩
  · obtain ⟨d, m⟩ := hcon _ hone _ (hraise A hA)
    refine ⟨d, finCombIn_mono ?_ m⟩
    rintro x (hx | hx)
    · exact hx.1
    · have hx' : 2 * c < x 3 := hx
      change 0 < x 3
      linarith
  · simp only [liftedInsertion, map_add, map_smul]
  · exact hRf.2 c hc F hF A hA h hh hs
theorem vacNormOne_holds (hF : CenteredInitialValues.InitialValues) :
    VacNormOne := by
  intro M S σ
  have hinner := σ.recon.inner_cls emptyComb emptyComb
  have hform : osForm S (toFree []) (toFree []) = 1 := by
    rw [osForm, freeConj_nil, actFree_nil, freeMul_nil_left]
    have e := liftLin_toFree (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ))
      (Ambient.emptyList defaultMirrorData Ambient.euclidean)
    have h1 := (hF S).1
    rw [h1] at e
    change liftLin (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ))
      (toFree []) = 1
    exact e.trans Complex.ofReal_one
  have hsq : ‖σ.recon.vac‖ ^ 2 = 1 := by
    have h₁ : inner ℂ σ.recon.vac σ.recon.vac = 1 := hinner.trans hform
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h₁]
    simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq
theorem continuous_planeComponent : Continuous planeComponent :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
    fin_cases i
    · exact continuous_apply 3
    · exact continuous_apply 0)
theorem continuous_orthogonalComponent : Continuous orthogonalComponent :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
    fin_cases i
    · exact continuous_apply 1
    · exact continuous_apply 2)
theorem supp_productFunction_subset (α : RealPlane → ℂ) (φ : RealPlane → ℝ) :
    supp (productFunction α φ) ⊆
      {x | planeComponent x ∈ tsupport α ∧ orthogonalComponent x ∈ tsupport φ} := by
  have hclosed :
      IsClosed {x : R4 | planeComponent x ∈ tsupport α ∧ orthogonalComponent x ∈ tsupport φ} :=
    ((isClosed_tsupport α).preimage continuous_planeComponent).inter
      ((isClosed_tsupport φ).preimage continuous_orthogonalComponent)
  refine (supp_subset_closure_ne _).trans (closure_minimal ?_ hclosed)
  intro x hx
  have hx' : α (planeComponent x) * (φ (orthogonalComponent x) : ℂ) ≠ 0 := hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'),
    subset_tsupport _ fun h => hx' (by simp [h])⟩
def coordPerm : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
  Equiv.ofBijective (Sum.elim ![3, 0] ![1, 2]) (by decide)
theorem measurePreserving_components :
    MeasurePreserving (fun x : R4 => (planeComponent x, orthogonalComponent x)) volume
      ((volume : Measure RealPlane).prod volume) := by
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin 4 => (volume : Measure ℝ))
    coordPerm).symm
  have h₂ := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin 2 ⊕ Fin 2 => ℝ)
    (fun _ => (volume : Measure ℝ))
  have h₃ := (PiLp.volume_preserving_toLp (Fin 2)).prod (PiLp.volume_preserving_toLp (Fin 2))
  have key : ∀ {f g : R4 → RealPlane × RealPlane}, f = g →
      MeasurePreserving g volume ((volume : Measure RealPlane).prod volume) →
      MeasurePreserving f volume ((volume : Measure RealPlane).prod volume) :=
    fun e h => e ▸ h
  refine key ?_ (h₃.comp (h₂.comp h₁))
  funext x
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl
theorem integral_norm_productFunction {α : RealPlane → ℂ} {φ : RealPlane → ℝ}
    (hα : α ∈ complexProfiles) (hφ : φ ∈ realLabels) :
    ∫ x : R4, ‖productFunction α φ x‖ = profileL1Norm α * ∫ y, ‖φ y‖ := by
  have hαc := hα.1.continuous
  have hφc := hφ.1.continuous
  have hc : Continuous fun p : RealPlane × RealPlane => ‖α p.1‖ * ‖φ p.2‖ := by
    fun_prop
  have e := integral_map (μ := (volume : Measure R4))
    measurePreserving_components.measurable.aemeasurable hc.aestronglyMeasurable
  rw [measurePreserving_components.map_eq] at e
  have e' : ∀ x : R4,
      ‖productFunction α φ x‖ = ‖α (planeComponent x)‖ * ‖φ (orthogonalComponent x)‖ :=
    fun x => by simp [productFunction]
  simp only [e']
  rw [← e]
  exact integral_prod_mul (fun y => ‖α y‖) (fun w => ‖φ w‖)
theorem profileRe_mem {α : RealPlane → ℂ} (hα : α ∈ complexProfiles) :
    profileRe α ∈ complexProfiles :=
  ⟨Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hα.1),
    hα.2.comp_left (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) (by simp)⟩
theorem profileIm_mem {α : RealPlane → ℂ} (hα : α ∈ complexProfiles) :
    profileIm α ∈ complexProfiles :=
  ⟨Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hα.1),
    hα.2.comp_left (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp)⟩
theorem tsupport_profileRe_subset (α : RealPlane → ℂ) :
    tsupport (profileRe α) ⊆ tsupport α :=
  closure_mono fun y hy h => hy (by simp [profileRe, h])
theorem tsupport_profileIm_subset (α : RealPlane → ℂ) :
    tsupport (profileIm α) ⊆ tsupport α :=
  closure_mono fun y hy h => hy (by simp [profileIm, h])
theorem productFunctionRules_holds (hPl : ProductFunctionsC1c) : ProductFunctionRules := by
  intro α hα φ hφ
  refine ⟨(hPl α hα φ hφ).1, supp_productFunction_subset α φ, ?_, ?_, profileRe_mem hα,
    profileIm_mem hα, tsupport_profileRe_subset α, tsupport_profileIm_subset α,
    integral_norm_productFunction hα hφ⟩
  · funext x
    simp [productFunction, profileRe]
  · funext x
    simp [productFunction, profileIm]
theorem shiftedProductInStrip_holds : ShiftedProductInStrip := by
  intro α _ φ _ t _ hs y
  rw [supp_actFn]
  rintro _ ⟨p, hp, rfl⟩
  have h₁ : |planeComponent p 0| < t := hs _ (supp_productFunction_subset α φ hp).1
  have h₂ : planeComponent p 0 = p 3 := by simp [planeComponent]
  have h₃ : (planeShift y) p 3 = p 3 + y 0 := by
    change (p + embedFour y) 3 = p 3 + y 0
    simp [embedFour, PeriodicLattice.coordVec]
  change |(planeShift y) p 3 - y 0| < t
  rw [h₃, add_sub_cancel_right, ← h₂]
  exact h₁
theorem motionMulTupleRules_holds (h₁ : TupleSpanActionRules)
    (h₂ : TupleFacts)
    (h₃ : CenteredInitialValues.InitialValues) :
    MotionMulTupleRules := by
  obtain ⟨hP, hI, hA, -, hD, hR, hAs, hW, hM, hRf, -, -⟩ := h₁
  obtain ⟨hT, hC, hPl⟩ := h₂
  exact ⟨emptyAndShiftRules_holds hC, shiftMulRule_holds hR, mulAssocRule_holds hAs,
    complexTupleRules_holds hW, headTailRules_holds hW hR hT, singleComponentValueZero_holds hP h₃,
    shiftFlipConjRule_holds hA hM, movedSupportRules_holds, finCombMonotone_holds,
    finCombAboveLevel_holds hI hM, insertionRules_holds hP hI hM hD hW hRf, vacNormOne_holds h₃,
    productFunctionRules_holds hPl, shiftedProductInStrip_holds⟩
end EuclideanFunctionals.MotionMulRules
end YangMills.Construction
