import YangMills.Construction.InfiniteLattice.FirstFactsOnArraysAndPerturbedSpecifications
import YangMills.Construction.InfiniteLattice.SurfaceBoundBetweenBoxAndTorusProof
import YangMills.Construction.InfiniteLattice.TorusMeasureSatisfiesThePerturbedEquationOfAWindow
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace InfiniteLattice
namespace TiltedTorusMeasureWindowEquation
section
variable {S P : Type} [Finite S] [Finite P]
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem integral_extend_haarPi (hG : ComplexMatrix2.FiniteProductGroupStatement) {ι : S → P}
    (hι : Function.Injective ι) {h : (P → ComplexMatrix2.specialUnitary) → ℂ} (hm : Measurable h)
    {C : ℝ} (hb : ∀ v, ‖h v‖ ≤ C) :
    ∫ v, (∫ V, h (Function.extend ι V v) ∂ComplexMatrix2.haarPi S) ∂ComplexMatrix2.haarPi P =
      ∫ v, h v ∂ComplexMatrix2.haarPi P := by
  classical
  have := secondCountableTopology_specialUnitary
  obtain ⟨-, -, hSp, -, hSr⟩ := hG.2.1 S
  obtain ⟨-, -, hPp, hPl, -⟩ := hG.2.1 P
  set e : (S → ComplexMatrix2.specialUnitary) → (P → ComplexMatrix2.specialUnitary) :=
    fun V => Function.extend ι V 1 with he
  have hupd : ∀ (v : P → ComplexMatrix2.specialUnitary) (V : S → ComplexMatrix2.specialUnitary),
      Function.extend ι V v = e (V * (v ∘ ι)⁻¹) * v := by
    intro v V
    funext p
    by_cases hp : ∃ s, ι s = p
    · obtain ⟨s, rfl⟩ := hp
      simp [he, hι.extend_apply]
    · simp [he, Function.extend_apply' _ _ _ hp]
  have hin : ∀ v : P → ComplexMatrix2.specialUnitary,
      ∫ V, h (Function.extend ι V v) ∂ComplexMatrix2.haarPi S =
        ∫ V, h (e V * v) ∂ComplexMatrix2.haarPi S := by
    intro v
    simp only [hupd]
    exact integral_mul_right_eq_self (fun V => h (e V * v)) ((v ∘ ι)⁻¹)
  simp only [hin]
  have hjoint : Measurable fun q : (P → ComplexMatrix2.specialUnitary) ×
      (S → ComplexMatrix2.specialUnitary) => e q.2 * q.1 := by
    refine measurable_pi_iff.2 fun p => ?_
    by_cases hp : ∃ s, ι s = p
    · obtain ⟨s, rfl⟩ := hp
      simp only [he, Pi.mul_apply, hι.extend_apply]
      exact ((measurable_pi_apply s).comp measurable_snd).mul
        ((measurable_pi_apply (ι s)).comp measurable_fst)
    · simp only [he, Pi.mul_apply, Function.extend_apply' _ _ _ hp]
      simp only [Pi.one_apply, one_mul]
      exact (measurable_pi_apply p).comp measurable_fst
  have hint : Integrable (Function.uncurry fun (v : P → ComplexMatrix2.specialUnitary)
      (V : S → ComplexMatrix2.specialUnitary) => h (e V * v))
      ((ComplexMatrix2.haarPi P).prod (ComplexMatrix2.haarPi S)) :=
    Integrable.of_bound (hm.comp hjoint).aestronglyMeasurable C (ae_of_all _ fun q => hb _)
  rw [integral_integral_swap hint]
  simp only [integral_mul_left_eq_self (μ := ComplexMatrix2.haarPi P) h]
  simp
end
theorem finsum_eq_image_add_compl {κ σ : Type*} [Finite κ] (e : σ → κ) {A : Set σ}
    (hA : InjOn e A) (f : κ → ℝ) :
    ∑ᶠ k, f k = (∑ᶠ i ∈ A, f (e i)) + ∑ᶠ k ∈ (univ \ e '' A), f k := by
  have h := finsum_mem_add_sdiff (subset_univ (e '' A)) finite_univ (f := f)
  rw [finsum_mem_univ, finsum_mem_image hA] at h
  exact h.symm
section
variable (Γ : PeriodSublattice 1)
theorem positiveLink_translate_zero (b : PositiveLink 1) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
theorem exists_period_of_linkClass_eq {b b' : PositiveLink 1}
    (h : Γ.linkClass b = Γ.linkClass b') : ∃ γ ∈ Γ.periods, b' = b.translate γ := by
  have h' : Γ.linkOrbit b = Γ.linkOrbit b' := congrArg Subtype.val h
  have hm : b' ∈ Γ.linkOrbit b' := ⟨0, zero_mem _, (positiveLink_translate_zero b').symm⟩
  rw [← h'] at hm
  exact hm
theorem isPositivelyOriented_shift_linkMap (v : LatticePoint 1) {b : Link 1}
    (hb : b.IsPositivelyOriented) : ((shift v).linkMap b).IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  refine ⟨μ, ?_⟩
  rw [← hμ]
  exact Subtype.ext (add_sub_add_right_eq_sub _ _ _)
theorem orientedRepresentative_of_isPositivelyOriented {b : Link 1}
    (hb : b.IsPositivelyOriented) : b.orientedRepresentative = b := by
  classical
  exact if_pos hb
theorem translate_mem_shiftLinks {𝓜 : Set (Link 1)} (h𝓜 : IsLinkSet 𝓜) {v v' : LatticePoint 1}
    (b : PositiveLink 1) (hb : b.1 ∈ shiftLinks 𝓜 v) :
    (b.translate (v' - v)).1 ∈ shiftLinks 𝓜 v' := by
  obtain ⟨b₁, hb₁, e⟩ := hb
  have hp : b₁.IsPositivelyOriented := h𝓜 hb₁
  have e' : (shift v).linkMap b₁ = b.1 := by
    rw [← e]
    exact (orientedRepresentative_of_isPositivelyOriented
      (isPositivelyOriented_shift_linkMap v hp)).symm
  refine ⟨b₁, hb₁, ?_⟩
  change ((shift v').linkMap b₁).orientedRepresentative = _
  rw [orientedRepresentative_of_isPositivelyOriented (isPositivelyOriented_shift_linkMap v' hp)]
  have ht : b.1.initial = b₁.initial + v := by rw [← e']; exact Subtype.ext rfl
  have hh : b.1.terminal = b₁.terminal + v := by rw [← e']; exact Subtype.ext rfl
  refine Link.ext ?_ ?_
  · change _ = b.1.initial + (v' - v)
    rw [ht]
    refine Eq.trans
      (Subtype.ext rfl : (shift v').pointMap b₁.initial = b₁.initial + v') ?_
    abel
  · change _ = b.1.terminal + (v' - v)
    rw [hh]
    refine Eq.trans
      (Subtype.ext rfl : (shift v').pointMap b₁.terminal = b₁.terminal + v') ?_
    abel
def movedBy (r : ElementaryPlaquette 1) (γ : LatticePoint 1) : ElementaryPlaquette 1 :=
  ⟨r.corner + γ, r.lowAxis, r.highAxis, r.lowAxis_lt_highAxis⟩
theorem translate_mem_linkSet_movedBy (r : ElementaryPlaquette 1) (γ : LatticePoint 1)
    {b : Link 1} (hb : b ∈ r.linkSet) (hp : b.IsPositivelyOriented) :
    (PositiveLink.translate ⟨b, hp⟩ γ).1 ∈ (movedBy r γ).linkSet := by
  simp only [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges, Set.mem_ofPred_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
  rcases hb with rfl | rfl | rfl | rfl
  · refine Or.inl (Link.ext ?_ ?_) <;>
      simp only [PositiveLink.translate, Link.forwardFrom, movedBy] <;> abel
  · refine Or.inr (Or.inl (Link.ext ?_ ?_)) <;>
      simp only [PositiveLink.translate, Link.forwardFrom, movedBy] <;> abel
  · refine Or.inr (Or.inr (Or.inl (Link.ext ?_ ?_))) <;>
      simp only [PositiveLink.translate, Link.forwardFrom, movedBy] <;> abel
  · refine Or.inr (Or.inr (Or.inr (Link.ext ?_ ?_))) <;>
      simp only [PositiveLink.translate, Link.forwardFrom, movedBy] <;> abel
variable {Γ}
theorem faceClass_movedBy (hf : Γ.IsFaithfulQuotient) (r : ElementaryPlaquette 1)
    {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) : Γ.faceClass (movedBy r γ) = Γ.faceClass r := by
  obtain ⟨e, he⟩ := hf.plaquette_equiv
  apply e.injective
  rw [he, he]
  refine Subtype.ext ?_
  have h0 : Γ.quotientMap γ = 0 := (QuotientAddGroup.eq_zero_iff γ).2 hγ
  simp only [movedBy, map_add, h0, add_zero]
theorem corner_sub_mem_of_faceClass_eq (hf : Γ.IsFaithfulQuotient) {p q : ElementaryPlaquette 1}
    (h : Γ.faceClass p = Γ.faceClass q) :
    q.corner - p.corner ∈ Γ.periods ∧ p.lowAxis = q.lowAxis ∧ p.highAxis = q.highAxis := by
  obtain ⟨e, he⟩ := hf.plaquette_equiv
  have h₁ := he p
  rw [h, he q] at h₁
  have h₂ := congrArg Subtype.val h₁
  simp only [Prod.mk.injEq] at h₂
  obtain ⟨h₃, h₄, h₅⟩ := h₂
  refine ⟨?_, h₄.symm, h₅.symm⟩
  have h₆ : (-p.corner + q.corner) ∈ Γ.periods := QuotientAddGroup.eq.1 h₃.symm
  rwa [neg_add_eq_sub] at h₆
theorem shift_zero_plaquetteMap (hf : Γ.IsFaithfulQuotient) (r : ElementaryPlaquette 1) :
    (shift (0 : LatticePoint 1)).plaquetteMap r = r := by
  classical
  have hmem : (shift (0 : LatticePoint 1)).plaquetteMap r ∈ Γ.plaquetteOrbit r :=
    ⟨0, zero_mem _, rfl⟩
  have hex : ∃ p' : ElementaryPlaquette 1,
      p'.cornerSet = (shift (0 : LatticePoint 1)).pointMap '' r.cornerSet := by
    refine ⟨r, ?_⟩
    have hid : (shift (0 : LatticePoint 1)).pointMap = id :=
      funext fun x => Subtype.ext (add_zero (x : AmbientSpace))
    rw [hid, image_id]
  have hcs : ((shift (0 : LatticePoint 1)).plaquetteMap r).cornerSet = r.cornerSet := by
    have hid : (shift (0 : LatticePoint 1)).pointMap = id :=
      funext fun x => Subtype.ext (add_zero (x : AmbientSpace))
    have hd : (shift (0 : LatticePoint 1)).plaquetteMap r = hex.choose := dif_pos hex
    rw [hd]
    exact hex.choose_spec.trans (by rw [hid, image_id])
  refine hf.plaquette_eq_of_shared_corner r _ hmem ⟨r.corner, ?_, ?_⟩
  · exact Or.inl rfl
  · rw [hcs]
    exact Or.inl rfl
theorem quotientFaceEnergy_faceClass (hf : Γ.IsFaithfulQuotient) (he : Γ.LiftIsFaithful)
    (U : Γ.QuotientField) (r : ElementaryPlaquette 1) :
    Γ.quotientFaceEnergy U (Γ.faceClass r) = faceEnergy (Γ.lift U) r :=
  (he.faceEnergy_lift U (Γ.faceClass r) r
    (show r ∈ Γ.plaquetteOrbit r from ⟨0, zero_mem _, (shift_zero_plaquetteMap hf r).symm⟩)).symm
end
section
variable (W : LinkWindow 1) (Γ : PeriodSublattice 1)
def windowLinkClass (c : W.links) : Γ.QuotientLink := Γ.linkClass ⟨c.1, W.isPositive c.1 c.2⟩
def replaceWindow (V : W.Assignments) (U : Γ.QuotientField) : Γ.QuotientField :=
  Function.extend (windowLinkClass W Γ) V U
def AvoidsWindow (b : Link 1) : Prop :=
  ∀ (hb : b.IsPositivelyOriented) (c : W.links), Γ.linkClass ⟨b, hb⟩ ≠ windowLinkClass W Γ c
variable {W Γ}
theorem lift_of_isPositivelyOriented (U : Γ.QuotientField) {b : Link 1}
    (h : b.IsPositivelyOriented) : Γ.lift U b = U (Γ.linkClass ⟨b, h⟩) := by
  classical
  exact dif_pos h
theorem glue_of_mem (V : W.Assignments) (X : GaugeField 1) {b : Link 1} (hb : b ∈ W.links) :
    W.glue one_pos V X b = V ⟨b, hb⟩ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxTorusSurfaceBound.glue_apply_of_mem <;> assumption
theorem glue_of_not_mem (V : W.Assignments) (X : GaugeField 1) {b : Link 1}
    (hp : b.IsPositivelyOriented) (hb : b ∉ W.links) : W.glue one_pos V X b = X b := by
  classical
  have h' : b.opposite ∉ W.links := fun h' =>
    Link.opposite_not_isPositivelyOriented one_pos hp (W.isPositive _ h')
  exact (dif_neg hb).trans (dif_neg h')
theorem lift_replaceWindow_of_mem (hι : Function.Injective (windowLinkClass W Γ))
    (V : W.Assignments) (U : Γ.QuotientField) {b : Link 1} (hb : b ∈ W.links) :
    Γ.lift (replaceWindow W Γ V U) b = V ⟨b, hb⟩ := by
  rw [lift_of_isPositivelyOriented _ (W.isPositive b hb)]
  exact hι.extend_apply V U ⟨b, hb⟩
theorem lift_replaceWindow_of_avoids (V : W.Assignments) (U : Γ.QuotientField) {b : Link 1}
    (hp : b.IsPositivelyOriented) (ho : AvoidsWindow W Γ b) :
    Γ.lift (replaceWindow W Γ V U) b = Γ.lift U b := by
  rw [lift_of_isPositivelyOriented _ hp, lift_of_isPositivelyOriented _ hp]
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨c, hc⟩
  exact ho hp c hc.symm
end
section
variable (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1)
def labelCoset (i : 𝔸.Label) : 𝔸.Cosets Γ × Fin 𝔸.size :=
  (QuotientAddGroup.mk i.1, i.2)
variable {𝔸 Γ}
theorem exists_tiltedWeight_factorization {β t : ℝ} {W : LinkWindow 1}
    (hf : Γ.IsFaithfulQuotient) (he : Γ.LiftIsFaithful)
    (hd : 𝔸.PeriodicDescentWellDefined Γ β t)
    (hPinj : InjOn Γ.faceClass (facesMeeting (W.links : Set (Link 1))))
    (hIinj : InjOn (labelCoset 𝔸 Γ) (𝔸.labelsTouching W))
    (hPdep : ∀ (r : ElementaryPlaquette 1) (X Y : GaugeField 1), (∀ b ∈ r.linkSet, X b = Y b) →
      faceEnergy X r = faceEnergy Y r)
    (hTdep : ∀ (i : 𝔸.Label) (X Y : GaugeField 1),
      (∀ b ∈ observableSupport (𝔸.translate i), X b = Y b) → 𝔸.translate i X = 𝔸.translate i Y)
    (hPout : ∀ (r : ElementaryPlaquette 1),
      Γ.faceClass r ∉ Γ.faceClass '' facesMeeting (W.links : Set (Link 1)) →
      ∀ b ∈ r.linkSet, b.IsPositivelyOriented ∧ AvoidsWindow W Γ b)
    (hIout : ∀ k : 𝔸.Cosets Γ × Fin 𝔸.size, k ∉ labelCoset 𝔸 Γ '' 𝔸.labelsTouching W →
      ∀ b ∈ observableSupport (𝔸.translate (𝔸.cosetRep Γ k.1, k.2)),
        b.IsPositivelyOriented ∧ AvoidsWindow W Γ b) :
    ∃ T : Γ.QuotientField → ℝ,
      (∀ U, 𝔸.tiltedWeight Γ β t U =
        Real.exp (-𝔸.windowEnergy β t W (Γ.lift U)) * Real.exp (T U)) ∧
      ∀ (V : W.Assignments) (U : Γ.QuotientField), T (replaceWindow W Γ V U) = T U := by
  classical
  have := hf.finite_quotientPlaquette
  have := hd.finite_cosets
  let Rp : Γ.QuotientField → ℝ := fun U =>
    ∑ᶠ P ∈ (univ \ Γ.faceClass '' facesMeeting (W.links : Set (Link 1))),
      Γ.quotientFaceEnergy U P
  let f : Γ.QuotientField → 𝔸.Cosets Γ × Fin 𝔸.size → ℝ := fun U k =>
    (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ k.1, k.2)) U).re
  let Ri : Γ.QuotientField → ℝ := fun U =>
    ∑ᶠ k ∈ (univ \ labelCoset 𝔸 Γ '' 𝔸.labelsTouching W), f U k
  refine ⟨fun U => t * Ri U - β * Rp U, fun U => ?_, fun V U => ?_⟩
  · have h₁ := finsum_eq_image_add_compl Γ.faceClass hPinj (fun P => Γ.quotientFaceEnergy U P)
    have h₂ := finsum_eq_image_add_compl (labelCoset 𝔸 Γ) hIinj (f U)
    have h₃ : ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)),
        Γ.quotientFaceEnergy U (Γ.faceClass p) =
        ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy (Γ.lift U) p :=
      finsum_mem_congr rfl fun p _ => quotientFaceEnergy_faceClass hf he U p
    have h₄ : ∑ᶠ i ∈ 𝔸.labelsTouching W, f U (labelCoset 𝔸 Γ i) =
        ∑ᶠ i ∈ 𝔸.labelsTouching W, (𝔸.translate i (Γ.lift U)).re := by
      refine finsum_mem_congr rfl fun i _ => ?_
      have h₅ := hd.periodize_translate (𝔸.cosetRep Γ (QuotientAddGroup.mk i.1)) i.1 i.2
        (Quotient.out_eq _)
      exact congrArg Complex.re (congrFun h₅ U)
    change Real.exp (t * ∑ᶠ k, f U k - β * ∑ᶠ P, Γ.quotientFaceEnergy U P) = _
    rw [h₂, h₁, h₃, h₄, ← Real.exp_add, LocalObservableArray.windowEnergy]
    congr 1
    ring
  · have hR₁ : Rp (replaceWindow W Γ V U) = Rp U := by
      refine finsum_mem_congr rfl fun P hP => ?_
      obtain ⟨_, r, rfl⟩ := P
      have hr : Γ.faceClass r ∉ Γ.faceClass '' facesMeeting (W.links : Set (Link 1)) := hP.2
      change Γ.quotientFaceEnergy _ (Γ.faceClass r) = Γ.quotientFaceEnergy _ (Γ.faceClass r)
      rw [quotientFaceEnergy_faceClass hf he, quotientFaceEnergy_faceClass hf he]
      refine hPdep r _ _ fun b hb => ?_
      obtain ⟨hp, ho⟩ := hPout r hr b hb
      exact lift_replaceWindow_of_avoids V U hp ho
    have hR₂ : Ri (replaceWindow W Γ V U) = Ri U := by
      refine finsum_mem_congr rfl fun k hk => ?_
      have h₆ := hTdep (𝔸.cosetRep Γ k.1, k.2) (Γ.lift (replaceWindow W Γ V U))
        (Γ.lift U) fun b hb => by
          obtain ⟨hp, ho⟩ := hIout k hk.2 b hb
          exact lift_replaceWindow_of_avoids V U hp ho
      exact congrArg Complex.re h₆
    change t * Ri (replaceWindow W Γ V U) - β * Rp (replaceWindow W Γ V U) = t * Ri U - β * Rp U
    rw [hR₁, hR₂]
theorem stateEval_tiltedLiftMeasure {β t : ℝ} (hext : Continuous Γ.lift)
    (hw : Continuous (𝔸.tiltedWeight Γ β t)) (hwpos : ∀ U, 0 ≤ 𝔸.tiltedWeight Γ β t U)
    {G : GaugeField 1 → ℂ} (hG : Continuous G) :
    stateEval (𝔸.tiltedLiftMeasure Γ β t) G =
      (ENNReal.ofReal (𝔸.tiltedPartition Γ β t))⁻¹.toReal •
        ∫ U, 𝔸.tiltedWeight Γ β t U • G (Γ.lift U) ∂Γ.quotientHaar := by
  have := secondCountableTopology_specialUnitary
  unfold stateEval LocalObservableArray.tiltedLiftMeasure
  rw [integral_map hext.measurable.aemeasurable hG.measurable.aestronglyMeasurable,
    LocalObservableArray.tiltedMeasure, integral_smul_measure]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hwpos _)]
theorem window_equation_of_factorization [Finite Γ.QuotientLink]
    (hG : ComplexMatrix2.FiniteProductGroupStatement)
    {β t : ℝ} {W : LinkWindow 1} (hι : Function.Injective (windowLinkClass W Γ))
    (hext : Continuous Γ.lift) (hw : Continuous (𝔸.tiltedWeight Γ β t))
    (hwpos : ∀ U, 0 ≤ 𝔸.tiltedWeight Γ β t U) {T : Γ.QuotientField → ℝ}
    (hfac : ∀ U, 𝔸.tiltedWeight Γ β t U =
      Real.exp (-𝔸.windowEnergy β t W (Γ.lift U)) * Real.exp (T U))
    (hT : ∀ (V : W.Assignments) (U : Γ.QuotientField), T (replaceWindow W Γ V U) = T U)
    {F : GaugeField 1 → ℂ} (hFc : Continuous F)
    (hHc : Continuous (𝔸.tiltedKernel β t W F))
    (hZ : ∀ X, 0 < 𝔸.windowPartition β t W X)
    (hFi : ∀ (V : W.Assignments) (U : Γ.QuotientField),
      F (Γ.lift (replaceWindow W Γ V U)) = F (W.glue one_pos V (Γ.lift U)))
    (hEi : ∀ (V : W.Assignments) (U : Γ.QuotientField),
      𝔸.windowEnergy β t W (Γ.lift (replaceWindow W Γ V U)) =
        𝔸.windowEnergy β t W (W.glue one_pos V (Γ.lift U)))
    (hHi : ∀ (V : W.Assignments) (U : Γ.QuotientField),
      𝔸.tiltedKernel β t W F (Γ.lift (replaceWindow W Γ V U)) =
        𝔸.tiltedKernel β t W F (Γ.lift U)) :
    stateEval (𝔸.tiltedLiftMeasure Γ β t) F =
      stateEval (𝔸.tiltedLiftMeasure Γ β t) (𝔸.tiltedKernel β t W F) := by
  have := secondCountableTopology_specialUnitary
  rw [stateEval_tiltedLiftMeasure hext hw hwpos hFc, stateEval_tiltedLiftMeasure hext hw hwpos hHc]
  congr 1
  have hc : ∀ {G : GaugeField 1 → ℂ}, Continuous G →
      Continuous fun U => 𝔸.tiltedWeight Γ β t U • G (Γ.lift U) :=
    fun hG => hw.smul (hG.comp hext)
  obtain ⟨C₁, hC₁⟩ := isCompact_univ.exists_bound_of_continuousOn (hc hFc).continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_univ.exists_bound_of_continuousOn (hc hHc).continuousOn
  have e₁ := integral_extend_haarPi hG hι (hc hFc).measurable (fun v => hC₁ v (mem_univ v))
  have e₂ := integral_extend_haarPi hG hι (hc hHc).measurable (fun v => hC₂ v (mem_univ v))
  refine e₁.symm.trans (Eq.trans ?_ e₂)
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  set X := Γ.lift U with hX
  have hhaar : ComplexMatrix2.haarPi W.links = W.haarProd := rfl
  have i₁ : ∀ V : W.Assignments,
      𝔸.tiltedWeight Γ β t (Function.extend (windowLinkClass W Γ) V U) •
          F (Γ.lift (Function.extend (windowLinkClass W Γ) V U)) =
        Real.exp (T U) • (F (W.glue one_pos V X) *
          (Real.exp (-𝔸.windowEnergy β t W (W.glue one_pos V X)) : ℂ)) := by
    intro V
    have a₁ := hFi V U
    have a₂ := hEi V U
    have a₃ := hT V U
    simp only [replaceWindow] at a₁ a₂ a₃
    rw [hfac, a₁, a₂, a₃]
    simp only [Complex.real_smul]
    push_cast
    ring
  have i₂ : ∀ V : W.Assignments,
      𝔸.tiltedWeight Γ β t (Function.extend (windowLinkClass W Γ) V U) •
          𝔸.tiltedKernel β t W F (Γ.lift (Function.extend (windowLinkClass W Γ) V U)) =
        (Real.exp (-𝔸.windowEnergy β t W (W.glue one_pos V X)) * Real.exp (T U)) •
          𝔸.tiltedKernel β t W F X := by
    intro V
    have a₂ := hEi V U
    have a₃ := hT V U
    have a₄ := hHi V U
    simp only [replaceWindow] at a₂ a₃ a₄
    rw [hfac, a₄, a₂, a₃]
  simp only [i₁, i₂, hhaar]
  rw [integral_smul, integral_smul_const, integral_mul_const]
  have hz : ((𝔸.windowPartition β t W X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hZ X).ne'
  change _ = (𝔸.windowPartition β t W X * Real.exp (T U)) • _
  simp only [LocalObservableArray.tiltedKernel, Complex.real_smul]
  push_cast
  field_simp
end
end TiltedTorusMeasureWindowEquation
open TiltedTorusMeasureWindowEquation in
theorem TiltedTorusMeasureWindowEquation.holds
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    (hFirst : BasicTiltedKernelFacts)
    (hElem : ElementaryLatticeFacts)
    (hG : ComplexMatrix2.FiniteProductGroupStatement) :
    TiltedTorusMeasureWindowEquation.Statement := by
  classical
  intro β hβ 𝔸 t W F hF
  obtain ⟨hTor, hArr, -, -⟩ := hFacts β hβ
  obtain ⟨hsup, hspec, hdesc⟩ := hArr 𝔸 t
  obtain ⟨-, hPl, -, hLoc, -, -, -, hIso, -⟩ := hElem 1 β one_pos hβ
  have hHloc := (hFirst β hβ 𝔸 W t).2.2.2 F hF
  have hsupp : ∀ G ∈ continuousLocalFunctions 1,
      DependsOnlyOn (observableSupport G) G ∧
        IsLinkSet (observableSupport G) ∧ (observableSupport G).Finite := by
    intro G hG
    obtain ⟨h₁, h₂, h₃, -⟩ := hLoc.2.2.2.2.2.2.2 G hG.1 hG.2.1
    exact ⟨h₁, h₂, h₃⟩
  have hgen : ∀ ι, 𝔸.gen ι ∈ continuousLocalFunctions 1 := 𝔸.gen_mem
  have hterm : ∀ i : 𝔸.Label, 𝔸.translate i ∈ continuousLocalFunctions 1 := by
    intro i
    have h := (hIso (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))).2.2.2.2.1
    rw [← h]
    exact ⟨_, hgen i.2, rfl⟩
  have hPfin : (facesMeeting (W.links : Set (Link 1))).Finite := hPl.2.2.2.2.2 W
  have hIfin : (𝔸.labelsTouching W).Finite := hsup.finite_labelsTouching W
  have hpb : ∀ p : ElementaryPlaquette 1, p.linkSet.Finite := fun p => List.finite_toSet p.edges
  let M : Set (Link 1) := (W.links : Set (Link 1)) ∪ observableSupport F ∪
    (⋃ p ∈ facesMeeting (W.links : Set (Link 1)), p.linkSet) ∪
    (⋃ i ∈ 𝔸.labelsTouching W, observableSupport (𝔸.translate i))
  have hLM : ∀ {b : Link 1}, b ∈ W.links → b ∈ M := fun hb => Or.inl (Or.inl (Or.inl hb))
  have hFM : ∀ {b : Link 1}, b ∈ observableSupport F → b ∈ M :=
    fun hb => Or.inl (Or.inl (Or.inr hb))
  have hPM : ∀ {p : ElementaryPlaquette 1} {b : Link 1},
      p ∈ facesMeeting (W.links : Set (Link 1)) → b ∈ p.linkSet → b ∈ M :=
    fun hp hb => Or.inl (Or.inr (mem_biUnion hp hb))
  have hIM : ∀ {i : 𝔸.Label} {b : Link 1}, i ∈ 𝔸.labelsTouching W →
      b ∈ observableSupport (𝔸.translate i) → b ∈ M := fun hi hb => Or.inr (mem_biUnion hi hb)
  have hMfin : M.Finite :=
    (((W.links.finite_toSet).union (hsupp F hF).2.2).union
      (hPfin.biUnion fun p _ => hpb p)).union
      (hIfin.biUnion fun i _ => (hsupp _ (hterm i)).2.2)
  have hpbp : ∀ {p : ElementaryPlaquette 1} {b : Link 1}, b ∈ p.linkSet →
      b.IsPositivelyOriented :=
    fun hb => ((hPl.2.2.1 _ _).1 hb).1
  have hMpos : ∀ b ∈ M, b.IsPositivelyOriented := by
    rintro b (((hb | hb) | hb) | hb)
    · exact W.isPositive b hb
    · exact (hsupp F hF).2.1 hb
    · obtain ⟨p, -, hb⟩ := mem_iUnion₂.1 hb
      exact hpbp hb
    · obtain ⟨i, -, hb⟩ := mem_iUnion₂.1 hb
      exact (hsupp _ (hterm i)).2.1 hb
  let S : Set (LatticePoint 1) := Link.initial '' M
  have hS : S.Finite := hMfin.image _
  obtain ⟨w, hw⟩ : ∃ w : ℝ, ∀ x ∈ S, ∀ y ∈ S,
      WholeSpace.maxNorm ((y - x : LatticePoint 1) : AmbientSpace) ≤ w := by
    obtain ⟨w, hw⟩ := ((hS.prod hS).image fun q : LatticePoint 1 × LatticePoint 1 =>
      WholeSpace.maxNorm ((q.2 - q.1 : LatticePoint 1) : AmbientSpace)).bddAbove
    exact ⟨w, fun x hx y hy => hw ⟨(x, y), ⟨hx, hy⟩, rfl⟩⟩
  refine ⟨w, fun Γ hΓ hlong => ?_⟩
  have hemb : ∀ x ∈ S, ∀ y ∈ S, y - x ∈ Γ.periods → y = x := by
    intro x hx y hy hγ
    by_contra hne
    exact absurd (hw x hx y hy) (not_le.2 (hlong _ hγ (sub_ne_zero.2 hne)))
  obtain ⟨hfaith, hextf, -⟩ := hTor 1 one_pos Γ
  have hd := hdesc Γ hΓ
  have htail : ∀ {b : Link 1}, b ∈ M → b.initial ∈ S := fun hb => ⟨_, hb, rfl⟩
  have hshift : ∀ {x : LatticePoint 1} {γ : LatticePoint 1}, x ∈ S → x + γ ∈ S →
      γ ∈ Γ.periods → γ = 0 := by
    intro x γ hx hy hγ
    have h := hemb x hx _ hy (by simpa using hγ)
    simpa using h
  have hclass : ∀ b b' : PositiveLink 1, b.1 ∈ M → b'.1 ∈ M →
      Γ.linkClass b = Γ.linkClass b' → b = b' := by
    intro b b' hb hb' h
    obtain ⟨γ, hγ, e⟩ := exists_period_of_linkClass_eq Γ h
    have ht : b'.1.initial = b.1.initial + γ := by rw [e]; rfl
    have hγ0 : γ = 0 := hshift (htail hb) (ht ▸ htail hb') hγ
    rw [e, hγ0, positiveLink_translate_zero]
  have hι : Function.Injective (windowLinkClass W Γ) := fun c c' h =>
    Subtype.ext (congrArg (fun q : PositiveLink 1 => q.1) (hclass _ _ (hLM c.2) (hLM c'.2) h))
  have hout : ∀ b ∈ M, b ∉ W.links → AvoidsWindow W Γ b := by
    intro b hb hbW hp c h
    have e : b = c.1 := congrArg (fun q : PositiveLink 1 => q.1) (hclass _ _ hb (hLM c.2) h)
    exact hbW (e ▸ c.2)
  have hbase : ∀ {r : ElementaryPlaquette 1}, r ∈ facesMeeting (W.links : Set (Link 1)) →
      r.corner ∈ S := by
    intro r hr
    refine ⟨Link.forwardFrom r.corner r.lowAxis, hPM hr ?_, rfl⟩
    simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
  have hPinj : InjOn Γ.faceClass (facesMeeting (W.links : Set (Link 1))) := by
    intro p hp q hq h
    obtain ⟨hb, h₁, h₂⟩ := corner_sub_mem_of_faceClass_eq hfaith h
    exact ElementaryPlaquette.ext (hemb _ (hbase hp) _ (hbase hq) hb).symm h₁ h₂
  have hIinj : InjOn (labelCoset 𝔸 Γ) (𝔸.labelsTouching W) := by
    rintro ⟨v, ι⟩ hi ⟨v', ι'⟩ hi' h
    have h₁ : (QuotientAddGroup.mk v : 𝔸.Cosets Γ) = QuotientAddGroup.mk v' :=
      congrArg Prod.fst h
    have h₂ : ι = ι' := congrArg Prod.snd h
    subst h₂
    have hγ : ((v' : LatticePoint 1) - (v : LatticePoint 1)) ∈ Γ.periods := by
      have h₃ := QuotientAddGroup.eq.1 h₁
      rw [AddSubgroup.mem_addSubgroupOf] at h₃
      simpa [neg_add_eq_sub] using h₃
    obtain ⟨b, hbS, hbL⟩ := hi
    have hbL' : b ∈ W.links := hbL
    let bp : PositiveLink 1 := ⟨b, W.isPositive b hbL'⟩
    have hb' : (bp.translate ((v' : LatticePoint 1) - (v : LatticePoint 1))).1 ∈
        observableSupport (𝔸.translate (v', ι)) := by
      have e₁ := hsup.observableSupport_translate (v, ι)
      have e₂ := hsup.observableSupport_translate (v', ι)
      rw [e₁] at hbS
      rw [e₂]
      exact translate_mem_shiftLinks (hsupp _ (hgen ι)).2.1 bp hbS
    have hγ0 := hshift (htail (hLM hbL')) (htail (hIM hi' hb')) hγ
    refine Prod.ext (Subtype.ext ?_) rfl
    exact (sub_eq_zero.1 hγ0).symm
  have hPdep : ∀ (r : ElementaryPlaquette 1) (X Y : GaugeField 1),
      (∀ b ∈ r.linkSet, X b = Y b) → faceEnergy X r = faceEnergy Y r := fun r X Y h =>
    Complex.ofReal_injective ((hPl.2.2.2.2.1 r).2 X Y h)
  have hTdep : ∀ (i : 𝔸.Label) (X Y : GaugeField 1),
      (∀ b ∈ observableSupport (𝔸.translate i), X b = Y b) →
        𝔸.translate i X = 𝔸.translate i Y :=
    fun i X Y h => (hsupp _ (hterm i)).1 X Y h
  have hPout : ∀ (r : ElementaryPlaquette 1),
      Γ.faceClass r ∉ Γ.faceClass '' facesMeeting (W.links : Set (Link 1)) →
      ∀ b ∈ r.linkSet, b.IsPositivelyOriented ∧ AvoidsWindow W Γ b := by
    intro r hr b hb
    refine ⟨hpbp hb, fun hp c h => hr ?_⟩
    obtain ⟨γ, hγ, e⟩ := exists_period_of_linkClass_eq Γ h
    refine ⟨movedBy r γ, ⟨c.1, ?_, c.2⟩, faceClass_movedBy hfaith r hγ⟩
    have e' : c.1 = (PositiveLink.translate ⟨b, hp⟩ γ).1 := congrArg Subtype.val e
    rw [e']
    exact translate_mem_linkSet_movedBy r γ hb hp
  have hIout : ∀ k : 𝔸.Cosets Γ × Fin 𝔸.size, k ∉ labelCoset 𝔸 Γ '' 𝔸.labelsTouching W →
      ∀ b ∈ observableSupport (𝔸.translate (𝔸.cosetRep Γ k.1, k.2)),
        b.IsPositivelyOriented ∧ AvoidsWindow W Γ b := by
    rintro ⟨c, ι⟩ hk b hb
    have hbp : b.IsPositivelyOriented := (hsupp _ (hterm _)).2.1 hb
    refine ⟨hbp, fun hp d h => hk ?_⟩
    obtain ⟨γ, hγ, e⟩ := exists_period_of_linkClass_eq Γ h
    let v : 𝔸.sublattice := 𝔸.cosetRep Γ c
    let g : 𝔸.sublattice := ⟨γ, hΓ hγ⟩
    refine ⟨(v + g, ι), ⟨d.1, ?_, d.2⟩, ?_⟩
    · have e₁ := hsup.observableSupport_translate (v, ι)
      have e₂ := hsup.observableSupport_translate (v + g, ι)
      have hb₁ : b ∈ observableSupport (𝔸.translate (v, ι)) := hb
      rw [e₁] at hb₁
      rw [e₂]
      have h₂ := translate_mem_shiftLinks (v' := ((v + g : 𝔸.sublattice) : LatticePoint 1))
        (hsupp _ (hgen ι)).2.1 ⟨b, hp⟩ hb₁
      have hsub : ((v + g : 𝔸.sublattice) : LatticePoint 1) - (v : LatticePoint 1) = γ := by
        simp [g]
      rw [hsub, ← e] at h₂
      exact h₂
    · have hg : (QuotientAddGroup.mk g : 𝔸.Cosets Γ) = 0 := by
        refine (QuotientAddGroup.eq_zero_iff g).2 ?_
        rw [AddSubgroup.mem_addSubgroupOf]
        exact hγ
      have hv : (QuotientAddGroup.mk v : 𝔸.Cosets Γ) = c := Quotient.out_eq c
      refine Prod.ext ?_ rfl
      change (QuotientAddGroup.mk (v + g) : 𝔸.Cosets Γ) = c
      rw [QuotientAddGroup.mk_add, hg, add_zero, hv]
  obtain ⟨T, hfac, hT⟩ :=
    exists_tiltedWeight_factorization hfaith hextf hd hPinj hIinj hPdep hTdep hPout hIout
  have hext : Continuous Γ.lift := hextf.isEmbedding_lift.continuous
  have := hfaith.finite_quotientPlaquette
  have := hfaith.finite_quotientLink
  have hwc : Continuous (𝔸.tiltedWeight Γ β t) := by
    have := Fintype.ofFinite Γ.QuotientPlaquette
    have h₁ : Continuous fun U : Γ.QuotientField =>
        ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := by
      simp only [finsum_eq_sum_of_fintype]
      exact continuous_finsetSum _ fun p _ => hextf.continuous_quotientFaceEnergy p
    exact Real.continuous_exp.comp
      ((continuous_const.mul hd.continuous_periodicSum).sub (continuous_const.mul h₁))
  have hwpos : ∀ U, 0 ≤ 𝔸.tiltedWeight Γ β t U := fun U => (Real.exp_pos _).le
  have hagree : ∀ (V : W.Assignments) (U : Γ.QuotientField), ∀ b ∈ M,
      Γ.lift (replaceWindow W Γ V U) b = W.glue one_pos V (Γ.lift U) b := by
    intro V U b hb
    by_cases hbW : b ∈ W.links
    · rw [lift_replaceWindow_of_mem hι V U hbW, glue_of_mem V _ hbW]
    · rw [glue_of_not_mem V _ (hMpos b hb) hbW,
        lift_replaceWindow_of_avoids V U (hMpos b hb) (hout b hb hbW)]
  have hFdep : ∀ X Y : GaugeField 1, (∀ b ∈ M, X b = Y b) → F X = F Y :=
    fun X Y h => (hsupp F hF).1 X Y fun b hb => h b (hFM hb)
  have hEdep : ∀ X Y : GaugeField 1, (∀ b ∈ M, X b = Y b) →
      𝔸.windowEnergy β t W X = 𝔸.windowEnergy β t W Y := by
    intro X Y h
    have h₁ : ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy X p =
        ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy Y p :=
      finsum_mem_congr rfl fun p hp => hPdep p X Y fun b hb => h b (hPM hp hb)
    have h₂ : ∑ᶠ i ∈ 𝔸.labelsTouching W, (𝔸.translate i X).re =
        ∑ᶠ i ∈ 𝔸.labelsTouching W, (𝔸.translate i Y).re :=
      finsum_mem_congr rfl fun i hi =>
        congrArg Complex.re (hTdep i X Y fun b hb => h b (hIM hi hb))
    simp only [LocalObservableArray.windowEnergy, h₁, h₂]
  have hins : ∀ (V : W.Assignments) (X Y : GaugeField 1),
      (∀ b ∈ M, b ∉ W.links → X b = Y b) →
      ∀ b ∈ M, W.glue one_pos V X b = W.glue one_pos V Y b := by
    intro V X Y h b hb
    by_cases hbW : b ∈ W.links
    · rw [glue_of_mem V _ hbW, glue_of_mem V _ hbW]
    · rw [glue_of_not_mem V _ (hMpos b hb) hbW, glue_of_not_mem V _ (hMpos b hb) hbW]
      exact h b hb hbW
  have hHdep : ∀ X Y : GaugeField 1, (∀ b ∈ M, b ∉ W.links → X b = Y b) →
      𝔸.tiltedKernel β t W F X = 𝔸.tiltedKernel β t W F Y := by
    intro X Y h
    have h₁ : ∀ V : W.Assignments, F (W.glue one_pos V X) = F (W.glue one_pos V Y) :=
      fun V => hFdep _ _ (hins V X Y h)
    have h₂ : ∀ V : W.Assignments, 𝔸.windowEnergy β t W (W.glue one_pos V X) =
        𝔸.windowEnergy β t W (W.glue one_pos V Y) := fun V => hEdep _ _ (hins V X Y h)
    simp only [LocalObservableArray.tiltedKernel, LocalObservableArray.windowPartition, h₁, h₂]
  exact window_equation_of_factorization hG hι hext hwc hwpos hfac hT hF.2.2 hHloc.2.2
    (fun X => hspec.windowPartition_pos W X)
    (fun V U => hFdep _ _ (hagree V U)) (fun V U => hEdep _ _ (hagree V U))
    (fun V U => hHdep _ _ fun b hb hbW =>
      lift_replaceWindow_of_avoids V U (hMpos b hb) (hout b hb hbW))
end InfiniteLattice
end YangMills.Construction
