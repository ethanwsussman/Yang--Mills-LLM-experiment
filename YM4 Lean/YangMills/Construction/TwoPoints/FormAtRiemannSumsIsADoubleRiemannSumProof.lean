import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.TwoPoints.ApproximateIdentitiesAndTheirTranslatesProof
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreeProperties
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSum
import YangMills.Construction.TwoPoints.PairingOfTranslatesIsContinuous
import YangMills.Construction.TwoPoints.TermsOfARiemannSum
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace GridSumForm
theorem euclidNorm_eq_norm_toLp (x : AmbientSpace) :
    euclidNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.TwoPoints.MollifierBump.euclidNorm_eq_norm_toLp <;> assumption
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem continuous_euclidNorm : Continuous (euclidNorm : AmbientSpace → ℝ) := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem exists_sep_margin {A B : Set AmbientSpace} (hA : IsCompact A) (hB : IsCompact B) {ε : ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ B, 2 * ε < euclidNorm (y - x)) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ A, ∀ y ∈ B, 2 * ε + η ≤ euclidNorm (y - x) := by
  have hcomp : IsCompact (A ×ˢ B) := hA.prod hB
  have hcont : ContinuousOn (fun p : AmbientSpace × AmbientSpace => euclidNorm (p.2 - p.1))
      (A ×ˢ B) :=
    (continuous_euclidNorm.comp (continuous_snd.sub continuous_fst)).continuousOn
  rcases (A ×ˢ B).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hx y hy => ?_⟩
    have hm : (x, y) ∈ A ×ˢ B := ⟨hx, hy⟩
    rw [he] at hm
    exact hm.elim
  · obtain ⟨p, hp, hmin⟩ := hcomp.exists_isMinOn hne hcont
    refine ⟨euclidNorm (p.2 - p.1) - 2 * ε, sub_pos.2 (hsep _ hp.1 _ hp.2),
      fun x hx y hy => ?_⟩
    have hle : euclidNorm (p.2 - p.1) ≤ euclidNorm ((x, y).2 - (x, y).1) :=
      hmin (show (x, y) ∈ A ×ˢ B from ⟨hx, hy⟩)
    linarith
theorem finite_gridCubes_meeting {A : Set AmbientSpace} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    {j : Fin 4 → ℤ | ∃ z ∈ A, z ∈ gridCube δ j}.Finite := by
  obtain ⟨C, hC⟩ := hA.isBounded.exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin 4 => ⌊-C / δ⌋ - 1) (fun _ => ⌈C / δ⌉)).subset ?_
  rintro j ⟨z, hz, hj⟩
  have hbound : ∀ μ, |z μ| ≤ C := fun μ => (norm_le_pi_norm z μ).trans (hC z hz)
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · obtain ⟨-, b⟩ := hj μ
    have hz' := (abs_le.1 (hbound μ)).1
    have h : ((⌊-C / δ⌋ : ℤ) : ℝ) < (j μ : ℝ) + 1 :=
      lt_of_le_of_lt (Int.floor_le _) (by rw [div_lt_iff₀ hδ]; linarith)
    have h' : ⌊-C / δ⌋ < j μ + 1 := by exact_mod_cast h
    show ⌊-C / δ⌋ - 1 ≤ j μ
    omega
  · obtain ⟨a, -⟩ := hj μ
    have hz' := (abs_le.1 (hbound μ)).2
    have h : (j μ : ℝ) ≤ ((⌈C / δ⌉ : ℤ) : ℝ) :=
      le_trans (by rw [le_div_iff₀ hδ]; linarith) (Int.le_ceil _)
    show j μ ≤ ⌈C / δ⌉
    exact_mod_cast h
theorem actOn_addRight (v : AmbientSpace) (f : AmbientSpace → ℂ) :
    actOn (Equiv.addRight v) f = translateFun v f := by
  funext x
  show f ((Equiv.addRight v)⁻¹ x) = f (x - v)
  rw [Equiv.Perm.inv_def]
  simp [sub_eq_add_neg]
theorem addRight_mem_euclideanMotions (v : AmbientSpace) :
    Equiv.addRight v ∈ euclideanMotions :=
  ⟨1, hyperoctahedralPerms.one_mem, v, fun _ => rfl⟩
theorem isDisjointSupportPair_symm {f g : AmbientSpace → ℂ} (p : IsDisjointSupportPair f g) :
    IsDisjointSupportPair g f :=
  ⟨p.2.1, p.1, Disjoint.symm p.2.2⟩
theorem isDisjointSupportPair_zero_left {g : AmbientSpace → ℂ} (hg : g ∈ compactC1Complex) :
    IsDisjointSupportPair 0 g :=
  ⟨compactC1Complex.zero_mem, hg, disjointSupports_zero_left g⟩
theorem complexifyForm_sum {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hL : ComplexifyLinear S) {ι : Type*} (F : Finset ι) (c : ι → ℂ) (f : ι → AmbientSpace → ℂ)
    {g : AmbientSpace → ℂ} (hg : g ∈ compactC1Complex)
    (hf : ∀ i ∈ F, IsDisjointSupportPair (f i) g) :
    IsDisjointSupportPair (∑ i ∈ F, c i • f i) g ∧
      complexifyForm S (∑ i ∈ F, c i • f i) g = ∑ i ∈ F, c i * complexifyForm S (f i) g ∧
      complexifyForm S g (∑ i ∈ F, c i • f i) = ∑ i ∈ F, c i * complexifyForm S g (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have p := isDisjointSupportPair_zero_left hg
    have e := hL 0 0 0 0 g p p
    simp only [zero_smul, add_zero, zero_mul] at e
    simpa using e
  | insert i F hi ih =>
    have ih' := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have e := hL (c i) 1 (f i) (∑ j ∈ F, c j • f j) g (hf i (Finset.mem_insert_self i F)) ih'.1
    simp only [one_smul, one_mul] at e
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨e.1, e.2.1.trans (by rw [ih'.2.1]), e.2.2.trans (by rw [ih'.2.2])⟩
theorem complexifyForm_sum_sum {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hL : ComplexifyLinear S) {ι κ : Type*} (F : Finset ι) (G : Finset κ) (c : ι → ℂ)
    (d : κ → ℂ) (f : ι → AmbientSpace → ℂ) (g : κ → AmbientSpace → ℂ)
    (hf : ∀ i, f i ∈ compactC1Complex) (hg : ∀ j, g j ∈ compactC1Complex)
    (hp : ∀ i ∈ F, ∀ j ∈ G, IsDisjointSupportPair (f i) (g j)) :
    complexifyForm S (∑ i ∈ F, c i • f i) (∑ j ∈ G, d j • g j) =
      ∑ i ∈ F, ∑ j ∈ G, c i * d j * complexifyForm S (f i) (g j) := by
  have hG : (∑ j ∈ G, d j • g j) ∈ compactC1Complex :=
    compactC1Complex.sum_mem fun j _ => compactC1Complex.smul_mem _ (hg j)
  have step : ∀ i ∈ F, IsDisjointSupportPair (f i) (∑ j ∈ G, d j • g j) ∧
      complexifyForm S (f i) (∑ j ∈ G, d j • g j) =
        ∑ j ∈ G, d j * complexifyForm S (f i) (g j) := by
    intro i hi
    have e := complexifyForm_sum hL G d g (hf i) fun j hj =>
      isDisjointSupportPair_symm (hp i hi j hj)
    exact ⟨isDisjointSupportPair_symm e.1, e.2.2⟩
  rw [(complexifyForm_sum hL F c f hG fun i hi => (step i hi).1).2.1]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(step i hi).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end GridSumForm
open GridSumForm in
theorem FormOnGridSumsIsPairedSum.proof (h₁ : AdmissibleFormConsequences.Statement)
    (h₂ : RiemannSumTermProperties.Statement) (h₃ : ShiftPairingContinuity.Statement) :
    FormOnGridSumsIsPairedSum.Statement := by
  intro St S hS hP ε hε φ₁ hφ₁ φ₂ hφ₂ k₁ hk₁ k₂ hk₂ hsep
  obtain ⟨C₂, hC₂⟩ := hP.ballDecay
  obtain ⟨-, -, -, hmaps, hext⟩ := h₁
  obtain ⟨⟨-, hL, hI, -, -⟩, -⟩ := hext St S C₂ hS hP hC₂
  have hφ₁' : ContDiff ℝ 1 φ₁ ∧ IsCompact (tsupport φ₁) ∧
      tsupport φ₁ ⊆ euclidOpenBall (0 : AmbientSpace) ε := hφ₁
  have hφ₂' : ContDiff ℝ 1 φ₂ ∧ IsCompact (tsupport φ₂) ∧
      tsupport φ₂ ⊆ euclidOpenBall (0 : AmbientSpace) ε := hφ₂
  have hc₁ : φ₁ ∈ compactC1Complex := ⟨hφ₁'.1, hφ₁'.2.1, subset_univ _⟩
  have hc₂ : φ₂ ∈ compactC1Complex := ⟨hφ₂'.1, hφ₂'.2.1, subset_univ _⟩
  have hK₁ := ((mem_ccIn_iff _ _).1 hk₁).2.1
  have hK₂ := ((mem_ccIn_iff _ _).1 hk₂).2.1
  obtain ⟨η, hη, hgap⟩ := exists_sep_margin hK₁ hK₂ hsep
  refine ⟨η / 2, half_pos hη, fun δ hδ hδη => ?_⟩
  have hT₁ := h₂ k₁ hk₁ φ₁ hc₁ δ hδ
  have hT₂ := h₂ k₂ hk₂ φ₂ hc₂ δ hδ
  have hpairing := (h₃ St S hS hP ε hε φ₁ hφ₁ φ₂ hφ₂).1
  have hfin₁ : {j : Fin 4 → ℤ | setIntegralOf (gridCube δ j) k₁ ≠ 0}.Finite :=
    (finite_gridCubes_meeting hK₁ hδ).subset fun j hj => hT₁.2.2.1 j hj
  have hfin₂ : {j : Fin 4 → ℤ | setIntegralOf (gridCube δ j) k₂ ≠ 0}.Finite :=
    (finite_gridCubes_meeting hK₂ hδ).subset fun j hj => hT₂.2.2.1 j hj
  set F₁ := hfin₁.toFinset with hF₁
  set F₂ := hfin₂.toFinset with hF₂
  have mem₁ : ∀ j, j ∈ F₁ ↔ setIntegralOf (gridCube δ j) k₁ ≠ 0 := fun j => by simp [hF₁]
  have mem₂ : ∀ j, j ∈ F₂ ↔ setIntegralOf (gridCube δ j) k₂ ≠ 0 := fun j => by simp [hF₂]
  have hfar : ∀ i ∈ F₁, ∀ j ∈ F₂,
      gridCenter δ j - gridCenter δ i ∈ farShifts ε := by
    intro i hi j hj
    obtain ⟨z₁, m₁, q₁⟩ := hT₁.2.2.1 i ((mem₁ i).1 hi)
    obtain ⟨z₂, m₂, q₂⟩ := hT₂.2.2.1 j ((mem₂ j).1 hj)
    have b₁ := hT₁.2.1 i z₁ q₁
    have b₂ := hT₂.2.1 j z₂ q₂
    have hg := hgap z₁ m₁ z₂ m₂
    have e : z₂ - z₁ = (z₂ - gridCenter δ j) +
        ((gridCenter δ j - gridCenter δ i) + -(z₁ - gridCenter δ i)) := by abel
    have t₁ := euclidNorm_add_le (z₂ - gridCenter δ j)
      ((gridCenter δ j - gridCenter δ i) + -(z₁ - gridCenter δ i))
    have t₂ := euclidNorm_add_le (gridCenter δ j - gridCenter δ i) (-(z₁ - gridCenter δ i))
    rw [euclidNorm_neg] at t₂
    rw [← e] at t₁
    show 2 * ε ≤ euclidNorm (gridCenter δ j - gridCenter δ i)
    linarith
  have hvalue : ∀ i ∈ F₁, ∀ j ∈ F₂,
      IsDisjointSupportPair (translateFun (gridCenter δ i) φ₁)
          (translateFun (gridCenter δ j) φ₂) ∧
        complexifyForm S (translateFun (gridCenter δ i) φ₁) (translateFun (gridCenter δ j) φ₂) =
          shiftPairing S φ₁ φ₂ (gridCenter δ j - gridCenter δ i) := by
    intro i hi j hj
    obtain ⟨a, b⟩ := hpairing _ (hfar i hi j hj)
    have e := hI _ (addRight_mem_euclideanMotions (gridCenter δ i)) φ₁
      (translateFun (gridCenter δ j - gridCenter δ i) φ₂) ⟨hc₁, a, b⟩
    have ht : translateFun (gridCenter δ i) (translateFun (gridCenter δ j - gridCenter δ i) φ₂) =
        translateFun (gridCenter δ j) φ₂ := by
      funext x
      show φ₂ (x - gridCenter δ i - (gridCenter δ j - gridCenter δ i)) = φ₂ (x - gridCenter δ j)
      congr 1
      abel
    rw [actOn_addRight, actOn_addRight, ht] at e
    exact e
  have hsum₁ : cubeRiemannSum δ k₁ φ₁ =
      ∑ j ∈ F₁, setIntegralOf (gridCube δ j) k₁ • translateFun (gridCenter δ j) φ₁ := by
    refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
    refine Finset.mem_coe.2 ((mem₁ j).2 fun h0 => hj ?_)
    simp [h0]
  have hsum₂ : cubeRiemannSum δ k₂ φ₂ =
      ∑ j ∈ F₂, setIntegralOf (gridCube δ j) k₂ • translateFun (gridCenter δ j) φ₂ := by
    refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
    refine Finset.mem_coe.2 ((mem₂ j).2 fun h0 => hj ?_)
    simp [h0]
  have hdouble : pairedGridSum δ k₁ k₂ (shiftPairing S φ₁ φ₂) =
      ∑ p ∈ F₁ ×ˢ F₂, setIntegralOf (gridCube δ p.1) k₁ * setIntegralOf (gridCube δ p.2) k₂ *
        shiftPairing S φ₁ φ₂ (gridCenter δ p.2 - gridCenter δ p.1) := by
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨(mem₁ _).2 fun h0 => hp ?_,
      (mem₂ _).2 fun h0 => hp ?_⟩)
    · simp [h0]
    · simp [h0]
  rw [hsum₁, hsum₂, hdouble, Finset.sum_product,
    complexifyForm_sum_sum hL F₁ F₂ _ _ _ _ (fun j => ((hmaps St).1 φ₁ hc₁ |>.1 _).1.mem)
      (fun j => ((hmaps St).1 φ₂ hc₂ |>.1 _).1.mem) fun i hi j hj => (hvalue i hi j hj).1]
  exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    rw [(hvalue i hi j hj).2]
end YangMills.Construction.TwoPoints
end
