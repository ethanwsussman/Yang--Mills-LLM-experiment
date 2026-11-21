import YangMills.Construction.InfiniteLattice.ConfigurationsOfTheTorusLatticeAtPositiveLinks
import YangMills.Construction.InfiniteLattice.CoveringOnBondsAndPlaquettes
import YangMills.Construction.InfiniteLattice.EquilibriumEquationOfThePeriodicExtensions
import YangMills.Construction.InfiniteLattice.KernelAndOperatorOfAWindowAtOneSpacing
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions.LiftedEquilibriumEquation
open YangMills.Construction.Matrices
section Resampling
variable {S P : Type} [Finite S] [Finite P]
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem integral_extend_haarPi (hprod : ComplexMatrix2.FiniteProductGroupStatement)
    {ι : S → P} (hι : Function.Injective ι) {f : (P → ComplexMatrix2.specialUnitary) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ v, ‖f v‖ ≤ C) :
    ∫ v, (∫ V, f (Function.extend ι V v) ∂ComplexMatrix2.haarPi S) ∂ComplexMatrix2.haarPi P =
      ∫ v, f v ∂ComplexMatrix2.haarPi P := by
  classical
  have := secondCountableTopology_specialUnitary
  obtain ⟨-, -, hSp, -, hSr⟩ := hprod.2.1 S
  obtain ⟨-, -, hPp, hPl, -⟩ := hprod.2.1 P
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
  have hinner : ∀ v : P → ComplexMatrix2.specialUnitary,
      ∫ V, f (Function.extend ι V v) ∂ComplexMatrix2.haarPi S =
        ∫ V, f (e V * v) ∂ComplexMatrix2.haarPi S := by
    intro v
    simp only [hupd]
    exact integral_mul_right_eq_self (fun V => f (e V * v)) ((v ∘ ι)⁻¹)
  simp only [hinner]
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
      (V : S → ComplexMatrix2.specialUnitary) => f (e V * v))
      ((ComplexMatrix2.haarPi P).prod (ComplexMatrix2.haarPi S)) :=
    Integrable.of_bound (hf.comp hjoint).aestronglyMeasurable C (ae_of_all _ fun q => hC _)
  rw [integral_integral_swap hint]
  simp only [integral_mul_left_eq_self (μ := ComplexMatrix2.haarPi P) f]
  simp
end Resampling
section Values
variable {L m : ℕ} {j : ℤ}
theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem measurable_boltzmannWeight [Finite (PeriodicLattice.Plaquette L m j)] (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.boltzmannWeight_measurable <;> assumption
end Values
abbrev CutoffPositiveBond (d : CutoffLinks.CutoffData) : Type :=
  PeriodicLattice.PositivelyOrientedBond d.L d.m ((d.K : ℕ) : ℤ)
theorem exists_periodicField_of_positive
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    {d : CutoffLinks.CutoffData} (v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary) :
    ∃ U : d.PeriodicFields, (∀ l : CutoffPositiveBond d, U.linkValue l.1 = v l) ∧
      U.1 = PeriodicLattice.gaugeFieldOfPositive v := by
  obtain ⟨⟨-, -, -, hxor, hbij⟩, -⟩ := hlinks d
  obtain ⟨U, hU⟩ := hbij.2 fun l =>
    v ⟨l.1, PeriodicLattice.mem_positiveBonds_iff.1 l.2⟩
  have hval : ∀ l : CutoffPositiveBond d, U.linkValue l.1 = v l := fun l =>
    congrFun hU ⟨l.1, PeriodicLattice.mem_positiveBonds_iff.2 l.2⟩
  refine ⟨U, hval, ?_⟩
  funext b
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h]
    exact congrArg Subtype.val (hval ⟨b, h⟩)
  · have h' : b.opposite.IsPositivelyOriented := by
      rcases hxor b with h₁ | h₁
      · exact absurd (PeriodicLattice.mem_positiveBonds_iff.1 h₁.1) h
      · obtain ⟨l', hl', rfl⟩ := h₁.1
        exact PeriodicLattice.mem_positiveBonds_iff.1 hl'
    rw [dif_neg h, dif_pos h']
    have e := U.2.2 b.opposite (mem_univ _)
    have hr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    rw [hr] at e
    have e₂ : U.1 b.opposite = ((v ⟨b.opposite, h'⟩ : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2) :=
      congrArg Subtype.val (hval ⟨b.opposite, h'⟩)
    rw [e, e₂]
theorem integralAgainst_liftedWilsonMeasure {d : CutoffLinks.CutoffData}
    [Finite d.PeriodicPlaquette] {G : GaugeField d.spacing → ℝ} (hG : Measurable G) :
    CutoffLattice.integralAgainst (liftedWilsonMeasure d.L d.m d.K d.coupling) G =
      (ENNReal.ofReal (PeriodicLattice.partitionFunction d.L d.m d.K d.coupling))⁻¹.toReal •
        ∫ v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary,
          PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v) *
            G (liftField d.L d.m ((d.K : ℕ) : ℤ) (PeriodicLattice.gaugeFieldOfPositive v))
          ∂ComplexMatrix2.haarPi (CutoffPositiveBond d) := by
  have hlift := measurable_liftField d.L d.m ((d.K : ℕ) : ℤ)
  have hpos := measurable_gaugeFieldOfPositive (L := d.L) (m := d.m) (j := ((d.K : ℕ) : ℤ))
  have hw := measurable_boltzmannWeight (L := d.L) (m := d.m) (j := ((d.K : ℕ) : ℤ)) d.coupling
  have hGl : Measurable fun U => G (liftField d.L d.m ((d.K : ℕ) : ℤ) U) := hG.comp hlift
  have e₁ : CutoffLattice.integralAgainst (liftedWilsonMeasure d.L d.m d.K d.coupling) G =
      ∫ U, G (liftField d.L d.m ((d.K : ℕ) : ℤ) U)
        ∂PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling :=
    integral_map hlift.aemeasurable hG.aestronglyMeasurable
  rw [e₁, PeriodicLattice.wilsonGibbsMeasure, integral_smul_measure]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hnn : ∀ U : PeriodicLattice.Bond d.L d.m ((d.K : ℕ) : ℤ) → ComplexMatrix2,
      0 ≤ PeriodicLattice.boltzmannWeight d.coupling U := fun U => (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
  exact integral_map hpos.aemeasurable (hw.mul hGl).aestronglyMeasurable
theorem holds
    (hprod : ComplexMatrix2.FiniteProductGroupStatement)
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    (hcov : Covering.CoveringProperties)
    (hop : WindowKernelOperatorProperties) :
    Statement := by
  classical
  intro d W S _ _ hWS hbS hinj F hF hFC hread
  obtain ⟨⟨-, hBf, hPf, -, -⟩, hact, -, -⟩ := hlinks d
  have := hBf
  have := hPf
  have hPos : Finite (CutoffPositiveBond d) := Subtype.finite
  have ha := d.spacing_pos
  obtain ⟨-, hcact, -, -, -, -, hWall⟩ := hcov d.toStandingParameters
  have hweight : ∀ (V : W.Assignments) (U : GaugeField d.spacing),
      W.boltzmannWeight d.spacing_pos d.coupling V U =
        Real.exp (-d.coupling * ∑ᶠ p ∈ W.faces, faceEnergy (W.glue d.spacing_pos V U) p) :=
    fun _ _ => rfl
  have hFb : TestFunctions.IsBoundedFun F := by
    obtain ⟨C, hC⟩ := hFC
    exact ⟨C, fun U => by simpa [Real.norm_eq_abs] using hC U⟩
  obtain ⟨hγm, ⟨Cγ, hCγ⟩, -, -, hγr⟩ := (hop d W).2.1 F hF hFb
  have hone := (hop d W).1.1
  have hSpos : ∀ b ∈ S, b.IsPositivelyOriented := fun b hb =>
    mem_positiveLinks_iff.1 (hread.1 hb)
  have pos : ∀ b : Link d.spacing, b.IsPositivelyOriented →
      (d.projLink b).IsPositivelyOriented := by
    intro b hb
    obtain ⟨x, κ, rfl⟩ := mem_positiveLinks_iff.2 hb
    rw [d.projLink_forwardFrom]
    exact PeriodicLattice.mem_positiveBonds_iff.1 ⟨_, _, rfl⟩
  let ι : W.links → CutoffPositiveBond d := fun b => ⟨d.projLink b, pos b (W.isPositive b b.2)⟩
  have hι : Function.Injective ι := fun b b' h => Subtype.ext
    (hinj (hWS (Finset.mem_coe.2 b.2)) (hWS (Finset.mem_coe.2 b'.2)) (congrArg Subtype.val h))
  have hout : ∀ b (hb : b ∈ S), b ∉ W.links → ∀ hp, ¬ ∃ s, ι s = ⟨d.projLink b, hp⟩ := by
    rintro b hb hbW hp ⟨s, hs⟩
    have e : (s : Link d.spacing) = b :=
      hinj (hWS (Finset.mem_coe.2 s.2)) hb (congrArg Subtype.val hs)
    exact hbW (e ▸ s.2)
  choose Uc hUval hUcfg using fun v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary =>
    exists_periodicField_of_positive hlinks (d := d) v
  let T : (CutoffPositiveBond d → ComplexMatrix2.specialUnitary) → GaugeField d.spacing :=
    fun v => liftField d.L d.m ((d.K : ℕ) : ℤ) (PeriodicLattice.gaugeFieldOfPositive v)
  have hT : ∀ v, T v = liftCompactField (Uc v) := by
    intro v
    change liftField _ _ _ _ = liftField _ _ _ (Uc v).1
    rw [hUcfg v]
  have hTv : ∀ v (b : Link d.spacing) (hb : b.IsPositivelyOriented),
      T v b = v ⟨d.projLink b, pos b hb⟩ := by
    intro v b hb
    rw [hT, liftCompactField_apply]
    exact hUval v ⟨d.projLink b, pos b hb⟩
  have hkeep : ∀ (V : W.Assignments) v, ∀ b ∈ S, b ∉ W.links →
      T (Function.extend ι V v) b = T v b := by
    intro V v b hb hbW
    rw [hTv _ b (hSpos b hb), hTv v b (hSpos b hb)]
    exact Function.extend_apply' _ _ _ (hout b hb hbW _)
  have hagree : ∀ (V : W.Assignments) v, ∀ b ∈ S,
      T (Function.extend ι V v) b = W.glue ha V (T v) b := by
    intro V v b hb
    by_cases hbW : b ∈ W.links
    · rw [hTv _ b (hSpos b hb)]
      have e : (⟨d.projLink b, pos b (hSpos b hb)⟩ : CutoffPositiveBond d) = ι ⟨b, hbW⟩ := rfl
      rw [e, hι.extend_apply]
      simp [LinkWindow.glue, hbW]
    · have hrev : b.opposite ∉ W.links := fun h' =>
        Link.opposite_not_isPositivelyOriented ha (hSpos b hb) (W.isPositive _ h')
      rw [hkeep V v b hb hbW]
      simp [LinkWindow.glue, hbW, hrev]
  have hFT : ∀ (V : W.Assignments) v,
      F (T (Function.extend ι V v)) = F (W.glue ha V (T v)) :=
    fun V v => hread.2 _ _ (funext fun b => hagree V v b b.2)
  have hγT : ∀ (V : W.Assignments) v,
      W.realOperator ha d.coupling F (T (Function.extend ι V v)) =
        W.realOperator ha d.coupling F (T v) := by
    intro V v
    refine (hγr S hread).2 _ _ (funext fun b => ?_)
    have hb : (b : Link d.spacing) ∈ S ∧ (b : Link d.spacing) ∉ W.links := by
      rcases b.2 with h | h
      · exact ⟨h.1, fun h' => h.2 (Finset.mem_coe.2 h')⟩
      · exact ⟨hbS h, h.2⟩
    exact hkeep V v b hb.1 hb.2
  obtain ⟨hbij, -⟩ := (hWall W).1 (hinj.mono (union_subset hWS hbS))
  set Q : Set d.PeriodicPlaquette := CutoffLattice.projectFace d.L d.m d.K '' W.faces
    with hQdef
  have hQ : Q = {P | TorusPlaquetteHasEdgeIn P
      (projectLink d.L d.m ((d.K : ℕ) : ℤ) '' (W.links : Set _))} :=
    hbij.image_eq
  let A₂ : (CutoffPositiveBond d → ComplexMatrix2.specialUnitary) → ℝ :=
    fun v => ∑ᶠ P ∈ (univ \ Q), d.faceAction P (Uc v)
  let A₁ : (CutoffPositiveBond d → ComplexMatrix2.specialUnitary) → ℝ :=
    fun v => ∑ᶠ p ∈ W.faces, faceEnergy (T v) p
  have hρ : ∀ v, PeriodicLattice.boltzmannWeight d.coupling
      (PeriodicLattice.gaugeFieldOfPositive v) =
        Real.exp (-d.coupling * A₁ v) * Real.exp (-d.coupling * A₂ v) := by
    intro v
    have h₁ : PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
        (∑ᶠ P ∈ Q, d.faceAction P (Uc v)) + A₂ v := by
      rw [← hUcfg v]
      have e := finsum_mem_add_sdiff (subset_univ Q) finite_univ
        (f := fun P => d.faceAction P (Uc v))
      rw [finsum_mem_univ] at e
      exact e.symm
    have h₂ : ∑ᶠ P ∈ Q, d.faceAction P (Uc v) = A₁ v := by
      rw [hQdef, finsum_mem_image hbij.injOn]
      refine finsum_mem_congr rfl fun p _ => ?_
      rw [hT]
      exact (hcact p (Uc v)).symm
    rw [PeriodicLattice.boltzmannWeight, h₁, h₂, ← Real.exp_add]
    congr 1
    ring
  have hA₂ : ∀ (V : W.Assignments) v, A₂ (Function.extend ι V v) = A₂ v := by
    intro V v
    refine finsum_mem_congr rfl fun P hP => (hact P).2.2 _ _ fun l hl => ?_
    simp only [CutoffLinks.CutoffData.FaceContains, WilsonOperator.periodicEdgeList,
      List.mem_cons, List.not_mem_nil, or_false] at hl
    have hlpos : l.IsPositivelyOriented := by
      rcases hl with rfl | rfl | rfl | rfl <;>
        exact PeriodicLattice.mem_positiveBonds_iff.1 ⟨_, _, rfl⟩
    have hl' : ¬ ∃ s, ι s = ⟨l, hlpos⟩ := by
      rintro ⟨s, hs⟩
      have hm : l ∈ projectLink d.L d.m ((d.K : ℕ) : ℤ) '' (W.links : Set _) :=
        ⟨s, Finset.mem_coe.2 s.2, congrArg Subtype.val hs⟩
      refine hP.2 ?_
      rw [hQ]
      change TorusPlaquetteHasEdgeIn P _
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr (Or.inl hm))
      · exact Or.inr (Or.inr (Or.inr hm))
    exact ((hUval _ ⟨l, hlpos⟩).trans (Function.extend_apply' _ _ _ hl')).trans
      (hUval v ⟨l, hlpos⟩).symm
  have hρE : ∀ (V : W.Assignments) v, PeriodicLattice.boltzmannWeight d.coupling
      (PeriodicLattice.gaugeFieldOfPositive (Function.extend ι V v)) =
        W.boltzmannWeight ha d.coupling V (T v) * Real.exp (-d.coupling * A₂ v) := by
    intro V v
    have e : A₁ (Function.extend ι V v) =
        ∑ᶠ p ∈ W.faces, faceEnergy (W.glue ha V (T v)) p := by
      refine finsum_mem_congr rfl fun p hp => ?_
      have key : ∀ b ∈ p.edges, T (Function.extend ι V v) b = W.glue ha V (T v) b := by
        intro b hb
        refine hagree V v b ?_
        by_cases hbW : b ∈ W.links
        · exact hWS (Finset.mem_coe.2 hbW)
        · exact hbS ⟨⟨p, hp, hb⟩, hbW⟩
      simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at key
      obtain ⟨h1, h2, h3, h4⟩ := key
      simp only [faceEnergy, faceHolonomy, h1, h2, h3, h4]
    rw [hρ, hA₂, e, hweight]
  have hρle : ∀ v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary,
      ‖PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v)‖ ≤ 1 := by
    intro v
    rw [Real.norm_eq_abs, ← hUcfg v, PeriodicLattice.boltzmannWeight,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have h0 : 0 ≤ PeriodicLattice.wilsonAction (Uc v).1 :=
      finsum_nonneg fun P => ((hact P).2.1 (Uc v)).1
    nlinarith [d.coupling_pos]
  have hcfg := measurable_gaugeFieldOfPositive (L := d.L) (m := d.m) (j := ((d.K : ℕ) : ℤ))
  have hlift := measurable_liftField d.L d.m ((d.K : ℕ) : ℤ)
  have hden := measurable_boltzmannWeight (L := d.L) (m := d.m) (j := ((d.K : ℕ) : ℤ))
    d.coupling
  have hTm : Measurable T := hlift.comp hcfg
  have hρm : Measurable fun v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v) :=
    hden.comp hcfg
  obtain ⟨C, hC⟩ := hFb
  have hCγ0 : 0 ≤ Cγ := (norm_nonneg _).trans (hCγ (trivialField d.spacing))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (trivialField d.spacing))
  have hbound : ∀ {B : ℝ} {G : GaugeField d.spacing → ℝ}, 0 ≤ B → (∀ U, ‖G U‖ ≤ B) →
      ∀ v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary,
        ‖PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v) *
          G (T v)‖ ≤ B := by
    intro B G hB hG v
    rw [norm_mul]
    calc _ ≤ 1 * B := mul_le_mul (hρle v) (hG _) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  rw [integralAgainst_liftedWilsonMeasure hγm, integralAgainst_liftedWilsonMeasure hF]
  congr 1
  have r₁ := integral_extend_haarPi hprod hι
    (f := fun v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v) *
      W.realOperator ha d.coupling F (T v)) (hρm.mul (hγm.comp hTm)) (hbound hCγ0 hCγ)
  have r₂ := integral_extend_haarPi hprod hι
    (f := fun v : CutoffPositiveBond d → ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight d.coupling (PeriodicLattice.gaugeFieldOfPositive v) *
        F (T v))
    (hρm.mul (hF.comp hTm)) (hbound hC0 hC)
  refine r₁.symm.trans (Eq.trans ?_ r₂)
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [hρE, hγT, hFT]
  set z : ℝ := ∫ V, W.boltzmannWeight ha d.coupling V (T v) ∂ComplexMatrix2.haarPi W.links
    with hzdef
  have hk : ∀ V : W.Assignments, W.rimKernel ha d.coupling V (W.restrictRim (T v)) =
      W.boltzmannWeight ha d.coupling V (T v) / z := fun V => by
    rw [W.rimKernel_restrictRim]
    rfl
  have hz : z ≠ 0 := by
    intro h0
    have h1 := hone (W.restrictRim (T v))
    simp only [hk, h0, div_zero, integral_zero] at h1
    exact zero_ne_one h1
  have hγv : W.realOperator ha d.coupling F (T v) =
      (∫ V, F (W.glue ha V (T v)) * W.boltzmannWeight ha d.coupling V (T v)
        ∂ComplexMatrix2.haarPi W.links) / z := by
    have e : W.realOperator ha d.coupling F (T v) =
        ∫ V, (F (W.glue ha V (T v)) * W.boltzmannWeight ha d.coupling V (T v)) / z
          ∂ComplexMatrix2.haarPi W.links := by
      refine integral_congr_ae (ae_of_all _ fun V => ?_)
      simp only [hk, mul_div_assoc]
    rw [e, integral_div]
  have e₁ : ∀ V : W.Assignments, W.boltzmannWeight ha d.coupling V (T v) *
      Real.exp (-d.coupling * A₂ v) * W.realOperator ha d.coupling F (T v) =
      W.boltzmannWeight ha d.coupling V (T v) *
        (Real.exp (-d.coupling * A₂ v) * W.realOperator ha d.coupling F (T v)) :=
    fun V => by ring
  have e₂ : ∀ V : W.Assignments, W.boltzmannWeight ha d.coupling V (T v) *
      Real.exp (-d.coupling * A₂ v) * F (W.glue ha V (T v)) =
      F (W.glue ha V (T v)) * W.boltzmannWeight ha d.coupling V (T v) *
        Real.exp (-d.coupling * A₂ v) :=
    fun V => by ring
  simp only [e₁, e₂]
  rw [integral_mul_const, integral_mul_const, ← hzdef, hγv]
  field_simp
end YangMills.Construction.InfiniteLattice.PeriodicExtensions.LiftedEquilibriumEquation
