import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import YangMills.Construction.ReflectionPositivity.CrossingIntegralIsAReflectedSeriesAtAnIntegerPosition
import YangMills.Construction.ReflectionPositivity.CrossingWeightExpansion
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCut
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import YangMills.Construction.ReflectionPositivity.ReflectedSeriesMultiply
import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies YangMills.Construction.SpinHarmonics
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.ReflectionPositivity.CrossingWeight (CharacterFamily chosenExpansion weightAt)
namespace CrossingIntegralAtIntegerLevel
variable (Γ : PeriodSublattice 1)
private theorem re_fullTrace_mul_inv_symm (g h : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace ((h * g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re := by
  have hinv : ∀ u : ComplexMatrix2.specialUnitary,
      ((u⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (u : ComplexMatrix2).conjTranspose :=
    fun _ => rfl
  have e : h * g⁻¹ = (g * h⁻¹)⁻¹ := by group
  rw [e, hinv, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose]
  simp
private theorem integrateOut_empty (f : Γ.QuotientField → ℂ)
    {𝓜 : Set Γ.QuotientLink} (h : 𝓜 = ∅) : Γ.integrateOut 𝓜 f = f := by
  subst h
  funext U
  have hj : ∀ V : ↥(∅ : Set Γ.QuotientLink) → ComplexMatrix2.specialUnitary,
      SpinHarmonics.glue (∅ : Set Γ.QuotientLink) V
        (SpinHarmonics.restrictTo (∅ : Set Γ.QuotientLink)ᶜ U) = U := by
    intro V
    funext b
    exact SpinHarmonics.glue_of_notMem (∅ : Set Γ.QuotientLink) V _ ⟨b, by simp⟩
  simp only [PeriodSublattice.integrateOut, hj]
  simp
private theorem linkClass_mem_plusLinks (n : AmbientSpace) (z : ℤ) (c : ℝ) (b : PositiveLink 1)
    (h₁ : c ≤ n ⬝ᵥ (b.1.initial : AmbientSpace)) (h₂ : n ⬝ᵥ (b.1.initial : AmbientSpace) ≤ c + (z : ℝ))
    (h₃ : c ≤ n ⬝ᵥ (b.1.terminal : AmbientSpace))
    (h₄ : n ⬝ᵥ (b.1.terminal : AmbientSpace) ≤ c + (z : ℝ)) :
    Γ.linkClass b ∈ Γ.plusLinks n z c := by
  obtain ⟨γ, hγ, h⟩ := Γ.exists_linkRep_eq b
  have site : ∀ x : LatticePoint 1, c ≤ n ⬝ᵥ (x : AmbientSpace) →
      n ⬝ᵥ (x : AmbientSpace) ≤ c + (z : ℝ) → Γ.quotientMap x ∈ Γ.plusHalf n z c :=
    fun x k₁ k₂ => ⟨n ⬝ᵥ (x : AmbientSpace), ⟨x, rfl, 0, by simp⟩, k₁, k₂⟩
  have proj : ∀ x : LatticePoint 1, Γ.quotientMap (x + γ) = Γ.quotientMap x := by
    intro x
    have h0 : Γ.quotientMap γ = 0 := (QuotientAddGroup.eq_zero_iff γ).2 hγ
    rw [map_add, h0, add_zero]
  intro s hs
  rw [PeriodSublattice.linkEndpoints, h] at hs
  rcases hs with rfl | hs
  · change Γ.quotientMap (b.1.initial + γ) ∈ _
    rw [proj]
    exact site _ h₁ h₂
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    change Γ.quotientMap (b.1.terminal + γ) ∈ _
    rw [proj]
    exact site _ h₃ h₄
private theorem liftValue_continuous_dependsOn (n : AmbientSpace) (z : ℤ) (c : ℝ) (b : Link 1)
    (h₁ : c ≤ n ⬝ᵥ (b.initial : AmbientSpace)) (h₂ : n ⬝ᵥ (b.initial : AmbientSpace) ≤ c + (z : ℝ))
    (h₃ : c ≤ n ⬝ᵥ (b.terminal : AmbientSpace))
    (h₄ : n ⬝ᵥ (b.terminal : AmbientSpace) ≤ c + (z : ℝ)) :
    Continuous (fun U : Γ.QuotientField => Γ.liftValue U b) ∧
      PeriodSublattice.DependsOnlyOn (fun U : Γ.QuotientField => Γ.liftValue U b)
        (Γ.plusLinks n z c) := by
  by_cases hp : b.IsPositivelyOriented
  · have hB := linkClass_mem_plusLinks Γ n z c ⟨b, hp⟩ h₁ h₂ h₃ h₄
    have e : (fun U : Γ.QuotientField => Γ.liftValue U b) =
        fun U => U (Γ.linkClass ⟨b, hp⟩) :=
      funext fun U => Γ.lift_apply_positive U ⟨b, hp⟩
    rw [e]
    exact ⟨continuous_apply _, fun U U' h => h _ hB⟩
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not hp
    have hB := linkClass_mem_plusLinks Γ n z c ⟨b.opposite, hr⟩ h₃ h₄ h₁ h₂
    have e : (fun U : Γ.QuotientField => Γ.liftValue U b) =
        fun U => (U (Γ.linkClass ⟨b.opposite, hr⟩))⁻¹ := by
      funext U
      have h := Γ.lift_apply_positive U ⟨b.opposite, hr⟩
      have h' := Γ.liftValue_opposite U b
      change Γ.liftValue U b.opposite = _ at h
      rw [← h, h', inv_inv]
    rw [e]
    exact ⟨(continuous_apply _).inv, fun U U' h => by simp only [h _ hB]⟩
private def pairHolonomy (b b' : Link 1) (U : Γ.QuotientField) : ComplexMatrix2.specialUnitary :=
  twoLinkHolonomy b b' (Γ.lift U)
private theorem pairHolonomy_continuous_dependsOn (n : AmbientSpace) (z : ℤ) (c : ℝ) (b b' : Link 1)
    (h₁ : c ≤ n ⬝ᵥ (b.initial : AmbientSpace)) (h₂ : n ⬝ᵥ (b.initial : AmbientSpace) ≤ c + (z : ℝ))
    (h₃ : c ≤ n ⬝ᵥ (b.terminal : AmbientSpace))
    (h₄ : n ⬝ᵥ (b.terminal : AmbientSpace) ≤ c + (z : ℝ))
    (h₅ : c ≤ n ⬝ᵥ (b'.initial : AmbientSpace))
    (h₆ : n ⬝ᵥ (b'.initial : AmbientSpace) ≤ c + (z : ℝ))
    (h₇ : c ≤ n ⬝ᵥ (b'.terminal : AmbientSpace))
    (h₈ : n ⬝ᵥ (b'.terminal : AmbientSpace) ≤ c + (z : ℝ)) :
    Continuous (pairHolonomy Γ b b') ∧
      PeriodSublattice.DependsOnlyOn (pairHolonomy Γ b b') (Γ.plusLinks n z c) := by
  obtain ⟨c₁, d₁⟩ := liftValue_continuous_dependsOn Γ n z c b h₁ h₂ h₃ h₄
  obtain ⟨c₂, d₂⟩ := liftValue_continuous_dependsOn Γ n z c b' h₅ h₆ h₇ h₈
  refine ⟨c₁.mul c₂, fun U U' h => ?_⟩
  have e₁ := d₁ U U' h
  have e₂ := d₂ U U' h
  change Γ.liftValue U b * Γ.liftValue U b' =
    Γ.liftValue U' b * Γ.liftValue U' b'
  simp only at e₁ e₂
  rw [e₁, e₂]
private theorem hasReflectionSeries_of_energy {β : ℝ} (hβ : 0 < β)
    (hC : YangMills.Construction.ReflectionPositivity.CrossingWeight.PositiveTypeStatement) (z : ℤ)
    (P : NormalLevelPair 1)
    (u : Γ.QuotientField → ComplexMatrix2.specialUnitary) (hu : Continuous u)
    (hd : PeriodSublattice.DependsOnlyOn u (Γ.plusLinks P.normal z P.level))
    (a : Γ.QuotientField → ℝ)
    (ha : ∀ U, a U = 1 - (1 / 2) * (ComplexMatrix2.fullTrace ((u U *
      (u (Γ.pullbackField P.reflectSymmetry U))⁻¹ : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2)).re) :
    Γ.HasReflectionSeries z P (fun U => ((Real.exp (-β * a U) : ℝ) : ℂ)) (Real.exp β) := by
  obtain ⟨hα, hsum, hcont, hbd, -, hnorm, hunif⟩ := hC β hβ.le
  let E := chosenExpansion β
  let x : Γ.QuotientField → ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary :=
    fun U => (u U, u (Γ.pullbackField P.reflectSymmetry U))
  have hterm : ∀ (j : E.index) (U : Γ.QuotientField),
      ((Real.exp (-β) * E.coeff j : ℝ) : ℂ) * E.fn j (u U) *
          Γ.conjReflect P (fun U => E.fn j (u U)) U =
        ((Real.exp (-β) : ℝ) : ℂ) * E.summand j (x U) := by
    intro j U
    simp only [PeriodSublattice.conjReflect, PeriodSublattice.compPullback,
      CharacterFamily.summand, x]
    push_cast
    ring
  have hweight : ∀ U, ((Real.exp (-β * a U) : ℝ) : ℂ) =
      ((Real.exp (-β) : ℝ) : ℂ) * weightAt β (x U) := by
    intro U
    simp only [weightAt, x]
    rw [← Complex.ofReal_mul, ← Real.exp_add, ha U]
    congr 2
    ring
  have hpos : 0 < Real.exp (-β) := Real.exp_pos _
  have hle : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  refine ⟨E.index, E.countable, fun j => Real.exp (-β) * E.coeff j,
    fun j U => E.fn j (u U), fun j => mul_nonneg hpos.le (hα j), ?_, fun j => ?_,
    fun j => ?_, fun U => ?_, ?_⟩
  · have h := hsum.mul_left (Real.exp (-β))
    have e : Real.exp (-β) * Real.exp (2 * β) = Real.exp β := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [e] at h
  · refine ⟨((hcont j).comp hu).measurable, ⟨1, fun U => hbd j _⟩, fun U U' h => ?_⟩
    change E.fn j (u U) = E.fn j (u U')
    rw [hd U U' h]
  · exact ciSup_le fun U => hbd j _
  · have h := (hnorm (x U)).mul_left (Real.exp (-β))
    refine h.congr fun j => ?_
    rw [hterm j U, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  · have hU := hasSumUniformlyOn_iff_tendstoUniformlyOn.1 hunif
    rw [tendstoUniformlyOn_univ] at hU
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.1 hU ε hε] with s hs U
    have h := hs (x U)
    rw [hweight U]
    simp only [hterm]
    rw [← Finset.mul_sum, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hpos.le, ← dist_eq_norm]
    calc Real.exp (-β) * dist (weightAt β (x U)) (∑ i ∈ s, E.summand i (x U))
        ≤ 1 * dist (weightAt β (x U)) (∑ i ∈ s, E.summand i (x U)) :=
          mul_le_mul_of_nonneg_right hle dist_nonneg
      _ < ε := by rwa [one_mul]
private theorem normSq_coordVec (μ : Fin 4) :
    normSq (coordVec μ) = 1 := by apply _root_.YangMills.Construction.TransferOperators.normSq_coordVec <;> assumption
end CrossingIntegralAtIntegerLevel
open CrossingIntegralAtIntegerLevel in
theorem crossingIntegralReflectionSeriesInteger_proof
    (hT : TwoLevelsOfOneReflection)
    (hC : YangMills.Construction.ReflectionPositivity.CrossingWeight.PositiveTypeStatement)
    (hM : ReflectionSeriesMul)
    (hF : PeriodQuotientFinite)
    (hB : SplitTorusPullbacks) :
    CrossingIntegralReflectionSeriesInteger := by
  intro β hβ Γ n hn z hz c hc hk P
  obtain ⟨hz', -, ha, -, -, -, -, -, -, hd, hlift, hext⟩ := hT Γ n hn z c hc hz
  obtain ⟨hempty, -, hq1, hq2⟩ := ha hk
  have hpull : Function.Involutive (Γ.pullbackField P.reflectSymmetry) :=
    ((hB β hβ Γ n hn z hz).1 c hc).1
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz.2.1
  have : Finite Γ.QuotientPlaquette := (hF 1 one_pos Γ).2.2
  have : Fintype Γ.QuotientPlaquette := Fintype.ofFinite _
  classical
  let s : Finset Γ.QuotientPlaquette := Finset.univ.filter fun q => Γ.IsSplitPlaquette n z c q
  let K : Γ.QuotientPlaquette → Γ.QuotientField → ℂ := fun q U =>
    ((Real.exp (-β * Γ.quotientFaceEnergy U q) : ℝ) : ℂ)
  have key : ∀ q ∈ s, Γ.HasReflectionSeries z P (K q) (Real.exp β) := by
    intro q hq
    have hcut : Γ.IsSplitPlaquette n z c q := (Finset.mem_filter.1 hq).2
    have hcase : ∃ μ lam : Fin 4, μ < lam ∧
        (n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam) := by
      rcases hn with ⟨μ, hμ⟩ | ⟨μ, lam, hlt, h | h⟩
      · exact absurd hcut (hq1 (by rw [hμ]; exact normSq_coordVec μ) q)
      · exact ⟨μ, lam, hlt, Or.inr h⟩
      · exact ⟨μ, lam, hlt, Or.inl h⟩
    obtain ⟨μ, lam, hlt, hnn⟩ := hcase
    obtain ⟨hiff, hlifts⟩ := hq2 μ lam hlt hnn
    obtain ⟨hplane, h1 | h2⟩ := (hiff q).1 hcut
    · obtain ⟨p, y, y', hl, hcb⟩ := hlifts P (Or.inl rfl) q hplane h1
      obtain ⟨zP, zM, b₁, b₂, b₃, b₄, -, hhP, hhM, t₁, e₁, t₂, e₂, -, -, -, -, hU⟩ :=
        (hd P (Or.inl rfl)).1 μ lam hlt hnn hk p y y' hcb
      obtain ⟨-, -, hy, hy', -, -⟩ := hcb
      have hy₀ : n ⬝ᵥ (y : AmbientSpace) = c := hy
      have hy₁ : n ⬝ᵥ (y' : AmbientSpace) = c := hy'
      have hP₀ : n ⬝ᵥ (zP : AmbientSpace) = c + 1 := hhP
      obtain ⟨hcu, hdu⟩ := pairHolonomy_continuous_dependsOn Γ n z c b₁ b₂
        (by rw [t₁, hy₀]) (by rw [t₁, hy₀]; linarith) (by rw [e₁, hP₀]; linarith)
        (by rw [e₁, hP₀]; linarith) (by rw [t₂, hP₀]; linarith) (by rw [t₂, hP₀]; linarith)
        (by rw [e₂, hy₁]) (by rw [e₂, hy₁]; linarith)
      refine hasReflectionSeries_of_energy Γ hβ hC z P (pairHolonomy Γ b₁ b₂) hcu hdu
        (fun U => Γ.quotientFaceEnergy U q) fun U => ?_
      rw [((hlift q p hl).1 U), (hU U).1, (hext U).2]
      rfl
    · obtain ⟨p, y, y', hl, hcb⟩ := hlifts _ (Or.inr rfl) q hplane h2
      obtain ⟨zP, zM, b₁, b₂, b₃, b₄, -, hhP, hhM, -, -, -, -, t₃, e₃, t₄, e₄, hU⟩ :=
        (hd _ (Or.inr rfl)).1 μ lam hlt hnn hk p y y' hcb
      obtain ⟨-, -, hy, hy', -, -⟩ := hcb
      have hy₀ : n ⬝ᵥ (y : AmbientSpace) = c + (z : ℝ) := hy
      have hy₁ : n ⬝ᵥ (y' : AmbientSpace) = c + (z : ℝ) := hy'
      have hM₀ : n ⬝ᵥ (zM : AmbientSpace) = c + (z : ℝ) - 1 := hhM
      obtain ⟨hcu, hdu⟩ := pairHolonomy_continuous_dependsOn Γ n z c b₃ b₄
        (by rw [t₃, hy₀]; linarith) (by rw [t₃, hy₀]) (by rw [e₃, hM₀]; linarith)
        (by rw [e₃, hM₀]; linarith) (by rw [t₄, hM₀]; linarith) (by rw [t₄, hM₀]; linarith)
        (by rw [e₄, hy₁]; linarith) (by rw [e₄, hy₁])
      have hv : ∀ U, twoLinkHolonomy b₁ b₂
          (Γ.lift (Γ.pullbackField P.reflectSymmetry U)) = pairHolonomy Γ b₃ b₄ U := by
        intro U
        have h := (hU U).2
        rw [(hext U).1, (hext U).2] at h
        exact h
      refine hasReflectionSeries_of_energy Γ hβ hC z P (pairHolonomy Γ b₃ b₄) hcu hdu
        (fun U => Γ.quotientFaceEnergy U q) fun U => ?_
      have hback : pairHolonomy Γ b₃ b₄ (Γ.pullbackField P.reflectSymmetry U) =
          twoLinkHolonomy b₁ b₂ (Γ.lift U) := by
        rw [← hv, hpull U]
      rw [((hlift q p hl).1 U), (hU U).1, (hext U).1, (hext U).2, hv U, hback,
        re_fullTrace_mul_inv_symm]
  have hprod := (hM Γ z P).2.2 Γ.QuotientPlaquette s K (fun _ => Real.exp β) key
  have hf : Γ.integrateOut (Γ.crossingLinks n z c)
      (fun U => (Γ.splitFaceWeight β n z c U : ℂ)) = ∏ q ∈ s, K q := by
    rw [integrateOut_empty Γ _ hempty]
    funext U
    rw [Finset.prod_apply]
    simp only [K]
    rw [← Complex.ofReal_prod, ← Real.exp_sum, PeriodSublattice.splitFaceWeight,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    simp only [finsum_eq_if]
    rw [Finset.sum_filter]
    simp only [mul_ite, mul_zero]
  have ha' : ∏ _q ∈ s, Real.exp β = Real.exp (β * (Γ.numSplitPlaquettes n z c : ℝ)) := by
    rw [Finset.prod_const, ← Real.exp_nat_mul, mul_comm]
    congr 3
    rw [PeriodSublattice.numSplitPlaquettes, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hf, ← ha']
  exact hprod
end YangMills.Construction.InfiniteLattice
