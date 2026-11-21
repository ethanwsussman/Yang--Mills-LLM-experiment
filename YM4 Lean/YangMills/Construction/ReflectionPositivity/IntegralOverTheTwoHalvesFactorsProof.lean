import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.Matrices.HaarRelabelInversion
import YangMills.Construction.ReflectionPositivity.IntegralOverTheTwoHalvesFactors
import YangMills.Construction.ReflectionPositivity.IntegralOverVariablesOfATorus
import YangMills.Construction.ReflectionPositivity.OneReflectionTwoMirrorsAndWhatTheyCut
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.HalvesFactorizationProof
open YangMills.Construction.NormalFamilies
theorem integral_mul_of_compl_dependence
    (hGlue : GlueMeasurePreserving)
    {J : Type} [Finite J] (B : Set J) {f g : (J → specialUnitary) → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (df : ∀ u u' : J → specialUnitary, (∀ b ∈ B, u b = u' b) → f u = f u')
    (dg : ∀ u u' : J → specialUnitary, (∀ b ∈ Bᶜ, u b = u' b) → g u = g u') :
    ∫ u, g u * f u ∂haarPi J =
      (∫ u, g u ∂haarPi J) * ∫ u, f u ∂haarPi J := by
  have hm := hGlue J B
  let f₁ : (↥B → specialUnitary) → ℂ := fun v => f (glue B v fun _ => 1)
  let g₁ : (↥Bᶜ → specialUnitary) → ℂ := fun y => g (glue B (fun _ => 1) y)
  have hf₁ : ∀ p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary), f (glue B p.1 p.2) = f₁ p.1 :=
    fun p => df _ _ fun b hb =>
      (glue_of_mem B _ _ ⟨b, hb⟩).trans (glue_of_mem B _ _ ⟨b, hb⟩).symm
  have hg₁ : ∀ p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary), g (glue B p.1 p.2) = g₁ p.2 :=
    fun p => dg _ _ fun b hb =>
      (glue_of_notMem B _ _ ⟨b, hb⟩).trans (glue_of_notMem B _ _ ⟨b, hb⟩).symm
  have push : ∀ h : (J → specialUnitary) → ℂ, Measurable h →
      ∫ u, h u ∂haarPi J =
        ∫ p, h (glue B p.1 p.2) ∂(haarPi ↥B).prod (haarPi ↥Bᶜ) := by
    intro h hh
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hh.aestronglyMeasurable]
  have ef : ∫ u, f u ∂haarPi J = ∫ v, f₁ v ∂haarPi ↥B := by
    rw [push f hf]
    simp_rw [hf₁]
    have := integral_prod_mul (μ := haarPi ↥B) (ν := haarPi ↥Bᶜ) f₁
      (fun _ => (1 : ℂ))
    simpa using this
  have eg : ∫ u, g u ∂haarPi J = ∫ y, g₁ y ∂haarPi ↥Bᶜ := by
    rw [push g hg]
    simp_rw [hg₁]
    have := integral_prod_mul (μ := haarPi ↥B) (ν := haarPi ↥Bᶜ)
      (fun _ => (1 : ℂ)) g₁
    simpa using this
  rw [push (fun u => g u * f u) (hg.mul hf), ef, eg]
  simp_rw [hf₁, hg₁]
  rw [mul_comm, ← integral_prod_mul f₁ g₁]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
theorem measurable_glue_left {J : Type} [Countable J] (M : Set J) (Z : ↥Mᶜ → specialUnitary) :
    Measurable fun V : ↥M → specialUnitary => glue M V Z := by
  refine measurable_pi_iff.2 fun b => ?_
  by_cases h : b ∈ M
  · have : (fun V : ↥M → specialUnitary => glue M V Z b) = fun V => V ⟨b, h⟩ := by
      funext V
      exact glue_of_mem M V Z ⟨b, h⟩
    rw [this]
    exact measurable_pi_apply _
  · have : (fun V : ↥M → specialUnitary => glue M V Z b) = fun _ => Z ⟨b, h⟩ := by
      funext V
      exact glue_of_notMem M V Z ⟨b, h⟩
    rw [this]
    exact measurable_const
section Torus
variable (Γ : PeriodSublattice 1)
theorem exists_orientedClass_eq (c : Γ.OrientedLink) :
    ∃ b, Γ.orientedClass b = c :=
  ⟨_, Γ.orientedClass_orientedRep c⟩
theorem oppositeOriented_oppositeOriented (c : Γ.OrientedLink) :
    Γ.oppositeOriented (Γ.oppositeOriented c) = c := by
  obtain ⟨b, rfl⟩ := exists_orientedClass_eq Γ c
  rw [Γ.oppositeOriented_orientedClass, Γ.oppositeOriented_orientedClass]
  rfl
variable {Γ}
theorem descendOrientedLink_oppositeOriented {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r)
    (c : Γ.OrientedLink) :
    Γ.descendOrientedLink r (Γ.oppositeOriented c) =
      Γ.oppositeOriented (Γ.descendOrientedLink r c) := by
  obtain ⟨b, rfl⟩ := exists_orientedClass_eq Γ c
  rw [Γ.oppositeOriented_orientedClass, hI.descendOrientedLink_orientedClass,
    hI.descendOrientedLink_orientedClass, Γ.oppositeOriented_orientedClass]
  rfl
variable (Γ)
theorem orientedOfLink_ne_oppositeOriented (b b' : Γ.QuotientLink) :
    Γ.orientedOfLink b ≠ Γ.oppositeOriented (Γ.orientedOfLink b') := by
  intro e
  have hp : Γ.OrientedIsPositive (Γ.orientedOfLink b) :=
    (Γ.orientedIsPositive_orientedClass_iff _).2 (Γ.linkRep b).2
  rw [e, PeriodSublattice.orientedOfLink, Γ.oppositeOriented_orientedClass,
    Γ.orientedIsPositive_orientedClass_iff] at hp
  exact PeriodSublattice.not_isPositivelyOriented_opposite Γ (Γ.linkRep b').2 hp
theorem orientedValue_orientedOfLink (U : Γ.QuotientField) (d : Γ.QuotientLink) :
    Γ.orientedValue U (Γ.orientedOfLink d) = U d := by
  have h := Γ.orientedValue_positive U (Γ.linkRep d)
  rwa [Γ.linkClass_linkRep] at h
theorem orientedValue_oppositeOriented_orientedOfLink (U : Γ.QuotientField) (d : Γ.QuotientLink) :
    Γ.orientedValue U (Γ.oppositeOriented (Γ.orientedOfLink d)) = (U d)⁻¹ := by
  rw [PeriodSublattice.orientedOfLink, Γ.oppositeOriented_orientedClass,
    Γ.orientedValue_opposite, Γ.linkClass_linkRep]
theorem orientedOfLink_linkImage (r : LatticeSymmetry 1) (b : Γ.QuotientLink) :
    (Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b)) ∧
        Γ.orientedOfLink (Γ.linkImage r b) =
          Γ.descendOrientedLink r (Γ.orientedOfLink b)) ∨
      (¬ Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b)) ∧
        Γ.orientedOfLink (Γ.linkImage r b) =
          Γ.oppositeOriented (Γ.descendOrientedLink r (Γ.orientedOfLink b))) := by
  by_cases h : Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b))
  · refine Or.inl ⟨h, ?_⟩
    rw [PeriodSublattice.linkImage, dif_pos h, Γ.orientedOfLink_linkClass,
      Γ.orientedClass_orientedRep]
  · refine Or.inr ⟨h, ?_⟩
    rw [PeriodSublattice.linkImage, dif_neg h, Γ.orientedOfLink_linkClass]
    rfl
variable {Γ}
theorem linkImage_injective {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r) :
    Function.Injective (Γ.linkImage r) := by
  intro b b' e
  apply Γ.orientedOfLink_injective
  apply hI.descendOrientedLink_bijective.1
  rcases orientedOfLink_linkImage Γ r b with ⟨-, q⟩ | ⟨-, q⟩ <;>
    rcases orientedOfLink_linkImage Γ r b' with ⟨-, q'⟩ | ⟨-, q'⟩ <;>
    rw [e] at q
  · exact q.symm.trans q'
  · exfalso
    have h : Γ.descendOrientedLink r (Γ.orientedOfLink b) =
        Γ.descendOrientedLink r (Γ.oppositeOriented (Γ.orientedOfLink b')) := by
      rw [descendOrientedLink_oppositeOriented hI, ← q', q]
    exact orientedOfLink_ne_oppositeOriented Γ b b' (hI.descendOrientedLink_bijective.1 h)
  · exfalso
    have h : Γ.descendOrientedLink r (Γ.orientedOfLink b') =
        Γ.descendOrientedLink r (Γ.oppositeOriented (Γ.orientedOfLink b)) := by
      rw [descendOrientedLink_oppositeOriented hI, ← q, q']
    exact orientedOfLink_ne_oppositeOriented Γ b' b (hI.descendOrientedLink_bijective.1 h)
  · have h := congrArg Γ.oppositeOriented (q.symm.trans q')
    rwa [oppositeOriented_oppositeOriented Γ, oppositeOriented_oppositeOriented Γ] at h
variable (Γ)
def linkSign (r : LatticeSymmetry 1) (b : Γ.QuotientLink) : ℤ :=
  open Classical in
  if Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b)) then 1 else -1
theorem linkSign_eq_one_or_neg_one (r : LatticeSymmetry 1) (b : Γ.QuotientLink) :
    linkSign Γ r b = 1 ∨ linkSign Γ r b = -1 := by
  unfold linkSign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
variable {Γ}
theorem pullbackField_eq_orientedValue {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r)
    (U : Γ.QuotientField) (b : Γ.QuotientLink) :
    Γ.pullbackField r U b =
      Γ.orientedValue U (Γ.descendOrientedLink r (Γ.orientedOfLink b)) := by
  rw [PeriodSublattice.orientedOfLink, hI.descendOrientedLink_orientedClass]
  rfl
theorem pullbackField_apply {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r)
    (U : Γ.QuotientField) (b : Γ.QuotientLink) :
    Γ.pullbackField r U b = U (Γ.linkImage r b) ^ linkSign Γ r b := by
  rw [pullbackField_eq_orientedValue hI]
  rcases orientedOfLink_linkImage Γ r b with ⟨p, q⟩ | ⟨p, q⟩
  · rw [linkSign, if_pos p, ← q, orientedValue_orientedOfLink Γ, zpow_one]
  · have q' := congrArg Γ.oppositeOriented q
    rw [oppositeOriented_oppositeOriented Γ] at q'
    rw [linkSign, if_neg p, ← q', orientedValue_oppositeOriented_orientedOfLink Γ, zpow_neg_one]
theorem integral_mul_conj_factor (hGlue : GlueMeasurePreserving)
    (hRel : RelabelInvertPreservesHaar)
    (hOut : IntegrateOutProperties) [Finite Γ.QuotientLink]
    {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r) {B A L : Set Γ.QuotientLink}
    (hAL : ∀ b, b ∈ A → b ∈ L → b ∈ B)
    (hfix : ∀ b ∈ B, ∀ U, Γ.pullbackField r U b = U b)
    (himg : Γ.linkImage r '' B = B)
    {F F' G w : Γ.QuotientField → ℂ}
    (hF : F ∈ Γ.boundedAlgebra A) (hF'm : Measurable F') (hF'b : ∃ C : ℝ, ∀ U, ‖F' U‖ ≤ C)
    (hG : G ∈ Γ.boundedAlgebra L)
    (hGF' : ∀ U, G U = conj (F' (Γ.pullbackField r U)))
    (hw : w ∈ Γ.boundedAlgebra B) :
    ∫ U, w U * G U * F U ∂Γ.quotientHaar =
      ∫ U, w U * conj (Γ.integrateOut Bᶜ F' U) * Γ.integrateOut Bᶜ F U
        ∂Γ.quotientHaar := by
  obtain ⟨Fm, ⟨CF, hCF⟩, Fd⟩ := hF
  obtain ⟨Gm, ⟨CG, hCG⟩, Gd⟩ := hG
  obtain ⟨wm, ⟨Cw, hCw⟩, wd⟩ := hw
  obtain ⟨CF', hCF'⟩ := hF'b
  have hinj := linkImage_injective hI
  have hbij : Function.Bijective (Γ.linkImage r) := Finite.injective_iff_bijective.1 hinj
  have hmaps : ∀ b, b ∈ Bᶜ → Γ.linkImage r b ∈ Bᶜ := by
    intro b hb h
    have h' : Γ.linkImage r b ∈ Γ.linkImage r '' B := by rwa [himg]
    obtain ⟨b₀, hb₀, e⟩ := h'
    exact hb (hinj e ▸ hb₀)
  have hback : ∀ b, Γ.linkImage r b ∈ Bᶜ → b ∈ Bᶜ := by
    intro b hb h
    apply hb
    rw [← himg]
    exact ⟨b, h, rfl⟩
  let σ : ↥Bᶜ → ↥Bᶜ := fun b => ⟨Γ.linkImage r b, hmaps b b.2⟩
  let ε : ↥Bᶜ → ℤ := fun b => linkSign Γ r b
  have hσ : Function.Bijective σ := by
    refine ⟨fun b b' e => Subtype.ext (hinj (congrArg Subtype.val e)), fun y => ?_⟩
    obtain ⟨x, e⟩ := hbij.2 y.1
    exact ⟨⟨x, hback x (e ▸ y.2)⟩, Subtype.ext e⟩
  have hjoin : ∀ (V : ↥Bᶜ → specialUnitary) (Z : ↥Bᶜᶜ → specialUnitary),
      Γ.pullbackField r (glue Bᶜ V Z) =
        glue Bᶜ (relabelInvert σ ε V) Z := by
    intro V Z
    funext b
    by_cases hb : b ∈ Bᶜ
    · rw [pullbackField_apply hI]
      have e₁ := glue_of_mem Bᶜ V Z ⟨Γ.linkImage r b, hmaps b hb⟩
      have e₂ := glue_of_mem Bᶜ (relabelInvert σ ε V) Z ⟨b, hb⟩
      change glue Bᶜ V Z (Γ.linkImage r b) = _ at e₁
      change glue Bᶜ _ Z b = _ at e₂
      rw [e₁, e₂]
      rfl
    · rw [hfix b (not_not.1 hb)]
      exact (glue_of_notMem Bᶜ V Z ⟨b, hb⟩).trans
        (glue_of_notMem Bᶜ _ Z ⟨b, hb⟩).symm
  have hAvG : ∀ Z : ↥Bᶜᶜ → specialUnitary,
      ∫ V, G (glue Bᶜ V Z) ∂haarPi ↥Bᶜ =
        conj (∫ V, F' (glue Bᶜ V Z) ∂haarPi ↥Bᶜ) := by
    intro Z
    have hrel := (hRel ↥Bᶜ ↥Bᶜ σ ε hσ fun b => linkSign_eq_one_or_neg_one Γ r b).2
      (fun V => F' (glue Bᶜ V Z)) (hF'm.comp (measurable_glue_left Bᶜ Z))
      ⟨CF', fun V => hCF' _⟩
    rw [← hrel, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    change G (glue Bᶜ V Z) = conj (F' (glue Bᶜ _ Z))
    rw [hGF', hjoin]
  have hkey : ∀ U, Γ.integrateOut Bᶜ (fun U => G U * F U) U =
      conj (Γ.integrateOut Bᶜ F' U) * Γ.integrateOut Bᶜ F U := by
    intro U
    let Z : ↥Bᶜᶜ → specialUnitary := SpinHarmonics.restrictTo Bᶜᶜ U
    have hjp : ∀ (V V' : ↥Bᶜ → specialUnitary) (T : Set Γ.QuotientLink),
        (∀ b : ↥Bᶜ, b.1 ∈ T → V b = V' b) →
        ∀ b ∈ T, glue Bᶜ V Z b = glue Bᶜ V' Z b := by
      intro V V' T h b hb
      by_cases hbc : b ∈ Bᶜ
      · exact (glue_of_mem Bᶜ V Z ⟨b, hbc⟩).trans
          ((h ⟨b, hbc⟩ hb).trans (glue_of_mem Bᶜ V' Z ⟨b, hbc⟩).symm)
      · exact (glue_of_notMem Bᶜ V Z ⟨b, hbc⟩).trans
          (glue_of_notMem Bᶜ V' Z ⟨b, hbc⟩).symm
    have hind := integral_mul_of_compl_dependence hGlue {b : ↥Bᶜ | b.1 ∈ A}
      (f := fun V => F (glue Bᶜ V Z)) (g := fun V => G (glue Bᶜ V Z))
      (Fm.comp (measurable_glue_left Bᶜ Z)) (Gm.comp (measurable_glue_left Bᶜ Z))
      (fun V V' h => Fd _ _ (hjp V V' A h))
      (fun V V' h => Gd _ _ (hjp V V' L fun b hb => h b fun hA => b.2 (hAL _ hA hb)))
    change ∫ V, G (glue Bᶜ V Z) * F (glue Bᶜ V Z) ∂haarPi ↥Bᶜ =
      conj (∫ V, F' (glue Bᶜ V Z) ∂haarPi ↥Bᶜ) *
        ∫ V, F (glue Bᶜ V Z) ∂haarPi ↥Bᶜ
    rw [hind, hAvG]
  have hstep := (hOut Γ Bᶜ).2.2 (fun U => G U * F U) w (max (CG * CF) Cw) (Gm.mul Fm) wm
    (fun U => le_max_of_le_left (by
      rw [norm_mul]
      exact mul_le_mul (hCG U) (hCF U) (norm_nonneg _) ((norm_nonneg _).trans (hCG U))))
    (fun U => le_max_of_le_right (hCw U))
    (fun U U' h => wd U U' fun b hb => h b (not_not.2 hb))
  calc ∫ U, w U * G U * F U ∂Γ.quotientHaar = ∫ U, w U * (G U * F U) ∂Γ.quotientHaar := by
        simp_rw [mul_assoc]
    _ = ∫ U, w U * Γ.integrateOut Bᶜ (fun U => G U * F U) U ∂Γ.quotientHaar := hstep
    _ = _ := by simp_rw [hkey, mul_assoc]
end Torus
theorem level_int_or_half {n : AmbientSpace} (hn : n ∈ normalSet) {c : ℝ}
    (hc : IsAllowedLevel 1 n c) :
    (∃ k : ℤ, c = (k : ℝ)) ∨ ∃ k : ℤ, c = (k : ℝ) + 1 / 2 := by
  obtain ⟨Fam, hFam⟩ := exists_reflectionClass hn
  cases Fam with
  | axial μ =>
    obtain ⟨k, hk⟩ := ((isAllowedLevel_one_iff n c).1 hc).1 (by
      rw [normSq_eq_dotProduct, ← hFam, ReflectionClass.realNormal_dot_axial])
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exact Or.inl ⟨m, by rw [hk]; push_cast; ring⟩
    · exact Or.inr ⟨m, by rw [hk]; push_cast; ring⟩
  | diagonal μ lam hlt s =>
    obtain ⟨k, hk⟩ := ((isAllowedLevel_one_iff n c).1 hc).2 (by
      rw [normSq_eq_dotProduct, ← hFam, ReflectionClass.realNormal_dot_diagonal])
    exact Or.inl ⟨k, hk⟩
theorem factorization_at_level (hGlue : GlueMeasurePreserving)
    (hRel : RelabelInvertPreservesHaar)
    (hFin : PeriodicQuotient.FinitenessClaim)
    (hDesc : SplitTorusDescent)
    (hTwo : TwoLevelsOfOneReflection)
    (hOut : IntegrateOutProperties)
    (Γ : PeriodSublattice 1) (n : AmbientSpace) (hn : n ∈ normalSet) (z : ℤ)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (c : ℝ) (hc : IsAllowedLevel 1 n c)
    {F F' w : Γ.QuotientField → ℂ} (hF : F ∈ Γ.plusAlgebra n z c)
    (hF' : F' ∈ Γ.plusAlgebra n z c)
    (hw : w ∈ Γ.boundedAlgebra (Γ.sharedLinks n z c)) :
    ∫ U, w U * Γ.conjReflect ⟨n, hn, c, hc⟩ F' U * F U ∂Γ.quotientHaar =
      ∫ U, w U * conj (Γ.integrateOut (Γ.sharedLinks n z c)ᶜ F' U) *
        Γ.integrateOut (Γ.sharedLinks n z c)ᶜ F U ∂Γ.quotientHaar := by
  have : Finite Γ.QuotientLink := (hFin.1 Γ).finite_quotientLink
  obtain ⟨_, -, ha, hb, -, -, himg, hΘ, -, -⟩ := hTwo Γ n hn z c hc hs
  obtain ⟨-, -, -, -, -, -, -, -, -, hI, -⟩ := hDesc Γ n hn z c hc 0 hs
  have hL : Γ.conjReflect ⟨n, hn, c, hc⟩ F' ∈ Γ.boundedAlgebra (Γ.minusLinks n z c) :=
    hΘ.subset ⟨F', hF', rfl⟩
  have hfix : ∀ b ∈ Γ.sharedLinks n z c, ∀ U,
      Γ.pullbackField (NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩) U b = U b := by
    intro b hbB U
    rcases level_int_or_half hn hc with hk | hk
    · rw [pullbackField_eq_orientedValue hI, (ha hk).2.1 b hbB, orientedValue_orientedOfLink Γ]
    · obtain ⟨μ, -, hemp, -⟩ := hb hk
      rw [hemp] at hbB
      exact hbB.elim
  exact integral_mul_conj_factor (B := Γ.sharedLinks n z c) (A := Γ.plusLinks n z c)
    (L := Γ.minusLinks n z c) hGlue hRel hOut hI (fun b h h' => ⟨h, h'⟩) hfix himg hF hF'.1
    hF'.2.1 hL (fun _ => rfl) hw
theorem halvesIntegralFactorization (hGlue : GlueMeasurePreserving)
    (hRel : RelabelInvertPreservesHaar)
    (hFin : PeriodicQuotient.FinitenessClaim)
    (hDesc : SplitTorusDescent)
    (hTwo : TwoLevelsOfOneReflection)
    (hOut : IntegrateOutProperties) :
    HalvesIntegralFactorization :=
  fun Γ n hn z hs c hc _ hF _ hF' _ hw =>
    factorization_at_level hGlue hRel hFin hDesc hTwo hOut Γ n hn z hs c hc hF hF' hw
end YangMills.Construction.InfiniteLattice.HalvesFactorizationProof
