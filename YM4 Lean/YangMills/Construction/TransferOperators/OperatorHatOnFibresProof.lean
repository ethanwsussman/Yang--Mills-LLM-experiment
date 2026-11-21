import YangMills.Construction.TransferOperators.HatAndFunctionsOfTheOtherVariablesProof
import YangMills.Construction.TransferOperators.OperatorHatOnFibres
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics.HatFibrewise
variable {J : Type} [Finite J]
omit [Finite J] in
theorem restrictTo_glue {A : Type*} (B : Set J) (v : ↥B → A) (z : ↥Bᶜ → A) :
    restrictTo B (glue B v z) = v :=
  funext fun b => glue_of_mem B v z b
omit [Finite J] in
theorem restrictTo_compl_glue {A : Type*} (B : Set J) (v : ↥B → A) (z : ↥Bᶜ → A) :
    restrictTo Bᶜ (glue B v z) = z :=
  funext fun b => glue_of_notMem B v z b
theorem partIsotypicProjC_glue (B : Set J) (l : ↥B → HalfNatural)
    (H : C(J → ComplexMatrix2.specialUnitary, ℂ))
    (v : ↥B → ComplexMatrix2.specialUnitary) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary) :
    partIsotypicProjC B l H (glue B v z) =
      ∫ v', isotypicKernel l v v' * H (glue B v' z) ∂ComplexMatrix2.haarPi ↥B := by
  change ∫ v', isotypicKernel l (restrictTo B (glue B v z)) v' *
    H (glue B v' (restrictTo Bᶜ (glue B v z))) ∂ComplexMatrix2.haarPi ↥B = _
  rw [restrictTo_glue, restrictTo_compl_glue]
def univSubtypeEquiv (B : Set J) :
    (↥(Set.univ : Set ↥B) → ComplexMatrix2.specialUnitary) ≃ᵐ (↥B → ComplexMatrix2.specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.specialUnitary) (Equiv.Set.univ ↥B)
omit [Finite J] in
theorem univSubtypeEquiv_apply (B : Set J)
    (x : ↥(Set.univ : Set ↥B) → ComplexMatrix2.specialUnitary) (b : ↥B) :
    univSubtypeEquiv B x b = x ⟨b, Set.mem_univ b⟩ :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ComplexMatrix2.specialUnitary)
    (Equiv.Set.univ ↥B) x ⟨b, Set.mem_univ b⟩
theorem integral_univSubtypeEquiv (B : Set J) (g : (↥B → ComplexMatrix2.specialUnitary) → ℂ) :
    ∫ x, g (univSubtypeEquiv B x) ∂ComplexMatrix2.haarPi ↥(Set.univ : Set ↥B) =
      ∫ v, g v ∂ComplexMatrix2.haarPi ↥B := by
  have hmp : MeasurePreserving (univSubtypeEquiv B) (ComplexMatrix2.haarPi ↥(Set.univ : Set ↥B))
      (ComplexMatrix2.haarPi ↥B) := by
    refine ⟨(univSubtypeEquiv B).measurable, ?_⟩
    unfold ComplexMatrix2.haarPi
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ => ComplexMatrix2.haarProb)
      (Equiv.Set.univ ↥B)
  exact hmp.integral_comp' g
omit [Finite J] in
theorem glue_univ (B : Set J) (x : ↥(Set.univ : Set ↥B) → ComplexMatrix2.specialUnitary)
    (z : ↥(Set.univ : Set ↥B)ᶜ → ComplexMatrix2.specialUnitary) :
    glue (Set.univ : Set ↥B) x z = univSubtypeEquiv B x := by
  funext b
  rw [univSubtypeEquiv_apply]
  exact glue_of_mem (Set.univ : Set ↥B) x z ⟨b, Set.mem_univ b⟩
omit [Finite J] in
theorem isotypicKernel_univ (B : Set J) (l : ↥B → HalfNatural)
    (v : ↥B → ComplexMatrix2.specialUnitary)
    (x : ↥(Set.univ : Set ↥B) → ComplexMatrix2.specialUnitary) :
    isotypicKernel (restrictTo Set.univ l) (restrictTo Set.univ v) x =
      isotypicKernel l v (univSubtypeEquiv B x) := by
  unfold isotypicKernel
  rw [← finprod_comp_equiv (Equiv.Set.univ ↥B)
    (f := fun b => ((2 * (l b).toReal + 1 : ℝ) : ℂ) *
      spinCharacter (l b) (v b * (univSubtypeEquiv B x b)⁻¹))]
  refine finprod_congr fun a => ?_
  obtain ⟨b, hb⟩ := a
  change _ = ((2 * (l b).toReal + 1 : ℝ) : ℂ) *
    spinCharacter (l b) (v b * (univSubtypeEquiv B x b)⁻¹)
  rw [univSubtypeEquiv_apply]
  rfl
theorem partIsotypicProjC_univ (B : Set J) (l : ↥B → HalfNatural)
    (H : C(↥B → ComplexMatrix2.specialUnitary, ℂ)) (v : ↥B → ComplexMatrix2.specialUnitary) :
    partIsotypicProjC Set.univ (restrictTo Set.univ l) H v =
      ∫ v', isotypicKernel l v v' * H v' ∂ComplexMatrix2.haarPi ↥B := by
  rw [← integral_univSubtypeEquiv]
  change ∫ x, isotypicKernel (restrictTo Set.univ l) (restrictTo Set.univ v) x *
    H (glue Set.univ x (restrictTo (Set.univ : Set ↥B)ᶜ v))
      ∂ComplexMatrix2.haarPi ↥(Set.univ : Set ↥B) = _
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change isotypicKernel (restrictTo Set.univ l) (restrictTo Set.univ v) x *
    H (glue Set.univ x (restrictTo (Set.univ : Set ↥B)ᶜ v)) = _
  rw [glue_univ, isotypicKernel_univ]
theorem fibreAt_partIsotypicProjC (B : Set J) (l : ↥B → HalfNatural)
    (H : C(J → ComplexMatrix2.specialUnitary, ℂ)) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary) :
    fibreAt B (partIsotypicProjC B l H) z =
      partIsotypicProjC Set.univ (restrictTo Set.univ l) (fibreAt B H z) := by
  ext v
  rw [partIsotypicProjC_univ]
  exact partIsotypicProjC_glue B l H v z
omit [Finite J] in
theorem fibreAt_mulPullback (B : Set J) (f : (↥B → ComplexMatrix2.specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (hw : IsRealEntryPolynomial (onUnivSubtype B f))
    (H : C(J → ComplexMatrix2.specialUnitary, ℂ)) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary) :
    fibreAt B (mulPullback B f hf H) z =
      mulPullback Set.univ (onUnivSubtype B f) hw (fibreAt B H z) := by
  ext v
  change f (restrictTo B (glue B v z)) * H (glue B v z) = _
  rw [restrictTo_glue]
  rfl
theorem fibreAt_hatSummand (B : Set J) (f : (↥B → ComplexMatrix2.specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (hw : IsRealEntryPolynomial (onUnivSubtype B f))
    (F : C(J → ComplexMatrix2.specialUnitary, ℂ)) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary)
    (l l' : ↥B → HalfNatural) :
    fibreAt B (hatSummand B f hf F l l') z =
      hatSummand Set.univ (onUnivSubtype B f) hw (fibreAt B F z)
        (restrictTo Set.univ l) (restrictTo Set.univ l') := by
  unfold hatSummand
  rw [fibreAt_partIsotypicProjC, fibreAt_mulPullback, fibreAt_partIsotypicProjC]
omit [Finite J] in
theorem charCoeffProd_univ (β : ℝ) (B : Set J) (l : ↥B → HalfNatural) :
    TransferOperators.charCoeffProd β (restrictTo Set.univ l) =
      TransferOperators.charCoeffProd β l :=
  finprod_comp_equiv (Equiv.Set.univ ↥B) (f := fun b => weightCharCoeff β (l b))
theorem charCoeffRatio_univ (β : ℝ) (B : Set J) (l l' : ↥B → HalfNatural) :
    charCoeffRatio β (restrictTo Set.univ l) (restrictTo Set.univ l') =
      charCoeffRatio β l l' := by
  unfold charCoeffRatio
  rw [charCoeffProd_univ, charCoeffProd_univ]
def weightsUnivEquiv (B : Set J) : (↥B → HalfNatural) ≃ (↥(Set.univ : Set ↥B) → HalfNatural) where
  toFun := restrictTo Set.univ
  invFun m := fun b => m ⟨b, Set.mem_univ b⟩
  left_inv _ := rfl
  right_inv _ := rfl
def fibreAddHom (B : Set J) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary) :
    C(J → ComplexMatrix2.specialUnitary, ℂ) →+ C(↥B → ComplexMatrix2.specialUnitary, ℂ) where
  toFun H := fibreAt B H z
  map_zero' := rfl
  map_add' _ _ := rfl
omit [Finite J] in
theorem continuous_fibreAddHom (B : Set J) (z : ↥Bᶜ → ComplexMatrix2.specialUnitary) :
    Continuous (fibreAddHom B z) :=
  ContinuousMap.continuous_precomp _
theorem summable_of_mem_hatSummableSet (β : ℝ) (B : Set J)
    (f : (↥B → ComplexMatrix2.specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → ComplexMatrix2.specialUnitary, ℂ)) (hF : F ∈ hatSummableSet β B f hf) :
    Summable fun p : (↥B → HalfNatural) × (↥B → HalfNatural) =>
      charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2 := by apply _root_.YangMills.Construction.SpinHarmonics.HatComplementMul.summable_of_mem_hatSummableSet <;> assumption
omit [Finite J] in
theorem isRealEntryPolynomial_onUnivSubtype (B : Set J)
    (f : (↥B → ComplexMatrix2.specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : IsRealEntryPolynomial (onUnivSubtype B f) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hf
  let g : ↥B → ↥(Set.univ : Set ↥B) := fun b => ⟨b, Set.mem_univ b⟩
  refine ⟨⟨MvPolynomial.rename
    (Sum.map (fun t => (g t.1, t.2)) (fun t => (g t.1, t.2))) p, fun v => ?_⟩, fun v => hr _⟩
  rw [MvPolynomial.eval_rename]
  refine (hp _).trans (congrArg (fun a => MvPolynomial.eval a p) ?_)
  funext x
  rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
theorem hatFibrewise (hDegrees : PolynomialDegrees.Statement)
    (hSeries : HatSeriesConvergesStatement) : HatFibrewiseStatement := by
  intro J _ _ β B f hf hβ hB _
  refine ⟨isRealEntryPolynomial_onUnivSubtype B f hf, fun F z v hF => ?_⟩
  have hne : Nonempty ↥B := hB.to_subtype
  obtain ⟨D, hD⟩ := (hDegrees ↥B f hf.1).2
  have hdom : F ∈ hatSummableSet β B f hf := (hSeries J β B f hf D hβ hB hD F hF).2.2.2.2.2.2.1
  have hsum := summable_of_mem_hatSummableSet β B f hf F hdom
  have hmap := hsum.map_tsum (fibreAddHom B z) (continuous_fibreAddHom B z)
  have hvalue : fibreAt B (hatSum β B f hf F) z =
      hatSum β Set.univ (onUnivSubtype B f)
        (isRealEntryPolynomial_onUnivSubtype B f hf) (fibreAt B F z) := by
    refine hmap.trans ?_
    unfold hatSum
    rw [← ((weightsUnivEquiv B).prodCongr (weightsUnivEquiv B)).tsum_eq]
    refine tsum_congr fun p => ?_
    change fibreAt B (charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2) z =
      charCoeffRatio β (restrictTo Set.univ p.1) (restrictTo Set.univ p.2) •
        hatSummand Set.univ (onUnivSubtype B f)
          (isRealEntryPolynomial_onUnivSubtype B f hf) (fibreAt B F z)
          (restrictTo Set.univ p.1) (restrictTo Set.univ p.2)
    rw [charCoeffRatio_univ, ← fibreAt_hatSummand B f hf]
    rfl
  exact DFunLike.congr_fun hvalue v
end YangMills.Construction.SpinHarmonics.HatFibrewise
end
