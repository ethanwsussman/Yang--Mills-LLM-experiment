import YangMills.Construction.TransferOperators.OperatorHatAlongInjectionsAndPermutations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics.HatNaturality
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators
theorem integral_comp_equiv {A C : Type} [Countable A] [Countable C] (σ : A ≃ C)
    (g : (A → specialUnitary) → ℂ) :
    ∫ v, g (fun a => v (σ a)) ∂haarPi C = ∫ w, g w ∂haarPi A := by
  have hmap := Measure.infinitePi_map_piCongrLeft (X := fun _ : A => specialUnitary)
    (μ := fun _ : A => haarProb) σ.symm
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : A => specialUnitary) σ.symm)
      (haarPi C) (haarPi A) := ⟨MeasurableEquiv.measurable _, hmap⟩
  have hfun : ∀ v : C → specialUnitary,
      (MeasurableEquiv.piCongrLeft (fun _ : A => specialUnitary) σ.symm v) =
      fun a => v (σ a) := by
    intro v
    funext a
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h := hmp.integral_comp' g
  simpa only [hfun] using h
theorem charCoeffProd_comp_symm (β : ℝ) {A C : Type} [Finite A] [Finite C] (σ : A ≃ C)
    (l : A → HalfNatural) : charCoeffProd β (l ∘ σ.symm) = charCoeffProd β l :=
  finprod_comp_equiv σ.symm (f := fun a => weightCharCoeff β (l a))
theorem charCoeffRatio_comp_symm (β : ℝ) {A C : Type} [Finite A] [Finite C] (σ : A ≃ C)
    (l l' : A → HalfNatural) :
    charCoeffRatio β (l ∘ σ.symm) (l' ∘ σ.symm) = charCoeffRatio β l l' := by
  simp only [charCoeffRatio, charCoeffProd_comp_symm]
theorem isotypicKernel_comp_symm {A C : Type} (σ : A ≃ C) (l : A → HalfNatural)
    (u u' : C → specialUnitary) :
    isotypicKernel (l ∘ σ.symm) u u' =
      isotypicKernel l (fun a => u (σ a)) (fun a => u' (σ a)) := by
  simp only [isotypicKernel]
  rw [← finprod_comp_equiv σ]
  simp
section Precomposition
variable {J J' : Type} (e : J → J')
theorem precompAlong_tsum {I : Type} (g : J' → J) (hg : Function.LeftInverse g e)
    (T : I → C(J → specialUnitary, ℂ)) :
    ∑' i, precompAlong e (T i) = precompAlong e (∑' i, T i) := by
  let A : C(J → specialUnitary, ℂ) →+ C(J' → specialUnitary, ℂ) :=
    { toFun := precompAlong e, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let A' : C(J' → specialUnitary, ℂ) →+ C(J → specialUnitary, ℂ) :=
    { toFun := precompAlong g, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hA : Continuous A := ContinuousMap.continuous_precomp _
  have hA' : Continuous A' := ContinuousMap.continuous_precomp _
  have hinv : Function.LeftInverse A' A := by
    intro F
    ext u
    show F (fun b => u (g (e b))) = F u
    simp only [hg _]
  by_cases hs : Summable T
  · exact (hs.map_tsum A hA).symm
  · have hs' : ¬ Summable fun i => precompAlong e (T i) := fun h =>
      hs ((Summable.map_iff_of_leftInverse A A' hA hA' hinv).1 h)
    rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable hs']
    rfl
variable (B : Set J)
theorem mulPullback_precompAlong (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (hf' : IsRealEntryPolynomial (transportAlong e B f)) (H : C(J → specialUnitary, ℂ)) :
    mulPullback (e '' B) (transportAlong e B f) hf' (precompAlong e H) =
      precompAlong e (mulPullback B f hf H) := by
  ext u
  rfl
variable (he : Function.Injective e)
def imageEquiv : ↥B ≃ ↥(e '' B) := Equiv.Set.image e B he
include he
theorem isRealEntryPolynomial_transportAlong (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) :
    IsRealEntryPolynomial (transportAlong e B f) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hf
  let r : EntryVar ↥B → EntryVar ↥(e '' B) :=
    Sum.map (Prod.map (imageEquiv e B he) id) (Prod.map (imageEquiv e B he) id)
  refine ⟨⟨MvPolynomial.rename r p, fun v => ?_⟩, fun v => hr _⟩
  have hv : entryEval (fun b : ↥B => v ⟨e b, Set.mem_image_of_mem e b.2⟩) = entryEval v ∘ r := by
    funext x
    rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
  rw [MvPolynomial.eval_rename, ← hv]
  exact hp _
variable [Finite J] [Finite J']
theorem partIsotypicProjC_precompAlong (l : ↥B → HalfNatural) (F : C(J → specialUnitary, ℂ)) :
    partIsotypicProjC (e '' B) (l ∘ (imageEquiv e B he).symm) (precompAlong e F) =
      precompAlong e (partIsotypicProjC B l F) := by
  ext u
  show ∫ v', isotypicKernel (l ∘ (imageEquiv e B he).symm) (restrictTo (e '' B) u) v' *
      precompAlong e F (glue (e '' B) v' (restrictTo (e '' B)ᶜ u)) ∂haarPi ↥(e '' B) =
    ∫ w, isotypicKernel l (restrictTo B fun b => u (e b)) w *
      F (glue B w (restrictTo Bᶜ fun b => u (e b))) ∂haarPi ↥B
  refine Eq.trans ?_ (integral_comp_equiv (imageEquiv e B he)
    (fun w => isotypicKernel l (restrictTo B fun b => u (e b)) w *
      F (glue B w (restrictTo Bᶜ fun b => u (e b)))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show _ * _ = _ * _
  congr 1
  · exact isotypicKernel_comp_symm (imageEquiv e B he) l _ _
  · show F _ = F _
    congr 1
    funext j
    by_cases h : j ∈ B
    · have hj : e j ∈ e '' B := ⟨j, h, rfl⟩
      exact (glue_of_mem (e '' B) v _ ⟨e j, hj⟩).trans
        (glue_of_mem B (fun a => v (imageEquiv e B he a))
          (restrictTo Bᶜ fun b => u (e b)) ⟨j, h⟩).symm
    · have hj : e j ∉ e '' B := fun ⟨x, hx, hxe⟩ => h (he hxe ▸ hx)
      exact (glue_of_notMem (e '' B) v _ ⟨e j, hj⟩).trans
        (glue_of_notMem B (fun a => v (imageEquiv e B he a))
          (restrictTo Bᶜ fun b => u (e b)) ⟨j, h⟩).symm
theorem hatSummand_precompAlong (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (hf' : IsRealEntryPolynomial (transportAlong e B f)) (F : C(J → specialUnitary, ℂ))
    (l l' : ↥B → HalfNatural) :
    hatSummand (e '' B) (transportAlong e B f) hf' (precompAlong e F)
        (l ∘ (imageEquiv e B he).symm) (l' ∘ (imageEquiv e B he).symm) =
      precompAlong e (hatSummand B f hf F l l') := by
  simp only [hatSummand]
  rw [partIsotypicProjC_precompAlong e B he, mulPullback_precompAlong e B f hf hf',
    partIsotypicProjC_precompAlong e B he]
theorem hatSum_precompAlong [Nonempty J] (β : ℝ) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f)
    (hf' : IsRealEntryPolynomial (transportAlong e B f)) (F : C(J → specialUnitary, ℂ)) :
    hatSum β (e '' B) (transportAlong e B f) hf' (precompAlong e F) =
      precompAlong e (hatSum β B f hf F) := by
  let σ := imageEquiv e B he
  let E : ((↥B → HalfNatural) × (↥B → HalfNatural)) ≃
      ((↥(e '' B) → HalfNatural) × (↥(e '' B) → HalfNatural)) :=
    (σ.arrowCongr (Equiv.refl _)).prodCongr (σ.arrowCongr (Equiv.refl _))
  have hterm : ∀ p, charCoeffRatio β (E p).1 (E p).2 •
      hatSummand (e '' B) (transportAlong e B f) hf' (precompAlong e F) (E p).1 (E p).2 =
      precompAlong e (charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2) := by
    intro p
    have h₁ : charCoeffRatio β (E p).1 (E p).2 = charCoeffRatio β p.1 p.2 :=
      charCoeffRatio_comp_symm β σ p.1 p.2
    have h₂ := hatSummand_precompAlong e B he f hf hf' F p.1 p.2
    have h₃ : hatSummand (e '' B) (transportAlong e B f) hf' (precompAlong e F) (E p).1 (E p).2 =
        precompAlong e (hatSummand B f hf F p.1 p.2) := h₂
    rw [h₁, h₃]
    rfl
  simp only [hatSum]
  rw [← E.tsum_eq, tsum_congr hterm]
  exact precompAlong_tsum e (Function.invFun e) (Function.leftInverse_invFun he) _
end Precomposition
theorem hatNaturality : HatNaturalityStatement := by
  intro J _ _ β B f hf _ _
  have key : HatNaturalInjective β B f hf := by
    intro J' _ e he
    exact ⟨isRealEntryPolynomial_transportAlong e B he f hf,
      fun F _ => hatSum_precompAlong e B he β f hf _ F⟩
  refine ⟨key, fun s => ?_⟩
  obtain ⟨hs, h⟩ := key J s s.injective
  exact ⟨hs, fun F hF => ((coe_precompAlong_perm s _).symm.trans
    (congrArg (fun H : C(J → specialUnitary, ℂ) => (H : (J → specialUnitary) → ℂ)) (h F hF).symm))⟩
end YangMills.Construction.SpinHarmonics.HatNaturality
end
