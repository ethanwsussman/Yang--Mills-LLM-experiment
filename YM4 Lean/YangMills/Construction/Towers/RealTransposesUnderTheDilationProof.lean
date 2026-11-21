import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.RealTransposesUnderTheDilation
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem scalingCommutesWithRealTranspose_of_pairing (hP : RealTransposeEdgeFormPairing)
    (hS : FiniteSideFormSpaces)
    (hD : ScalingNearTrivialField) :
    ScalingCommutesWithRealTranspose := by
  intro L n k j hL hj hst hn a ha b hb A A' hA g g' hg
  have hn' : 0 < scaledExponent n k j := Nat.add_pos_left hn _
  have hDa := (hD L n k j a a hL hj hst hn ha ha).1
  have hDb := (hD L n k j b b hL hj hst hn hb hb).1
  obtain ⟨Ta, hTa⟩ := hDa.2.2.2.1
  have pa := hDa.2.2.2.2.1
  have pb := hDb.2.2.2.2.1
  obtain ⟨-, -, -, c, hc⟩ := hS L (scaledExponent n k j) j a hst hn' ha
  set u : edgeFormSpace L n k a :=
    PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k a)
      (S' := edgePairedSpace L n k b) A g with hu
  set u' : edgeFormSpace L (scaledExponent n k j) j a :=
    PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L (scaledExponent n k j) j a)
      (S' := edgePairedSpace L (scaledExponent n k j) j b) A' g' with hu'
  have key : ∀ f : edgeFormSpace L n k a, c.inner u' (Ta f) = c.inner (Ta u) (Ta f) := by
    intro f
    have e₁ : edgeFormPairing (u' : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2)
        (Ta f : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) =
        edgeFormPairing (g' : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2)
          (A' (Ta f) : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2) :=
      hP L (scaledExponent n k j) j a b hst hn' ha hb A' g' (Ta f)
    have e₂ : edgeFormPairing (u : Edge L n k a → Matrices.ComplexMatrix2)
        (f : Edge L n k a → Matrices.ComplexMatrix2) =
        edgeFormPairing (g : Edge L n k b → Matrices.ComplexMatrix2)
          (A f : Edge L n k b → Matrices.ComplexMatrix2) :=
      hP L n k a b hst hn (ha.trans hj) (hb.trans hj) A g f
    have e₃ := pb g.1 g.2 (A f).1 (A f).2
    have e₄ := pa u.1 u.2 f.1 f.2
    have e₅ : (A' (Ta f) : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2) =
        transportTotal (scaleEdge hL hj b) (A f : Edge L n k b → Matrices.ComplexMatrix2) :=
      hA f (Ta f) (hTa f)
    have e₆ : edgeFormPairing (Ta u : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2)
        (Ta f : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) =
        edgeFormPairing (u : Edge L n k a → Matrices.ComplexMatrix2)
          (f : Edge L n k a → Matrices.ComplexMatrix2) := by
      rw [hTa u, hTa f]
      exact e₄
    have e₇ : ((c.inner u' (Ta f) : ℝ) : ℂ) = ((c.inner (Ta u) (Ta f) : ℝ) : ℂ) := by
      rw [← hc, ← hc, e₁, e₅, hg, e₆, e₂]
      exact e₃
    exact_mod_cast e₇
  have hd : u' + (-1 : ℝ) • Ta u = 0 := by
    apply c.definite
    have e := key (Ta.symm (u' + (-1 : ℝ) • Ta u))
    rw [LinearEquiv.apply_symm_apply] at e
    rw [c.add_left, c.smul_left, e]
    simp
  have hfin : u' = Ta u := by
    rw [neg_one_smul ℝ (Ta u)] at hd
    exact add_neg_eq_zero.mp hd
  calc (u' : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2)
      = (Ta u : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) := by rw [hfin]
    _ = _ := hTa u
end YangMills.Construction.Tower
end
