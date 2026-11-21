import YangMills.Construction.Towers.AxialGaugeOfTheLift
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverage
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranch
import YangMills.Construction.Towers.SecondDerivativeAtOneIsBilinear
import YangMills.Construction.Towers.SecondFormOfTheNextLevel
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace NextLevelHessian
theorem bilin_eq_zero_of_self_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (q : V → V → ℝ) (hsymm : ∀ x ∈ S, ∀ y ∈ S, q x y = q y x)
    (hlin : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ c : ℝ, q (c • x + y) z = c * q x z + q y z)
    (hnonneg : ∀ x ∈ S, 0 ≤ q x x) {x y : V} (hx : x ∈ S) (hxx : q x x = 0) (hy : y ∈ S) :
    q x y = 0 := by
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * q x y + q y y := by
    intro t
    have hmem : t • x + y ∈ S := S.add_mem (S.smul_mem t hx) hy
    have ha : q x (t • x + y) = q x y := by
      rw [hsymm x hx _ hmem, hlin x hx y hy x hx t, hxx, hsymm y hy x hx]
      ring
    have hb : q y (t • x + y) = t * q x y + q y y := by
      rw [hsymm y hy _ hmem, hlin x hx y hy y hy t]
    have hc := hnonneg _ hmem
    rw [hlin x hx y hy _ hmem t, ha, hb] at hc
    linarith
  by_contra hne
  have hd := hquad (-(q y y + 1) / (2 * q x y))
  have he : 2 * (-(q y y + 1) / (2 * q x y)) * q x y = -(q y y + 1) := by
    field_simp
  linarith
end NextLevelHessian
theorem nextLevelHessian_holds
    (hStep : StepQuadraticForm)
    (hGauge : AxialGaugeOfProlongation)
    (hComposite : CompositeSecondOrderAtIdentity)
    (hBilinear : LeftSecondDerivAtIdentityBilinear)
    (hSmoothing : LinearSmoothingOnClosedForms) :
    NextLevelHessian.Statement := by
  intro L n k i hL hn hi b 𝒰 ε p hb hp
  obtain ⟨⟨𝒰F, h𝒰F, hanF⟩, hF1, hgradF, hsec, hpos⟩ := hStep L n k i hL hn hi b hb
  obtain ⟨𝒲, h𝒲, hanp⟩ := hp.analytic_section
  obtain ⟨⟨𝒲', h𝒲', hanC⟩, hnear, hgradC, hchain⟩ :=
    hComposite L n k i hL hn hi 𝒰F 𝒲 (b.gaugeFixedEnergy i) p h𝒰F hanF h𝒲 hanp hp.section_trivial hgradF
  obtain ⟨𝒰S, h𝒰S, hanS⟩ := hb.analytic_energy i le_rfl
  obtain ⟨symS, linS⟩ := hBilinear L n k i hL hn hi.le 𝒰S (b.energy i) h𝒰S hanS
  obtain ⟨symF, linF⟩ := hBilinear L n k i hL hn hi.le 𝒰F (b.gaugeFixedEnergy i) h𝒰F hanF
  obtain ⟨symC, linC⟩ := hBilinear L n k (i + 1) hL hn hi 𝒲' _ h𝒲' hanC
  obtain ⟨hQsub, hQclosed, hlift⟩ := hSmoothing L n k i hL hn hi
  have hsecP := hp.deriv_section
  have hortho := hp.deriv_orthogonal
  have hone := hp.section_trivial
  have hA := hGauge L n k i hL hn hi b 𝒰 ε p hb hp
  have hS := hnear _ (hb.energy_nonneg i le_rfl)
  clear hStep hGauge hComposite hBilinear hSmoothing hnear hp
  generalize leftDifferential p (trivialField L n k (i + 1)) = P at *
  generalize leftSecondDeriv (b.gaugeFixedEnergy i) (trivialField L n k i) = G at *
  generalize leftSecondDeriv (fun W => b.gaugeFixedEnergy i (p W))
    (trivialField L n k (i + 1)) = C at *
  have hen0 : ∀ ξ ∈ edgeFormSpace L n k i, 0 ≤ b.stepQuadratic i ξ := fun ξ hξ =>
    add_nonneg (hb.hessianAtOne_nonneg i le_rfl ξ hξ) (sq_nonneg _)
  have hCG : ∀ B ∈ edgeFormSpace L n k (i + 1), C B B = b.stepQuadratic i (P B) := fun B hB => by
    rw [hchain B hB B hB, hsec _ (hsecP B hB).1]
  have hsplit : ∀ B ∈ edgeFormSpace L n k (i + 1), ∀ ξ ∈ edgeFormSpace L n k i,
      linearSmoothing L n k i ξ = B →
      ξ - P B ∈ edgeFormSpace L n k i ∧ linearSmoothing L n k i (ξ - P B) = 0 ∧
        b.stepQuadratic i ξ = b.stepQuadratic i (P B) + b.stepQuadratic i (ξ - P B) := by
    intro B hB ξ hξ hq
    obtain ⟨hPf, hPq⟩ := hsecP B hB
    have hd : ξ - P B ∈ edgeFormSpace L n k i := (edgeFormSpace L n k i).sub_mem hξ hPf
    have hq0 : linearSmoothing L n k i (ξ - P B) = 0 := by
      rw [hQsub ξ hξ _ hPf, hq, hPq, sub_self]
    refine ⟨hd, hq0, ?_⟩
    have hdec : (1 : ℝ) • P B + (ξ - P B) = ξ := by simp
    have ho : G (P B) (ξ - P B) = 0 := hortho B hB _ hd hq0
    have h1 : G ξ ξ = G (P B) ξ + G (ξ - P B) ξ := by
      have h := linF (P B) hPf (ξ - P B) hd ξ hξ 1
      rwa [hdec, one_mul] at h
    have h2 : G (P B) ξ = G (P B) (P B) := by
      have h := linF (P B) hPf (ξ - P B) hd (P B) hPf 1
      rw [hdec, one_mul] at h
      rw [symF _ hPf _ hξ, h, symF _ hd _ hPf, ho, add_zero]
    have h3 : G (ξ - P B) ξ = G (ξ - P B) (ξ - P B) := by
      have h := linF (P B) hPf (ξ - P B) hd (ξ - P B) hd 1
      rw [hdec, one_mul, ho, zero_add] at h
      rw [symF _ hd _ hξ, h]
    rw [← hsec ξ hξ, ← hsec _ hPf, ← hsec _ hd, h1, h2, h3]
  have hnonneg : ∀ B ∈ edgeFormSpace L n k (i + 1), 0 ≤ C B B := fun B hB => by
    rw [hCG B hB]
    exact hen0 _ (hsecP B hB).1
  refine ⟨⟨𝒲', h𝒲', hanC⟩, ?_, ?_, hgradC, hnonneg, ?_, ?_, ?_⟩
  · filter_upwards [hS, hA] with W h1 h2
    rw [h2.2]
    exact h1
  · rw [hone]
    exact hF1
  · intro B hB
    constructor
    · intro h
      have h0 := h B hB
      rw [hCG B hB] at h0
      obtain ⟨hPf, hPq⟩ := hsecP B hB
      have hs0 : b.hessianAtOne i (P B) (P B) = 0 := by
        have h1 := hb.hessianAtOne_nonneg i le_rfl _ hPf
        have h2 := sq_nonneg (traceFinsumNorm (fineOnlyContourAverage L n k i (P B)))
        unfold CriticalBranchData.stepQuadratic at h0
        linarith
      have hcl : IsClosedEdgeForm (P B) := (hb.hessianAtOne_null_iff i le_rfl _ hPf).1 fun B' hB' =>
        NextLevelHessian.bilin_eq_zero_of_self_eq_zero (edgeFormSpace L n k i) (b.hessianAtOne i)
          symS linS (hb.hessianAtOne_nonneg i le_rfl) hPf hs0 hB'
      have h1 := hQclosed _ hPf hcl
      rwa [hPq] at h1
    · intro hc
      obtain ⟨ξ, hξ, hcl, hq, hL0⟩ := hlift B hB hc
      have hnull := (hb.hessianAtOne_null_iff i le_rfl ξ hξ).2 hcl
      have he : b.stepQuadratic i ξ = 0 := by
        unfold CriticalBranchData.stepQuadratic
        rw [hnull ξ hξ, hL0]
        have htr : Matrices.ComplexMatrix2.halfTrace (0 : Matrices.ComplexMatrix2) = 0 := by
          simp [Matrices.ComplexMatrix2.halfTrace]
        simp [traceFinsumNorm, traceFinsumPairing, htr]
      obtain ⟨hd, -, h3⟩ := hsplit B hB ξ hξ hq
      have h4 := hen0 _ hd
      have h5 := hen0 _ (hsecP B hB).1
      have hCB : C B B = 0 := by
        rw [hCG B hB]
        linarith
      exact fun B' hB' => NextLevelHessian.bilin_eq_zero_of_self_eq_zero
        (edgeFormSpace L n k (i + 1)) C symC linC hnonneg hB hCB hB'
  · intro B hB
    obtain ⟨hPf, hPq⟩ := hsecP B hB
    refine ⟨⟨P B, hPf, hPq, hCG B hB⟩, ?_⟩
    rintro r ⟨ξ, hξ, hq, rfl⟩
    obtain ⟨hd, -, h3⟩ := hsplit B hB ξ hξ hq
    rw [hCG B hB, h3]
    linarith [hen0 _ hd]
  · intro B hB ξ
    obtain ⟨hPf, hPq⟩ := hsecP B hB
    constructor
    · rintro ⟨hξ, hq, he⟩
      obtain ⟨hd, hq0, h3⟩ := hsplit B hB ξ hξ hq
      by_contra hne
      have h4 := hpos _ hd hq0 (sub_ne_zero.mpr hne)
      rw [hCG B hB] at he
      linarith
    · rintro rfl
      exact ⟨hPf, hPq, (hCG B hB).symm⟩
end YangMills.Construction.Tower
end
