import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.GradientsUnderTheDilation
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k j : ℕ}
theorem isLeftGradient_of_edgeForm {𝔇 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {f : (Edge L n k j → Matrices.ComplexMatrix2) → ℂ}
    {U X : Edge L n k j → Matrices.ComplexMatrix2} (hX : X ∈ edgeFormSpace L n k j)
    (h : ∀ B ∈ edgeFormSpace L n k j, edgeFormPairing X B = leftDeriv f U B) :
    IsLeftGradient 𝔇 f U X :=
  ⟨⟨fun b hb => (hX.1 b hb).2, hX.2⟩, fun _ => hX, fun B hB _ => h B hB⟩
theorem leftGradient_ofReal_spec {𝔇 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ}
    {U X : Edge L n k j → Matrices.ComplexMatrix2}
    (hX : IsLeftGradient 𝔇 (fun V => (F V : ℂ)) U X) :
    leftGradient 𝔇 (fun V => (F V : ℂ)) U ∈ edgeFormSpace L n k j ∧
      ∀ B ∈ edgeFormSpace L n k j, HasFiniteSupp (restrictToPositiveEdges B) →
        edgeFormPairing (leftGradient 𝔇 (fun V => (F V : ℂ)) U) B =
          leftDeriv (fun V => (F V : ℂ)) U B := by
  have hε := Classical.epsilon_spec (p := IsLeftGradient 𝔇 (fun V => (F V : ℂ)) U) ⟨X, hX⟩
  exact ⟨hε.2.1 fun V _ => Complex.ofReal_im _, hε.2.2⟩
theorem edgeForm_eq_of_pairing_eq {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → Matrices.ComplexMatrix2)
      (B' : Edge L n k j → Matrices.ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    {x y : edgeFormSpace L n k j}
    (h : ∀ B : edgeFormSpace L n k j,
      edgeFormPairing (x : Edge L n k j → Matrices.ComplexMatrix2)
        (B : Edge L n k j → Matrices.ComplexMatrix2) =
      edgeFormPairing (y : Edge L n k j → Matrices.ComplexMatrix2)
        (B : Edge L n k j → Matrices.ComplexMatrix2)) : x = y := by
  have hz : ∀ B : edgeFormSpace L n k j, c.inner (x - y) B = 0 := by
    intro B
    have h1 : c.inner x B = c.inner y B := by
      have hxy := h B
      rw [hc, hc] at hxy
      exact_mod_cast hxy
    have h2 := c.add_left (x - y) y B
    rw [sub_add_cancel, h1] at h2
    linarith
  exact sub_eq_zero.1 (c.definite _ (hz _))
theorem scaledGradients_of_analytic (hRA : AnalyticMapsAlongCurves)
    (hP : diffAtZeroPathsStatement) (hS : FiniteSideFormSpaces)
    (hD : ScalingNearTrivialField) : ScaledGradients := by
  intro L n k j hL hj hstd hn l hl 𝒰 F F' hF hcar U hU
  have hlk : l ≤ k := hl.trans hj
  have hn' : 0 < scaledExponent n k j := Nat.add_pos_left hn _
  have hU1 : U ∈ fieldSpace L n k l := hF.1.1 hU
  obtain ⟨hbij, -, -, ⟨T, hT⟩, hpair, hexp⟩ := (hD L n k j l l hL hj hstd hn hl hl).1
  obtain ⟨X, hX, hXd⟩ := (hRA L n k l l hstd hn hlk hlk).2 𝒰 F hF U hU
  obtain ⟨-, -, hline⟩ := hP L n k l hstd hn hlk
  obtain ⟨hfin, -, -, c, hc⟩ := hS L n k l hstd hn hlk
  obtain ⟨hfin', -, -, c', hc'⟩ := hS L (scaledExponent n k j) j l hstd hn' hl
  have hd1 : ∀ B ∈ edgeFormSpace L n k l,
      edgeFormPairing X B = leftDeriv (fun V => (F V : ℂ)) U B := by
    intro B hB
    obtain ⟨hp, h0, ht⟩ := hline U hU1 B hB
    have hder := hXd _ hp h0
    rw [ht] at hder
    have hreal : edgeFormPairing X B = (((edgeFormPairing X B).re : ℝ) : ℂ) := by
      have hcXB := hc ⟨X, hX⟩ ⟨B, hB⟩
      simp only at hcXB
      rw [hcXB, Complex.ofReal_re]
    rw [hreal]
    exact hder.ofReal_comp.deriv.symm
  have hg1 := leftGradient_ofReal_spec (𝔇 := fieldSpace L n k l) (F := F) (U := U)
    (isLeftGradient_of_edgeForm hX hd1)
  set G := leftGradient (fieldSpace L n k l) (fun V => (F V : ℂ)) U with hG
  have hGf : G ∈ edgeFormSpace L n k l := hg1.1
  have hTf : ∀ B ∈ edgeFormSpace L n k l, transportTotal (scaleEdge hL hj l) B ∈
      edgeFormSpace L (scaledExponent n k j) j l := fun B hB => by
    rw [← hT ⟨B, hB⟩]
    exact (T ⟨B, hB⟩).2
  have hder : ∀ B ∈ edgeFormSpace L n k l,
      leftDeriv (fun V => (F' V : ℂ)) (transportTotal (scaleEdge hL hj l) U)
          (transportTotal (scaleEdge hL hj l) B) =
        leftDeriv (fun V => (F V : ℂ)) U B := by
    intro B hB
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(hline U hU1 B hB).1.1] with t ht
    have hsm : ((t : ℂ) • B) ∈ edgeFormSpace L n k l := by
      have hts : ((t : ℂ) • B) = t • B := algebraMap_smul ℂ t B
      rw [hts]
      exact (edgeFormSpace L n k l).smul_mem t hB
    have he := hexp U hU1 _ hsm
    have hcv := hcar _ ht
    rw [he] at hcv
    show ((F' (PeriodicLattice.expTwist ((t : ℂ) • transportTotal (scaleEdge hL hj l) B)
      (transportTotal (scaleEdge hL hj l) U)) : ℝ) : ℂ) =
      ((F (PeriodicLattice.expTwist ((t : ℂ) • B) U) : ℝ) : ℂ)
    exact congrArg _ hcv
  have hfs : ∀ B : Edge L n k l → Matrices.ComplexMatrix2,
      HasFiniteSupp (restrictToPositiveEdges B) :=
    fun B => Set.toFinite _
  have hd2 : ∀ B' ∈ edgeFormSpace L (scaledExponent n k j) j l,
      edgeFormPairing (transportTotal (scaleEdge hL hj l) G) B' =
        leftDeriv (fun V => (F' V : ℂ)) (transportTotal (scaleEdge hL hj l) U) B' := by
    intro B' hB'
    obtain ⟨B, hB⟩ := T.surjective ⟨B', hB'⟩
    have hB'' : B' = transportTotal (scaleEdge hL hj l) (B : Edge L n k l → Matrices.ComplexMatrix2) := by
      rw [← hT B, hB]
    rw [hB'', hpair G hGf B B.2, hder B B.2]
    exact hg1.2 B B.2 (hfs _)
  have hg2 := leftGradient_ofReal_spec (𝔇 := fieldSpace L (scaledExponent n k j) j l) (F := F')
    (U := transportTotal (scaleEdge hL hj l) U) (isLeftGradient_of_edgeForm (hTf G hGf) hd2)
  have hfs' : ∀ B : Edge L (scaledExponent n k j) j l → Matrices.ComplexMatrix2,
      HasFiniteSupp (restrictToPositiveEdges B) := fun B => Set.toFinite _
  have hxy := edgeForm_eq_of_pairing_eq hc' (x := ⟨_, hg2.1⟩) (y := ⟨_, hTf G hGf⟩) fun B =>
    (hg2.2 B B.2 (hfs' _)).trans (hd2 B B.2).symm
  exact congrArg Subtype.val hxy
end YangMills.Construction.Tower
end
