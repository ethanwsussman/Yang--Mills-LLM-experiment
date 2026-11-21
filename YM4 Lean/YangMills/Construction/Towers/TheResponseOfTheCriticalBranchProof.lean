import YangMills.Construction.Towers.ClosedFormsInTheKernelOfTheIteratedAverage
import YangMills.Construction.Towers.CrossingAndLinearAveragesUpToADifference
import YangMills.Construction.Towers.DifferentialOfTheLiftOfTheCriticalBranch
import YangMills.Construction.Towers.GradientsAreFormedAlongTheCriticalBranch
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import YangMills.Construction.Towers.SecondDifferentialAtACriticalPointProof
import YangMills.Construction.Towers.TheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CriticalBranchResponse
open ResponseMaps (OnTower)
variable {L n k j : ℕ}
private theorem vertexCoboundary_mem_edgeFormSpace {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) :
    vertexCoboundary f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
private theorem vertexCoboundary_add (f g : Vertex L n k j → Matrices.ComplexMatrix2) :
    vertexCoboundary (f + g) = vertexCoboundary f + vertexCoboundary g := by
  funext e
  simp only [vertexCoboundary, Pi.add_apply]
  abel
abbrev _root_.YangMills.SharedProofs.p26773 := @vertexCoboundary_add
private theorem isClosedEdgeForm_vertexCoboundary (hClosed : ClosedEdgeFormsOnPeriodicLattice)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) : IsClosedEdgeForm (vertexCoboundary f) := by
  refine (hClosed L n k j hL hn hj _ (vertexCoboundary_mem_edgeFormSpace hf)).2
    ⟨f, hf, 0, (edgeFormSpace L n k j).zero_mem, fun _ _ _ => rfl, by simp⟩
private theorem eq_zero_of_edgeFormPairing_self (hSpaces : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (A : edgeFormSpace L n k j)
    (h : edgeFormPairing (A : Edge L n k j → Matrices.ComplexMatrix2)
      (A : Edge L n k j → Matrices.ComplexMatrix2) = 0) : A = 0 := by
  obtain ⟨_, _, _, c, hc⟩ := hSpaces L n k j hL hn hj
  have h0 : c.inner A A = 0 := by
    have := hc A A
    rw [h] at this
    exact_mod_cast this.symm
  exact c.definite A h0
private theorem edgeFormPairing_sub_left (hSpaces : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (A A' C : edgeFormSpace L n k j) :
    edgeFormPairing ((A - A' : edgeFormSpace L n k j) : Edge L n k j → Matrices.ComplexMatrix2)
        (C : Edge L n k j → Matrices.ComplexMatrix2) =
      edgeFormPairing (A : Edge L n k j → Matrices.ComplexMatrix2)
          (C : Edge L n k j → Matrices.ComplexMatrix2) -
        edgeFormPairing (A' : Edge L n k j → Matrices.ComplexMatrix2)
          (C : Edge L n k j → Matrices.ComplexMatrix2) := by
  obtain ⟨_, _, _, c, hc⟩ := hSpaces L n k j hL hn hj
  have h := c.add_left (A - A') A' C
  rw [sub_add_cancel] at h
  rw [hc, hc, hc, h]
  push_cast
  ring
private theorem edgeFormPairing_add_right (hSpaces : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (C A A' : edgeFormSpace L n k j) :
    edgeFormPairing (C : Edge L n k j → Matrices.ComplexMatrix2)
        ((A + A' : edgeFormSpace L n k j) : Edge L n k j → Matrices.ComplexMatrix2) =
      edgeFormPairing (C : Edge L n k j → Matrices.ComplexMatrix2)
          (A : Edge L n k j → Matrices.ComplexMatrix2) +
        edgeFormPairing (C : Edge L n k j → Matrices.ComplexMatrix2)
          (A' : Edge L n k j → Matrices.ComplexMatrix2) := by
  obtain ⟨_, _, _, c, hc⟩ := hSpaces L n k j hL hn hj
  have hs : ∀ x y : edgeFormSpace L n k j, c.inner x y = c.inner y x := fun x y => by
    simpa using (c.conj_inner_symm x y).symm
  rw [hc, hc, hc, hs C, hs C, hs C, c.add_left]
  push_cast
  rfl
private theorem edgeFormPairing_zero_left (C : Edge L n k j → Matrices.ComplexMatrix2) :
    edgeFormPairing (0 : Edge L n k j → Matrices.ComplexMatrix2) C = 0 := by apply _root_.YangMills.Construction.Tower.CriticalSecondDeriv.edgeFormPairing_zero <;> assumption
private theorem edgeFormPairing_zero_right (C : Edge L n k j → Matrices.ComplexMatrix2) :
    edgeFormPairing C (0 : Edge L n k j → Matrices.ComplexMatrix2) = 0 := by
  simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, Matrices.ComplexMatrix2.halfTrace]
private theorem responses_differ_by_coboundary
    (hRel : TorusResponseRelations.statement)
    (hSmooth : CrossingAndLinearSmoothingDifferByCoboundary)
    (hKer : ClosedInSmoothingKernelIsExact)
    (hMaps : ResponseMaps.ResponseMapsHold)
    (hClosed : ClosedEdgeFormsOnPeriodicLattice) (hSpaces : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n) (B : edgeFormSpace L n k k)
    (A₁ : edgeFormSpace L n k 0) (μ₁ : edgeFormSpace L n k k)
    (hD : ProlongDifferential.FormConditions L n k B A₁ μ₁) :
    (∃ f ∈ vertexFunctionSpace L n k 0, (A₁ : Edge L n k 0 → Matrices.ComplexMatrix2) =
      (meshScaledResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2) + vertexCoboundary f) ∧
    μ₁ = periodicDefect L n k B ∧
    formCoboundary L n k A₁ = formCoboundary L n k (meshScaledResponse L n k B) := by
  have R := hRel L hL k hk n hn B
  have T : OnTower L n k := hMaps L hL k n hk hn
  obtain ⟨hup, hex⟩ := hSmooth L hL k n hk hn
  obtain ⟨f₀, hf₀, hq⟩ := hex _ (meshScaledResponse L n k B).2
  have h0k : 0 ≤ k := Nat.zero_le k
  set A₂ : edgeFormSpace L n k 0 := meshScaledResponse L n k B with hA₂
  set μ₂ : edgeFormSpace L n k k := periodicDefect L n k B with hμ₂
  let G : edgeFormSpace L n k 0 := ⟨vertexCoboundary f₀, vertexCoboundary_mem_edgeFormSpace hf₀⟩
  have hG : formCoboundary L n k G = 0 :=
    Subtype.ext ((T.coboundary_eq G).trans (isClosedEdgeForm_vertexCoboundary hClosed hL hn h0k hf₀))
  let E : edgeFormSpace L n k 0 := A₁ - (A₂ + G)
  have hQ₁ : linearSmoothingToTop L n k A₁ = B :=
    Subtype.ext ((T.linear_eq A₁).trans hD.smoothing_eq)
  have hQ₂ : linearSmoothingToTop L n k (A₂ + G) = B :=
    Subtype.ext ((T.linear_eq (A₂ + G)).trans (hq.trans R.smoothing_eq))
  have hQE : linearSmoothingToTop L n k E = 0 := by
    simp only [E, map_sub, hQ₁, hQ₂, sub_self]
  have hμ : ∀ ξ : edgeFormSpace L n k 0,
      edgeFormPairing (μ₂ : Edge L n k k → Matrices.ComplexMatrix2)
          (linearSmoothingToTop L n k ξ : Edge L n k k → Matrices.ComplexMatrix2) =
        edgeFormPairing (μ₂ : Edge L n k k → Matrices.ComplexMatrix2)
          (crossingSmoothingToTop L n k ξ : Edge L n k k → Matrices.ComplexMatrix2) := by
    intro ξ
    obtain ⟨f', hf', he⟩ := hup k le_rfl ξ ξ.2 0 (vertexFunctionSpace L n k 0).zero_mem
    have hz : vertexCoboundary (0 : Vertex L n k 0 → Matrices.ComplexMatrix2) = 0 := by
      funext e
      simp [vertexCoboundary]
    rw [hz, add_zero] at he
    let Y : edgeFormSpace L n k k := ⟨vertexCoboundary f', vertexCoboundary_mem_edgeFormSpace hf'⟩
    have hY : linearSmoothingToTop L n k ξ = crossingSmoothingToTop L n k ξ + Y :=
      Subtype.ext ((T.linear_eq ξ).trans
        (he.trans (by rw [Submodule.coe_add, T.crossing_eq ξ])))
    rw [hY, edgeFormPairing_add_right hSpaces hL hn le_rfl]
    change _ + edgeFormPairing (μ₂ : Edge L n k k → Matrices.ComplexMatrix2) (vertexCoboundary f') = _
    rw [show edgeFormPairing (μ₂ : Edge L n k k → Matrices.ComplexMatrix2) (vertexCoboundary f') = 0 from
      R.pairing_vertex_eq_zero f' hf', add_zero]
  have hTr : linearSmoothingTranspose L n k μ₂ = crossingSmoothingTranspose L n k μ₂ := by
    have hX := eq_zero_of_edgeFormPairing_self hSpaces hL hn h0k
      (linearSmoothingTranspose L n k μ₂ - crossingSmoothingTranspose L n k μ₂) (by
        rw [edgeFormPairing_sub_left hSpaces hL hn h0k, T.linear_transpose, T.crossing_transpose, hμ,
          sub_self])
    exact sub_eq_zero.1 hX
  have hfE : formCoboundary L n k E = formCoboundary L n k A₁ - formCoboundary L n k A₂ := by
    simp only [E, map_sub, map_add, hG, add_zero]
  have hDE : formCoboundaryTranspose L n k (formCoboundary L n k E) =
      linearSmoothingTranspose L n k (μ₁ - μ₂) := by
    rw [hfE, map_sub, hD.coboundary_eq, R.coboundary_eq, map_sub, hTr]
  have hE0 : formCoboundary L n k E = 0 := by
    refine T.face_pairing_definite _ ?_
    have h := T.coboundary_transpose (formCoboundary L n k E) E
    rw [hDE, T.linear_transpose, hQE] at h
    rw [← h]
    exact edgeFormPairing_zero_right _
  have hcl : IsClosedEdgeForm (E : Edge L n k 0 → Matrices.ComplexMatrix2) :=
    (T.coboundary_eq E).symm.trans (congrArg Subtype.val hE0)
  have hker : linearSmoothingIter L n k k (E : Edge L n k 0 → Matrices.ComplexMatrix2) = 0 :=
    (T.linear_eq E).symm.trans (congrArg Subtype.val hQE)
  obtain ⟨f, hf, hfE'⟩ := hKer L hL k n hk hn E E.2 hcl hker
  refine ⟨⟨f₀ + f, (vertexFunctionSpace L n k 0).add_mem hf₀ hf, ?_⟩, ?_, ?_⟩
  · rw [vertexCoboundary_add, hfE']
    funext e
    simp only [E, G, Submodule.coe_sub, Submodule.coe_add, Pi.add_apply, Pi.sub_apply]
    abel
  · obtain ⟨ξ, hξ⟩ := T.linear_surjective (μ₁ - μ₂)
    have h := T.linear_transpose (μ₁ - μ₂) ξ
    rw [← hDE, hE0, map_zero, hξ] at h
    refine sub_eq_zero.1 (eq_zero_of_edgeFormPairing_self hSpaces hL hn le_rfl _ ?_)
    rw [← h]
    exact edgeFormPairing_zero_left _
  · exact sub_eq_zero.1 (hfE.symm.trans hE0)
theorem responseProperties_of_steps (hRel : TorusResponseRelations.statement)
    (hDiff : ProlongDifferential.ProlongDifferentialHolds)
    (hGrad : CriticalBranchGradients.GradientsExistAlongBranch)
    (hLift : ChosenProlongDerivAtIdentity)
    (hSmooth : CrossingAndLinearSmoothingDifferByCoboundary)
    (hKer : ClosedInSmoothingKernelIsExact)
    (hMaps : ResponseMaps.ResponseMapsHold)
    (hClosed : ClosedEdgeFormsOnPeriodicLattice) (hSpaces : FiniteSideFormSpaces) :
    ResponseConditions := by
  intro L hL i
  refine ⟨PeriodicLattice.torusSide L 1, ⟨1, by norm_num, rfl⟩, ?_⟩
  rintro s - - n hn rfl B hB
  have hk : 1 ≤ i + 1 := by omega
  obtain ⟨A₁, μ₁, hD⟩ := hDiff L hL (i + 1) hk n hn ⟨B, hB⟩
  obtain ⟨⟨f, hf, he⟩, hμ, hcob⟩ :=
    responses_differ_by_coboundary hRel hSmooth hKer hMaps hClosed hSpaces hL hk hn ⟨B, hB⟩ A₁ μ₁ hD
  have hdiff : (A₁ : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) =
      leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
        (trivialField L n (i + 1) (i + 1)) B := hD.deriv_eq
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨f, hf, ?_⟩
    rw [← hdiff, he, add_sub_cancel_left]
  · have hG := hGrad L hL (i + 1) hk n hn ⟨B, hB⟩
    have R := hRel L hL (i + 1) hk n hn ⟨B, hB⟩
    refine ⟨hG.1, hG.2, ?_, ?_, R.coboundary_eq⟩
    · have h := hD.energy_hasDeriv
      rw [hμ] at h
      exact h
    · have h := hD.action_hasDeriv
      rw [hcob] at h
      exact h
  · obtain ⟨hup, -⟩ := hSmooth L hL (i + 1) n hk hn
    obtain ⟨f', hf', he'⟩ := hup i (by omega) _ (meshScaledResponse L n (i + 1) B).2 f hf
    refine ⟨f', hf', ?_⟩
    rw [hLift L hL i n hn B hB, ← hdiff, he, he', add_sub_cancel_left]
end YangMills.Construction.Tower.CriticalBranchResponse
end
