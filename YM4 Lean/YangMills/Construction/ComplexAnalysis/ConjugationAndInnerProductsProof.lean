import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.ComplexAnalysis.BanachValuedAffineCoordinates
import YangMills.Construction.ComplexAnalysis.ConjugationAndInnerProducts
import YangMills.Construction.ComplexAnalysis.ScalarHolomorphyAgreement
import Mathlib
open Filter
open scoped ComplexConjugate Topology
noncomputable section
namespace YangMills.Construction.BanachValued.ConjugationInner
variable {p : ℕ}
theorem continuous_conjPoint : Continuous (conjPoint (p := p)) :=
  continuous_pi fun j => Complex.continuous_conj.comp (continuous_apply j)
theorem conjPoint_add_smul_stdBasisVector (a : Coordinates.ComplexCoordinates p) (ζ : ℂ)
    (j : Fin p) :
    conjPoint (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
      conjPoint a + conj ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [conjPoint, Coordinates.ComplexCoordinates.stdBasisVector]
  · simp [conjPoint, Coordinates.ComplexCoordinates.stdBasisVector, hij]
theorem isCoordHolomorphicOn_iff {U : Set (Coordinates.ComplexCoordinates p)}
    {g : Coordinates.ComplexCoordinates p → ℂ} :
    IsCoordHolomorphicOn U g ↔
      IsOpen U ∧ ContinuousOn g U ∧ ∀ a ∈ U, ∀ j : Fin p, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => g (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.DeltaSharedProofs.p501560 <;> assumption
theorem isCoordHolomorphicOn_conj_comp_conjPoint {U : Set (Coordinates.ComplexCoordinates p)}
    {g : Coordinates.ComplexCoordinates p → ℂ} (hg : IsCoordHolomorphicOn U g) :
    IsCoordHolomorphicOn (conjSet U) fun z => conj (g (conjPoint z)) := by
  obtain ⟨hU, hc, hd⟩ := isCoordHolomorphicOn_iff.1 hg
  refine isCoordHolomorphicOn_iff.2 ⟨hU.preimage continuous_conjPoint, ?_, ?_⟩
  · exact Complex.continuous_conj.comp_continuousOn
      (hc.comp continuous_conjPoint.continuousOn fun z hz => hz)
  · intro a ha j
    have hconj : Tendsto (fun ζ : ℂ => conj ζ) (𝓝 0) (𝓝 0) := by
      simpa using (Complex.continuous_conj.tendsto (0 : ℂ))
    refine (hconj.eventually (hd (conjPoint a) ha j)).mono fun ζ hζ => ?_
    have h := differentiableAt_conj_conj_iff.2 hζ
    have heq : (fun ζ : ℂ =>
          conj (g (conjPoint (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)))) =
        (conj ∘ (fun ζ : ℂ =>
          g (conjPoint a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ∘ conj) := by
      funext ζ
      simp [conjPoint_add_smul_stdBasisVector]
    rw [heq]
    exact h
theorem properties_holds (hAgree : ScalarAgreement.Agreement)
    (hComp : AffineCoordinates.HolomorphicCompositionProperties) : Properties := by
  intro p hp U hU
  refine ⟨fun g => (hAgree p hp U hU g).symm, fun g hg => isCoordHolomorphicOn_conj_comp_conjPoint hg, ?_⟩
  intro K _ _ _ Φ ψ hΦ
  have hfirst : IsCoordHolomorphicOn U (fun z => inner ℂ ψ (Φ z)) := by
    have h := (hComp K p hp U Φ hΦ).2.1 (innerSL ℂ ψ)
    exact (hAgree p hp U hU _).2 (by simpa using h)
  refine ⟨hfirst, ?_⟩
  have h := isCoordHolomorphicOn_conj_comp_conjPoint hfirst
  simpa [inner_conj_symm] using h
end YangMills.Construction.BanachValued.ConjugationInner
