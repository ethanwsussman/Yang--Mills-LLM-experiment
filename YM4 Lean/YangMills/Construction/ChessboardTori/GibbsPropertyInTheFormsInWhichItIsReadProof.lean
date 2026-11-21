import YangMills.Construction.ChessboardTori.GibbsPropertyInTheFormsInWhichItIsRead
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice InfiniteLattice.GibbsEquivalences
namespace GibbsForms
theorem isBoundedObservable_const_one {a : ℝ} :
    IsBoundedObservable (fun _ : GaugeField a => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem tfae_isGibbs (hEquiv : GibbsEquivalenceStatement) (D : ChessboardSetup)
    (ν : Measure D.GaugeField) (hν : IsProbabilityMeasure ν) :
    List.TFAE [IsGibbs D.β ν, KernelCondExpInner D.mesh_pos D.β ν,
      KernelCondExp D.mesh_pos D.β ν, KernelInvariant D.mesh_pos D.β ν] := by
  obtain ⟨-, -, hs, -⟩ := hEquiv D.mesh D.β D.mesh_pos D.beta_pos
  obtain ⟨ht, hg⟩ := hs ν hν
  tfae_have 1 → 2 := fun h => (hg.1 h).2.1
  tfae_have 2 → 3 := (ht.out 1 2).1
  tfae_have 3 → 4 := (ht.out 2 3).1
  tfae_have 4 → 1 := fun h =>
    hg.2 ⟨(ht.out 3 0).1 h, (ht.out 3 1).1 h, (ht.out 3 2).1 h, h⟩
  tfae_finish
theorem proof (hEquiv : GibbsEquivalenceStatement) : Statement := by
  intro D
  refine ⟨tfae_isGibbs hEquiv D, ?_, ?_, rfl⟩
  · intro ν hν hG Λ hΛ A hA
    have hV : KernelCondExp D.mesh_pos D.β ν :=
      ((tfae_isGibbs hEquiv D ν hν).out 0 2).1 hG
    obtain ⟨-, -, hH⟩ := hV Λ hΛ A hA
    have h1 := hH (fun _ => (1 : ℂ)) isBoundedObservable_const_one measurable_const
    simp only [mul_one] at h1
    exact ⟨h1.symm, rfl⟩
  · ext ν
    constructor
    · rintro ⟨hG, hP⟩
      have hν : IsProbabilityMeasure ν := hG.1
      exact ⟨hν, ((tfae_isGibbs hEquiv D ν hν).out 0 1).1 hG, hP⟩
    · rintro ⟨hν, h1, hP⟩
      exact ⟨((tfae_isGibbs hEquiv D ν hν).out 1 0).1 h1, hP⟩
end GibbsForms
end YangMills.Construction.ChessboardTori
