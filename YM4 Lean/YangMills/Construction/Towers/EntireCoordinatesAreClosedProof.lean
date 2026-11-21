import YangMills.Construction.Towers.EntireCoordinatesAreClosed
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open PeriodicOperators
open EntireDependence
theorem entireDependence_closed : EntireDependenceClosed := by
  intro F S
  refine ⟨fun c => ⟨fun _ => c, differentiable_const c, fun _ => rfl⟩, ?_, ?_, ?_⟩
  · intro κ hκ
    exact ⟨fun η => η ⟨κ, hκ⟩, differentiable_apply _, fun _ => rfl⟩
  · rintro g g' ⟨h, hh, hg⟩ ⟨h', hh', hg'⟩
    exact ⟨⟨fun η => h η + h' η, hh.add hh', fun ζ => congrArg₂ (· + ·) (hg ζ) (hg' ζ)⟩,
      ⟨fun η => h η * h' η, hh.mul hh', fun ζ => congrArg₂ (· * ·) (hg ζ) (hg' ζ)⟩⟩
  · rintro S' g hS ⟨h, hh, hg⟩
    refine ⟨fun η => h fun κ => η ⟨κ.1, hS κ.2⟩, hh.comp ?_, fun ζ => hg ζ⟩
    exact differentiable_pi.2 fun κ => differentiable_apply _
end YangMills.Construction.Tower.FullSpace
end
