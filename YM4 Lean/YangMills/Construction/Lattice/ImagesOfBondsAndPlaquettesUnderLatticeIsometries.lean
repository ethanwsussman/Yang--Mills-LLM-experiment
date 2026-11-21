import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def ElementaryPlaquette.cornerSet (p : ElementaryPlaquette a) : Set (LatticePoint a) :=
  {p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
    p.corner + axisStep a p.highAxis}
end InfiniteLattice
namespace PeriodicLattice
namespace TorusLatticeSymmetry
variable {L m K : ℕ} (s : TorusLatticeSymmetry L m K)
def IsBondImage (e e' : Bond L m (K : ℤ)) : Prop :=
  (e'.source, e'.target) = s.pairMap (e.source, e.target)
def bondMap (e : Bond L m (K : ℤ)) : Bond L m (K : ℤ) :=
  open Classical in
  if h : ∃ e', s.IsBondImage e e' then h.choose else e
theorem isBondImage_opposite {e e' : Bond L m (K : ℤ)} (h : s.IsBondImage e e') :
    s.IsBondImage e.opposite e'.opposite := by
  have h₁ : e'.source = s.pointMap e.source := congrArg Prod.fst h
  have h₂ : e'.target = s.pointMap e.target := congrArg Prod.snd h
  change (e'.target, e'.source) = (s.pointMap e.target, s.pointMap e.source)
  rw [h₁, h₂]
theorem isBondImage_unique {e e' e'' : Bond L m (K : ℤ)} (h : s.IsBondImage e e')
    (h' : s.IsBondImage e e'') : e' = e'' := by
  have h₀ : (e'.source, e'.target) = (e''.source, e''.target) := h.trans h'.symm
  exact Bond.ext (congrArg Prod.fst h₀) (congrArg Prod.snd h₀)
theorem bondMap_opposite (e : Bond L m (K : ℤ)) :
    s.bondMap e.opposite = (s.bondMap e).opposite := by
  classical
  by_cases h : ∃ e', s.IsBondImage e e'
  · have h' : ∃ e', s.IsBondImage e.opposite e' :=
      ⟨h.choose.opposite, s.isBondImage_opposite h.choose_spec⟩
    have q₁ : s.bondMap e = h.choose := dif_pos h
    have q₂ : s.bondMap e.opposite = h'.choose := dif_pos h'
    rw [q₁, q₂]
    exact s.isBondImage_unique h'.choose_spec (s.isBondImage_opposite h.choose_spec)
  · have h' : ¬∃ e', s.IsBondImage e.opposite e' := by
      rintro ⟨e', he⟩
      exact h ⟨e'.opposite, s.isBondImage_opposite he⟩
    have q₁ : s.bondMap e = e := dif_neg h
    have q₂ : s.bondMap e.opposite = e.opposite := dif_neg h'
    rw [q₁, q₂]
end TorusLatticeSymmetry
def SymmetriesPreserveBondsAndPlaquettes : Prop :=
  ∀ D : Conventions.StandingParameters,
    (∀ s : TorusLatticeSymmetry D.L D.m D.K,
      (∀ e : Bond D.L D.m ((D.K : ℕ) : ℤ), ∃ e' : Bond D.L D.m ((D.K : ℕ) : ℤ),
        (e'.source, e'.target) = s.pairMap (e.source, e.target)) ∧
      (∀ e : Bond D.L D.m ((D.K : ℕ) : ℤ), s.bondMap e.opposite = (s.bondMap e).opposite) ∧
      (∀ p : Plaquette D.L D.m ((D.K : ℕ) : ℤ), ∃! p' : Plaquette D.L D.m ((D.K : ℕ) : ℤ),
        p'.vertices = s.pointMap '' p.vertices)) ∧
    (∀ s : InfiniteLattice.LatticeSymmetry (meshSize D.L ((D.K : ℕ) : ℤ)),
      (∀ e : InfiniteLattice.Link (meshSize D.L ((D.K : ℕ) : ℤ)),
        ∃ e' : InfiniteLattice.Link (meshSize D.L ((D.K : ℕ) : ℤ)),
          (e'.initial, e'.terminal) = s.pairMap (e.initial, e.terminal)) ∧
      (∀ e : InfiniteLattice.Link (meshSize D.L ((D.K : ℕ) : ℤ)),
        s.linkMap e.opposite = (s.linkMap e).opposite) ∧
      (∀ p : InfiniteLattice.ElementaryPlaquette (meshSize D.L ((D.K : ℕ) : ℤ)),
        ∃! p' : InfiniteLattice.ElementaryPlaquette (meshSize D.L ((D.K : ℕ) : ℤ)),
          p'.cornerSet = s.pointMap '' p.cornerSet))
end PeriodicLattice
end YangMills.Construction
