import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace PlaquetteCircuits
variable {L m : ℕ} {j : ℤ}
def meshVector (L : ℕ) (j : ℤ) (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ (meshSize L j)
def IsAlongAxis (e : Fin 4 → ℝ) (L : ℕ) (j : ℤ) (μ : Fin 4) : Prop :=
  e = meshVector L j μ ∨ e = -meshVector L j μ
def meshVectors (L : ℕ) (j : ℤ) : Set (Fin 4 → ℝ) := {e | ∃ μ, IsAlongAxis e L j μ}
instance instNegMeshVectors : Neg (meshVectors L j) where
  neg e := ⟨-e.1, by
    obtain ⟨μ, h | h⟩ := e.2
    · exact ⟨μ, Or.inr (by rw [h])⟩
    · exact ⟨μ, Or.inl (by rw [h, neg_neg])⟩⟩
def addVector (y : FourTorus L m) (ζ : Fin 4 → ℝ) : FourTorus L m :=
  y + TorusMetric.torusProj (torusSide L m) ζ
theorem torusProj_meshVector (μ : Fin 4) :
    TorusMetric.torusProj (torusSide L m) (meshVector L j μ) =
      (unitStep L m j μ : FourTorus L m) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [TorusMetric.torusProj, meshVector, unitStep, pointOnAxis]
  · simp [TorusMetric.torusProj, meshVector, unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem torusProj_neg (v : Fin 4 → ℝ) :
    TorusMetric.torusProj (torusSide L m) (-v) = -TorusMetric.torusProj (torusSide L m) v := by
  funext ν
  simp [TorusMetric.torusProj]
def meshVectorSite (e : meshVectors L j) : Site L m j :=
  ⟨TorusMetric.torusProj (torusSide L m) e.1, by
    obtain ⟨μ, h | h⟩ := e.2
    · rw [h, torusProj_meshVector]
      exact (unitStep L m j μ).2
    · rw [h, torusProj_neg, torusProj_meshVector]
      exact neg_mem (unitStep L m j μ).2⟩
def bondFrom (y : Site L m j) (e : meshVectors L j) : Bond L m j where
  source := y
  target := y + meshVectorSite e
  isNeighbour := by
    obtain ⟨μ, h | h⟩ := e.2
    · refine ⟨μ, Or.inl ?_⟩
      rw [add_sub_cancel_left]
      apply Subtype.ext
      change TorusMetric.torusProj (torusSide L m) e.1 = _
      rw [h, torusProj_meshVector]
    · refine ⟨μ, Or.inr ?_⟩
      rw [add_sub_cancel_left]
      apply Subtype.ext
      change TorusMetric.torusProj (torusSide L m) e.1 = _
      rw [h, torusProj_neg, torusProj_meshVector]
      rfl
def bondFromSegment (y : Site L m j) (e : meshVectors L j) : Set (FourTorus L m) :=
  {p | ∃ s ∈ Icc (0 : ℝ) 1, p = addVector (y : FourTorus L m) (s • e.1)}
def plaquetteSpannedBy (x : Site L m j) (μ ν : Fin 4) (h : μ ≠ ν) : Plaquette L m j :=
  if hl : μ < ν then ⟨x, μ, ν, hl⟩ else ⟨x, ν, μ, lt_of_le_of_ne (not_lt.mp hl) h.symm⟩
theorem barycenter_plaquetteSpannedBy (x : Site L m j) (μ ν : Fin 4) (h : μ ≠ ν) :
    (plaquetteSpannedBy x μ ν h).barycenter =
      addVector (addVector (x : FourTorus L m) ((1 / 2 : ℝ) • meshVector L j μ))
        ((1 / 2 : ℝ) • meshVector L j ν) := by
  have key : ∀ ρ : Fin 4, TorusMetric.torusProj (torusSide L m) ((1 / 2 : ℝ) • meshVector L j ρ) =
      pointOnAxis L m ρ (meshSize L j / 2) := by
    intro ρ
    funext σ
    by_cases hσ : σ = ρ
    · subst hσ
      simp [TorusMetric.torusProj, meshVector, pointOnAxis, div_eq_inv_mul]
    · simp [TorusMetric.torusProj, meshVector, pointOnAxis, Pi.single_eq_of_ne hσ]
  unfold plaquetteSpannedBy Plaquette.barycenter addVector
  rw [key, key]
  split_ifs with hl
  · rfl
  · exact add_right_comm _ _ _
def faceSpannedBy (x : Site L m j) (μ ν : Fin 4) : Set (FourTorus L m) :=
  {q | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
    q = addVector (x : FourTorus L m) (s • meshVector L j μ + t • meshVector L j ν)}
def IsFrame (p : Plaquette L m j) (e e' : meshVectors L j) : Prop :=
  (IsAlongAxis e.1 L j p.firstAxis ∧ IsAlongAxis e'.1 L j p.secondAxis) ∨
    (IsAlongAxis e.1 L j p.secondAxis ∧ IsAlongAxis e'.1 L j p.firstAxis)
def frameVertex (p : Plaquette L m j) (e e' : meshVectors L j) : FourTorus L m :=
  addVector (addVector p.barycenter (-((1 / 2 : ℝ) • e.1))) (-((1 / 2 : ℝ) • e'.1))
def circuitFrom (c : Site L m j) (e e' : meshVectors L j) : Fin 4 → Bond L m j :=
  ![bondFrom c e, bondFrom (c + meshVectorSite e) e',
    bondFrom (c + meshVectorSite e + meshVectorSite e') (-e), bondFrom (c + meshVectorSite e') (-e')]
def IsCircuit (p : Plaquette L m j) (γ : Fin 4 → Bond L m j) : Prop :=
  ∃ e e' : meshVectors L j, IsFrame p e e' ∧
    ∃ c : Site L m j, (c : FourTorus L m) = frameVertex p e e' ∧ γ = circuitFrom c e e'
end PlaquetteCircuits
end PeriodicLattice
end YangMills.Construction
