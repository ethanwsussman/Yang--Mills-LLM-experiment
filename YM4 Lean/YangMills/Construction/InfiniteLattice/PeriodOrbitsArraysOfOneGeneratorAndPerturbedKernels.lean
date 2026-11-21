import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing
variable {a : ℝ}
theorem norm_eq_linfNorm (x : AmbientSpace) : ‖x‖ = linfNorm x := by
  have h0 : 0 ≤ linfNorm x :=
    (abs_nonneg (x 0)).trans (Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ (0 : Fin 4)))
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg h0).2 fun μ =>
      Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
  · exact Finset.sup'_le _ _ fun μ _ => norm_le_pi_norm x μ
section Orbits
variable (Γ : PeriodSublattice a)
def minPeriodNorm : ℝ :=
  sInf {s | ∃ γ ∈ Γ.periods, γ ≠ 0 ∧ s = linfNorm (γ : AmbientSpace)}
def pointOrbit (x : LatticePoint a) : Set (LatticePoint a) := {y | ∃ γ ∈ Γ.periods, y = x + γ}
theorem mem_pointOrbit_iff (x y : LatticePoint a) :
    y ∈ pointOrbit Γ x ↔ Γ.quotientMap y = Γ.quotientMap x := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact (QuotientAddGroup.eq.2 (by simpa using neg_mem hγ)).symm
  · intro h
    refine ⟨-x + y, QuotientAddGroup.eq.1 h.symm, by abel⟩
end Orbits
structure SingleGeneratorArray (a : ℝ) where
  sublattice : AddSubgroup (LatticePoint a)
  sublattice_finiteIndex : sublattice.FiniteIndex
  gen : GaugeField a → ℝ
  gen_mem : IsRealLocalContinuous gen
namespace SingleGeneratorArray
variable (A : SingleGeneratorArray a)
def translate (v : A.sublattice) : GaugeField a → ℝ :=
  (shift (v : LatticePoint a)).actOn A.gen
def supportIndices (ha : 0 < a) (L : Finset (Link a)) : Set A.sublattice :=
  {v | ∃ ℓ ∈ L, DependsOnLink ha (A.translate v) ℓ}
def tiltedEnergy (ha : 0 < a) (β t : ℝ) (L : Finset (Link a)) (U : GaugeField a) : ℝ :=
  wilsonLinkEnergy β L U - t * ∑ᶠ v ∈ A.supportIndices ha L, A.translate v U
def tiltedKernel (ha : 0 < a) (β t : ℝ) (L : Finset (Link a))
    (h : HasNoOppositePairs (L : Set (Link a))) (F : GaugeField a → ℂ)
    (U : GaugeField a) : ℂ :=
  linkKernel L h (A.tiltedEnergy ha β t L) F U
theorem tiltedEnergy_zero (ha : 0 < a) (β : ℝ) (L : Finset (Link a)) :
    A.tiltedEnergy ha β 0 L = wilsonLinkEnergy β L := by
  funext U
  simp [tiltedEnergy]
theorem tiltedKernel_zero (ha : 0 < a) (β : ℝ) (L : Finset (Link a))
    (h : HasNoOppositePairs (L : Set (Link a))) :
    A.tiltedKernel ha β 0 L h = wilsonLinkKernel β L h := by
  funext F U
  simp only [tiltedKernel, wilsonLinkKernel, A.tiltedEnergy_zero ha β L]
def IsTiltedGibbsState (ha : 0 < a) (β t : ℝ)
    (ν : Measure (GaugeField a)) : Prop :=
  IsProbabilityMeasure ν ∧
    ∀ (L : Finset (Link a)) (h : HasNoOppositePairs (L : Set (Link a))),
      ∀ F ∈ continuousLocal a,
        ∫ U, A.tiltedKernel ha β t L h F U ∂ν = ∫ U, F U ∂ν
end SingleGeneratorArray
end GibbsAtFixedSpacing
end YangMills.Construction
end
