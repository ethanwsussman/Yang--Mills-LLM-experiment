import YangMills.Construction.OneLoopLaw.MotionsOfTheUnitLatticeOfATorus
import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries
variable {L n : ℕ}
abbrev tangentPushforward (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (B : PeriodicOperators.Tempered.UnitEdge L n → Matrices.ComplexMatrix2) :
    PeriodicOperators.Tempered.UnitEdge L n → Matrices.ComplexMatrix2 :=
  Tower.isometryOnTangent (k := 0) (j := 0) f (PeriodicOperators.Tempered.identityField L n) B
def phaseSite (L n : ℕ) (a : Fin 3) (p : InfiniteLattice.AmbientSpace) :
    Tower.Vertex L n 0 0 → Matrices.ComplexMatrix2 :=
  fun x => PeriodicOperators.Tempered.phase p (x : PeriodicLattice.FourTorus L n) •
    Matrices.ComplexMatrix2.pauliFamily a
def flipCoord (ρ : Fin 4) (p : InfiniteLattice.AmbientSpace) : InfiniteLattice.AmbientSpace :=
  Function.update p ρ (-p ρ)
structure PlaneWaveLaws (L n : ℕ) : Prop where
  mem_complex : ∀ (a : Fin 3) (μ : Fin 4), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
    PeriodicOperators.Tempered.fourierModeForm L n a p μ ∈ Tower.complexEdgeForms L n 0 0
  periodic : ∀ (a : Fin 3) (μ : Fin 4), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
    ∀ e : Fin 4 → ℤ,
    PeriodicOperators.Tempered.fourierModeForm L n a
        (p + (2 * Real.pi) • PeriodicOperators.castVec e) μ =
      PeriodicOperators.Tempered.fourierModeForm L n a p μ
  shift : ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) (m : Fin 4 → ℤ),
    Tower.IsDistancePreserving f → Tower.MapsSublatticeOnto 0 0 f →
    UnitLatticeMotions.IsInducedByMotion f 1 m →
    ∀ (a : Fin 3) (μ : Fin 4), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
      tangentPushforward f (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
        Complex.exp (-(Complex.I * PeriodicOperators.bilinDot (PeriodicOperators.toComplexVec p)
          (PeriodicOperators.toComplexVec (PeriodicOperators.castVec m)))) •
          PeriodicOperators.Tempered.fourierModeForm L n a p μ
  permute : ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (σ : Equiv.Perm (Fin 4)),
    Tower.IsDistancePreserving f → Tower.MapsSublatticeOnto 0 0 f →
    UnitLatticeMotions.IsInducedByMotion f (UnitLatticeMotions.permMatrix σ) 0 →
    ∀ (a : Fin 3) (μ : Fin 4), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
      tangentPushforward f (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
        PeriodicOperators.Tempered.fourierModeForm L n a (p ∘ σ.symm) (σ μ)
  reflect_off_axis : ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (ρ : Fin 4),
    Tower.IsDistancePreserving f → Tower.MapsSublatticeOnto 0 0 f →
    UnitLatticeMotions.IsInducedByMotion f (UnitLatticeMotions.axisReflectionMatrix ρ) 0 →
    ∀ (a : Fin 3) (μ : Fin 4), μ ≠ ρ → ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
      tangentPushforward f (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
        PeriodicOperators.Tempered.fourierModeForm L n a (flipCoord ρ p) μ
  reflect_on_axis : ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (ρ : Fin 4),
    Tower.IsDistancePreserving f → Tower.MapsSublatticeOnto 0 0 f →
    UnitLatticeMotions.IsInducedByMotion f (UnitLatticeMotions.axisReflectionMatrix ρ) 0 →
    ∀ (a : Fin 3), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
      tangentPushforward f (PeriodicOperators.Tempered.fourierModeForm L n a p ρ) =
        (-Complex.exp (-(Complex.I * (p ρ : ℂ)))) •
          PeriodicOperators.Tempered.fourierModeForm L n a (flipCoord ρ p) ρ
  phaseSite_traceless : ∀ (a : Fin 3), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ x,
    phaseSite L n a p x ∈ Matrices.ComplexMatrix2.traceless
  covDiff_phaseSite : ∀ (a : Fin 3), ∀ p ∈ PeriodicOperators.dualLattice (2 * L ^ n),
    Tower.covDiff (k := 0) (j := 0) (PeriodicOperators.Tempered.identityField L n)
        (phaseSite L n a p) =
      ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) •
        PeriodicOperators.Tempered.fourierModeForm L n a p μ
def PlaneWaveLawsHold : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → PlaneWaveLaws L n
end YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries
end
