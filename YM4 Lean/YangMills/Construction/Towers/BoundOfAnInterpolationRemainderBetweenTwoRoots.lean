import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import YangMills.Construction.Towers.TraceOfThreePropagators
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
def conjugateBy {I : PeriodicData} (p : Fin 4 → ℂ) (N T : JetQuad I I) : JetQuad I I :=
  mul p (mul p N T) N
structure InvertibleWithConjugate {I : PeriodicData} (p : Fin 4 → ℂ) (N T : JetQuad I I) (b : ℝ) :
    Prop where
  invertible : IsInvertibleJet stripHalfWidth p T
  conj_invertible : IsInvertibleJet stripHalfWidth p (conjugateBy p N T)
  conj_inv_norm_le : jetNorm stripHalfWidth p (invJet p (conjugateBy p N T)) ≤ ENNReal.ofReal b
structure RootInterpolationData {I J J' : PeriodicData} (p : Fin 4 → ℂ) (A W N M : JetQuad I I)
    (P : I.Carrier → I.Carrier → ℂ) (Q : JetQuad I J) (y : JetQuad J' I) (a b g : ℝ) : Prop where
  isJet_A : IsJet stripHalfWidth p A
  isJet_W : IsJet stripHalfWidth p W
  isJet_N : IsJet stripHalfWidth p N
  isJet_M : IsJet stripHalfWidth p M
  isJet_Q : IsJet stripHalfWidth p Q
  isJet_y : IsJet stripHalfWidth p y
  left_inv : EqAsJet stripHalfWidth p (mul p M N) (one I)
  transpose_self : EqAsJet stripHalfWidth p (transposeAt p N) N
  mul_self : EqAsJet stripHalfWidth p (mul p N N) (ofKernel I I P)
  kernel_norm_le : jetNorm stripHalfWidth p (ofKernel I I P) ≤ ENNReal.ofReal g
  x_norm_le : jetNorm stripHalfWidth p (mul p Q N) ≤ ENNReal.ofReal a
  y_norm_le : jetNorm stripHalfWidth p y ≤ ENNReal.ofReal a
  conj_decomp : EqAsJet stripHalfWidth p (conjugateBy p N W)
    ((mul p (transposeAt p (mul p Q N)) (mul p Q N)).add
      (smul (-1) (mul p y (transposeAt p y))))
  path : ∀ t ∈ Icc (0 : ℝ) 1, InvertibleWithConjugate p N (unitShiftedPath A W t) b
  shifted : ∀ τ ∈ Icc (0 : ℝ) 1, InvertibleWithConjugate p N (addScalarJet (A.add W) τ) b
def fiberDim (I : PeriodicData) : ℝ := Module.finrank ℂ (I.UnitQuot → ℂ)
def RemainderBoundClaim : Prop :=
  ∀ (I J J' : PeriodicData), IsPeriodic I → IsPeriodic J → IsPeriodic J' →
    ∀ (γ : ℝ) (P : I.Carrier → I.Carrier → ℂ), 0 ≤ γ → ResolventTrace.TraceBoundOn γ I P →
    ∀ (p : Fin 4 → ℂ) (A W N M : JetQuad I I) (Q : JetQuad I J) (y : JetQuad J' I) (a b g : ℝ),
      0 ≤ a → 0 ≤ b → 0 ≤ g → RootInterpolationData p A W N M P Q y a b g →
      ‖pathRemainder p A W‖ ≤
          (fiberDim J + fiberDim J') * a ^ 2 * b * (1 + g * b + g ^ 2 * b ^ 2) +
            γ * b ^ 3 ∧
        jetNorm stripHalfWidth p (mul p (mul p Q (invJet p (A.add W))) (transposeAt p Q)) ≤
          ENNReal.ofReal (a ^ 2 * b)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
end
