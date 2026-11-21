import YangMills.Construction.SpectralTheory.MatrixMeasuresAndCommutation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ResolvedOps
open HilbertSpaceBasics (UnboundedOp)
open BorelSpectral SpectralTheorem
open JointSpectral (dirac)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsDiagonalized (A : UnboundedOp H) : Prop :=
  ∃ E : SpectralMeasure RealLineSet H, IsSpectralMeasureFor E A
def expComplex (A : UnboundedOp H) (z : ℂ) : H →L[ℂ] H :=
  (spectralMeasure A).integralOp fun y =>
    (Ici (0 : ℝ)).indicator (fun x => Complex.exp (-z * (x : ℂ))) (y.1 0)
def StronglyCommute (A B : UnboundedOp H) : Prop :=
  SpectralMeasure.Commutes (spectralMeasure A) (spectralMeasure B)
variable {r : ℕ}
def boxSet (S : Fin r → BorelSubsets ℝ) : BorelSubsets (univ : Set (Fin r → ℝ)) :=
  ⟨{y | ∀ k, y.1 k ∈ (S k).1}, by
    have hS : {y : (univ : Set (Fin r → ℝ)) | ∀ k, y.1 k ∈ (S k).1} =
        ⋂ k, (fun y : (univ : Set (Fin r → ℝ)) => y.1 k) ⁻¹' (S k).1 := by
      ext y
      simp
    rw [hS]
    exact MeasurableSet.iInter fun k =>
      ((measurable_pi_apply k).comp measurable_subtype_coe) (S k).2⟩
def IsJointSpectralMeasure (A : Fin r → UnboundedOp H)
    (E : SpectralMeasure (univ : Set (Fin r → ℝ)) H) : Prop :=
  ∀ S : Fin r → BorelSubsets ℝ,
    E (boxSet S) = (List.ofFn fun k => spectralMeasure (A k) (realLineSet (S k))).prod
def jointSpectralMeasure (hr : 1 ≤ r) (A : Fin r → UnboundedOp H) :
    SpectralMeasure (univ : Set (Fin r → ℝ)) H :=
  haveI : Nonempty (SpectralMeasure (univ : Set (Fin r → ℝ)) H) :=
    ⟨dirac hr MeasurableSet.univ ⟨0, mem_univ _⟩⟩
  Classical.epsilon (IsJointSpectralMeasure A)
end YangMills.Construction.ResolvedOps
