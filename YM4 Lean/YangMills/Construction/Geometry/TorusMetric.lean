import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusMetric
abbrev Torus4 (S : ℝ) : Type := Fin 4 → AddCircle S
def torusProj (S : ℝ) (v : Fin 4 → ℝ) : Torus4 S := fun μ => (v μ : AddCircle S)
def supNormVec (v : Fin 4 → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |v μ|
def l1NormVec (v : Fin 4 → ℝ) : ℝ := ∑ μ, |v μ|
def euclidNormVec (v : Fin 4 → ℝ) : ℝ := Real.sqrt (∑ μ, v μ ^ 2)
variable {S : ℝ}
def torusSupNorm (x : Torus4 S) : ℝ := sInf (supNormVec '' (torusProj S ⁻¹' {x}))
def torusL1Norm (x : Torus4 S) : ℝ := sInf (l1NormVec '' (torusProj S ⁻¹' {x}))
def torusEuclidNorm (x : Torus4 S) : ℝ := sInf (euclidNormVec '' (torusProj S ⁻¹' {x}))
def setSupDist (A B : Set (Torus4 S)) : ℝ≥0∞ :=
  ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (torusSupNorm (a - b))
def setEuclidDist (A B : Set (Torus4 S)) : ℝ≥0∞ :=
  ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (torusEuclidNorm (a - b))
structure LiftedSegment where
  tail : Fin 4 → ℝ
  head : Fin 4 → ℝ
def LiftedSegment.displacement (s : LiftedSegment) : Fin 4 → ℝ := s.head - s.tail
def LiftedSegment.pointAt (S : ℝ) (s : LiftedSegment) (u : ℝ) : Torus4 S :=
  torusProj S (s.tail + u • s.displacement)
def LiftedSegment.support (S : ℝ) (s : LiftedSegment) : Set (Torus4 S) := s.pointAt S '' Icc 0 1
def segmentsSupport (S : ℝ) (Γ : List LiftedSegment) : Set (Torus4 S) := ⋃ s ∈ Γ, s.support S
def pathLength (Γ : List LiftedSegment) : ℝ := (Γ.map fun s => l1NormVec s.displacement).sum
def pathLengthIn (S : ℝ) (Γ : List LiftedSegment) (A : Set (Torus4 S)) : ℝ :=
  (Γ.map fun s => l1NormVec s.displacement * (volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A)).toReal).sum
def IsTreeGraph (S : ℝ) (Γ : List LiftedSegment) : Prop := IsConnected (segmentsSupport S Γ)
theorem exists_coe_eq_abs_eq_norm (y : AddCircle S) : ∃ v : ℝ, (v : AddCircle S) = y ∧ |v| = ‖y‖ := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨a - round (S⁻¹ * a) * S, ?_, ?_⟩
  · have hround : ((round (S⁻¹ * a) * S : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round (S⁻¹ * a), by simp⟩
    rw [AddCircle.coe_sub, hround, sub_zero]
  · exact (AddCircle.norm_eq S).symm
theorem addCircle_norm_coe_le_abs (v : ℝ) : ‖(v : AddCircle S)‖ ≤ |v| := by
  simpa using QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples S) (m := v)
theorem torusL1Norm_eq_sum_norm (x : Torus4 S) : torusL1Norm x = ∑ μ, ‖x μ‖ := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S b = x := funext hb
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hproj, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · simp [l1NormVec, hb']
  · refine le_csInf ⟨_, b, hproj, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj S v = x := hv
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [← hv']
    exact addCircle_norm_coe_le_abs _
end TorusMetric
end YangMills.Construction
