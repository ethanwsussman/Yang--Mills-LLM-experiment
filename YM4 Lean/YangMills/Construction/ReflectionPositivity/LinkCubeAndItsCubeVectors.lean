import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint AmbientSpace axisStep shift
  closedHalfSpace)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def linkBlock (r : ℕ+) : Set AmbientSpace := {x | ∀ l, x l ∈ Icc (-(r : ℝ)) ((r : ℝ) - 1)}
def linkBlockVector (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) : ReflectionPair.link.Hilb ν μ :=
  ReflectionPair.link.obsClass ν μ ((shift ((r : ℕ) • axisStep 1 μ)).actOn A)
theorem coe_nsmul_axisStep_apply (r : ℕ+) (μ l : Fin 4) :
    (((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) l =
      if l = μ then (r : ℝ) else 0 := by
  by_cases hlμ : l = μ
  · subst hlμ
    simp [axisStep]
  · simp [axisStep, hlμ]
theorem imageSet_shift_linkBlock (r : ℕ+) (μ : Fin 4) :
    (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).setImage (linkBlock r) =
      {x | 0 ≤ x μ ∧ x μ ≤ 2 * (r : ℝ) - 1 ∧
        ∀ l, l ≠ μ → -(r : ℝ) ≤ x l ∧ x l ≤ (r : ℝ) - 1} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hcoord : ∀ l, (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).toFun y l =
        y l + if l = μ then (r : ℝ) else 0 := fun l => by
      rw [← coe_nsmul_axisStep_apply r μ l]
      rfl
    refine ⟨?_, ?_, fun l hl => ?_⟩
    · have := (hy μ).1
      rw [hcoord, if_pos rfl]
      linarith
    · have := (hy μ).2
      rw [hcoord, if_pos rfl]
      linarith
    · rw [hcoord, if_neg hl, add_zero]
      exact hy l
  · rintro ⟨hlow, hhigh, hrest⟩
    refine ⟨x - (((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace),
      fun l => ?_, ?_⟩
    · rw [Pi.sub_apply, coe_nsmul_axisStep_apply]
      by_cases hl : l = μ
      · subst hl
        rw [if_pos rfl]
        constructor <;> linarith
      · rw [if_neg hl, sub_zero]
        exact hrest l hl
    · exact sub_add_cancel _ _
theorem imageSet_shift_linkBlock_subset (r : ℕ+) (μ : Fin 4) :
    (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).setImage (linkBlock r) ⊆ closedHalfSpace μ := by
  rw [imageSet_shift_linkBlock]
  exact fun _ hx => hx.1
theorem isBounded_imageSet_shift_linkBlock (r : ℕ+) (μ : Fin 4) :
    Bornology.IsBounded ((shift ((r : ℕ) • axisStep (1 : ℝ) μ)).setImage (linkBlock r)) := by
  have hbdd : Bornology.IsBounded (linkBlock r) := by
    have hpi : linkBlock r = Set.pi univ fun _ => Icc (-(r : ℝ)) ((r : ℝ) - 1) := by
      ext x
      exact ⟨fun h l _ => h l, fun h l => h l (mem_univ l)⟩
    rw [hpi]
    exact Bornology.IsBounded.pi fun _ => Metric.isBounded_Icc _ _
  obtain ⟨C, hC⟩ := hbdd.subset_closedBall (0 : AmbientSpace)
  refine (Metric.isBounded_closedBall (x := (0 : AmbientSpace))
    (r := C + ‖(((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace)‖)).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have hnorm : ‖y‖ ≤ C := mem_closedBall_zero_iff.mp (hC hy)
  refine mem_closedBall_zero_iff.mpr ((norm_add_le y _).trans ?_)
  gcongr
end YangMills.Construction.ReflectionPositivity.DirectionPictures
