import YangMills.Construction.Continuum.ModesAreCutoffsTimesCharacters
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff Matrix
namespace YangMills.Construction.ConfigSpace
open Bumps
theorem abs_le_supCoord (x : Fin 4 → ℝ) (j : Fin 4) : |x j| ≤ EuclideanCoords.supCoord x :=
  le_ciSup (f := fun ι => |x ι|) (Set.finite_range _).bddAbove j
theorem supCoord_le {x : Fin 4 → ℝ} {r : ℝ} (h : ∀ j, |x j| ≤ r) : EuclideanCoords.supCoord x ≤ r :=
  ciSup_le h
theorem modesAreLocalCharacters_of_gevreyBumpBounds (hbump : GevreyBumpBounds) :
    ModesAreLocalCharacters := by
  obtain ⟨-, -, -, -, ⟨hsmooth, -, -, hone, hsupp, -⟩, -⟩ := hbump
  intro n _ Q i ξ _
  have hs : 0 < Q.scale := Q.scale_pos
  have hBoxCpt : IsCompact (Set.pi univ fun j : Fin 4 =>
      Icc (Q.base i j - Q.scale) (Q.base i j + Q.scale)) :=
    isCompact_univ_pi fun j => isCompact_Icc
  have hBoxSub : (Set.pi univ fun j : Fin 4 =>
      Icc (Q.base i j - Q.scale) (Q.base i j + Q.scale)) ⊆ Q.outerBox i := by
    intro y hy
    show EuclideanCoords.supCoord (y - Q.base i) ≤ 2 * Q.scale / 2
    refine supCoord_le fun j => ?_
    have hj := hy j (mem_univ j)
    rw [Pi.sub_apply, abs_le]
    constructor <;> linarith [hj.1, hj.2]
  have hSupp : tsupport (Q.modeFun i ξ) ⊆ (Set.pi univ fun j : Fin 4 =>
      Icc (Q.base i j - Q.scale) (Q.base i j + Q.scale)) := by
    refine closure_minimal ?_ hBoxCpt.isClosed
    intro y hy
    by_contra hyBox
    apply hy
    have hoff : Q.scale⁻¹ • (y - Q.base i) ∉ tsupport cubeBump := by
      intro h
      apply hyBox
      intro j _
      have hj := hsupp h j (mem_univ j)
      have h1 : -1 ≤ Q.scale⁻¹ * (y j - Q.base i j) := hj.1
      have h2 : Q.scale⁻¹ * (y j - Q.base i j) ≤ 1 := hj.2
      have h3 := (le_inv_mul_iff₀ hs).1 h1
      have h4 := (inv_mul_le_iff₀ hs).1 h2
      constructor <;> linarith
    simp only [PointSystem.modeFun]
    rw [image_eq_zero_of_notMem_tsupport hoff]
    simp
  have hSmooth : ContDiff ℝ ∞ (Q.modeFun i ξ) := by
    have hAff : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => Q.scale⁻¹ • (y - Q.base i) :=
      (contDiff_id.sub contDiff_const).const_smul Q.scale⁻¹
    have hCut : ContDiff ℝ ∞ fun y : Fin 4 → ℝ =>
        ((cubeBump (Q.scale⁻¹ • (y - Q.base i)) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (ContDiff.comp hsmooth hAff)
    have hDot : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => ξ i ⬝ᵥ (y - Q.base i) := by
      unfold dotProduct
      refine ContDiff.sum fun j _ => contDiff_const.mul ?_
      exact (contDiff_apply ℝ ℝ j).sub contDiff_const
    have hChar : ContDiff ℝ ∞ fun y : Fin 4 → ℝ =>
        Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ) : ℂ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hDot)).cexp
    exact hCut.mul hChar
  refine ⟨⟨hSmooth, hBoxCpt.of_isClosed_subset (isClosed_tsupport _) hSupp⟩, hSupp.trans hBoxSub, ?_⟩
  intro y hy
  have hy' : EuclideanCoords.supCoord (y - Q.base i) ≤ 3 / 2 * Q.scale / 2 := hy
  have hInner : ∀ c, (Q.scale⁻¹ • (y - Q.base i)) c ∈ Icc (-(3 / 4) : ℝ) (3 / 4) := by
    intro c
    have hc := abs_le.1 ((abs_le_supCoord (y - Q.base i) c).trans hy')
    have h1 : y c - Q.base i c ≤ 3 / 2 * Q.scale / 2 := hc.2
    have h2 : -(3 / 2 * Q.scale / 2) ≤ y c - Q.base i c := hc.1
    show Q.scale⁻¹ * (y c - Q.base i c) ∈ Icc (-(3 / 4) : ℝ) (3 / 4)
    constructor
    · rw [le_inv_mul_iff₀ hs]
      linarith
    · rw [inv_mul_le_iff₀ hs]
      linarith
  simp only [PointSystem.modeFun]
  rw [hone _ hInner]
  simp
end YangMills.Construction.ConfigSpace
