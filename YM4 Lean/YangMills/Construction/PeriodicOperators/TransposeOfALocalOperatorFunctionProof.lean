import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNormProof
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open TorusMetric (euclidNormVec)
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace OpFunTransposeLocal
theorem euclidNormVec_sub_comm (x y : InfiniteLattice.AmbientSpace) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem euclidNormVec_sub_le (x y w : InfiniteLattice.AmbientSpace) :
    euclidNormVec (x - w) ≤ euclidNormVec (x - y) + euclidNormVec (y - w) := by apply _root_.YangMills.Construction.LatticeCovering.euclidNormVec_sub_le_add <;> assumption
theorem isOpen_openPolydisk (n : ℕ) (r : ℝ) :
    IsOpen (openPolydisk (0 : ComplexCoordinates n) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem weightOf_translate {I : PeriodicData} (hI : IsPeriodic I) (n : Fin 4 → ℤ) (i : I.Carrier) :
    I.weightOf (I.translate n i) = I.weightOf i := by apply _root_.YangMills.Construction.PeriodicOperators.Quotients.weightOf_translate <;> assumption
section Restriction
variable {F : PeriodicData} {S S' : Set F.Carrier} {m m' : ℕ}
def restrictCoords (hS : S ⊆ S') (e : Fin m ≃ S) (e' : Fin m' ≃ S') :
    ComplexCoordinates m' → ComplexCoordinates m :=
  fun z j => z (e'.symm ⟨e j, hS (e j).2⟩)
theorem restrictCoords_fieldValues (hS : S ⊆ S') (e : Fin m ≃ S) (e' : Fin m' ≃ S')
    (ζ : F.Carrier → ℂ) : restrictCoords hS e e' (fieldValues e' ζ) = fieldValues e ζ := by
  funext j
  show ζ ((e' (e'.symm ⟨e j, hS (e j).2⟩) : S') : F.Carrier) = ζ (e j)
  rw [Equiv.apply_symm_apply]
theorem isHolomorphicIn_const_mul_restrictCoords
    (hAff : Matrices.GroupLieProduct.ExpChartHolomorphy.AffineHolomorphy)
    (hPS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hS : S ⊆ S') (e : Fin m ≃ S) (e' : Fin m' ≃ S') {g : ComplexCoordinates m → ℂ} {ρ : ℝ}
    (hg : ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk 0 ρ) (fun z _ => g z))
    (c : ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk 0 ρ)
      (fun z _ => c * g (restrictCoords hS e e' z)) := by
  have hRes : ComplexCoordinates.IsHolomorphicIn (openPolydisk (0 : ComplexCoordinates m') ρ)
      (restrictCoords hS e e') := by
    have haff := hAff m' m (fun j => MvPolynomial.X (e'.symm ⟨e j, hS (e j).2⟩))
      fun j => (MvPolynomial.totalDegree_X _).le
    have hfun : (fun (z : ComplexCoordinates m') (j : Fin m) =>
        MvPolynomial.eval z (MvPolynomial.X (e'.symm ⟨e j, hS (e j).2⟩))) =
        restrictCoords hS e e' := by
      funext z j
      simp only [MvPolynomial.eval_X]
      rfl
    rw [hfun] at haff
    exact ⟨isOpen_openPolydisk _ _, haff.2.1.mono (subset_univ _),
      fun x _ j => haff.2.2 x (mem_univ x) j⟩
  have hmaps : MapsTo (restrictCoords hS e e') (openPolydisk (0 : ComplexCoordinates m') ρ)
      (openPolydisk (0 : ComplexCoordinates m) ρ) := by
    intro z hz j
    have h1 : ‖z (e'.symm ⟨e j, hS (e j).2⟩) - (0 : ComplexCoordinates m') _‖ < ρ := hz _
    show ‖z (e'.symm ⟨e j, hS (e j).2⟩) - (0 : ComplexCoordinates m) j‖ < ρ
    simpa only [Pi.zero_apply, sub_zero] using h1
  have hcomp := ((hPS.1 m _ hg.1).1 1 _ hg).2.2.2.1 m' _ _ hRes hmaps
  obtain ⟨ho, hc, hd⟩ := hcomp
  refine ⟨ho, ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ => continuousOn_const.mul ?_
    exact (continuous_apply (0 : Fin 1)).comp_continuousOn hc
  · intro x hx j
    filter_upwards [hd x hx j] with w hw
    refine differentiableAt_pi.2 fun _ => (differentiableAt_const c).mul ?_
    exact (differentiableAt_pi.1 hw) 0
end Restriction
theorem isLocalWith_opFunTranspose
    (hAff : Matrices.GroupLieProduct.ExpChartHolomorphy.AffineHolomorphy)
    (hPS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {F I I' : PeriodicData} (hFin : ∀ (y : InfiniteLattice.AmbientSpace) (s : ℝ),
      (nearIndices F y s).Finite)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) :
    IsLocalWith F I' I (opFunTranspose T) ρ (2 * |R|) where
  radius_pos := hT.radius_pos
  vanish_far := by
    intro ζ hζ i j hfar
    have hR : R ≤ 2 * |R| := by linarith [le_abs_self R, abs_nonneg R]
    have h0 : T ζ j i = 0 := hT.vanish_far ζ hζ j i fun h => hfar (by
      rw [euclidNormVec_sub_comm]
      exact h.trans hR)
    show ((I'.weightOf j / I.weightOf i : ℝ) : ℂ) * T ζ j i = 0
    rw [h0, mul_zero]
  holo_entry := by
    intro i j
    have := (hFin (I.pos i) (2 * |R|)).to_subtype
    obtain ⟨m', ⟨e'⟩⟩ := Finite.exists_equiv_fin (nearIndices F (I.pos i) (2 * |R|))
    by_cases hnear : euclidNormVec (I.pos i - I'.pos j) ≤ R
    · obtain ⟨m, e, g, hg, hgT⟩ := hT.holo_entry j i
      have hS : nearIndices F (I'.pos j) R ⊆ nearIndices F (I.pos i) (2 * |R|) := by
        intro k hk
        have h1 : euclidNormVec (F.pos k - I'.pos j) ≤ R := hk
        have h2 := euclidNormVec_sub_le (F.pos k) (I'.pos j) (I.pos i)
        rw [euclidNormVec_sub_comm (I'.pos j)] at h2
        show euclidNormVec (F.pos k - I.pos i) ≤ 2 * |R|
        linarith [le_abs_self R]
      refine ⟨m', e'.symm, fun z => ((I'.weightOf j / I.weightOf i : ℝ) : ℂ) *
        g (restrictCoords hS e e'.symm z), ?_, ?_⟩
      · exact isHolomorphicIn_const_mul_restrictCoords hAff hPS hS e e'.symm hg _
      · intro ζ hζ
        show ((I'.weightOf j / I.weightOf i : ℝ) : ℂ) * T ζ j i = _
        rw [hgT ζ hζ]
        exact congrArg _ (congrArg g (restrictCoords_fieldValues hS e e'.symm ζ).symm)
    · refine ⟨m', e'.symm, fun _ => 0, ?_, ?_⟩
      · exact ⟨isOpen_openPolydisk _ _, continuousOn_const,
          fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
      · intro ζ hζ
        show ((I'.weightOf j / I.weightOf i : ℝ) : ℂ) * T ζ j i = 0
        rw [hT.vanish_far ζ hζ j i hnear, mul_zero]
  shift_covariant := by
    intro ζ hζ n i j
    show ((I'.weightOf (I'.translate n j) / I.weightOf (I.translate n i) : ℝ) : ℂ) *
        T (shiftField F n ζ) (I'.translate n j) (I.translate n i) =
      ((I'.weightOf j / I.weightOf i : ℝ) : ℂ) * T ζ j i
    rw [weightOf_translate hI, weightOf_translate hI', hT.shift_covariant ζ hζ n j i]
end OpFunTransposeLocal
theorem OpFunTransposeLocal.claim_holds
    (hKer : CovariantFiniteRange.Claim)
    (hExp : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hPS : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    OpFunTransposeLocal.Claim := by
  intro F I I' hF hI hI' T hT
  obtain ⟨ρ, R, hloc⟩ := hT
  exact ⟨ρ, 2 * |R|, OpFunTransposeLocal.isLocalWith_opFunTranspose hExp.1 hPS
    (hKer.1 F hF).1 hI hI' hloc⟩
end YangMills.Construction.PeriodicOperators
end
