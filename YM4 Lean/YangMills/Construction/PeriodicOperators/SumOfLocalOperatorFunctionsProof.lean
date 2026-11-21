import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace OpFunAdd
theorem isHolomorphicIn_add {m : ℕ} {U : Set (YangMills.Construction.Coordinates.ComplexCoordinates m)}
    {u v : YangMills.Construction.Coordinates.ComplexCoordinates m → ℂ}
    (hu : YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U
      fun w _ => u w)
    (hv : YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U
      fun w _ => v w) :
    YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U
      fun w _ => u w + v w := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.add <;> assumption
variable {P Q Q' : PeriodicData}
def reindex {A : Set P.Carrier} {m m' : ℕ} (σ : Fin m ≃ A) (σ' : Fin m' ≃ A)
    (w : YangMills.Construction.Coordinates.ComplexCoordinates m) :
    YangMills.Construction.Coordinates.ComplexCoordinates m' :=
  fun k => w (σ.symm (σ' k))
theorem reindex_fieldValues {A : Set P.Carrier} {m m' : ℕ} (σ : Fin m ≃ A) (σ' : Fin m' ≃ A)
    (φ : P.Carrier → ℂ) : reindex σ σ' (fieldValues σ φ) = fieldValues σ' φ := by
  funext k
  show φ ((σ (σ.symm (σ' k)) : A) : P.Carrier) = φ (σ' k)
  rw [Equiv.apply_symm_apply]
theorem isLocalWith_add
    (hAff : YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy.AffineHolomorphy)
    (hPow : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {A B : (P.Carrier → ℂ) → Q'.Carrier → Q.Carrier → ℂ} {r L : ℝ}
    (hA : IsLocalWith P Q Q' A r L) (hB : IsLocalWith P Q Q' B r L) :
    IsLocalWith P Q Q' (opFunAdd A B) r L where
  radius_pos := hA.radius_pos
  vanish_far := fun φ hφ x' x hx => by
    show A φ x' x + B φ x' x = 0
    rw [hA.vanish_far φ hφ x' x hx, hB.vanish_far φ hφ x' x hx, add_zero]
  shift_covariant := fun φ hφ t x' x => by
    show A (shiftField P t φ) (Q'.translate t x') (Q.translate t x) +
        B (shiftField P t φ) (Q'.translate t x') (Q.translate t x) = A φ x' x + B φ x' x
    rw [hA.shift_covariant φ hφ, hB.shift_covariant φ hφ]
  holo_entry := by
    intro x' x
    obtain ⟨m, σ, u, hu, hAu⟩ := hA.holo_entry x' x
    obtain ⟨m', σ', v, hv, hBv⟩ := hB.holo_entry x' x
    have hReix : YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn
        (openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) r)
        (reindex σ σ') := by
      have hlin := hAff m m' (fun k => MvPolynomial.X (σ.symm (σ' k)))
        fun k => (MvPolynomial.totalDegree_X _).le
      have heq : (fun (w : YangMills.Construction.Coordinates.ComplexCoordinates m) (k : Fin m') =>
          MvPolynomial.eval w (MvPolynomial.X (σ.symm (σ' k)))) = reindex σ σ' := by
        funext w k
        simp only [MvPolynomial.eval_X]
        rfl
      rw [heq] at hlin
      exact ⟨hu.1, hlin.2.1.mono (subset_univ _), fun a _ k => hlin.2.2 a (mem_univ a) k⟩
    have hinto : MapsTo (reindex σ σ')
        (openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) r)
        (openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates m') r) := by
      intro w hw k
      have hk : ‖w (σ.symm (σ' k)) -
          (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) _‖ < r := hw _
      show ‖w (σ.symm (σ' k)) - (0 : YangMills.Construction.Coordinates.ComplexCoordinates m') k‖ < r
      simpa only [Pi.zero_apply, sub_zero] using hk
    have hcomp : YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
        (openPolydisk (0 : YangMills.Construction.Coordinates.ComplexCoordinates m) r)
        fun w _ => v (reindex σ σ' w) :=
      ((hPow.1 m' _ hv.1).1 1 _ hv).2.2.2.1 m _ _ hReix hinto
    refine ⟨m, σ, fun w => u w + v (reindex σ σ' w), isHolomorphicIn_add hu hcomp, ?_⟩
    intro φ hφ
    show A φ x' x + B φ x' x = u (fieldValues σ φ) + v (reindex σ σ' (fieldValues σ φ))
    rw [hAu φ hφ, hBv φ hφ, reindex_fieldValues]
end OpFunAdd
theorem OpFunAdd.localClosed_holds
    (hPar : ParameterIndependence.Claim)
    (hExp : YangMills.Construction.Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hPow : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    OpFunAdd.LocalClosed := by
  rintro P Q Q' hP hQ hQ' A B ⟨r, L, hA⟩ ⟨r', L', hB⟩
  have hr := lt_min hA.radius_pos hB.radius_pos
  have hA₂ := (hPar P Q Q' hP hQ hQ' A r L r L hA hA).1.1 (min r r') (max L L') hr
    (min_le_left _ _) (le_max_left _ _)
  have hB₂ := (hPar P Q Q' hP hQ hQ' B r' L' r' L' hB hB).1.1 (min r r') (max L L') hr
    (min_le_right _ _) (le_max_right _ _)
  exact ⟨_, _, OpFunAdd.isLocalWith_add hExp.1 hPow hA₂ hB₂⟩
end YangMills.Construction.PeriodicOperators
end
