import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.WilsonWeightAsASlabIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.SlabDecompositionOfWilsonWeight
variable {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
theorem slabSliceIndex_zero_injective :
    Function.Injective fun k : ZMod (m : ℕ) => T.slabSliceIndex m k 0 := by
  intro k k' h
  simp only [TransferSetup.slabSliceIndex, add_zero] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  have hr : (T.ratioNat : ℤ) ≠ 0 := by
    have := T.two_le_ratioNat
    omega
  have hd : (((m : ℕ) : ℕ) : ℤ) ∣ (k'.cast : ℤ) - (k.cast : ℤ) := by
    refine ⟨c, mul_right_cancel₀ hr ?_⟩
    push_cast at hc
    linarith
  have hk := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd
  simpa using hk
theorem exp_neg_beta_wilsonAction_eq_prod (hP : T.FacesOfSlices m) (hC : T.CrossingFaces m)
    (hV : T.SlabDecompositionProperties m) (hW : T.SlabBoltzmannWeights m)
    (U : (T.torusPeriods m).GaugeConfig) :
    Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ)) =
      (∏ k : ZMod (m : ℕ), T.slabBoltzmann m (fun _ => 0) k (T.slabRestriction m k U)) *
        ∏ k : ZMod (m : ℕ), ∏ b : T.PositiveTransverseEdge,
          TransferSetup.boltzmannFactor D
            (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
              (T.sliceField m U (T.slabSliceIndex m k 1))
              (T.axialField m U (T.slabSliceIndex m k 0)) b) := by
  classical
  have hfin : Finite (T.torusPeriods m).Face := by
    have : Finite ((T.SliceLabel m × T.TransverseFace) ⊕ (T.SliceLabel m × T.PositiveTransverseEdge)) :=
      inferInstance
    exact Finite.of_surjective _ hP.1.2
  let _ : Fintype (T.torusPeriods m).Face := Fintype.ofFinite _
  let f : (T.torusPeriods m).Face → ℂ := fun p =>
    Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).faceEnergy U p : ℂ))
  have hA : (((T.torusPeriods m).wilsonAction U : ℝ) : ℂ) =
      ∑ p, (((T.torusPeriods m).faceEnergy U p : ℝ) : ℂ) := by
    have h : (T.torusPeriods m).wilsonAction U = ∑ p, (T.torusPeriods m).faceEnergy U p :=
      finsum_eq_sum_of_fintype _
    rw [h]
    push_cast
    rfl
  have hexp : Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ)) = ∏ p, f p := by
    rw [hA, Finset.mul_sum, Complex.exp_sum]
  have hin : ∀ k : ZMod (m : ℕ), T.slabBoltzmann m (fun _ => 0) k (T.slabRestriction m k U) =
      ∏ p ∈ Finset.univ.filter (T.IsInSlab m k), f p := by
    intro k
    rw [((hW (fun _ => 0) ⟨0, by simp⟩).1 k).2.2 U]
    simp only [zero_sub]
    exact finprod_cond_eq_prod_of_cond_iff _ (by simp)
  have hcross : ∏ p ∈ Finset.univ.filter (T.IsCrossingFace m), f p =
      ∏ k : ZMod (m : ℕ), ∏ b : T.PositiveTransverseEdge,
        f (T.axialFace m (T.slabSliceIndex m k 0) b) := by
    rw [← Fintype.prod_prod_type']
    symm
    refine Finset.prod_bij (fun x _ => T.axialFace m (T.slabSliceIndex m x.1 0) x.2)
      (fun x _ => ?_) (fun x _ y _ hxy => ?_) (fun p hp => ?_) (fun _ _ => rfl)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC.2.1 _).mpr ⟨x.1, x.2, rfl⟩⟩
    · have h := hP.1.1 (a₁ := .inr (T.slabSliceIndex m x.1 0, x.2))
        (a₂ := .inr (T.slabSliceIndex m y.1 0, y.2)) hxy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Sum.inr.inj h)
      exact Prod.ext (slabSliceIndex_zero_injective T m h1) h2
    · obtain ⟨k, b, rfl⟩ := (hC.2.1 p).mp (Finset.mem_filter.mp hp).2
      exact ⟨(k, b), Finset.mem_univ _, rfl⟩
  have hunion : Finset.univ.filter (fun p => ¬ T.IsCrossingFace m p) =
      Finset.univ.biUnion fun k : ZMod (m : ℕ) => Finset.univ.filter (T.IsInSlab m k) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hp
      rcases hC.1 p with ⟨k, hk, -⟩ | h
      · exact ⟨k, hk⟩
      · exact absurd h hp
    · rintro ⟨k, hk⟩ h
      exact h k hk
  have hdisj : ((Finset.univ : Finset (ZMod (m : ℕ))) : Set (ZMod (m : ℕ))).PairwiseDisjoint
      fun k => Finset.univ.filter (T.IsInSlab m k) := by
    intro k _ k' _ hkk
    refine Finset.disjoint_left.mpr fun p hp hp' => hkk ?_
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hp').2
    rcases hC.1 p with hu | h
    · exact hu.unique h1 h2
    · exact absurd h1 (h k)
  rw [hexp, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (T.IsCrossingFace m) f, hcross,
    hunion, Finset.prod_biUnion hdisj, mul_comm]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => (hin k).symm) ?_
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun b _ => (hV.2.2 U k b).symm
theorem statement_of_transferAssertions (hAssert : TransferAssertions.Statement) : Statement := by
  intro D T m Ψ
  obtain ⟨-, -, -, hP, hC, -, hV, -, hW⟩ := hAssert D T m
  unfold TransferSetup.slabProductIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [exp_neg_beta_wilsonAction_eq_prod T m hP hC hV hW U, Pi.mul_apply, Finset.prod_mul_distrib]
  ring
end YangMills.Construction.ChessboardTori.SlabDecompositionOfWilsonWeight
end
