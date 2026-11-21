import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ResponseInTheExpansion.IsometriesCarryTheScores
import YangMills.Construction.ResponseInTheExpansion.ResponseIntegralIsCarried
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields WeightedResponses BlockAverages LumpContours
namespace BlockResponseIntegralInvariance
variable {n : ℕ}
private theorem axisSign_mul_cancel (g : TorusIsometry) (i : Fin 4) {a b : ZMod n}
    (h : (g.axisSign i : ZMod n) * a = (g.axisSign i : ZMod n) * b) : a = b := by
  rcases g.axisSign_unit i with hs | hs
  · simpa [hs] using h
  · simpa [hs] using h
private theorem mapSite_injective (g : TorusIsometry) :
    Function.Injective (g.mapSite : TorusSite n → TorusSite n) := by
  intro x x' h
  funext q
  have h1 := congrFun h (g.axisPerm.symm q)
  simp only [TorusIsometry.mapSite, add_left_inj] at h1
  have h2 := axisSign_mul_cancel g _ h1
  simpa using h2
abbrev _root_.YangMills.SharedProofs.p54677 := @mapSite_injective
private theorem transports_injective [NeZero n] (g : TorusIsometry) {W₁ W₂ W' : TorusField n}
    (h₁ : g.Transports W₁ W') (h₂ : g.Transports W₂ W') : W₁ = W₂ := by
  funext x k
  have a := h₁ x k
  have b := h₂ x k
  split_ifs at a b
  · rw [← a, ← b]
  · rw [← a, ← b]
private theorem sum_responseMass_block_image {R : StepSetup} (A : ResponseSetup R) [NeZero n]
    (hA : A.IsAdmissible) (hblock : IsBlockTorusSide R.params (n * R.params.side)) (g : TorusIsometry)
    (hparent : ∀ z : TorusSite (n * R.params.side),
      parentBlock R.params.side ((g.scaledLift R.params.side).mapSite z) = g.mapSite (parentBlock R.params.side z))
    (y : TorusSite n) (W W' : TorusField (n * R.params.side)) (hW : (g.scaledLift R.params.side).Transports W W') :
    ∑ z ∈ sitesInBlocks R.params.side {g.mapSite y},
        responseMass R.params R.depth R.coupling R.labels R.labelWeight A.hull (n * R.params.side) z W' =
      ∑ z ∈ sitesInBlocks R.params.side {y},
        responseMass R.params R.depth R.coupling R.labels R.labelWeight A.hull (n * R.params.side) z W := by
  classical
  have hinj : Function.Injective
      ((g.scaledLift R.params.side).mapSite : TorusSite (n * R.params.side) → TorusSite (n * R.params.side)) :=
    mapSite_injective _
  have hbij : Function.Bijective
      ((g.scaledLift R.params.side).mapSite : TorusSite (n * R.params.side) → TorusSite (n * R.params.side)) :=
    Finite.injective_iff_bijective.mp hinj
  have hmem : ∀ z, z ∈ sitesInBlocks R.params.side ({y} : Finset (TorusSite n)) ↔
      parentBlock R.params.side z = y := by
    intro z
    simp [sitesInBlocks]
  have hmem' : ∀ z, z ∈ sitesInBlocks R.params.side ({g.mapSite y} : Finset (TorusSite n)) ↔
      parentBlock R.params.side z = g.mapSite y := by
    intro z
    simp [sitesInBlocks]
  refine (Finset.sum_bij (fun z _ => (g.scaledLift R.params.side).mapSite z) ?_
    (fun _ _ _ _ e => hinj e) ?_ ?_).symm
  · intro z hz
    rw [hmem'] at *
    rw [hparent, (hmem z).mp hz]
  · intro z' hz'
    obtain ⟨z, rfl⟩ := hbij.2 z'
    refine ⟨z, (hmem z).mpr (mapSite_injective g ?_), rfl⟩
    rw [← hparent]
    exact (hmem' _).mp hz'
  · intro z _
    exact (hA.bounds.mass_carried (n * R.params.side) hblock (g.scaledLift R.params.side) z W W' hW).symm
theorem blockResponseIntegral_isometry_invariant (hH : FieldHaar.HaarInvariantUnderSymmetries)
    (hI : WeightedResponses.isometriesPreserveScoresStatement) :
    ResponseInTheExpansion.blockResponseIntegralIsometryInvariantStatement := by
  intro R A hR hA n _ hn g y V V' hV
  have hadm := hR.admissible
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.params.side)
  have hnL : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Nat.dvd_mul_left _ _, by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hn⟩
  obtain ⟨hparent, e, he⟩ := hI R hadm n hn g
  obtain ⟨Ψ, hΨ, hc⟩ := (hH (n * R.params.side)).2 (g.scaledLift R.params.side)
  have hinj : Function.Injective Ψ := fun W₁ W₂ h =>
    transports_injective _ (hc W₁) (h ▸ hc W₂)
  haveI : SecondCountableTopology UnitQuaternion := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : CompleteSpace UnitQuaternion := complete_of_compact
  haveI : PolishSpace UnitQuaternion := inferInstance
  have hemb : MeasurableEmbedding Ψ := hΨ.measurable.measurableEmbedding hinj
  unfold blockResponseIntegral
  rw [← hΨ.integral_comp hemb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show fieldBlockResponse A V' (g.mapSite y) (Ψ W) = fieldBlockResponse A V y W
  unfold fieldBlockResponse
  refine (Fintype.sum_equiv e _ _ fun b => ?_).symm
  obtain ⟨h1, h2⟩ := he W (Ψ W) V V' (hc W) hV b
  rw [h1, sum_responseMass_block_image A hA hblock g hparent y W (Ψ W) (hc W),
    (hR.functional_spec (n * R.params.side) hnL).2.2.2 _ W (Ψ W) (hc W)]
  by_cases hb : baseLaw (R := R) W b = 0
  · simp [hb]
  · rw [h2 hb y]
end BlockResponseIntegralInvariance
end YangMills.Construction.ResponseInTheExpansion
end
