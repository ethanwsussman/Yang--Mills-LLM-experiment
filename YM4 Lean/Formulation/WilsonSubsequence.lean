import Formulation.FixedObservableContinuum
import Formulation.WilsonOSProof
import Formulation.WilsonVolume

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace YangMills
open Wilson

/-- The SU(2) continuum limit on four-space, with the bare coupling selected by
the smallest positive solution of the fixed two-point reference equation. -/
theorem su2_wilson_subsequence : Wilson.ContinuumLimitFor (specialUnitary 2) := by
  apply continuum_matrix_iff_quaternion.mpr
  unfold Wilson.ContinuumLimitFor
  obtain ⟨L₀, main⟩ := su2_fixed_observable_continuum_limit
  refine ⟨max L₀ 13, fun L ho hL => ?_⟩
  have h₁₃ : 13 ≤ (L:ℕ) := (le_max_right ..).trans hL
  have h₂ : 2 ≤ (L:ℕ) := by omega
  have ha : Construction.Conventions.IsAdmissibleBlockingFactor L := ⟨ho,h₁₃⟩
  obtain ⟨M, δ, hside, hδ, roots, hmain⟩ := main L ho ((le_max_left ..).trans hL)
  refine ⟨M, δ, hside, hδ, ?_, ?_⟩
  · filter_upwards [roots, eventually_ge_atTop 1] with k hk hk₁
    intro g₀ hg
    let K : ℕ+ := ⟨k,hk₁⟩
    change IsLeast (couplingsAt su2Model L M K g₀) (bareCoupling su2Model L M K g₀)
    rw [Wilson.couplingsAt_eq ha M K, Wilson.bareCoupling_eq ha M K]
    exact hk g₀ hg
  intro g₀ hg g
  obtain ⟨K, m, ν, C, X₂, X₄, hK, hroot, haf, hν, hm, _, _, hmom,
    hsmooth, hpos, hsm₄, hpos₄, ⟨D,T,hD,hT,hgrowth,hE,hOS,hperm,hreal,hC⟩,
    ⟨A, Dc, hDc, hA, hcomp, hng⟩⟩ := hmain g₀ hg
  let β (j : ℕ) := (renormalizedBareCoupling L M (K j) g₀ ^ 2)⁻¹
  have hβ j : 0 < β j := inv_pos.mpr (sq_pos_of_pos (hroot j).1.1)
  have heq (j : ℕ) : g (K j) = renormalizedBareCoupling L M (K j) g₀ :=
    Wilson.bareCoupling_eq ha M (K j) g₀
  choose v hv hvol using fun j => Wilson.volume_moments_at_state ha (K j) (hβ j) (hν j)
  refine ⟨K,m,v,WilsonOS.ofFlatSequence T,hK,hm,hv,?_,?_,?_,
    WilsonOS.axioms_of_schwinger hD hT hgrowth hE hOS hperm hreal,
    WilsonOS.decomposition_of_components hT hA hDc hcomp hng, ?_, ?_⟩
  · intro j
    rw [Wilson.couplingsAt_eq ha M (K j), heq]
    exact hroot j
  · have hcoeff : 24 * Real.pi^2 / (11 * su2Model.adjointCasimir) = 3 * Real.pi^2 / 11 := by
      change 24 * Real.pi^2 / (11 * 8) = 3 * Real.pi^2 / 11
      ring
    simpa only [heq, hcoeff] using haf
  · intro n f hf
    let X : Construction.TestSpaces.SepTupleOfCard n :=
      ⟨f, fun i => ⟨(hf.1 i).1.of_le (by norm_num), (hf.1 i).2, Set.subset_univ _⟩, hf.2⟩
    change ∃ z : ℕ → ℂ, _ ∧ _ ∧ _
    refine ⟨fun j => Construction.InfiniteLattice.centeredMoment (ν j) f, ?_, ?_, ?_⟩
    · intro j
      simpa only [heq] using hvol j n X
    · rw [show f = X.1 from rfl, WilsonOS.tensor_evaluation hT X (fun i => (hf.1 i).1)]
      exact (hmom n X).1
    · rw [show f = X.1 from rfl, WilsonOS.tensor_evaluation hT X (fun i => (hf.1 i).1)]
      apply ((hmom n X).2).congr
      intro j
      rw [heq, Wilson.centeredMoment_eq _ h₂ (m j).pos X]
  · refine ⟨X₂.1, ⟨fun i => ⟨hsmooth i, (X₂.2.1 i).2.1⟩,X₂.2.2⟩,?_⟩
    rw [WilsonOS.tensor_evaluation hT X₂ hsmooth, Construction.TestSpaces.RecursionTriangular.centredOfCumulants_pair]
    exact hpos
  · refine ⟨X₄.1, ⟨fun i => ⟨hsm₄ i, (X₄.2.1 i).2.1⟩, X₄.2.2⟩, ?_⟩
    rw [WilsonOS.connected_value hT X₄ hsm₄, hC]
    exact hpos₄

/-- The Wilson continuum limit for the gauge group chosen in the challenge. -/
theorem wilson_subsequence : Wilson.ContinuumLimitFor selectedGauge :=
  su2_wilson_subsequence

end YangMills
end
