import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import YangMills.Construction.RunningCouplingSlope.CellCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.RootsReadOnASide
import YangMills.Construction.Towers.TheRootsOfTheFreePropagatorsOnTheStrip
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.LocalKernels.Periodisation (periodSide)
private theorem exists_matrix_of_periodization {L n k : ℕ} {I : PeriodicData} {ι : Type}
    {q : I.Carrier → ι} {c : ι → Vertex L n k k} (hq : IsCellQuotient L n k I q c)
    (hI : IsPeriodic I) (hPer : PeriodicOperators.Periodized.Claim) (hs : 0 < periodSide L n)
    (T : I.Carrier → I.Carrier → ℂ) (hT : IsPeriodicKernel I I T) :
    ∃ M : ι → ι → ℂ, ∀ i' i, M (q i') (q i) = periodization I I T (periodSide L n) i' i := by
  obtain ⟨-, C₁, δ, hC₁, hδ, hb⟩ := id hT
  have facts := hPer I I hI hI T δ hT ⟨hδ, C₁, hC₁, hb⟩
  let l := Function.surjInv hq.surjective
  refine ⟨fun u v => periodization I I T (periodSide L n) (l u) (l v), fun i' i => ?_⟩
  have cl : ∀ i, I.mkQuot (periodSide L n) (l (q i)) = I.mkQuot (periodSide L n) i := by
    intro i
    obtain ⟨m, hm⟩ := (hq.image_eq_iff i (l (q i))).1 (Function.surjInv_eq hq.surjective (q i)).symm
    rw [hm]
    exact (Quot.sound ⟨m, rfl⟩ : I.mkQuot (periodSide L n) i = _).symm
  exact facts.depends_quot _ hs _ _ _ _ (cl i') (cl i)
theorem resolventRootsPeriodize_holds (hR : CellQuotientsOfTower)
    (hFree : Tower.ResolventRootsOnStrip.ResolventRootsHold)
    (hPer : PeriodicOperators.Periodized.Claim)
    (hSets : PeriodicOperators.TowerIndexSets.Claim) : ResolventRootsPeriodize := by
  intro L n k hL hn hk
  have hL0 : 0 < L := by have := hL.2; omega
  have hs : 0 < periodSide L n := by
    simp only [periodSide]
    positivity
  obtain ⟨hsite, hbond, -, -, -⟩ := hR L n k hL hn
  obtain ⟨fb, fs⟩ := hFree L hL k hk
  obtain ⟨hS0, hB0, -⟩ := hSets L hL k 0 (Nat.zero_le _)
  obtain ⟨Mb, hMb⟩ := exists_matrix_of_periodization hbond hB0 hPer hs _ fb.sqrt_periodic
  obtain ⟨Ms, hMs⟩ := exists_matrix_of_periodization hsite hS0 hPer hs _ fs.sqrt_periodic
  exact ⟨Classical.epsilon_spec (p := IsEdgePeriodization L n k (Tower.FreeResolvents.edgeResolventSqrt L k))
      ⟨Mb, hMb⟩,
    Classical.epsilon_spec (p := IsVertexPeriodization L n k (Tower.FreeResolvents.vertexResolventSqrt L k))
      ⟨Ms, hMs⟩⟩
end YangMills.Construction.RunningCouplingSlope
end
