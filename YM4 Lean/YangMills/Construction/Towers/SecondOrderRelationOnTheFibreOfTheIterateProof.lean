import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import YangMills.Construction.Towers.SecondOrderRelationOnTheFibreOfTheIterate
import YangMills.Construction.Towers.TheChainOfABlockField
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FibreSecondOrderRelationProof
section Expansion
variable {E F : Type*}
private theorem linear_add_bilinear_eq_zero_of_innerCore [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (core : InnerProductSpace.Core ℝ E)
    (N : E → ℝ) (hN : ∀ x, N x = Real.sqrt (core.inner x x))
    (l : E →ₗ[ℝ] F) (β : E →ₗ[ℝ] E →ₗ[ℝ] F) {X : ℝ → E} {B ξ : E} {C : ℝ} (hB : l B = 0)
    (hrem : (fun t : ℝ => N (X t - t • B - (t ^ 2 / 2) • ξ)) =o[𝓝 0] fun t : ℝ => t ^ 2)
    (hC : ∀ᶠ t in 𝓝 (0 : ℝ), ‖l (X t) + (1 / 2 : ℝ) • β (X t) (X t)‖ ≤ C * N (X t) ^ 3) :
    l ξ + β B B = 0 := by apply _root_.YangMills.Construction.Tower.FibreHessian.linear_add_quadratic_eq_zero_of_core <;> assumption
end Expansion
open YangMills.Construction.Matrices
theorem fibreSecondOrderRelation (hQ : IterLeftChartExpansion)
    (hC : BlockFieldChainProperties)
    (hT : ProlongCompositesAndVertexLayers.Statement)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hG : FiniteSideFormSpaces) :
    FibreSecondOrderRelation := by
  intro L n k hL hn hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨-, hfd, -, core, hcore⟩ := hG L n (i + 1) 0 hL hn (Nat.zero_le _)
  have hchain : ∀ᶠ W in 𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)),
      ChainOverBottom W :=
    Filter.Eventually.mono (hC L n (i + 1) hL hn hk hL0).1 fun W h => h.1
  have hcomp := (hT.1 L n (i + 1) hL hn hk).1
  have hzero : ∀ᶠ W in 𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)),
      chosenProlongIter L n (i + 1) (Nat.zero_le _) W =
        chosenProlongComp L n (i + 1) (i + 1) W := hcomp.comp_zero_eq
  have hbase : Tendsto (chainBottom (L := L) (m := n) (k := i + 1))
      (𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)))
      (𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2))) := by
    refine Tendsto.congr' ?_ (hcomp.tendsto 0 (Nat.zero_le _))
    filter_upwards [hchain, hzero] with W hW hz
    have h := (hW (i + 1) le_rfl).1
    rw [descendingChain_top] at h
    exact hz.trans h.symm
  have hexp := hbase.eventually (hQ L n (i + 1) hL hn hk)
  have hlin := hbase.eventually
    ((hY L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)).complexIterDeriv_isLinear
  show ∀ᶠ W in 𝓝[fieldSpace L n (i + 1) (i + 1)] (fun _ => (1 : ComplexMatrix2)), _
  filter_upwards [self_mem_nhdsWithin, hchain, hexp, hlin] with W hWc hW hE hTW
  intro X B ξ hB hX0 hrem hfib c
  obtain ⟨⟨-, hUreal, hnear, -⟩, -, -, hq, -⟩ := hE
  obtain ⟨T, hTeq⟩ := hTW
  obtain ⟨Cq, hCq⟩ := hq.2 c
  have hWU : smoothingIter L n (i + 1) (i + 1) (chainBottom W) = W := by
    have h := (hW (i + 1) le_rfl).2
    rw [descendingChain_top] at h
    exact h.symm
  have hWinv : W (c : Edge L n (i + 1) (i + 1)) * (W (c : Edge L n (i + 1) (i + 1)))⁻¹ = 1 := by
    have hu : W (c : Edge L n (i + 1) (i + 1)) ∈ PeriodicLattice.compactGaugeGroup :=
      hWc.1 _ (Set.mem_univ _)
    have : IsUnit (W (c : Edge L n (i + 1) (i + 1))).det := by
      have := hu.2
      simp_all
    exact Matrix.mul_nonsing_inv _ this
  have hlog1 : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
  have hvanish : ∀ᶠ t in 𝓝 (0 : ℝ), iterLogRatio (chainBottom W) c
      (X t : Edge L n (i + 1) 0 → ComplexMatrix2) = 0 := by
    filter_upwards [hX0.eventually hnear, hfib] with t ht hf
    obtain ⟨-, hreal, -⟩ := ht
    unfold iterLogRatio
    rw [hreal c, hf, hUreal c, hWU, hWinv, hlog1, smul_zero]
  let l : edgeFormSpace L n (i + 1) 0 →ₗ[ℝ] ComplexMatrix2 :=
    (LinearMap.proj (c : Edge L n (i + 1) (i + 1))) ∘ₗ
      (edgeFormSpace L n (i + 1) (i + 1)).subtype ∘ₗ T
  let β : edgeFormSpace L n (i + 1) 0 →ₗ[ℝ] edgeFormSpace L n (i + 1) 0 →ₗ[ℝ] ComplexMatrix2 :=
    (iterQuadraticTerm (chainBottom W)).compr₂ (LinearMap.proj c)
  have hl : ∀ A : edgeFormSpace L n (i + 1) 0, l A =
      complexIterDeriv L n (i + 1) (i + 1) (chainBottom W)
        (A : Edge L n (i + 1) 0 → ComplexMatrix2) c := fun A => congrFun (hTeq A) c
  have hN : ∀ A : edgeFormSpace L n (i + 1) 0, edgeFormNorm (A : Edge L n (i + 1) 0 → ComplexMatrix2) =
      Real.sqrt (core.inner A A) := fun A => by
    have h := hcore A A
    unfold edgeFormNorm traceFinsumNorm
    unfold edgeFormPairing at h
    rw [h, Complex.ofReal_re]
  have hrel := linear_add_bilinear_eq_zero_of_innerCore core
    (fun A : edgeFormSpace L n (i + 1) 0 => edgeFormNorm (A : Edge L n (i + 1) 0 → ComplexMatrix2)) hN l β
    (X := X) (B := B) (ξ := ξ) (C := Cq)
    (by rw [hl, hB]; rfl) hrem (by
      filter_upwards [hX0.eventually hCq, hvanish] with t ht hv
      rw [hv] at ht
      refine le_trans (le_of_eq ?_) ht
      rw [hl]
      rw [← norm_neg]
      congr 1
      show _ = _
      simp only [β, LinearMap.compr₂_apply, LinearMap.proj_apply]
      abel)
  rw [hl] at hrel
  exact eq_neg_of_add_eq_zero_left hrel
end YangMills.Construction.Tower.FibreSecondOrderRelationProof
end
