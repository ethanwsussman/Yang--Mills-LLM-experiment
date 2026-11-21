import Mathlib
open Filter Set
open scoped Topology
namespace YangMills.ReferenceCalibration

/-- A positive fixed reference value and cold decay give a recurrent interval
of prescribed width for the terminal inverse coupling. -/
theorem fixed_window_of_positive_reference (p f : ℕ → ℝ) {c d H : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hfloor : ∀ j, H ≤ p j) (hfix : ∀ j, f j = c)
    (hcold : ∀ e : ℕ → ℕ, StrictMono e → Tendsto (p ∘ e) atTop atTop →
      Tendsto (f ∘ e) atTop (𝓝 0)) :
    ∃ Q, H ≤ Q ∧ ∃ᶠ j in atTop, p j ≤ Q ∧ Q < p j + d := by
  have hbounded : ∃ B : ℝ, ∃ᶠ j in atTop, p j ≤ B := by
    by_contra! hab
    have htop : Tendsto p atTop atTop := tendsto_atTop.2 fun b =>
      (hab b).mono fun j hj => hj.le
    have hzero := hcold id strictMono_id (by simpa using htop)
    have hconst : Tendsto (f ∘ id) atTop (𝓝 c) := by
      exact tendsto_const_nhds.congr fun j => (hfix (id j)).symm
    exact hc.ne' (tendsto_nhds_unique hconst hzero)
  obtain ⟨B, hB⟩ := hbounded
  have hI : ∃ᶠ j in atTop, p j ∈ Icc H B := hB.mono fun j hj => ⟨hfloor j, hj⟩
  obtain ⟨v, hv, e, he, hpe⟩ := isCompact_Icc.tendsto_subseq' hI
  refine ⟨v+d/2, by linarith [hv.1], ?_⟩
  apply he.tendsto_atTop.frequently
  apply Eventually.frequently
  filter_upwards [hpe.eventually (gt_mem_nhds (by linarith : v < v+d/2)),
    hpe.eventually (lt_mem_nhds (by linarith : v-d/2 < v))] with j hhi hlo
  change p (e j) < _ at hhi
  change _ < p (e j) at hlo
  exact ⟨hhi.le, by linarith⟩

end YangMills.ReferenceCalibration
