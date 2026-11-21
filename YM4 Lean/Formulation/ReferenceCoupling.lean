import Formulation.ReferenceCorrelations
import Formulation.FixedReferenceBump
import Formulation.GibbsCalibration

/-! Least positive bare couplings for one reference two-point observable on a common subsequence of SU(2) Wilson cutoffs. -/

noncomputable section
open Filter Set
open scoped Topology

namespace YangMills.Formulation

/-- The smallest positive bare coupling at which the fixed observable reaches the given level.
The observable takes inverse temperature as its argument. -/
def leastBareAt (F : ℝ → ℝ) (r : ℝ) : ℝ := sInf {g : ℝ | 0 < g ∧ F (g ^ 2)⁻¹ = r}

theorem leastBareAt_of_trial {F : ℝ → ℝ} {β r : ℝ} (hβ : 0 < β) (hr : 0 < r)
    (hcross : r ≤ F β) (hf : ContinuousOn F (Ioi 0)) (hz : Tendsto F atTop (𝓝 0)) :
    IsLeast {g : ℝ | 0 < g ∧ F (g ^ 2)⁻¹ = r} (leastBareAt F r) ∧
      leastBareAt F r ≤ (Real.sqrt β)⁻¹ := by
  have hid : (((Real.sqrt β)⁻¹) ^ 2)⁻¹ = β := by rw [inv_pow, inv_inv, Real.sq_sqrt hβ.le]
  apply isLeast_positive_level_of_le hr (inv_pos.mpr (Real.sqrt_pos.2 hβ))
  · rw [hid]; exact hcross
  · refine hf.comp (continuousOn_id.pow 2 |>.inv₀ ?_) ?_
    · intro x hx; exact pow_ne_zero _ (ne_of_gt hx)
    · intro x hx; exact inv_pos.mpr (pow_pos (show 0 < x from hx) 2)
  · apply hz.comp
    simpa [Function.comp_def, inv_pow] using (tendsto_pow_atTop (n := 2) (by decide)).comp
      (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))

/-- A common sequence of trial inverse temperatures above a fixed positive observable level
gives true smallest roots at every smaller level on the same tail.  The one-sided running
coupling bound is uniform in the level. -/
theorem cofinal_least_bare {ι : Type*} {l : Filter ι} (F : ι → ℝ → ℝ) (β w : ι → ℝ)
    {ρ A : ℝ} (continuousF : ∀ j, ContinuousOn (F j) (Ioi 0))
    (cold : ∀ j, Tendsto (F j) atTop (𝓝 0))
    (trial : ∀ᶠ j in l, ρ ≤ F j (β j)) (hotIndex : Tendsto β l atTop)
    (hw : ∀ᶠ j in l, 0 ≤ w j) (slope : Tendsto (fun j => w j / β j) l (𝓝 A)) :
    (∀ᶠ j in l, ∀ r ∈ Ioo (0 : ℝ) ρ,
      IsLeast {g : ℝ | 0 < g ∧ F j (g ^ 2)⁻¹ = r} (leastBareAt (F j) r) ∧
        leastBareAt (F j) r ≤ (Real.sqrt (β j))⁻¹) ∧
    (∀ ε > 0, ∀ᶠ j in l, ∀ r ∈ Ioo (0 : ℝ) ρ,
      0 < leastBareAt (F j) r ∧ leastBareAt (F j) r < ε ∧
      (leastBareAt (F j) r) ^ 2 * w j < A + ε) ∧
    ∀ r ∈ Ioo (0 : ℝ) ρ, Tendsto (fun j => leastBareAt (F j) r) l (𝓝 0) := by
  have minimum : ∀ᶠ j in l, ∀ r ∈ Ioo (0 : ℝ) ρ,
      IsLeast {g : ℝ | 0 < g ∧ F j (g ^ 2)⁻¹ = r} (leastBareAt (F j) r) ∧
        leastBareAt (F j) r ≤ (Real.sqrt (β j))⁻¹ := by
    filter_upwards [trial, hotIndex.eventually_gt_atTop 0] with j hj hb
    intro r hr
    exact leastBareAt_of_trial hb hr.1 (hr.2.le.trans hj) (continuousF j) (cold j)
  have shrinks : Tendsto (fun j => (Real.sqrt (β j))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hotIndex)
  refine ⟨minimum, ?_, ?_⟩
  · intro ε hε
    filter_upwards [minimum, hw, shrinks.eventually_lt_const hε, hotIndex.eventually_gt_atTop 0,
      slope.eventually_lt_const (lt_add_of_pos_right A hε)] with j hj hjw hεj hβ hsl
    intro r hr
    obtain ⟨hm, hu⟩ := hj r hr
    have hg := hm.1.1
    refine ⟨hg, hu.trans_lt hεj, lt_of_le_of_lt ?_ hsl⟩
    calc
      (leastBareAt (F j) r) ^ 2 * w j ≤ (Real.sqrt (β j))⁻¹ ^ 2 * w j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg.le hu 2) hjw
      _ = w j / β j := by rw [inv_pow, Real.sq_sqrt hβ.le, div_eq_mul_inv, mul_comm]
  · intro r hr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds shrinks
      (minimum.mono fun j hj => (hj r hr).1.1.1.le) (minimum.mono fun j hj => (hj r hr).2)

end YangMills.Formulation
end

noncomputable section
open Filter Set
open scoped Topology
namespace YangMills

open Construction Construction.PeriodicLattice Formulation

/-- Connected two-point function of the fixed bump and its three-unit translate. -/
def referenceResponse (L M K : ℕ) (β : ℝ) : ℝ :=
  (SchwingerFunctions.connectedSchwinger L M K β (fixedReferenceTests L M)).re

/-- On a single fixed torus, a common increasing cutoff sequence works for all sufficiently
small target values. Its least bare couplings vanish and obey the one-sided one-loop bound. -/
theorem su2_least_bare_subsequence :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
      ∃ (M : ℕ+) (K : ℕ → ℕ+) (ρ : ℝ),
        8 ≤ torusSide L M ∧ StrictMono K ∧ 0 < ρ ∧
        (∀ j, ∀ r ∈ Ioo (0 : ℝ) ρ,
          IsLeast {g : ℝ | 0 < g ∧ referenceResponse L M (K j) (g ^ 2)⁻¹ = r}
            (leastBareAt (referenceResponse L M (K j)) r)) ∧
        (∀ r ∈ Ioo (0 : ℝ) ρ,
          Tendsto (fun j => leastBareAt (referenceResponse L M (K j)) r) atTop (𝓝 0)) ∧
        ∀ ε > 0, ∀ᶠ j in atTop, ∀ r ∈ Ioo (0 : ℝ) ρ,
          (leastBareAt (referenceResponse L M (K j)) r) ^ 2 * (K j : ℝ) * Real.log L <
            3 * Real.pi ^ 2 / 11 + ε := by
  obtain ⟨Lstar, orig⟩ := su2_reference_subsequence
  refine ⟨max Lstar 13, ?_⟩
  intro L hodd hL
  have h13 : 13 ≤ L := (le_max_right Lstar 13).trans hL
  obtain ⟨m, k, β, ρ, hm, hk, hβpos, hβ, hrun, hρ, hobs⟩ :=
    orig L hodd ((le_max_left _ _).trans hL)
  have hmpos : 0 < m := by
    by_contra! hn
    have : m = 0 := Nat.eq_zero_of_le_zero hn
    norm_num [this, torusSide] at hm
  let M : ℕ+ := ⟨m, hmpos⟩
  let s : Conventions.StandingParameters := ⟨L, ⟨hodd,h13⟩, 1, M⟩
  have hsucc : Tendsto Nat.succPNat atTop atTop := tendsto_atTop.2 fun n =>
    Filter.eventually_atTop.2 ⟨(n : ℕ), fun j hj => by change (n : ℕ) ≤ j + 1; omega⟩
  obtain ⟨ψ, hψ, hkψ⟩ := strictMono_subseq_of_tendsto_atTop (hk.comp hsucc)
  let f : ℕ → ℕ+ := Nat.succPNat ∘ ψ
  have hf : Tendsto f atTop atTop := hsucc.comp hψ.tendsto_atTop
  have htail := hf.eventually ((hk.eventually_ge_atTop 1).and hobs)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (show ∀ᶠ i in atTop, 1 ≤ k (f i) ∧
      ρ < referenceResponse L m (k (f i)) (β (f i)) from htail)
  let I (j : ℕ) := f (j + N)
  have hI : Tendsto I atTop atTop := hf.comp (tendsto_atTop_mono (fun j : ℕ => Nat.le_add_right j N) tendsto_id)
  have hh j : 1 ≤ k (I j) ∧ ρ < referenceResponse L m (k (I j)) (β (I j)) :=
    hN (j + N) (Nat.le_add_left N j)
  let K (j : ℕ) : ℕ+ := ⟨k (I j), (hh j).1⟩
  have hK : StrictMono K := fun i j hij =>
    (show k (f (i+N)) < k (f (j+N)) from hkψ (Nat.add_lt_add_right hij N))
  let F (j : ℕ) := referenceResponse L M (K j)
  have compare (j : ℕ) {b : ℝ} (hb : 0 < b) :
      F j b = ReferenceCalibration.energyCovariance s (K j) (fixedReferenceTests L M) b :=
    ReferenceCalibration.reference_covariance_eq s (K j) (fixedReferenceTests L M) hb
  have cont (j : ℕ) : ContinuousOn (F j) (Ioi 0) :=
    (ReferenceCalibration.covariance_continuous s (K j) (fixedReferenceTests L M)).continuousOn.congr
      (fun _ hx => compare j hx)
  have cold (j : ℕ) : Tendsto (F j) atTop (𝓝 0) :=
    (ReferenceCalibration.covariance_cold s (K j) (fixedReferenceTests L M)).congr'
      ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx => (compare j hx).symm)
  let w (j : ℕ) : ℝ := (K j : ℝ) * Real.log L
  have hwinv : Tendsto (fun j => w j / β (I j)) atTop (𝓝 (3 * Real.pi ^ 2 / 11)) := by
    have hi := (hrun.comp hI).inv₀ (by positivity)
    convert hi using 1 <;> simp [w, K, inv_div]
  have hw (j : ℕ) : 0 ≤ w j := mul_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega)))
  obtain ⟨minim, small, zero⟩ := cofinal_least_bare F (fun j => β (I j)) w cont cold
    (Eventually.of_forall fun j => (hh j).2.le) (hβ.comp hI) (Eventually.of_forall hw) hwinv
  -- The fixed witnesses already cross the threshold at every selected index.
  have minimum (j : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) ρ) :
      IsLeast {g : ℝ | 0 < g ∧ F j (g ^ 2)⁻¹ = r} (leastBareAt (F j) r) := by
    exact (leastBareAt_of_trial (hβpos (I j)) hr.1 (hr.2.le.trans (hh j).2.le) (cont j) (cold j)).1
  refine ⟨M, K, ρ, hm, hK, hρ, fun j r hr => minimum j hr, zero, ?_⟩
  intro ε hε
  filter_upwards [small ε hε] with j hj r hr
  simpa only [w, mul_assoc] using (hj r hr).2.2

end YangMills
end

noncomputable section
open Filter Set
open scoped Topology
namespace YangMills

open Construction Construction.PeriodicLattice Formulation

def renormalizedBareCoupling (L M K : ℕ) (g₀ : ℝ) : ℝ :=
  leastBareAt (referenceResponse L M K) (fixedPhysicalLevel g₀)

/-- For one fixed smooth bump and its three-unit translate, the smallest positive solution
exists at every cutoff of a common sequence for every sufficiently small physical coupling.
These bare couplings tend to zero with a uniform one-loop upper bound. -/
theorem su2_fixed_observable_coupling :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (M : ℕ+) (K : ℕ → ℕ+) (δ : ℝ),
      8 ≤ torusSide L M ∧ StrictMono K ∧ 0 < δ ∧
      (∀ g₀ ∈ Ioo (0 : ℝ) δ,
        (∀ j, IsLeast {g : ℝ | 0 < g ∧ referenceResponse L M (K j) (g ^ 2)⁻¹ = fixedPhysicalLevel g₀}
           (renormalizedBareCoupling L M (K j) g₀)) ∧
        Tendsto (fun j => renormalizedBareCoupling L M (K j) g₀) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ j in atTop, ∀ g₀ ∈ Ioo (0 : ℝ) δ,
        (renormalizedBareCoupling L M (K j) g₀) ^ 2 * (K j : ℝ) * Real.log L <
          3 * Real.pi ^ 2 / 11 + ε := by
  obtain ⟨L₀, h⟩ := su2_least_bare_subsequence
  refine ⟨L₀, ?_⟩
  intro L hodd hL
  obtain ⟨M, K, ρ, hM, hK, hρ, hm, hz, hupper⟩ := h L hodd hL
  obtain ⟨δ, hδ, hsmall⟩ := fixedPhysicalLevel_small hρ
  refine ⟨M, K, δ, hM, hK, hδ, ?_, ?_⟩
  · intro g₀ h₀
    exact ⟨fun j => hm j _ (hsmall g₀ h₀), hz _ (hsmall g₀ h₀)⟩
  · intro ε hε
    exact (hupper ε hε).mono fun j hj g₀ h₀ => hj _ (hsmall g₀ h₀)

end YangMills
end
