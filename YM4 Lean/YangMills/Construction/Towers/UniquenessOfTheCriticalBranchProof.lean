import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import YangMills.Construction.Towers.UniquenessOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace CriticalBranchUniqueness
variable {L m k : ℕ}
theorem exists_isOpen_of_isOpenFieldSet (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj : j ≤ k)
    {𝒰 : Set (Edge L m k j → Matrices.ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    ∃ O, IsOpen O ∧ 𝒰 = O ∩ fieldSpace L m k j :=
  (((hE L hL k j hj).1 m hm).2.2.2.2.2.2.2.2.1 𝒰 h.1).2 h.2
theorem tendsto_prolong (hE : BondSetFields.ProductStructureHolds)
    (hP : AnalyticMapsAlongCurves) (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {b : CriticalBranchData L m k} (hb : b.IsCritical) {i : ℕ} (hi : i < k) :
    Tendsto (b.prolong i)
      (𝓝[fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)))
      (𝓝[fieldSpace L m k i] (fun _ => (1 : Matrices.ComplexMatrix2))) := by
  obtain ⟨𝒰, h1, h2⟩ := hb.analytic_prolong i hi
  have hc := ((hP L m k (i + 1) i hL hm hi hi.le).1 𝒰 (b.prolong i) h2).1
  obtain ⟨O, hO, rfl⟩ := exists_isOpen_of_isOpenFieldSet hE hL hm (Nat.succ_le_of_lt hi) h1.1
  have hnear : O ∩ fieldSpace L m k (i + 1) ∈
      𝓝[fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)) :=
    mem_nhdsWithin.2 ⟨O, hO, h1.2.1, fun _ hW => hW⟩
  have heq : 𝓝[O ∩ fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)) =
      𝓝[fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)) :=
    le_antisymm (nhdsWithin_mono _ inter_subset_right) (nhdsWithin_le_of_mem hnear)
  have ht := (hc _ h1.2).tendsto
  rw [hb.prolong_trivial i hi, heq] at ht
  exact tendsto_nhdsWithin_iff.2 ⟨ht, eventually_of_mem hnear fun W hW => h2.2.1 hW⟩
theorem prolong_eq_of_energy_eq (hE : BondSetFields.ProductStructureHolds)
    (hP : AnalyticMapsAlongCurves) (hN : FibreNeighbourhoodsOfSteps)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {b c : CriticalBranchData L m k}
    (hb : b.IsCritical) {i : ℕ} (hi : i < k) {𝒰 : Set (Edge L m k i → Matrices.ComplexMatrix2)}
    (hU : c.IsFibreNhd i 𝒰)
    (hF : EventuallyNearIdentity (fieldSpace L m k i) fun V => b.energy i V = c.energy i V) :
    EventuallyNearIdentity (fieldSpace L m k (i + 1)) fun W => b.prolong i W = c.prolong i W := by
  obtain ⟨hcrit, -, hloc, -⟩ := hN
  have hR := hloc L m k i
  obtain ⟨𝒰b, h11, -, 𝒪, -, h13⟩ := hb.fibre_structure i hi
  obtain ⟨Ob, hOb, hObeq⟩ := exists_isOpen_of_isOpenFieldSet hE hL hm hi.le h11.1
  obtain ⟨Oc, hOc, hOceq⟩ :=
    exists_isOpen_of_isOpenFieldSet hE hL hm hi.le hU.isOpenNhd.1
  obtain ⟨Of, hOf, h1f, hOfsub⟩ := mem_nhdsWithin.1 hF
  have h1b : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ Ob := by
    have h := h11.2
    rw [hObeq] at h
    exact h.1
  have h1c : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ Oc := by
    have h := hU.isOpenNhd.2
    rw [hOceq] at h
    exact h.1
  let Ω : Set (Edge L m k i → Matrices.ComplexMatrix2) := Of ∩ Ob ∩ Oc
  have hΩ : IsOpen Ω := (hOf.inter hOb).inter hOc
  have h1Ω : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ Ω := ⟨⟨h1f, h1b⟩, h1c⟩
  have hlim := tendsto_prolong hE hP hL hm hb hi
  have hnearΩ : ∀ᶠ W in 𝓝[fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)),
      b.prolong i W ∈ Ω :=
    hlim.eventually (mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds h1Ω))
  have hnearconf : ∀ᶠ W in 𝓝[fieldSpace L m k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)),
      b.prolong i W ∈ fieldSpace L m k i :=
    hlim.eventually self_mem_nhdsWithin
  filter_upwards [h13, hU.unique_critical, hb.prolong_section i hi, hnearΩ, hnearconf]
    with W hWb hWc hWs hWΩ hWconf
  obtain ⟨⟨-, hxcrit, -⟩, -⟩ := hWb
  obtain ⟨⟨-, -, huniq⟩, -⟩ := hWc
  have hxU : b.prolong i W ∈ CriticalBranchData.levelFibre 𝒰 W :=
    ⟨by rw [hOceq]; exact ⟨hWΩ.2, hWconf⟩, hWs.1⟩
  let M : Set (Edge L m k i → Matrices.ComplexMatrix2) := Ω ∩ CriticalBranchData.levelFibre 𝒰b W
  have hMb : Matrices.ComplexMatrix2.IsRelativelyOpen (CriticalBranchData.levelFibre 𝒰b W) M :=
    ⟨Ω, hΩ, rfl⟩
  have hMc : Matrices.ComplexMatrix2.IsRelativelyOpen (CriticalBranchData.levelFibre 𝒰 W) M := by
    refine ⟨Ω, hΩ, ?_⟩
    ext V
    constructor
    · rintro ⟨hV, hV𝒰, hVW⟩
      rw [hObeq] at hV𝒰
      exact ⟨hV, by rw [hOceq]; exact ⟨hV.2, hV𝒰.2⟩, hVW⟩
    · rintro ⟨hV, hV𝒰, hVW⟩
      rw [hOceq] at hV𝒰
      exact ⟨hV, by rw [hObeq]; exact ⟨hV.1.2, hV𝒰.2⟩, hVW⟩
  have h1 := (hcrit (Edge L m k i → Matrices.ComplexMatrix2) (Edge L m k i → Matrices.ComplexMatrix2)
    (fieldCurveData L m k i) hR _ _ (b.gaugeFixedEnergy i) hMb (b.prolong i W)).1.2
    ⟨⟨hWΩ, hxcrit.1⟩, hxcrit⟩
  have h2 : (fieldCurveData L m k i).IsCriticalOn M (c.gaugeFixedEnergy i) (b.prolong i W) := by
    refine ⟨h1.1, fun I γ hγ hmaps h0 => ?_⟩
    have hI := (hR.isCurve_local I γ hγ).1
    have hev : (fun t => c.gaugeFixedEnergy i (γ t)) =ᶠ[𝓝 (0 : ℝ)]
        fun t => b.gaugeFixedEnergy i (γ t) := by
      filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
      have hmt := hmaps ht
      have hm𝒰 := hmt.2.1
      rw [hObeq] at hm𝒰
      have heq : b.energy i (γ t) = c.energy i (γ t) := hOfsub ⟨hmt.1.1.1, hm𝒰.2⟩
      simp only [CriticalBranchData.gaugeFixedEnergy, heq]
    exact hev.deriv_eq.trans (h1.2 I γ hγ hmaps h0)
  have h3 := (hcrit (Edge L m k i → Matrices.ComplexMatrix2) (Edge L m k i → Matrices.ComplexMatrix2)
    (fieldCurveData L m k i) hR _ _ (c.gaugeFixedEnergy i) hMc (b.prolong i W)).1.1 h2
  exact huniq _ hxU h3.2
end CriticalBranchUniqueness
theorem criticalBranchUnique_of_chosen
    (hFixed : ChosenBranchIsCritical)
    (hNeighbourhood : FibreNeighbourhoodsOfSteps)
    (hPaths : AnalyticMapsAlongCurves)
    (hBonds : BondSetFields.ProductStructureHolds) :
    CriticalBranchUnique := by
  intro L m k hL hm b hb
  obtain ⟨hc, hU⟩ := hFixed L m k hL hm
  have hstep : ∀ i < k, EventuallyNearIdentity (fieldSpace L m k i)
      (fun V => b.energy i V = (chosenCriticalBranch L m k).energy i V) →
      EventuallyNearIdentity (fieldSpace L m k (i + 1))
        (fun W => b.prolong i W = (chosenCriticalBranch L m k).prolong i W) := fun i hi hF =>
    CriticalBranchUniqueness.prolong_eq_of_energy_eq hBonds hPaths hNeighbourhood hL hm hb hi
      (hU i hi) hF
  have hfun : ∀ l ≤ k, EventuallyNearIdentity (fieldSpace L m k l)
      (fun V => b.energy l V = (chosenCriticalBranch L m k).energy l V) := by
    intro l
    induction l with
    | zero =>
      intro _
      filter_upwards [hb.energy_bottom, hc.energy_bottom] with V h1 h2
      rw [h1, h2]
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      have hF := ih hi'.le
      filter_upwards [hstep i hi' hF, hb.prolong_section i hi', hc.prolong_section i hi',
        (CriticalBranchUniqueness.tendsto_prolong hBonds hPaths hL hm hb hi').eventually hF]
        with W h1 h2 h3 h4
      rw [h2.2.2.1, h4, h1, h3.2.2.1]
  exact ⟨hfun, fun l hl => hstep l hl (hfun l hl.le)⟩
end YangMills.Construction.Tower
end
