import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.TermsLieInTheirBoxes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.TermsInBoxes
open YangMills.Construction.InfiniteLattice.BoxTorusComparisonData
theorem coe_axisStep_apply (μ ν : Fin 4) :
    ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) ν = if ν = μ then 1 else 0 := by
  simp [axisStep, Pi.single_apply]
theorem self_mem_siteCube (z : LatticePoint 1) (r : ℕ+) : z ∈ siteCube z r :=
  ⟨0, fun _ => Nat.zero_le _, fun μ => by simp⟩
theorem add_axisStep_mem_siteCube (z : LatticePoint 1) (r : ℕ+) (μ : Fin 4) :
    z + axisStep 1 μ ∈ siteCube z r := by
  refine ⟨fun ν => if ν = μ then 1 else 0, fun ν => ?_, fun ν => ?_⟩
  · have := r.pos
    dsimp only
    split_ifs <;> omega
  · have h := coe_axisStep_apply μ ν
    simp only [AddSubgroup.coe_add, Pi.add_apply, h]
    split_ifs <;> simp
theorem add_two_axisSteps_mem_siteCube (z : LatticePoint 1) (r : ℕ+) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    z + axisStep 1 μ + axisStep 1 ν ∈ siteCube z r := by
  refine ⟨fun κ => (if κ = μ then 1 else 0) + (if κ = ν then 1 else 0), fun κ => ?_, fun κ => ?_⟩
  · have := r.pos
    dsimp only
    by_cases h₁ : κ = μ
    · have h₂ : κ ≠ ν := fun h => hμν (h₁.symm.trans h)
      simp only [h₁, if_true, if_neg (h₁ ▸ h₂)]
      omega
    · simp only [if_neg h₁]
      split_ifs <;> omega
  · have h₁ := coe_axisStep_apply μ κ
    have h₂ := coe_axisStep_apply ν κ
    simp only [AddSubgroup.coe_add, Pi.add_apply, h₁, h₂]
    (split_ifs <;> simp); ring
theorem add_mem_siteCube_add {x z : LatticePoint 1} {r : ℕ+} (v : LatticePoint 1)
    (h : x ∈ siteCube z r) : x + v ∈ siteCube (z + v) r := by
  obtain ⟨k, hk, hx⟩ := h
  refine ⟨k, hk, fun μ => ?_⟩
  simp only [AddSubgroup.coe_add, Pi.add_apply, hx μ]
  ring
theorem isPositivelyOriented_of_mem_observableSupport (d : BoxTorusComparisonData) {e : Link 1}
    (he : e ∈ observableSupport d.obs) : e.IsPositivelyOriented := by
  by_cases hex : ∃ S : Set (Link 1), IsLinkSet S ∧ S.Finite ∧ DependsOnlyOn S d.obs
  · obtain ⟨S, hS⟩ := hex
    exact hS.1 (Set.mem_sInter.mp he S hS)
  · exfalso
    have hall : ∀ c : Link 1, c ∈ observableSupport d.obs :=
      fun c => Set.mem_sInter.mpr fun S hS => (hex ⟨S, hS⟩).elim
    obtain ⟨⟨z, ⟨k, -, hz⟩, hzt⟩, -⟩ :=
      d.obs_support (Link.forwardFrom (d.obsAnchor - axisStep 1 0) 0) (hall _)
    have h0 : (z : AmbientSpace) 0 = (d.obsAnchor : AmbientSpace) 0 - 1 := by
      have h := congrFun hzt 0
      have hs := coe_axisStep_apply 0 0
      simpa [Link.forwardFrom, hs] using h
    have := hz 0
    linarith
theorem eq_forwardFrom_initial {e : Link 1} (he : e.IsPositivelyOriented) :
    ∃ μ : Fin 4, e = Link.forwardFrom e.initial μ := by
  obtain ⟨μ, hμ⟩ := he
  exact ⟨μ, Link.ext rfl (sub_eq_iff_eq_add'.mp hμ)⟩
theorem links_shifted (h : YangMills.Construction.InfiniteLattice.ToriArraysAndTiltedMeasuresFacts)
    (d : BoxTorusComparisonData) (v : d.translationGroup) :
    (Term.shifted v : d.Term).links =
      shiftLinks (observableSupport d.obs) (v : LatticePoint 1) :=
  ((h 1 one_pos).2.1 d.obsArray 0).1.observableSupport_translate
    (⟨v, ⟨0, Nat.one_pos⟩⟩ : d.obsArray.Label)
theorem link_endpoints_mem_and_positive
    (h : YangMills.Construction.InfiniteLattice.ToriArraysAndTiltedMeasuresFacts)
    (d : BoxTorusComparisonData) (T : d.Term) {e : Link 1} (he : e ∈ T.links) :
    e.initial ∈ T.siteBox ∧ e.terminal ∈ T.siteBox ∧ e.IsPositivelyOriented := by
  cases T with
  | plaquette p =>
    have hpos : ∀ (x : LatticePoint 1) (μ : Fin 4), (Link.forwardFrom x μ).IsPositivelyOriented :=
      fun x μ => ⟨μ, add_sub_cancel_left x (axisStep 1 μ)⟩
    have he' : e ∈ p.edges := he
    have hne : p.lowAxis ≠ p.highAxis := ne_of_lt p.lowAxis_lt_highAxis
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl
    · exact ⟨self_mem_siteCube _ _, add_axisStep_mem_siteCube _ _ _, hpos _ _⟩
    · exact ⟨add_axisStep_mem_siteCube _ _ _, add_two_axisSteps_mem_siteCube _ _ hne, hpos _ _⟩
    · exact ⟨add_axisStep_mem_siteCube _ _ _, add_two_axisSteps_mem_siteCube _ _ hne.symm, hpos _ _⟩
    · exact ⟨self_mem_siteCube _ _, add_axisStep_mem_siteCube _ _ _, hpos _ _⟩
  | shifted v =>
    rw [links_shifted h d v] at he
    obtain ⟨c, hc, rfl⟩ := he
    have hcpos := isPositivelyOriented_of_mem_observableSupport d hc
    obtain ⟨⟨z, hz, hzt⟩, ⟨z', hz', hzh⟩⟩ := d.obs_support c hc
    have hi : c.initial ∈ siteCube d.obsAnchor d.boxWidth := Subtype.ext hzt ▸ hz
    have ht : c.terminal ∈ siteCube d.obsAnchor d.boxWidth := Subtype.ext hzh ▸ hz'
    have hmap : ((shift (v : LatticePoint 1)).linkMap c).IsPositivelyOriented := by
      obtain ⟨μ, hμ⟩ := hcpos
      refine ⟨μ, ?_⟩
      rw [← hμ]
      exact add_sub_add_right_eq_sub _ _ _
    have heq : ((shift (v : LatticePoint 1)).linkMap c).orientedRepresentative =
        (shift (v : LatticePoint 1)).linkMap c := by
      simp only [Link.orientedRepresentative, if_pos hmap]
    beta_reduce
    rw [heq]
    exact ⟨add_mem_siteCube_add (v : LatticePoint 1) hi,
      add_mem_siteCube_add (v : LatticePoint 1) ht, hmap⟩
theorem injOn_quotientMap_siteCube (d : BoxTorusComparisonData) (x : LatticePoint 1) :
    Set.InjOn d.periodSublattice.quotientMap (siteCube x (d.boxWidth + 1)) := by
  intro y hy y' hy' hyy
  obtain ⟨k, hk, hky⟩ := hy
  obtain ⟨k', hk', hky'⟩ := hy'
  have hyy' : (y : LatticePoint 1 ⧸ d.periodSublattice.periods) = y' := hyy
  have hγ : -y + y' ∈ d.periodSublattice.periods := QuotientAddGroup.eq.mp hyy'
  by_contra hne
  have hne' : -y + y' ≠ 0 := fun h0 => hne (neg_add_eq_zero.mp h0)
  have hlt := d.no_short_period _ hγ hne'
  have hle : ‖((-y + y' : LatticePoint 1) : AmbientSpace)‖ ≤ ((d.boxWidth : ℕ) : ℝ) + 1 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
    have h₁ : (k μ : ℝ) ≤ ((d.boxWidth : ℕ) : ℝ) + 1 := by
      have := hk μ
      rw [PNat.add_coe, PNat.one_coe] at this
      exact_mod_cast this
    have h₂ : (k' μ : ℝ) ≤ ((d.boxWidth : ℕ) : ℝ) + 1 := by
      have := hk' μ
      rw [PNat.add_coe, PNat.one_coe] at this
      exact_mod_cast this
    have h₅ : ((-y + y' : LatticePoint 1) : AmbientSpace) μ = (k' μ : ℝ) - (k μ : ℝ) := by
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Pi.add_apply, Pi.neg_apply, hky μ,
        hky' μ]
      ring
    rw [h₅, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact absurd hlt (not_lt.mpr hle)
theorem statement_holds
    (h : YangMills.Construction.InfiniteLattice.ToriArraysAndTiltedMeasuresFacts) :
    YangMills.Construction.InfiniteLattice.TermsInBoxes.Statement := by
  intro d
  refine ⟨links_shifted h d, fun T e he => ?_, injOn_quotientMap_siteCube d⟩
  obtain ⟨hi, ht, hpos⟩ := link_endpoints_mem_and_positive h d T he
  obtain ⟨μ, hμ⟩ := eq_forwardFrom_initial hpos
  exact ⟨hi, ht, e.initial, hi, μ, hμ⟩
end YangMills.Construction.InfiniteLattice.TermsInBoxes
end
