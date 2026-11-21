import YangMills.Construction.LawOnABoxOfTheFlow.LeastFillingIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.BoxLaws
private theorem exists_measurable_min_head {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} (C : Set (X × (Fin (n + 1) → ℝ))) (hC : IsCompact C) :
    ∃ h : X → ℝ,
      (∀ x ∈ Prod.fst '' C, (∃ y, (x, y) ∈ C ∧ y 0 = h x) ∧ ∀ y, (x, y) ∈ C → h x ≤ y 0) ∧
      Measurable fun x : (Prod.fst '' C : Set X) => h x := by
  have hhead : Continuous fun p : X × (Fin (n + 1) → ℝ) => p.2 0 :=
    (continuous_apply 0).comp continuous_snd
  let F : X → Set ℝ := fun x => (fun p : X × (Fin (n + 1) → ℝ) => p.2 0) '' (C ∩ {p | p.1 = x})
  have hF : ∀ x, IsCompact (F x) := fun x =>
    (hC.inter_right (isClosed_eq continuous_fst continuous_const)).image hhead
  have hmin : ∀ x ∈ Prod.fst '' C, (∃ y, (x, y) ∈ C ∧ y 0 = sInf (F x)) ∧
      ∀ y, (x, y) ∈ C → sInf (F x) ≤ y 0 := by
    intro x hx
    obtain ⟨⟨x', y₀⟩, hp, rfl⟩ := hx
    have hne : (F x').Nonempty := ⟨y₀ 0, (x', y₀), ⟨hp, rfl⟩, rfl⟩
    refine ⟨?_, fun y hy => csInf_le (hF x').bddBelow ⟨(x', y), ⟨hy, rfl⟩, rfl⟩⟩
    obtain ⟨⟨x'', y⟩, ⟨hq, hx⟩, hy⟩ := (hF x').sInf_mem hne
    obtain rfl : x'' = x' := hx
    exact ⟨y, hq, hy⟩
  refine ⟨fun x => sInf (F x), hmin, measurable_of_Iic fun t => ?_⟩
  have hclosed : IsClosed (Prod.fst '' (C ∩ {p : X × (Fin (n + 1) → ℝ) | p.2 0 ≤ t})) :=
    ((hC.inter_right (isClosed_le hhead continuous_const)).image continuous_fst).isClosed
  have hpre : (fun x : (Prod.fst '' C : Set X) => sInf (F x)) ⁻¹' Iic t =
      Subtype.val ⁻¹' (Prod.fst '' (C ∩ {p : X × (Fin (n + 1) → ℝ) | p.2 0 ≤ t})) := by
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_Iic]
    constructor
    · intro h
      obtain ⟨⟨y, hy, hy0⟩, -⟩ := hmin x hx
      exact ⟨(x, y), ⟨hy, by simpa [hy0] using h⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hy, ht⟩, rfl⟩
      exact ((hmin x' hx).2 y hy).trans ht
  rw [hpre]
  exact measurable_subtype_coe hclosed.measurableSet
private theorem toLex_cons_le_of_head {n : ℕ} {a : ℝ} {v : Fin n → ℝ} {y : Fin (n + 1) → ℝ} (ha : a ≤ y 0)
    (htail : a = y 0 → toLex v ≤ toLex fun i : Fin n => y i.succ) :
    toLex (Fin.cons a v : Fin (n + 1) → ℝ) ≤ toLex y := by
  rcases ha.lt_or_eq with h | h
  · exact le_of_lt ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
  · rcases (htail h).lt_or_eq with hlt | he
    · obtain ⟨i, hi, hv⟩ := hlt
      refine le_of_lt ⟨i.succ, fun j hj => ?_, hv⟩
      induction j using Fin.cases with
      | zero => exact h
      | succ j => exact hi j (Fin.succ_lt_succ_iff.1 hj)
    · refine le_of_eq (congrArg toLex ?_)
      have hv : v = fun i : Fin n => y i.succ := toLex.injective he
      funext i
      induction i using Fin.cases with
      | zero => exact h
      | succ i => exact congrFun hv i
private theorem exists_measurable_lexLeast_section (n : ℕ) :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
      (C : Set (X × (Fin n → ℝ))), IsCompact C →
      ∃ s : X → Fin n → ℝ,
        (∀ x ∈ Prod.fst '' C, (x, s x) ∈ C ∧ ∀ y, (x, y) ∈ C → toLex (s x) ≤ toLex y) ∧
        Measurable fun x : (Prod.fst '' C : Set X) => s x := by
  induction n with
  | zero =>
    intro X _ _ _ _ _ C _
    refine ⟨fun _ => 0, fun x hx => ?_, measurable_const⟩
    obtain ⟨⟨x', y₀⟩, hp, rfl⟩ := hx
    obtain rfl : y₀ = 0 := Subsingleton.elim _ _
    exact ⟨hp, fun y _ => le_of_eq (congrArg toLex (Subsingleton.elim _ _))⟩
  | succ n ih =>
    intro X _ _ _ _ _ C hC
    obtain ⟨h, hh, hhm⟩ := exists_measurable_min_head C hC
    let ψ : X × (Fin (n + 1) → ℝ) → (X × ℝ) × (Fin n → ℝ) :=
      fun p => ((p.1, p.2 0), fun i => p.2 i.succ)
    have hψ : Continuous ψ :=
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)).prodMk
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd)
    obtain ⟨s', hs', hsm⟩ := ih (X × ℝ) (ψ '' C) (hC.image hψ)
    have hin : ∀ x ∈ Prod.fst '' C, (x, h x) ∈ Prod.fst '' (ψ '' C) := by
      intro x hx
      obtain ⟨⟨y, hy, hy0⟩, -⟩ := hh x hx
      exact ⟨ψ (x, y), ⟨(x, y), hy, rfl⟩, by simp [ψ, hy0]⟩
    refine ⟨fun x => Fin.cons (h x) (s' (x, h x)), fun x hx => ⟨?_, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨⟨⟨x', y⟩, hy, he⟩, -⟩ := hs' (x, h x) (hin x hx)
      have e1 : x' = x := congrArg (fun q => q.1.1) he
      have e2 : y 0 = h x := congrArg (fun q => q.1.2) he
      have e3 : (fun i : Fin n => y i.succ) = s' (x, h x) := congrArg (fun q => q.2) he
      subst e1
      have hy' : (Fin.cons (h x') (s' (x', h x')) : Fin (n + 1) → ℝ) = y := by
        funext i
        induction i using Fin.cases with
        | zero => exact e2.symm
        | succ i => exact (congrFun e3 i).symm
      simpa [hy'] using hy
    · refine toLex_cons_le_of_head ((hh x hx).2 y hy) fun e => ?_
      exact (hs' (x, h x) (hin x hx)).2 _ ⟨(x, y), hy, by simp [ψ, e]⟩
    · have hpair : Measurable fun x : (Prod.fst '' C : Set X) =>
          (⟨(x.1, h x.1), hin x.1 x.2⟩ : (Prod.fst '' (ψ '' C) : Set (X × ℝ))) :=
        Measurable.subtype_mk (measurable_subtype_coe.prodMk hhm)
      have htail := hsm.comp hpair
      refine measurable_pi_iff.2 fun i => ?_
      induction i using Fin.cases with
      | zero => exact hhm
      | succ i => exact (measurable_pi_apply i).comp htail
theorem lexLeastSectionMeasurable_holds : LexLeastSectionMeasurable :=
  fun X _ _ _ _ _ n C hC => exists_measurable_lexLeast_section n X C hC
end YangMills.Construction.BoxLaws
end
