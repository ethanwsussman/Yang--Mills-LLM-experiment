import YangMills.Construction.Continuum.LinearCombinationsOfAdmissibleSequences
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace.AdmissibleCombinations
theorem zero_mem_schwartzFlatOffPosTime (h : SchwartzSupremaStatement) {n : ℕ} (hn : 1 ≤ n) :
    (fun _ => 0 : Config n → ℂ) ∈ schwartzFlatOffPosTime n := by
  obtain ⟨-, hlin, -, -, -, S, hS, -⟩ := h n hn
  have hs : IsSchwartz (0 : Config n → ℂ) := by
    have h0 : (0 : Config n → ℂ) ∈ (S : Set (Config n → ℂ)) := S.zero_mem
    rw [hS] at h0
    exact h0
  have hsm : ContDiff ℝ ∞ (0 : Config n → ℂ) := contDiff_const
  obtain ⟨-, -, hpd⟩ := hlin 0 0 hsm hsm 0 0 0 0 le_rfl
  refine ⟨hs, hsm, isOpen_posTimeSet, fun x _ => ⟨hsm, fun α => ?_⟩⟩
  have e : iteratedPartial α (0 : Config n → ℂ) = 0 := by simpa using hpd α
  show iteratedPartial α (0 : Config n → ℂ) x = 0
  rw [e]
  rfl
theorem linComb_mem_schwartzFlatOffPosTime (h : SchwartzSupremaStatement) {n : ℕ} (hn : 1 ≤ n)
    {f g : Config n → ℂ} (hf : f ∈ schwartzFlatOffPosTime n)
    (hg : g ∈ schwartzFlatOffPosTime n) (a b : ℂ) :
    (fun y => a * f y + b * g y) ∈ schwartzFlatOffPosTime n := by
  obtain ⟨-, hlin, hsch, -, -, -⟩ := h n hn
  obtain ⟨hs, hsm, ho, hfl⟩ := hf
  obtain ⟨hs', hsm', -, hgl⟩ := hg
  have e : (fun y => a * f y + b * g y) = a • f + b • g := by
    funext y
    simp
  rw [e]
  obtain ⟨-, hcd, hpd⟩ := hlin f g hsm hsm' a b 0 0 le_rfl
  refine ⟨(hsch f g hs hs' a b).2, hcd, ho, fun x hx => ⟨hcd, fun α => ?_⟩⟩
  rw [hpd α]
  simp [(hfl x hx).2 α, (hgl x hx).2 α]
theorem zeroOfDegree_mem (h : SchwartzSupremaStatement) (q : ℕ) :
    zeroOfDegree q ∈ flatOffPosTimeAt q := by
  cases q with
  | zero => exact Set.mem_univ _
  | succ n => exact zero_mem_schwartzFlatOffPosTime h (Nat.succ_pos n)
theorem linCombAt_mem (h : SchwartzSupremaStatement) (a b : ℂ) {q : ℕ}
    {f g : FnOrScalar q} (hf : f ∈ flatOffPosTimeAt q)
    (hg : g ∈ flatOffPosTimeAt q) :
    linCombAt a b f g ∈ flatOffPosTimeAt q := by
  cases q with
  | zero => exact Set.mem_univ _
  | succ n => exact linComb_mem_schwartzFlatOffPosTime h (Nat.succ_pos n) hf hg a b
theorem linCombAt_zeroOfDegree (a b : ℂ) (q : ℕ) :
    linCombAt a b (zeroOfDegree q) (zeroOfDegree q) = zeroOfDegree q := by
  cases q with
  | zero =>
    show a * (0 : ℂ) + b * (0 : ℂ) = (0 : ℂ)
    simp
  | succ n =>
    show (fun _ : Config (n + 1) => a * (0 : ℂ) + b * (0 : ℂ)) = fun _ => (0 : ℂ)
    simp
theorem linCombClosure_holds (h : SchwartzSupremaStatement) : LinCombClosure := by
  refine ⟨⟨fun q => ⟨zeroOfDegree q, zeroOfDegree_mem h q⟩, ?_, fun q => rfl⟩,
    fun a b Φ Ψ hΦ hΨ =>
      ⟨fun q => ⟨linCombAt a b (Φ q).1 (Ψ q).1,
        linCombAt_mem h a b (Φ q).2 (Ψ q).2⟩, ?_, fun q => rfl⟩⟩
  · simp [PosTimeSeq.IsFinitelySupported]
  · refine (hΦ.union hΨ).subset fun q hq => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    apply hq
    show linCombAt a b (Φ q).1 (Ψ q).1 = zeroOfDegree q
    rw [hn.1, hn.2, linCombAt_zeroOfDegree]
end YangMills.Construction.ConfigSpace.AdmissibleCombinations
end
