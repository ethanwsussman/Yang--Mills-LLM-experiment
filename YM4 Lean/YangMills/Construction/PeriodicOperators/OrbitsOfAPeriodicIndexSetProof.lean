import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSetProof
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuotOrbits
variable {I : PeriodicData}
theorem mkQuot_eq_iff (hI : IsPeriodic I) (s : ℕ) (x y : I.Carrier) :
    I.mkQuot s x = I.mkQuot s y ↔ ∃ n : Fin 4 → ℤ, y = I.translate (s • n) x := by
  constructor
  · intro e
    have key : ∀ a b, Relation.EqvGen
        (fun x y : I.Carrier => ∃ n : Fin 4 → ℤ, y = I.translate (s • n) x) a b →
        ∃ n : Fin 4 → ℤ, b = I.translate (s • n) a := by
      intro a b hab
      induction hab with
      | rel a b hab => exact hab
      | refl a => exact ⟨0, by simp [hI.translate_zero]⟩
      | symm a b _ ih =>
        obtain ⟨n, rfl⟩ := ih
        refine ⟨-n, ?_⟩
        rw [← hI.translate_add]
        simp [hI.translate_zero]
      | trans a b c _ _ ih₁ ih₂ =>
        obtain ⟨m, rfl⟩ := ih₁
        obtain ⟨n, rfl⟩ := ih₂
        exact ⟨m + n, by rw [← hI.translate_add, smul_add]⟩
    exact key _ _ (Quot.eqvGen_exact e)
  · rintro ⟨n, rfl⟩
    exact Quot.sound ⟨n, rfl⟩
theorem translate_vector_unique (hI : IsPeriodic I) (x : I.Carrier) {a b : Fin 4 → ℤ}
    (e : I.translate a x = I.translate b x) : a = b := by apply _root_.YangMills.Construction.PeriodicOperators.IdKernelFacts.translate_injective <;> assumption
theorem nsmul_vector_injective {s : ℕ} (hs : 0 < s) {a b : Fin 4 → ℤ}
    (e : s • a = s • b) : a = b := by
  funext μ
  have hμ := congrFun e μ
  simp only [Pi.smul_apply, nsmul_eq_mul] at hμ
  have hs' : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  exact mul_left_cancel₀ hs' hμ
theorem claim_holds : Claim := by
  intro I hI
  refine ⟨mkQuot_eq_iff hI, ?_⟩
  intro s hs r hr
  constructor
  · rintro ⟨c, m⟩ ⟨c', m'⟩ e
    simp only at e
    have hc : c = c' := by
      have e₁ : I.mkQuot s (r c) = I.mkQuot s (I.translate (s • m) (r c)) :=
        (mkQuot_eq_iff hI s _ _).mpr ⟨m, rfl⟩
      have e₂ : I.mkQuot s (r c') = I.mkQuot s (I.translate (s • m') (r c')) :=
        (mkQuot_eq_iff hI s _ _).mpr ⟨m', rfl⟩
      rw [← hr c, ← hr c', e₁, e₂, e]
    subst hc
    have := nsmul_vector_injective hs (translate_vector_unique hI (r c) e)
    rw [this]
  · intro x
    obtain ⟨n, hn⟩ := (mkQuot_eq_iff hI s (r (I.mkQuot s x)) x).mp (hr _)
    exact ⟨(I.mkQuot s x, n), hn.symm⟩
end YangMills.Construction.PeriodicOperators.QuotOrbits
end
