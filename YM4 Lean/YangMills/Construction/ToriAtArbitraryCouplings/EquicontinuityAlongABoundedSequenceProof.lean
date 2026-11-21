import YangMills.Construction.ToriAtArbitraryCouplings.BoundedFormsAlongABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityAlongABoundedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityAlongSequence
private theorem entry_mem_c1Submodule (s : TorusSide) {n : ℕ} (f : Fin n → s.Point .torus → ℝ)
    (hf : List.ofFn f ∈ s.sepOfLength .torus n) (A : Fin n → Set (s.Point .torus))
    (hA : ∀ l, s.closedSupport .torus (f l) ⊆ A l) (l : Fin n) :
    f l ∈ s.c1Submodule .torus (A l) := by
  have hent := ((s.mem_sepOfLength_iff .torus n _).1 hf).2.1 (f l)
    (List.mem_ofFn.2 ⟨l, rfl⟩)
  exact (s.mem_c1Submodule_iff .torus _ _).2 ⟨hent.1, hent.2, hA l⟩
theorem holds_of_forms (hForms : BoundedMultilinearForms.Statement)
    (hTel : TelescopingEquicontinuity.Claim) : Holds := by
  intro s hL m' K β C h j n hn d hd A hA f g hf hg hfA hgA
  obtain ⟨Ψ, hΨ⟩ := hForms s hL m' K β C h j n hn d hd A hA
  have hC : 0 ≤ C n d := h.isClusterConstant.nonneg n hn d hd
  have hObey := ((hTel.2 s hL m' .torus n hn d hd A hA).1 (C n d) hC).2 Ψ fun u => (hΨ u).2
  let F : (l : Fin n) → s.c1Submodule .torus (A l) :=
    fun l => ⟨f l, entry_mem_c1Submodule s f hf A hfA l⟩
  let G : (l : Fin n) → s.c1Submodule .torus (A l) :=
    fun l => ⟨g l, entry_mem_c1Submodule s g hg A hgA l⟩
  have key := hObey F G
  have e1 : s.cumulantAt (K j) (β j) (List.ofFn f) = (Ψ F : ℂ) := (hΨ F).1.symm
  have e2 : s.cumulantAt (K j) (β j) (List.ofFn g) = (Ψ G : ℂ) := (hΨ G).1.symm
  change ‖s.cumulantAt (K j) (β j) (List.ofFn f) -
    s.cumulantAt (K j) (β j) (List.ofFn g)‖ ≤ _
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact key
end YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityAlongSequence
end
