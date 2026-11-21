import YangMills.Construction.ToriAtArbitraryCouplings.HypercubicMapsAndAdicTranslationsOnSupports
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace LatticeSymmetriesOnSupports
open TorusSymmetries (actOn translateOn isDistIsometry_actOn isDistIsometry_translateOn actOn_proj)
open TorusTransport (hyperoctahedral hyperoctahedralLinear)
def PreservesRationalBoxes (ρ : Equiv.Perm (Fin 4 → ℝ)) : Prop :=
  ∀ P, IsRationalBox P → IsRationalBox (ρ '' P)
theorem image_eq_of_mem_iff (ρ : Equiv.Perm (Fin 4 → ℝ)) {P P' : Set (Fin 4 → ℝ)}
    (h : ∀ x, x ∈ P ↔ ρ x ∈ P') : ρ '' P = P' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨ρ.symm y, (h _).2 (by simpa using hy), by simp⟩
theorem preservesSupports_euclidean (s : TorusSide) (ρ : Equiv.Perm (Fin 4 → ℝ))
    (hbox : PreservesRationalBoxes ρ) (hsmooth : ContDiff ℝ 1 ρ.symm)
    (hdist : ∀ x y, s.pointDist .euclidean (ρ x) (ρ y) = s.pointDist .euclidean x y) :
    PreservesSupports s .euclidean ρ := by
  refine ⟨?_, ?_, hdist⟩
  · rintro Q ⟨B, hB, hP, rfl⟩
    refine ⟨(fun P => ρ '' P) '' B, hB.image _, ?_, Set.image_sUnion⟩
    rintro _ ⟨P, hPB, rfl⟩
    exact hbox P (hP P hPB)
  · intro f hf
    have key : ∀ g : (Fin 4 → ℝ) → ℝ, ContDiff ℝ 1 g → ContDiff ℝ 1 (g ∘ ρ.symm) :=
      fun g hg => hg.comp hsmooth
    exact key f hf
theorem preservesSupports_torus (s : TorusSide) (ρ : Equiv.Perm (Fin 4 → ℝ))
    (r : Equiv.Perm s.asMirrorData.Torus) (hbox : PreservesRationalBoxes ρ)
    (hsmooth : ContDiff ℝ 1 ρ.symm)
    (hproj : ∀ y, r (s.proj y) = s.proj (ρ y))
    (hdist : ∀ x y, s.pointDist .torus (r x) (r y) = s.pointDist .torus x y) :
    PreservesSupports s .torus r := by
  refine ⟨?_, ?_, hdist⟩
  · rintro Q ⟨B, hB, hP, rfl⟩
    refine ⟨(fun P => ρ '' P) '' B, hB.image _, ?_, ?_⟩
    · rintro _ ⟨P, hPB, rfl⟩
      refine ⟨hbox P (hP P hPB).1, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
      rw [← hproj, ← hproj] at h
      exact congrArg ρ ((hP P hPB).2 hx hy (r.injective h))
    · have e : r '' (⋃ P ∈ B, s.proj '' P) =
          ⋃ P ∈ (fun P => ρ '' P) '' B, s.proj '' P := by
        rw [Set.image_iUnion₂, Set.biUnion_image]
        refine Set.iUnion₂_congr fun P _ => ?_
        rw [Set.image_image, Set.image_image]
        exact Set.image_congr fun y _ => hproj y
      exact e
  · intro f hf
    have e : (f ∘ r.symm) ∘ s.asMirrorData.projection = (f ∘ s.asMirrorData.projection) ∘ ρ.symm := by
      funext y
      have h : r.symm (s.proj y) = s.proj (ρ.symm y) := by
        rw [Equiv.symm_apply_eq, hproj, Equiv.apply_symm_apply]
      exact congrArg f h
    change ContDiff ℝ 1 ((f ∘ r.symm) ∘ s.asMirrorData.projection)
    rw [e]
    exact ContDiff.comp (show ContDiff ℝ 1 (f ∘ s.asMirrorData.projection) from hf) hsmooth
theorem unit_mul_mem_Icc_iff (ε : ℤˣ) (a b : ℚ) (t : ℝ) :
    ((ε : ℤ) : ℝ) * t ∈ Set.Icc (((if ε = 1 then a else -b : ℚ)) : ℝ)
        (((if ε = 1 then b else -a : ℚ)) : ℝ) ↔ t ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  rcases Int.units_eq_one_or ε with h | h
  · simp [h]
  · have : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [h, this, if_false, Set.mem_Icc]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
theorem preservesRationalBoxes_hyperoctahedral (w : hyperoctahedral) : PreservesRationalBoxes w.1 := by
  obtain ⟨σ, ε, h⟩ := w.2
  rw [h]
  rintro _ ⟨a, b, hab, rfl⟩
  refine ⟨fun μ => if ε μ = 1 then a (σ μ) else -b (σ μ),
    fun μ => if ε μ = 1 then b (σ μ) else -a (σ μ), fun μ => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hab _
    · exact neg_lt_neg (hab _)
  · refine image_eq_of_mem_iff _ fun x => ?_
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, TorusTransport.signedCoordinateEquiv_apply,
      unit_mul_mem_Icc_iff]
    exact ⟨fun h μ => h (σ μ), fun h ν => by simpa using h (σ.symm ν)⟩
theorem exists_rat_of_mem_adicGridPoints {L : ℕ} {x : ℝ} (hx : x ∈ PeriodicLattice.adicGridPoints L) :
    ∃ q : ℚ, x = q := by
  obtain ⟨k, m, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff L x).1 hx
  refine ⟨(m : ℚ) * (L : ℚ) ^ (-(k : ℤ)), ?_⟩
  simp [PeriodicLattice.meshSize]
theorem preservesRationalBoxes_addRight {v : Fin 4 → ℝ} {q : Fin 4 → ℚ} (hq : ∀ μ, v μ = q μ) :
    PreservesRationalBoxes (Equiv.addRight v) := by
  rintro _ ⟨a, b, hab, rfl⟩
  refine ⟨a + q, b + q, fun μ => by simpa using hab μ, ?_⟩
  refine image_eq_of_mem_iff _ fun x => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, Equiv.coe_addRight, Pi.add_apply, Rat.cast_add,
    hq, Set.mem_Icc, add_le_add_iff_right]
theorem contDiff_symm_hyperoctahedral (w : hyperoctahedral) : ContDiff ℝ 1 w.1.symm := by
  have e : (w.1.symm : (Fin 4 → ℝ) → Fin 4 → ℝ) =
      LinearMap.toContinuousLinearMap (hyperoctahedralLinear w⁻¹) := by
    funext x
    exact (congrFun (TorusTransport.coe_hyperoctahedralLinear w⁻¹) x).symm
  rw [e]
  exact ContinuousLinearMap.contDiff _
theorem contDiff_symm_addRight (v : Fin 4 → ℝ) :
    ContDiff ℝ 1 (Equiv.addRight v : Equiv.Perm (Fin 4 → ℝ)).symm := by
  rw [Equiv.addRight_symm]
  exact contDiff_id.add contDiff_const
theorem holds : Statement := by
  intro s
  have rat : ∀ v : Fin 4 → ℝ, (∀ μ, v μ ∈ PeriodicLattice.adicGridPoints s.L) →
      PreservesRationalBoxes (Equiv.addRight v) := fun v hv => by
    choose q hq using fun μ => exists_rat_of_mem_adicGridPoints (hv μ)
    exact preservesRationalBoxes_addRight hq
  refine ⟨fun w => ?_, fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact preservesSupports_torus s w.1 _ (preservesRationalBoxes_hyperoctahedral w)
      (contDiff_symm_hyperoctahedral w) (actOn_proj _ .torus w) (isDistIsometry_actOn _ .torus w)
  · exact preservesSupports_euclidean s _ (preservesRationalBoxes_hyperoctahedral w)
      (contDiff_symm_hyperoctahedral w) (isDistIsometry_actOn _ .euclidean w)
  · exact preservesSupports_torus s (Equiv.addRight v) _ (rat v hv) (contDiff_symm_addRight v)
      (fun y => rfl) (isDistIsometry_translateOn _ .torus _)
  · exact preservesSupports_euclidean s _ (rat v hv) (contDiff_symm_addRight v)
      (isDistIsometry_translateOn _ .euclidean _)
end LatticeSymmetriesOnSupports
end YangMills.Construction.ToriAtArbitraryCouplings
end
