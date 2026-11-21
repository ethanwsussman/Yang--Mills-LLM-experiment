import YangMills.Construction.HessianOfTheMainTerm.LengthOfASiteOfATorus
import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.PeriodicLattice
namespace HessianOfTheMainTerm
theorem torusSupNorm_eq_sup' {S : ℝ} (x : TorusMetric.Torus4 S) :
    TorusMetric.torusSupNorm x = Finset.univ.sup' Finset.univ_nonempty fun μ => ‖x μ‖ := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_eq_sup <;> assumption
theorem siteLengthFacts_holds : SiteLengthFacts := by
  intro L m j hL hmj
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hh : 0 < meshSize L j := by unfold meshSize; exact zpow_pos hLpos _
  have hnorm : ∀ u : Site L m j, supLengthInMesh u =
      (Finset.univ.sup' Finset.univ_nonempty fun μ => ‖(u : FourTorus L m) μ‖) / meshSize L j :=
    fun u => by rw [supLengthInMesh, torusSupNorm_eq_sup']
  have hN : (sitesPerSide L m j : ℝ) * meshSize L j = torusSide L m := by
    have e1 : (((m : ℤ) + j).toNat : ℤ) = (m : ℤ) + j := Int.toNat_of_nonneg hmj
    have e2 : (L : ℝ) ^ (((m : ℤ) + j).toNat) = (L : ℝ) ^ ((m : ℤ) + j) := by
      rw [← zpow_natCast, e1]
    simp only [sitesPerSide, torusSide, meshSize]
    push_cast
    rw [e2, mul_assoc, ← zpow_add₀ hLpos.ne']
    simp
  have hrep : ∀ u : Site L m j, ∃ n : Fin 4 → ℤ,
      (∀ μ, (u : FourTorus L m) μ = (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) ∧
      (∀ μ, ‖(u : FourTorus L m) μ‖ = |(n μ : ℝ)| * meshSize L j) := by
    intro u
    obtain ⟨n', hn'⟩ := u.2
    set r : Fin 4 → ℤ := fun μ => round ((torusSide L m)⁻¹ * ((n' μ : ℝ) * meshSize L j)) with hr
    refine ⟨fun μ => n' μ - r μ * (sitesPerSide L m j : ℤ), fun μ => ?_, fun μ => ?_⟩
    · rw [hn' μ]
      have e : (((n' μ - r μ * (sitesPerSide L m j : ℤ) : ℤ) : ℝ) * meshSize L j) =
          (n' μ : ℝ) * meshSize L j - (r μ : ℝ) * torusSide L m := by
        push_cast
        rw [← hN]; ring
      rw [e, AddCircle.coe_sub]
      have h0 : (((r μ : ℝ) * torusSide L m : ℝ) : AddCircle (torusSide L m)) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨r μ, by simp⟩
      rw [h0, sub_zero]
    · rw [hn' μ, AddCircle.norm_eq]
      have e : (n' μ : ℝ) * meshSize L j -
          (round ((torusSide L m)⁻¹ * ((n' μ : ℝ) * meshSize L j)) : ℝ) * torusSide L m =
          ((n' μ - r μ * (sitesPerSide L m j : ℤ) : ℤ) : ℝ) * meshSize L j := by
        have hrμ : (round ((torusSide L m)⁻¹ * ((n' μ : ℝ) * meshSize L j)) : ℤ) = r μ := rfl
        rw [hrμ]
        push_cast
        rw [← hN]; ring
      rw [e, abs_mul, abs_of_pos hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · choose n hn hn' using hrep
    have hinj : Function.Injective n := by
      intro u v huv
      apply Subtype.ext
      funext μ
      rw [hn u μ, hn v μ, huv]
    have hbound : ∀ u μ, |(n u μ : ℝ)| ≤ sitesPerSide L m j := by
      intro u μ
      have hs : 0 < torusSide L m := mul_pos two_pos (pow_pos hLpos m)
      have h1 := AddCircle.norm_le_half_period (torusSide L m) hs.ne' (x := (u : FourTorus L m) μ)
      rw [abs_of_pos hs, hn' u μ] at h1
      have : |(n u μ : ℝ)| * meshSize L j ≤ (sitesPerSide L m j : ℝ) * meshSize L j := by
        rw [hN]; linarith
      exact le_of_mul_le_mul_right this hh
    have hset : Set.Finite {f : Fin 4 → ℤ | ∀ μ, f μ ∈
        Set.Icc (-(sitesPerSide L m j : ℤ)) (sitesPerSide L m j : ℤ)} :=
      Set.Finite.pi' fun _ => Set.finite_Icc _ _
    refine Finite.of_injective (fun u => (⟨n u, ?_⟩ : hset.toFinset)) ?_
    · rw [Set.Finite.mem_toFinset]
      intro μ
      have := hbound u μ
      rw [abs_le] at this
      constructor
      · have h := this.1; exact_mod_cast h
      · have h := this.2; exact_mod_cast h
    · intro u v huv
      exact hinj (congrArg Subtype.val huv)
  · intro x y
    rw [torusSupNorm_eq_sup', torusSupNorm_eq_sup', torusSupNorm_eq_sup']
    refine Finset.sup'_le _ _ fun μ _ => ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact Finset.le_sup' (fun μ => ‖x μ‖) (Finset.mem_univ μ)
    · exact Finset.le_sup' (fun μ => ‖y μ‖) (Finset.mem_univ μ)
  · intro x
    rw [torusSupNorm_eq_sup', torusSupNorm_eq_sup']
    simp
  · intro x
    rw [torusSupNorm_eq_sup']
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun μ => ‖x μ‖) (Finset.mem_univ 0))
  · intro x κ
    rw [torusSupNorm_eq_sup']
    exact Finset.le_sup' (fun μ => ‖x μ‖) (Finset.mem_univ κ)
  · rw [hnorm]
    simp
  · intro u
    rw [hnorm]
    refine div_nonneg ?_ hh.le
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun μ => ‖(u : FourTorus L m) μ‖) (Finset.mem_univ 0))
  · intro u
    rw [hnorm, hnorm]
    simp
  · intro u v
    rw [hnorm, hnorm, hnorm, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hh.le
    refine Finset.sup'_le _ _ fun μ _ => ?_
    have e : ((u + v : Site L m j) : FourTorus L m) μ = (u : FourTorus L m) μ + (v : FourTorus L m) μ := rfl
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact Finset.le_sup' (fun μ => ‖(u : FourTorus L m) μ‖) (Finset.mem_univ μ)
    · exact Finset.le_sup' (fun μ => ‖(v : FourTorus L m) μ‖) (Finset.mem_univ μ)
  · intro u
    obtain ⟨n, hn, hn'⟩ := hrep u
    refine ⟨n, hn, ?_⟩
    rw [hnorm]
    simp only [hn']
    apply le_antisymm
    · rw [div_le_iff₀ hh]
      refine Finset.sup'_le _ _ fun μ _ => ?_
      exact mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun μ => |(n μ : ℝ)|) (Finset.mem_univ μ)) hh.le
    · refine Finset.sup'_le _ _ fun μ _ => ?_
      rw [le_div_iff₀ hh]
      exact Finset.le_sup' (fun μ => |(n μ : ℝ)| * meshSize L j) (Finset.mem_univ μ)
end HessianOfTheMainTerm
end YangMills.Construction
