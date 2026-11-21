import YangMills.Construction.Lattice.SourceDiscAndSourceClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound.SourceDiskAndClass
open TestFunctions TorusMetric
theorem torusEuclidNorm_le_abs {S : ℝ} (hS : S ≠ 0) (x : Torus4 S) :
    torusEuclidNorm x ≤ |S| := by
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S v = x := funext hv
  have hin : euclidNormVec v ∈ euclidNormVec '' (torusProj S ⁻¹' {x}) := ⟨v, hproj, rfl⟩
  have hlow : BddBelow (euclidNormVec '' (torusProj S ⁻¹' {x})) :=
    ⟨0, by rintro _ ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (csInf_le hlow hin).trans ?_
  have hcoord : ∀ μ, v μ ^ 2 ≤ (|S| / 2) ^ 2 := fun μ => by
    have habs : |v μ| ≤ |S| / 2 := (hv' μ).trans_le (AddCircle.norm_le_half_period S hS)
    rw [← sq_abs (v μ)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsq : ∑ μ, v μ ^ 2 ≤ |S| ^ 2 := by
    calc ∑ μ, v μ ^ 2 ≤ ∑ _μ : Fin 4, (|S| / 2) ^ 2 := Finset.sum_le_sum fun μ _ => hcoord μ
      _ = |S| ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  unfold euclidNormVec
  exact Real.sqrt_le_iff.mpr ⟨abs_nonneg _, hsq⟩
theorem isBoundedFun_of_lipschitz {S : ℝ} (hS : S ≠ 0) {f : Torus4 S → ℝ}
    (hf : IsLipschitzFor euclidDistTorus f) : IsBoundedFun f := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖f 0‖ + C * |S|, fun x => ?_⟩
  have hdiff : ‖f x - f 0‖ ≤ C * |S| :=
    (hf x 0).trans (mul_le_mul_of_nonneg_left (torusEuclidNorm_le_abs hS _) hC)
  have hrev := norm_sub_norm_le (f x) (f 0)
  linarith
theorem complexSource_isBoundedFun {L m n : ℕ} {f : Fin n → PeriodicLattice.FourTorus L m → ℝ}
    (hf : ∀ i, IsBoundedFun (f i)) (z : Fin n → ℂ) :
    IsBoundedFun (PeriodicLattice.complexSource f z) := by
  choose C hC using hf
  refine ⟨∑ i, ‖z i‖ * C i, fun x => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hC i x) (norm_nonneg _)
theorem torusSide_ne_zero (D : Setup) : PeriodicLattice.torusSide D.L (D.m : ℕ) ≠ 0 := by
  have hL : D.L ≠ 0 := by
    have := D.isAdmissible.2
    omega
  have hLr : (D.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  exact mul_ne_zero two_ne_zero (pow_ne_zero _ hLr)
theorem statement_holds : Statement := by
  intro D n f ϱ hf hϱ
  have hbd : ∀ i, IsBoundedFun (f i) := fun i =>
    isBoundedFun_of_lipschitz (torusSide_ne_zero D) (hf.2 i)
  have hup : ∀ i, BddAbove (Set.range fun x => ‖f i x‖) := fun i => by
    obtain ⟨C, hC⟩ := hbd i
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hnn : ∀ i, 0 ≤ D.sharpNorm (f i) := fun i =>
    le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
  have horigin : (0 : Fin n → ℂ) ∈ D.disc ϱ f := by
    show ∑ i, ‖(0 : Fin n → ℂ) i‖ * D.sharpNorm (f i) < ϱ
    simpa using hϱ
  refine ⟨fun i => ⟨hbd i, hup i, hf.2 i, hnn i, fun h x => ?_⟩, fun z => ?_, ?_, ?_, ?_, horigin,
    ?_, ?_⟩
  · have hx : ‖f i x‖ ≤ uniformNorm (f i) := le_ciSup (hup i) x
    have hu : uniformNorm (f i) ≤ D.sharpNorm (f i) := le_max_left _ _
    rw [h] at hu
    exact norm_le_zero_iff.mp (hx.trans hu)
  · exact complexSource_isBoundedFun hbd z
  · show IsOpen {z : Fin n → ℂ | ∑ i, ‖z i‖ * D.sharpNorm (f i) < ϱ}
    exact isOpen_lt
      (continuous_finsetSum _ fun i _ => (continuous_apply i).norm.mul continuous_const)
      continuous_const
  · intro z hz w hw a c ha hc hac
    show ∑ i, ‖(a • z + c • w) i‖ * D.sharpNorm (f i) < ϱ
    have hle : ∑ i, ‖(a • z + c • w) i‖ * D.sharpNorm (f i) ≤
        a • (∑ i, ‖z i‖ * D.sharpNorm (f i)) + c • (∑ i, ‖w i‖ * D.sharpNorm (f i)) := by
      rw [smul_eq_mul, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hcomb : ‖(a • z + c • w) i‖ ≤ a * ‖z i‖ + c * ‖w i‖ := by
        simp only [Pi.add_apply, Pi.smul_apply]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
      calc ‖(a • z + c • w) i‖ * D.sharpNorm (f i)
          ≤ (a * ‖z i‖ + c * ‖w i‖) * D.sharpNorm (f i) :=
            mul_le_mul_of_nonneg_right hcomb (hnn i)
        _ = a * (‖z i‖ * D.sharpNorm (f i)) + c * (‖w i‖ * D.sharpNorm (f i)) := by ring
    exact lt_of_le_of_lt hle (convex_Iio ϱ (Set.mem_Iio.mpr hz) (Set.mem_Iio.mpr hw) ha hc hac)
  · have hconj : ∀ z : Fin n → ℂ,
        (∑ i, ‖starRingEnd ℂ (z i)‖ * D.sharpNorm (f i)) =
          ∑ i, ‖z i‖ * D.sharpNorm (f i) := fun z =>
      Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_conj]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show ∑ i, ‖starRingEnd ℂ (z i)‖ * D.sharpNorm (f i) < ϱ
      rw [hconj]
      exact hz
    · intro hw
      refine ⟨fun i => starRingEnd ℂ (w i), ?_, funext fun i => Complex.conj_conj _⟩
      show ∑ i, ‖starRingEnd ℂ (w i)‖ * D.sharpNorm (f i) < ϱ
      rw [hconj]
      exact hw
  · intro w hw
    obtain ⟨k, g, z, hg, -, rfl⟩ := (D.mem_sources_iff ϱ w).1 hw
    exact complexSource_isBoundedFun
      (fun i => isBoundedFun_of_lipschitz (torusSide_ne_zero D) (hg.2 i)) z
  · refine (D.mem_sources_iff ϱ 0).2 ⟨n, f, 0, hf, horigin, ?_⟩
    funext x
    simp [PeriodicLattice.complexSource]
end YangMills.Construction.TorusBound.SourceDiskAndClass
end
