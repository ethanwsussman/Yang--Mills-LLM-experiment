import YangMills.Construction.Dirichlet.CubeCoverAndWalks
import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.CubeBump
def productBump (d : ℕ) (w : Fin d → ℝ) : ℝ := ∏ μ, bumpProfile (w μ)
theorem bumpProfile_eq_zero_of_lt_abs {x : ℝ} (h : 2 / 3 < |x|) : bumpProfile x = 0 :=
  bumpProfile_isEvenBump.eq_zero_of_not_mem x fun hx => by
    have := abs_le.mpr ⟨hx.1, hx.2⟩
    linarith
theorem productBump_contDiff (d : ℕ) : ContDiff ℝ ∞ (productBump d) :=
  contDiff_prod fun μ _ => bumpProfile_isEvenBump.contDiff.comp (contDiff_apply ℝ ℝ μ)
theorem addCircle_coe_eq_iff {S x y : ℝ} :
    (x : AddCircle S) = (y : AddCircle S) ↔ ∃ m : ℤ, x - y = m * S := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact exists_congr fun m => by rw [zsmul_eq_mul, eq_comm]
theorem le_abs_sub_of_coe_eq {S x y : ℝ} (hS : 0 < S) (h : (x : AddCircle S) = (y : AddCircle S))
    (hne : x ≠ y) : S ≤ |x - y| := by
  obtain ⟨m, hm⟩ := addCircle_coe_eq_iff.mp h
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [sub_eq_zero] using hm
  have h₁ : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
  rw [hm, abs_mul, abs_of_pos hS]
  nlinarith
theorem circleRep_spec {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    circleRep θ ∈ Ioc (-(S / 2)) (S / 2) ∧ ((circleRep θ : ℝ) : AddCircle S) = θ := by
  have : Fact (0 < S) := ⟨hS⟩
  have hmem := (AddCircle.equivIoc S (-(S / 2)) θ).2
  have hend : -(S / 2) + S = S / 2 := by ring
  unfold circleRep
  exact Classical.epsilon_spec (p := fun v : ℝ => v ∈ Ioc (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ)
    ⟨_, ⟨hmem.1, hmem.2.trans_eq hend⟩, AddCircle.coe_equivIoc⟩
theorem abs_circleRep_le_half {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    |circleRep θ| ≤ S / 2 := by
  have h := (circleRep_spec hS θ).1
  exact abs_le.mpr ⟨h.1.le, h.2⟩
theorem abs_circleRep_le {S : ℝ} (hS : 0 < S) (w : ℝ) :
    |circleRep (w : AddCircle S)| ≤ |w| := by
  have hc := (circleRep_spec hS (w : AddCircle S)).2
  have hh := abs_circleRep_le_half hS (w : AddCircle S)
  by_cases hne : circleRep (w : AddCircle S) = w
  · rw [hne]
  · have h₁ := le_abs_sub_of_coe_eq hS hc hne
    have h₂ := abs_sub (circleRep (w : AddCircle S)) w
    linarith
theorem bumpProfile_circleRep_div {S σ t : ℝ} (hσ : 0 < σ) (h2 : 2 * σ ≤ S)
    (ht : |t| < S - 2 / 3 * σ) :
    bumpProfile (circleRep (t : AddCircle S) / σ) = bumpProfile (t / σ) := by
  have hS : 0 < S := by linarith
  have hc := (circleRep_spec hS (t : AddCircle S)).2
  have hh := abs_circleRep_le_half hS (t : AddCircle S)
  by_cases hne : circleRep (t : AddCircle S) = t
  · rw [hne]
  · have h₁ := le_abs_sub_of_coe_eq hS hc hne
    have h₂ := abs_sub (circleRep (t : AddCircle S)) t
    have e₁ : bumpProfile (circleRep (t : AddCircle S) / σ) = 0 := by
      apply bumpProfile_eq_zero_of_lt_abs
      rw [abs_div, abs_of_pos hσ, lt_div_iff₀ hσ]
      linarith
    have e₂ : bumpProfile (t / σ) = 0 := by
      apply bumpProfile_eq_zero_of_lt_abs
      rw [abs_div, abs_of_pos hσ, lt_div_iff₀ hσ]
      linarith
    rw [e₁, e₂]
def periodicBump {d : ℕ} (S σ : ℝ) (c : PeriodicTorus d S) (y : Fin d → ℝ) : ℝ :=
  ∏ μ, bumpProfile (circleRep (torusProj d S y μ - c μ) / σ)
theorem periodicBump_eventuallyEq {d : ℕ} {S σ : ℝ} (hσ : 0 < σ) (h2 : 2 * σ ≤ S)
    (c : PeriodicTorus d S) (v : Fin d → ℝ) :
    ∃ b : Fin d → ℝ,
      periodicBump S σ c =ᶠ[𝓝 v] fun y => productBump d (σ⁻¹ • (y - b)) := by
  have hSpos : 0 < S := by linarith
  let shift : Fin d → ℝ := fun μ => v μ - circleRep (torusProj d S v μ - c μ)
  refine ⟨shift, ?_⟩
  have hshift : ∀ μ, (shift μ : AddCircle S) = c μ := by
    intro μ
    have hr := (circleRep_spec hSpos (torusProj d S v μ - c μ)).2
    simp only [shift, AddCircle.coe_sub, hr]
    simp [torusProj]
  have hclose : ∀ μ, ∀ᶠ y : Fin d → ℝ in 𝓝 v, |y μ - shift μ| < S - 2 / 3 * σ := by
    intro μ
    have hv : v μ - shift μ = circleRep (torusProj d S v μ - c μ) := by
      simp only [shift]
      ring
    have hhalf := abs_circleRep_le_half hSpos (torusProj d S v μ - c μ)
    have hat : |v μ - shift μ| < S - 2 / 3 * σ := by
      rw [hv]
      linarith
    have hcts : ContinuousAt (fun y : Fin d → ℝ => |y μ - shift μ|) v :=
      (continuous_abs.comp ((continuous_apply μ).sub continuous_const)).continuousAt
    exact hcts.eventually_lt continuousAt_const hat
  filter_upwards [eventually_all.mpr hclose] with y hy
  refine Finset.prod_congr rfl fun μ _ => ?_
  have hy' : torusProj d S y μ - c μ = ((y μ - shift μ : ℝ) : AddCircle S) := by
    rw [AddCircle.coe_sub, hshift]
    rfl
  rw [hy', bumpProfile_circleRep_div hσ h2 (hy μ)]
  simp [div_eq_inv_mul]
theorem periodicBump_contDiff {d : ℕ} {S σ : ℝ} (hσ : 0 < σ) (h2 : 2 * σ ≤ S)
    (c : PeriodicTorus d S) : ContDiff ℝ ∞ (periodicBump S σ c) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  obtain ⟨b, hb⟩ := periodicBump_eventuallyEq hσ h2 c v
  have h : ContDiff ℝ ∞ fun y : Fin d → ℝ => productBump d (σ⁻¹ • (y - b)) :=
    (productBump_contDiff d).comp ((contDiff_id.sub contDiff_const).const_smul σ⁻¹)
  exact h.contDiffAt.congr_of_eventuallyEq hb
theorem supNorm_torusProj_le {d : ℕ} {S : ℝ} (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro r ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem continuous_torusProj {d : ℕ} {S : ℝ} : Continuous (torusProj d S) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
end YangMills.Construction.Dirichlet.CubeBump
