import YangMills.Construction.ResponseInTheExpansion.DisplacementsNearSites
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
private theorem circleSub_eq_of_lift (N : ℕ) (hN : 0 < N) (u v w : ℝ) (k : ℤ) (h : u - v = w + k * N)
    (hw : |w| < (N : ℝ) / 2) :
    LinearResponse.circleSub N u v = w := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv : (u - v) / N = w / N + k := by
    rw [h]
    field_simp
  have hr : round (w / (N : ℝ)) = 0 := by
    rw [round_eq_zero_iff]
    have h1 := abs_lt.mp hw
    constructor
    · rw [le_div_iff₀ hN']
      linarith [h1.1]
    · rw [div_lt_iff₀ hN']
      linarith [h1.2]
  simp only [LinearResponse.circleSub]
  rw [hdiv, round_add_intCast, hr, h]
  push_cast
  ring
private theorem exists_lift_torusDisplacement (N : ℕ) (x y : TorusFields.TorusSite N) (μ : Fin 4) :
    ∃ k : ℤ, ((y μ).val : ℝ) - (x μ).val = LinearResponse.torusDisplacement x y μ + k * N := by
  refine ⟨round ((((y μ).val : ℝ) - (x μ).val) / N), ?_⟩
  simp only [LinearResponse.torusDisplacement, LinearResponse.circleSub]
  ring
private theorem exists_lift_valMinAbs (N : ℕ) [NeZero N] (a x : TorusFields.TorusSite N) (μ : Fin 4) :
    ∃ k : ℤ, ((a μ).val : ℝ) - (x μ).val = ((a μ - x μ).valMinAbs : ℝ) + k * N := by
  have h1 : (((a μ - x μ).valMinAbs : ℤ) : ZMod N) = (((a μ).val : ℤ) - ((x μ).val : ℤ) : ℤ) := by
    rw [ZMod.coe_valMinAbs]
    push_cast
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  refine ⟨k, ?_⟩
  have : (((a μ).val : ℤ) - ((x μ).val : ℤ)) - (a μ - x μ).valMinAbs = (N : ℤ) * k := hk
  have h2 : (((a μ).val : ℝ) - (x μ).val) - ((a μ - x μ).valMinAbs : ℝ) = (N : ℝ) * k := by exact_mod_cast this
  linarith
private theorem abs_valMinAbs_le_supDist (N : ℕ) (a x : TorusFields.TorusSite N) (μ : Fin 4) :
    |((a μ - x μ).valMinAbs : ℝ)| ≤ (TorusFields.supDist a x : ℝ) := by
  have h1 : (a μ - x μ).valMinAbs.natAbs ≤ TorusFields.supDist a x :=
    Finset.le_sup (f := fun i => (a i - x i).valMinAbs.natAbs) (Finset.mem_univ μ)
  have h2 : |((a μ - x μ).valMinAbs : ℝ)| = (((a μ - x μ).valMinAbs.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs]
    simp
  rw [h2]
  exact_mod_cast h1
theorem torusDisplacementNearSites : LinearResponse.TorusDisplacementNearSites := by
  intro N _ x y
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨fun a b hsmall μ => ?_, fun μ hsmall => ?_, fun u u' hu hu' hsmall μ => ?_⟩
  · obtain ⟨k₀, h₀⟩ := exists_lift_torusDisplacement N x y μ
    obtain ⟨k₁, h₁⟩ := exists_lift_valMinAbs N b y μ
    obtain ⟨k₂, h₂⟩ := exists_lift_valMinAbs N a x μ
    have ha := abs_valMinAbs_le_supDist N a x μ
    have hb := abs_valMinAbs_le_supDist N b y μ
    set α : ℝ := ((a μ - x μ).valMinAbs : ℝ)
    set β : ℝ := ((b μ - y μ).valMinAbs : ℝ)
    have hw : |LinearResponse.torusDisplacement x y μ + β - α| < (N : ℝ) / 2 := by
      have := hsmall μ
      calc _ ≤ |LinearResponse.torusDisplacement x y μ| + |β| + |α| := by
            refine (abs_sub _ _).trans ?_
            exact add_le_add (abs_add_le _ _) le_rfl
        _ ≤ |LinearResponse.torusDisplacement x y μ| + (TorusFields.supDist b y : ℝ) +
              (TorusFields.supDist a x : ℝ) := by linarith
        _ < _ := by linarith
    have heq : LinearResponse.torusDisplacement a b μ = LinearResponse.torusDisplacement x y μ + β - α := by
      refine circleSub_eq_of_lift N hN _ _ _ (k₀ + k₁ - k₂) ?_ hw
      push_cast
      linarith
    rw [heq]
    have : LinearResponse.torusDisplacement x y μ + β - α - LinearResponse.torusDisplacement x y μ = β - α := by ring
    rw [this]
    calc _ ≤ |β| + |α| := abs_sub _ _
      _ ≤ _ := by linarith
  · obtain ⟨k₀, h₀⟩ := exists_lift_torusDisplacement N x y μ
    refine circleSub_eq_of_lift N hN _ _ _ (-k₀) ?_ (by rwa [abs_neg])
    push_cast
    linarith
  · obtain ⟨k₀, h₀⟩ := exists_lift_torusDisplacement N x y μ
    set t : ℝ := u μ - (x μ).val with ht
    set t' : ℝ := u' μ - (y μ).val with ht'
    have h1 := hu μ
    have h2 := hu' μ
    have hd : |t' - t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hw : |LinearResponse.torusDisplacement x y μ + (t' - t)| < (N : ℝ) / 2 := by
      have := hsmall μ
      calc _ ≤ |LinearResponse.torusDisplacement x y μ| + |t' - t| := abs_add_le _ _
        _ ≤ |LinearResponse.torusDisplacement x y μ| + 1 := by linarith
        _ < _ := this
    have heq : LinearResponse.circleSub N (u' μ) (u μ) = LinearResponse.torusDisplacement x y μ + (t' - t) := by
      refine circleSub_eq_of_lift N hN _ _ _ k₀ ?_ hw
      simp only [ht, ht']
      linarith
    rw [heq]
    have : LinearResponse.torusDisplacement x y μ + (t' - t) - LinearResponse.torusDisplacement x y μ = t' - t := by ring
    rwa [this]
end YangMills.Construction.LinearResponse
end
