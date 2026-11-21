import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsATotal
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsCarried
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsGaugeInvariant
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTwiceDifferentiable
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages (UnitQuaternion)
open YangMills.Construction.TorusFields Filter
namespace YangMills.Construction.SlopeCoefficient
private theorem unitary_eq_sphere :
    (unitary ℍ[ℝ] : Set ℍ[ℝ]) = Metric.sphere (0 : ℍ[ℝ]) 1 := by
  ext q
  simp only [SetLike.mem_coe, mem_sphere_zero_iff_norm]
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star]
  constructor
  · rintro ⟨h, -⟩
    have h1 : Quaternion.normSq q = 1 := by simpa using congrArg (fun z : ℍ[ℝ] => z.re) h
    have h2 : ‖q‖ * ‖q‖ = 1 := by rw [← Quaternion.normSq_eq_norm_mul_self, h1]
    nlinarith [norm_nonneg q]
  · intro h
    have h1 : Quaternion.normSq q = 1 := by rw [Quaternion.normSq_eq_norm_mul_self, h]; norm_num
    rw [h1]
    simp
private instance : ConnectedSpace UnitQuaternion := by
  have h : IsConnected (unitary ℍ[ℝ] : Set ℍ[ℝ]) := by
    rw [unitary_eq_sphere]
    exact isConnected_sphere (by rw [Quaternion.rank_eq_four]; norm_num) 0 zero_le_one
  exact isConnected_iff_connectedSpace.mp h
variable {n : ℕ}
private def globalRotate (g : UnitQuaternion) (V : TorusField n) : TorusField n :=
  gaugeTransform (fun _ => g) V
private theorem globalRotate_one (V : TorusField n) : globalRotate 1 V = V := by
  funext x i
  simp [globalRotate, gaugeTransform]
private theorem globalRotate_mul (g h : UnitQuaternion) (V : TorusField n) :
    globalRotate (g * h) V = globalRotate g (globalRotate h V) := by
  funext x i
  simp [globalRotate, gaugeTransform, mul_assoc]
private theorem globalRotate_trivialField (g : UnitQuaternion) :
    globalRotate g (trivialField n) = trivialField n := by
  funext x i
  simp [globalRotate, gaugeTransform, trivialField]
private theorem continuous_globalRotate :
    Continuous fun p : TorusField n × UnitQuaternion => globalRotate p.2 p.1 := by
  refine continuous_pi fun x => continuous_pi fun i => ?_
  have h2 : Continuous fun p : TorusField n × UnitQuaternion => p.1 x i :=
    (continuous_apply i).comp ((continuous_apply x).comp continuous_fst)
  exact (continuous_snd.mul h2).mul continuous_snd.inv
private theorem constant_invariant_of_local {G : TorusField n → ℝ}
    (hG : ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
      G (gaugeTransform p.1 p.2) = G p.2) (g : UnitQuaternion) :
    ∀ᶠ V in 𝓝 (trivialField n), G (gaugeTransform (fun _ => g) V) = G V := by
  rw [nhds_prod_eq, eventually_prod_iff] at hG
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hG
  have hN : ∀ᶠ V in 𝓝 (trivialField n), ∀ h ∈ (Set.univ : Set UnitQuaternion),
      pb (globalRotate h V) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun h _ => ?_
    have ht : Tendsto (fun p : TorusField n × UnitQuaternion => globalRotate p.2 p.1)
        (𝓝 (trivialField n, h)) (𝓝 (trivialField n)) := by
      have := (continuous_globalRotate (n := n)).tendsto (trivialField n, h)
      simpa only [globalRotate_trivialField] using this
    exact ht.eventually hpb
  let S : Subgroup UnitQuaternion :=
    { carrier := {h | ∀ V, (∀ h', pb (globalRotate h' V)) → G (globalRotate h V) = G V}
      one_mem' := fun V _ => by rw [globalRotate_one]
      mul_mem' := fun {h h'} hh hh' V hV => by
        have hV' : ∀ h'', pb (globalRotate h'' (globalRotate h' V)) := fun h'' => by
          rw [← globalRotate_mul]
          exact hV _
        rw [globalRotate_mul, hh _ hV', hh' _ hV]
      inv_mem' := fun {h} hh V hV => by
        have hV' : ∀ h'', pb (globalRotate h'' (globalRotate h⁻¹ V)) := fun h'' => by
          rw [← globalRotate_mul]
          exact hV _
        have e := hh _ hV'
        rw [← globalRotate_mul, mul_inv_cancel, globalRotate_one] at e
        exact e.symm }
  have hopen : (S : Set UnitQuaternion) ∈ 𝓝 (1 : UnitQuaternion) := by
    have hc : Tendsto (fun h : UnitQuaternion => (fun _ => h : TorusSite n → UnitQuaternion))
        (𝓝 1) (𝓝 1) :=
      (continuous_pi fun _ => continuous_id).tendsto' _ _ rfl
    filter_upwards [hc.eventually hpa] with h hh V hV
    have h1 : pb V := by
      have := hV 1
      rwa [globalRotate_one] at this
    exact hab hh h1
  have htop : S = ⊤ := by
    have ho : IsOpen (S : Set UnitQuaternion) := Subgroup.isOpen_of_mem_nhds S hopen
    have hcl : IsClosed (S : Set UnitQuaternion) := Subgroup.isClosed_of_isOpen S ho
    have := (IsClopen.eq_univ ⟨hcl, ho⟩ ⟨1, S.one_mem⟩)
    exact SetLike.coe_injective (by simpa using this)
  filter_upwards [hN] with V hV
  have hg : g ∈ S := by simp [htop]
  exact hg V fun h' => hV h' (Set.mem_univ _)
theorem stepGaugeTotal_isGaugeTotal (hs : RunningCouplingSlope.StepGaugeTotalContDiff)
    (hg : StepGaugeTotalInvariant)
    (hc : RunningCouplingSlope.StepGaugeTotalIsometryInvariant) : StepGaugeTotalIsGaugeTotal := by
  intro a ha L hL t ρ h0 hρ
  filter_upwards [hs a ha L hL t ρ h0 hρ, hg a ha L hL t ρ h0 hρ, hc a ha L hL t ρ h0 hρ]
    with n h₁ h₂ h₃
  exact ⟨h₁, h₂, fun g => constant_invariant_of_local h₂ g, h₃⟩
end YangMills.Construction.SlopeCoefficient
end
