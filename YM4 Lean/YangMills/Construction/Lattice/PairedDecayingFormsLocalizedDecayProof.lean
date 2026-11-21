import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.PointDecayingOneForms
import YangMills.Construction.Lattice.FieldNormProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace PairedDecay
section Cube
variable {s : Mesh N} {ι : Type} [Fintype ι]
end Cube
namespace Decaying
variable {L j : ℕ} (S : Scales d L j N)
variable {S} {δ k : ℝ} {kh : ℝ → ℝ} {p : Torus d N} {g : OneForm d S.fineMesh}
theorem norm_mulLeft_gradGrad_le (hf : SiteFunNormFacts d S.fineMesh) (hk : 0 ≤ k)
    (h : S.DecaysFromPoint δ k kh p g) (u : Torus d N)
    (ζ : SiteFun d S.fineMesh) (hζ : SiteFun.SupportedIn ζ (closedMaxBall S.fineMesh u)) :
    ‖MultiField.mulLeft ζ (S.oneFormGradGrad g)‖ ≤
      k * Real.exp (-δ * taxicabDist u p) * SiteFun.maxNorm ζ := by
  by_cases hx : ∃ x, x ∈ closedMaxBall S.fineMesh u
  · obtain ⟨x, hx⟩ := hx
    exact (h u x hx ζ hζ).norm_mulLeft_gradGrad_le
  · have hz : MultiField.mulLeft ζ (S.oneFormGradGrad g) = 0 := by
      refine ScaledFun.ext fun q => ?_
      have hval : (MultiField.mulLeft ζ (S.oneFormGradGrad g)) q =
          ζ q.2 * (S.oneFormGradGrad g) q := rfl
      rw [hval, hζ q.2 fun hq => hx ⟨_, hq⟩, zero_mul]
      rfl
    rw [hz, norm_zero]
    have := hf.maxNorm_nonneg ζ
    positivity
end Decaying
section Sum
variable {L j : ℕ} (S : Scales d L j N) {ι : Type}
variable [Fintype ι]
end Sum
end PairedDecay
end YangMills.Construction.PeriodicLattice
