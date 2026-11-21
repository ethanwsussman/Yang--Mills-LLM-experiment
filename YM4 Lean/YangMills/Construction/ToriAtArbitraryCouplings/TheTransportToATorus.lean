import YangMills.Construction.ToriAtArbitraryCouplings.TheGradientNorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def HasCompactSupportWithin (A : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  s.IsCompactWrt .euclidean (s.closedSupport .euclidean f) ∧ s.closedSupport .euclidean f ⊆ A
def torusTransport (f : (Fin 4 → ℝ) → ℝ) : s.Point .torus → ℝ :=
  TestFunctions.periodize s.length f
end TorusSide
namespace TransportToTorus
def Properties : Prop :=
  ∀ (s : TorusSide) (S : Set (Fin 4 → ℝ)), TestFunctions.HasDiameterLE S (s.length / 2) →
    (∀ f : (Fin 4 → ℝ) → ℝ, s.HasCompactSupportWithin S f →
      (∀ (v : Fin 4 → ℝ) (k k' : Fin 4 → ℤ),
        f (v + TestFunctions.latticeTranslate s.length k) ≠ 0 →
        f (v + TestFunctions.latticeTranslate s.length k') ≠ 0 → k = k') ∧
      s.torusTransport f ∘ s.proj = TestFunctions.periodicSum s.length f ∧
      (∃! g : s.Point .torus → ℝ,
        g ∘ s.proj = TestFunctions.periodicSum s.length f) ∧
      (TestFunctions.IsBoundedFun f → TestFunctions.IsBoundedFun (s.torusTransport f) ∧
        TestFunctions.uniformNorm (s.torusTransport f) = TestFunctions.uniformNorm f) ∧
      s.closedSupport .torus (s.torusTransport f) = s.proj '' s.closedSupport .euclidean f ∧
      (s.IsC1Fun .euclidean f → s.IsC1Fun .torus (s.torusTransport f)) ∧
      (TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
        TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (s.torusTransport f) ∧
        s.lipConst .torus (s.torusTransport f) ≤ s.lipConst .euclidean f ∧
        ∀ m' : ℕ, s.sharpNormAt m' .torus (s.torusTransport f) ≤ s.sharpNormAt m' .euclidean f)) ∧
    ∀ f h : (Fin 4 → ℝ) → ℝ, s.HasCompactSupportWithin S f → s.HasCompactSupportWithin S h →
      (∀ α α' : ℝ, s.torusTransport (α • f + α' • h) =
        α • s.torusTransport f + α' • s.torusTransport h) ∧
      s.setDist .torus (s.closedSupport .torus (s.torusTransport f))
          (s.closedSupport .torus (s.torusTransport h)) =
        s.setDist .euclidean (s.closedSupport .euclidean f) (s.closedSupport .euclidean h)
end TransportToTorus
end YangMills.Construction.ToriAtArbitraryCouplings
end
