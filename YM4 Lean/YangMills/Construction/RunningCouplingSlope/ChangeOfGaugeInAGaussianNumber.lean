import YangMills.Construction.RunningCouplingSlope.VolumeFactorsOfLinearMaps
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearConstraint
def kerMapOfCompEq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {Q Q' : E →ₗ[ℝ] F} (τ : E →ₗ[ℝ] E) (hτ : Q ∘ₗ τ = Q') :
    LinearMap.ker Q' →ₗ[ℝ] LinearMap.ker Q :=
  τ.restrict fun v hv => by
    have h₁ : Q (τ v) = Q' v := LinearMap.congr_fun hτ v
    exact LinearMap.mem_ker.mpr (h₁.trans (LinearMap.mem_ker.mp hv))
def GaugeChangeGaussianIdentity : Prop :=
  ∀ (G A Gc C : Type)
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc) (m : A →ₗ[ℝ] Gc)
    (T : QuadraticForm ℝ (LinearMap.ker Q)),
    Function.Surjective Q →
    r ∘ₗ LinearMap.adjoint r = LinearMap.id →
    Q ∘ₗ D = Dc ∘ₗ r →
    Function.Bijective ((r + m ∘ₗ D) ∘ₗ LinearMap.adjoint r) →
    Function.Injective (D ∘ₗ (LinearMap.ker r).subtype) →
    (∀ v, 0 ≤ T v) →
    (∀ v : LinearMap.ker Q, T v = 0 ↔ (v : A) ∈ (LinearMap.ker r).map D) →
    Function.Bijective (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ m : A →ₗ[ℝ] A) ∧
    LinearMap.det (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ m : A →ₗ[ℝ] A) =
      LinearMap.det ((r + m ∘ₗ D) ∘ₗ LinearMap.adjoint r) ∧
    ∃ h : Q ∘ₗ (LinearMap.id + D ∘ₗ LinearMap.adjoint r ∘ₗ m) = Q + Dc ∘ₗ m,
      ∀ (Y Y' : Type)
        [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
        (l : A →ₗ[ℝ] Y) (l' : A →ₗ[ℝ] Y'),
        Function.Bijective (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) →
        Function.Bijective (l' ∘ₗ D ∘ₗ (LinearMap.ker (r + m ∘ₗ D)).subtype) →
        GaussianConstraint.constrainedGaussianNumber Q (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
            absDetOfMap (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) =
          LinearMap.det ((r + m ∘ₗ D) ∘ₗ LinearMap.adjoint (r + m ∘ₗ D)) ^ (1 / 2 : ℝ) *
            GaussianConstraint.constrainedGaussianNumber (Q + Dc ∘ₗ m)
              (T.comp (kerMapOfCompEq _ h) +
                (normSqForm l').comp (LinearMap.ker (Q + Dc ∘ₗ m)).subtype) *
            absDetOfMap (l' ∘ₗ D ∘ₗ (LinearMap.ker (r + m ∘ₗ D)).subtype)
end YangMills.Construction.LinearConstraint
end
