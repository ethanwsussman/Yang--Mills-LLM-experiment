import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GaussianConstraint
section AbsoluteDeterminant
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
def absDetInBases {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V)
    (c : OrthonormalBasis ι ℝ W) (f : V →ₗ[ℝ] W) : ℝ :=
  |(LinearMap.toMatrix b.toBasis c.toBasis f).det|
def absDet (f : V →ₗ[ℝ] W) : ℝ :=
  open Classical in
  if h : Module.finrank ℝ V = Module.finrank ℝ W then
    absDetInBases (stdOrthonormalBasis ℝ V) ((stdOrthonormalBasis ℝ W).reindex (finCongr h.symm)) f
  else 0
end AbsoluteDeterminant
def AbsDetIndependentOfBases : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (f : V →ₗ[ℝ] W),
    Function.Bijective f →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V)
        (c : OrthonormalBasis ι ℝ W), absDetInBases b c f = absDet f
section LinearData
variable {A C G Gc W : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
def constraintPreimage (Q : A →ₗ[ℝ] C) (Dc : Gc →ₗ[ℝ] C) : Submodule ℝ A :=
  (LinearMap.range Dc).comap Q
def shiftedGaugeMap (r : G →ₗ[ℝ] Gc) (N : A →ₗ[ℝ] Gc) (D : G →ₗ[ℝ] A) : G →ₗ[ℝ] Gc :=
  r + N ∘ₗ D
def shiftedConstraint (Q : A →ₗ[ℝ] C) (Dc : Gc →ₗ[ℝ] C) (N : A →ₗ[ℝ] Gc) : A →ₗ[ℝ] C :=
  Q + Dc ∘ₗ N
def gaugeRestrictKer (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q' : A →ₗ[ℝ] C) (r' : G →ₗ[ℝ] Gc)
    (h : Q' ∘ₗ D = Dc ∘ₗ r') : LinearMap.ker r' →ₗ[ℝ] LinearMap.ker Q' :=
  D.restrict fun x hx => by
    have hr : r' x = 0 := hx
    have hQ : Q' (D x) = Dc (r' x) := LinearMap.congr_fun h x
    rw [LinearMap.mem_ker, hQ, hr, map_zero]
def gaugeFixedForm {E K : Submodule ℝ A} (H : QuadraticForm ℝ E) (hK : K ≤ E)
    (Lf : K →ₗ[ℝ] W) : QuadraticForm ℝ K :=
  H.comp (Submodule.inclusion hK) + (LinearMap.BilinMap.toQuadraticMap (innerₗ W)).comp Lf
def gaugeFixedNumber (Q' : A →ₗ[ℝ] C) (r' : G →ₗ[ℝ] Gc)
    (T : QuadraticForm ℝ (LinearMap.ker Q')) (v : LinearMap.ker r' →ₗ[ℝ] W) : ℝ :=
  constrainedGaussianNumber Q' T * absDet v *
    LinearMap.det (r' ∘ₗ LinearMap.adjoint r') ^ (1 / 2 : ℝ)
end LinearData
def GaugeFixingIndependence : Prop :=
  AbsDetIndependentOfBases ∧
    ∀ (A C G Gc : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
      [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
      [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
      (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc),
      Function.Injective D → Function.Injective Dc →
      Function.Surjective Q → Function.Surjective r →
      Q ∘ₗ D = Dc ∘ₗ r →
      ∀ H : QuadraticForm ℝ (constraintPreimage Q Dc),
        (∀ x, 0 ≤ H x) →
        (∀ x, H x = 0 ↔ (x : A) ∈ LinearMap.range D) →
        ∃ c : ℝ, ∀ N : A →ₗ[ℝ] Gc,
          Function.Surjective (shiftedGaugeMap r N D) →
          Function.Surjective (shiftedConstraint Q Dc N) ∧
          0 < LinearMap.det (shiftedGaugeMap r N D ∘ₗ LinearMap.adjoint (shiftedGaugeMap r N D)) ∧
          ∃ (hD : shiftedConstraint Q Dc N ∘ₗ D = Dc ∘ₗ shiftedGaugeMap r N D)
            (hE : LinearMap.ker (shiftedConstraint Q Dc N) ≤ constraintPreimage Q Dc),
            ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
              (Lf : LinearMap.ker (shiftedConstraint Q Dc N) →ₗ[ℝ] W),
              Module.finrank ℝ W = Module.finrank ℝ (LinearMap.ker (shiftedGaugeMap r N D)) →
              Function.Bijective (Lf ∘ₗ gaugeRestrictKer D Dc _ _ hD) →
              (gaugeFixedForm H hE Lf).PosDef ∧
                gaugeFixedNumber (shiftedConstraint Q Dc N) (shiftedGaugeMap r N D)
                  (gaugeFixedForm H hE Lf) (Lf ∘ₗ gaugeRestrictKer D Dc _ _ hD) = c
end YangMills.Construction.GaussianConstraint
end
