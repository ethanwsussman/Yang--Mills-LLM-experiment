import YangMills.Construction.RotationInvariance.GramKernelOnLabelledTubePoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
open scoped InnerProductSpace
namespace EuclideanFunctionals
namespace PlaneDataWithAperture
variable {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S)
def mollifierVector {n : ℕ} (ε : ℝ) (ρ : ℕ+ → RealPlane → ℝ) (j : ℕ+) (ψ : Fin n → realLabels)
    (x : Fin n → ℂ × ℂ) : d.base.sigma.space :=
  d.base.sigma.productVec ε (fun _ => ofRealFun (ρ j))
    (fun i => (ψ i : RealPlane → ℝ)) x
def mollifierGramValue {n n' : ℕ} (ε : ℝ) (ρ : ℕ+ → RealPlane → ℝ) (j : ℕ+)
    (ψ : Fin n → realLabels) (ψ' : Fin n' → realLabels) (x : Fin n → ℂ × ℂ)
    (y : Fin n' → ℂ × ℂ) : ℂ :=
  if h : 2 ≤ n + n' then
    d.mollifiedKernel (q := n + n' - 1) ε ρ
      (fun k => (gramLabelOrder ψ ψ' (Fin.cast (by omega) k) : RealPlane → ℝ)) j
      (gramKernelArgs x y)
  else if n + n' = 0 then 1 else 0
end PlaneDataWithAperture
namespace MollifierInnerAtRealPoints
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (ε : ℝ),
    ε ∈ Set.Ioc (0 : ℝ) 1 → ∀ ρ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier ε ρ →
    ∀ (j : ℕ+) (n n' : ℕ) (ψ : Fin n → realLabels) (ψ' : Fin n' → realLabels),
    ∀ a ∈ orderedTimeTuples n ε, ∀ b ∈ orderedTimeTuples n' ε,
      ⟪d.mollifierVector ε ρ j ψ (realTuple a), d.mollifierVector ε ρ j ψ' (realTuple b)⟫_ℂ =
        d.mollifierGramValue ε ρ j ψ ψ' (realTuple a) (realTuple b)
end MollifierInnerAtRealPoints
end EuclideanFunctionals
end YangMills.Construction
end
