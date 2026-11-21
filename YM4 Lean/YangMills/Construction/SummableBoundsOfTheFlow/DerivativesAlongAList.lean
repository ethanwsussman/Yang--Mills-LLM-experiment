import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
namespace IteratedDerivative
def derivAlong {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) : List E → E → F
  | [] => f
  | v :: vs => fun x => fderiv ℝ (derivAlong f vs) x v
structure DerivAlongRules (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop where
  congr : ∀ (f g : E → F) (x : E) (vs : List E), f =ᶠ[𝓝 x] g → derivAlong f vs =ᶠ[𝓝 x] derivAlong g vs
  append : ∀ (f : E → F) (vs ws : List E), derivAlong f (vs ++ ws) = derivAlong (derivAlong f ws) vs
  contDiffAt : ∀ (f : E → F) (x : E) (n : ℕ) (vs : List E), ContDiffAt ℝ ((n + vs.length : ℕ) : WithTop ℕ∞) f x →
    ContDiffAt ℝ (n : WithTop ℕ∞) (derivAlong f vs) x
  iteratedFDeriv_eq : ∀ (f : E → F) (x : E) (n : ℕ) (v : Fin n → E), ContDiffAt ℝ (n : WithTop ℕ∞) f x →
    iteratedFDeriv ℝ n f x v = derivAlong f (List.ofFn v) x
  perm : ∀ (f : E → F) (x : E) (vs ws : List E), vs.Perm ws →
    ContDiffAt ℝ (vs.length : WithTop ℕ∞) f x → derivAlong f vs x = derivAlong f ws x
  add : ∀ (f g : E → F) (x : E) (vs : List E), ContDiffAt ℝ (vs.length : WithTop ℕ∞) f x →
    ContDiffAt ℝ (vs.length : WithTop ℕ∞) g x →
    derivAlong (fun y => f y + g y) vs x = derivAlong f vs x + derivAlong g vs x
  smul : ∀ (c : ℝ) (f : E → F) (x : E) (vs : List E), ContDiffAt ℝ (vs.length : WithTop ℕ∞) f x →
    derivAlong (fun y => c • f y) vs x = c • derivAlong f vs x
  smul_slot : ∀ (f : E → F) (x : E) (vs ws : List E) (c : ℝ) (v : E),
    ContDiffAt ℝ ((vs ++ v :: ws).length : WithTop ℕ∞) f x →
    derivAlong f (vs ++ (c • v) :: ws) x = c • derivAlong f (vs ++ v :: ws) x
  add_slot : ∀ (f : E → F) (x : E) (vs ws : List E) (v v' : E),
    ContDiffAt ℝ ((vs ++ v :: ws).length : WithTop ℕ∞) f x →
    derivAlong f (vs ++ (v + v') :: ws) x = derivAlong f (vs ++ v :: ws) x + derivAlong f (vs ++ v' :: ws) x
def DerivAlongRulesHold : Prop :=
  (∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F],
    DerivAlongRules E F) ∧
  ∀ (E E' F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (T : E' →L[ℝ] E) (x₀ : E) (y : E') (vs : List E'),
    ContDiffAt ℝ (vs.length : WithTop ℕ∞) f (x₀ + T y) →
    derivAlong (fun y' => f (x₀ + T y')) vs y = derivAlong f (vs.map T) (x₀ + T y)
end IteratedDerivative
end YangMills.Construction
end
