import Mathlib
set_option autoImplicit false
universe u
namespace YangMills.Construction.Conventions
noncomputable def boundNumber {α : Type u} [Nonempty α] (P : α → Prop) : α :=
  Classical.epsilon P
end YangMills.Construction.Conventions
