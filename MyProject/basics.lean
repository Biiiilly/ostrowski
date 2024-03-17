/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Seminorm related definitions
## Tags
ring_norm, equivalent
-/

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def is_nonarchimedean {α : Type*} [HAdd α α α] {β : Type*} [Max β] [LE β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

lemma is_nonarchimedean_def {α : Type*} [HAdd α α α] {β : Type*} [Max β] [LE β] (f : α → β) :
is_nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) := by rfl

/-- A function `f : α → β` is `multiplicative` if it satisfies the equality
  `f (a * b) = (f a) * (f b)` for all `a, b ∈ α`. -/
def mul_eq {α : Type*} [HMul α α α] {β : Type*} [HMul β β β] (f : α → β) : Prop :=
∀ r s, f (r * s) = (f r) * (f s)

lemma mul_eq_def {α : Type*} [HMul α α α] {β : Type*} [HMul β β β] (f : α → β) :
mul_eq f ↔ ∀ r s, f (r * s) = (f r) * (f s) := by rfl

namespace mul_ring_norm

end mul_ring_norm
