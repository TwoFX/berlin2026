/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option linter.unusedVariables false

#doc (Slides) "Proofs for programs, programs for proofs" =>
%%%
slideNumber := true
transition := "fade"
%%%


# Proofs for programs, programs for proofs
Julia Markus Himmel

Lean FRO

# Software verification approaches

Which options are there for writing verified software?

# Write in mainstream language, extract verification conditions

Examples:

* Aeneas (Rust → Lean)
* AutoCorres (C → Isabelle)
* Frama-C (C → SMT)
* Liquid Haskell (Haskell → SMT)

# Write in verification-aware system, extract to mainstream language

Examples:

* Dafny (to C# and others)
* Rocq (to OCaml)

# Write in verification-aware programming language

Examples:

* Idris 2
* Lean 4

:::fragment
Difference: no “phase separation” between code and proofs
:::

# Proofs about code

```lean
def addOne (n : Nat) : Nat :=
  n + 1

theorem addOne_pos : ∀ n, 0 < addOne n := by
  grind [addOne]
```

# Proofs inside code

```lean
def addProducts (left right : Array Nat) : Nat := Id.run do
  let mut ans := 0

  for h : i in 0...min left.size right.size do
    ans := ans + left[i] * right[i]

  return ans
```

:::fragment
```lean +error
def addProducts' (left right : Array Nat) : Nat := Id.run do
  let mut ans := 0

  for h : i in 0...max left.size right.size do
    ans := ans + left[i] * right[i]

  return ans
```
:::

# Proofs inside code

```lean -show
section
variable {arr : Array Nat} (_ha : 0 < arr.size)
```

Many operations in Lean come in three variants:
* Safe: *no* runtime check, needs proof: {lean}`arr[0]` or {lean}`arr[0]'(by grind)`
* Checked: runtime check, returns {lean}`Option`: {lean}`arr[1]?`
* Panicking: runtime check, panics: {lean}`arr[1]!`

:::fragment
Can write safe, efficient, and (with automation) user-friendly code.
:::

:::fragment
How does this work, and how far can we take this?
:::

# How does this work?

Lean has two main mechanisms for influencing the compiler with proofs:
* Runtime functions, and
* pattern matching on empty types

# Runtime functions

Lean has a runtime written in C++ for some primitives and I/O.

:::fragment
{lean}`arr[0]` desugars to a call into a runtime
function that performs the unsafe access.

```lean -show
end
```

```lean
@[extern "lean_array_fget"]
def Array.getInternal' {α : Type u} (a : @& Array α)
    (i : @& Nat) (h : i < a.size) : α :=
  a.toList.get ⟨i, h⟩
```

```cpp
static inline lean_obj_res lean_array_fget(b_lean_obj_arg a, b_lean_obj_arg i)
```

Lean's proof checking ensures that access is safe.

In the runtime, types and proofs no longer exist.
:::

# Matching on empty types

```lean +error
def firstOrZero (l : List Nat) : Nat :=
  match h : l ++ [0] with
  | x :: _ => x
  | [] => -- Unreachable, what to put here?
```

:::fragment
```lean
def firstOrZero' (l : List Nat) : Nat :=
  match h : l ++ [0] with
  | x :: _ => x
  | [] => unreachable! -- Runtime check + panic
```


```lean
def firstOrZero'' (l : List Nat) : Nat :=
  match h : l ++ [0] with
  | x :: _ => x
  | [] =>
    have false : False := by simp at h
    nomatch false
```

Inhabit {lean}`False`, an uninhabited type, from the contradictory context, and
match on it. There are no cases!

The compiler has special handling for this.
:::


# Matching on empty types

Sometimes you get this for free:

```lean
def first (l : List Nat) (hl : l ≠ []) : Nat :=
  match l, hl with
  | x :: _, _ => x
```

Lean derives the contradiction in the other arm for you.

:::fragment (index := 1)
Here is what the compiler sees at first:
```
def first._redArg l : tobj :=
  cases l : tobj
  | List.nil =>
    ⊥
  | List.cons =>
    let head.1 := oproj[0] l;
    return head.1
```
:::

:::fragment (index := 2)
One of the phases turns this into
```
def first._redArg l : tobj :=
  let head.1 := oproj[0] l;
  return head.1
```
:::

# Rust

Rust comes with an `unreachable!` macro and an `unreachable_unchecked` function.

```rust
/// # Safety
/// All values in `indices` must be in bounds for `data`.
unsafe fn sum_at(data: &[u64], indices: &[usize]) -> u64 {
    indices.iter().fold(0, |acc, &i| {
        if i >= data.len() {
            // Safety: by the precondition of the function
            unsafe { std::hint::unreachable_unchecked(); }
        }
        acc + data[i]
    })
}
```

:::fragment
```lean
def sumAt (data : Array UInt64) (indices : Array USize)
    (h : ∀ i ∈ indices, i.toNat < data.size) : UInt64 :=
  indices.attach.iter.fold (init := 0) fun acc i =>
    acc + data[i.1]'(by grind)
```

More assistance, more explicit, user-extensible.
:::

# Use case: self-balancing binary search trees

The Lean standard library ships an implementation of weight-balanced trees, a type of
self-balancing binary search tree.

After modifications, we need to rebalance. This is a nested pattern match.

# Use case: UTF-8 strings

# Ergonomics is the key

# Limitations
