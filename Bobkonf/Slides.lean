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

# How do programs and proofs meet?

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

Lean has serveral mechanisms for influencing the compiler with proofs, among them:
* Runtime functions, and
* pattern matching on empty types.

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

# Self-balancing BSTs: no proofs

Without balancing proofs, impossible cases must be checked at runtime:
```lean -show
section
namespace Std.DTreeMap.Internal.Impl.My
```

```lean -panel
def balanceL! (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match r with
  | leaf => match l with
    | /- !replace ... -/ leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner .. ) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf) /- !end replace -/
    | inner ls lk lv ll@(.inner ..) lr@(.inner lrs ..) =>
        .inner (1 + ls) lk lv ll
          (.inner (1 + lrs) k v lr .leaf)
  | inner rs .. => match l with
    | /- !replace ... -/ leaf => .inner (1 + rs) k v .leaf r /- !end replace -/
    | inner ls lk lv ll lr =>
      if ls > delta * rs then match ll, lr with
        | inner lls .., inner lrs lrk lrv lrl lrr => /- !replace ... -/ if lrs < ratio * lls then
            .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
          else
            .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
              (.inner (1 + rs + lrr.size) k v lrr r) /- !end replace -/
        | inner .., leaf => panic! "balanceL! input was not balanced"
        | leaf, _ => panic! "balanceL! input was not balanced"
      else .inner (1 + ls + rs) k v l r
```

```lean -show
end Std.DTreeMap.Internal.Impl.My
end
```

# Self-balancing BSTs: with proofs

With proofs, the compiler eliminates impossible branches:

```lean -show
axiom mySorry {α : Sort u} : α

section
namespace Std.DTreeMap.Internal.Impl.My


def Balanced {α : Type u} {β : α → Type v} (i : Impl α β) : Prop := True
def BalanceLPrecond (ls rs : Nat) : Prop := True
```

```lean -panel
def balanceL (k : α) (v : β k) (l r : Impl α β)
    (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLPrecond l.size r.size) :
    Impl α β :=
  match r with
  | leaf => match l with
    | /- !replace ... -/ leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner .. ) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf) /- !end replace -/
    | inner ls lk lv (.inner lls ..) (.inner lrs ..) => False.elim /- !replace ✓ -/ mySorry /- !end replace -/
  | inner rs .. => match l with
    | /- !replace ... -/ leaf => .inner (1 + rs) k v .leaf r /- !end replace -/
    | inner ls lk lv ll lr =>
      if hlsd : delta * rs < ls then match ll, lr with
        | inner lls .., inner lrs lrk lrv lrl lrr => /- !replace ... -/ if lrs < ratio * lls then
            .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
          else
            .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
              (.inner (1 + rs + lrr.size) k v lrr r) /- !end replace -/
        | inner .., leaf => False.elim /- !replace ✓ -/ mySorry /- !end replace -/
        | leaf, _ => False.elim /- !replace ✓ -/ mySorry /- !end replace -/
      else .inner (1 + ls + rs) k v (.inner ls lk lv ll lr) r

```

```lean -show
end Std.DTreeMap.Internal.Impl.My
end
```

:::fragment
`✓` is a custom tactic combining `simp`, `omega` and case analysis.
:::

:::fragment
Result: measurable ~3% improvement at runtime.
:::

# Use case: UTF-8 strings

Lean strings are UTF-8 encoded byte arrays. String positions are byte offsets.

```lean -show
namespace Slides.S
```

```lean -panel
structure String where ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```

```lean -show
end Slides.S
```

Every `String` carries a proof that its bytes are valid UTF-8.

# UTF-8 strings: invariant propagation

String operations propagate the invariant:

```lean -show
namespace Slides.S
```

```lean -panel
def String.append (s : String) (t : @& String) : String where
  toByteArray := s.toByteArray ++ t.toByteArray
  isValidUTF8 := s.isValidUTF8.append t.isValidUTF8
```

```lean -show
end Slides.S
```

:::fragment (index := 1)
Relies on a library lemma:

```lean -show
section
open ByteArray
variable {b b' : ByteArray}
namespace My
```

```lean -panel
theorem ByteArray.IsValidUTF8.append (h : IsValidUTF8 b) (h' : IsValidUTF8 b') :
    IsValidUTF8 (b ++ b') :=
  /- !replace ... -/ mySorry /- !end replace -/
```

```lean -show
end My
end
```
:::

# UTF-8 strings: safe character access

Decoding a character at a valid position always succeeds:

```lean -show
section
open String String.Slice
variable {s : Slice}
```

```lean -panel
def Slice.Pos.get {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  s.str.decodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx) /- !replace <proof> -/ mySorry /- !end replace -/
```

:::fragment
`decodeChar` can be implemented efficiently both in C++ or in Lean.

```lean -panel
@[extern "lean_string_utf8_get_fast", expose]
def decodeChar (s : @& String) (byteIdx : @& Nat)
    (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome) : Char :=
  s.toByteArray.utf8DecodeChar byteIdx h
```

Performance impact: noticeable in practice (e.g., identifier auto-completion)

```lean -show
end
```
:::

# UTF-8: theory building

Getting here requires a fair amount of theory building:

:::fragment
1. A library of results about bit vectors (bytes are `BitVec 8`)
2. A formalization of UTF-8 encoding, e.g., the exact byte-level encoding of characters:

```lean -show
section
open String ByteArray ByteArray.utf8DecodeChar?
variable {c : Char} {b b' : ByteArray}
```

```lean -panel
theorem toBitVec_eq_of_parseFirstByte_eq_twoMore
    {b : UInt8} (h : parseFirstByte b = .twoMore) :
    b.toBitVec = 0b1110#4 ++ b.toBitVec.setWidth 4 := /- !replace ... -/ mySorry /- !end replace -/

theorem assemble₃_eq_some_iff_utf8EncodeChar_eq {w x y : UInt8} {c : Char} :
    parseFirstByte w = .twoMore ∧ assemble₃ w x y = some c ↔
      String.utf8EncodeChar c = [w, x, y] := /- !replace ... -/ mySorry /- !end replace -/
```


3. Compositional lemmas such as: if byte arrays {lean}`b` and {lean}`b ++ b'` are valid UTF-8, then so is {lean}`b'`
4. Connecting these results to the string operations in the library
:::

```lean -show
end
```

# Ergonomics

Tracking invariants like this is a bet on the system scaling.

:::fragment
Two axes:
* How hard do the proof obligations become?
* How expensive is it to bail out and perform a runtime check?

:::

# Ergonomics

Verification style differs for binary search trees and strings.
* Trees: peel away all abstractions and discharge SMT-style
* Strings: proper theory-building and hand-written proofs

:::fragment (index := 1)
Opinions:
* Theory-building gets you further than VC generation.
* For true robustness, you need a system that is interactive, highly automated, and understandable.
:::

# Conclusion

Proofs can influence compiled code. Safety does not necessarily mean
paying a runtime cost or blindly hoping that the compiler plays along.

:::fragment
Code and proofs can co-evolve. Safety of programs should not be
held back by the ergonomics of proving systems.

Question: can we get the benefits of mixing programs and proofs while maintaining
them separaretly?
:::
