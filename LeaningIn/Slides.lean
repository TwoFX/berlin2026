/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
import VersoSlides
import Verso.Doc.Concrete
import Std
import Std.Tactic.Do

open VersoSlides

open Std
open Std.Do
open Std.Internal.IO.Async

set_option linter.unusedVariables false
set_option mvcgen.warning false

#doc (Slides) "Verified software development in Lean" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Verified software development in Lean

Julia Markus Himmel

Lean FRO

# Did you know that Lean is not just a theorem prover, but also a really good programming language? Also, check out all of the cool things that we added to Lean in the past two years that make it even better for programming and proving things about programs

Julia Markus Himmel

Lean FRO

# Lean is a programming language

It's a functional programming language in the ML familiy just like OCaml, Haskell, F#, etc.

:::fragment
It compiles to fast native code.

It can be and is used to write any kind of program, not just Lean metaprograms.

As you know, it supports proofs, so you can do verified software development
(as opposed to just software verification) in it!
:::

# Language Server & VS Code Extension

It's what makes Lean so productive (and fun)!

Way too many highlights to even attempt listing them.

# Unknown identifier code action

![Unknown identifier code action](codeaction.png)

# Signature help

![Signature help](signaturehelp.png)

# New compiler & `do` elaborator

Rewritten for better maintainability and extensibility

Expect more fixes, improvements and extension points!

# Module System

Fine-grained control over which information files export

:::fragment
Default flips from public to private

Amazing for rebuild times

Amazing for kernel checking times

Amazing for encapsulation
:::

# Coinductive predicates

```lean -show
section
```

```lean -panel
coinductive InfSeq (R : α → α → Prop) : α → Prop where
  | step : R a b → InfSeq R b → InfSeq R a
```

:::fragment (index := 1)
Automatically generates the coinduction principle:

```lean -panel
#check @InfSeq.coinduct
```

```lean -show
end
```
:::

# Verso

Our framework for building Lean-aware documentation tools.

These slides are powered by Verso!

```lean
theorem List.toArray_comp_toList :
    List.toArray (α := α) ∘ Array.toList = id := by
  funext a
  simp
```

:::fragment (index := 1)

Cool new feature: Verso docstrings are checked and interactive!

```lean -panel +error
set_option doc.verso true

/-- One side of the bijection between {name}`List` and {name}`Aray` -/
theorem foo {l : List α} : l.toArray.toList = l := by
  simp
```
:::

# Grind

```lean
example (f : Nat → Nat)
    (h₁ : f (f x) = x)
    (h₂ : f (f (f y)) = y) :
    f x = y → f y = x := by
  grind
```

:::fragment
SMT-style tactic: E-matching, congruence closure, case splitting

Good for mathematics, amazing for programming

Sometimes subtle to drive well
:::

# Grind Interactive Mode

```lean +error
example (x y : Rat) (_ : x^2 = 1) (_ : x + y = 1) :
    y ≤ 2 := by
  grind
```

:::fragment

```lean
example (x y : Rat) (_ : x^2 = 1) (_ : x + y = 1) :
    y ≤ 2 := by
  grind =>
    have : x = 1 ∨ x = -1
    finish
```
:::

# Functional induction

```lean -show
section
variable (P : Nat → Prop)
```

```lean
def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by p => p
```

:::fragment (index := 1)

`fun_induction` generates induction goals mirroring the recursive structure:

```lean
example : P (ackermann p) := by
  fun_induction ackermann p with
  | case1 m => sorry
  | case2 n ih => sorry
  | case3 n m ih₁ ih₂ => sorry
```
:::

```lean -show
end
```

# Std.Do / mvcgen

```lean
abbrev TwoBankAccountsM := StateM (Nat × Nat)

def transferFromFirstToSecond (amt : Nat) :
    TwoBankAccountsM Unit := do
  -- Debit first account
  modify (fun (first, second) => (first - amt, second))
  -- Credit second account
  modify (fun (first, second) => (first, second + amt))

theorem transfer_preserves_balance {amt : Nat} {balance : Nat} :
    ⦃fun (accts : Nat × Nat) =>
      ⌜amt ≤ accts.1 ∧ accts.1 + accts.2 = balance⌝⦄
    transferFromFirstToSecond amt
    ⦃⇓ _ (accts : Nat × Nat) =>
      ⌜accts.1 + accts.2 = balance⌝⦄ := by
  mvcgen [transferFromFirstToSecond]
  grind
```

# Concurrency Primitives

```lean
example : IO Unit := do
  let ch ← Std.Channel.new (α := Nat)
    (capacity := (10 : Nat))
  let _ ← ch.send 42
  let task ← ch.recv
  let v := task.get
  IO.println v
```

:::fragment (index := 1)
* {lean}`Std.Mutex`: mutual exclusion guarding shared state
* {lean}`Std.Condvar`: condition variable
* {lean}`Std.Channel`: multi-producer multi-consumer FIFO
* {lean}`Std.Broadcast`: broadcast channel
* {lean}`Std.Barrier`: synchronization barrier
* {lean}`Std.CancellationToken`: cooperative cancellation
:::


# Async I/O

Built on libuv, fully asynchronous:

```lean -show
section
open Std.Internal.IO.Async TCP
```

```lean
def listenAndWait : Async Bool := do
  let server ← Socket.Server.mk
  server.listen 128

  let sleep ← Sleep.mk 1000

  Selectable.one #[
    .case server.acceptSelector (fun _ => pure true),
    .case sleep.selector (fun _ => pure false)]
```

```lean -show
end
```

# HTTP server & client

Coming soon (PRs in review):

* HTTP/1.1 server
* HTTP client including TLS support

# Date and Time library

```lean -show
section
open Std.Time
```

```lean
#eval do
  let now ← Timestamp.now
  let rules ← Database.defaultGetZoneRules "Europe/Berlin"
  let berlin := ZonedDateTime.ofTimestamp now rules
  let nextWeek := berlin.addDays 7
  let fmt := "uuuu-MM-dd HH:mm"
  return s!"{berlin.format fmt} → {nextWeek.format fmt}"
```

```lean -show
end
```

# Iterators

Lazy, composable, provably terminating:

```lean
#eval [1, 2, 3, 4, 5].iter
  |>.filter (· % 2 == 0)
  |>.map (· * 10)
  |>.toArray
```

:::fragment
* Combinators: `map`, `filter`, `filterMap`, `flatMap`, `take`, ...
* Consumers: `fold`, `toArray`, `toList`, `count`, ...
* `Iter` (pure) and `IterM` (monadic)
* Built-in finiteness tracking for termination proofs
:::

# Containers

Verified standard library containers with specification lemmas:

* Hash-based: `HashMap`, `HashSet`
* Tree-based (weight-balanced BSTs): `TreeMap`, `TreeSet`

Also: dependent maps, extensional maps and sets, variants suitable for use in nested inductives

:::fragment
```lean -show
section
open Std Iterators

def Std.Iter.toHashSet {α β : Type w} [BEq β] [Hashable β] [Iterator α Id β]
    [IteratorLoop α Id Id] (it : Iter (α := α) β) : HashSet β :=
  it.fold (init := ∅) (fun sofar a => sofar.insert a)

axiom mySorry {α : Sort u} : α

```

```lean -panel
def sameChars (s₁ s₂ : String) : Bool :=
  s₁.chars.toHashSet == s₂.chars.toHashSet

theorem sameChars_iff {s₁ s₂ : String} :
    sameChars s₁ s₂ ↔ (∀ c, c ∈ s₁.toList ↔ c ∈ s₂.toList) :=
  /- !replace ... -/ mySorry /- !end replace -/
```

```lean -show
end
```
:::

# Strings

* Strings are UTF-8 encoded byte arrays carrying a validity proof
* {lean}`String.Slice`: zero-copy view into a string with bounds proofs
* Safe character access: no runtime bounds or validity checks needed
* Pattern-based API: `split`, `contains`, `startsWith`, ...

```lean -panel
-- Uses KMP!
#eval "hello, world!".contains "o, "
```

```lean -panel
theorem contains_string_iff {t s : String} :
    s.contains t ↔ t.toList <:+: s.toList :=
  /- !replace ... -/ mySorry /- !end replace -/
```
