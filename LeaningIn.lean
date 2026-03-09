/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
import LeaningIn.Slides

open VersoSlides

def main (args : List String) : IO UInt32 :=
  slidesMain (doc := %doc LeaningIn.Slides) (args := args)
