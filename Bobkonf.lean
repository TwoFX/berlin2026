/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
import Bobkonf.Slides

open VersoSlides

private def customCss : String := include_str "style.css"

def main (args : List String) : IO UInt32 := do
  let result ← slidesMain (config := { extraCss := #["custom.css"] }) (doc := %doc Bobkonf.Slides) (args := args)
  IO.FS.writeFile ("_slides" / "custom.css") customCss
  return result
