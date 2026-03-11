/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
import LeaningIn.Slides

open VersoSlides

private def customCss : String := include_str "style.css"

def copyFile (src dst : System.FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

def main (args : List String) : IO UInt32 := do
  let result ← slidesMain (config := { extraCss := #["custom.css"] }) (doc := %doc LeaningIn.Slides) (args := args)
  IO.FS.writeFile ("_slides" / "custom.css") customCss
  copyFile ("LeaningIn" / "codeaction.png") ("_slides" / "codeaction.png")
  copyFile ("LeaningIn" / "signaturehelp.png") ("_slides" / "signaturehelp.png")
  return result
