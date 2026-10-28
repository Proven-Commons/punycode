/-
  Command line front end.

    punycode encode TEXT
    punycode decode PUNYCODE

  print the Punycode string for the code points of TEXT, or the text a
  Punycode string stands for, and exit with 1 when it stands for none.

    punycode serve

  answers requests on standard input, one per line, for the
  differential tests. A string is sent as the hex digits of its UTF-8
  bytes, so that any code point, a line break included, can be sent.

    encode HEX   prints  OK and the hex of the Punycode string
    decode HEX   prints  OK and the hex of the decoded text, or FAIL

  A malformed request prints `error`: an unknown operation, the wrong
  number of arguments, hex digits that are not in pairs, or bytes that
  are not UTF-8. A request line may end in LF or CR LF.

  Every answer comes from the proved functions in `Punycode/`: `encode`
  and `decode`. The hex coding and the request handling here are
  covered by the tests, not by a proof.
-/

import Punycode

open Punycode

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The string whose UTF-8 bytes the hex digits give. -/
def fromHex (h : String) : Option String := do
  let bs ← hexBytes h.toList
  String.fromUTF8? ⟨bs.toArray⟩

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- The hex digits of a string's UTF-8 bytes. -/
def toHex (s : String) : String :=
  String.ofList (s.toUTF8.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["encode", h] => do
    let s ← fromHex h
    pure ("OK " ++ toHex (encode s.toList))
  | ["decode", h] => do
    let s ← fromHex h
    pure (match decode s with
      | some cs => "OK " ++ toHex (String.ofList cs)
      | none => "FAIL")
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")

def usage : String :=
  "usage: punycode encode TEXT\n       punycode decode PUNYCODE\n       punycode serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["encode", s] => IO.println (encode s.toList); return 0
  | ["decode", s] =>
    match decode s with
    | some cs => IO.println (String.ofList cs); return 0
    | none => IO.eprintln "not a Punycode string"; return 1
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
