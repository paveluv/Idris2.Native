||| A static object (`Static`), and the words it holds (`SField`).
|||
||| Part of the located IR (`Compiler.Native.LocatedIR.Program` says what it
||| is).
module Compiler.Native.LocatedIR.Static

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind as HeapObject
import Core.Name

%default total

||| A word of a static object.
public export
data SField
  = ||| A raw word or an immediate value.
    SWord Int64
  | ||| The address of another static. Reserved for constant data built from
    ||| statics; nothing makes one yet.
    SRef Name
  | ||| The entry address of a function of the program, such as `HALT`'s code
    ||| or a static closure's: the only absolute addresses in an image, and
    ||| so the only words a position-independent image would relocate.
    SCode Name

||| A static object: an object the compiler creates in the image's read-only
||| data, laid out exactly as a heap object of its kind, and never
||| allocated, moved, freed or written. `fields` are the words after its
||| header. A static never points into a collected space, which lets the
||| collector recognise statics by address alone and leave them untouched.
public export
record Static (enc : HeapObject.Enc) where
  constructor MkStatic
  sym : Name
  kind : HeapObject.Kind
  header : HeapObject.Header enc kind
  fields : List SField
