||| A static object (`Static`), and the words it holds (`SField`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Static

import Core.Name
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

||| A word of a static object. A word that is another static's address or a
||| function's is an absolute address, which the link writes once the image
||| is laid out, and which a position-independent image would relocate.
public export
data SField
  = ||| A raw word, as it is.
    SWord Int64
  | ||| A uniform value that is this integer, a fixnum, whose word the
    ||| value encoding gives; the erased value is 0.
    SVal Int64
  | ||| The address of another static, as a pointer word: the value
    ||| encoding's pointer tag added, as code's pointers to it have it.
    SRef Name
  | ||| The entry address of a function of the program, such as a static
    ||| closure's code, untagged.
    SCode Name

||| A static object: an object the compiler creates in the image's read-only
||| data, laid out exactly as a heap object of its kind, and never
||| allocated, moved, freed or written. `fields` are the words after its
||| header. A static never points into a collected space, which lets the
||| collector recognise statics by address alone and leave them untouched.
public export
record Static (enc : Types.Enc) where
  constructor MkStatic
  sym : Name
  kind : Types.Kind
  header : Types.Header enc kind
  fields : List SField
